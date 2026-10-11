//! A running process for the engine's live view.
//!
//! The engine reads a process through [`borer_engine::live::Memory`]; this
//! crate is the one implementation over the operating system: attach to a
//! process by name or id with the least rights that allow reading
//! (`PROCESS_VM_READ` and `PROCESS_QUERY_INFORMATION`, never a write or a
//! debug right), list its modules and its committed regions, and read its
//! memory. It is the one place in borer that calls the process API and so
//! the one crate that holds `unsafe`: each call is a thin wrapper over a
//! Win32 function with what it requires stated beside it. Every borer
//! process comes here too, to step behind the desktop
//! ([`run_below_normal`]), and the server's relay to tie the worker it
//! starts to its own life ([`Tether`]); the allocator's settings and calls
//! are here too ([`commit_on_demand`], [`release_free_memory`]). On another
//! operating system every live entry point says that live access is not
//! available in this build.
#![allow(
    unsafe_code,
    reason = "the process API is foreign; every call is wrapped here with its invariants"
)]

pub use os::{Process, Tether, processes, run_below_normal};

use libmimalloc_sys as _;

unsafe extern "C" {
    /// mimalloc's `void mi_collect(bool force)`: frees what its heaps hold
    /// free and, forced, returns it to the system at once.
    fn mi_collect(force: bool);
    /// mimalloc's `int mi_version(void)`: major, minor and patch as
    /// `major * 10000 + minor * 100 + patch`.
    fn mi_version() -> core::ffi::c_int;
    /// mimalloc's `void mi_option_set(mi_option_t option, long value)`.
    fn mi_option_set(option: core::ffi::c_int, value: core::ffi::c_long);
}

/// The place of `mi_option_page_commit_on_demand` among the options of
/// mimalloc 3.3, the version this build links.
const PAGE_COMMIT_ON_DEMAND: core::ffi::c_int = 40;

/// mimalloc 3.3 as [`mi_version`] reports it, with the patch level
/// divided away: the version [`PAGE_COMMIT_ON_DEMAND`] is the index for.
const MIMALLOC_3_3: core::ffi::c_int = 303;

/// Has the allocator commit a page's memory as it is first touched, rather
/// than all of the page when it hands the page out.
///
/// Every thread takes pages of its own, so committing them whole charged an
/// analysis's sixteen walker threads sixty megabytes they never touched: on
/// a small program, two thirds of what the process committed, with no gain
/// in speed. The setting applies to pages handed out after the call, so it
/// is made first thing in `main`. A mimalloc other than 3.3 numbers its
/// options its own way and is left as it is.
pub fn commit_on_demand() {
    // SAFETY: mi_version takes nothing and reports a constant.
    if unsafe { mi_version() } / 100 != MIMALLOC_3_3 {
        return;
    }
    // SAFETY: the option is the 3.3 index, checked above, and both
    // arguments are plain integers.
    unsafe { mi_option_set(PAGE_COMMIT_ON_DEMAND, 1) };
}

/// Hands the memory the allocator holds free back to the system.
///
/// mimalloc, the allocator borer links, returns freed memory only while the
/// process goes on allocating, so a server that answered a large request
/// and then waited kept what the request had freed for as long as it
/// waited: two hundred megabytes after building a large program's index.
/// Called once an answer is written, it leaves a waiting server holding
/// what it uses; the next request takes fresh memory as it needs it.
pub fn release_free_memory() {
    // SAFETY: mi_collect takes a flag by value and works on the allocator's
    // own bookkeeping, which it guards for use from any thread.
    unsafe { mi_collect(true) };
}

/// The Windows implementation: `ToolHelp` snapshots for processes and
/// modules, `OpenProcess` with read rights, `ReadProcessMemory` and
/// `VirtualQueryEx`.
#[cfg(windows)]
mod os {
    use core::ffi::c_void;
    use std::os::windows::io::AsRawHandle as _;
    use std::process::Child;

    use borer_engine::live::{Memory, Module, Region};
    use windows_sys::Wdk::System::Threading::{NtQueryInformationThread, ThreadBasicInformation};
    use windows_sys::Win32::Foundation::{CloseHandle, GetLastError, HANDLE, INVALID_HANDLE_VALUE};
    use windows_sys::Win32::System::Diagnostics::Debug::ReadProcessMemory;
    use windows_sys::Win32::System::Diagnostics::ToolHelp::{
        CreateToolhelp32Snapshot, MODULEENTRY32W, Module32FirstW, Module32NextW, PROCESSENTRY32W,
        Process32FirstW, Process32NextW, TH32CS_SNAPMODULE, TH32CS_SNAPMODULE32,
        TH32CS_SNAPPROCESS, TH32CS_SNAPTHREAD, THREADENTRY32, Thread32First, Thread32Next,
    };
    use windows_sys::Win32::System::JobObjects::{
        AssignProcessToJobObject, CreateJobObjectW, JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE,
        JOBOBJECT_EXTENDED_LIMIT_INFORMATION, JobObjectExtendedLimitInformation,
        SetInformationJobObject,
    };
    use windows_sys::Win32::System::Memory::{
        MEM_COMMIT, MEM_IMAGE, MEMORY_BASIC_INFORMATION, PAGE_EXECUTE, PAGE_EXECUTE_READ,
        PAGE_EXECUTE_READWRITE, PAGE_EXECUTE_WRITECOPY, PAGE_GUARD, PAGE_NOACCESS, PAGE_READWRITE,
        PAGE_WRITECOPY, VirtualQueryEx,
    };
    use windows_sys::Win32::System::Threading::{
        BELOW_NORMAL_PRIORITY_CLASS, GetCurrentProcess, MEMORY_PRIORITY_BELOW_NORMAL,
        MEMORY_PRIORITY_INFORMATION, OpenProcess, OpenThread, PROCESS_QUERY_INFORMATION,
        PROCESS_VM_READ, ProcessMemoryPriority, SetPriorityClass, SetProcessInformation,
        THREAD_QUERY_INFORMATION,
    };

    /// What `NtQueryInformationThread(ThreadBasicInformation)` fills: the
    /// documented `THREAD_BASIC_INFORMATION`, which the bindings do not
    /// declare. Only the TEB address is read.
    #[repr(C)]
    struct ThreadBasics {
        /// `NTSTATUS ExitStatus`.
        exit_status: i32,
        /// `PVOID TebBaseAddress`.
        teb: *mut c_void,
        /// `CLIENT_ID ClientId`: process and thread ids as handles.
        client_id: [usize; 2],
        /// `KAFFINITY AffinityMask`.
        affinity: usize,
        /// `KPRIORITY Priority`.
        priority: i32,
        /// `KPRIORITY BasePriority`.
        base_priority: i32,
    }

    /// Bytes read in one piece when a whole read fails and the range is
    /// retried page by page.
    const PAGE: usize = 4096;

    /// Most times the module snapshot is retried when the system reports
    /// the list changed under it (`ERROR_BAD_LENGTH`), as its documentation
    /// says to.
    const SNAPSHOT_RETRIES: usize = 8;

    /// `ERROR_BAD_LENGTH`: the module snapshot must be retried.
    const ERROR_BAD_LENGTH: u32 = 24;

    /// A Win32 handle closed when dropped.
    #[derive(Debug)]
    struct Handle(HANDLE);

    impl Drop for Handle {
        fn drop(&mut self) {
            // SAFETY: the handle came from a successful OpenProcess,
            // CreateToolhelp32Snapshot or CreateJobObjectW and is closed
            // exactly once, here.
            unsafe {
                CloseHandle(self.0);
            }
        }
    }

    // SAFETY: a process handle is a kernel object reference the system
    // allows any thread to use; nothing here ties it to the opening thread.
    unsafe impl Send for Handle {}
    // SAFETY: every use of the handle is a read of another process; the
    // calls take the handle by value and keep no state in this process.
    unsafe impl Sync for Handle {}

    /// Text of a NUL-terminated UTF-16 buffer.
    ///
    /// # Arguments
    ///
    /// * `units` - The buffer, with the terminator somewhere in it.
    fn wide(units: &[u16]) -> String {
        let len = units.iter().position(|u| *u == 0).unwrap_or(units.len());
        String::from_utf16_lossy(&units[..len])
    }

    /// The last Win32 error, for a message.
    fn last_error() -> u32 {
        // SAFETY: GetLastError reads the calling thread's error slot and
        // takes nothing.
        unsafe { GetLastError() }
    }

    /// Lowers this process below normal priority, for the processor and for
    /// memory, so the desktop and the machine's other work go first.
    ///
    /// Its threads then run on the cores that work leaves free, and its
    /// pages are the first the system takes back when memory runs short. A
    /// process alone on an idle machine runs as fast as before, and the
    /// processes it starts begin at the same priority. A refusal leaves the
    /// priority as it was, which costs the machine's responsiveness and
    /// never an answer, so it is not reported.
    pub fn run_below_normal() {
        // SAFETY: GetCurrentProcess returns a pseudo-handle that is never
        // closed, and SetPriorityClass takes it and the class by value.
        unsafe { SetPriorityClass(GetCurrentProcess(), BELOW_NORMAL_PRIORITY_CLASS) };
        let memory = MEMORY_PRIORITY_INFORMATION {
            MemoryPriority: MEMORY_PRIORITY_BELOW_NORMAL,
        };
        let Ok(size) = u32::try_from(size_of::<MEMORY_PRIORITY_INFORMATION>()) else {
            return;
        };
        // SAFETY: the pointer and length describe `memory`, which outlives
        // the call, and the pseudo-handle names this process.
        unsafe {
            SetProcessInformation(
                GetCurrentProcess(),
                ProcessMemoryPriority,
                core::ptr::from_ref(&memory).cast::<c_void>(),
                size,
            )
        };
    }

    /// A job that ends every process tied to it when the process holding it
    /// ends, however that ends: an exit, a crash, or a kill from outside.
    ///
    /// The relay holds one for the worker it serves the session through. A
    /// worker otherwise notices its relay is gone only when it next reads
    /// its input, so one killed mid-request ran that request to its end,
    /// on every core, for an answer no one would read.
    #[derive(Debug)]
    pub struct Tether(Handle);

    impl Tether {
        /// Creates the job, with the limit that ends its processes when its
        /// last handle closes. The handle is not inherited, so the processes
        /// tied to it do not keep it open themselves.
        ///
        /// # Errors
        ///
        /// When the system refuses to create or set up the job.
        pub fn new() -> Result<Tether, String> {
            // SAFETY: no security attributes and no name make an anonymous
            // job with an uninheritable handle, checked for null before use.
            let job = unsafe { CreateJobObjectW(core::ptr::null(), core::ptr::null()) };
            if job.is_null() {
                return Err(format!("cannot create a job: Win32 error {}", last_error()));
            }
            let job = Handle(job);
            let mut limits = JOBOBJECT_EXTENDED_LIMIT_INFORMATION::default();
            limits.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
            let size = u32::try_from(size_of::<JOBOBJECT_EXTENDED_LIMIT_INFORMATION>())
                .map_err(|e| format!("the job's limits do not fit a length: {e}"))?;
            // SAFETY: the pointer and length describe `limits`, which
            // outlives the call, and the job handle is open.
            let set = unsafe {
                SetInformationJobObject(
                    job.0,
                    JobObjectExtendedLimitInformation,
                    core::ptr::from_ref(&limits).cast::<c_void>(),
                    size,
                )
            };
            if set == 0 {
                return Err(format!(
                    "cannot set the job's limits: Win32 error {}",
                    last_error()
                ));
            }
            Ok(Tether(job))
        }

        /// Ties a child process to the job, so it ends when this process
        /// does.
        ///
        /// # Arguments
        ///
        /// * `child` - The process, still running.
        ///
        /// # Errors
        ///
        /// When the system refuses, as for a process that already ended.
        pub fn tie(&self, child: &Child) -> Result<(), String> {
            // SAFETY: the job handle is open for the life of `self`, and the
            // child's handle for the life of `child`.
            let tied = unsafe { AssignProcessToJobObject(self.0.0, child.as_raw_handle()) };
            if tied == 0 {
                return Err(format!(
                    "cannot tie process {} to the job: Win32 error {}",
                    child.id(),
                    last_error()
                ));
            }
            Ok(())
        }
    }

    /// Lists the running processes.
    ///
    /// # Returns
    ///
    /// `(pid, executable name)` pairs.
    ///
    /// # Errors
    ///
    /// When the system refuses the process snapshot.
    pub fn processes() -> Result<Vec<(u32, String)>, String> {
        // SAFETY: a process snapshot takes no pointers; the handle is checked
        // against the invalid value before use.
        let snap = unsafe { CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0) };
        if snap == INVALID_HANDLE_VALUE {
            return Err(format!(
                "cannot list processes: Win32 error {}",
                last_error()
            ));
        }
        let snap = Handle(snap);
        // SAFETY: PROCESSENTRY32W is plain data; every field is valid as zero.
        let mut entry: PROCESSENTRY32W = unsafe { core::mem::zeroed() };
        entry.dwSize = u32::try_from(size_of::<PROCESSENTRY32W>()).unwrap_or(0);
        let mut out = Vec::new();
        // SAFETY: `entry` is a properly sized PROCESSENTRY32W that outlives
        // the call, and the snapshot handle is valid.
        let mut more = unsafe { Process32FirstW(snap.0, &mut entry) } != 0;
        while more {
            out.push((entry.th32ProcessID, wide(&entry.szExeFile)));
            // SAFETY: as for Process32FirstW.
            more = unsafe { Process32NextW(snap.0, &mut entry) } != 0;
        }
        Ok(out)
    }

    /// Lists a process's modules.
    ///
    /// # Arguments
    ///
    /// * `pid` - The process.
    ///
    /// # Errors
    ///
    /// When the system refuses the module snapshot after its retries.
    fn modules_of(pid: u32) -> Result<Vec<Module>, String> {
        let mut error = 0;
        for _ in 0..SNAPSHOT_RETRIES {
            // SAFETY: a module snapshot takes no pointers; the handle is
            // checked against the invalid value before use.
            let snap =
                unsafe { CreateToolhelp32Snapshot(TH32CS_SNAPMODULE | TH32CS_SNAPMODULE32, pid) };
            if snap == INVALID_HANDLE_VALUE {
                error = last_error();
                if error == ERROR_BAD_LENGTH {
                    continue;
                }
                break;
            }
            let snap = Handle(snap);
            // SAFETY: MODULEENTRY32W is plain data; every field is valid as
            // zero (its pointers are only read back, never followed here).
            let mut entry: MODULEENTRY32W = unsafe { core::mem::zeroed() };
            entry.dwSize = u32::try_from(size_of::<MODULEENTRY32W>()).unwrap_or(0);
            let mut out = Vec::new();
            // SAFETY: `entry` is a properly sized MODULEENTRY32W that
            // outlives the call, and the snapshot handle is valid.
            let mut more = unsafe { Module32FirstW(snap.0, &mut entry) } != 0;
            while more {
                out.push(Module {
                    name: wide(&entry.szModule),
                    path: wide(&entry.szExePath),
                    base: entry.modBaseAddr as usize as u64,
                    size: u64::from(entry.modBaseSize),
                });
                // SAFETY: as for Module32FirstW.
                more = unsafe { Module32NextW(snap.0, &mut entry) } != 0;
            }
            return Ok(out);
        }
        Err(format!(
            "cannot list the modules of process {pid}: Win32 error {error}"
        ))
    }

    /// A process opened for reading.
    #[derive(Debug)]
    pub struct Process {
        /// The open handle.
        handle: Handle,
        /// Process id.
        pid: u32,
        /// Executable name.
        name: String,
        /// Modules at attach time.
        modules: Vec<Module>,
    }

    impl Process {
        /// Opens a process for reading.
        ///
        /// # Arguments
        ///
        /// * `spec` - A process id, or an executable name (`notepad` or
        ///   `notepad.exe`, case does not matter).
        ///
        /// # Errors
        ///
        /// When no process matches, several do, or the system refuses the
        /// handle (another user's process, or one protected by its
        /// anti-tamper, needs rights this never asks for).
        pub fn attach(spec: &str) -> Result<Process, String> {
            let spec = spec.trim();
            let (pid, name) = match spec.parse::<u32>() {
                Ok(pid) => {
                    let name = processes()?
                        .into_iter()
                        .find(|(p, _)| *p == pid)
                        .map(|(_, n)| n)
                        .ok_or_else(|| format!("no process has id {pid}"))?;
                    (pid, name)
                }
                Err(_) => {
                    let want = spec.to_lowercase();
                    let want_exe = if want.ends_with(".exe") {
                        want.clone()
                    } else {
                        format!("{want}.exe")
                    };
                    let hits: Vec<(u32, String)> = processes()?
                        .into_iter()
                        .filter(|(_, n)| {
                            let n = n.to_lowercase();
                            n == want || n == want_exe
                        })
                        .collect();
                    match hits.as_slice() {
                        [] => return Err(format!("no running process is named {spec}")),
                        [one] => one.clone(),
                        many => {
                            let ids: Vec<String> =
                                many.iter().map(|(p, _)| p.to_string()).collect();
                            return Err(format!(
                                "{} processes are named {spec}: pass one id of {}",
                                many.len(),
                                ids.join(", ")
                            ));
                        }
                    }
                }
            };
            // SAFETY: OpenProcess takes plain values; the handle is checked
            // for null before it is kept.
            let handle =
                unsafe { OpenProcess(PROCESS_VM_READ | PROCESS_QUERY_INFORMATION, 0, pid) };
            if handle.is_null() {
                return Err(format!(
                    "cannot open process {pid} ({name}) for reading: Win32 error {}",
                    last_error()
                ));
            }
            let handle = Handle(handle);
            let modules = modules_of(pid)?;
            Ok(Process {
                handle,
                pid,
                name,
                modules,
            })
        }

        /// The process id.
        #[must_use]
        pub fn pid(&self) -> u32 {
            self.pid
        }

        /// The executable name.
        #[must_use]
        pub fn name(&self) -> &str {
            &self.name
        }

        /// The process's thread ids, in the order the system lists them
        /// (creation order, the main thread first, as a rule).
        ///
        /// # Errors
        ///
        /// When the system refuses the thread snapshot.
        pub fn threads(&self) -> Result<Vec<u32>, String> {
            // SAFETY: a thread snapshot takes no pointers; the handle is
            // checked against the invalid value before use.
            let snap = unsafe { CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0) };
            if snap == INVALID_HANDLE_VALUE {
                return Err(format!("cannot list threads: Win32 error {}", last_error()));
            }
            let snap = Handle(snap);
            // SAFETY: THREADENTRY32 is plain data; every field is valid as zero.
            let mut entry: THREADENTRY32 = unsafe { core::mem::zeroed() };
            entry.dwSize = u32::try_from(size_of::<THREADENTRY32>()).unwrap_or(0);
            let mut out = Vec::new();
            // SAFETY: `entry` is a properly sized THREADENTRY32 that outlives
            // the call, and the snapshot handle is valid.
            let mut more = unsafe { Thread32First(snap.0, &mut entry) } != 0;
            while more {
                if entry.th32OwnerProcessID == self.pid {
                    out.push(entry.th32ThreadID);
                }
                // SAFETY: as for Thread32First.
                more = unsafe { Thread32Next(snap.0, &mut entry) } != 0;
            }
            Ok(out)
        }

        /// The address of a thread's environment block (TEB) in the process.
        ///
        /// # Arguments
        ///
        /// * `tid` - A thread of the process.
        ///
        /// # Errors
        ///
        /// When the thread cannot be opened or queried.
        pub fn teb_of(&self, tid: u32) -> Result<u64, String> {
            // SAFETY: OpenThread takes plain values; the handle is checked
            // for null before it is kept.
            let h = unsafe { OpenThread(THREAD_QUERY_INFORMATION, 0, tid) };
            if h.is_null() {
                return Err(format!(
                    "cannot open thread {tid}: Win32 error {}",
                    last_error()
                ));
            }
            let h = Handle(h);
            // SAFETY: ThreadBasics is plain data; every field is valid as
            // zero (the pointer is only read back, never followed here).
            let mut info: ThreadBasics = unsafe { core::mem::zeroed() };
            let mut len: u32 = 0;
            // SAFETY: `info` is a properly sized buffer that outlives the
            // call, its length is passed, and the handle is open with
            // QUERY_INFORMATION.
            let status = unsafe {
                NtQueryInformationThread(
                    h.0,
                    ThreadBasicInformation,
                    (&raw mut info).cast::<c_void>(),
                    u32::try_from(size_of::<ThreadBasics>()).unwrap_or(0),
                    &mut len,
                )
            };
            if status < 0 {
                return Err(format!("cannot query thread {tid}: NTSTATUS {status:#x}"));
            }
            Ok(info.teb as usize as u64)
        }

        /// Reads one piece, as many bytes as the system gives.
        ///
        /// # Arguments
        ///
        /// * `va` - First address.
        /// * `buf` - Receives the bytes.
        ///
        /// # Returns
        ///
        /// Bytes read, zero when the piece is not readable.
        fn read_piece(&self, va: u64, buf: &mut [u8]) -> usize {
            // An address past the pointer width is not readable.
            let Ok(at) = usize::try_from(va) else {
                return 0;
            };
            let mut got: usize = 0;
            // SAFETY: `buf` is a live, writable slice of exactly `buf.len()`
            // bytes for the duration of the call, `got` outlives it, and
            // the handle is open with VM_READ; the foreign address is only
            // passed on, never dereferenced here.
            let ok = unsafe {
                ReadProcessMemory(
                    self.handle.0,
                    at as *const c_void,
                    buf.as_mut_ptr().cast::<c_void>(),
                    buf.len(),
                    &mut got,
                )
            };
            if ok == 0 { 0 } else { got.min(buf.len()) }
        }
    }

    impl Memory for Process {
        fn read(&self, va: u64, len: usize) -> Option<Vec<u8>> {
            let mut buf = vec![0u8; len];
            let got = self.read_piece(va, &mut buf);
            if got == len {
                return Some(buf);
            }
            // The range runs into memory that is not there: take it page by
            // page up to the first page that fails.
            let mut total = 0usize;
            while total < len {
                let next_page = ((va + total as u64) / PAGE as u64 + 1) * PAGE as u64;
                let piece = usize::try_from(next_page - (va + total as u64))
                    .unwrap_or(PAGE)
                    .min(len - total);
                let got = self.read_piece(va + total as u64, &mut buf[total..total + piece]);
                if got == 0 {
                    break;
                }
                total += got;
                if got < piece {
                    break;
                }
            }
            if total == 0 {
                return None;
            }
            buf.truncate(total);
            Some(buf)
        }

        fn regions(&self) -> Vec<Region> {
            let mut out = Vec::new();
            let mut at: u64 = 0;
            // An address past the pointer width has no region to query.
            while let Ok(here) = usize::try_from(at) {
                // SAFETY: MEMORY_BASIC_INFORMATION is plain data; every
                // field is valid as zero.
                let mut info: MEMORY_BASIC_INFORMATION = unsafe { core::mem::zeroed() };
                // SAFETY: `info` is a properly sized buffer that outlives the
                // call and the handle is open with QUERY_INFORMATION.
                let n = unsafe {
                    VirtualQueryEx(
                        self.handle.0,
                        here as *const c_void,
                        &mut info,
                        size_of::<MEMORY_BASIC_INFORMATION>(),
                    )
                };
                if n == 0 {
                    break;
                }
                let base = info.BaseAddress as usize as u64;
                let size = info.RegionSize as u64;
                let readable = info.State == MEM_COMMIT
                    && info.Protect & PAGE_GUARD == 0
                    && info.Protect & PAGE_NOACCESS == 0
                    && info.Protect != 0;
                if readable {
                    let p = info.Protect;
                    out.push(Region {
                        base,
                        size,
                        writable: p
                            & (PAGE_READWRITE
                                | PAGE_WRITECOPY
                                | PAGE_EXECUTE_READWRITE
                                | PAGE_EXECUTE_WRITECOPY)
                            != 0,
                        executable: p
                            & (PAGE_EXECUTE
                                | PAGE_EXECUTE_READ
                                | PAGE_EXECUTE_READWRITE
                                | PAGE_EXECUTE_WRITECOPY)
                            != 0,
                        image: info.Type == MEM_IMAGE,
                    });
                }
                let Some(next) = base.checked_add(size) else {
                    break;
                };
                if next <= at {
                    break;
                }
                at = next;
            }
            out
        }

        fn modules(&self) -> Vec<Module> {
            self.modules.clone()
        }
    }
}

/// The stand-in off Windows: every live entry point says live access is
/// not available in this build, and a tether ties nothing.
#[cfg(not(windows))]
mod os {
    use std::process::Child;

    use borer_engine::live::{Memory, Module, Region};

    /// Leaves the priority as it is off Windows.
    pub fn run_below_normal() {}

    /// Ties nothing off Windows: a worker there ends when its input closes,
    /// which is when its relay ends unless the worker is mid-request.
    #[derive(Debug)]
    pub struct Tether;

    impl Tether {
        /// Makes the stand-in.
        ///
        /// # Errors
        ///
        /// Never; the signature is the Windows one.
        pub fn new() -> Result<Tether, String> {
            Ok(Tether)
        }

        /// Ties nothing.
        ///
        /// # Arguments
        ///
        /// * `_child` - The process.
        ///
        /// # Errors
        ///
        /// Never; the signature is the Windows one.
        pub fn tie(&self, _child: &Child) -> Result<(), String> {
            Ok(())
        }
    }

    /// A process opened for reading; never constructed off Windows.
    #[derive(Debug)]
    pub struct Process {
        /// Process id.
        pid: u32,
        /// Executable name.
        name: String,
    }

    /// Lists the running processes.
    ///
    /// # Errors
    ///
    /// Always: live access is not available in this build.
    pub fn processes() -> Result<Vec<(u32, String)>, String> {
        Err("live process access is available on Windows only".to_owned())
    }

    impl Process {
        /// Opens a process for reading.
        ///
        /// # Arguments
        ///
        /// * `spec` - A process id or executable name.
        ///
        /// # Errors
        ///
        /// Always: live access is not available in this build.
        pub fn attach(spec: &str) -> Result<Process, String> {
            Err(format!(
                "cannot attach to {spec}: live process access is available on Windows only"
            ))
        }

        /// The process id.
        #[must_use]
        pub fn pid(&self) -> u32 {
            self.pid
        }

        /// The executable name.
        #[must_use]
        pub fn name(&self) -> &str {
            &self.name
        }

        /// The process's thread ids.
        ///
        /// # Errors
        ///
        /// Always: live access is not available in this build.
        pub fn threads(&self) -> Result<Vec<u32>, String> {
            Err(format!(
                "cannot list the threads of pid {}: live process access is available on Windows only",
                self.pid
            ))
        }

        /// The address of a thread's environment block.
        ///
        /// # Arguments
        ///
        /// * `tid` - A thread of the process.
        ///
        /// # Errors
        ///
        /// Always: live access is not available in this build.
        pub fn teb_of(&self, tid: u32) -> Result<u64, String> {
            Err(format!(
                "cannot query thread {tid} of pid {}: live process access is available on Windows only",
                self.pid
            ))
        }
    }

    impl Memory for Process {
        fn read(&self, _va: u64, _len: usize) -> Option<Vec<u8>> {
            None
        }

        fn regions(&self) -> Vec<Region> {
            Vec::new()
        }

        fn modules(&self) -> Vec<Module> {
            Vec::new()
        }
    }
}

#[cfg(all(test, windows))]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};

    use borer_engine::live::{Memory, find_words};

    use windows_sys::Win32::System::Threading::{
        BELOW_NORMAL_PRIORITY_CLASS, GetCurrentProcess, GetPriorityClass,
    };

    use super::{
        MIMALLOC_3_3, PAGE_COMMIT_ON_DEMAND, Process, Tether, commit_on_demand, mi_version,
        release_free_memory, run_below_normal,
    };

    unsafe extern "C" {
        /// mimalloc's `long mi_option_get(mi_option_t option)`.
        fn mi_option_get(option: core::ffi::c_int) -> core::ffi::c_long;
        /// mimalloc's `mi_process_info`; only the commit charge is read.
        fn mi_process_info(
            elapsed_msecs: *mut usize,
            user_msecs: *mut usize,
            system_msecs: *mut usize,
            current_rss: *mut usize,
            peak_rss: *mut usize,
            current_commit: *mut usize,
            peak_commit: *mut usize,
            page_faults: *mut usize,
        );
    }

    /// The linked mimalloc is the 3.3 whose option index is written down,
    /// and after the call it commits pages on demand.
    ///
    /// A new mimalloc fails here before it can set the wrong option.
    #[test]
    fn the_allocator_commits_pages_on_demand() {
        // SAFETY: mi_version takes nothing.
        assert_eq!(
            unsafe { mi_version() } / 100,
            MIMALLOC_3_3,
            "another mimalloc: check the place of mi_option_page_commit_on_demand"
        );
        commit_on_demand();
        // SAFETY: the option is a plain integer naming a 3.3 option.
        assert_eq!(unsafe { mi_option_get(PAGE_COMMIT_ON_DEMAND) }, 1);
    }

    /// Bytes this process has committed, as mimalloc reads them.
    fn committed() -> usize {
        let mut v = [0usize; 8];
        let [a, b, c, d, e, f, g, h] = &mut v;
        // SAFETY: every pointer is to a live, writable `usize`.
        unsafe { mi_process_info(a, b, c, d, e, f, g, h) };
        v[5]
    }

    /// Memory the allocator holds free goes back to the system when it is
    /// released, where the allocator alone would keep it until the process
    /// next allocated.
    #[test]
    fn freed_memory_goes_back_when_released() {
        /// Bytes allocated, written and freed.
        const BLOCKS: usize = 8 * 1024;
        /// Bytes per block.
        const BLOCK: usize = 1024;
        let blocks: Vec<*mut u8> = (0..BLOCKS)
            .map(|_| {
                // SAFETY: a plain allocation, written in full and freed below.
                let p = unsafe { libmimalloc_sys::mi_malloc(BLOCK) }.cast::<u8>();
                assert!(!p.is_null());
                // SAFETY: `p` points to `BLOCK` writable bytes.
                unsafe { p.write_bytes(1, BLOCK) };
                p
            })
            .collect();
        for p in blocks {
            // SAFETY: each block came from mi_malloc and is freed once.
            unsafe { libmimalloc_sys::mi_free(p.cast()) };
        }
        let held = committed();
        release_free_memory();
        let after = committed();
        assert!(
            after + BLOCKS * BLOCK / 2 < held,
            "committed {held} before and {after} after"
        );
    }

    /// After stepping behind the desktop the process runs below normal
    /// priority.
    #[test]
    fn a_process_steps_behind_the_desktop() {
        run_below_normal();
        // SAFETY: the pseudo-handle names this process and needs no closing.
        let class = unsafe { GetPriorityClass(GetCurrentProcess()) };
        assert_eq!(class, BELOW_NORMAL_PRIORITY_CLASS);
    }

    /// A process tied to a tether ends when the tether is dropped.
    ///
    /// Dropping it closes the last handle to the job, as the system does
    /// when the relay holding it is killed: a `ping` asked to run for a
    /// minute is gone within seconds.
    #[test]
    fn a_tied_process_ends_with_its_tether() {
        let tether = Tether::new().expect("a job");
        let mut child = Command::new("ping")
            .args(["-n", "60", "127.0.0.1"])
            .stdout(Stdio::null())
            .spawn()
            .expect("ping starts");
        tether.tie(&child).expect("the child is tied");
        assert!(child.try_wait().expect("poll").is_none(), "still running");
        drop(tether);
        #[expect(
            clippy::disallowed_methods,
            reason = "the test bounds how long the tied process outlives its tether"
        )]
        let since = Instant::now();
        while child.try_wait().expect("poll").is_none() {
            assert!(
                since.elapsed() < Duration::from_secs(20),
                "the tied process outlived its tether"
            );
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    /// The current process reads its own bytes back, lists its modules with
    /// this executable among them, and finds a word planted on its heap.
    #[test]
    fn the_current_process_reads_itself() {
        let me = Process::attach(&std::process::id().to_string()).expect("attach to self");
        assert_eq!(me.pid(), std::process::id());
        let planted: Vec<u64> = vec![0x5a5a_1234_abcd_0001, 0, 0x5a5a_1234_abcd_0001];
        let at = planted.as_ptr() as usize as u64;
        let bytes = me.read(at, 24).expect("read own heap");
        assert_eq!(bytes.len(), 24);
        assert_eq!(&bytes[..8], &0x5a5a_1234_abcd_0001u64.to_le_bytes());
        assert!(me.read(0x10, 8).is_none(), "the null page is not readable");
        let modules = me.modules();
        assert!(
            modules
                .iter()
                .any(|m| m.name.to_lowercase().ends_with(".exe")),
            "{modules:?}"
        );
        let regions = me.regions();
        assert!(
            regions
                .iter()
                .any(|r| (r.base..r.base + r.size).contains(&at) && r.writable),
            "the heap is a writable region"
        );
        let scan = find_words(&me, &[0x5a5a_1234_abcd_0001], 8, 16);
        assert!(scan.hits.contains(&at), "planted {at:#x}: {scan:?}");
        assert!(
            scan.hits.contains(&(at + 16)),
            "planted {:#x}: {scan:?}",
            at + 16
        );
        let threads = me.threads().expect("list own threads");
        assert!(!threads.is_empty());
        let teb = me.teb_of(threads[0]).expect("the TEB of a thread");
        assert!(teb > 0x1_0000, "{teb:#x}");
        assert!(me.read(teb, 8).is_some(), "the TEB is readable");
    }
}
