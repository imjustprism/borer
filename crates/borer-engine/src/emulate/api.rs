//! The modeled outside world: imported API stubs, their arguments and
//! results, allocations, and Linux system calls.

use super::calls::ApiCall;
use super::{Emulator, Stop, image_byte, linux_syscall_name};
use crate::analysis::decompile::abi;
use crate::isa::x86::{Instruction, Register};
use crate::num::{from_usize, lo8};

/// Base of the synthetic addresses that stand in for imported functions.
///
/// Distinct from image, stack and allocations so a call to one is recognized
/// as an API call; the slots of the import table are prefilled with these.
const API_STUB_BASE: u64 = 0x7ffd_0000_0000;

/// Base of the API stubs on a 32-bit target: below the scratch stack and
/// clear of any image, where a system library would load, so a four-byte
/// import slot holds all of a stub address.
pub(super) const API_STUB_BASE_32: u64 = 0x7e00_0000;

/// Base of the memory a modeled allocator returns, bumped per call.
pub(super) const ALLOC_BASE: u64 = 0x6000_0000_0000;

/// Base of the memory a modeled allocator returns on a 32-bit target: above
/// the bases an executable and a DLL are linked at, below the API stubs, so
/// a four-byte pointer holds all of it.
pub(super) const ALLOC_BASE_32: u64 = 0x6000_0000;

/// Most bytes one modeled `memcpy`, `memmove` or `memset` moves, so a
/// wild length cannot fill the memory map.
const API_COPY_MAX: usize = 0x1_0000;

/// Address space one modeled allocation takes, whatever size it asked for.
pub(super) const ALLOC_STRIDE: u64 = 0x0010_0000;

/// Where an argument lives on entry: a 64-bit convention puts the first few
/// in registers and the rest on the stack, a 32-bit convention all of them
/// on the stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ArgSlot {
    /// One of the convention's argument registers.
    Register(Register),
    /// A stack address past the return address the call pushed.
    Stack(u64),
}

impl Emulator<'_> {
    /// Reads the `n`th argument of the API being serviced.
    ///
    /// On a 64-bit target the first few travel in the registers of the
    /// program's convention; on a 32-bit one every argument sits on the
    /// stack above the return address the call pushed, which the stack
    /// pointer still points at when the stub is entered.
    ///
    /// # Arguments
    ///
    /// * `n` - Argument index from zero.
    fn api_arg(&self, n: usize) -> u64 {
        match self.arg_slot(n) {
            ArgSlot::Register(r) => self.reg(r),
            ArgSlot::Stack(slot) => self.load(slot, self.word).unwrap_or(0),
        }
    }

    /// Where the `n`th argument lives as the callee sees it on entry.
    ///
    /// The registers are those of the program's convention ([`abi::conv`]);
    /// the stack slots count from the one past the return address, which
    /// the stack pointer still points at, and past any shadow space.
    ///
    /// # Arguments
    ///
    /// * `n` - Argument index from zero.
    pub(super) fn arg_slot(&self, n: usize) -> ArgSlot {
        let conv = abi::conv(self.program, self.bitness);
        if let Some(r) = conv.args.get(n) {
            return ArgSlot::Register(*r);
        }
        let word = from_usize(self.word);
        let past = from_usize(n.saturating_sub(conv.args.len()));
        ArgSlot::Stack(
            self.reg(Register::RSP)
                .wrapping_add(word)
                .wrapping_add(conv.shadow.unsigned_abs())
                .wrapping_add(past.wrapping_mul(word)),
        )
    }

    /// Prefills the import table so each slot holds a stub for its API.
    ///
    /// The OS loader writes the address of each imported function into its
    /// import-address-table slot; a packer then reads those slots and calls
    /// through them. This writes a distinct synthetic address into every slot
    /// and remembers which API it stands for, so a call reaching that address
    /// is serviced by [`Emulator::service_api`] instead of faulting on the zero
    /// a static image leaves there. The writes are setup, not materialized
    /// code, so they are not reported as unpacked.
    pub fn install_imports(&mut self) {
        let slots: Vec<(u64, String)> = self
            .program
            .symbols
            .iter()
            .filter(|s| s.kind == crate::program::SymbolKind::Import && s.addr != 0)
            .map(|s| (s.addr, s.name.clone()))
            .collect();
        for (i, (slot, name)) in slots.into_iter().enumerate() {
            let stub = self.api_stub(i);
            self.plant(slot, stub, self.word);
            std::sync::Arc::make_mut(&mut self.apis).insert(stub, name);
        }
    }

    /// The synthetic address of the `index`th API stub, at the target's
    /// pointer width so an import slot holds all of it.
    ///
    /// # Arguments
    ///
    /// * `index` - The stub's ordinal among those handed out.
    fn api_stub(&self, index: usize) -> u64 {
        let base = if self.bitness == 32 {
            API_STUB_BASE_32
        } else {
            API_STUB_BASE
        };
        base.wrapping_add(from_usize(index) * 8)
    }

    /// The imported APIs and syscalls the run serviced, in order, each with
    /// its decoded arguments and result.
    #[must_use]
    pub fn api_calls(&self) -> &[ApiCall] {
        &self.calls
    }

    /// The byte at `a` only when a write or the image states it: zero
    /// backing left out, so a checker can tell a known byte from an
    /// untouched one.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    #[must_use]
    pub fn byte_stated(&self, a: u64) -> Option<u8> {
        self.mem.get(a).or_else(|| image_byte(self.program, a))
    }

    /// The most recent region the modeled allocator handed out, if any.
    #[must_use]
    pub fn last_alloc(&self) -> Option<u64> {
        self.allocs.last().map(|(base, _)| *base)
    }

    /// The names of the serviced calls, in order: the order and names a
    /// check compares and a count sums, without the decoded arguments.
    #[must_use]
    pub fn api_names(&self) -> Vec<&str> {
        self.calls.iter().map(|c| c.api.as_str()).collect()
    }

    /// Reads a printable string from memory as a load reads it, for decoding
    /// a string argument of a serviced call.
    ///
    /// # Arguments
    ///
    /// * `addr` - The pointer.
    /// * `wide` - Whether the characters are 16-bit.
    ///
    /// # Returns
    ///
    /// The text, or `None` when the address is zero, nothing is mapped, or
    /// no printable character is there ([`super::calls::read_text`]).
    fn read_memory_text(&self, addr: u64, wide: bool) -> Option<String> {
        super::calls::read_text(addr, wide, super::calls::TEXT_MAX, |a| self.byte_at(a))
    }

    /// Services a call that reached an imported function's stub.
    ///
    /// The run transferred to a synthetic stub address, so the call already
    /// pushed its return address; this models the API's effect on `rax` and
    /// hands back the address to resume at. Only the handful of APIs a packer
    /// leans on to stage its payload are modeled with intent (a memory
    /// allocator hands out a fresh region, or the address a `VirtualAlloc`
    /// asks for, a module lookup returns the image base); the rest return
    /// zero so the run continues and stops somewhere the output can name.
    ///
    /// # Arguments
    ///
    /// * `stub` - The stub address the call reached.
    ///
    /// # Returns
    ///
    /// The address to continue at: the caller's return address.
    ///
    /// # Errors
    ///
    /// A fault when the stack holds no return address to pop.
    pub(super) fn service_api(&mut self, stub: u64) -> Result<u64, Stop> {
        let full = self.apis.get(&stub).cloned().unwrap_or_default();
        let api = crate::analysis::bare_name(&full);
        let format = self.program.format;
        let bits = u8::try_from(self.bitness).unwrap_or(64);
        let caller = self.load(self.reg(Register::RSP), self.word).unwrap_or(0);
        let args = super::calls::decode_api_args(
            api,
            format,
            bits,
            |n| self.api_arg(n),
            |addr, wide| self.read_memory_text(addr, wide),
        );
        let void = super::calls::returns_void(api, format);
        let rcx = self.api_arg(0);
        let rv: u64 = if api.starts_with("GetModuleHandle") || api.starts_with("LoadLibrary") {
            self.program.image_base
        } else if api.starts_with("GetProcAddress") {
            let asked = self.api_arg(1);
            let key = self
                .read_memory_text(asked, false)
                .unwrap_or_else(|| format!("#{asked:#x}"));
            if let Some(&stub) = self.resolved.get(&key) {
                stub
            } else {
                let next = self.api_stub(self.apis.len());
                std::sync::Arc::make_mut(&mut self.apis).insert(next, format!("{full}:resolved"));
                self.resolved.insert(key, next);
                next
            }
        } else if api.starts_with("VirtualAlloc") || api == "HeapAlloc" || api == "malloc" {
            let requested = match api {
                "VirtualAlloc" => rcx,
                "VirtualAllocEx" => self.api_arg(1),
                _ => 0,
            };
            if requested == 0 {
                self.allocate()
            } else {
                requested
            }
        } else if api == "memcpy" || api == "memmove" {
            let (src, len) = (self.api_arg(1), self.api_arg(2));
            let len = usize::try_from(len).unwrap_or(0).min(API_COPY_MAX);
            let bytes: Vec<u8> = (0..len)
                .map(|k| self.byte(src.wrapping_add(from_usize(k))).unwrap_or(0))
                .collect();
            for (k, b) in bytes.into_iter().enumerate() {
                self.write(rcx.wrapping_add(from_usize(k)), u64::from(b), 1)?;
            }
            rcx
        } else if api == "memset" {
            let (dst, len) = (self.api_arg(1), self.api_arg(2));
            let len = usize::try_from(len).unwrap_or(0).min(API_COPY_MAX);
            let fill = lo8(rcx);
            for k in 0..len {
                self.write(dst.wrapping_add(from_usize(k)), u64::from(fill), 1)?;
            }
            rcx
        } else if api.starts_with("VirtualProtect")
            || api.starts_with("VirtualFree")
            || api == "AddVectoredExceptionHandler"
            || api == "RemoveVectoredExceptionHandler"
        {
            1
        } else {
            self.neutralize(api).unwrap_or_default()
        };
        self.set_reg(Register::RAX, rv);
        self.calls.push(ApiCall {
            api: api.to_owned(),
            syscall: None,
            args,
            ret: (!void).then_some(rv),
            caller,
        });
        let ret = self.pop()?;
        if self.bitness == 32 {
            use crate::analysis::prototypes::{arity, is_c_runtime, msvc_prototype};
            let dll = full.split_once('!').map_or("", |(d, _)| d);
            let popped = msvc_prototype(api)
                .map(|p| if p.callee_pops { p.params } else { 0 })
                .or_else(|| arity(api).filter(|_| !is_c_runtime(dll)))
                .unwrap_or(0);
            let sp = self
                .reg(Register::RSP)
                .wrapping_add(u64::from(popped) * from_usize(self.word));
            self.set_reg(Register::RSP, sp);
        }
        Ok(ret)
    }

    /// Hands out the region a modeled allocator returns.
    ///
    /// Regions are [`ALLOC_STRIDE`] apart, from the target's allocation base
    /// up to its API stubs, and step over the image wherever it sits in
    /// between, so no pointer handed out is one the image, the stubs or the
    /// scratch stack above them also answer for. A 32-bit target runs out
    /// after a few hundred regions, and the call then fails as the OS would.
    ///
    /// # Returns
    ///
    /// The region's base, or zero, the null pointer of a failed allocation,
    /// when no region is left below the stubs.
    pub(super) fn allocate(&mut self) -> u64 {
        let (base, sections) = (self.program.image_base, &self.program.sections);
        let start = sections.iter().map(|s| s.va.0).fold(base, u64::min);
        let end = sections
            .iter()
            .map(|s| s.va.0.saturating_add(s.vsize.max(s.file_size)))
            .fold(base, u64::max);
        let mut at = self.alloc_next;
        if at < end && at.saturating_add(ALLOC_STRIDE) > start {
            let Some(past) = end.checked_next_multiple_of(ALLOC_STRIDE) else {
                return 0;
            };
            at = past;
        }
        match at.checked_add(ALLOC_STRIDE) {
            Some(next) if next <= self.api_stub(0) => {
                self.alloc_next = next;
                self.allocs.push((at, next));
                at
            }
            _ => 0,
        }
    }

    /// Answers an anti-analysis query the way an unwatched process would.
    ///
    /// Every emulation feature dies the moment a target checks for a
    /// debugger: the run takes the detection path and reports on code that
    /// never executes in anger. These answers are the ones a process sees
    /// when nothing is attached, and each is recorded so the analyst learns
    /// the target's anti-analysis inventory as a side effect of running it.
    ///
    /// # Arguments
    ///
    /// * `api` - The imported function's bare name.
    ///
    /// # Returns
    ///
    /// The value to leave in `rax`, or `None` when the API is not one of
    /// these and the caller should apply its own default.
    fn neutralize(&mut self, api: &str) -> Option<u64> {
        let (rdx, r8, r9) = (self.api_arg(1), self.api_arg(2), self.api_arg(3));
        let rv = match api {
            "IsDebuggerPresent" => 0,
            "CheckRemoteDebuggerPresent" => {
                self.write_zeros(rdx, 4);
                1
            }
            "NtQueryInformationProcess" | "ZwQueryInformationProcess" => {
                self.write_zeros(r8, r9.min(64));
                0
            }
            "NtSetInformationThread" | "ZwSetInformationThread" => 0,
            "NtGetContextThread" | "ZwGetContextThread" | "GetThreadContext" => {
                self.write_zeros(rdx.wrapping_add(0x48), 0x30);
                1
            }
            "NtQuerySystemInformation" | "ZwQuerySystemInformation" => {
                self.write_zeros(rdx, r8.min(64));
                0
            }
            "OutputDebugStringA" | "OutputDebugStringW" => 0,
            _ => return None,
        };
        self.neutralized.insert(api.to_owned());
        Some(rv)
    }

    /// Writes `len` zero bytes at `addr`, bounded so a wild pointer cannot
    /// fill the map.
    ///
    /// # Arguments
    ///
    /// * `addr` - Where to write; a zero address writes nothing.
    /// * `len` - How many bytes, capped at 256.
    fn write_zeros(&mut self, addr: u64, len: u64) {
        if addr == 0 {
            return;
        }
        for k in 0..len.min(256) {
            self.mem.set(addr.wrapping_add(k), 0, false);
        }
    }

    /// Answers a `syscall` the way a kernel that runs nothing would.
    ///
    /// A `syscall` in an ELF is a numbered Linux kernel entry, `rax` the
    /// number and the arguments in `rdi`, `rsi`, `rdx`, `r10`, `r8` and `r9`
    /// (the x86-64 ABI), and full kernel emulation is out of scope. The
    /// honest static model is the loader's benign-answer pattern: `mmap`
    /// hands out one of the modeled allocator's regions (or honors a
    /// non-null hint, which the kernel is allowed to), `write` returns the
    /// count it was asked to write, and `exit`/`exit_group` end the program;
    /// every other number returns zero so the run continues, as an unlisted
    /// Windows API does. Each serviced call is recorded in order with its
    /// number, name and arguments ([`super::calls::decode_syscall_args`]), so a
    /// report names what the program asked the kernel for; it is not also
    /// one of the [`Emulator::neutralized`] answers, which a report lists
    /// apart, so each call is told once.
    ///
    /// # Arguments
    ///
    /// * `i` - The `syscall` instruction.
    ///
    /// # Returns
    ///
    /// `Ok(None)`: the kernel is modeled as returning, so execution falls
    /// through past the `syscall`.
    ///
    /// # Errors
    ///
    /// [`Stop::Exited`] for the exit numbers, which never return.
    pub(super) fn linux_syscall(&mut self, i: &Instruction) -> Result<Option<u64>, Stop> {
        let (nr, rdi, rdx) = (
            self.reg(Register::RAX),
            self.reg(Register::RDI),
            self.reg(Register::RDX),
        );
        let name = linux_syscall_name(nr);
        let api = name.map_or_else(|| format!("sys_{nr}"), ToOwned::to_owned);
        let args = name.map_or_else(Vec::new, |n| {
            super::calls::decode_syscall_args(
                n,
                u8::try_from(self.bitness).unwrap_or(64),
                |k| self.syscall_arg(k),
                |addr, wide| self.read_memory_text(addr, wide),
            )
        });
        let rv = match nr {
            9 => {
                if rdi == 0 {
                    self.allocate()
                } else {
                    rdi
                }
            }
            1 => rdx,
            60 | 231 => return Err(Stop::Exited),
            _ => 0,
        };
        self.set_reg(Register::RAX, rv);
        self.calls.push(ApiCall {
            api,
            syscall: Some(nr),
            args,
            ret: Some(rv),
            caller: i.ip(),
        });
        if self.bitness == 64 {
            self.set_reg(Register::RCX, i.next_ip());
            self.set_reg(Register::R11, self.rflags());
        }
        Ok(None)
    }

    /// Reads the `n`th argument of a Linux `syscall` from the register the
    /// kernel ABI puts it in.
    ///
    /// # Arguments
    ///
    /// * `n` - Argument index from zero.
    ///
    /// # Returns
    ///
    /// The register value, or zero past the sixth argument.
    fn syscall_arg(&self, n: usize) -> u64 {
        let regs = [
            Register::RDI,
            Register::RSI,
            Register::RDX,
            Register::R10,
            Register::R8,
            Register::R9,
        ];
        regs.get(n).map_or(0, |r| self.reg(*r))
    }

    /// The anti-analysis APIs this run answered benignly, in name order.
    #[must_use]
    pub fn neutralized(&self) -> Vec<&str> {
        self.neutralized.iter().map(String::as_str).collect()
    }
}
