//! Where a function ends: a call that returns or does not, the starts
//! that say which, a `hlt`, and the extents the file declares.
//!
//! A wrong end loses the code past it with no note, so each test states
//! which bytes are the function's and which are not. Every fixture is a
//! hand-assembled x64 ELF-shaped image: `.text` at 0x1000 and a `.got`
//! page at 0x2000 whose slots the imports fill.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::num::{from_usize, lo32, saturating_usize};
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};

use crate::decompiled::{decompiled, replays_clean};

/// Where `.got` starts: import `k` fills the slot at `GOT + 8 * k`.
const GOT: u64 = 0x2000;

/// Where the stub through the first slot sits in the fixtures that call
/// one import.
const STUB: u64 = 0x1000;

/// Builds the image: each piece of `code` at its address in `.text`, the
/// rest `int3`, entered at `entry`, with `imports` filling the `.got`
/// slots in order.
///
/// # Arguments
///
/// * `code` - Each piece of code with the address it starts at.
/// * `entry` - The entry point.
/// * `imports` - The imports' names, one slot each from [`GOT`].
fn image(code: &[(u64, Vec<u8>)], entry: u64, imports: &[&str]) -> Program {
    let mut bytes = vec![0xccu8; 0x1000];
    bytes.resize(0x2000, 0);
    for (at, b) in code {
        let off = saturating_usize(at - 0x1000);
        bytes[off..off + b.len()].copy_from_slice(b);
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(entry),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".got", GOT, 0x1000, 0x1000, false, false),
        ],
    );
    p.format = BinaryFormat::Elf;
    for (k, name) in (0u64..).zip(imports) {
        p.symbols.push(Symbol {
            name: (*name).to_owned(),
            addr: GOT + 8 * k,
            kind: SymbolKind::Import,
        });
    }
    p
}

/// Returns an instruction at `at` whose 32-bit displacement, its last four
/// bytes, reaches `to` from its end.
///
/// # Arguments
///
/// * `at` - Where the instruction starts.
/// * `op` - Its bytes before the displacement.
/// * `to` - The address the displacement reaches.
fn rel32(at: u64, op: &[u8], to: u64) -> Vec<u8> {
    let end = at + from_usize(op.len()) + 4;
    [op, &lo32(to.wrapping_sub(end)).to_le_bytes()].concat()
}

/// Returns `call to`, at `at`.
///
/// # Arguments
///
/// * `at` - Where the call starts.
/// * `to` - The callee.
fn call(at: u64, to: u64) -> Vec<u8> {
    rel32(at, &[0xe8], to)
}

/// Returns `jmp to` with a 32-bit displacement, at `at`.
///
/// # Arguments
///
/// * `at` - Where the jump starts.
/// * `to` - The target.
fn jmp(at: u64, to: u64) -> Vec<u8> {
    rel32(at, &[0xe9], to)
}

/// Returns `mov eax, n; ret`.
///
/// # Arguments
///
/// * `n` - The value returned.
fn returns(n: u8) -> Vec<u8> {
    vec![0xb8, n, 0x00, 0x00, 0x00, 0xc3]
}

/// Returns a procedure linkage table stub built for indirect-branch
/// tracking, at `at`: `endbr64; bnd jmp [rip+slot]`, eleven bytes.
///
/// # Arguments
///
/// * `at` - Where the stub starts.
/// * `slot` - The `.got` slot it jumps through.
fn ibt_stub(at: u64, slot: u64) -> Vec<u8> {
    let endbr64 = [0xf3, 0x0f, 0x1e, 0xfa];
    [&endbr64[..], &rel32(at + 4, &[0xf2, 0xff, 0x25], slot)].concat()
}

/// Builds an image where two functions call `callee` and a start that
/// only a jump's shape names lies right after one of the calls.
///
/// The entry `E` (0x1100) calls `H` (0x1200), `X` (0x1300) and `callee`,
/// then returns 1. `H` jumps to 0x1405, which opens with a `jmp` forward
/// and so reads as a thunk: the jump is taken as a tail call and 0x1405 as
/// a start. `X` calls `A` (0x1400), so `A` is walked once that start is
/// known: `A` calls `callee` and 0x1405 follows the call. `free` fills the
/// one slot, through the stub at [`STUB`].
///
/// # Arguments
///
/// * `callee` - What `E` and `A` call: [`STUB`], or 0x1500, a function
///   that saves a register and jumps to the stub, with no `ret` of its own.
fn after_a_shaped_start(callee: u64) -> Program {
    let mut code = vec![
        (STUB, ibt_stub(STUB, GOT)),
        (
            0x1100,
            [call(0x1100, 0x1200), call(0x1105, 0x1300)].concat(),
        ),
        (0x110a, [call(0x110a, callee), returns(1)].concat()),
        (0x1200, jmp(0x1200, 0x1405)),
        (0x1300, [call(0x1300, 0x1400), vec![0xc3]].concat()), // ASM: ret
        (0x1400, call(0x1400, callee)),
        (0x1405, jmp(0x1405, 0x1410)),
        (0x1410, returns(7)),
    ];
    if callee != STUB {
        code.push((callee, [vec![0x53, 0x5b], jmp(callee + 2, STUB)].concat())); // ASM: push rbx; pop rbx
    }
    image(&code, 0x1100, &["free"])
}

/// A start only a jump's shape names, right after a call to `free`'s IBT
/// stub, leaves the stub returning, and the other caller keeps its code
/// after its call.
///
/// rsyslogd's `asyncWriterThread` jumps to an `-O0` block that opens with
/// a `jmp`, and that block was taken as a function; walked again, its call
/// to `pthread_mutex_lock` landed on it, and the stub, `endbr64; bnd jmp
/// [slot]`, was taken never to return, since the check stopped at the
/// `endbr64`. 187 functions in twelve binaries ended at a call to `free`,
/// `pthread_mutex_lock` or `error`, `hdlr_sighup` after its first line.
#[test]
fn a_start_a_jump_names_after_a_call_leaves_the_stub_returning() {
    let p = after_a_shaped_start(STUB);
    let a = Analysis::compute(&p);
    let e = a.function(0x1100).unwrap();
    assert_eq!(e.end, 0x1115, "the entry ended at its call: {e:?}");
    assert!(!a.noreturn.contains(&STUB), "{:?}", a.noreturn);
    let text = decompiled(&p, 0x1100);
    assert!(text.contains("return 1;"), "{text}");
}

/// The same start is no evidence that a callee with no `ret` of its own
/// never returns.
///
/// The callee returns through its tail call. Only a start the file
/// declares or a call reaches says the call before it never returns.
#[test]
fn a_start_a_jump_names_after_a_call_is_no_evidence_it_never_returns() {
    let p = after_a_shaped_start(0x1500);
    let a = Analysis::compute(&p);
    let e = a.function(0x1100).unwrap();
    assert_eq!(e.end, 0x1115, "the entry ended at its call: {e:?}");
    assert!(!a.noreturn.contains(&0x1500), "{:?}", a.noreturn);
}

/// glibc's `error` returns unless its status is a nonzero constant, behind
/// an IBT stub too, even where a declared start follows a status-1 call.
///
/// `D` (0x1200) passes status 1 and the next function's symbol follows its
/// call, the way GCC lays out a call it knows does not return; `C`
/// (0x1300) passes the status it was handed and returns 5. `D` ends at its
/// call, `C` keeps its code past it, and the stub is not taken never to
/// return.
#[test]
fn error_returns_unless_its_status_is_a_nonzero_constant() {
    let code = vec![
        (STUB, ibt_stub(STUB, GOT)),
        (
            0x1100,
            [call(0x1100, 0x1200), call(0x1105, 0x1300), vec![0xc3]].concat(), // ASM: ret
        ),
        (0x1200, vec![0xbf, 0x01, 0x00, 0x00, 0x00, 0x31, 0xf6]), // ASM: mov edi, 1; xor esi, esi
        (0x1207, call(0x1207, STUB)),
        (0x120c, vec![0x31, 0xc0, 0xc3]), // ASM: xor eax, eax; ret
        (0x1300, vec![0x89, 0xf7]),       // ASM: mov edi, esi
        (0x1302, [call(0x1302, STUB), returns(5)].concat()),
    ];
    let mut p = image(&code, 0x1100, &["error"]);
    p.symbols.push(Symbol {
        name: "after_error".to_owned(),
        addr: 0x120c,
        kind: SymbolKind::Local,
    });
    let a = Analysis::compute(&p);
    let d = a.function(0x1200).unwrap();
    assert_eq!(d.end, 0x120c, "the status-1 call returned: {d:?}");
    let c = a.function(0x1300).unwrap();
    assert_eq!(c.end, 0x130d, "the call with a handed status ended: {c:?}");
    assert!(!a.noreturn.contains(&STUB), "{:?}", a.noreturn);
    let text = decompiled(&p, 0x1300);
    assert!(text.contains("return 5;"), "{text}");
}

/// A function whose one way out is glibc's `error` with status 1 never
/// returns, so its callers end at their calls to it.
///
/// find's `fatal_nontarget_file_error` is this shape. It was taken never to
/// return only from a start split off after some caller's call to it, and
/// with no such start a caller ran on past its call into the padding.
#[test]
fn a_function_whose_way_out_is_a_status_1_error_never_returns() {
    let code = vec![
        (STUB, ibt_stub(STUB, GOT)),
        (0x1100, [call(0x1100, 0x1300), vec![0xc3]].concat()), // ASM: ret
        (0x1200, vec![0xbf, 0x01, 0x00, 0x00, 0x00, 0x31, 0xf6]), // ASM: mov edi, 1; xor esi, esi
        (0x1207, call(0x1207, STUB)),
        (0x1300, [call(0x1300, 0x1200), returns(5)].concat()),
    ];
    let p = image(&code, 0x1100, &["error"]);
    let a = Analysis::compute(&p);
    assert!(a.noreturn.contains(&0x1200), "{:?}", a.noreturn);
    let c = a.function(0x1300).unwrap();
    assert_eq!(c.end, 0x1305, "the caller ran past its call: {c:?}");
}

/// Calls that never return still end their callers' paths.
///
/// They reach `exit`, `abort` and `__stack_chk_fail` behind IBT stubs, and
/// a function of the program whose one way out is a call to `exit`: the
/// code after each call is not the caller's.
#[test]
fn calls_that_never_return_still_end_their_callers() {
    let code = vec![
        (0x1000, ibt_stub(0x1000, GOT)),
        (0x1010, ibt_stub(0x1010, GOT + 8)),
        (0x1020, ibt_stub(0x1020, GOT + 16)),
        (0x1080, [vec![0x53], call(0x1081, 0x1000)].concat()), // ASM: push rbx
        (
            0x1100,
            [call(0x1100, 0x1200), call(0x1105, 0x1300)].concat(),
        ),
        (
            0x110a,
            [call(0x110a, 0x1400), call(0x110f, 0x1500), vec![0xc3]].concat(), // ASM: ret
        ),
        (0x1200, vec![0x31, 0xff]), // ASM: xor edi, edi
        (0x1202, [call(0x1202, 0x1000), returns(1)].concat()),
        (0x1300, [call(0x1300, 0x1010), returns(2)].concat()),
        (0x1400, [call(0x1400, 0x1020), returns(3)].concat()),
        (0x1500, [call(0x1500, 0x1080), returns(4)].concat()),
    ];
    let p = image(&code, 0x1100, &["exit", "abort", "__stack_chk_fail"]);
    let a = Analysis::compute(&p);
    for (caller, end) in [
        (0x1200, 0x1207),
        (0x1300, 0x1305),
        (0x1400, 0x1405),
        (0x1500, 0x1505),
    ] {
        let f = a.function(caller).unwrap();
        assert_eq!(f.end, end, "{caller:#x} ran past its call: {f:?}");
    }
    assert!(a.noreturn.contains(&0x1080), "{:?}", a.noreturn);
}

/// Calls that end a thread or fail a check end their callers' paths too,
/// behind IBT stubs.
///
/// rsyslogd's `wtpWorker` and `thrdStarter` ran on past their calls to
/// `pthread_exit`, which no name marked: since the walk skips a stub's
/// `endbr64`, the stub was a jump through a slot that returns. newlib's
/// `__assert` ran on past `__assert_func` into the next function, and
/// `RtlExitUserThread` is the call kernel32's thread exits make.
#[test]
fn calls_that_end_a_thread_or_fail_a_check_end_their_callers() {
    for name in [
        "pthread_exit",
        "thrd_exit",
        "__chk_fail",
        "__fortify_fail",
        "__assert_perror_fail",
        "__assert",
        "__assert_func",
        "RtlExitUserProcess",
        "RtlExitUserThread",
    ] {
        let code = vec![
            (STUB, ibt_stub(STUB, GOT)),
            (0x1100, [call(0x1100, 0x1200), vec![0xc3]].concat()), // ASM: ret
            (0x1200, vec![0x31, 0xff]),                            // ASM: xor edi, edi
            (0x1202, [call(0x1202, STUB), returns(1)].concat()),
        ];
        let a = Analysis::compute(&image(&code, 0x1100, &[name]));
        let f = a.function(0x1200).unwrap();
        assert_eq!(f.end, 0x1207, "{name}: the caller ran past its call: {f:?}");
    }
}

/// Builds glibc's `_start`, with headers that say nothing of the image's
/// kind.
///
/// It passes `main` to `__libc_start_main`, which never returns, and a
/// `hlt` after the call crashes the process should it ever do so; a
/// ten-byte `nop` aligns the next function, which follows.
fn glibc_start() -> Program {
    let code = vec![
        (
            0x1000,
            vec![
                0xf3, 0x0f, 0x1e, 0xfa, // ASM: endbr64
                0x31, 0xed, // ASM: xor ebp, ebp
                0x49, 0x89, 0xd1, // ASM: mov r9, rdx
                0x5e, // ASM: pop rsi
                0x48, 0x89, 0xe2, // ASM: mov rdx, rsp
                0x48, 0x83, 0xe4, 0xf0, // ASM: and rsp, -16
                0x50, // ASM: push rax
                0x54, // ASM: push rsp
                0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
                0x31, 0xc9, // ASM: xor ecx, ecx
            ],
        ),
        (0x1018, rel32(0x1018, &[0x48, 0x8d, 0x3d], 0x1100)), // ASM: lea rdi, [rip+main]
        (0x101f, rel32(0x101f, &[0xff, 0x15], GOT)),          // ASM: call [rip+__libc_start_main]
        (0x1025, vec![0xf4]),                                 // ASM: hlt
        (0x1026, vec![0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0]), // ASM: nop word cs:[rax+rax]
        (0x1030, vec![0x31, 0xc0, 0xc3]),                     // ASM: xor eax, eax; ret
        (0x1100, vec![0x31, 0xc0, 0xc3]),                     // ASM: xor eax, eax; ret
    ];
    let mut p = image(&code, 0x1000, &["__libc_start_main"]);
    p.symbols.push(Symbol {
        name: "deregister_tm_clones".to_owned(),
        addr: 0x1030,
        kind: SymbolKind::Local,
    });
    p
}

/// `_start` ends at its `hlt` wherever the headers say the image runs in
/// user mode, where the instruction faults and nothing after it runs.
///
/// That is a position-independent executable, one with a program
/// interpreter, and a PE for a Windows subsystem. The walk read on through
/// the alignment `nop` to the next function, and the text ended in
/// `goto *0x1030;` after `__halt();`, as 203 `_start`s of the benchmark's
/// x64 binaries did.
#[test]
fn start_ends_at_its_hlt() {
    let user_modes: [fn(&mut Program); 3] = [
        |p| p.headers.kind = Some("ET_DYN (pie)"),
        |p| {
            p.headers.kind = Some("ET_EXEC");
            p.headers.interpreter = Some("/lib64/ld-linux-x86-64.so.2".to_owned());
        },
        |p| {
            p.format = BinaryFormat::Pe;
            p.headers.subsystem = Some("console");
        },
    ];
    for (k, set) in user_modes.iter().enumerate() {
        let mut p = glibc_start();
        set(&mut p);
        let a = Analysis::compute(&p);
        let f = a.function(0x1000).unwrap();
        assert_eq!(f.end, 0x1026, "headers {k}: {f:?}");
        assert!(
            a.function(0x1030).is_some(),
            "headers {k}: {:?}",
            a.functions
        );
        let text = decompiled(&p, 0x1000);
        assert!(text.contains("__halt();"), "headers {k}: {text}");
        assert!(!text.contains("goto"), "headers {k}: {text}");
        replays_clean(&p, &a, &[0x1000]);
    }
}

/// `hlt` runs on where no header says the image runs in user mode: a
/// kernel or firmware waits there for an interrupt and then goes on, as
/// the Linux kernel's idle loop returns after its `sti; hlt`.
#[test]
fn hlt_runs_on_where_no_header_says_user_mode() {
    let code = vec![
        (0x1000, [call(0x1000, 0x1100), returns(1)].concat()),
        (0x1100, vec![0xf3, 0x0f, 0x1e, 0xfa, 0xfb, 0xf4, 0xc3]), // ASM: endbr64; sti; hlt; ret
    ];
    let mut p = image(&code, 0x1000, &[]);
    p.headers.kind = Some("ET_EXEC");
    let a = Analysis::compute(&p);
    assert!(!a.noreturn.contains(&0x1100), "{:?}", a.noreturn);
    assert_eq!(a.function(0x1100).unwrap().end, 0x1107);
    assert_eq!(a.function(0x1000).unwrap().end, 0x100b);
}

/// Builds functions whose unwind entries declare their extents, each with
/// a jump inside it that reads as a tail call by its target's shape.
///
/// `F` (0x1100..0x114a) is `-O0` code for a loop around a switch: each
/// case ends `jmp` to the switch's end, a block that is one `jmp` on to
/// the loop's step, and a `jmp` there reads as a thunk. `G`
/// (0x1200..0x1213) jumps to its `abort` call, `sub rsp, 8; call abort`,
/// which opens the way a frame does. `H` (0x1300..0x1307) tail-calls `K`
/// (0x1340..0x1344), a leaf whose start only its extent declares; `abort`
/// fills the one slot, through the stub at [`STUB`].
fn declared() -> Program {
    let code = vec![
        (STUB, ibt_stub(STUB, GOT)),
        (
            0x1100,
            vec![
                0x55, // ASM: push rbp
                0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
                0xc7, 0x45, 0xfc, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [rbp-4], 0
                0xc7, 0x45, 0xf8, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [rbp-8], 0
            ],
        ),
        (0x1112, jmp(0x1112, 0x113f)),
        (
            0x1117,
            vec![
                0x8b, 0x45, 0xfc, // ASM: mov eax, [rbp-4]
                0x83, 0xf8, 0x01, // ASM: cmp eax, 1
                0x74, 0x0a, // ASM: je 0x1129
                0x83, 0xf8, 0x02, // ASM: cmp eax, 2
                0x74, 0x0e, // ASM: je 0x1132
            ],
        ),
        (0x1124, jmp(0x1124, 0x113b)),
        (0x1129, vec![0x83, 0x45, 0xf8, 0x01]), // ASM: add dword [rbp-8], 1
        (0x112d, jmp(0x112d, 0x1124)),
        (0x1132, vec![0x83, 0x6d, 0xf8, 0x01]), // ASM: sub dword [rbp-8], 1
        (0x1136, jmp(0x1136, 0x1124)),
        (
            0x113b,
            vec![
                0x83, 0x45, 0xfc, 0x01, // ASM: add dword [rbp-4], 1
                0x83, 0x7d, 0xfc, 0x09, // ASM: cmp dword [rbp-4], 9
                0x7e, 0xd2, // ASM: jle 0x1117
                0x8b, 0x45, 0xf8, // ASM: mov eax, [rbp-8]
                0x5d, // ASM: pop rbp
                0xc3, // ASM: ret
            ],
        ),
        (
            0x1200,
            vec![
                0x48, 0x85, 0xff, // ASM: test rdi, rdi
                0x75, 0x02, // ASM: jne 0x1207
                0xeb, 0x03, // ASM: jmp 0x120a
                0x8b, 0x07, // ASM: mov eax, [rdi]
                0xc3, // ASM: ret
                0x48, 0x83, 0xec, 0x08, // ASM: sub rsp, 8
            ],
        ),
        (0x120e, call(0x120e, STUB)),
        (0x1300, [vec![0x89, 0xf8], jmp(0x1302, 0x1340)].concat()), // ASM: mov eax, edi
        (0x1340, vec![0x83, 0xc0, 0x01, 0xc3]),                     // ASM: add eax, 1; ret
    ];
    let mut p = image(&code, 0x1100, &["abort"]);
    p.function_ranges = vec![
        (0x1100, 0x114a),
        (0x1200, 0x1213),
        (0x1300, 0x1307),
        (0x1340, 0x1344),
    ];
    p
}

/// A jump inside the extent an unwind entry declares stays the function's
/// own, whatever its target opens with.
///
/// `F`'s cases jumped to a `jmp` and `G` to its `abort` call; each was
/// read as a tail call, so `F` ended its loop in `return sub_1124();` and
/// `G` called a `sub_120a` that only aborts, as 914 x64 functions of the
/// benchmark's tree split inside their own unwind entries.
#[test]
fn a_jump_inside_a_declared_extent_stays_the_functions_own() {
    let p = declared();
    let a = Analysis::compute(&p);
    for (entry, end, piece) in [(0x1100, 0x114a, "sub_1124"), (0x1200, 0x1213, "sub_120a")] {
        let f = a.function(entry).unwrap();
        assert_eq!(f.end, end, "{entry:#x} split: {f:?}");
        let inside: Vec<u64> = a
            .functions
            .iter()
            .map(|g| g.entry)
            .filter(|&g| g > entry && g < end)
            .collect();
        assert!(inside.is_empty(), "{entry:#x} split at {inside:x?}");
        let text = decompiled(&p, entry);
        assert!(!text.contains(piece), "{text}");
    }
    let text = decompiled(&p, 0x1200);
    assert!(text.contains("abort()"), "{text}");
}

/// A jump to the start of another declared extent stays a tail call, though
/// its target opens like no function: the extent says one starts there.
#[test]
fn a_jump_to_another_declared_start_stays_a_tail_call() {
    let p = declared();
    let a = Analysis::compute(&p);
    let h = a.function(0x1300).unwrap();
    assert_eq!(h.end, 0x1307, "{h:?}");
    assert!(h.callees.contains(&0x1340), "{h:?}");
    assert!(a.function(0x1340).is_some(), "{:?}", a.functions);
}
