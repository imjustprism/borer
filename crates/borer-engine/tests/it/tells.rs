//! Anti-analysis labels that depend on the instructions around them.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Symbol, SymbolKind};

use crate::raw::image;

fn report(code: &[u8]) -> String {
    let p = image(Arch::X86_64, code, &[]);
    let a = Analysis::compute(&p);
    borer_engine::analysis::render::anti_analysis_tsv(&p, &a, &Overlay::default())
}

/// One `cpuid` and one `rdtsc` are a feature probe and a read. A hypervisor
/// leaf and a subtracted pair are the probes the old labels claimed for every
/// one of them.
#[test]
fn cpuid_and_rdtsc_are_labeled_by_what_the_code_does() {
    let probe = report(&[
        0x0f, 0xa2, // ASM: cpuid
        0x0f, 0x31, // ASM: rdtsc
        0xc3, // ASM: ret
    ]);
    assert!(probe.contains("cpuid (feature probe)"), "{probe}");
    assert!(probe.contains("rdtsc (read)"), "{probe}");
    assert!(!probe.starts_with("# anti-analysis:"), "{probe}");
    let hyper = report(&[
        0xb8, 0x00, 0x00, 0x00, 0x40, // ASM: mov eax, 0x40000000
        0x0f, 0xa2, // ASM: cpuid
        0xc3, // ASM: ret
    ]);
    assert!(hyper.contains("cpuid (hypervisor probe)"), "{hyper}");
    let timing = report(&[
        0x0f, 0x31, // ASM: rdtsc
        0x89, 0xc1, // ASM: mov ecx, eax
        0x0f, 0x31, // ASM: rdtsc
        0x29, 0xc8, // ASM: sub eax, ecx
        0x3d, 0xff, 0x0f, 0x00, 0x00, // ASM: cmp eax, 0xfff
        0x72, 0x01, // ASM: jb 0x40100f
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ]);
    assert!(timing.contains("rdtsc (timing)"), "{timing}");
    assert!(!timing.contains("rdtsc (read)"), "{timing}");
}

/// A bare `in` is a port read. The `VMware` backdoor is the `VMXh` magic.
#[test]
fn a_bare_in_is_a_port_read_and_the_backdoor_magic_is_named() {
    let bare = report(&[
        0x31, 0xc0, // ASM: xor eax, eax
        0xed, // ASM: in eax, dx
        0xc3, // ASM: ret
    ]);
    assert!(bare.contains("in (port read)"), "{bare}");
    assert!(!bare.contains("VMware"), "{bare}");
    assert!(!bare.starts_with("# anti-analysis:"), "{bare}");
    let backdoor = report(&[
        0xb8, 0x68, 0x58, 0x4d, 0x56, // ASM: mov eax, 0x564d5868
        0xed, // ASM: in eax, dx
        0xc3, // ASM: ret
    ]);
    assert!(backdoor.contains("in (VMware backdoor port)"), "{backdoor}");
}

/// `int 2dh` is its own strong tell and tips the verdict by itself.
#[test]
fn int_2dh_tips_the_verdict() {
    let text = report(&[
        0x31, 0xc0, // ASM: xor eax, eax
        0xcd, 0x2d, // ASM: int 0x2d
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("int 2dh"), "{text}");
    assert!(text.starts_with("# anti-analysis:"), "{text}");
}

/// `CheckRemoteDebuggerPresent` tips the verdict with no other tell.
/// `IsDebuggerPresent` does not.
#[test]
fn one_real_anti_debug_import_tips_and_the_runtime_one_does_not() {
    let build = |import: &str| {
        let mut p = image(Arch::X86_64, &[0xc3], &[]);
        p.symbols.push(Symbol {
            name: format!("KERNEL32.dll!{import}"),
            addr: 0x402000,
            kind: SymbolKind::Import,
        });
        let a = Analysis::compute(&p);
        borer_engine::analysis::render::anti_analysis_tsv(&p, &a, &Overlay::default())
    };
    let remote = build("CheckRemoteDebuggerPresent");
    assert!(remote.starts_with("# anti-analysis:"), "{remote}");
    let runtime = build("IsDebuggerPresent");
    assert!(!runtime.starts_with("# anti-analysis:"), "{runtime}");
}

/// `fs:[0x30]` is a PEB read and not a named field. `fs:[0x18]` then a
/// stack-base read is not a PEB read.
#[test]
fn a_peb_read_is_a_tell_and_the_teb_stack_base_is_not() {
    let peb = report(&[
        0x64, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov eax, fs:[0x30]
        0xc3, // ASM: ret
    ]);
    assert!(peb.contains("peb read"), "{peb}");
    assert!(!peb.contains("BeingDebugged"), "{peb}");
    assert!(peb.starts_with("# anti-analysis:"), "{peb}");
    let stack = report(&[
        0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, // ASM: mov eax, fs:[0x18]
        0x8b, 0x40, 0x04, // ASM: mov eax, [eax+4]
        0xc3, // ASM: ret
    ]);
    assert!(!stack.contains("peb read"), "{stack}");
}

/// A byte at `+2` is `BeingDebugged`. `+0x68` and `+0xBC` are `NtGlobalFlag`.
/// An `Ldr` walk stays a plain PEB read.
#[test]
fn a_peb_field_is_named_from_the_following_read() {
    let debugged = report(&[
        0x64, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov eax, fs:[0x30]
        0x8a, 0x40, 0x02, // ASM: mov al, [eax+2]
        0xc3, // ASM: ret
    ]);
    assert!(debugged.contains("peb read (BeingDebugged)"), "{debugged}");
    let teb = report(&[
        0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, // ASM: mov eax, fs:[0x18]
        0x8b, 0x40, 0x30, // ASM: mov eax, [eax+0x30]
        0x0f, 0xb6, 0x40, 0x02, // ASM: movzx eax, byte [eax+2]
        0xc3, // ASM: ret
    ]);
    assert!(teb.contains("peb read (BeingDebugged)"), "{teb}");
    let flag32 = report(&[
        0x64, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov eax, fs:[0x30]
        0x8b, 0x80, 0x68, 0x00, 0x00, 0x00, // ASM: mov eax, [eax+0x68]
        0xc3, // ASM: ret
    ]);
    assert!(flag32.contains("peb read (NtGlobalFlag)"), "{flag32}");
    assert!(!flag32.contains("BeingDebugged"), "{flag32}");
    let flag64 = report(&[
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x60, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[0x60]
        0x8b, 0x80, 0xbc, 0x00, 0x00, 0x00, // ASM: mov eax, [rax+0xbc]
        0xc3, // ASM: ret
    ]);
    assert!(flag64.contains("peb read (NtGlobalFlag)"), "{flag64}");
    let ldr = report(&[
        0x64, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov eax, fs:[0x30]
        0x8b, 0x40, 0x0c, // ASM: mov eax, [eax+0x0c]
        0xc3, // ASM: ret
    ]);
    assert!(ldr.contains("peb read"), "{ldr}");
    assert!(!ldr.contains("BeingDebugged"), "{ldr}");
    assert!(!ldr.contains("NtGlobalFlag"), "{ldr}");
    let wide = report(&[
        0x64, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov eax, fs:[0x30]
        0x8b, 0x40, 0x02, // ASM: mov eax, [eax+2]
        0xc3, // ASM: ret
    ]);
    assert!(wide.contains("peb read"), "{wide}");
    assert!(!wide.contains("BeingDebugged"), "{wide}");
}

/// `mov dr0` inside a function is a hardware-breakpoint tell.
#[test]
fn a_debug_register_move_is_a_tell() {
    let text = report(&[
        0x0f, 0x23, 0xc0, // ASM: mov dr0, rax
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("hardware breakpoint"), "{text}");
}

/// Builds a report whose code calls the named imports.
fn report_calls(code: &[u8], data: &[u8], imports: &[(&str, u64)]) -> String {
    let mut p = image(Arch::X86_64, code, data);
    for (name, addr) in imports {
        p.symbols.push(Symbol {
            name: format!("KERNEL32.dll!{name}"),
            addr: *addr,
            kind: SymbolKind::Import,
        });
    }
    let a = Analysis::compute(&p);
    borer_engine::analysis::render::anti_analysis_tsv(&p, &a, &Overlay::default())
}

/// `GetThreadContext` is a hardware-breakpoint tell only beside the debug-register flags.
#[test]
fn get_thread_context_needs_the_debug_register_flags() {
    let flagged = report_calls(
        &[
            0xb8, 0x10, 0x00, 0x01, 0x00, // ASM: mov eax, 0x10010
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(flagged.contains("GetThreadContext"), "{flagged}");
    let plain = report_calls(
        &[
            0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!plain.contains("hardware breakpoint"), "{plain}");
}

/// `FindWindow` of a debugger class, followed by an exit, is a tell.
/// An ordinary class is not.
#[test]
fn a_debugger_window_is_named_and_an_ordinary_class_is_not() {
    let mut olly = vec![0u8; 0x108];
    olly[0x100..0x107].copy_from_slice(b"OLLYDBG");
    let code = [
        0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
        0xe8, 0x06, 0x10, 0x00, 0x00, // ASM: call 0x402010
        0x68, 0x00, 0x21, 0x40, 0x00, // ASM: push 0x402100
        0xc3, // ASM: ret
    ];
    let text = report_calls(
        &code,
        &olly,
        &[("FindWindowA", 0x402000), ("ExitProcess", 0x402010)],
    );
    assert!(text.contains("debugger window"), "{text}");
    assert!(text.starts_with("# anti-analysis:"), "{text}");
    let mut ordinary = vec![0u8; 0x108];
    ordinary[0x100..0x107].copy_from_slice(b"NOTEPAD");
    let text = report_calls(
        &code,
        &ordinary,
        &[("FindWindowA", 0x402000), ("ExitProcess", 0x402010)],
    );
    assert!(!text.contains("debugger window"), "{text}");
}

/// Creating a process and waiting on a debug event is a debug block.
#[test]
fn a_debug_process_block_is_a_tell() {
    let code = [
        0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
        0xe8, 0x06, 0x10, 0x00, 0x00, // ASM: call 0x402010
        0xc3, // ASM: ret
    ];
    let text = report_calls(
        &code,
        &[],
        &[
            ("CreateProcessA", 0x402000),
            ("WaitForDebugEvent", 0x402010),
        ],
    );
    assert!(text.contains("debug block"), "{text}");
    assert!(text.starts_with("# anti-analysis:"), "{text}");
    let alone = report_calls(
        &[
            0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("CreateProcessA", 0x402000)],
    );
    assert!(!alone.contains("debug block"), "{alone}");
}

/// A loop that compares with `0xCC` and then exits is a breakpoint scan.
/// The compare alone is not, and a compare followed by a store into
/// executable memory is a patch.
#[test]
fn a_breakpoint_scan_needs_a_loop_and_an_exit() {
    let scan = report_calls(
        &[
            0x3c, 0xcc, // ASM: cmp al, 0xcc
            0x75, 0xfc, // ASM: jne 0x401000
            0xe8, 0xf7, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("ExitProcess", 0x402000)],
    );
    assert!(scan.contains("breakpoint scan"), "{scan}");
    assert!(scan.starts_with("# anti-analysis:"), "{scan}");
    let compare = report(&[
        0x3c, 0xcc, // ASM: cmp al, 0xcc
        0x75, 0xfc, // ASM: jne 0x401000
        0xc3, // ASM: ret
    ]);
    assert!(!compare.contains("breakpoint"), "{compare}");
    let patch = report(&[
        0x31, 0xc0, // ASM: xor eax, eax
        0x3c, 0xcc, // ASM: cmp al, 0xcc
        0xc6, 0x04, 0x25, 0x00, 0x10, 0x40, 0x00, 0x90, // ASM: mov byte [0x401000], 0x90
        0xc3, // ASM: ret
    ]);
    assert!(patch.contains("breakpoint patch"), "{patch}");
}

/// An exception filter over an illegal opcode is a tell.
///
/// The call alone is not, and neither is the bad instruction when its
/// address is not executable.
#[test]
fn an_exception_filter_over_an_illegal_opcode_is_a_tell() {
    let trap = [
        0xb9, 0x30, 0x10, 0x40, 0x00, // ASM: mov ecx, 0x401030
        0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
        0xf0, 0xf0, 0xc7, 0xc8, // ASM: two lock prefixes, not an instruction
        0xeb, 0x01, // ASM: jmp short +1
        0x6e, // ASM: outsb, skipped
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let text = report_calls(&trap, &[], &[("SetUnhandledExceptionFilter", 0x402000)]);
    assert!(text.contains("illegal opcode"), "{text}");
    assert!(text.starts_with("# anti-analysis:"), "{text}");
    let plain = report_calls(
        &[
            0xb9, 0x30, 0x10, 0x40, 0x00, // ASM: mov ecx, 0x401030
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("SetUnhandledExceptionFilter", 0x402000)],
    );
    assert!(!plain.contains("illegal opcode"), "{plain}");
    assert!(!plain.starts_with("# anti-analysis:"), "{plain}");
    let data = report_calls(
        &[
            0xb9, 0x00, 0x21, 0x40, 0x00, // ASM: mov ecx, 0x402100
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xf0, 0xf0, 0xc7, 0xc8, // ASM: two lock prefixes, not an instruction
            0xeb, 0x01, // ASM: jmp short +1
            0x6e, // ASM: outsb, skipped
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
        ],
        &[],
        &[("SetUnhandledExceptionFilter", 0x402000)],
    );
    assert!(!data.contains("illegal opcode"), "{data}");
}
