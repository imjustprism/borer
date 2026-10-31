//! Anti-analysis labels that depend on the instructions around them.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Symbol, SymbolKind};
use iced_x86::{Decoder, DecoderOptions, Mnemonic, Register};

use crate::raw::image;

fn report(code: &[u8]) -> String {
    let p = image(Arch::X86_64, code, &[]);
    let a = Analysis::compute(&p);
    borer_engine::analysis::render::anti_analysis_tsv(&p, &a, &Overlay::default())
}

/// Returns the first instruction's mnemonic, segment, base, index, and displacement.
fn segment_slot(code: &[u8]) -> (Mnemonic, Register, Register, Register, u64) {
    let i = Decoder::with_ip(64, code, 0x401000, DecoderOptions::NONE).decode();
    (
        i.mnemonic(),
        i.segment_prefix(),
        i.memory_base(),
        i.memory_index(),
        i.memory_displacement64(),
    )
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

/// `sub eax, eax` clears the timestamp. A compare of another register is
/// not a timing check, so both reads stay plain reads.
#[test]
fn a_cleared_timestamp_is_a_read() {
    let text = report(&[
        0x0f, 0x31, // ASM: rdtsc
        0x0f, 0x31, // ASM: rdtsc
        0x29, 0xc0, // ASM: sub eax, eax
        0x83, 0xf9, 0x01, // ASM: cmp ecx, 1
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("rdtsc (read)"), "{text}");
    assert!(!text.contains("rdtsc (timing)"), "{text}");
}

/// A leaf overwritten before `cpuid` is not a hypervisor probe.
///
/// A test of `ecx` against the hypervisor bit is. A test of another
/// register is not.
#[test]
fn a_replaced_leaf_is_not_a_hypervisor_probe() {
    let replaced = report(&[
        0xb8, 0x00, 0x00, 0x00, 0x40, // ASM: mov eax, 0x40000000
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x0f, 0xa2, // ASM: cpuid
        0xc3, // ASM: ret
    ]);
    assert!(replaced.contains("cpuid (feature probe)"), "{replaced}");
    assert!(!replaced.contains("hypervisor"), "{replaced}");
    let bit = report(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x0f, 0xa2, // ASM: cpuid
        0xf7, 0xc1, 0x00, 0x00, 0x00, 0x80, // ASM: test ecx, 0x80000000
        0xc3, // ASM: ret
    ]);
    assert!(bit.contains("cpuid (hypervisor probe)"), "{bit}");
    let other = report(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x0f, 0xa2, // ASM: cpuid
        0xf7, 0xc2, 0x00, 0x00, 0x00, 0x80, // ASM: test edx, 0x80000000
        0xc3, // ASM: ret
    ]);
    assert!(other.contains("cpuid (feature probe)"), "{other}");
    assert!(!other.contains("hypervisor"), "{other}");
}

/// Leaf 7's top `ecx` bit is a feature, not the hypervisor bit.
#[test]
fn a_feature_leaf_bit_is_not_a_hypervisor_probe() {
    let text = report(&[
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax, 7
        0x0f, 0xa2, // ASM: cpuid
        0xf7, 0xc1, 0x00, 0x00, 0x00, 0x80, // ASM: test ecx, 0x80000000
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("cpuid (feature probe)"), "{text}");
    assert!(!text.contains("hypervisor"), "{text}");
}

/// `ecx` overwritten before the hypervisor-bit test is a feature probe.
#[test]
fn a_cleared_hypervisor_bit_is_a_feature_probe() {
    let text = report(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x0f, 0xa2, // ASM: cpuid
        0x31, 0xc9, // ASM: xor ecx, ecx
        0xf7, 0xc1, 0x00, 0x00, 0x00, 0x80, // ASM: test ecx, 0x80000000
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("cpuid (feature probe)"), "{text}");
    assert!(!text.contains("hypervisor"), "{text}");
}

/// `bt ecx, 31` after leaf 1 is the hypervisor bit. The same bit test after
/// leaf 7 is a feature. `bt edx, 31`, `test ecx, 31`, and `cmp ecx, 31` are
/// not that bit.
#[test]
fn a_bit_test_of_ecx_is_the_hypervisor_bit() {
    let bit = report(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x0f, 0xa2, // ASM: cpuid
        0x0f, 0xba, 0xe1, 0x1f, // ASM: bt ecx, 31
        0xc3, // ASM: ret
    ]);
    assert!(bit.contains("cpuid (hypervisor probe)"), "{bit}");
    let leaf = report(&[
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax, 7
        0x0f, 0xa2, // ASM: cpuid
        0x0f, 0xba, 0xe1, 0x1f, // ASM: bt ecx, 31
        0xc3, // ASM: ret
    ]);
    assert!(leaf.contains("cpuid (feature probe)"), "{leaf}");
    assert!(!leaf.contains("hypervisor"), "{leaf}");
    let other = report(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x0f, 0xa2, // ASM: cpuid
        0x0f, 0xba, 0xe2, 0x1f, // ASM: bt edx, 31
        0xc3, // ASM: ret
    ]);
    assert!(!other.contains("hypervisor"), "{other}");
    let masked = report(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x0f, 0xa2, // ASM: cpuid
        0xf7, 0xc1, 0x1f, 0x00, 0x00, 0x00, // ASM: test ecx, 31
        0xc3, // ASM: ret
    ]);
    assert!(!masked.contains("hypervisor"), "{masked}");
    let compared = report(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x0f, 0xa2, // ASM: cpuid
        0x83, 0xf9, 0x1f, // ASM: cmp ecx, 31
        0xc3, // ASM: ret
    ]);
    assert!(!compared.contains("hypervisor"), "{compared}");
}

/// A call or a multiply replaces `eax` before `cpuid`. The earlier leaf is
/// not the one that ran.
#[test]
fn a_call_before_cpuid_replaces_the_leaf() {
    let called = report_calls(
        &[
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0x0f, 0xa2, // ASM: cpuid
            0xf7, 0xc1, 0x00, 0x00, 0x00, 0x80, // ASM: test ecx, 0x80000000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetCurrentProcess", 0x402000)],
    );
    assert!(called.contains("cpuid (feature probe)"), "{called}");
    assert!(!called.contains("hypervisor"), "{called}");
    let vendor = report_calls(
        &[
            0xb8, 0x00, 0x00, 0x00, 0x40, // ASM: mov eax, 0x40000000
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0x0f, 0xa2, // ASM: cpuid
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetCurrentProcess", 0x402000)],
    );
    assert!(!vendor.contains("hypervisor"), "{vendor}");
    let multiplied = report(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xf7, 0xe1, // ASM: mul ecx
        0x0f, 0xa2, // ASM: cpuid
        0xf7, 0xc1, 0x00, 0x00, 0x00, 0x80, // ASM: test ecx, 0x80000000
        0xc3, // ASM: ret
    ]);
    assert!(multiplied.contains("cpuid (feature probe)"), "{multiplied}");
    assert!(!multiplied.contains("hypervisor"), "{multiplied}");
}

/// A discarded read before a measured pair does not hide that pair.
#[test]
fn a_discarded_rdtsc_does_not_hide_a_later_pair() {
    let text = report(&[
        0x0f, 0x31, // ASM: rdtsc
        0x31, 0xc0, // ASM: xor eax, eax
        0x0f, 0x31, // ASM: rdtsc
        0x89, 0xc3, // ASM: mov ebx, eax
        0x0f, 0x31, // ASM: rdtsc
        0x29, 0xd8, // ASM: sub eax, ebx
        0x3d, 0xe8, 0x03, 0x00, 0x00, // ASM: cmp eax, 0x3e8
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("rdtsc (timing)"), "{text}");
}

/// A saved timestamp overwritten before the subtraction is a plain read.
#[test]
fn an_overwritten_timestamp_is_a_read() {
    let text = report(&[
        0x0f, 0x31, // ASM: rdtsc
        0x89, 0xc3, // ASM: mov ebx, eax
        0x0f, 0x31, // ASM: rdtsc
        0x31, 0xdb, // ASM: xor ebx, ebx
        0x29, 0xd8, // ASM: sub eax, ebx
        0x3d, 0xe8, 0x03, 0x00, 0x00, // ASM: cmp eax, 0x3e8
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("rdtsc (read)"), "{text}");
    assert!(!text.contains("rdtsc (timing)"), "{text}");
}

/// The second timestamp replaced before the subtraction is a plain read.
#[test]
fn a_replaced_second_timestamp_is_a_read() {
    let text = report(&[
        0x0f, 0x31, // ASM: rdtsc
        0x89, 0xc3, // ASM: mov ebx, eax
        0x0f, 0x31, // ASM: rdtsc
        0x31, 0xc0, // ASM: xor eax, eax
        0x29, 0xd8, // ASM: sub eax, ebx
        0x3d, 0xe8, 0x03, 0x00, 0x00, // ASM: cmp eax, 0x3e8
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("rdtsc (read)"), "{text}");
    assert!(!text.contains("rdtsc (timing)"), "{text}");
}

/// A compare of a copied difference is still a timing check.
#[test]
fn a_copied_timestamp_difference_is_timing() {
    let text = report(&[
        0x0f, 0x31, // ASM: rdtsc
        0x89, 0xc3, // ASM: mov ebx, eax
        0x0f, 0x31, // ASM: rdtsc
        0x29, 0xd8, // ASM: sub eax, ebx
        0x89, 0xc7, // ASM: mov edi, eax
        0x85, 0xff, // ASM: test edi, edi
        0x74, 0x00, // ASM: jz 0x40100e
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("rdtsc (timing)"), "{text}");
    assert!(!text.contains("rdtsc (read)"), "{text}");
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

/// A port or magic overwritten before `in` is a plain port read.
///
/// The value still in the register is what the instruction uses.
#[test]
fn an_overwritten_port_is_a_plain_read() {
    let port = report(&[
        0xba, 0x58, 0x56, 0x00, 0x00, // ASM: mov edx, 0x5658
        0xba, 0x80, 0x00, 0x00, 0x00, // ASM: mov edx, 0x80
        0xed, // ASM: in eax, dx
        0xc3, // ASM: ret
    ]);
    assert!(port.contains("in (port read)"), "{port}");
    assert!(!port.contains("VMware"), "{port}");
    let magic = report(&[
        0xb8, 0x68, 0x58, 0x4d, 0x56, // ASM: mov eax, 0x564d5868
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xed, // ASM: in eax, dx
        0xc3, // ASM: ret
    ]);
    assert!(magic.contains("in (port read)"), "{magic}");
    assert!(!magic.contains("VMware"), "{magic}");
    let live = report(&[
        0xba, 0x80, 0x00, 0x00, 0x00, // ASM: mov edx, 0x80
        0xba, 0x58, 0x56, 0x00, 0x00, // ASM: mov edx, 0x5658
        0xed, // ASM: in eax, dx
        0xc3, // ASM: ret
    ]);
    assert!(live.contains("in (VMware backdoor port)"), "{live}");
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

/// A lone `NtQueryInformationProcess` import does not decide the verdict.
/// A call that asks for `ProcessDebugPort` does. `ProcessBasicInformation`
/// does not.
#[test]
fn a_debug_port_query_is_a_tell_and_the_import_alone_is_not() {
    let alone = report_calls(&[0xc3], &[], &[("NtQueryInformationProcess", 0x402000)]);
    assert!(alone.contains("NtQueryInformationProcess"), "{alone}");
    assert!(!alone.contains("debug port"), "{alone}");
    assert!(!alone.starts_with("# anti-analysis:"), "{alone}");
    let basic = report_calls(
        &[
            0xba, 0x00, 0x00, 0x00, 0x00, // ASM: mov edx, 0
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("NtQueryInformationProcess", 0x402000)],
    );
    assert!(!basic.contains("debug port"), "{basic}");
    assert!(!basic.starts_with("# anti-analysis:"), "{basic}");
    let port = report_calls(
        &[
            0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx, 7
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("NtQueryInformationProcess", 0x402000)],
    );
    assert!(port.contains("debug port"), "{port}");
    assert!(port.starts_with("# anti-analysis:"), "{port}");
    let other = report_calls(
        &[
            0xba, 0x00, 0x00, 0x00, 0x00, // ASM: mov edx, 0
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx, 7
            0xe8, 0xfc, 0x0f, 0x00, 0x00, // ASM: call 0x402010
            0xc3, // ASM: ret
        ],
        &[],
        &[
            ("NtQueryInformationProcess", 0x402000),
            ("GetCurrentProcessId", 0x402010),
        ],
    );
    assert!(!other.contains("debug port"), "{other}");
    assert!(!other.starts_with("# anti-analysis:"), "{other}");
}

/// A byte written over `edx` is not the whole information class.
///
/// `mov edx, 0x100; mov dl, 7` passes `0x107`. A compare of `edx` does
/// not erase a class of `7` moved into it.
#[test]
fn a_partial_class_write_is_not_the_debug_port() {
    let mixed = report_calls(
        &[
            0xba, 0x00, 0x01, 0x00, 0x00, // ASM: mov edx, 0x100
            0xb2, 0x07, // ASM: mov dl, 7
            0xe8, 0xf4, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("NtQueryInformationProcess", 0x402000)],
    );
    assert!(!mixed.contains("debug port"), "{mixed}");
    assert!(!mixed.starts_with("# anti-analysis:"), "{mixed}");
    let compared = report_calls(
        &[
            0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx, 7
            0x83, 0xfa, 0x01, // ASM: cmp edx, 1
            0xe8, 0xf3, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("NtQueryInformationProcess", 0x402000)],
    );
    assert!(compared.contains("debug port"), "{compared}");
    assert!(compared.starts_with("# anti-analysis:"), "{compared}");
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

/// `lea gs:[0x60]` names the address. A base, an index, or a store is a
/// different access, and `lea` of the TEB does not become the PEB pointer.
#[test]
fn an_address_or_another_slot_is_not_a_peb_read() {
    let address = [
        0x65, 0x48, 0x8d, 0x04, 0x25, 0x60, 0x00, 0x00, 0x00, // ASM: lea rax, gs:[0x60]
        0xc3, // ASM: ret
    ];
    assert_eq!(
        segment_slot(&address),
        (
            Mnemonic::Lea,
            Register::GS,
            Register::None,
            Register::None,
            0x60
        )
    );
    let address_text = report(&address);
    assert!(!address_text.contains("peb read"), "{address_text}");
    let based = [
        0x65, 0x48, 0x8b, 0x43, 0x60, // ASM: mov rax, gs:[rbx+0x60]
        0xc3, // ASM: ret
    ];
    assert_eq!(
        segment_slot(&based),
        (
            Mnemonic::Mov,
            Register::GS,
            Register::RBX,
            Register::None,
            0x60
        )
    );
    let based_text = report(&based);
    assert!(!based_text.contains("peb read"), "{based_text}");
    let indexed = [
        0x65, 0x48, 0x8b, 0x04, 0x1d, 0x60, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[rbx*1+0x60]
        0xc3, // ASM: ret
    ];
    assert_eq!(
        segment_slot(&indexed),
        (
            Mnemonic::Mov,
            Register::GS,
            Register::None,
            Register::RBX,
            0x60
        )
    );
    let indexed_text = report(&indexed);
    assert!(!indexed_text.contains("peb read"), "{indexed_text}");
    let stored = [
        0x65, 0x48, 0x89, 0x04, 0x25, 0x60, 0x00, 0x00, 0x00, // ASM: mov gs:[0x60], rax
        0xc3, // ASM: ret
    ];
    assert_eq!(
        segment_slot(&stored),
        (
            Mnemonic::Mov,
            Register::GS,
            Register::None,
            Register::None,
            0x60
        )
    );
    let stored_text = report(&stored);
    assert!(!stored_text.contains("peb read"), "{stored_text}");
    let teb = [
        0x65, 0x48, 0x8d, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: lea rax, gs:[0x30]
        0x48, 0x8b, 0x40, 0x60, // ASM: mov rax, [rax+0x60]
        0xc3, // ASM: ret
    ];
    assert_eq!(
        segment_slot(&teb),
        (
            Mnemonic::Lea,
            Register::GS,
            Register::None,
            Register::None,
            0x30
        )
    );
    let teb_text = report(&teb);
    assert!(!teb_text.contains("peb read"), "{teb_text}");
}

/// `fs:[0x30]` on ELF is the thread pointer guard, not the Windows PEB.
#[test]
fn an_elf_thread_word_is_not_a_peb_read() {
    let mut p = image(
        Arch::X86_64,
        &[
            0x64, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov eax, fs:[0x30]
            0xc3, // ASM: ret
        ],
        &[],
    );
    p.format = BinaryFormat::Elf;
    let a = Analysis::compute(&p);
    let text = borer_engine::analysis::render::anti_analysis_tsv(&p, &a, &Overlay::default());
    assert!(!text.contains("peb read"), "{text}");
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

/// A TEB read is a PEB read only when the next access uses that pointer.
#[test]
fn an_unrelated_slot_after_a_teb_read_is_not_a_peb_read() {
    let text = report(&[
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[0x30]
        0x48, 0x8b, 0x4b, 0x60, // ASM: mov rcx, [rbx+0x60]
        0xc3, // ASM: ret
    ]);
    assert!(!text.contains("peb read"), "{text}");
}

/// A field read has to use the PEB pointer. Another base, and a store,
/// stay a plain PEB read. A copy of the pointer still names the field.
#[test]
fn a_peb_field_read_uses_the_peb_pointer() {
    let other = report(&[
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x60, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[0x60]
        0x0f, 0xb6, 0x53, 0x02, // ASM: movzx edx, byte [rbx+2]
        0xc3, // ASM: ret
    ]);
    assert!(other.contains("peb read"), "{other}");
    assert!(!other.contains("BeingDebugged"), "{other}");
    let store = report(&[
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x60, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[0x60]
        0xc6, 0x40, 0x02, 0x00, // ASM: mov byte [rax+2], 0
        0xc3, // ASM: ret
    ]);
    assert!(store.contains("peb read"), "{store}");
    assert!(!store.contains("BeingDebugged"), "{store}");
    let copied = report(&[
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x60, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[0x60]
        0x48, 0x89, 0xc3, // ASM: mov rbx, rax
        0x0f, 0xb6, 0x53, 0x02, // ASM: movzx edx, byte [rbx+2]
        0xc3, // ASM: ret
    ]);
    assert!(copied.contains("peb read (BeingDebugged)"), "{copied}");
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

/// `GetThreadContext` is a hardware-breakpoint tell only when the
/// debug-register flags are stored into its buffer.
#[test]
fn get_thread_context_needs_the_debug_register_flags() {
    let flagged = report_calls(
        &[
            0xc7, 0x42, 0x30, 0x10, 0x00, 0x01, 0x00, // ASM: mov dword [rdx+0x30], 0x10010
            0xe8, 0xf4, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(flagged.contains("GetThreadContext"), "{flagged}");
    let unstored = report_calls(
        &[
            0xb8, 0x10, 0x00, 0x01, 0x00, // ASM: mov eax, 0x10010
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!unstored.contains("hardware breakpoint"), "{unstored}");
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

/// The last store of `ContextFlags` is the request the call makes.
///
/// `CONTEXT_DEBUG_REGISTERS` replaced by `CONTEXT_CONTROL` is not a
/// hardware breakpoint. The other order still is. A register stored over
/// the field, with no debug flags in that register, is not either.
#[test]
fn a_replaced_context_flag_is_not_a_hardware_breakpoint() {
    let replaced = report_calls(
        &[
            0xc7, 0x42, 0x30, 0x10, 0x00, 0x01, 0x00, // ASM: mov dword [rdx+0x30], 0x10010
            0xc7, 0x42, 0x30, 0x01, 0x00, 0x10, 0x00, // ASM: mov dword [rdx+0x30], 0x100001
            0xe8, 0xed, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!replaced.contains("hardware breakpoint"), "{replaced}");
    let kept = report_calls(
        &[
            0xc7, 0x42, 0x30, 0x01, 0x00, 0x10, 0x00, // ASM: mov dword [rdx+0x30], 0x100001
            0xc7, 0x42, 0x30, 0x10, 0x00, 0x01, 0x00, // ASM: mov dword [rdx+0x30], 0x10010
            0xe8, 0xed, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(kept.contains("hardware breakpoint"), "{kept}");
    let unknown = report_calls(
        &[
            0xc7, 0x42, 0x30, 0x10, 0x00, 0x01, 0x00, // ASM: mov dword [rdx+0x30], 0x10010
            0x89, 0x42, 0x30, // ASM: mov [rdx+0x30], eax
            0xe8, 0xf0, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!unknown.contains("hardware breakpoint"), "{unknown}");
}

/// `CONTEXT_ALL` is a hardware-breakpoint tell.
///
/// A `Dr0` load is one when it reads the context buffer the call was given.
/// `CONTEXT_CONTROL` is not, a store is not, and a load through another
/// register is not.
#[test]
fn context_all_and_a_dr_read_are_hardware_breakpoints() {
    let all = report_calls(
        &[
            0xb8, 0x1f, 0x00, 0x10, 0x00, // ASM: mov eax, 0x10001f
            0x89, 0x42, 0x30, // ASM: mov [rdx+0x30], eax
            0xe8, 0xf3, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("NtGetContextThread", 0x402000)],
    );
    assert!(all.contains("hardware breakpoint"), "{all}");
    let control = report_calls(
        &[
            0xb8, 0x01, 0x00, 0x10, 0x00, // ASM: mov eax, 0x100001
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!control.contains("hardware breakpoint"), "{control}");
    let integer = report_calls(
        &[
            0xb8, 0x02, 0x00, 0x10, 0x00, // ASM: mov eax, 0x100002
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("ZwGetContextThread", 0x402000)],
    );
    assert!(!integer.contains("hardware breakpoint"), "{integer}");
    let read = report_calls(
        &[
            0x48, 0x8d, 0x5c, 0x24, 0x20, // ASM: lea rbx, [rsp+0x20]
            0x48, 0x89, 0xda, // ASM: mov rdx, rbx
            0xe8, 0xf3, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0x48, 0x8b, 0x43, 0x48, // ASM: mov rax, [rbx+0x48]
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(read.contains("hardware breakpoint"), "{read}");
    let replaced = report_calls(
        &[
            0x48, 0x8d, 0x5c, 0x24, 0x20, // ASM: lea rbx, [rsp+0x20]
            0x48, 0x89, 0xf3, // ASM: mov rbx, rsi
            0x48, 0x89, 0xda, // ASM: mov rdx, rbx
            0xe8, 0xf0, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0x48, 0x8b, 0x84, 0x24, 0x68, 0x00, 0x00, 0x00, // ASM: mov rax, [rsp+0x68]
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!replaced.contains("hardware breakpoint"), "{replaced}");
    let slot = report_calls(
        &[
            0x48, 0x8d, 0x54, 0x24, 0x20, // ASM: lea rdx, [rsp+0x20]
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0x48, 0x8b, 0x44, 0x24, 0x68, // ASM: mov rax, [rsp+0x68]
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(slot.contains("hardware breakpoint"), "{slot}");
    let other = report_calls(
        &[
            0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0x48, 0x8b, 0x43, 0x48, // ASM: mov rax, [rbx+0x48]
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!other.contains("hardware breakpoint"), "{other}");
    let store = report_calls(
        &[
            0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0x48, 0x89, 0x42, 0x48, // ASM: mov [rdx+0x48], rax
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!store.contains("hardware breakpoint"), "{store}");
}

/// A buffer passed to a later call is not the context `GetThreadContext` got.
#[test]
fn a_later_call_does_not_make_a_context_buffer() {
    let text = report_calls(
        &[
            0xb8, 0x01, 0x00, 0x10, 0x00, // ASM: mov eax, 0x100001
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0x48, 0x89, 0xda, // ASM: mov rdx, rbx
            0xe8, 0xfe, 0x0f, 0x00, 0x00, // ASM: call 0x402010
            0x48, 0x8b, 0x43, 0x48, // ASM: mov rax, [rbx+0x48]
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000), ("SuspendThread", 0x402010)],
    );
    assert!(!text.contains("hardware breakpoint"), "{text}");
}

/// A compare that holds the debug-register flags is not a request for them.
#[test]
fn a_compared_context_word_is_not_a_hardware_breakpoint() {
    let text = report_calls(
        &[
            0x3d, 0x10, 0x00, 0x10, 0x00, // ASM: cmp eax, 0x100010
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!text.contains("hardware breakpoint"), "{text}");
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

/// `lea rcx, [rip+name]` passes the class on x64.
///
/// `OLLYDBG` there is a debugger window. An ordinary name is not.
#[test]
fn a_rip_relative_debugger_window_is_named() {
    let named = |bytes: &[u8]| {
        let mut data = vec![0u8; 0x100 + bytes.len()];
        data[0x100..].copy_from_slice(bytes);
        let code = [
            0x48, 0x8d, 0x0d, 0xf9, 0x10, 0x00, 0x00, // ASM: lea rcx, [rip+0x10f9]
            0xe8, 0xf4, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xe8, 0xff, 0x0f, 0x00, 0x00, // ASM: call 0x402010
            0xc3, // ASM: ret
        ];
        report_calls(
            &code,
            &data,
            &[("FindWindowA", 0x402000), ("ExitProcess", 0x402010)],
        )
    };
    let olly = named(b"OLLYDBG\0");
    assert!(olly.contains("debugger window"), "{olly}");
    let notepad = named(b"NOTEPAD\0");
    assert!(!notepad.contains("debugger window"), "{notepad}");
}

/// `FindWindowW` of a wide debugger class is the same tell. A wide
/// ordinary class is not.
#[test]
fn a_wide_debugger_window_is_named() {
    let wide = |bytes: &[u8]| {
        let mut data = vec![0u8; 0x100 + bytes.len()];
        data[0x100..].copy_from_slice(bytes);
        let code = [
            0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xe8, 0x06, 0x10, 0x00, 0x00, // ASM: call 0x402010
            0x68, 0x00, 0x21, 0x40, 0x00, // ASM: push 0x402100
            0xc3, // ASM: ret
        ];
        report_calls(
            &code,
            &data,
            &[("FindWindowW", 0x402000), ("ExitProcess", 0x402010)],
        )
    };
    let olly = wide(&[
        0x4f, 0x00, 0x4c, 0x00, 0x4c, 0x00, 0x59, 0x00, 0x44, 0x00, 0x42, 0x00, 0x47, 0x00, 0x00,
        0x00,
    ]);
    assert!(olly.contains("debugger window"), "{olly}");
    let notepad = wide(&[
        0x4e, 0x00, 0x4f, 0x00, 0x54, 0x00, 0x45, 0x00, 0x50, 0x00, 0x41, 0x00, 0x44, 0x00, 0x00,
        0x00,
    ]);
    assert!(!notepad.contains("debugger window"), "{notepad}");
}

/// Creating a process with `DEBUG_PROCESS` and waiting on a debug event
/// is a debug block. The same calls without that flag are not.
#[test]
fn a_debug_process_block_is_a_tell() {
    let flagged = |flag: u8| {
        let code = [
            0xc7, 0x44, 0x24, 0x28, flag, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x28], flag
            0xe8, 0xf3, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xe8, 0xfe, 0x0f, 0x00, 0x00, // ASM: call 0x402010
            0xc3, // ASM: ret
        ];
        report_calls(
            &code,
            &[],
            &[
                ("CreateProcessA", 0x402000),
                ("WaitForDebugEvent", 0x402010),
            ],
        )
    };
    let debug = flagged(1);
    assert!(debug.contains("debug block"), "{debug}");
    assert!(debug.starts_with("# anti-analysis:"), "{debug}");
    let only = flagged(2);
    assert!(only.contains("debug block"), "{only}");
    let suspended = flagged(4);
    assert!(!suspended.contains("debug block"), "{suspended}");
    let plain = report_calls(
        &[
            0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xe8, 0x06, 0x10, 0x00, 0x00, // ASM: call 0x402010
            0xc3, // ASM: ret
        ],
        &[],
        &[
            ("CreateProcessA", 0x402000),
            ("WaitForDebugEvent", 0x402010),
        ],
    );
    assert!(!plain.contains("debug block"), "{plain}");
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

/// A later store of the process flags replaces an earlier debug flag.
///
/// `CREATE_SUSPENDED` after `DEBUG_PROCESS` is not a debug block. A later
/// `DEBUG_PROCESS` still is. A register stored over the flag is not a
/// known debug flag either.
#[test]
fn a_replaced_process_flag_is_not_a_debug_block() {
    let replaced = report_calls(
        &[
            0xc7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x28], 1
            0xc7, 0x44, 0x24, 0x28, 0x04, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x28], 4
            0xe8, 0xeb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402010
            0xc3, // ASM: ret
        ],
        &[],
        &[
            ("CreateProcessA", 0x402000),
            ("WaitForDebugEvent", 0x402010),
        ],
    );
    assert!(!replaced.contains("debug block"), "{replaced}");
    let kept = report_calls(
        &[
            0xc7, 0x44, 0x24, 0x28, 0x04, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x28], 4
            0xc7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x28], 1
            0xe8, 0xeb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402010
            0xc3, // ASM: ret
        ],
        &[],
        &[
            ("CreateProcessA", 0x402000),
            ("WaitForDebugEvent", 0x402010),
        ],
    );
    assert!(kept.contains("debug block"), "{kept}");
    let unknown = report_calls(
        &[
            0xc7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x28], 1
            0x89, 0x44, 0x24, 0x28, // ASM: mov [rsp+0x28], eax
            0xe8, 0xef, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xe8, 0xfa, 0x0f, 0x00, 0x00, // ASM: call 0x402010
            0xc3, // ASM: ret
        ],
        &[],
        &[
            ("CreateProcessA", 0x402000),
            ("WaitForDebugEvent", 0x402010),
        ],
    );
    assert!(!unknown.contains("debug block"), "{unknown}");
}

/// Taking the address of the two debug APIs is not a call, so it is not a
/// debug block.
#[test]
fn addresses_of_debug_apis_are_not_a_debug_block() {
    let code = [
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [rip+0xff9]
        0x48, 0x8d, 0x05, 0x02, 0x10, 0x00, 0x00, // ASM: lea rax, [rip+0x1002]
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
    assert!(!text.contains("debug block"), "{text}");
}

/// An indirect `GetThreadContext` followed by a `Dr0` load of its buffer
/// is a hardware breakpoint. The call alone is not.
#[test]
fn an_indirect_context_call_and_a_dr_read_is_a_hardware_breakpoint() {
    let read = report_calls(
        &[
            0x48, 0x8d, 0x5c, 0x24, 0x20, // ASM: lea rbx, [rsp+0x20]
            0x48, 0x89, 0xda, // ASM: mov rdx, rbx
            0xff, 0x15, 0xf2, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0xff2]
            0x48, 0x8b, 0x43, 0x48, // ASM: mov rax, [rbx+0x48]
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(read.contains("hardware breakpoint"), "{read}");
    let bare = report_calls(
        &[
            0xff, 0x15, 0xfa, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0xffa]
            0xc3, // ASM: ret
        ],
        &[],
        &[("GetThreadContext", 0x402000)],
    );
    assert!(!bare.contains("hardware breakpoint"), "{bare}");
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
    let counter = report_calls(
        &[
            0xff, 0xc0, // ASM: inc eax
            0x3d, 0x90, 0x00, 0x00, 0x00, // ASM: cmp eax, 0x90
            0x75, 0xf7, // ASM: jne 0x401000
            0xe8, 0xf2, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[("ExitProcess", 0x402000)],
    );
    assert!(!counter.contains("breakpoint"), "{counter}");
    assert!(!counter.starts_with("# anti-analysis:"), "{counter}");
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

/// A code address passed to another call is not the filter's handler.
///
/// Clearing the filter and then running into bad bytes is not the tell.
/// Bad bytes before the filter call are not it either.
#[test]
fn a_filter_needs_its_own_handler_and_the_bad_bytes_after_it() {
    let cleared = report_calls(
        &[
            0xb9, 0x40, 0x10, 0x40, 0x00, // ASM: mov ecx, 0x401040
            0xe8, 0x06, 0x10, 0x00, 0x00, // ASM: call 0x402010
            0xb9, 0x00, 0x00, 0x00, 0x00, // ASM: mov ecx, 0
            0xe8, 0xec, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xf0, 0xf0, 0xc7, 0xc8, // ASM: two lock prefixes, not an instruction
            0xeb, 0x01, // ASM: jmp short +1
            0x6e, // ASM: outsb, skipped
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
        ],
        &[],
        &[
            ("SetUnhandledExceptionFilter", 0x402000),
            ("CloseHandle", 0x402010),
        ],
    );
    assert!(!cleared.contains("illegal opcode"), "{cleared}");
    let earlier = report_calls(
        &[
            0xb9, 0x40, 0x10, 0x40, 0x00, // ASM: mov ecx, 0x401040
            0xe8, 0x06, 0x10, 0x00, 0x00, // ASM: call 0x402010
            0xf0, 0xf0, 0xc7, 0xc8, // ASM: two lock prefixes, not an instruction
            0xeb, 0x01, // ASM: jmp short +1
            0x6e, // ASM: outsb, skipped
            0xb9, 0x30, 0x10, 0x40, 0x00, // ASM: mov ecx, 0x401030
            0xe8, 0xd7, 0x0f, 0x00, 0x00, // ASM: call 0x402000
            0xc3, // ASM: ret
        ],
        &[],
        &[
            ("SetUnhandledExceptionFilter", 0x402000),
            ("CloseHandle", 0x402010),
        ],
    );
    assert!(!earlier.contains("illegal opcode"), "{earlier}");
}
