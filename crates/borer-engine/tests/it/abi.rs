//! The ABI layer: linkage stubs bound to the program's own functions, an
//! indirect result's pointer placed as the source prototype has it, and
//! runtime helpers printed as the operators they are.
//!
//! The arm64 routines are assembled by LLVM (`clang --target=aarch64-linux-gnu`)
//! and checked against `llvm-objdump`, with the page and offset of each
//! `adrp` pair filled in for the image's layout; each word's comment is
//! its instruction.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Symbol, SymbolKind};

/// Where [`crate::raw::image`] maps the code.
const TEXT: u64 = 0x40_1000;
/// Where it maps the data: the stubs' slots.
const SLOTS: u64 = 0x40_2000;

/// arm64 routines at [`TEXT`]:
///
/// ```text
/// fib(n)     : n < 2 ? n : fib_plt(n - 1) + n   at +0x00
/// fib_plt    : the PLT entry of slot 0, which binds fib   at +0x30
/// mkrect(a)  : writes {a, -a} through x8         at +0x40
/// userect()  : calls mkrect into its frame       at +0x50
/// powmod(a, m): __umodti3(a, 0, m, 0)            at +0x74
/// umod_plt   : the PLT entry of slot 1, an import at +0x94
/// walk(p)    : p ? walk(*p) + p : p, its frame set up past the test at +0xa8
/// ```
const ROUTINES: [u32; 53] = [
    0xa9be_7bfd, // ASM: stp x29, x30, [sp, #-0x20]! (fib)
    0x9100_03fd, // ASM: mov x29, sp
    0xf900_0bf3, // ASM: str x19, [sp, #0x10]
    0x2a00_03f3, // ASM: mov w19, w0
    0x7100_081f, // ASM: cmp w0, #0x2
    0x5400_008b, // ASM: b.lt fib+0x24
    0x5100_0660, // ASM: sub w0, w19, #0x1
    0x9400_0005, // ASM: bl fib_plt
    0x0b13_0000, // ASM: add w0, w0, w19
    0xf940_0bf3, // ASM: ldr x19, [sp, #0x10]
    0xa8c2_7bfd, // ASM: ldp x29, x30, [sp], #0x20
    0xd65f_03c0, // ASM: ret
    0xb000_0010, // ASM: adrp x16, 0x402000 (fib_plt)
    0xf940_0211, // ASM: ldr x17, [x16]
    0x9100_0210, // ASM: add x16, x16, #0x0
    0xd61f_0220, // ASM: br x17
    0xb900_0100, // ASM: str w0, [x8] (mkrect)
    0x4b00_03e9, // ASM: neg w9, w0
    0xb900_0509, // ASM: str w9, [x8, #0x4]
    0xd65f_03c0, // ASM: ret
    0xd100_83ff, // ASM: sub sp, sp, #0x20 (userect)
    0xa901_7bfd, // ASM: stp x29, x30, [sp, #0x10]
    0x9100_43fd, // ASM: add x29, sp, #0x10
    0x9100_03e8, // ASM: mov x8, sp
    0x97ff_fff8, // ASM: bl mkrect
    0xb940_07e0, // ASM: ldr w0, [sp, #0x4]
    0xa941_7bfd, // ASM: ldp x29, x30, [sp, #0x10]
    0x9100_83ff, // ASM: add sp, sp, #0x20
    0xd65f_03c0, // ASM: ret
    0xa9bf_7bfd, // ASM: stp x29, x30, [sp, #-0x10]! (powmod)
    0x9100_03fd, // ASM: mov x29, sp
    0xaa01_03e2, // ASM: mov x2, x1
    0xaa1f_03e1, // ASM: mov x1, xzr
    0xaa1f_03e3, // ASM: mov x3, xzr
    0x9400_0003, // ASM: bl umod_plt
    0xa8c1_7bfd, // ASM: ldp x29, x30, [sp], #0x10
    0xd65f_03c0, // ASM: ret
    0xb000_0010, // ASM: adrp x16, 0x402000 (umod_plt)
    0xf940_0611, // ASM: ldr x17, [x16, #0x8]
    0x9100_2210, // ASM: add x16, x16, #0x8
    0xd61f_0220, // ASM: br x17
    0xd503_201f, // ASM: nop
    0xb400_0140, // ASM: cbz x0, walk+0x28 (walk)
    0xa9be_7bfd, // ASM: stp x29, x30, [sp, #-0x20]!
    0x9100_03fd, // ASM: mov x29, sp
    0xf900_0bf3, // ASM: str x19, [sp, #0x10]
    0xaa00_03f3, // ASM: mov x19, x0
    0xf940_0000, // ASM: ldr x0, [x0]
    0x97ff_fffa, // ASM: bl walk
    0x8b13_0000, // ASM: add x0, x0, x19
    0xf940_0bf3, // ASM: ldr x19, [sp, #0x10]
    0xa8c2_7bfd, // ASM: ldp x29, x30, [sp], #0x20
    0xd65f_03c0, // ASM: ret
];

/// [`ROUTINES`] as an arm64 ELF image: slot 0 holds `fib`'s address as the
/// loader binds it, slot 1 is the import `__umodti3`.
///
/// The format is ELF's, as the PLT stubs are: the runtime helpers take a
/// 128-bit operand in two registers there, and by pointer on Windows.
fn image() -> Program {
    let code: Vec<u8> = ROUTINES.iter().flat_map(|w| w.to_le_bytes()).collect();
    let mut p = crate::raw::image(Arch::Arm64, &code, &TEXT.to_le_bytes());
    p.format = BinaryFormat::Elf;
    let named = |name: &str, addr: u64, kind: SymbolKind| Symbol {
        name: name.to_owned(),
        addr,
        kind,
    };
    p.symbols = vec![
        named("fib", TEXT, SymbolKind::Export),
        named("mkrect", TEXT + 0x40, SymbolKind::Export),
        named("userect", TEXT + 0x50, SymbolKind::Export),
        named("powmod", TEXT + 0x74, SymbolKind::Export),
        named("walk", TEXT + 0xa8, SymbolKind::Export),
        named("__umodti3", SLOTS + 8, SymbolKind::Import),
    ];
    p
}

/// A PLT entry whose slot the loader binds to a function of the program's
/// own is that function: the stub takes its name, and a call through it
/// passes the arguments that function takes.
///
/// The stub was `sub_401030()`, a call with no arguments to a name no
/// compiler declares, since the stub's own body reads nothing but `x16`.
#[test]
fn a_plt_stub_calls_the_function_its_slot_binds() {
    let p = image();
    let a = Analysis::compute(&p);
    let stub = a.function(TEXT + 0x30).expect("the stub is a function");
    assert_eq!(
        (stub.name.as_deref(), stub.bound),
        (Some("fib"), Some(TEXT))
    );
    let text = decompile(&p, &a, &Overlay::default(), TEXT).expect("decompiles");
    assert!(text.contains("fib((a1 - 1)"), "{text}");
    assert!(!text.contains("sub_"), "{text}");
}

/// An indirect result's address in `x8` is an ABI fact, not the last
/// parameter: the signature and every call list it first, where the
/// source prototype has it, so the text calls the same on any host.
#[test]
fn an_indirect_result_comes_first() {
    let p = image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let mkrect = decompile(&p, &a, &o, TEXT + 0x40).expect("decompiles");
    assert!(
        mkrect.contains("// signature: void mkrect(void *result, uint64_t a1)"),
        "{mkrect}"
    );
    let user = decompile(&p, &a, &o, TEXT + 0x50).expect("decompiles");
    let call = user
        .lines()
        .find(|l| l.contains("mkrect(") && !l.starts_with("extern "))
        .expect("the call is shown");
    assert!(call.contains("mkrect(&"), "{user}");
}

/// A call to `__umodti3` passes two 128-bit operands as four halves and
/// is the remainder of their `unsigned __int128` values.
///
/// The header may name the helper and its prototype; the body calls it
/// nowhere.
#[test]
fn a_128_bit_helper_prints_as_its_operator() {
    let p = image();
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), TEXT + 0x74).expect("decompiles");
    let body: Vec<&str> = text.lines().filter(|l| !l.starts_with("//")).collect();
    assert!(!body.iter().any(|l| l.contains("__umodti3(")), "{text}");
    assert!(text.contains(" % (uint128_t)"), "{text}");
}

/// A save outside the entry block is still a save, which prints nothing.
///
/// The prologue is shrink-wrapped past the function's first test, so the
/// frame record and `x19` are stored after it; those stores printed as
/// assignments of registers no statement set (`local_20 = x29;`).
#[test]
fn a_save_past_the_entry_block_prints_nothing() {
    let p = image();
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), TEXT + 0xa8).expect("decompiles");
    for reg in ["x19", "x29", "x30"] {
        assert!(!text.contains(&format!("= {reg};")), "{reg}: {text}");
    }
    assert!(text.contains("walk("), "{text}");
}
