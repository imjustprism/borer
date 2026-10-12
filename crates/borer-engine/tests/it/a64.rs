//! AArch64 decoding and disassembly.
//!
//! A table of words assembled by LLVM (`clang --target=aarch64-linux-gnu`)
//! and checked against `llvm-objdump`, each with the text, control flow and
//! branch target the engine gives it; then thin arm64 Mach-O, ELF, PE and
//! raw images, built here, disassembled at their entry, and a sweep of
//! every word.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

use borer_engine::analysis::{Analysis, render};
use borer_engine::disasm;
use borer_engine::isa::Isa;
use borer_engine::isa::a64::{self, Flow, Mem, Mode, Op, Opnd, Reg, Shift};
use borer_engine::program::{Arch, BinaryFormat, Feature, Program};

/// Where the first word of [`WORDS`] sits; each next word is four bytes on.
const BASE: u64 = 0x10000;

/// Words laid out from [`BASE`] as one block, as the assembler placed
/// them: the encoded word, its text, its flow and its direct target.
/// Branch targets are the block's two labels, `0x10050` and `0x100cc`.
const WORDS: &[(u32, &str, Flow, Option<u64>)] = &[
    // ASM: b 0x100cc
    (0x14000033, "b 0x100cc", Flow::Jump, Some(0x100cc)),
    // ASM: bl 0x10050
    (0x94000013, "bl 0x10050", Flow::Call, Some(0x10050)),
    // ASM: b.eq 0x100cc
    (0x54000620, "b.eq 0x100cc", Flow::CondJump, Some(0x100cc)),
    // ASM: b.ne 0x10050
    (0x54000221, "b.ne 0x10050", Flow::CondJump, Some(0x10050)),
    // ASM: b.hi 0x100cc
    (0x540005e8, "b.hi 0x100cc", Flow::CondJump, Some(0x100cc)),
    // ASM: b.lt 0x100cc
    (0x540005cb, "b.lt 0x100cc", Flow::CondJump, Some(0x100cc)),
    // ASM: cbz w0, 0x100cc
    (0x340005a0, "cbz w0, 0x100cc", Flow::CondJump, Some(0x100cc)),
    // ASM: cbnz x1, 0x10050
    (
        0xb50001a1,
        "cbnz x1, 0x10050",
        Flow::CondJump,
        Some(0x10050),
    ),
    // ASM: tbz w2, #3, 0x100cc
    (
        0x36180562,
        "tbz w2, #0x3, 0x100cc",
        Flow::CondJump,
        Some(0x100cc),
    ),
    // ASM: tbnz x3, #40, 0x10050
    (
        0xb7400163,
        "tbnz x3, #0x28, 0x10050",
        Flow::CondJump,
        Some(0x10050),
    ),
    // ASM: br x16
    (0xd61f0200, "br x16", Flow::Jump, None),
    // ASM: blr x8
    (0xd63f0100, "blr x8", Flow::Call, None),
    // ASM: ret
    (0xd65f03c0, "ret", Flow::Return, None),
    // ASM: ret x1
    (0xd65f0020, "ret x1", Flow::Return, None),
    // ASM: retaa
    (0xd65f0bff, "retaa", Flow::Return, None),
    // ASM: retab
    (0xd65f0fff, "retab", Flow::Return, None),
    // ASM: braa x16, x17
    (0xd71f0a11, "braa x16, x17", Flow::Jump, None),
    // ASM: blraa x8, sp
    (0xd73f091f, "blraa x8, sp", Flow::Call, None),
    // ASM: braaz x16
    (0xd61f0a1f, "braaz x16", Flow::Jump, None),
    // ASM: eret
    (0xd69f03e0, "eret", Flow::Return, None),
    // ASM: brk #0x1
    (0xd4200020, "brk #0x1", Flow::Invalid, None),
    // ASM: udf #0x0
    (0x00000000, "udf #0x0", Flow::Invalid, None),
    // ASM: hlt #0x0
    (0xd4400000, "hlt #0x0", Flow::Invalid, None),
    // ASM: svc #0x80
    (0xd4001001, "svc #0x80", Flow::Next, None),
    // ASM: adr x0, 0x100cc
    (0x10000360, "adr x0, 0x100cc", Flow::Next, None),
    // ASM: adr x1, 0x10050
    (0x10ffff61, "adr x1, 0x10050", Flow::Next, None),
    // ASM: ldr x2, 0x100cc
    (0x58000322, "ldr x2, 0x100cc", Flow::Next, None),
    // ASM: ldr w3, 0x10050
    (0x18ffff23, "ldr w3, 0x10050", Flow::Next, None),
    // ASM: mov x0, #0x10
    (0xd2800200, "mov x0, #0x10", Flow::Next, None),
    // ASM: movk x0, #0x1234, lsl #16
    (0xf2a24680, "movk x0, #0x1234, lsl #16", Flow::Next, None),
    // ASM: mov w1, #-1
    (0x12800001, "mov w1, #0xffffffff", Flow::Next, None),
    // ASM: mov x2, x3
    (0xaa0303e2, "mov x2, x3", Flow::Next, None),
    // ASM: add x0, x1, #0x10
    (0x91004020, "add x0, x1, #0x10", Flow::Next, None),
    // ASM: add x0, sp, #0x1, lsl #12
    (0x914007e0, "add x0, sp, #0x1, lsl #12", Flow::Next, None),
    // ASM: sub sp, sp, #0x20
    (0xd10083ff, "sub sp, sp, #0x20", Flow::Next, None),
    // ASM: cmp w0, #0x3
    (0x71000c1f, "cmp w0, #0x3", Flow::Next, None),
    // ASM: cmn x1, #0x1
    (0xb100043f, "cmn x1, #0x1", Flow::Next, None),
    // ASM: adds x0, x1, x2
    (0xab020020, "adds x0, x1, x2", Flow::Next, None),
    // ASM: subs w0, w1, w2, lsl #2
    (0x6b020820, "subs w0, w1, w2, lsl #2", Flow::Next, None),
    // ASM: and x0, x1, #0xff
    (0x92401c20, "and x0, x1, #0xff", Flow::Next, None),
    // ASM: orr w0, w1, w2
    (0x2a020020, "orr w0, w1, w2", Flow::Next, None),
    // ASM: eor x0, x1, x2, lsr #3
    (0xca420c20, "eor x0, x1, x2, lsr #3", Flow::Next, None),
    // ASM: tst w0, #0x1
    (0x7200001f, "tst w0, #0x1", Flow::Next, None),
    // ASM: lsl x0, x1, #4
    (0xd37cec20, "lsl x0, x1, #0x4", Flow::Next, None),
    // ASM: lsr w0, w1, #2
    (0x53027c20, "lsr w0, w1, #0x2", Flow::Next, None),
    // ASM: asr x0, x1, #63
    (0x937ffc20, "asr x0, x1, #0x3f", Flow::Next, None),
    // ASM: mul x0, x1, x2
    (0x9b027c20, "mul x0, x1, x2", Flow::Next, None),
    // ASM: sdiv w0, w1, w2
    (0x1ac20c20, "sdiv w0, w1, w2", Flow::Next, None),
    // ASM: csel x0, x1, x2, ne
    (0x9a821020, "csel x0, x1, x2, ne", Flow::Next, None),
    // ASM: cset w0, eq
    (0x1a9f17e0, "cset w0, eq", Flow::Next, None),
    // ASM: ccmp x0, #0x2, #0x0, hs
    (0xfa422800, "ccmp x0, #0x2, #0x0, hs", Flow::Next, None),
    // ASM: ldr x0, [x1]
    (0xf9400020, "ldr x0, [x1]", Flow::Next, None),
    // ASM: ldr w0, [x1, #8]
    (0xb9400820, "ldr w0, [x1, #0x8]", Flow::Next, None),
    // ASM: str x0, [sp, #16]
    (0xf9000be0, "str x0, [sp, #0x10]", Flow::Next, None),
    // ASM: stp x29, x30, [sp, #-16]!
    (0xa9bf7bfd, "stp x29, x30, [sp, #-0x10]!", Flow::Next, None),
    // ASM: ldp x29, x30, [sp], #16
    (0xa8c17bfd, "ldp x29, x30, [sp], #0x10", Flow::Next, None),
    // ASM: ldrb w0, [x1, #1]
    (0x39400420, "ldrb w0, [x1, #0x1]", Flow::Next, None),
    // ASM: ldrsw x0, [x1, #4]
    (0xb9800420, "ldrsw x0, [x1, #0x4]", Flow::Next, None),
    // ASM: ldr x0, [x1, x2, lsl #3]
    (0xf8627820, "ldr x0, [x1, x2, lsl #3]", Flow::Next, None),
    // ASM: ldr w0, [x1, w2, sxtw #2]
    (0xb862d820, "ldr w0, [x1, w2, sxtw #2]", Flow::Next, None),
    // ASM: ldur x0, [x1, #-8]
    (0xf85f8020, "ldur x0, [x1, #-0x8]", Flow::Next, None),
    // ASM: nop
    (0xd503201f, "nop", Flow::Next, None),
    // ASM: bti c
    (0xd503245f, "bti c", Flow::Next, None),
    // ASM: bti j
    (0xd503249f, "bti j", Flow::Next, None),
    // ASM: bti jc
    (0xd50324df, "bti jc", Flow::Next, None),
    // ASM: bti
    (0xd503241f, "bti", Flow::Next, None),
    // ASM: paciasp
    (0xd503233f, "paciasp", Flow::Next, None),
    // ASM: autiasp
    (0xd50323bf, "autiasp", Flow::Next, None),
    // ASM: pacibsp
    (0xd503237f, "pacibsp", Flow::Next, None),
    // ASM: xpaclri
    (0xd50320ff, "xpaclri", Flow::Next, None),
    // ASM: yield
    (0xd503203f, "yield", Flow::Next, None),
    // ASM: pacia x0, x1
    (0xdac10020, "pacia x0, x1", Flow::Next, None),
    // ASM: autia x0, sp
    (0xdac113e0, "autia x0, sp", Flow::Next, None),
    // ASM: xpaci x0
    (0xdac143e0, "xpaci x0", Flow::Next, None),
    // ASM: ldraa x0, [x1, #8]
    (0xf8201420, "ldraa x0, [x1, #0x8]", Flow::Next, None),
    // ASM: fmov d0, x1
    (0x9e670020, "fmov d0, x1", Flow::Next, None),
    // ASM: fadd s0, s1, s2
    (0x1e222820, "fadd s0, s1, s2", Flow::Next, None),
    // ASM: mrs x0, tpidr_el0
    (0xd53bd040, "mrs x0, tpidr_el0", Flow::Next, None),
    // ASM: dmb ish
    (0xd5033bbf, "dmb ish", Flow::Next, None),
    // ASM: isb
    (0xd5033fdf, "isb", Flow::Next, None),
    // ASM: adrp x8, 0x13000
    (0xf0000008, "adrp x8, 0x13000", Flow::Next, None),
    // ASM: adrp x9, 0xf000
    (0xf0ffffe9, "adrp x9, 0xf000", Flow::Next, None),
    // ASM: add z0.d, z1.d, z2.d (SVE)
    (0x04e20020, ".inst 0x04e20020 ; sve", Flow::Next, None),
    // ASM: zero {za} (SME)
    (0xc00800ff, ".inst 0xc00800ff ; sme", Flow::Next, None),
    // ASM: (unallocated) br with op2 0b00000 instead of 0b11111
    (0xd6000000, "(bad)", Flow::Invalid, None),
    // ASM: (unallocated) b.cond with o1, bit 24, set
    (0x57000000, "(bad)", Flow::Invalid, None),
    // ASM: (unallocated) the reserved space, op1 not zero
    (0x00010000, "(bad)", Flow::Invalid, None),
    // ASM: ld1 {v0.16b}, [x0]
    (0x4c407000, "ld1 {v0.16b}, [x0]", Flow::Next, None),
    // ASM: movi v0.2d, #0
    (0x6f00e400, "movi v0.2d, #0x0", Flow::Next, None),
    // ASM: ldr x0, 0x10164
    (0x58000000, "ldr x0, 0x10164", Flow::Next, None),
    // ASM: fmov d0, #2.0
    (0x1e601000, "fmov d0, #2.0", Flow::Next, None),
    // ASM: hvc #0
    (0xd4000002, "hvc #0x0", Flow::Next, None),
    // ASM: hint #0x23
    (0xd503247f, "hint #0x23", Flow::Next, None),
];

/// Every word of the table decodes to its text, flow and target, at the
/// address the assembler placed it.
#[test]
fn words_decode_to_their_text_flow_and_target() {
    let mut va = BASE;
    for &(word, text, flow, target) in WORDS {
        let insn = a64::decode(word, va);
        assert_eq!(
            (a64::text(&insn).as_str(), insn.flow, insn.target()),
            (text, flow, target),
            "{word:#010x} at {va:#x}"
        );
        assert_eq!((insn.va, insn.word, insn.flow), (va, word, insn.op.flow()));
        va += 4;
    }
}

/// The operands are engine values: an `adrp` names its page, a pre-indexed
/// store its base, offset and write-back, a register-offset load its
/// extended index, and a comparison writes the zero register.
#[test]
fn operands_carry_pages_memory_and_registers() {
    // ASM: adrp x9, 0xf000 (at 0x10144, one page below its own)
    let adrp = a64::decode(0xf0ff_ffe9, 0x10144);
    assert_eq!(adrp.op, Op::Adrp);
    assert_eq!(
        adrp.operands[..2],
        [
            Opnd::Reg {
                reg: Reg::X(9),
                bits: 64
            },
            Opnd::PcRel(0xf000)
        ]
    );
    // ASM: stp x29, x30, [sp, #-16]!
    let stp = a64::decode(0xa9bf_7bfd, 0);
    assert_eq!(
        stp.operands[2],
        Opnd::Mem(Mem {
            base: Reg::Sp,
            index: None,
            extend: Shift::Lsl,
            shift: 0,
            disp: -16,
            mode: Mode::PreIndex,
        })
    );
    // ASM: ldr w0, [x1, w2, sxtw #2]
    let ldr = a64::decode(0xb862_d820, 0);
    assert_eq!(
        ldr.operands[1],
        Opnd::Mem(Mem {
            base: Reg::X(1),
            index: Some((Reg::X(2), 32)),
            extend: Shift::Sxtw,
            shift: 2,
            disp: 0,
            mode: Mode::Offset,
        })
    );
    // ASM: cmp w0, #0x3
    let cmp = a64::decode(0x7100_0c1f, 0);
    assert_eq!(
        cmp.operands[..3],
        [
            Opnd::Reg {
                reg: Reg::Zr,
                bits: 32
            },
            Opnd::Reg {
                reg: Reg::X(0),
                bits: 32
            },
            Opnd::Imm(3)
        ]
    );
}

/// Pointer authentication and branch target identification decode as
/// what they are, and an authenticated branch as the branch it
/// authenticates: `retaa` is a return, `braa` an indirect jump.
#[test]
fn authenticated_branches_keep_the_plain_branch_class() {
    // ASM: paciasp
    assert_eq!(a64::decode(0xd503_233f, 0).op, Op::Pac);
    // ASM: bti c
    assert_eq!(a64::decode(0xd503_245f, 0).op, Op::Bti);
    // ASM: hint #0x23, one past bti c and not a bti
    assert_eq!(a64::decode(0xd503_247f, 0).op, Op::Nop);
    // ASM: retaa
    assert_eq!(a64::decode(0xd65f_0bff, 0).op, Op::Ret);
    // ASM: braa x16, x17
    assert_eq!(a64::decode(0xd71f_0a11, 0).op, Op::Br);
    // ASM: blraa x8, sp
    assert_eq!(a64::decode(0xd73f_091f, 0).op, Op::Blr);
}

/// The code every image fixture holds at its entry: a guarded frame that
/// calls a helper six words on.
const BLOCK: [u32; 8] = [
    // ASM: bti c
    0xd503_245f,
    // ASM: stp x29, x30, [sp, #-16]!
    0xa9bf_7bfd,
    // ASM: bl entry+0x18
    0x9400_0004,
    // ASM: ldp x29, x30, [sp], #16
    0xa8c1_7bfd,
    // ASM: ret
    0xd65f_03c0,
    // ASM: nop
    0xd503_201f,
    // ASM: add w0, w0, #1
    0x1100_0400,
    // ASM: ret
    0xd65f_03c0,
];

/// Returns [`BLOCK`] as the bytes an image stores.
fn block_bytes() -> Vec<u8> {
    BLOCK.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// Checks that an arm64 program disassembles [`BLOCK`] at its entry, word
/// by word with the call's target, that an address inside a word lists
/// from the word, and that disassembly is all that applies yet.
fn check_disassembles(p: &Program, entry: u64) {
    assert_eq!((p.arch, p.is_64, p.entry), (Arch::Arm64, true, Some(entry)));
    let code = p.read_va(entry, 32).expect("the block is mapped");
    let lines = disasm::disassemble_isa(code, entry, Isa::A64, 64);
    let call = format!("bl {:#x}", entry + 0x18);
    let text: Vec<&str> = lines.iter().map(|l| l.text.as_str()).collect();
    assert_eq!(
        text,
        [
            "bti c",
            "stp x29, x30, [sp, #-0x10]!",
            call.as_str(),
            "ldp x29, x30, [sp], #0x10",
            "ret",
            "nop",
            "add w0, w0, #0x1",
            "ret"
        ]
    );
    assert_eq!(lines[2].target, Some(entry + 0x18));
    assert!(
        lines
            .iter()
            .zip(0u64..)
            .all(|(l, i)| l.va == entry + 4 * i && l.bytes.len() == 4)
    );
    assert_eq!(p.isa_for(Feature::Disasm), Ok(Isa::A64));
    let why = p
        .refuses(Feature::Discover)
        .expect("functions are not discovered yet");
    assert!(
        why.contains("arch 'arm64': borer disassembles arm64 code")
            && why.contains("does not yet discover its functions"),
        "{why}"
    );
    assert!(p.summary().contains(&why), "{}", p.summary());
    let a = Analysis::compute(p);
    assert!(a.functions.is_empty());
    assert_eq!(
        render::instruction_at_or_before(p, &a, entry + 6),
        Some(entry + 4)
    );
}

/// A thin arm64 Mach-O: the x86-64 fixture with its CPU type set to
/// `CPU_TYPE_ARM64` and arm64 code at its entry.
#[test]
fn a_thin_arm64_macho_disassembles_at_its_entry() {
    let mut bytes = crate::macho::thin();
    bytes[4..8].copy_from_slice(&0x0100_000cu32.to_le_bytes());
    bytes[8..12].copy_from_slice(&0u32.to_le_bytes());
    bytes[0x300..0x320].copy_from_slice(&block_bytes());
    let p = Program::from_bytes(PathBuf::from("arm64.macho"), bytes).expect("parses");
    assert_eq!(p.format, BinaryFormat::MachO);
    check_disassembles(&p, crate::macho::MAIN);
}

/// An arm64 ELF: the x86-64 fixture with `e_machine` set to `EM_AARCH64`
/// (183) and arm64 code at its entry.
#[test]
fn an_arm64_elf_disassembles_at_its_entry() {
    let mut bytes = crate::elf::elf_bytes(false);
    bytes[0x12..0x14].copy_from_slice(&183u16.to_le_bytes());
    bytes[0x180..0x1a0].copy_from_slice(&block_bytes());
    let p = Program::from_bytes(PathBuf::from("arm64.elf"), bytes).expect("parses");
    assert_eq!(p.format, BinaryFormat::Elf);
    check_disassembles(&p, crate::elf::MAIN);
}

/// An arm64 PE: one code section entered at its start, with the COFF
/// machine set to `IMAGE_FILE_MACHINE_ARM64` (`0xaa64`).
#[test]
fn an_arm64_pe_disassembles_at_its_entry() {
    let mut bytes = crate::protection::pe(
        &[crate::protection::sec(".text", 0x1000, block_bytes())],
        0x1000,
    );
    let machine = crate::protection::PE_AT + 4;
    bytes[machine..machine + 2].copy_from_slice(&0xaa64u16.to_le_bytes());
    let p = Program::from_bytes(PathBuf::from("arm64.exe"), bytes).expect("parses");
    assert_eq!(p.format, BinaryFormat::Pe);
    check_disassembles(&p, crate::protection::IMAGE_BASE + 0x1000);
}

/// A raw arm64 image, built in memory with no container, is 64-bit and
/// disassembles like a loaded one.
#[test]
fn a_raw_arm64_image_disassembles_at_its_entry() {
    let p = crate::raw::image(Arch::Arm64, &block_bytes(), &[]);
    check_disassembles(&p, 0x40_1000);
}

/// Trailing bytes too few for a word are one `(bad)` line that keeps them,
/// rather than being dropped, and the instruction cap holds.
#[test]
fn a_truncated_last_word_keeps_its_bytes() {
    let mut code = block_bytes();
    code.truncate(10);
    let lines = disasm::disassemble_isa(&code, 0x1000, Isa::A64, 16);
    assert_eq!(lines.len(), 3);
    assert_eq!(
        (
            lines[2].va,
            lines[2].bytes.as_slice(),
            lines[2].text.as_str(),
            lines[2].target
        ),
        (0x1008, &[0x04, 0x00][..], "(bad)", None)
    );
    assert_eq!(disasm::disassemble_isa(&code, 0x1000, Isa::A64, 1).len(), 1);
}

/// Every one of the 2^32 words decodes to one line of four bytes.
///
/// A word is all the input one instruction has, so the sweep proves that no
/// input reaches a panic in the decoder or its text.
#[test]
#[ignore = "decodes all 2^32 words: minutes on every core"]
fn every_word_decodes_to_one_line_of_four_bytes() {
    /// Chunks of [`CHUNK`] words each, and words per chunk: 2^16 each.
    const CHUNK: u32 = 1 << 16;
    /// The same count as a line count.
    const LINES: usize = 1 << 16;
    let next = AtomicU32::new(0);
    let threads = std::thread::available_parallelism().map_or(4, std::num::NonZero::get);
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let chunk = next.fetch_add(1, Ordering::Relaxed);
                    if chunk >= CHUNK {
                        break;
                    }
                    let first = chunk << 16;
                    let code: Vec<u8> = (first..=first | (CHUNK - 1))
                        .flat_map(u32::to_le_bytes)
                        .collect();
                    let lines =
                        disasm::disassemble_isa(&code, u64::from(first) << 2, Isa::A64, LINES);
                    assert_eq!(lines.len(), LINES, "chunk {chunk:#x}");
                    assert!(
                        lines
                            .iter()
                            .all(|l| l.bytes.len() == 4 && !l.text.is_empty()),
                        "chunk {chunk:#x}"
                    );
                }
            });
        }
    });
}

// ---- unwind tables ----

/// Returns words as the bytes an image stores.
fn le_words(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// Where [`crate::protection::pe`] puts the exception directory's row: the
/// fourth data directory of the PE32+ optional header.
const EXCEPTION_DIR: usize = crate::protection::PE_AT + 24 + 112 + 3 * 8;

/// Builds the bytes of an arm64 PE: `code` in `.text` at 0x1000, entered
/// there; the `.pdata` entries at 0x2000, which the exception directory
/// names; and `xdata` at 0x3000.
///
/// # Arguments
///
/// * `code` - The words of `.text`.
/// * `pdata` - The entries: a start relative to the image base, and the
///   unwind word.
/// * `xdata` - The words of `.xdata`.
fn arm64_pe_bytes(code: &[u32], pdata: &[(u32, u32)], xdata: &[u32]) -> Vec<u8> {
    let entries: Vec<u32> = pdata
        .iter()
        .flat_map(|&(at, unwind)| [at, unwind])
        .collect();
    let mut bytes = crate::protection::pe(
        &[
            crate::protection::sec(".text", 0x1000, le_words(code)),
            crate::protection::data(".pdata", 0x2000, le_words(&entries)),
            crate::protection::data(".xdata", 0x3000, le_words(xdata)),
        ],
        0x1000,
    );
    let machine = crate::protection::PE_AT + 4;
    bytes[machine..machine + 2].copy_from_slice(&0xaa64u16.to_le_bytes());
    let size = u32::try_from(entries.len() * 4).expect("a few entries");
    bytes[EXCEPTION_DIR..EXCEPTION_DIR + 4].copy_from_slice(&0x2000u32.to_le_bytes());
    bytes[EXCEPTION_DIR + 4..EXCEPTION_DIR + 8].copy_from_slice(&size.to_le_bytes());
    bytes
}

/// Code an arm64 PE's `.pdata` describes: a framed function at 0x1000, a
/// leaf at 0x1010 and a fragment at 0x1018.
const PDATA_CODE: [u32; 8] = [
    // ASM: stp x29, x30, [sp, #-16]!
    0xa9bf_7bfd,
    // ASM: mov x29, sp
    0x9100_03fd,
    // ASM: ldp x29, x30, [sp], #16
    0xa8c1_7bfd,
    // ASM: ret
    0xd65f_03c0,
    // ASM: add w0, w0, #1
    0x1100_0400,
    // ASM: ret
    0xd65f_03c0,
    // ASM: mov w0, #0
    0x5280_0000,
    // ASM: ret
    0xd65f_03c0,
];

/// The `.pdata` of [`PDATA_CODE`].
///
/// A packed function 16 bytes long (flag 1, length 4 words), a function
/// whose `.xdata` record at 0x3000 states 8 bytes, and a packed fragment 8
/// bytes long (flag 2, length 2 words).
const PDATA: [(u32, u32); 3] = [(0x1000, 1 | 4 << 2), (0x1010, 0x3000), (0x1018, 2 | 2 << 2)];

/// The `.xdata` record [`PDATA`] names: a function length of 2 words, the
/// epilog in the header (bit 21) and one word of unwind codes (bits 27 to
/// 31), then that word: `end` and three `nop`s.
const XDATA: [u32; 2] = [2 | 1 << 21 | 1 << 27, 0xe3e3_e3e4];

/// An arm64 PE's `.pdata` declares its functions, packed and through an
/// `.xdata` record alike, each with the extent its entry states; a
/// fragment is a chunk of a function, not one.
#[test]
fn pdata_declares_packed_and_xdata_functions_but_not_fragments() {
    let bytes = arm64_pe_bytes(&PDATA_CODE, &PDATA, &XDATA);
    let p = Program::from_bytes(PathBuf::from("pdata.exe"), bytes).expect("parses");
    let base = crate::protection::IMAGE_BASE;
    assert_eq!(p.arch, Arch::Arm64);
    assert_eq!(
        p.function_ranges,
        [
            (base + 0x1000, base + 0x1010),
            (base + 0x1010, base + 0x1018)
        ]
    );
    assert_eq!(p.headers.chained_chunks, [(base + 0x1018, base + 0x1020)]);
}

/// Damaged `.pdata` declares nothing, and the image still loads.
///
/// An entry with the reserved flag, one whose `.xdata` record lies outside
/// every section and one stating no length each declare nothing, and a
/// directory that runs past the end of the file declares nothing rather
/// than faulting.
#[test]
fn hostile_pdata_declares_nothing() {
    let mut bytes = arm64_pe_bytes(
        &PDATA_CODE,
        &[(0x1000, 3), (0x1008, 0x00ff_fff0), (0x1010, 1)],
        &XDATA,
    );
    let p = Program::from_bytes(PathBuf::from("pdata.exe"), bytes.clone()).expect("loads");
    assert!(p.function_ranges.is_empty(), "{:x?}", p.function_ranges);
    assert!(p.headers.chained_chunks.is_empty());
    bytes[EXCEPTION_DIR + 4..EXCEPTION_DIR + 8].copy_from_slice(&0x0fff_fff8u32.to_le_bytes());
    let p = Program::from_bytes(PathBuf::from("pdata.exe"), bytes).expect("still loads");
    assert!(p.function_ranges.is_empty(), "{:x?}", p.function_ranges);
}
