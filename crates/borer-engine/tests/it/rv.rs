//! RISC-V images: the loader's machine, and the decoder.
//!
//! An ELF for `EM_RISCV` loads as RV64 or RV32 by its class. Every form the
//! tests list, hand-encoded from the ISA manual's tables, reads as GNU
//! objdump reads it with its aliases, a compressed instruction as what it expands to; each
//! decodes to the control flow it has; random bytes decode and print
//! without a panic.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::disasm;
use borer_engine::isa::Isa;
use borer_engine::isa::rv::{Flow, Xlen, decode, text};
use borer_engine::program::{Arch, Feature, Program};

use crate::elfgen::{self, AX, ET_EXEC, PROGBITS, Sec};

/// `EM_RISCV`.
pub(crate) const EM_RISCV: u16 = 243;

/// Where the test images map their code.
pub(crate) const TEXT: u64 = 0x1_0000;

/// Forms of RV64GC: the address, the encoding (two bytes for a compressed
/// instruction) and the text.
const RV64_FORMS: &[(u64, u32, u8, &str)] = &[
    (0x1000, 0x1141, 2, "addi sp, sp, -16"),
    (0x1000, 0xe406, 2, "sd ra, 8(sp)"),
    (0x1000, 0x0800, 2, "addi s0, sp, 16"),
    (0x1000, 0x60a2, 2, "ld ra, 8(sp)"),
    (0x1000, 0x8082, 2, "ret"),
    (0x1000, 0x4501, 2, "li a0, 0"),
    (0x1000, 0x85aa, 2, "mv a1, a0"),
    (0x1000, 0x0505, 2, "addi a0, a0, 1"),
    (0x1000, 0x357d, 2, "addiw a0, a0, -1"),
    (0x1000, 0x2501, 2, "sext.w a0, a0"),
    (0x1000, 0x9d2d, 2, "addw a0, a0, a1"),
    (0x1000, 0x8d0d, 2, "sub a0, a0, a1"),
    (0x1000, 0x6785, 2, "lui a5, 0x1"),
    (0x1000, 0x7139, 2, "addi sp, sp, -64"),
    (0x1000, 0x8782, 2, "jr a5"),
    (0x1000, 0x9782, 2, "jalr a5"),
    (0x1000, 0x9002, 2, "ebreak"),
    (0x1000, 0x1502, 2, "slli a0, a0, 0x20"),
    (0x1000, 0x9101, 2, "srli a0, a0, 0x20"),
    (0x1000, 0x41c8, 2, "lw a0, 4(a1)"),
    (0x1000, 0x6588, 2, "ld a0, 8(a1)"),
    (0x1000, 0xc119, 2, "beqz a0, 0x1006"),
    (0x1000, 0xa001, 2, "j 0x1000"),
    (0x1000, 0x0000, 2, "(bad)"),
    (0x1000, 0x0000_0013, 4, "nop"),
    (0x1000, 0x0000_0073, 4, "ecall"),
    (0x1000, 0x0010_0073, 4, "ebreak"),
    (0x1000, 0x00a5_0533, 4, "add a0, a0, a0"),
    (0x1000, 0xfe01_0113, 4, "addi sp, sp, -32"),
    (0x1000, 0x0011_3c23, 4, "sd ra, 24(sp)"),
    (0x1c, 0xfe5f_f0ef, 4, "jal 0x0"),
    (0x1000, 0x0000_1517, 4, "auipc a0, 0x1"),
    (0x1000, 0x0055_3513, 4, "sltiu a0, a0, 5"),
    (0x1000, 0x3020_0073, 4, "mret"),
    (0x1000, 0x0020_0073, 4, "uret"),
    (0x1000, 0x1200_0073, 4, "sfence.vma zero, zero"),
    (0x1000, 0x000e_0367, 4, "jalr t1, t3"),
    (0x1000, 0x0005_0513, 4, "mv a0, a0"),
    (0x1000, 0x00b5_0463, 4, "beq a0, a1, 0x1008"),
    (0x1000, 0x0001_25b7, 4, "lui a1, 0x12"),
    (0x1000, 0x02b5_0533, 4, "mul a0, a0, a1"),
    (0x1000, 0x02b5_453b, 4, "divw a0, a0, a1"),
    (0x1000, 0x02b5_7553, 4, "fadd.d fa0, fa0, fa1"),
    (0x1000, 0xd205_0553, 4, "fcvt.d.w fa0, a0"),
    (0x1000, 0xc205_1553, 4, "fcvt.w.d a0, fa0, rtz"),
    (0x1000, 0xf205_0553, 4, "fmv.d.x fa0, a0"),
    (0x1000, 0x0081_3507, 4, "fld fa0, 8(sp)"),
    (0x1000, 0x06b6_252f, 4, "amoadd.w.aqrl a0, a1, (a2)"),
    (0x1000, 0x1005_b52f, 4, "lr.d a0, (a1)"),
    (0x1000, 0x0010_2573, 4, "csrr a0, fflags"),
    (0x1000, 0x0ff0_000f, 4, "fence"),
    (0x1000, 0x0330_000f, 4, "fence rw, rw"),
    (0x1000, 0x4005_5513, 4, "srai a0, a0, 0x0"),
    (0x1000, 0x0205_7557, 4, ".4byte 0x2057557"),
];

/// Every listed RV64 form decodes to its instruction and prints as objdump
/// reads it, its length the encoding's.
#[test]
fn every_rv64_form_decodes_and_prints() {
    for &(va, word, len, want) in RV64_FORMS {
        let bytes = word.to_le_bytes();
        let i = decode(&bytes[..usize::from(len)], va, Xlen::X64).expect("decodes");
        assert_eq!(text(&i), want, "{va:#x} {word:#x}");
        assert_eq!(i.len, len, "{want}");
    }
}

/// The encodings RV32 and RV64 read differently: `c.jal` against
/// `c.addiw`, `c.flw` against `c.ld`, and the RV64-only shifts and loads.
#[test]
fn rv32_reads_its_own_compressed_forms() {
    let cases: [(u32, u8, &str, &str); 4] = [
        (0x2001, 2, "jal 0x1000", "(bad)"),
        (0x6588, 2, "flw fa0, 8(a1)", "ld a0, 8(a1)"),
        (0x0005_3503, 4, "(bad)", "ld a0, 0(a0)"),
        (0x1502, 2, "(bad)", "slli a0, a0, 0x20"),
    ];
    for (word, len, rv32, rv64) in cases {
        let bytes = word.to_le_bytes();
        let bytes = &bytes[..usize::from(len)];
        let at32 = decode(bytes, 0x1000, Xlen::X32).expect("decodes");
        let at64 = decode(bytes, 0x1000, Xlen::X64).expect("decodes");
        assert_eq!((text(&at32).as_str(), text(&at64).as_str()), (rv32, rv64));
    }
}

/// Each instruction moves control as it links.
///
/// A call links in `ra` or `t0`, a `jr` through either or a trap return
/// returns, `sfence.vma` falls through, any other `jal` or `jalr` jumps,
/// a branch is conditional and `ebreak` and an undecodable word stop.
#[test]
fn each_instruction_moves_control_as_it_links() {
    let cases: [(u32, u8, Flow); 13] = [
        (0x3020_0073, 4, Flow::Return),
        (0x1020_0073, 4, Flow::Return),
        (0x1200_0073, 4, Flow::Next),
        (0x8082, 2, Flow::Return),
        (0x8282, 2, Flow::Return),
        (0xfe5f_f0ef, 4, Flow::Call),
        (0xa001, 2, Flow::Jump),
        (0x8782, 2, Flow::Jump),
        (0x9782, 2, Flow::Call),
        (0xc119, 2, Flow::CondJump),
        (0x9002, 2, Flow::Invalid),
        (0x0000, 2, Flow::Invalid),
        (0x0505, 2, Flow::Next),
    ];
    for (word, len, flow) in cases {
        let bytes = word.to_le_bytes();
        let i = decode(&bytes[..usize::from(len)], 0x1000, Xlen::X64).expect("decodes");
        assert_eq!(i.flow(), flow, "{}", text(&i));
    }
}

/// Bytes too few for the instruction, and an odd address, decode to
/// nothing.
#[test]
fn a_cut_instruction_decodes_to_nothing() {
    assert!(decode(&[0x13], 0x1000, Xlen::X64).is_none());
    assert!(decode(&[0x13, 0x00], 0x1000, Xlen::X64).is_none());
    assert!(decode(&[0x01, 0x45], 0x1001, Xlen::X64).is_none());
}

/// Random words and every halfword decode and print at both widths without
/// a panic.
#[test]
fn random_bytes_decode_without_a_panic() {
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    for k in 0..=u16::MAX {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        let mut bytes = x.to_le_bytes();
        bytes[..2].copy_from_slice(&k.to_le_bytes());
        for xlen in [Xlen::X32, Xlen::X64] {
            if let Some(i) = decode(&bytes, 0x1_0000, xlen) {
                assert!(!text(&i).is_empty());
                assert!(i.len == 2 || i.len == 4);
            }
        }
    }
}

/// A 64-bit `EM_RISCV` executable with `code` as its `.text` at [`TEXT`].
///
/// # Arguments
///
/// * `code` - The code.
pub(crate) fn elf64(code: &[u8]) -> Vec<u8> {
    elfgen::build(
        ET_EXEC,
        EM_RISCV,
        TEXT,
        &[Sec::new(".text", PROGBITS, AX, TEXT, code.to_vec())],
    )
}

/// An `EM_RISCV` ELF64 loads as RV64, and its code lists through the
/// program's instruction set, compressed and full-width instructions mixed.
#[test]
fn a_riscv_elf_loads_and_lists() {
    let code: [u8; 12] = [
        0x41, 0x11, // ASM: addi sp, sp, -16
        0x06, 0xe4, // ASM: sd ra, 8(sp)
        0x13, 0x05, 0xa0, 0x02, // ASM: li a0, 42
        0xa2, 0x60, // ASM: ld ra, 8(sp)
        0x82, 0x80, // ASM: ret
    ];
    let p = Program::from_bytes("rv.elf".into(), elf64(&code)).expect("loads");
    assert_eq!(p.arch, Arch::RiscV64);
    assert_eq!(p.arch.isa(), Some(Isa::Rv(Xlen::X64)));
    assert!(p.refuses(Feature::Disasm).is_none());
    let bytes = p.read_va(TEXT, code.len()).expect("mapped");
    let lines: Vec<String> = disasm::disassemble_program(&p, bytes, TEXT, Isa::Rv(Xlen::X64), 16)
        .into_iter()
        .map(|l| format!("{:x} {}", l.va, l.text))
        .collect();
    assert_eq!(
        lines,
        [
            "10000 addi sp, sp, -16",
            "10002 sd ra, 8(sp)",
            "10004 li a0, 42",
            "10008 ld ra, 8(sp)",
            "1000a ret"
        ]
    );
}
