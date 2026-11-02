//! RISC-V images: the loader's machine, the decoder and discovery.
//!
//! An ELF for `EM_RISCV` loads as RV64 or RV32 by its class. Every form the
//! tests list, hand-encoded from the ISA manual's tables, reads as GNU
//! objdump reads it with its aliases, a compressed instruction as what it
//! expands to; each decodes to the control flow it has; random bytes
//! decode and print without a panic. Discovery follows the `auipc` pairs
//! and names a PLT entry after its import.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, RefKind};
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

/// The PLT entry of `puts` in [`linked`].
const PLT_PUTS: u64 = 0x1_0040;
/// The GOT slot `puts` binds.
const GOT_PUTS: u64 = 0x1_2000;
/// The string `main` addresses.
const GREETING: u64 = 0x1_1000;
/// The local function `main` calls through `auipc` and `jalr`.
const HELPER: u64 = 0x1_0030;

/// `R_RISCV_JUMP_SLOT`.
const R_JUMP_SLOT: u32 = 5;

/// `main` of [`linked`]: it addresses [`GREETING`] with `auipc` and
/// `addi`, calls [`HELPER`] with `auipc` and `jalr`, and calls `puts`
/// through its PLT entry.
const MAIN: [(usize, u32, usize); 10] = [
    (0x00, 0x1141, 2),      // ASM: addi sp, sp, -16
    (0x02, 0xe406, 2),      // ASM: sd ra, 8(sp)
    (0x04, 0x0000_1517, 4), // ASM: auipc a0, 0x1
    (0x08, 0xffc5_0513, 4), // ASM: addi a0, a0, -4
    (0x0c, 0x0000_0097, 4), // ASM: auipc ra, 0x0
    (0x10, 0x0240_80e7, 4), // ASM: jalr 36(ra)
    (0x14, 0x02c0_00ef, 4), // ASM: jal 0x10040
    (0x18, 0x60a2, 2),      // ASM: ld ra, 8(sp)
    (0x1a, 0x0141, 2),      // ASM: addi sp, sp, 16
    (0x1c, 0x8082, 2),      // ASM: ret
];

/// A dynamically linked RV64 executable: [`MAIN`] at [`TEXT`].
fn linked() -> Program {
    linked_with(&MAIN)
}

/// A dynamically linked RV64 executable.
///
/// `main` at [`TEXT`] is the code given; [`HELPER`] loads 7 into `a0`,
/// and `puts` is called through its PLT entry at [`PLT_PUTS`], whose GOT
/// slot a `JUMP_SLOT` relocation binds.
///
/// # Arguments
///
/// * `main` - Each instruction's offset in `.text`, encoding and length.
fn linked_with(main: &[(usize, u32, usize)]) -> Program {
    let mut text = vec![0u8; 0x50];
    let rest: [(usize, u32, usize); 4] = [
        (0x30, 0x451d, 2),      // ASM: li a0, 7
        (0x32, 0x8082, 2),      // ASM: ret
        (0x40, 0x0000_2e17, 4), // ASM: auipc t3, 0x2
        (0x44, 0xfc0e_3e03, 4), // ASM: ld t3, -64(t3)
    ];
    for &(at, w, n) in main.iter().chain(&rest) {
        text[at..at + n].copy_from_slice(&w.to_le_bytes()[..n]);
    }
    text[0x48..0x4c].copy_from_slice(&0x000e_0367u32.to_le_bytes()); // ASM: jalr t1, 0(t3)
    text[0x4c..0x50].copy_from_slice(&0x0000_0013u32.to_le_bytes()); // ASM: nop
    let dynstr = b"\0puts\0".to_vec();
    let mut dynsym = vec![0u8; 24];
    dynsym.extend(elfgen::sym(1, 0x12, 0, 0));
    let rela = elfgen::rela(GOT_PUTS, 1, R_JUMP_SLOT, 0);
    let dynamic = elfgen::dynamic(&[
        (23, 0x1_3000),
        (2, 24),
        (20, 7),
        (6, 0x1_3100),
        (5, 0x1_3200),
        (10, 6),
        (11, 24),
    ]);
    let mut secs = vec![
        Sec::new(".text", PROGBITS, AX, TEXT, text),
        Sec::new(".rodata", PROGBITS, elfgen::A, GREETING, b"hi\0".to_vec()),
        Sec::new(".got.plt", PROGBITS, elfgen::WA, GOT_PUTS, vec![0; 16]),
        Sec::new(".rela.plt", elfgen::RELA, elfgen::A, 0x1_3000, rela),
        Sec::new(".dynsym", elfgen::DYNSYM, elfgen::A, 0x1_3100, dynsym),
        Sec::new(".dynstr", elfgen::STRTAB, elfgen::A, 0x1_3200, dynstr),
        Sec::new(".dynamic", elfgen::DYNAMIC, elfgen::WA, 0x1_3300, dynamic),
    ];
    secs[3].link = 5;
    secs[3].entsize = 24;
    secs[4].link = 6;
    secs[4].entsize = 24;
    secs[6].link = 6;
    secs[6].entsize = 16;
    let bytes = elfgen::build(ET_EXEC, EM_RISCV, TEXT, &secs);
    Program::from_bytes("linked.elf".into(), bytes).expect("loads")
}

/// Discovery follows the calls `auipc` and `jalr` or a `jal` make.
///
/// It names a PLT entry after the import its GOT slot binds, and
/// reads the address `auipc` and `addi` build as a data reference.
#[test]
fn discovery_resolves_auipc_pairs_and_names_plt_entries() {
    let p = linked();
    assert!(p.refuses(Feature::Discover).is_none());
    let a = Analysis::compute(&p);
    let main = a.function(TEXT).expect("main is found");
    assert_eq!(main.callees, [HELPER, PLT_PUTS]);
    assert_eq!(main.end, TEXT + 0x1e, "main ends at its ret");
    let helper = a.function(HELPER).expect("the auipc call is followed");
    assert_eq!(helper.instr_count, 2);
    let plt = a.function(PLT_PUTS).expect("the PLT entry is a function");
    assert_eq!(plt.name.as_deref(), Some("puts"));
    assert_eq!(plt.thunk, Some(GOT_PUTS));
    let calls: Vec<(u64, RefKind)> = a.xrefs_to(HELPER).iter().map(|s| (s.va, s.kind)).collect();
    assert_eq!(calls, [(TEXT + 0x10, RefKind::Call)]);
    let data: Vec<(u64, RefKind)> = a
        .xrefs_to(GREETING)
        .iter()
        .map(|s| (s.va, s.kind))
        .collect();
    assert_eq!(data, [(TEXT + 8, RefKind::Data)]);
    let slot: Vec<u64> = a.xrefs_to(GOT_PUTS).iter().map(|s| s.va).collect();
    assert_eq!(slot, [PLT_PUTS + 4], "the PLT entry's load reads its slot");
}

/// A call to a PLT entry of an import that never returns ends the path:
/// the bytes after it are not code of the caller.
#[test]
fn a_call_to_a_noreturn_import_ends_the_path() {
    let mut p = linked();
    for s in &mut p.symbols {
        if s.name == "puts" {
            s.name = "exit".to_owned();
        }
    }
    let a = Analysis::compute(&p);
    let main = a.function(TEXT).expect("main is found");
    assert_eq!(main.end, TEXT + 0x18, "nothing after the call to exit");
}

/// Random bytes as a RISC-V program's code discover without a panic, and
/// every function found holds its entry.
#[test]
fn random_code_discovers_without_a_panic() {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let code: Vec<u8> = (0..0x4000)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x.to_le_bytes()[0]
        })
        .collect();
    let p = Program::from_bytes("noise.elf".into(), elf64(&code)).expect("loads");
    let a = Analysis::compute(&p);
    for f in &a.functions {
        assert!(
            f.blocks.iter().any(|b| b.start == f.entry),
            "{:#x}",
            f.entry
        );
    }
}

/// A register a call, a system call or an instruction the engine does not
/// model stands between is not read as the address `lui` set: each may
/// have left anything in it.
#[test]
fn a_call_or_an_unmodeled_write_ends_what_lui_set() {
    let between: [u32; 3] = [
        0x00c0_00ef, // ASM: jal 0x10010
        0x40b5_7533, // ASM: andn a0, a0, a1
        0x0000_0073, // ASM: ecall
    ];
    for middle in between {
        let mut text = vec![0u8; 0x12];
        let words: [(usize, u32, usize); 5] = [
            (0x00, 0x0001_1537, 4), // ASM: lui a0, 0x11
            (0x04, middle, 4),
            (0x08, 0x0005_3583, 4), // ASM: ld a1, 0(a0)
            (0x0c, 0x8082, 2),      // ASM: ret
            (0x10, 0x8082, 2),      // ASM: ret
        ];
        for (at, w, n) in words {
            text[at..at + n].copy_from_slice(&w.to_le_bytes()[..n]);
        }
        let secs = [
            Sec::new(".text", PROGBITS, AX, TEXT, text),
            Sec::new(".rodata", PROGBITS, elfgen::A, GREETING, vec![0; 8]),
        ];
        let bytes = elfgen::build(ET_EXEC, EM_RISCV, TEXT, &secs);
        let p = Program::from_bytes("lui.elf".into(), bytes).expect("loads");
        let a = Analysis::compute(&p);
        assert!(a.function(TEXT).is_some(), "{middle:#x}");
        assert!(a.xrefs_to(GREETING).is_empty(), "{middle:#x}");
    }
}

/// A function due a second walk keeps its first one when the fuel runs out
/// first.
///
/// `main` jumps to a `ret` that `other`, walked after it, then calls, so
/// `main` is due a second walk; seventy symbols into one long run of
/// `nop`s, walked after both, spend the fuel before it.
#[test]
fn a_walk_due_again_stays_when_the_fuel_runs_out() {
    const RUN: usize = 0x1_0000;
    const OTHER: u64 = 0x3_0000;
    const MAIN: u64 = 0x3_0020;
    let mut run: Vec<u8> = 0x0001u16.to_le_bytes().repeat(RUN / 2);
    run[RUN - 2..].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    let mut code = vec![0u8; 0x40];
    code[..4].copy_from_slice(&0x0300_00efu32.to_le_bytes()); // ASM: jal 0x30030
    code[4..6].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    code[0x20..0x22].copy_from_slice(&0xa801u16.to_le_bytes()); // ASM: j 0x30030
    code[0x30..0x32].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    let entries: Vec<u64> = (0..70u64)
        .map(|k| TEXT + 2 * k)
        .chain([OTHER, MAIN])
        .collect();
    let p = symbolized(
        vec![
            Sec::new(".text", PROGBITS, AX, TEXT, run),
            Sec::new(".text.main", PROGBITS, AX, OTHER, code),
        ],
        &entries,
        MAIN,
    );
    let a = Analysis::compute(&p);
    assert!(a.incomplete, "the fuel ran out");
    assert!(a.function(MAIN).is_some(), "main keeps its first walk");
}

/// An RV64 executable of the code sections given, with a function symbol
/// at each start.
///
/// # Arguments
///
/// * `secs` - The code sections, below `0x4_0000`.
/// * `starts` - The function symbols' addresses.
/// * `entry` - The entry point.
fn symbolized(mut secs: Vec<Sec>, starts: &[u64], entry: u64) -> Program {
    let mut strtab = vec![0u8];
    let mut symtab = vec![0u8; 24];
    for (k, &at) in starts.iter().enumerate() {
        let name = u32::try_from(strtab.len()).expect("fits");
        strtab.extend_from_slice(format!("f{k}\0").as_bytes());
        symtab.extend(elfgen::sym(name, 0x12, 1, at));
    }
    let at = secs.len();
    let mut table = Sec::new(".symtab", elfgen::SYMTAB, 0, 0x4_0000, symtab);
    table.link = u32::try_from(at + 2).expect("fits");
    table.info = 1;
    table.entsize = 24;
    secs.push(table);
    secs.push(Sec::new(".strtab", elfgen::STRTAB, 0, 0x5_0000, strtab));
    let bytes = elfgen::build(ET_EXEC, EM_RISCV, entry, &secs);
    Program::from_bytes("sym.elf".into(), bytes).expect("loads")
}

/// Two functions alike but for `beq` against `bne` to the same place
/// fingerprint differently: the hash drops a branch's offset, not its
/// comparison.
#[test]
fn a_branch_keeps_its_comparison_in_the_fingerprint() {
    let mut code = vec![0u8; 0x20];
    for (at, branch) in [(0, 0x00b5_0463u32), (0x10, 0x00b5_1463)] {
        code[at..at + 4].copy_from_slice(&branch.to_le_bytes()); // ASM: beq or bne a0, a1, +8
        code[at + 4..at + 6].copy_from_slice(&0x4505u16.to_le_bytes()); // ASM: li a0, 1
        code[at + 6..at + 8].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
        code[at + 8..at + 10].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    }
    let text = vec![Sec::new(".text", PROGBITS, AX, TEXT, code)];
    let p = symbolized(text, &[TEXT, TEXT + 0x10], TEXT);
    let a = Analysis::compute(&p);
    let hash = |va| a.function(va).expect("found").body_hash;
    assert_ne!(hash(TEXT), hash(TEXT + 0x10));
}

/// Functions that load through an `auipc` pair fingerprint by the address
/// the pair forms: one reading other data differs, one reading the same
/// data from another place matches.
#[test]
fn an_auipc_load_fingerprints_by_the_address_it_forms() {
    let mut code = vec![0u8; 0x30];
    for (at, page, ld) in [
        (0, 0x0000_1517u32, 0x0005_3503u32),
        (0x10, 0x0000_2517, 0x0005_3503),
        (0x20, 0x0000_1517, 0xfe05_3503),
    ] {
        code[at..at + 4].copy_from_slice(&page.to_le_bytes()); // ASM: auipc a0, 0x1 or 0x2
        code[at + 4..at + 8].copy_from_slice(&ld.to_le_bytes()); // ASM: ld a0, 0 or -32(a0)
        code[at + 8..at + 10].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    }
    let secs = vec![
        Sec::new(".text", PROGBITS, AX, TEXT, code),
        Sec::new(
            ".data",
            PROGBITS,
            elfgen::WA,
            TEXT + 0x1000,
            vec![0; 0x2000],
        ),
    ];
    let p = symbolized(secs, &[TEXT, TEXT + 0x10, TEXT + 0x20], TEXT);
    let a = Analysis::compute(&p);
    let hash = |va| a.function(va).expect("found").body_hash;
    assert_ne!(hash(TEXT), hash(TEXT + 0x10));
    assert_eq!(hash(TEXT), hash(TEXT + 0x20));
}

/// Functions whose compressed loads through an `auipc` pair read the same
/// address into different registers fingerprint differently: the hash
/// drops the load's offset, not its registers.
#[test]
fn a_compressed_auipc_load_keeps_its_registers_in_the_fingerprint() {
    let mut code = vec![0u8; 0x20];
    for (at, ld) in [(0, 0x6b88u16), (0x10, 0x638cu16)] {
        code[at..at + 4].copy_from_slice(&0x0000_1797u32.to_le_bytes()); // ASM: auipc a5, 0x1
        code[at + 4..at + 6].copy_from_slice(&ld.to_le_bytes()); // ASM: c.ld a0, 16(a5) or c.ld a1, 0(a5)
        code[at + 6..at + 8].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    }
    let secs = vec![
        Sec::new(".text", PROGBITS, AX, TEXT, code),
        Sec::new(
            ".data",
            PROGBITS,
            elfgen::WA,
            TEXT + 0x1000,
            vec![0; 0x1000],
        ),
    ];
    let p = symbolized(secs, &[TEXT, TEXT + 0x10], TEXT);
    let a = Analysis::compute(&p);
    let hash = |va| a.function(va).expect("found").body_hash;
    assert_ne!(hash(TEXT), hash(TEXT + 0x10));
}

/// A jump `auipc` and `jr` build to a label of the same function stays in
/// it: the label is a block, not a function of its own.
#[test]
fn a_built_jump_to_a_local_label_stays_in_its_function() {
    let mut code = vec![0u8; 0x14];
    code[..4].copy_from_slice(&0x0000_0317u32.to_le_bytes()); // ASM: auipc t1, 0x0
    code[4..8].copy_from_slice(&0x0103_0067u32.to_le_bytes()); // ASM: jr 16(t1)
    code[8..10].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    code[0x10..0x12].copy_from_slice(&0x4505u16.to_le_bytes()); // ASM: li a0, 1
    code[0x12..0x14].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    let p = Program::from_bytes("jr.elf".into(), elf64(&code)).expect("loads");
    let a = Analysis::compute(&p);
    let f = a.function(TEXT).expect("found");
    assert!(f.blocks.iter().any(|b| b.start == TEXT + 0x10));
    assert!(f.callees.is_empty());
    assert!(a.function(TEXT + 0x10).is_none());
}

/// Two functions alike but for `add` against `sub` take different shapes:
/// the shape keeps each instruction's operation.
#[test]
fn a_shape_keeps_each_operation() {
    let mut code = vec![0u8; 0x10];
    for (at, op) in [(0, 0x00b5_0533u32), (8, 0x40b5_0533)] {
        code[at..at + 4].copy_from_slice(&op.to_le_bytes()); // ASM: add or sub a0, a0, a1
        code[at + 4..at + 6].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    }
    let text = vec![Sec::new(".text", PROGBITS, AX, TEXT, code)];
    let p = symbolized(text, &[TEXT, TEXT + 8], TEXT);
    let a = Analysis::compute(&p);
    let shape = |va| a.function(va).expect("found").shape_hash;
    assert_ne!(shape(TEXT), shape(TEXT + 8));
}

/// A function that ran on past a call into code a later walk calls is
/// walked again and ends at that call: the callee never returned, and the
/// code after it is the other function's.
///
/// `main` calls `helper`, which calls the code right after `main`'s call
/// and then spins; nothing names the three.
#[test]
fn a_caller_ends_at_a_call_whose_next_address_becomes_a_function() {
    let mut code = vec![0u8; 0x16];
    code[..4].copy_from_slice(&0x0100_00efu32.to_le_bytes()); // ASM: jal 0x10010
    code[4..6].copy_from_slice(&0x4505u16.to_le_bytes()); // ASM: li a0, 1
    code[6..8].copy_from_slice(&0x8082u16.to_le_bytes()); // ASM: ret
    code[0x10..0x14].copy_from_slice(&0xff5f_f0efu32.to_le_bytes()); // ASM: jal 0x10004
    code[0x14..0x16].copy_from_slice(&0xa001u16.to_le_bytes()); // ASM: j 0x10014
    let p = Program::from_bytes("noret.elf".into(), elf64(&code)).expect("loads");
    let a = Analysis::compute(&p);
    let main = a.function(TEXT).expect("main is found");
    assert_eq!(main.end, TEXT + 4, "main ends at its call");
    assert_eq!(main.callees, [TEXT + 0x10]);
    assert!(a.function(TEXT + 4).is_some());
}

/// A result whose `a0` the caller overwrites before calling an import is
/// not a float the import reads: the PLT entry says nothing of `fa0`.
#[test]
fn an_import_after_a_call_reads_no_float_result() {
    let p = linked_with(&[
        (0x00, 0x1141, 2),      // ASM: addi sp, sp, -16
        (0x02, 0xe406, 2),      // ASM: sd ra, 8(sp)
        (0x04, 0x02c0_00ef, 4), // ASM: jal 0x10030
        (0x08, 0x0000_1517, 4), // ASM: auipc a0, 0x1
        (0x0c, 0xff85_0513, 4), // ASM: addi a0, a0, -8
        (0x10, 0x0300_00ef, 4), // ASM: jal 0x10040
        (0x14, 0x60a2, 2),      // ASM: ld ra, 8(sp)
        (0x16, 0x0141, 2),      // ASM: addi sp, sp, 16
        (0x18, 0x8082, 2),      // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let helper = a.function(HELPER).expect("the helper is found");
    assert_eq!(helper.ret_float, None);
}
