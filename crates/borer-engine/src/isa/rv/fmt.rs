//! Assembly text for one RISC-V instruction, in GNU objdump's syntax.

use super::{
    Alu, AmoOp, BrCond, CsrOp, CsrSrc, FArith, FCmp, FOp, Fmt, Fused, Insn, IntFmt, Op, RA, Reg,
    Width, ZERO,
};

/// What a listing shows for bytes that decode to no instruction, as the
/// other listings do.
const BAD: &str = "(bad)";

/// The ABI names of the integer registers, `x0` first.
const X_NAMES: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

/// The ABI names of the float registers, `f0` first.
const F_NAMES: [&str; 32] = [
    "ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7", "fs0", "fs1", "fa0", "fa1", "fa2",
    "fa3", "fa4", "fa5", "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7", "fs8", "fs9",
    "fs10", "fs11", "ft8", "ft9", "ft10", "ft11",
];

/// The CSRs named by number; any other prints as hex.
const CSR_NAMES: [(u16, &str); 30] = [
    (0x001, "fflags"),
    (0x002, "frm"),
    (0x003, "fcsr"),
    (0x100, "sstatus"),
    (0x104, "sie"),
    (0x105, "stvec"),
    (0x140, "sscratch"),
    (0x141, "sepc"),
    (0x142, "scause"),
    (0x143, "stval"),
    (0x144, "sip"),
    (0x180, "satp"),
    (0x300, "mstatus"),
    (0x301, "misa"),
    (0x304, "mie"),
    (0x305, "mtvec"),
    (0x340, "mscratch"),
    (0x341, "mepc"),
    (0x342, "mcause"),
    (0x343, "mtval"),
    (0x344, "mip"),
    (0xc00, "cycle"),
    (0xc01, "time"),
    (0xc02, "instret"),
    (0xc80, "cycleh"),
    (0xc81, "timeh"),
    (0xc82, "instreth"),
    (0xf11, "mvendorid"),
    (0xf12, "marchid"),
    (0xf14, "mhartid"),
];

/// Returns a register's ABI name (`a0`, `sp`, `fa0`).
///
/// # Arguments
///
/// * `r` - The register.
#[must_use]
pub fn name(r: Reg) -> &'static str {
    let (table, n) = match r {
        Reg::X(n) => (&X_NAMES, n),
        Reg::F(n) => (&F_NAMES, n),
    };
    table.get(usize::from(n)).copied().unwrap_or("?")
}

/// Returns a memory operand, `off(base)`.
///
/// # Arguments
///
/// * `off` - The offset.
/// * `base` - The base register.
fn mem(off: i64, base: Reg) -> String {
    format!("{off}({})", name(base))
}

/// Returns a float format's suffix letter.
///
/// # Arguments
///
/// * `f` - The format.
fn fs(f: Fmt) -> &'static str {
    match f {
        Fmt::S => "s",
        Fmt::D => "d",
    }
}

/// Returns the operand a rounding mode field adds: nothing for dynamic.
///
/// # Arguments
///
/// * `rm` - The field.
fn rounding(rm: u8) -> String {
    match rm {
        0 => ", rne".to_owned(),
        1 => ", rtz".to_owned(),
        2 => ", rdn".to_owned(),
        3 => ", rup".to_owned(),
        4 => ", rmm".to_owned(),
        7 => String::new(),
        _ => format!(", {rm}"),
    }
}

/// Returns the operand a conversion's rounding mode adds: nothing for a
/// conversion that is always exact under the default mode `rne`, as
/// objdump prints `fcvt.d.w` and `fcvt.d.s`.
///
/// # Arguments
///
/// * `rm` - The field.
/// * `exact` - Whether every value converts exactly.
fn inexact(rm: u8, exact: bool) -> String {
    if exact && rm == 0 {
        String::new()
    } else {
        rounding(rm)
    }
}

/// Returns the suffix the `aq` and `rl` bits add to an atomic.
///
/// # Arguments
///
/// * `order` - `aq` in bit 1, `rl` in bit 0.
fn ordering(order: u8) -> &'static str {
    match order & 3 {
        3 => ".aqrl",
        2 => ".aq",
        1 => ".rl",
        _ => "",
    }
}

/// Returns a memory access width's letter in a mnemonic (`b`, `hu`, `d`).
///
/// # Arguments
///
/// * `w` - The width.
fn width(w: Width) -> &'static str {
    match w {
        Width::B => "b",
        Width::Bu => "bu",
        Width::H => "h",
        Width::Hu => "hu",
        Width::W => "w",
        Width::Wu => "wu",
        Width::D => "d",
    }
}

/// Renders one instruction as assembly text.
///
/// GNU objdump's syntax and aliases (`li a0, 5`, `ld ra, 8(sp)`, `ret`,
/// `beqz a0, 0x10230`), with `", "` between operands and a PC-relative
/// operand printed as the absolute address it resolves to. A compressed
/// instruction prints as what it expands to, as objdump does.
///
/// # Arguments
///
/// * `insn` - The decoded instruction.
///
/// # Returns
///
/// The text; `.2byte` or `.4byte` and the encoding for a word the engine
/// does not model, and `(bad)` for one that decodes to no instruction.
#[must_use]
pub fn text(insn: &Insn) -> String {
    match insn.op {
        Op::Lui { rd, imm } => format!("lui {}, {:#x}", name(rd), (imm >> 12) & 0xfffff),
        Op::Auipc { rd, .. } => format!("auipc {}, {:#x}", name(rd), insn.word >> 12),
        Op::Jal { rd, target } => match rd {
            ZERO => format!("j {target:#x}"),
            RA => format!("jal {target:#x}"),
            _ => format!("jal {}, {target:#x}", name(rd)),
        },
        Op::Jalr { rd, rs1, off } => jalr(rd, rs1, off),
        Op::Branch {
            cond,
            rs1,
            rs2,
            target,
        } => branch(cond, rs1, rs2, target),
        Op::Load {
            width: w,
            rd,
            rs1,
            off,
        } => format!("l{} {}, {}", width(w), name(rd), mem(off, rs1)),
        Op::Store {
            width: w,
            rs2,
            rs1,
            off,
        } => format!("s{} {}, {}", width(w), name(rs2), mem(off, rs1)),
        Op::Imm {
            op,
            rd,
            rs1,
            imm,
            word,
        } => imm_text(op, rd, rs1, imm, word),
        Op::Reg3 {
            op,
            rd,
            rs1,
            rs2,
            word,
        } => reg_text(op, rd, rs1, rs2, word),
        Op::Fence { pred, succ, fm } => fence(pred, succ, fm),
        Op::FenceI => "fence.i".to_owned(),
        Op::Ecall => "ecall".to_owned(),
        Op::Ebreak => "ebreak".to_owned(),
        Op::Csr { op, rd, src, csr } => csr_text(op, rd, src, csr),
        Op::Lr {
            width: w,
            rd,
            rs1,
            order,
        } => format!(
            "lr.{}{} {}, ({})",
            width(w),
            ordering(order),
            name(rd),
            name(rs1)
        ),
        Op::Sc {
            width: w,
            rd,
            rs1,
            rs2,
            order,
        } => format!(
            "sc.{}{} {}, {}, ({})",
            width(w),
            ordering(order),
            name(rd),
            name(rs2),
            name(rs1)
        ),
        Op::Amo {
            op,
            width: w,
            rd,
            rs1,
            rs2,
            order,
        } => format!(
            "amo{}.{}{} {}, {}, ({})",
            amo_name(op),
            width(w),
            ordering(order),
            name(rd),
            name(rs2),
            name(rs1)
        ),
        Op::TrapRet | Op::System => system(insn.word),
        Op::Float(op) => float_text(op),
        Op::Unknown => raw(insn),
        Op::Invalid => BAD.to_owned(),
    }
}

/// Returns the directive that spells an encoding the engine does not
/// model.
///
/// # Arguments
///
/// * `insn` - The instruction.
fn raw(insn: &Insn) -> String {
    if insn.len == 2 {
        format!(".2byte {:#x}", insn.word)
    } else {
        format!(".4byte {:#x}", insn.word)
    }
}

/// Renders a `jalr` and its aliases (`ret`, `jr`, `jalr rs`).
///
/// # Arguments
///
/// * `rd` - The link register.
/// * `rs1` - The base.
/// * `off` - The offset.
fn jalr(rd: Reg, rs1: Reg, off: i64) -> String {
    match (rd, off) {
        (ZERO, 0) if rs1 == RA => "ret".to_owned(),
        (ZERO, 0) => format!("jr {}", name(rs1)),
        (ZERO, _) => format!("jr {}", mem(off, rs1)),
        (RA, 0) => format!("jalr {}", name(rs1)),
        (RA, _) => format!("jalr {}", mem(off, rs1)),
        (_, 0) => format!("jalr {}, {}", name(rd), name(rs1)),
        _ => format!("jalr {}, {}", name(rd), mem(off, rs1)),
    }
}

/// Renders a conditional branch and its compare-with-zero aliases.
///
/// # Arguments
///
/// * `cond` - The comparison.
/// * `rs1` - The left operand.
/// * `rs2` - The right operand.
/// * `target` - Where it goes.
fn branch(cond: BrCond, rs1: Reg, rs2: Reg, target: u64) -> String {
    let mnemonic = match cond {
        BrCond::Eq => "beq",
        BrCond::Ne => "bne",
        BrCond::Lt => "blt",
        BrCond::Ge => "bge",
        BrCond::Ltu => "bltu",
        BrCond::Geu => "bgeu",
    };
    let zero_form = match (cond, rs1 == ZERO, rs2 == ZERO) {
        (BrCond::Eq, false, true) => Some(("beqz", rs1)),
        (BrCond::Ne, false, true) => Some(("bnez", rs1)),
        (BrCond::Lt, false, true) => Some(("bltz", rs1)),
        (BrCond::Ge, false, true) => Some(("bgez", rs1)),
        (BrCond::Lt, true, false) => Some(("bgtz", rs2)),
        (BrCond::Ge, true, false) => Some(("blez", rs2)),
        _ => None,
    };
    match zero_form {
        Some((m, r)) => format!("{m} {}, {target:#x}", name(r)),
        None => format!("{mnemonic} {}, {}, {target:#x}", name(rs1), name(rs2)),
    }
}

/// Returns an integer operation's mnemonic stem (`add`, `mulhu`).
///
/// # Arguments
///
/// * `op` - The operation.
fn alu_name(op: Alu) -> &'static str {
    match op {
        Alu::Add => "add",
        Alu::Sub => "sub",
        Alu::Sll => "sll",
        Alu::Slt => "slt",
        Alu::Sltu => "sltu",
        Alu::Xor => "xor",
        Alu::Srl => "srl",
        Alu::Sra => "sra",
        Alu::Or => "or",
        Alu::And => "and",
        Alu::Mul => "mul",
        Alu::Mulh => "mulh",
        Alu::Mulhsu => "mulhsu",
        Alu::Mulhu => "mulhu",
        Alu::Div => "div",
        Alu::Divu => "divu",
        Alu::Rem => "rem",
        Alu::Remu => "remu",
    }
}

/// Renders an immediate operation and its aliases (`li`, `mv`, `nop`,
/// `not`, `seqz`, `sext.w`).
///
/// # Arguments
///
/// * `op` - The operation.
/// * `rd` - The destination.
/// * `rs1` - The register operand.
/// * `imm` - The immediate.
/// * `word` - Whether it is a `w` form.
fn imm_text(op: Alu, rd: Reg, rs1: Reg, imm: i64, word: bool) -> String {
    let (d, s) = (name(rd), name(rs1));
    let w = if word { "w" } else { "" };
    match (op, word) {
        (Alu::Add, false) if rd == ZERO && rs1 == ZERO && imm == 0 => "nop".to_owned(),
        (Alu::Add, false) if rs1 == ZERO => format!("li {d}, {imm}"),
        (Alu::Add, false) if imm == 0 => format!("mv {d}, {s}"),
        (Alu::Add, true) if imm == 0 => format!("sext.w {d}, {s}"),
        (Alu::Xor, false) if imm == -1 => format!("not {d}, {s}"),
        (Alu::Sltu, false) if imm == 1 => format!("seqz {d}, {s}"),
        (Alu::Sltu, false) => format!("sltiu {d}, {s}, {imm}"),
        (Alu::Sll | Alu::Srl | Alu::Sra, _) => format!("{}i{w} {d}, {s}, {imm:#x}", alu_name(op)),
        _ => format!("{}i{w} {d}, {s}, {imm}", alu_name(op)),
    }
}

/// Renders a register operation and its aliases (`mv`, `neg`, `snez`,
/// `sltz`, `sgtz`).
///
/// # Arguments
///
/// * `op` - The operation.
/// * `rd` - The destination.
/// * `rs1` - The left operand.
/// * `rs2` - The right operand.
/// * `word` - Whether it is a `w` form.
fn reg_text(op: Alu, rd: Reg, rs1: Reg, rs2: Reg, word: bool) -> String {
    let (d, a, b) = (name(rd), name(rs1), name(rs2));
    let w = if word { "w" } else { "" };
    match op {
        Alu::Add if !word && rs1 == ZERO => format!("mv {d}, {b}"),
        Alu::Sub if rs1 == ZERO => format!("neg{w} {d}, {b}"),
        Alu::Sltu if rs1 == ZERO => format!("snez {d}, {b}"),
        Alu::Slt if rs2 == ZERO => format!("sltz {d}, {a}"),
        Alu::Slt if rs1 == ZERO => format!("sgtz {d}, {b}"),
        _ => format!("{}{w} {d}, {a}, {b}", alu_name(op)),
    }
}

/// Renders a `fence`: bare when it orders everything, `fence.tso`, or
/// with its predecessor and successor sets.
///
/// # Arguments
///
/// * `pred` - The predecessor set.
/// * `succ` - The successor set.
/// * `fm` - The fence mode.
fn fence(pred: u8, succ: u8, fm: u8) -> String {
    let set = |v: u8| -> String {
        "iorw"
            .chars()
            .zip([8u8, 4, 2, 1])
            .filter(|&(_, bit)| v & bit != 0)
            .map(|(c, _)| c)
            .collect()
    };
    match (fm, pred, succ) {
        (8, 3, 3) => "fence.tso".to_owned(),
        (_, 0xf, 0xf) => "fence".to_owned(),
        _ => format!("fence {}, {}", set(pred), set(succ)),
    }
}

/// Returns a CSR's name, or its number in hex.
///
/// # Arguments
///
/// * `csr` - The number.
fn csr_name(csr: u16) -> String {
    CSR_NAMES
        .iter()
        .find(|(n, _)| *n == csr)
        .map_or_else(|| format!("{csr:#x}"), |(_, s)| (*s).to_owned())
}

/// Renders a CSR instruction and its aliases (`csrr`, `csrw`, `csrs`,
/// `csrc` and their `i` forms).
///
/// # Arguments
///
/// * `op` - The operation.
/// * `rd` - The destination.
/// * `src` - The value or mask.
/// * `csr` - The CSR number.
fn csr_text(op: CsrOp, rd: Reg, src: CsrSrc, csr: u16) -> String {
    let c = csr_name(csr);
    let stem = match op {
        CsrOp::Rw => "w",
        CsrOp::Rs => "s",
        CsrOp::Rc => "c",
    };
    match src {
        CsrSrc::Reg(ZERO) if op == CsrOp::Rs => format!("csrr {}, {c}", name(rd)),
        CsrSrc::Reg(r) if rd == ZERO => format!("csr{stem} {c}, {}", name(r)),
        CsrSrc::Reg(r) => format!("csrr{stem} {}, {c}, {}", name(rd), name(r)),
        CsrSrc::Imm(v) if rd == ZERO => format!("csr{stem}i {c}, {v}"),
        CsrSrc::Imm(v) => format!("csrr{stem}i {}, {c}, {v}", name(rd)),
    }
}

/// Returns an atomic operation's mnemonic stem after `amo`.
///
/// # Arguments
///
/// * `op` - The operation.
fn amo_name(op: AmoOp) -> &'static str {
    match op {
        AmoOp::Swap => "swap",
        AmoOp::Add => "add",
        AmoOp::Xor => "xor",
        AmoOp::And => "and",
        AmoOp::Or => "or",
        AmoOp::Min => "min",
        AmoOp::Max => "max",
        AmoOp::Minu => "minu",
        AmoOp::Maxu => "maxu",
    }
}

/// Renders a privileged instruction the engine names but does not model.
///
/// # Arguments
///
/// * `word` - The encoding.
fn system(word: u32) -> String {
    match word {
        0x3020_0073 => "mret".to_owned(),
        0x1020_0073 => "sret".to_owned(),
        0x0020_0073 => "uret".to_owned(),
        0x1050_0073 => "wfi".to_owned(),
        w if w >> 25 == 0x09 && w & 0x7fff == 0x73 => format!(
            "sfence.vma {}, {}",
            name(super::x(w, 15)),
            name(super::x(w, 20))
        ),
        w => format!(".4byte {w:#x}"),
    }
}

/// Returns an integer format's letters in a conversion (`w`, `lu`).
///
/// # Arguments
///
/// * `i` - The format.
fn int_name(i: IntFmt) -> &'static str {
    match i {
        IntFmt::W => "w",
        IntFmt::Wu => "wu",
        IntFmt::L => "l",
        IntFmt::Lu => "lu",
    }
}

/// Returns registers' names joined by `", "`.
///
/// # Arguments
///
/// * `regs` - The registers.
fn regs(regs: &[Reg]) -> String {
    regs.iter().map(|&r| name(r)).collect::<Vec<_>>().join(", ")
}

/// Returns the letter a float format takes in a load, store or move
/// mnemonic: `w` for single, `d` for double.
///
/// # Arguments
///
/// * `f` - The format.
fn word(f: Fmt) -> &'static str {
    match f {
        Fmt::S => "w",
        Fmt::D => "d",
    }
}

/// Renders a floating-point instruction and its sign-injection aliases
/// (`fmv.d`, `fneg.d`, `fabs.d`).
///
/// # Arguments
///
/// * `op` - The operation.
fn float_text(op: FOp) -> String {
    match op {
        FOp::Load { fmt, rd, rs1, off } => {
            format!("fl{} {}, {}", word(fmt), name(rd), mem(off, rs1))
        }
        FOp::Store { fmt, rs2, rs1, off } => {
            format!("fs{} {}, {}", word(fmt), name(rs2), mem(off, rs1))
        }
        FOp::Arith {
            op,
            fmt,
            rd,
            rs1,
            rs2,
            rm,
        } => {
            let f = fs(fmt);
            let (stem, rm) = match op {
                FArith::Sgnj if rs1 == rs2 => return format!("fmv.{f} {}", regs(&[rd, rs1])),
                FArith::Sgnjn if rs1 == rs2 => return format!("fneg.{f} {}", regs(&[rd, rs1])),
                FArith::Sgnjx if rs1 == rs2 => return format!("fabs.{f} {}", regs(&[rd, rs1])),
                FArith::Add => ("fadd", rounding(rm)),
                FArith::Sub => ("fsub", rounding(rm)),
                FArith::Mul => ("fmul", rounding(rm)),
                FArith::Div => ("fdiv", rounding(rm)),
                FArith::Min => ("fmin", String::new()),
                FArith::Max => ("fmax", String::new()),
                FArith::Sgnj => ("fsgnj", String::new()),
                FArith::Sgnjn => ("fsgnjn", String::new()),
                FArith::Sgnjx => ("fsgnjx", String::new()),
            };
            format!("{stem}.{f} {}{rm}", regs(&[rd, rs1, rs2]))
        }
        FOp::Sqrt { fmt, rd, rs1, rm } => {
            format!("fsqrt.{} {}{}", fs(fmt), regs(&[rd, rs1]), rounding(rm))
        }
        FOp::Fused {
            op,
            fmt,
            rd,
            rs1,
            rs2,
            rs3,
            rm,
        } => {
            let stem = match op {
                Fused::Madd => "fmadd",
                Fused::Msub => "fmsub",
                Fused::Nmsub => "fnmsub",
                Fused::Nmadd => "fnmadd",
            };
            let operands = regs(&[rd, rs1, rs2, rs3]);
            format!("{stem}.{} {operands}{}", fs(fmt), rounding(rm))
        }
        FOp::Cmp {
            op,
            fmt,
            rd,
            rs1,
            rs2,
        } => {
            let stem = match op {
                FCmp::Eq => "feq",
                FCmp::Lt => "flt",
                FCmp::Le => "fle",
            };
            format!("{stem}.{} {}", fs(fmt), regs(&[rd, rs1, rs2]))
        }
        FOp::Class { fmt, rd, rs1 } => format!("fclass.{} {}", fs(fmt), regs(&[rd, rs1])),
        FOp::ToInt {
            fmt,
            int,
            rd,
            rs1,
            rm,
        } => cvt(int_name(int), fs(fmt), rd, rs1, &rounding(rm)),
        FOp::FromInt {
            fmt,
            int,
            rd,
            rs1,
            rm,
        } => {
            let exact = fmt == Fmt::D && matches!(int, IntFmt::W | IntFmt::Wu);
            cvt(fs(fmt), int_name(int), rd, rs1, &inexact(rm, exact))
        }
        FOp::Convert {
            from,
            to,
            rd,
            rs1,
            rm,
        } => cvt(fs(to), fs(from), rd, rs1, &inexact(rm, to == Fmt::D)),
        FOp::MvToInt { fmt, rd, rs1 } => format!("fmv.x.{} {}", word(fmt), regs(&[rd, rs1])),
        FOp::MvFromInt { fmt, rd, rs1 } => format!("fmv.{}.x {}", word(fmt), regs(&[rd, rs1])),
    }
}

/// Renders an `fcvt`.
///
/// # Arguments
///
/// * `to` - The format written, as the mnemonic spells it.
/// * `from` - The format read.
/// * `rd` - The destination.
/// * `rs1` - The operand.
/// * `rm` - The rounding operand, or nothing.
fn cvt(to: &str, from: &str, rd: Reg, rs1: Reg, rm: &str) -> String {
    format!("fcvt.{to}.{from} {}{rm}", regs(&[rd, rs1]))
}
