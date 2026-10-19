//! Assembly text for one A32 or T32 instruction.

use super::{
    Addr, Block, Cond, Cvt, DpKind, FpOp, FpUn, Index, Insn, Offset, Op, Operand, PC, Reg, Shift,
    Width, cond_code,
};

/// What a listing shows for a word that decodes to no instruction.
const BAD: &str = "(bad)";

/// The suffix a condition adds to a mnemonic: empty for `al`.
///
/// # Arguments
///
/// * `c` - The condition.
fn suffix(c: Cond) -> &'static str {
    const NAMES: [&str; 16] = [
        "eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "", "",
    ];
    NAMES.get(usize::from(cond_code(c))).copied().unwrap_or("")
}

/// Names a register as assembly writes it.
///
/// # Arguments
///
/// * `r` - The register.
#[must_use]
pub fn name(r: Reg) -> String {
    match r {
        Reg::R(13) => "sp".to_owned(),
        Reg::R(14) => "lr".to_owned(),
        Reg::R(15) => "pc".to_owned(),
        Reg::R(n) => format!("r{n}"),
        Reg::S(n) => format!("s{n}"),
        Reg::D(n) => format!("d{n}"),
    }
}

/// Names a shift.
///
/// # Arguments
///
/// * `s` - The shift.
fn shift_name(s: Shift) -> &'static str {
    match s {
        Shift::Lsl => "lsl",
        Shift::Lsr => "lsr",
        Shift::Asr => "asr",
        Shift::Ror => "ror",
        Shift::Rrx => "rrx",
    }
}

/// Renders a shifted register: `r1`, `r1, lsl #2`, `r1, rrx`.
///
/// # Arguments
///
/// * `rm` - The register.
/// * `shift` - The shift.
/// * `amount` - The amount.
fn shifted(rm: Reg, shift: Shift, amount: u8) -> String {
    match (shift, amount) {
        (Shift::Lsl, 0) => name(rm),
        (Shift::Rrx, _) => format!("{}, rrx", name(rm)),
        (s, n) => format!("{}, {} #{n}", name(rm), shift_name(s)),
    }
}

/// Renders a data-processing operand.
///
/// # Arguments
///
/// * `o` - The operand.
fn operand(o: Operand) -> String {
    match o {
        Operand::Imm { value, .. } => format!("#{value:#x}"),
        Operand::Reg { rm, shift, amount } => shifted(rm, shift, amount),
        Operand::RegShift { rm, shift, rs } => {
            format!("{}, {} {}", name(rm), shift_name(shift), name(rs))
        }
    }
}

/// Renders a memory operand.
///
/// # Arguments
///
/// * `a` - The operand.
/// * `literal` - The absolute address of a literal, printed instead.
fn address(a: Addr, literal: Option<u64>) -> String {
    if let Some(at) = literal {
        return format!("[{at:#x}]");
    }
    let off = match a.offset {
        Offset::Imm(0) => String::new(),
        Offset::Imm(d) if d < 0 => format!(", #-{:#x}", d.unsigned_abs()),
        Offset::Imm(d) => format!(", #{d:#x}"),
        Offset::Reg {
            rm,
            sub,
            shift,
            amount,
        } => format!(
            ", {}{}",
            if sub { "-" } else { "" },
            shifted(rm, shift, amount)
        ),
    };
    match a.index {
        Index::Offset => format!("[{}{off}]", name(a.base)),
        Index::Pre => format!("[{}{off}]!", name(a.base)),
        Index::Post => format!("[{}]{off}", name(a.base)),
    }
}

/// Renders a register list: `{r4, r5, lr}`.
///
/// # Arguments
///
/// * `regs` - Bit `n` for `rn`.
fn list(regs: u16) -> String {
    let names: Vec<String> = (0u8..16)
        .filter(|n| regs & (1 << n) != 0)
        .map(|n| name(Reg::R(n)))
        .collect();
    format!("{{{}}}", names.join(", "))
}

/// The mnemonic of a data-processing operation.
///
/// # Arguments
///
/// * `k` - The operation.
fn dp_name(k: DpKind) -> &'static str {
    match k {
        DpKind::And => "and",
        DpKind::Eor => "eor",
        DpKind::Sub => "sub",
        DpKind::Rsb => "rsb",
        DpKind::Add => "add",
        DpKind::Adc => "adc",
        DpKind::Sbc => "sbc",
        DpKind::Rsc => "rsc",
        DpKind::Tst => "tst",
        DpKind::Teq => "teq",
        DpKind::Cmp => "cmp",
        DpKind::Cmn => "cmn",
        DpKind::Orr => "orr",
        DpKind::Mov => "mov",
        DpKind::Bic => "bic",
        DpKind::Mvn => "mvn",
        DpKind::Orn => "orn",
    }
}

/// The precision suffix of a VFP register: `.f32` or `.f64`.
///
/// # Arguments
///
/// * `r` - The register.
fn precision(r: Reg) -> &'static str {
    match r {
        Reg::D(_) => ".f64",
        Reg::R(_) | Reg::S(_) => ".f32",
    }
}

/// Renders one instruction as assembly text.
///
/// The usual syntax, with a branch target and a literal's address printed
/// as the absolute address they resolve to.
///
/// # Arguments
///
/// * `i` - The decoded instruction.
///
/// # Returns
///
/// The text; `.inst 0x........ ; neon` for an Advanced SIMD word,
/// `.inst 0x........` for a word the engine does not model, and `(bad)`
/// for one that decodes to no instruction.
#[must_use]
pub fn text(i: &Insn) -> String {
    let c = suffix(i.cond);
    let s = if i.sets { "s" } else { "" };
    let lit = i.literal();
    match i.op {
        Op::Dp { kind, rd, rn, src } => {
            if kind.compares() {
                format!("{}{c} {}, {}", dp_name(kind), name(rn), operand(src))
            } else if kind.moves() {
                match (kind, src) {
                    (DpKind::Mov, Operand::Reg { rm, shift, amount })
                        if !(shift == Shift::Lsl && amount == 0) =>
                    {
                        let by = if shift == Shift::Rrx {
                            String::new()
                        } else {
                            format!(", #{amount}")
                        };
                        format!("{}{s}{c} {}, {}{by}", shift_name(shift), name(rd), name(rm))
                    }
                    (DpKind::Mov, Operand::RegShift { rm, shift, rs }) => format!(
                        "{}{s}{c} {}, {}, {}",
                        shift_name(shift),
                        name(rd),
                        name(rm),
                        name(rs)
                    ),
                    _ => format!("{}{s}{c} {}, {}", dp_name(kind), name(rd), operand(src)),
                }
            } else {
                format!(
                    "{}{s}{c} {}, {}, {}",
                    dp_name(kind),
                    name(rd),
                    name(rn),
                    operand(src)
                )
            }
        }
        Op::Movw { rd, imm } => format!("movw{c} {}, #{imm:#x}", name(rd)),
        Op::Movt { rd, imm } => format!("movt{c} {}, #{imm:#x}", name(rd)),
        Op::Adr { rd, target } => format!("adr{c} {}, {target:#x}", name(rd)),
        Op::Mul {
            rd,
            rn,
            rm,
            acc,
            sub,
        } => match acc {
            None => format!("mul{s}{c} {}, {}, {}", name(rd), name(rn), name(rm)),
            Some(a) => format!(
                "{}{s}{c} {}, {}, {}, {}",
                if sub { "mls" } else { "mla" },
                name(rd),
                name(rn),
                name(rm),
                name(a)
            ),
        },
        Op::MulLong {
            signed,
            acc,
            lo,
            hi,
            rn,
            rm,
        } => format!(
            "{}{}{s}{c} {}, {}, {}, {}",
            if signed { "sm" } else { "um" },
            if acc { "lal" } else { "ull" },
            name(lo),
            name(hi),
            name(rn),
            name(rm)
        ),
        Op::Smmul { rd, rn, rm, acc } => match acc {
            None => format!("smmul{c} {}, {}, {}", name(rd), name(rn), name(rm)),
            Some(a) => format!(
                "smmla{c} {}, {}, {}, {}",
                name(rd),
                name(rn),
                name(rm),
                name(a)
            ),
        },
        Op::Smulxy {
            rd,
            rn,
            rm,
            n_top,
            m_top,
            acc,
        } => {
            let half = |top: bool| if top { 't' } else { 'b' };
            let m = format!(
                "{}{}{}",
                if acc.is_some() { "smla" } else { "smul" },
                half(n_top),
                half(m_top)
            );
            match acc {
                None => format!("{m}{c} {}, {}, {}", name(rd), name(rn), name(rm)),
                Some(a) => format!(
                    "{m}{c} {}, {}, {}, {}",
                    name(rd),
                    name(rn),
                    name(rm),
                    name(a)
                ),
            }
        }
        Op::Div { signed, rd, rn, rm } => format!(
            "{}div{c} {}, {}, {}",
            if signed { "s" } else { "u" },
            name(rd),
            name(rn),
            name(rm)
        ),
        Op::Clz { rd, rm } => format!("clz{c} {}, {}", name(rd), name(rm)),
        Op::Rbit { rd, rm } => format!("rbit{c} {}, {}", name(rd), name(rm)),
        Op::Rev { rd, rm } => format!("rev{c} {}, {}", name(rd), name(rm)),
        Op::Rev16 { rd, rm } => format!("rev16{c} {}, {}", name(rd), name(rm)),
        Op::Revsh { rd, rm } => format!("revsh{c} {}, {}", name(rd), name(rm)),
        Op::Bfx {
            signed,
            rd,
            rn,
            lsb,
            width,
        } => format!(
            "{}bfx{c} {}, {}, #{lsb}, #{width}",
            if signed { "s" } else { "u" },
            name(rd),
            name(rn)
        ),
        Op::Sat {
            signed,
            rd,
            rn,
            bits,
            shift,
            amount,
        } => {
            let shifted = match (shift, amount) {
                (Shift::Lsl, 0) => String::new(),
                (Shift::Lsl, n) => format!(", lsl #{n}"),
                (_, n) => format!(", asr #{n}"),
            };
            format!(
                "{}sat{c} {}, #{bits}, {}{shifted}",
                if signed { "s" } else { "u" },
                name(rd),
                name(rn)
            )
        }
        Op::Bfi { rd, rn, lsb, width } => match rn {
            Some(rn) => format!("bfi{c} {}, {}, #{lsb}, #{width}", name(rd), name(rn)),
            None => format!("bfc{c} {}, #{lsb}, #{width}", name(rd)),
        },
        Op::Extend {
            signed,
            bits,
            rd,
            rm,
            rotate,
            add,
        } => {
            let base = format!(
                "{}xt{}{}",
                if signed { "s" } else { "u" },
                if add.is_some() { "a" } else { "" },
                if bits == 8 { "b" } else { "h" }
            );
            let rot = if rotate == 0 {
                String::new()
            } else {
                format!(", ror #{rotate}")
            };
            match add {
                Some(a) => format!("{base}{c} {}, {}, {}{rot}", name(rd), name(a), name(rm)),
                None => format!("{base}{c} {}, {}{rot}", name(rd), name(rm)),
            }
        }
        Op::Load { width, rt, addr } => {
            let w = match width {
                Width::Word => "",
                Width::Byte => "b",
                Width::SByte => "sb",
                Width::Half => "h",
                Width::SHalf => "sh",
            };
            format!("ldr{w}{c} {}, {}", name(rt), address(addr, lit))
        }
        Op::Store { width, rt, addr } => {
            let w = match width {
                Width::Word | Width::SByte | Width::SHalf => "",
                Width::Byte => "b",
                Width::Half => "h",
            };
            format!("str{w}{c} {}, {}", name(rt), address(addr, lit))
        }
        Op::LoadEx { width, rt, addr } => {
            let w = match width {
                Width::Byte => "b",
                Width::Half => "h",
                Width::Word | Width::SByte | Width::SHalf => "",
            };
            format!("ldrex{w}{c} {}, {}", name(rt), address(addr, None))
        }
        Op::StoreEx {
            width,
            rd,
            rt,
            addr,
        } => {
            let w = match width {
                Width::Byte => "b",
                Width::Half => "h",
                Width::Word | Width::SByte | Width::SHalf => "",
            };
            format!(
                "strex{w}{c} {}, {}, {}",
                name(rd),
                name(rt),
                address(addr, None)
            )
        }
        Op::LoadDual { rt, rt2, addr } => format!(
            "ldrd{c} {}, {}, {}",
            name(rt),
            name(rt2),
            address(addr, lit)
        ),
        Op::StoreDual { rt, rt2, addr } => format!(
            "strd{c} {}, {}, {}",
            name(rt),
            name(rt2),
            address(addr, None)
        ),
        Op::Ldm {
            rn,
            regs,
            wback,
            block,
        } => {
            if rn == super::SP && wback && block == Block::Ia {
                format!("pop{c} {}", list(regs))
            } else {
                format!(
                    "ldm{}{c} {}{}, {}",
                    block_name(block),
                    name(rn),
                    if wback { "!" } else { "" },
                    list(regs)
                )
            }
        }
        Op::Stm {
            rn,
            regs,
            wback,
            block,
        } => {
            if rn == super::SP && wback && block == Block::Db {
                format!("push{c} {}", list(regs))
            } else {
                format!(
                    "stm{}{c} {}{}, {}",
                    block_name(block),
                    name(rn),
                    if wback { "!" } else { "" },
                    list(regs)
                )
            }
        }
        Op::B { target } => format!("b{c} {target:#x}"),
        Op::Bl { target } => format!("bl{c} {target:#x}"),
        Op::Blx { target } => format!("blx{c} {target:#x}"),
        Op::BlxReg { rm } => format!("blx{c} {}", name(rm)),
        Op::Bx { rm } => format!("bx{c} {}", name(rm)),
        Op::Cbz {
            rn,
            target,
            nonzero,
        } => format!(
            "cb{}z {}, {target:#x}",
            if nonzero { "n" } else { "" },
            name(rn)
        ),
        Op::Tb { half, rn, rm } => {
            if half {
                format!("tbh{c} [{}, {}, lsl #1]", name(rn), name(rm))
            } else {
                format!("tbb{c} [{}, {}]", name(rn), name(rm))
            }
        }
        Op::It { first, mask } => {
            let base = cond_code(first) & 1;
            let mut pattern = String::new();
            let stop = mask.trailing_zeros();
            for k in (stop + 1..4).rev() {
                pattern.push(if (mask >> k) & 1 == base { 't' } else { 'e' });
            }
            format!("it{pattern} {}", suffix(first))
        }
        Op::Svc { imm } => format!("svc{c} #{imm:#x}"),
        Op::Trap => format!("udf{c}"),
        Op::Nop => format!("nop{c}"),
        Op::Mrs { rd } => format!("mrs{c} {}, apsr", name(rd)),
        Op::Msr { rn } => format!("msr{c} apsr_nzcvq, {}", name(rn)),
        Op::VLoad { vd, addr } => format!("vldr{c} {}, {}", name(vd), address(addr, lit)),
        Op::VStore { vd, addr } => format!("vstr{c} {}, {}", name(vd), address(addr, lit)),
        Op::VLdm {
            rn,
            first,
            count,
            wback,
            db,
        } => vlist("vldm", c, rn, first, count, wback, db),
        Op::VStm {
            rn,
            first,
            count,
            wback,
            db,
        } => vlist("vstm", c, rn, first, count, wback, db),
        Op::FpBin { op, vd, vn, vm } => {
            let m = match op {
                FpOp::Add => "vadd",
                FpOp::Sub => "vsub",
                FpOp::Mul => "vmul",
                FpOp::Div => "vdiv",
                FpOp::Nmul => "vnmul",
                FpOp::Mla => "vmla",
                FpOp::Mls => "vmls",
                FpOp::Nmla => "vnmla",
                FpOp::Nmls => "vnmls",
                FpOp::Fma => "vfma",
                FpOp::Fms => "vfms",
                FpOp::Fnma => "vfnma",
                FpOp::Fnms => "vfnms",
            };
            format!(
                "{m}{c}{} {}, {}, {}",
                precision(vd),
                name(vd),
                name(vn),
                name(vm)
            )
        }
        Op::FpUn { op, vd, vm } => {
            let m = match op {
                FpUn::Mov => "vmov",
                FpUn::Abs => "vabs",
                FpUn::Neg => "vneg",
                FpUn::Sqrt => "vsqrt",
            };
            format!("{m}{c}{} {}, {}", precision(vd), name(vd), name(vm))
        }
        Op::FpImm { vd, imm8 } => {
            let bits = if matches!(vd, Reg::D(_)) { 64 } else { 32 };
            let value = crate::emulate::a64::vfp_expand(u32::from(imm8), bits).map_or_else(
                || format!("{imm8:#x}"),
                |v| {
                    if bits == 64 {
                        format!("{:?}", f64::from_bits(v))
                    } else {
                        format!("{:?}", f32::from_bits(crate::num::lo32(v)))
                    }
                },
            );
            format!("vmov{c}{} {}, #{value}", precision(vd), name(vd))
        }
        Op::FpCmp { vd, vm } => match vm {
            Some(m) => format!("vcmp{c}{} {}, {}", precision(vd), name(vd), name(m)),
            None => format!("vcmp{c}{} {}, #0", precision(vd), name(vd)),
        },
        Op::Vcvt { cvt, vd, vm } => {
            let types = match cvt {
                Cvt::SingleToDouble => ".f64.f32",
                Cvt::DoubleToSingle => ".f32.f64",
                Cvt::SignedToFloat => match vd {
                    Reg::D(_) => ".f64.s32",
                    Reg::R(_) | Reg::S(_) => ".f32.s32",
                },
                Cvt::UnsignedToFloat => match vd {
                    Reg::D(_) => ".f64.u32",
                    Reg::R(_) | Reg::S(_) => ".f32.u32",
                },
                Cvt::FloatToSigned | Cvt::FloatToSignedR => match vm {
                    Reg::D(_) => ".s32.f64",
                    Reg::R(_) | Reg::S(_) => ".s32.f32",
                },
                Cvt::FloatToUnsigned | Cvt::FloatToUnsignedR => match vm {
                    Reg::D(_) => ".u32.f64",
                    Reg::R(_) | Reg::S(_) => ".u32.f32",
                },
            };
            let r = if matches!(cvt, Cvt::FloatToSignedR | Cvt::FloatToUnsignedR) {
                "r"
            } else {
                ""
            };
            format!("vcvt{r}{c}{types} {}, {}", name(vd), name(vm))
        }
        Op::VmovCore { to_core, rt, sn } => {
            if to_core {
                format!("vmov{c} {}, {}", name(rt), name(sn))
            } else {
                format!("vmov{c} {}, {}", name(sn), name(rt))
            }
        }
        Op::VmovPair {
            to_core,
            rt,
            rt2,
            dm,
        } => {
            if to_core {
                format!("vmov{c} {}, {}, {}", name(rt), name(rt2), name(dm))
            } else {
                format!("vmov{c} {}, {}, {}", name(dm), name(rt), name(rt2))
            }
        }
        Op::Vmrs { rt } => {
            if rt == PC {
                format!("vmrs{c} apsr_nzcv, fpscr")
            } else {
                format!("vmrs{c} {}, fpscr", name(rt))
            }
        }
        Op::Vmsr { rt } => format!("vmsr{c} fpscr, {}", name(rt)),
        Op::Neon { .. } => format!(".inst {:#010x} ; neon", i.word),
        Op::Unknown => format!(".inst {:#010x}", i.word),
        Op::Invalid => BAD.to_owned(),
    }
}

/// The suffix of a block transfer's order.
///
/// # Arguments
///
/// * `b` - The order.
fn block_name(b: Block) -> &'static str {
    match b {
        Block::Ia => "ia",
        Block::Ib => "ib",
        Block::Da => "da",
        Block::Db => "db",
    }
}

/// Renders a VFP block transfer: `vpush {d8, d9}`, `vldmia r0!, {s0-s3}`.
///
/// # Arguments
///
/// * `m` - The mnemonic.
/// * `c` - The condition suffix.
/// * `rn` - The base.
/// * `first` - The first register.
/// * `count` - How many.
/// * `wback` - Whether the base is written back.
/// * `db` - Decrement before.
fn vlist(m: &str, c: &str, rn: Reg, first: Reg, count: u8, wback: bool, db: bool) -> String {
    let regs: Vec<String> = super::run(first, count).map(name).collect();
    let regs = format!("{{{}}}", regs.join(", "));
    match (m, rn == super::SP && wback, db) {
        ("vstm", true, true) => format!("vpush{c} {regs}"),
        ("vldm", true, false) => format!("vpop{c} {regs}"),
        _ => format!(
            "{m}{}{c} {}{}, {regs}",
            if db { "db" } else { "ia" },
            name(rn),
            if wback { "!" } else { "" }
        ),
    }
}
