//! The jump tables an arm64 `br` dispatches through.
//!
//! A switch compiled for arm64 bounds its index, loads an entry from a
//! table the index selects and jumps to a base plus the entry: clang
//! writes `cmp w9, #0x4c; b.hi default; adr x12, base; ldrb w13, [x23,
//! x9]; add x12, x12, x13, lsl #2; br x12` (or `ldrh`, or `ldrsw` with the
//! table as its own base), GCC `ldrb w1, [x1, w0, uxtw]; adr x2, base; add
//! x1, x2, w1, sxtb #2`, and MSVC keeps the table inline in `.text`,
//! `adr x9, table; ldrsw x8, [x9, w10, uxtw #2]; adr x9, base; add x8, x9,
//! x8, lsl #2`. [`shape`] reads the bound, the load and the add from the
//! words that fall through to the `br`, at most [`SLICE_MAX`] of them, and
//! [`resolve`] takes the table's and the base's addresses from the
//! constants the function's registers hold there ([`Tracker`]), which
//! finds them however far back the compiler hoisted them. A table whose
//! entries mostly land outside the code is no table
//! ([`accept_table`]).

use super::discover::{Text, falls_through};
use super::refs::{Tracker, Val, any_reg, gpr, mem, writes, x_reg};
use crate::analysis::functions::tables::{TABLE_ENTRIES_MAX, accept_table};
use crate::isa::a64::{self, Cond, Insn, Mnemonic, Op, Opnd, Shift, Width};
use crate::num::{from_usize, lo8, lo16, lo32, sext32};
use crate::program::Program;

/// Most instructions read back from a `br` for its dispatch.
///
/// The bound, the branch to the default case, the table's address, the
/// load, the base and the add fit, with the compiler's other work
/// scheduled between them.
const SLICE_MAX: usize = 32;

/// A jump table resolved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Table {
    /// The `br` that dispatches through it.
    pub(super) site: u64,
    /// Where its entries start.
    pub(super) at: u64,
    /// The bytes its entries take.
    pub(super) len: u64,
    /// The case targets, in table order, each an instruction in the code.
    pub(super) targets: Vec<u64>,
}

/// How a `br` dispatches, as far as the words before it tell; the
/// addresses come from the constants the registers hold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Shape {
    /// The `br`.
    site: u64,
    /// The load of the entry.
    load: u64,
    /// The register holding the table's address at the load.
    table: usize,
    /// The bytes one entry takes: 1, 2, 4 or 8.
    size: u64,
    /// The entry is sign-extended to 64 bits as loaded.
    signed: bool,
    /// How many entries the bound allows.
    entries: u64,
    /// The `add` of the entry to a base: its address, the base's register,
    /// how it extends the entry and how far it shifts it. `None` when the
    /// entry is the target itself.
    add: Option<(u64, usize, Shift, u8)>,
}

/// Reads the dispatch of a `br` from the words that fall through to it.
///
/// The `br`'s register must come from an `add` of a loaded entry to a
/// base register (or from a 64-bit load, an entry that is the target);
/// the entry from a load indexed by a register; and that index must be
/// bounded by `cmp` with an immediate and `b.hi` or `b.hs` before the
/// load, nothing between them changing it but a copy.
///
/// # Arguments
///
/// * `text` - The code.
/// * `br` - The `br`.
///
/// # Returns
///
/// The shape, or `None` when the words read as no bounded table.
pub(super) fn shape(text: &Text<'_>, br: &Insn) -> Option<Shape> {
    let target = x_reg(&br.operands[0])?;
    let mut slice: Vec<Insn> = Vec::with_capacity(SLICE_MAX);
    let mut va = br.va;
    while slice.len() < SLICE_MAX {
        let Some(prev) = va.checked_sub(4) else {
            break;
        };
        let Some(insn) = text.word(prev).map(|w| a64::decode(w, prev)) else {
            break;
        };
        if !falls_through(&insn) {
            break;
        }
        slice.push(insn);
        va = prev;
    }
    let def = |from: usize, reg: usize| {
        slice
            .iter()
            .enumerate()
            .skip(from)
            .find(|(_, i)| writes(i) & (1u32 << reg) != 0)
    };
    let (k, last) = def(0, target)?;
    if last.op != Op::Other {
        return None;
    }
    let (j, load, add) = if last.mnemonic == Mnemonic::Add {
        let base = x_reg(&last.operands[1])?;
        let (reg, shift, amount) = match last.operands[2] {
            Opnd::Shifted {
                reg, shift, amount, ..
            } => (gpr(reg)?, shift, amount),
            Opnd::Reg { reg, bits: 64 } => (gpr(reg)?, Shift::Lsl, 0),
            Opnd::None
            | Opnd::Reg { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => return None,
        };
        let (j, load) = def(k + 1, reg)?;
        (j, load, Some((last.va, base, shift, amount)))
    } else {
        (k, last, None)
    };
    let m = mem(load).filter(|m| m.disp == 0)?;
    let (index, _) = m.index?;
    let Mnemonic::Ldr(width) = load.mnemonic else {
        return None;
    };
    let bits = match load.operands[0] {
        Opnd::Reg { bits, .. } => bits,
        Opnd::None
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => return None,
    };
    let (size, signed) = match width {
        Width::Byte => (1, false),
        Width::SByte => (1, true),
        Width::Half => (2, false),
        Width::SHalf => (2, true),
        Width::SWord => (4, true),
        Width::Reg if bits == 32 => (4, false),
        Width::Reg if bits == 64 => (8, false),
        Width::Reg => return None,
    };
    if add.is_none() && size != 8 {
        return None;
    }
    let entries = bound(slice.get(j + 1..)?, gpr(index)?)?;
    Some(Shape {
        site: br.va,
        load: load.va,
        table: gpr(m.base)?,
        size,
        signed,
        entries,
        add,
    })
}

/// Reads how many entries the check before a table's load allows.
///
/// The instructions are replayed oldest first, each register holding a
/// value number: a copy (or a zero- or sign-extension from bit 0) gives its
/// destination the source's number, any other write a fresh one. A `cmp`
/// of a register with an immediate followed by `b.hi` or `b.hs` bounds the
/// value the register held, and the table's index is bounded when it
/// still holds that value at the load, whichever register it went through.
///
/// # Arguments
///
/// * `older` - The instructions before the load, nearest first.
/// * `index` - The register indexing the table at the load.
///
/// # Returns
///
/// `N + 1` for `cmp r, #N; b.hi`, `N` for `b.hs`, or `None` when no check
/// bounds the value the index holds at the load.
fn bound(older: &[Insn], index: usize) -> Option<u64> {
    let mut held: [u64; 31] = std::array::from_fn(from_usize);
    let mut fresh = from_usize(held.len());
    let mut compared: Option<(u64, u64)> = None;
    let mut bounded: Option<(u64, u64)> = None;
    for insn in older.iter().rev() {
        if let Op::BCond(c) = insn.op {
            if let Some((value, n)) = compared.take() {
                bounded = match c {
                    Cond::Hi => n.checked_add(1).map(|e| (value, e)),
                    Cond::Hs => Some((value, n)),
                    Cond::Eq
                    | Cond::Ne
                    | Cond::Lo
                    | Cond::Mi
                    | Cond::Pl
                    | Cond::Vs
                    | Cond::Vc
                    | Cond::Ls
                    | Cond::Ge
                    | Cond::Lt
                    | Cond::Gt
                    | Cond::Le
                    | Cond::Al
                    | Cond::Nv => bounded,
                };
            }
            continue;
        }
        if insn.op == Op::Other
            && insn.mnemonic == Mnemonic::Subs
            && matches!(
                insn.operands[0],
                Opnd::Reg {
                    reg: a64::Reg::Zr,
                    ..
                }
            )
            && let (Some(r), Opnd::Imm(n)) = (any_reg(&insn.operands[1]), insn.operands[2])
        {
            compared = held.get(r).map(|&v| (v, n));
            continue;
        }
        let copy = copied_from(insn).and_then(|r| held.get(r).copied());
        let mask = writes(insn);
        for (r, v) in held.iter_mut().enumerate() {
            if mask & (1u32 << r) != 0 {
                *v = copy.unwrap_or_else(|| {
                    fresh += 1;
                    fresh
                });
            }
        }
    }
    let (value, entries) = bounded?;
    (held.get(index) == Some(&value)).then_some(entries)
}

/// Returns the register an instruction copies or zero- or sign-extends
/// from its low bits into its destination: `mov`, `uxtw`, `sxtw`,
/// `ubfx` and `sbfx` from bit 0.
///
/// # Arguments
///
/// * `insn` - The instruction.
fn copied_from(insn: &Insn) -> Option<usize> {
    match insn.mnemonic {
        Mnemonic::Orr
            if matches!(
                insn.operands[1],
                Opnd::Reg {
                    reg: a64::Reg::Zr,
                    ..
                }
            ) =>
        {
            any_reg(&insn.operands[2])
        }
        Mnemonic::Ubfm | Mnemonic::Sbfm if insn.operands[2] == Opnd::Imm(0) => {
            any_reg(&insn.operands[1])
        }
        Mnemonic::Movz
        | Mnemonic::Movn
        | Mnemonic::Movk
        | Mnemonic::Add
        | Mnemonic::Adds
        | Mnemonic::Sub
        | Mnemonic::Subs
        | Mnemonic::Adc
        | Mnemonic::Adcs
        | Mnemonic::Sbc
        | Mnemonic::Sbcs
        | Mnemonic::And
        | Mnemonic::Ands
        | Mnemonic::Orr
        | Mnemonic::Orn
        | Mnemonic::Eor
        | Mnemonic::Eon
        | Mnemonic::Bic
        | Mnemonic::Bics
        | Mnemonic::Ubfm
        | Mnemonic::Sbfm
        | Mnemonic::Bfm
        | Mnemonic::Extr
        | Mnemonic::Lslv
        | Mnemonic::Lsrv
        | Mnemonic::Asrv
        | Mnemonic::Rorv
        | Mnemonic::Madd
        | Mnemonic::Msub
        | Mnemonic::Smaddl
        | Mnemonic::Smsubl
        | Mnemonic::Umaddl
        | Mnemonic::Umsubl
        | Mnemonic::Smulh
        | Mnemonic::Umulh
        | Mnemonic::Udiv
        | Mnemonic::Sdiv
        | Mnemonic::Clz
        | Mnemonic::Cls
        | Mnemonic::Rbit
        | Mnemonic::Rev
        | Mnemonic::Rev16
        | Mnemonic::Rev32
        | Mnemonic::Csel
        | Mnemonic::Csinc
        | Mnemonic::Csinv
        | Mnemonic::Csneg
        | Mnemonic::Ccmp
        | Mnemonic::Ccmn
        | Mnemonic::Ldr(_)
        | Mnemonic::Str(_)
        | Mnemonic::Ldp(_)
        | Mnemonic::Stp
        | Mnemonic::Stxr(_)
        | Mnemonic::Stxp
        | Mnemonic::Atomic(..)
        | Mnemonic::Cas(_)
        | Mnemonic::Prfm
        | Mnemonic::Fmov
        | Mnemonic::Fadd
        | Mnemonic::Fsub
        | Mnemonic::Fmul
        | Mnemonic::Fdiv
        | Mnemonic::Fmadd
        | Mnemonic::Fmsub
        | Mnemonic::Fnmadd
        | Mnemonic::Fnmsub
        | Mnemonic::Fsqrt
        | Mnemonic::Fabs
        | Mnemonic::Fneg
        | Mnemonic::Fmax
        | Mnemonic::Fmin
        | Mnemonic::Fcmp
        | Mnemonic::Fcmpe
        | Mnemonic::Fccmp
        | Mnemonic::Fcsel
        | Mnemonic::Scvtf
        | Mnemonic::Ucvtf
        | Mnemonic::Fcvtzs
        | Mnemonic::Fcvtzu
        | Mnemonic::Fcvt
        | Mnemonic::Dup
        | Mnemonic::Mul
        | Mnemonic::Neg
        | Mnemonic::Abs
        | Mnemonic::Movi
        | Mnemonic::Mvni
        | Mnemonic::Svc
        | Mnemonic::Mrs
        | Mnemonic::Msr
        | Mnemonic::Barrier
        | Mnemonic::Ld1
        | Mnemonic::St1
        | Mnemonic::Simd(_)
        | Mnemonic::Other => None,
    }
}

/// Resolves a dispatch's table: its address and the base from the
/// constants the registers hold, its entries read and turned into case
/// targets.
///
/// # Arguments
///
/// * `program` - The loaded image, for the table's bytes.
/// * `text` - The code: a target that is no instruction in it (unaligned,
///   outside it, a zero word or one that does not decode) is dropped.
/// * `tracker` - The constants the walked function's registers hold.
/// * `s` - The dispatch.
///
/// # Returns
///
/// The table, or `None` when the table's address or the base is not a
/// known address, the bound allows more than [`TABLE_ENTRIES_MAX`]
/// entries, the image does not hold them, or too many of them land
/// outside the code ([`accept_table`]).
pub(super) fn resolve(
    program: &Program,
    text: &Text<'_>,
    tracker: &Tracker<'_>,
    s: &Shape,
) -> Option<Table> {
    let addr = |va: u64, reg: usize| match tracker.before(va)?.get(reg).copied().flatten()? {
        Val::Addr(a) => Some(a),
        Val::Loaded(_) => None,
    };
    let at = addr(s.load, s.table)?;
    if s.entries == 0 || s.entries > TABLE_ENTRIES_MAX {
        return None;
    }
    let len = s.entries.checked_mul(s.size)?;
    let bytes = program.read_va(at, usize::try_from(len).ok()?)?;
    let base = match s.add {
        Some((va, reg, ..)) => Some(addr(va, reg)?),
        None => None,
    };
    let targets: Vec<u64> = bytes
        .chunks_exact(usize::try_from(s.size).ok()?)
        .map(|c| {
            let raw = c.iter().rev().fold(0u64, |v, &b| (v << 8) | u64::from(b));
            let entry = match (s.size, s.signed) {
                (1, true) => sext8(raw),
                (2, true) => sext16(raw),
                (4, true) => sext32(raw),
                _ => raw,
            };
            match (s.add, base) {
                (Some((_, _, shift, amount)), Some(base)) => extend(entry, shift)
                    .and_then(|e| e.checked_shl(u32::from(amount)))
                    .map(|e| base.wrapping_add(e)),
                (Some(_), None) | (None, Some(_)) => None,
                (None, None) => Some(entry),
            }
        })
        .collect::<Option<Vec<u64>>>()?;
    if !accept_table(program, &targets) {
        return None;
    }
    let targets: Vec<u64> = targets
        .into_iter()
        .filter(|&t| {
            text.word(t)
                .is_some_and(|w| w != 0 && a64::decode(w, t).op != Op::Invalid)
        })
        .collect();
    (!targets.is_empty()).then_some(Table {
        site: s.site,
        at,
        len: from_usize(bytes.len()),
        targets,
    })
}

/// Sign-extends the low byte of a value.
///
/// # Arguments
///
/// * `v` - The value.
fn sext8(v: u64) -> u64 {
    i64::from(lo8(v).cast_signed()).cast_unsigned()
}

/// Sign-extends the low halfword of a value.
///
/// # Arguments
///
/// * `v` - The value.
fn sext16(v: u64) -> u64 {
    i64::from(lo16(v).cast_signed()).cast_unsigned()
}

/// Extends a loaded entry the way the `add` reads it.
///
/// # Arguments
///
/// * `v` - The entry as loaded.
/// * `shift` - How the `add` reads its register.
///
/// # Returns
///
/// The extended entry, or `None` for a shift no table dispatch uses.
fn extend(v: u64, shift: Shift) -> Option<u64> {
    match shift {
        Shift::Lsl | Shift::Uxtx | Shift::Sxtx => Some(v),
        Shift::Uxtb => Some(u64::from(lo8(v))),
        Shift::Uxth => Some(u64::from(lo16(v))),
        Shift::Uxtw => Some(u64::from(lo32(v))),
        Shift::Sxtb => Some(sext8(v)),
        Shift::Sxth => Some(sext16(v)),
        Shift::Sxtw => Some(sext32(v)),
        Shift::Lsr | Shift::Asr | Shift::Ror => None,
    }
}
