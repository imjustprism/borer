//! The jump tables a RISC-V `jr` dispatches through.
//!
//! RISC-V has no indexed load, so a switch builds the entry's address:
//! clang at `-O2` writes `li a1, 11; bltu a1, a0, default; slli a0, a0, 2;
//! lui a1, %hi(table); addi a1, a1, %lo(table); add a0, a0, a1; lw a0,
//! 0(a0); jr a0`, a position-independent build forms the table with
//! `auipc` and adds the entry to a base, and at `-O0` the index is spilled
//! to a frame slot across its check. [`resolve`] replays the straight-line
//! code that falls through to the `jr`, oldest first, each register holding
//! a [`Sym`]: what it can say of the value, and the value number a check
//! bounds. The table is the one the jump's register was loaded from, with
//! as many entries as the check before the load admits; a table whose
//! entries mostly land outside the code is no table ([`accept_table`]).

use std::collections::BTreeMap;

use super::dest;
use crate::analysis::functions::tables::{TABLE_ENTRIES_MAX, accept_table};
use crate::isa::rv::{Alu, BrCond, FOp, Flow, Insn, Op, Reg, SP, Width, Xlen, ZERO};
use crate::num::sext32;
use crate::program::Program;

/// Most instructions replayed back from a `jr`: the check, the reload,
/// the shift, the table's address, the add, the load and the compiler's
/// spills between them.
const LOOK_BACK: usize = 32;
/// The frame pointer, `s0`.
const FP: Reg = Reg::X(8);

/// What the replay knows of a register's value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sym {
    /// A constant.
    Const(u64),
    /// A value nothing explains, by number: equal numbers are equal values.
    Val(u32),
    /// A value shifted left by `shift` bits.
    Scaled {
        /// The value's number.
        value: u32,
        /// The shift, in bits.
        shift: i64,
    },
    /// A table's address plus a scaled value.
    Slot {
        /// The table's address.
        table: u64,
        /// The value's number.
        value: u32,
        /// The shift, in bits.
        shift: i64,
    },
    /// The entry a scaled value selects, read from a table, plus a base
    /// when the entries are offsets from one.
    Entry {
        /// The table's address.
        table: u64,
        /// The value's number.
        value: u32,
        /// The shift, in bits.
        shift: i64,
        /// How each entry is read.
        width: Width,
        /// The address the entry is added to, when one is.
        base: Option<u64>,
    },
}

/// A jump table resolved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Table {
    /// Where its entries start.
    pub(super) at: u64,
    /// The case targets, in table order.
    pub(super) targets: Vec<u64>,
}

/// The replay's state: each register's symbol, the frame slots' and the
/// value the last check bounds.
struct Replay {
    /// The registers written so far; any other holds its own unknown value.
    regs: BTreeMap<Reg, Sym>,
    /// Frame slots by base, offset and bytes, with what was stored there.
    slots: Vec<((Reg, i64, u8), Sym)>,
    /// The next fresh value number.
    fresh: u32,
    /// The value a check bounds and how many entries it admits.
    bound: Option<(u32, u64)>,
    /// The register width.
    xlen: Xlen,
}

impl Replay {
    /// Returns what a register holds.
    fn read(&self, r: Reg) -> Sym {
        match (r, self.regs.get(&r)) {
            (ZERO, _) => Sym::Const(0),
            (_, Some(s)) => *s,
            (Reg::X(n), None) => Sym::Val(u32::from(n)),
            (Reg::F(n), None) => Sym::Val(32 + u32::from(n)),
        }
    }

    /// Returns a value no other register holds.
    fn fresh(&mut self) -> Sym {
        self.fresh += 1;
        Sym::Val(self.fresh)
    }

    /// Replays one instruction; `taken` when the path leaves a branch by
    /// its target.
    fn step(&mut self, i: &Insn, taken: bool) {
        let sym = if let Op::Lui { imm, .. } = i.op {
            Some(Sym::Const(self.xlen.addr(imm.cast_unsigned())))
        } else if let Op::Auipc { target, .. } = i.op {
            Some(Sym::Const(target))
        } else if let Op::Imm {
            op, rs1, imm, word, ..
        } = i.op
        {
            Some(self.imm(op, rs1, imm, word))
        } else if let Op::Reg3 {
            op: Alu::Add,
            rs1,
            rs2,
            word: false,
            ..
        } = i.op
        {
            Some(self.add(rs1, rs2))
        } else if let Op::Load {
            width, rs1, off, ..
        } = i.op
        {
            Some(self.load(width, rs1, off))
        } else {
            None
        };
        if let Op::Store {
            width,
            rs2,
            rs1,
            off,
        } = i.op
        {
            self.store(width, rs2, rs1, off);
        } else if let Op::Branch { cond, rs1, rs2, .. } = i.op {
            self.check(cond, rs1, rs2, taken);
        } else if matches!(
            i.op,
            Op::Amo { .. } | Op::Sc { .. } | Op::Float(FOp::Store { .. })
        ) {
            self.slots.clear();
        } else if i.op == Op::Ecall {
            self.slots.clear();
            for n in 10..18 {
                let v = self.fresh();
                self.regs.insert(Reg::X(n), v);
            }
        }
        if let Some(rd) = dest(i.op) {
            if matches!(rd, SP | FP) {
                self.slots.clear();
            }
            let s = match sym {
                Some(s) => s,
                None => self.fresh(),
            };
            if rd != ZERO {
                self.regs.insert(rd, s);
            }
        }
    }

    /// What an operation with an immediate leaves: a constant folds, a
    /// copy (`addi rd, rs, 0`) keeps its value, a shift scales it.
    fn imm(&mut self, op: Alu, rs1: Reg, imm: i64, word: bool) -> Sym {
        let w = |v: u64| if word { sext32(v) } else { v };
        match (op, self.read(rs1)) {
            (Alu::Add, Sym::Const(c)) => Sym::Const(self.xlen.addr(w(c.wrapping_add_signed(imm)))),
            (Alu::Add, s) if imm == 0 && !word => s,
            (Alu::Sll, Sym::Const(c)) if (0..64).contains(&imm) && !word => {
                Sym::Const(self.xlen.addr(c << imm))
            }
            (Alu::Sll, Sym::Val(value)) if (0..64).contains(&imm) && !word => {
                Sym::Scaled { value, shift: imm }
            }
            _ => self.fresh(),
        }
    }

    /// What an `add` leaves: a table plus a scaled index, an entry plus a
    /// base, or two constants.
    fn add(&mut self, rs1: Reg, rs2: Reg) -> Sym {
        let (a, b) = (self.read(rs1), self.read(rs2));
        match (a, b) {
            (Sym::Const(x), Sym::Const(y)) => Sym::Const(self.xlen.addr(x.wrapping_add(y))),
            (Sym::Const(table), Sym::Scaled { value, shift })
            | (Sym::Scaled { value, shift }, Sym::Const(table)) => Sym::Slot {
                table,
                value,
                shift,
            },
            (
                Sym::Entry {
                    table,
                    value,
                    shift,
                    width,
                    base: None,
                },
                Sym::Const(base),
            )
            | (
                Sym::Const(base),
                Sym::Entry {
                    table,
                    value,
                    shift,
                    width,
                    base: None,
                },
            ) => Sym::Entry {
                table,
                value,
                shift,
                width,
                base: Some(base),
            },
            _ => self.fresh(),
        }
    }

    /// What a load leaves: a frame slot's value, or the entry a table's
    /// scaled index selects.
    fn load(&mut self, width: Width, rs1: Reg, off: i64) -> Sym {
        if matches!(rs1, SP | FP) {
            let key = (rs1, off, width.bytes());
            return match self.slots.iter().find(|(k, _)| *k == key) {
                Some((_, s)) if width == full(self.xlen) => *s,
                _ => self.fresh(),
            };
        }
        match self.read(rs1) {
            Sym::Slot {
                table,
                value,
                shift,
            } => Sym::Entry {
                table: self.xlen.addr(table.wrapping_add_signed(off)),
                value,
                shift,
                width,
                base: None,
            },
            _ => self.fresh(),
        }
    }

    /// Records a store: a frame slot takes the value, and any slot it
    /// overlaps, or every slot for a store elsewhere, is forgotten.
    fn store(&mut self, width: Width, rs2: Reg, rs1: Reg, off: i64) {
        if !matches!(rs1, SP | FP) {
            self.slots.clear();
            return;
        }
        let end = off.saturating_add(i64::from(width.bytes()));
        self.slots.retain(|((b, d, n), _)| {
            *b == rs1 && (d.saturating_add(i64::from(*n)) <= off || *d >= end)
        });
        let v = self.read(rs2);
        self.slots.push(((rs1, off, width.bytes()), v));
    }

    /// Reads a branch on the path as a bound: `bltu c, x` falls through
    /// and `bgeu c, x` is taken when `x <= c`; `bgeu x, c` falls through
    /// and `bltu x, c` is taken when `x < c`.
    fn check(&mut self, cond: BrCond, rs1: Reg, rs2: Reg, taken: bool) {
        let bound = match (cond, taken, self.read(rs1), self.read(rs2)) {
            (BrCond::Ltu, false, Sym::Const(c), Sym::Val(v))
            | (BrCond::Geu, true, Sym::Const(c), Sym::Val(v)) => c.checked_add(1).map(|n| (v, n)),
            (BrCond::Geu, false, Sym::Val(v), Sym::Const(c))
            | (BrCond::Ltu, true, Sym::Val(v), Sym::Const(c)) => Some((v, c)),
            _ => None,
        };
        if bound.is_some() {
            self.bound = bound;
        }
    }
}

/// How many ways the walk enters an instruction: the branches and jumps
/// that target it, and the one before it when that runs on into it.
///
/// A path two ways enter is a join, where a check one of them made no
/// longer bounds the index the other brings.
///
/// # Arguments
///
/// * `seen` - The walk's instructions by address.
/// * `sources` - The branches and jumps of the walk targeting each address.
/// * `i` - The instruction.
fn entered(seen: &BTreeMap<u64, Insn>, sources: &BTreeMap<u64, Vec<u64>>, i: &Insn) -> usize {
    let falls = seen.range(..i.va).next_back().is_some_and(|(_, p)| {
        p.next() == i.va && matches!(p.flow(), Flow::Next | Flow::CondJump | Flow::Call)
    });
    sources.get(&i.va).map_or(0, Vec::len) + usize::from(falls)
}

/// The access that moves a whole register: `ld` on RV64, `lw` on RV32.
fn full(xlen: Xlen) -> Width {
    match xlen {
        Xlen::X64 => Width::D,
        Xlen::X32 => Width::W,
    }
}

/// The path to `at`, nearest first, each with whether the path leaves it
/// by its target.
///
/// The path falls back through the instructions that fall through to it,
/// and where none does (`bgeu c, x, dispatch; j default`), through the one
/// conditional branch that targets it.
///
/// # Arguments
///
/// * `seen` - The walk's instructions by address.
/// * `sources` - The branches and jumps of the walk targeting each address.
/// * `at` - The `jr`.
fn before<'a>(
    seen: &'a BTreeMap<u64, Insn>,
    sources: &BTreeMap<u64, Vec<u64>>,
    at: u64,
) -> Vec<(&'a Insn, bool)> {
    let mut out = Vec::new();
    let mut cur = at;
    while out.len() < LOOK_BACK {
        let falls = seen
            .range(..cur)
            .next_back()
            .map(|(_, p)| p)
            .filter(|p| p.next() == cur && matches!(p.flow(), Flow::Next | Flow::CondJump));
        let step = match falls {
            Some(p) => (p, false),
            None => {
                let mut into = sources
                    .get(&cur)
                    .into_iter()
                    .flatten()
                    .filter_map(|va| seen.get(va))
                    .filter(|i| i.flow() == Flow::CondJump);
                match (into.next(), into.next()) {
                    (Some(b), None) => (b, true),
                    _ => break,
                }
            }
        };
        out.push(step);
        cur = step.0.va;
    }
    out
}

/// Resolves the jump table a `jr` dispatches through.
///
/// # Arguments
///
/// * `program` - The image.
/// * `seen` - The walk's instructions by address.
/// * `sources` - The branches and jumps of the walk targeting each address.
/// * `jr` - The indirect jump.
/// * `xlen` - The register width.
///
/// # Returns
///
/// The table, or `None` when the jump reads no bounded entry of one.
pub(super) fn resolve(
    program: &Program,
    seen: &BTreeMap<u64, Insn>,
    sources: &BTreeMap<u64, Vec<u64>>,
    jr: &Insn,
    xlen: Xlen,
) -> Option<Table> {
    let Op::Jalr {
        rd: ZERO,
        rs1,
        off: 0,
    } = jr.op
    else {
        return None;
    };
    let mut r = Replay {
        regs: BTreeMap::new(),
        slots: Vec::new(),
        fresh: 64,
        bound: None,
        xlen,
    };
    let path = before(seen, sources, jr.va);
    for (i, taken) in path.iter().rev().copied().chain([(jr, false)]) {
        if entered(seen, sources, i) > 1 {
            r.regs.clear();
            r.slots.clear();
            r.bound = None;
        }
        if i.va != jr.va {
            r.step(i, taken);
        }
    }
    let Sym::Entry {
        table,
        value,
        shift,
        width,
        base,
    } = r.read(rs1)
    else {
        return None;
    };
    let (bounded, entries) = r.bound.filter(|(_, n)| *n <= TABLE_ENTRIES_MAX)?;
    let size = width.bytes();
    let fits = matches!(
        (width, xlen),
        (Width::W | Width::Wu, _) | (Width::D, Xlen::X64)
    );
    if bounded != value || !fits || 1u64 << shift.clamp(0, 63) != u64::from(size) {
        return None;
    }
    let targets = (0..entries)
        .map(|k| {
            let slot = table.checked_add(k.checked_mul(u64::from(size))?)?;
            let bytes = program.read_va_upto(slot, usize::from(size))?;
            if bytes.len() != usize::from(size) {
                return None;
            }
            let raw = bytes
                .iter()
                .rev()
                .fold(0u64, |acc, b| (acc << 8) | u64::from(*b));
            let e = if width == Width::W { sext32(raw) } else { raw };
            Some(xlen.addr(base.map_or(e, |b| b.wrapping_add(e))) & !1)
        })
        .collect::<Option<Vec<u64>>>()?;
    accept_table(program, &targets).then_some(Table { at: table, targets })
}
