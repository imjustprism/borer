//! The stubs an arm64 linker writes to reach an import, and the calls
//! through an import's slot that need none.
//!
//! Every stub loads the import's address from its slot and jumps there.
//! A Mach-O `__stubs` entry and a PE import thunk are `adrp x16, page;
//! ldr x16, [x16, #off]; br x16`; an ELF PLT entry also hands the slot's
//! address to the lazy binder, `adrp x16, page; ldr x17, [x16, #off];
//! add x16, x16, #off; br x17`, sometimes landed with `bti c` and with
//! `autia1716` before the jump; a Mach-O `__auth_stubs` entry forms the
//! slot's address first and authenticates the jump with it, `adrp x17,
//! page; add x17, x17, #off; ldr x16, [x17]; braa x16, x17`. [`slot`]
//! reads any of them; [`name`] names a function that is one after the
//! import its slot holds and records the slot as its thunk. Code that
//! calls an import without a stub loads the slot itself, `adrp x8, page;
//! ldr x8, [x8, #off]; blr x8`, which [`slot_call`] reads back from the
//! call.

use std::collections::BTreeMap;

use super::discover::{Text, falls_through};
use super::refs::{gpr, mem, writes, x_reg};
use crate::analysis::{Function, NameSource};
use crate::isa::a64::{self, Insn, Mnemonic, Mode, Op, Opnd, Width};
use crate::program::{Program, SymbolKind};

/// Most instructions a stub holds: a landing pad, the four of an ELF PLT
/// entry and an authentication.
const STUB_INSNS_MAX: usize = 6;
/// Most instructions [`slot_call`] reads back from a call for the load of
/// its register: the arguments a compiler sets between the load and the
/// call fit.
const SLICE_MAX: usize = 8;

/// Reads a 64-bit load at a constant offset from a register.
///
/// # Arguments
///
/// * `insn` - The instruction.
///
/// # Returns
///
/// The loaded register, the base register and the offset, or `None` when
/// the instruction is no such load.
fn load(insn: &Insn) -> Option<(usize, usize, i64)> {
    if insn.op != Op::Other || insn.mnemonic != Mnemonic::Ldr(Width::Reg) {
        return None;
    }
    let m = mem(insn).filter(|m| m.index.is_none() && m.mode == Mode::Offset)?;
    Some((x_reg(&insn.operands[0])?, gpr(m.base)?, m.disp))
}

/// Reads an `adrp`.
///
/// # Arguments
///
/// * `insn` - The instruction.
///
/// # Returns
///
/// The register it sets and the page, or `None` for any other instruction.
fn adrp(insn: &Insn) -> Option<(usize, u64)> {
    let (Op::Adrp, Opnd::PcRel(page)) = (insn.op, insn.operands[1]) else {
        return None;
    };
    Some((x_reg(&insn.operands[0])?, page))
}

/// Reads an `add` of an immediate to a 64-bit register.
///
/// # Arguments
///
/// * `insn` - The instruction.
///
/// # Returns
///
/// The register written, the register read and the immediate, or `None`
/// for any other instruction.
fn add_imm(insn: &Insn) -> Option<(usize, usize, u64)> {
    if insn.op != Op::Other || insn.mnemonic != Mnemonic::Add {
        return None;
    }
    let Opnd::Imm(imm) = insn.operands[2] else {
        return None;
    };
    Some((x_reg(&insn.operands[0])?, x_reg(&insn.operands[1])?, imm))
}

/// Returns the slot the stub at `va` jumps through.
///
/// # Arguments
///
/// * `text` - The code.
/// * `va` - Where the stub would start.
///
/// # Returns
///
/// The slot's address, or `None` when the words at `va` are no stub.
pub(super) fn slot(text: &Text<'_>, va: u64) -> Option<u64> {
    let mut insns = (0..STUB_INSNS_MAX).map_while(|k| {
        let at = va.checked_add(u64::try_from(k).ok()?.checked_mul(4)?)?;
        Some(a64::decode(text.word(at)?, at))
    });
    let mut first = insns.next()?;
    if first.op == Op::Bti {
        first = insns.next()?;
    }
    let (page_reg, page) = adrp(&first)?;
    let second = insns.next()?;
    let (reg, slot) = match add_imm(&second) {
        Some((at_reg, from, off)) if from == page_reg => {
            let (reg, base, 0) = load(&insns.next()?)? else {
                return None;
            };
            (base == at_reg).then_some((reg, page.wrapping_add(off)))?
        }
        Some(_) => return None,
        None => {
            let (reg, base, disp) = load(&second)?;
            (base == page_reg).then_some((reg, page.wrapping_add_signed(disp)))?
        }
    };
    for insn in insns {
        if insn.op == Op::Br {
            return (x_reg(&insn.operands[0]) == Some(reg)).then_some(slot);
        }
        let aside = insn.op == Op::Pac || add_imm(&insn).is_some_and(|(to, ..)| to != reg);
        if !aside {
            return None;
        }
    }
    None
}

/// Returns the slot a `blr` or `br` calls through when the instructions
/// right before it load its register from a constant address.
///
/// The words before the call are read back, while each falls through to
/// the next, for the last write to the call's register: a 64-bit load at
/// an offset from a register an `adrp` set, nothing between writing
/// either register.
///
/// # Arguments
///
/// * `text` - The code.
/// * `call` - The `blr` or `br`.
///
/// # Returns
///
/// The slot's address, or `None` when the register is not loaded that way
/// within [`SLICE_MAX`] instructions.
pub(super) fn slot_call(text: &Text<'_>, call: &Insn) -> Option<u64> {
    let mut want = x_reg(&call.operands[0])?;
    let mut disp: Option<i64> = None;
    let mut va = call.va;
    for _ in 0..SLICE_MAX {
        va = va.checked_sub(4)?;
        let insn = a64::decode(text.word(va)?, va);
        if !falls_through(&insn) {
            return None;
        }
        if writes(&insn) & (1u32 << want) == 0 {
            continue;
        }
        if let Some(d) = disp {
            let (reg, page) = adrp(&insn)?;
            return (reg == want).then_some(page.wrapping_add_signed(d));
        }
        let (reg, base, off) = load(&insn)?;
        if reg != want {
            return None;
        }
        want = base;
        disp = Some(off);
    }
    None
}

/// Names every unnamed function that is a stub after what its slot holds.
///
/// A slot that holds an import names the stub after it and is recorded as
/// the function's thunk ([`Function::thunk`]). A slot the loader binds to
/// a function of the program's own names the stub after that function,
/// recorded as the one it reaches ([`Function::bound`]).
///
/// # Arguments
///
/// * `program` - The loaded image, for the import slots and the bound
///   slots.
/// * `text` - The code.
/// * `functions` - The functions, updated in place.
pub(super) fn name(program: &Program, text: &Text<'_>, functions: &mut [Function]) {
    let mut imports: BTreeMap<u64, &str> = BTreeMap::new();
    for s in &program.symbols {
        if s.kind == SymbolKind::Import && s.addr != 0 {
            imports.entry(s.addr).or_insert(&s.name);
        }
    }
    let own: BTreeMap<u64, String> = functions
        .iter()
        .filter(|f| f.name_source == NameSource::Symbol)
        .filter_map(|f| Some((f.entry, f.name.clone()?)))
        .collect();
    for f in functions
        .iter_mut()
        .filter(|f| f.name.is_none() && f.instr_count <= STUB_INSNS_MAX)
    {
        let Some(slot) = slot(text, f.entry) else {
            continue;
        };
        if let Some(import) = imports.get(&slot) {
            f.name = Some(crate::search::demangled_name(import));
            f.thunk = Some(slot);
        } else if let Some((target, name)) = crate::analysis::decompile::abi::bound(program, slot)
            .filter(|t| *t != f.entry)
            .and_then(|t| Some((t, own.get(&t)?)))
        {
            f.name = Some(name.clone());
            f.bound = Some(target);
        } else {
            continue;
        }
        f.name_source = NameSource::Symbol;
    }
}
