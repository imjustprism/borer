//! Every instruction that dereferences `[register + offset]` for one offset:
//! who reads or writes a struct field, found at the instruction level.
//!
//! [`super::classes::class_layout`] answers "which fields does this class
//! touch"; this answers the inverse, "who touches this field", across the
//! whole program. A byte search for the encoding finds the same sites among
//! dozens that share the displacement by accident and names none of them;
//! here each site carries its function, width, direction and the immediate it
//! stores, so `mov byte [rdi+0x551], 1` reads as the write it is.

use std::fmt::Write as _;

use crate::isa::{Instruction, InstructionInfoFactory, Mnemonic, OpAccess, Register};

use super::functions::decode_block;
use super::{Analysis, Function, Overlay, is_imm, name_of, striped};
use crate::program::Program;

/// How one site uses the field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldAccess {
    /// The field is loaded.
    Read,
    /// The field is stored.
    Write,
    /// The field is loaded and stored by the one instruction (`add`, `inc`, `xchg`).
    ReadWrite,
    /// The field's address is taken (`lea`), not its value.
    Address,
}

impl FieldAccess {
    /// Returns the direction as listings print it: `r`, `w`, `rw` or `&`.
    #[must_use]
    pub fn code(self) -> &'static str {
        match self {
            FieldAccess::Read => "r",
            FieldAccess::Write => "w",
            FieldAccess::ReadWrite => "rw",
            FieldAccess::Address => "&",
        }
    }
}

/// One instruction that touches `[base + offset]`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldRef {
    /// The instruction's address.
    pub va: u64,
    /// Entry of the function the instruction belongs to.
    pub entry: u64,
    /// The base register in its full width (`rdi`, never `edi`).
    pub base: Register,
    /// Bytes accessed; `0` when the access has no width (an `lea`).
    pub width: usize,
    /// The direction of the access.
    pub access: FieldAccess,
    /// The instruction's mnemonic.
    pub mnemonic: Mnemonic,
    /// The immediate operand when the instruction carries one (`mov [..], 1`, `or [..], 4`).
    pub immediate: Option<u64>,
}

/// Tells whether a base register addresses an object rather than the stack
/// or the code: any general-purpose register but the stack pointer.
///
/// `rbp` stays in: x64 code that keeps no frame pointer uses it as an ordinary
/// object pointer, and a listing shows the base so a frame use reads as one.
///
/// # Arguments
///
/// * `base` - The memory operand's base register.
fn is_object_base(base: Register) -> bool {
    base.is_gpr() && base.full_register() != Register::RSP
}

/// The first immediate operand an instruction carries, if any.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
fn immediate_of(instr: &Instruction) -> Option<u64> {
    (0..instr.op_count()).find_map(|i| {
        is_imm(instr.op_kind(i))
            .then(|| instr.try_immediate(i).ok())
            .flatten()
    })
}

/// Collects the sites in one function, in address order.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `f` - The function whose blocks are decoded.
/// * `bitness` - Decoder bitness, `32` or `64`.
/// * `offset` - The field offset the sites must address.
pub(crate) fn refs_in(program: &Program, f: &Function, bitness: u32, offset: i64) -> Vec<FieldRef> {
    let mut factory = InstructionInfoFactory::new();
    let mut out = Vec::new();
    for instr in f
        .blocks
        .iter()
        .flat_map(|b| decode_block(program, bitness, b))
    {
        let base = instr.memory_base();
        if !is_object_base(base)
            || instr.memory_index() != Register::None
            || crate::disasm::displacement(&instr, bitness) != offset
        {
            continue;
        }
        let (access, width) = if instr.mnemonic() == Mnemonic::Lea {
            (FieldAccess::Address, 0)
        } else {
            let info = factory.info(&instr);
            let Some(m) = info.used_memory().iter().find(|m| m.base() == base) else {
                continue;
            };
            let access = match m.access() {
                OpAccess::Read | OpAccess::CondRead => FieldAccess::Read,
                OpAccess::Write | OpAccess::CondWrite => FieldAccess::Write,
                OpAccess::ReadWrite | OpAccess::ReadCondWrite => FieldAccess::ReadWrite,
                OpAccess::None | OpAccess::NoMemAccess => continue,
            };
            (access, m.memory_size().size())
        };
        out.push(FieldRef {
            va: instr.ip(),
            entry: f.entry,
            base: base.full_register(),
            width,
            access,
            mnemonic: instr.mnemonic(),
            immediate: immediate_of(&instr),
        });
    }
    out
}

/// Finds every instruction in the program that reads, writes or takes the
/// address of `[base + offset]`.
///
/// Only a plain base is matched: an indexed operand (`[rcx+rax*8+off]`)
/// addresses an array element, not a field, and a stack-relative one a local.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results; every function's blocks are decoded.
/// * `offset` - The field's byte offset, signed as the instruction encodes it.
///
/// # Returns
///
/// The sites in address order; empty on an architecture the decoder does not
/// cover.
#[must_use]
pub fn field_refs(program: &Program, analysis: &Analysis, offset: i64) -> Vec<FieldRef> {
    let Some(bitness) = program.arch.bitness() else {
        return Vec::new();
    };
    let per_function = striped(&analysis.functions, |f| {
        refs_in(program, f, bitness, offset)
    });
    let mut out: Vec<FieldRef> = per_function.into_iter().flatten().flatten().collect();
    out.sort_by_key(|r| r.va);
    out.dedup_by_key(|r| r.va);
    out
}

/// Renders a signed field offset as `+0x10` or `-0x8`.
///
/// # Arguments
///
/// * `offset` - The offset.
fn signed_hex(offset: i64) -> String {
    if offset < 0 {
        format!("-{:#x}", offset.unsigned_abs())
    } else {
        format!("+{offset:#x}")
    }
}

/// Renders the sites for one offset as a `#`-headed table, paged.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `offset` - The field's byte offset.
/// * `filter` - Case-insensitive substring of the function name; empty for all.
/// * `skip` - Rows to skip.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn field_refs_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    offset: i64,
    filter: &str,
    skip: usize,
    limit: usize,
) -> String {
    let q = filter.to_lowercase();
    let rows: Vec<(FieldRef, String)> = field_refs(program, analysis, offset)
        .into_iter()
        .map(|r| {
            let name = name_of(analysis, overlay, r.entry);
            (r, name)
        })
        .filter(|(_, name)| q.is_empty() || name.to_lowercase().contains(&q))
        .collect();
    let total = rows.len();
    let shown = total.saturating_sub(skip).min(limit);
    let mut out = format!(
        "# {total} sites touch [reg{}], showing {shown} from {skip}\n",
        signed_hex(offset)
    );
    out.push_str("va\tfunction\top\tbase\twidth\tdir\timm\n");
    for (r, name) in rows.into_iter().skip(skip).take(limit) {
        let imm = r.immediate.map_or_else(String::new, |v| format!("{v:#x}"));
        let _ = writeln!(
            out,
            "{:#x}\t{name}\t{}\t{}\t{}\t{}\t{imm}",
            r.va,
            format!("{:?}", r.mnemonic).to_lowercase(),
            format!("{:?}", r.base).to_lowercase(),
            r.width,
            r.access.code()
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A one-section program whose entry function touches `[rcx+0x551]` four
    /// ways and `[rsp+8]` once.
    fn program() -> Program {
        Program::raw_x64(&[
            0xc6, 0x81, 0x51, 0x05, 0x00, 0x00, 0x01, // ASM: mov byte [rcx+0x551], 1
            0x8b, 0x81, 0x51, 0x05, 0x00, 0x00, // ASM: mov eax, [rcx+0x551]
            0x48, 0x8d, 0x91, 0x51, 0x05, 0x00, 0x00, // ASM: lea rdx, [rcx+0x551]
            0x83, 0x81, 0x51, 0x05, 0x00, 0x00, 0x02, // ASM: add dword [rcx+0x551], 2
            0x8b, 0x44, 0x24, 0x08, // ASM: mov eax, [rsp+8]
            0xc3, // ASM: ret
        ])
    }

    /// Every way the entry touches the field is found with its direction,
    /// width and immediate, and the stack slot with the same displacement
    /// shape is not.
    ///
    /// # Panics
    ///
    /// When a site disagrees with the hand-assembled code.
    #[test]
    fn finds_each_access_kind_and_skips_the_stack() {
        let p = program();
        let a = Analysis::compute(&p);
        let refs = field_refs(&p, &a, 0x551);
        let shape: Vec<(u64, FieldAccess, usize, Option<u64>)> = refs
            .iter()
            .map(|r| (r.va, r.access, r.width, r.immediate))
            .collect();
        assert_eq!(
            shape,
            vec![
                (0x1000, FieldAccess::Write, 1, Some(1)),
                (0x1007, FieldAccess::Read, 4, None),
                (0x100d, FieldAccess::Address, 0, None),
                (0x1014, FieldAccess::ReadWrite, 4, Some(2)),
            ]
        );
        assert!(
            refs.iter()
                .all(|r| r.base == Register::RCX && r.entry == 0x1000)
        );
        assert!(
            field_refs(&p, &a, 8).is_empty(),
            "[rsp+8] is a local, not a field"
        );
        let text = field_refs_tsv(&p, &a, &Overlay::default(), 0x551, "", 0, 100);
        assert!(text.starts_with("# 4 sites touch [reg+0x551], showing 4 from 0\n"));
        assert!(
            text.contains("0x1000\tsub_1000\tmov\trcx\t1\tw\t0x1\n"),
            "{text}"
        );
        assert!(
            text.contains("0x100d\tsub_1000\tlea\trcx\t0\t&\t\n"),
            "{text}"
        );
        let none = field_refs_tsv(&p, &a, &Overlay::default(), 0x551, "nomatch", 0, 100);
        assert!(none.starts_with("# 0 sites touch"));
    }

    /// A negative offset prints with its sign, not as a two's-complement word.
    ///
    /// # Panics
    ///
    /// When the rendering disagrees with its expectation.
    #[test]
    fn negative_offsets_print_signed() {
        assert_eq!(signed_hex(-8), "-0x8");
        assert_eq!(signed_hex(0x10), "+0x10");
    }
}
