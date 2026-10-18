//! How many entries a switch's jump table has: the range check that bounds
//! the value indexing it.
//!
//! A compiler checks the index before it reads the table, but not always
//! in the register it reads the table with. LLVM checks a rebased copy
//! (`lea r8d, [rcx - 6]; cmp r8b, 8; ja default; add ecx, -6`), masks one
//! copy and checks another (`and cl, 0xf; cmp cl, 6; ja default; and eax,
//! 0xf`), and unoptimized code keeps the index in a stack slot. So the
//! instructions before the jump are followed as values rather than
//! registers: each is a base plus a constant offset, and a check counts
//! when the value it checks is the value the table is read with. Taking
//! the nearest check of any value instead read a table indexed by a value
//! that is only ever 2 or 3 as 64 entries, on into its neighbors'.
//!
//! The window is only the last few dozen instructions, though, and an
//! index that comes into it from further back may have been tied to a
//! checked value there, or be an enum's tag whose type bounds it with no
//! check at all. Only for such an index does the nearest check of some
//! other value still stand, as a guess, and the table it sizes is cut
//! short where its entries stop looking like cases.

use crate::isa::x86::{
    FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register,
};

use super::functions::tables::TABLE_ENTRIES_MAX;
use super::is_imm;
use crate::fxmap::FxHashMap;
use crate::num::{lo32, saturating_usize};

/// How many entries a range check allows a jump table, and where the
/// check sits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct TableBound {
    /// Position of the check in the window before the jump.
    pub check_at: usize,
    /// The entries the check allows.
    pub entries: u64,
    /// The count is only an upper bound (a mask's, or a guess from a check
    /// of another value): the table may be shorter and the data after it
    /// read as entries.
    pub loose: bool,
}

/// The entries a range check bounds a table to.
///
/// The check is `cmp idx, N` (or `sub idx, N`, which sets the flags the
/// same way and appears when the index is also rebased) immediately
/// followed by an unsigned conditional jump: `ja`/`jbe` mean `0..=N`,
/// `jae`/`jb` mean `0..N`.
///
/// # Arguments
///
/// * `i` - The candidate check.
/// * `jcc` - The instruction after it.
///
/// # Returns
///
/// The entry count, or `None` when `i` is not such a check.
pub(super) fn check_bound(i: &Instruction, jcc: Option<&Instruction>) -> Option<u64> {
    if !matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Sub) {
        return None;
    }
    let jcc = jcc?;
    (0..i.op_count())
        .filter(|&op| is_imm(i.op_kind(op)))
        .map(|op| i.immediate(op))
        .filter(|v| (1..=TABLE_ENTRIES_MAX).contains(v))
        .filter_map(|v| match jcc.mnemonic() {
            Mnemonic::Ja | Mnemonic::Jbe => Some(v + 1),
            Mnemonic::Jae | Mnemonic::Jb => Some(v),
            _ => None,
        })
        .next_back()
}

/// Whether the path to the table leaves a check's jump where the value is
/// small.
///
/// That is the fall-through of `ja`/`jae`, which jump away to the default,
/// or the target of `jbe`/`jb`. On the other edge the check is a lower
/// bound and bounds no table: `cmp al, 2; jb elsewhere` falls through with
/// `al` at least 2.
///
/// # Arguments
///
/// * `jcc` - The check's jump.
/// * `next` - Address of the instruction the path reaches after it.
fn below_on_path(jcc: &Instruction, next: u64) -> bool {
    let taken = next != jcc.next_ip();
    match jcc.mnemonic() {
        Mnemonic::Ja | Mnemonic::Jae => !taken,
        Mnemonic::Jbe | Mnemonic::Jb => taken,
        _ => false,
    }
}

/// Where a jump table is read, and the register that indexes it.
///
/// The jump itself reads it for `jmp [T + idx * 8]`; otherwise it is the
/// last load before the jump that scales an index by 4 or 8 (`movsxd rax,
/// [rcx + rax * 4]`, `mov ecx, [rdx + rax * 4 + T]`).
///
/// # Arguments
///
/// * `window` - The instructions before the jump, in order.
/// * `jmp` - The jump.
///
/// # Returns
///
/// The load's position in `window` (its length for the jump) and its index
/// register, or `None` when nothing scales an index.
pub(super) fn table_index(
    window: &[Instruction],
    jmp: Option<&Instruction>,
) -> Option<(usize, Register)> {
    if let Some(j) = jmp
        && j.op0_kind() == OpKind::Memory
        && j.memory_index() != Register::None
    {
        return Some((window.len(), j.memory_index()));
    }
    window.iter().enumerate().rev().find_map(|(k, i)| {
        let loads = (0..i.op_count()).any(|op| i.op_kind(op) == OpKind::Memory);
        (loads
            && i.mnemonic() != Mnemonic::Lea
            && matches!(i.memory_index_scale(), 4 | 8)
            && i.memory_index() != Register::None)
            .then(|| (k, i.memory_index()))
    })
}

/// The register a byte-table read is indexed by, when `i` is one.
///
/// MSVC picks a jump table's slot from a table of bytes when cases share
/// targets: `movzx eax, byte [rdx + rcx + T]` in 64-bit code, where `rdx`
/// holds the image base, and `movzx eax, byte [ecx + T]` in 32-bit code,
/// where the table's address is the displacement. A byte local (`[ebp -
/// 8]`) has no such displacement.
///
/// # Arguments
///
/// * `i` - The instruction.
fn byte_table_index(i: &Instruction) -> Option<Register> {
    if i.mnemonic() != Mnemonic::Movzx
        || i.op1_kind() != OpKind::Memory
        || i.memory_size().size() != 1
    {
        return None;
    }
    if i.memory_index() != Register::None {
        return Some(i.memory_index().full_register());
    }
    let d = i.memory_displacement64();
    let address = if d > u64::from(u32::MAX) {
        false
    } else {
        i64::from(lo32(d).cast_signed()) >= 0x1_0000
    };
    (address && i.memory_base().is_gpr()).then(|| i.memory_base().full_register())
}

/// A value the trace follows: an interned base plus a constant offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Val {
    /// Index into [`Trace::bases`].
    base: u32,
    /// What was added to the base.
    off: i64,
}

/// How a base value arose. Interned, so the same computation of the same
/// value is one base: `and cl, 0xf` of a copy of `eax` and `and eax, 0xf`
/// agree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Base {
    /// What a home held when the window began: read before anything in
    /// the window wrote it.
    Incoming(u32),
    /// What an instruction the trace does not model wrote.
    Opaque(u32),
    /// A value masked with a constant.
    Masked(Val, u64),
    /// An entry of a byte table read at a value: MSVC picks the jump
    /// table's slot this way, and the check bounds the byte table's index.
    Picked(Val),
}

/// Where a value lives: a register by its full width, or a stack slot by
/// its base register and displacement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Home {
    /// A general register.
    Reg(Register),
    /// A memory operand with no index register.
    Slot(Register, u64),
}

impl Home {
    /// The home operand `op` of `i` names, when it can hold an index.
    fn of(i: &Instruction, op: u32) -> Option<Home> {
        match i.op_kind(op) {
            OpKind::Register if i.op_register(op).is_gpr() => {
                Some(Home::Reg(i.op_register(op).full_register()))
            }
            OpKind::Memory
                if i.memory_index() == Register::None
                    && !matches!(
                        i.memory_base(),
                        Register::None | Register::RIP | Register::EIP
                    ) =>
            {
                Some(Home::Slot(
                    i.memory_base().full_register(),
                    i.memory_displacement64(),
                ))
            }
            _ => None,
        }
    }
}

/// One check of a value the trace saw.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Check {
    /// Position of the check in the window.
    at: usize,
    /// The value it checks.
    value: Val,
    /// The entries it allows a table indexed by that value.
    entries: u64,
    /// The check is a mask, which only bounds the value to its width.
    masked: bool,
}

/// The values held along the instructions before a jump, and every check
/// made of them.
#[derive(Default)]
struct Trace {
    /// Interned bases, by id.
    bases: Vec<Base>,
    /// Id of each interned base.
    ids: FxHashMap<Base, u32>,
    /// What each home holds, where known.
    held: FxHashMap<Home, Val>,
    /// Every check, in window order.
    bounds: Vec<Check>,
    /// Incoming and opaque bases made so far, which keeps each one apart.
    fresh: u32,
}

impl Trace {
    /// The value of `base` with no offset, interning it.
    fn intern(&mut self, base: Base) -> Val {
        let next = u32::try_from(self.bases.len()).unwrap_or(u32::MAX);
        let id = *self.ids.entry(base).or_insert(next);
        if id == next {
            self.bases.push(base);
        }
        Val { base: id, off: 0 }
    }

    /// A value an instruction the trace does not model wrote.
    fn unknown(&mut self) -> Val {
        self.fresh += 1;
        self.intern(Base::Opaque(self.fresh))
    }

    /// What `home` holds: when nothing in the window wrote it, the value it
    /// came in with, the same for every read so that copies of it agree.
    fn read(&mut self, home: Home) -> Val {
        if let Some(v) = self.held.get(&home) {
            return *v;
        }
        self.fresh += 1;
        let v = self.intern(Base::Incoming(self.fresh));
        self.held.insert(home, v);
        v
    }

    /// Whether `v` came into the window rather than being computed in it.
    fn incoming(&self, v: Val) -> bool {
        matches!(
            self.bases.get(saturating_usize(u64::from(v.base))),
            Some(Base::Incoming(_))
        )
    }

    /// Applies one instruction; one the trace does not model leaves what it
    /// wrote unknown.
    ///
    /// # Arguments
    ///
    /// * `k` - Its position.
    /// * `i` - The instruction.
    /// * `next` - The instruction after it, the jump a check feeds.
    /// * `after` - Address the path reaches after `next`.
    /// * `info` - Register-access facts for writes the trace does not model.
    fn step(
        &mut self,
        k: usize,
        i: &Instruction,
        next: Option<&Instruction>,
        after: u64,
        info: &mut InstructionInfoFactory,
    ) {
        if matches!(
            i.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            self.held.clear();
            return;
        }
        let dst = if i.op_count() > 0 {
            Home::of(i, 0)
        } else {
            None
        };
        let imm = (i.op_count() > 1 && is_imm(i.op1_kind())).then(|| {
            let bits = 8 * i.op0_register().size().max(i.memory_size().size()).max(1);
            let v = i.immediate(1);
            if bits >= 64 {
                v.cast_signed()
            } else {
                (v << (64 - bits)).cast_signed() >> (64 - bits)
            }
        });
        match (i.mnemonic(), dst) {
            (Mnemonic::Cmp | Mnemonic::Sub, Some(h)) if check_bound(i, next).is_some() => {
                let mut v = self.read(h);
                if i.mnemonic() == Mnemonic::Sub {
                    v.off = v.off.wrapping_sub(imm.unwrap_or(0));
                    self.held.insert(h, v);
                }
                if next.is_some_and(|j| below_on_path(j, after)) {
                    self.bounds.push(Check {
                        at: k,
                        value: v,
                        entries: check_bound(i, next).unwrap_or(0),
                        masked: false,
                    });
                }
                return;
            }
            (
                Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Cdqe | Mnemonic::Cwde | Mnemonic::Cbw,
                _,
            ) => {
                return;
            }
            (Mnemonic::Add | Mnemonic::Sub, Some(h)) if imm.is_some() => {
                let d = imm.unwrap_or(0);
                let mut v = self.read(h);
                v.off = if i.mnemonic() == Mnemonic::Add {
                    v.off.wrapping_add(d)
                } else {
                    v.off.wrapping_sub(d)
                };
                self.held.insert(h, v);
                return;
            }
            (Mnemonic::And, Some(h)) if imm.is_some() => {
                let mask = i.immediate(1);
                let from = self.read(h);
                let v = self.intern(Base::Masked(from, mask));
                self.held.insert(h, v);
                if mask < TABLE_ENTRIES_MAX {
                    self.bounds.push(Check {
                        at: k,
                        value: v,
                        entries: mask + 1,
                        masked: true,
                    });
                }
                return;
            }
            (Mnemonic::Mov | Mnemonic::Movzx | Mnemonic::Movsx | Mnemonic::Movsxd, Some(h)) => {
                let v = match byte_table_index(i) {
                    Some(at) => {
                        let at = self.read(Home::Reg(at));
                        self.intern(Base::Picked(at))
                    }
                    None => match Home::of(i, 1) {
                        Some(src) => self.read(src),
                        None => self.unknown(),
                    },
                };
                self.held.insert(h, v);
                return;
            }
            (Mnemonic::Lea, Some(h))
                if i.memory_index() == Register::None
                    && !matches!(
                        i.memory_base(),
                        Register::None | Register::RIP | Register::EIP
                    ) =>
            {
                let d = i.memory_displacement64();
                let d = if d > u64::from(u32::MAX) {
                    d.cast_signed()
                } else {
                    i64::from(lo32(d).cast_signed())
                };
                let mut v = self.read(Home::Reg(i.memory_base().full_register()));
                v.off = v.off.wrapping_add(d);
                self.held.insert(h, v);
                return;
            }
            _ => {}
        }
        let written: Vec<Register> = info
            .info(i)
            .used_registers()
            .iter()
            .filter(|u| {
                matches!(
                    u.access(),
                    OpAccess::Write
                        | OpAccess::CondWrite
                        | OpAccess::ReadWrite
                        | OpAccess::ReadCondWrite
                ) && u.register().is_gpr()
            })
            .map(|u| u.register().full_register())
            .collect();
        for r in written {
            let v = self.unknown();
            self.held.insert(Home::Reg(r), v);
        }
        if let Some(h @ Home::Slot(..)) = dst {
            let v = self.unknown();
            self.held.insert(h, v);
        }
    }
}

/// The range check that bounds a table's index.
///
/// The instructions before the load are followed as values ([`Trace`]);
/// a check counts when it checks the value the load indexes with or, when
/// nothing does and that value was read from a byte table, the value the
/// byte table was read at (MSVC checks the case, not the slot it picks).
/// The window is one path to the jump, and a check far up it need not
/// govern every path that joins it later, so the check nearest the load
/// wins. A mask only bounds the index to its width, so it counts when no
/// compare does: after `and cl, 0xf; cmp cl, 6; ja default; and eax, 0xf`
/// the table has 7 entries, not 16.
///
/// When nothing checks an index that came into the window from before it,
/// the nearest compare of any value is taken as a loose guess: the two may
/// have been one value further back. An index the window computes gets no
/// such guess, since the window shows where it came from.
///
/// # Arguments
///
/// * `window` - The instructions before the jump, in order.
/// * `jmp_va` - Address of the jump.
/// * `at` - Position of the table load in `window`.
/// * `index` - The load's index register.
///
/// # Returns
///
/// The bound, or `None` when nothing checks the index.
pub(super) fn index_bound(
    window: &[Instruction],
    jmp_va: u64,
    at: usize,
    index: Register,
) -> Option<TableBound> {
    let mut trace = Trace::default();
    let mut info = InstructionInfoFactory::new();
    let end = at.min(window.len());
    let ip = |p: usize| window.get(p).map_or(jmp_va, Instruction::ip);
    for (k, i) in window.iter().enumerate().take(end) {
        trace.step(k, i, window.get(k + 1), ip(k + 2), &mut info);
    }
    let v = trace.read(Home::Reg(index.full_register()));
    let nearest = |checked: Val| {
        trace
            .bounds
            .iter()
            .filter(|c| c.value == checked)
            .max_by_key(|c| (!c.masked, c.at))
            .map(|c| TableBound {
                check_at: c.at,
                entries: c.entries,
                loose: c.masked,
            })
    };
    let source = match trace.bases.get(saturating_usize(u64::from(v.base))) {
        Some(Base::Picked(at)) if v.off == 0 => Some(*at),
        _ => None,
    };
    if let Some(found) = nearest(v).or_else(|| source.and_then(nearest)) {
        return Some(found);
    }
    if !trace.incoming(source.unwrap_or(v)) {
        return None;
    }
    trace
        .bounds
        .iter()
        .filter(|c| !c.masked)
        .max_by_key(|c| c.at)
        .map(|c| TableBound {
            check_at: c.at,
            entries: c.entries,
            loose: true,
        })
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{TableBound, index_bound, table_index};
    use crate::isa::x86::{Decoder, DecoderOptions, Instruction};

    /// Decodes `code` at 0x1000 in 64-bit mode.
    fn decode(code: &[u8]) -> Vec<Instruction> {
        Decoder::with_ip(64, code, 0x1000, DecoderOptions::NONE)
            .into_iter()
            .collect()
    }

    /// Bounds the table read by the last instruction of `code` but the jump.
    fn bound(code: &[u8]) -> Option<u64> {
        bound_at(&decode(code))
    }

    /// [`bound`] for 32-bit code.
    fn bound32(code: &[u8]) -> Option<u64> {
        let all: Vec<Instruction> = Decoder::with_ip(32, code, 0x1000, DecoderOptions::NONE)
            .into_iter()
            .collect();
        bound_at(&all)
    }

    /// Bounds the table the jump ending `all` reads.
    fn bound_at(all: &[Instruction]) -> Option<u64> {
        let (window, jmp) = all.split_at(all.len() - 1);
        let jmp = jmp.first()?;
        let (at, index) = table_index(window, Some(jmp))?;
        index_bound(window, jmp.ip(), at, index).map(|b| b.entries)
    }

    #[test]
    fn a_check_of_the_index_register_bounds_it() {
        let code: &[u8] = &[
            0x48, 0x83, 0xfd, 0x04, // ASM: cmp rbp,4
            0x73, 0x1d, // ASM: jae +0x1d
            0x48, 0x8d, 0x0d, 0xa8, 0x83, 0x94, 0x00, // ASM: lea rcx,[rip+X]
            0x48, 0x63, 0x04, 0xa9, // ASM: movsxd rax,[rcx+rbp*4]
            0x48, 0x01, 0xc8, // ASM: add rax,rcx
            0xff, 0xe0, // ASM: jmp rax
        ];
        assert_eq!(bound(code), Some(4));
    }

    /// An index loaded from a table of its own is checked as itself, not
    /// as the index of the table it came from.
    #[test]
    fn an_index_loaded_through_another_index_is_checked_as_itself() {
        let code: &[u8] = &[
            0x49, 0x8b, 0x6c, 0xc5, 0x10, // ASM: mov rbp,[r13+rax*8+0x10]
            0x48, 0x83, 0xfd, 0x04, // ASM: cmp rbp,4
            0x73, 0x1d, // ASM: jae +0x1d
            0x48, 0x8d, 0x0d, 0xa8, 0x83, 0x94, 0x00, // ASM: lea rcx,[rip+X]
            0x48, 0x63, 0x04, 0xa9, // ASM: movsxd rax,[rcx+rbp*4]
            0x48, 0x01, 0xc8, // ASM: add rax,rcx
            0xff, 0xe0, // ASM: jmp rax
        ];
        assert_eq!(bound(code), Some(4));
    }

    /// LLVM checks a rebased byte copy and then rebases the index itself.
    #[test]
    fn a_rebased_copy_checked_bounds_the_rebased_index() {
        let code: &[u8] = &[
            0x0f, 0xb6, 0x8d, 0xd1, 0x01, 0x00, 0x00, // ASM: movzx ecx,byte [rbp+0x1d1]
            0x44, 0x8d, 0x41, 0xfa, // ASM: lea r8d,[rcx-6]
            0x41, 0x80, 0xf8, 0x08, // ASM: cmp r8b,8
            0x0f, 0x87, 0x90, 0x03, 0x00, 0x00, // ASM: ja +0x390
            0x83, 0xc1, 0xfa, // ASM: add ecx,-6
            0x4c, 0x8d, 0x05, 0x8a, 0x72, 0x88, 0x00, // ASM: lea r8,[rip+X]
            0x49, 0x63, 0x0c, 0x88, // ASM: movsxd rcx,[r8+rcx*4]
            0x4c, 0x01, 0xc1, // ASM: add rcx,r8
            0xff, 0xe1, // ASM: jmp rcx
        ];
        assert_eq!(bound(code), Some(9));
    }

    /// Two copies masked alike are one value, and a check of either
    /// bounds the other tighter than the mask does.
    #[test]
    fn a_check_of_a_masked_copy_bounds_the_masked_index() {
        let code: &[u8] = &[
            0x89, 0xc1, // ASM: mov ecx,eax
            0x80, 0xe1, 0x0f, // ASM: and cl,0xf
            0x80, 0xf9, 0x06, // ASM: cmp cl,6
            0x0f, 0x87, 0x35, 0x01, 0x00, 0x00, // ASM: ja +0x135
            0x83, 0xe0, 0x0f, // ASM: and eax,0xf
            0x48, 0x8d, 0x0d, 0x30, 0x9d, 0x5b, 0x00, // ASM: lea rcx,[rip+X]
            0x48, 0x63, 0x04, 0x81, // ASM: movsxd rax,[rcx+rax*4]
            0x48, 0x01, 0xc8, // ASM: add rax,rcx
            0xff, 0xe0, // ASM: jmp rax
        ];
        assert_eq!(bound(code), Some(7));
    }

    /// A 32-bit byte table is indexed by its base register; the check of
    /// that register bounds the byte table.
    #[test]
    fn a_32_bit_byte_table_is_bounded_by_its_base_register() {
        let code: &[u8] = &[
            0x83, 0xfb, 0x07, // ASM: cmp ebx,7
            0x0f, 0x87, 0xac, 0x00, 0x00, 0x00, // ASM: ja +0xac
            0x0f, 0xb6, 0x83, 0x7d, 0x06, 0x02, 0x10, // ASM: movzx eax,byte [ebx+0x1002067d]
            0xff, 0x24, 0x85, 0x71, 0x06, 0x02, 0x10, // ASM: jmp dword [eax*4+0x10020671]
        ];
        assert_eq!(bound32(code), Some(8));
    }

    /// A lower bound on the path is no bound: `cmp al, 2; jb` falls through
    /// with `al` at least 2, and the table's own check is the later one.
    #[test]
    fn a_lower_bound_on_the_path_is_not_the_tables() {
        let code: &[u8] = &[
            0x3c, 0x02, // ASM: cmp al,2
            0x72, 0x40, // ASM: jb +0x40
            0x3c, 0x0c, // ASM: cmp al,0xc
            0x77, 0x3c, // ASM: ja +0x3c
            0x0f, 0xb6, 0xc0, // ASM: movzx eax,al
            0x0f, 0xb6, 0x80, 0x04, 0x3a, 0x01, 0x10, // ASM: movzx eax,byte [eax+0x10013a04]
            0xff, 0x24, 0x85, 0xe8, 0x39, 0x01, 0x10, // ASM: jmp dword [eax*4+0x100139e8]
        ];
        assert_eq!(bound32(code), Some(13));
    }

    /// A byte read from a buffer and then checked is bounded by its own
    /// check, not by the index it was read at.
    #[test]
    fn a_checked_byte_is_bounded_as_itself() {
        let code: &[u8] = &[
            0x48, 0x83, 0xfa, 0x04, // ASM: cmp rdx,4
            0x73, 0x31, // ASM: jae +0x31
            0x0f, 0xb6, 0xb4, 0x15, 0x10, 0x05, 0x00,
            0x00, // ASM: movzx esi,byte [rbp+rdx+0x510]
            0x48, 0x83, 0xfe, 0x18, // ASM: cmp rsi,0x18
            0x77, 0xd2, // ASM: ja -0x2e
            0x4c, 0x8d, 0x3d, 0xde, 0x88, 0x59, 0x00, // ASM: lea r15,[rip+X]
            0x49, 0x63, 0x34, 0xb7, // ASM: movsxd rsi,[r15+rsi*4]
            0x4c, 0x01, 0xfe, // ASM: add rsi,r15
            0xff, 0xe6, // ASM: jmp rsi
        ];
        assert_eq!(bound(code), Some(25));
    }

    /// MSVC widens the checked index with `cdqe` between the check and the
    /// load; the widened index is the one it checked.
    #[test]
    fn a_widened_index_is_the_one_checked() {
        let code: &[u8] = &[
            0xff, 0xc8, // ASM: dec eax
            0x83, 0xf8, 0x0a, // ASM: cmp eax,0xa
            0x0f, 0x87, 0x29, 0xd3, 0xff, 0xff, // ASM: ja -0x2cd7
            0x48, 0x8d, 0x15, 0x27, 0x61, 0xff, 0xff, // ASM: lea rdx,[rip+X]
            0x48, 0x98, // ASM: cdqe
            0x8b, 0x8c, 0x82, 0x30, 0xac, 0x00, 0x00, // ASM: mov ecx,[rdx+rax*4+0xac30]
            0x48, 0x03, 0xca, // ASM: add rcx,rdx
            0xff, 0xe1, // ASM: jmp rcx
        ];
        assert_eq!(bound(code), Some(11));
    }

    /// An index that comes into the window unchecked takes the nearest
    /// check of another value as a loose guess; they may have been one
    /// value before the window began.
    #[test]
    fn an_incoming_index_takes_a_nearby_check_as_a_guess() {
        let code: &[u8] = &[
            0x41, 0x80, 0xfe, 0x08, // ASM: cmp r14b,8
            0x0f, 0x87, 0x00, 0x09, 0x00, 0x00, // ASM: ja +0x900
            0x48, 0x8d, 0x15, 0xec, 0xe6, 0x83, 0x00, // ASM: lea rdx,[rip+X]
            0x4e, 0x63, 0x04, 0x92, // ASM: movsxd r8,[rdx+r10*4]
            0x49, 0x01, 0xd0, // ASM: add r8,rdx
            0x41, 0xff, 0xe0, // ASM: jmp r8
        ];
        let all = decode(code);
        let (window, jmp) = all.split_at(all.len() - 1);
        let jmp = jmp.first().expect("a jump");
        let (at, index) = table_index(window, Some(jmp)).expect("a table load");
        assert_eq!(
            index_bound(window, jmp.ip(), at, index),
            Some(TableBound {
                check_at: 0,
                entries: 9,
                loose: true
            })
        );
    }

    /// A check of some other value bounds nothing: the index here is only
    /// ever 2 or 3, and the nearby compare is of a different register.
    #[test]
    fn a_check_of_another_value_bounds_nothing() {
        let code: &[u8] = &[
            0x48, 0x83, 0xf8, 0x3f, // ASM: cmp rax,0x3f
            0x0f, 0x86, 0xef, 0x02, 0x00, 0x00, // ASM: jbe +0x2ef
            0x48, 0x8d, 0x48, 0xc0, // ASM: lea rcx,[rax-0x40]
            0x48, 0x83, 0xf9, 0x40, // ASM: cmp rcx,0x40
            0x0f, 0x92, 0xc2, // ASM: setb dl
            0x80, 0xca, 0x02, // ASM: or dl,2
            0x0f, 0xb6, 0xc2, // ASM: movzx eax,dl
            0x48, 0x8d, 0x0d, 0x9a, 0x9f, 0x9d, 0x00, // ASM: lea rcx,[rip+X]
            0x48, 0x63, 0x04, 0x81, // ASM: movsxd rax,[rcx+rax*4]
            0x48, 0x01, 0xc8, // ASM: add rax,rcx
            0xff, 0xe0, // ASM: jmp rax
        ];
        assert_eq!(bound(code), None);
    }
}
