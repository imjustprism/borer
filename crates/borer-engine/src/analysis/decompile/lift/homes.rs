//! Where a prologue stores the argument registers.
//!
//! The Microsoft x64 home slots and the System V register save area tell a
//! variadic function's fixed arguments from its variable ones.

use super::*;

/// Bytes of one integer register's place in the System V save area.
const GPR: i64 = 8;

/// What one instruction does with the home slots of the argument registers.
pub(super) enum Home {
    /// Stores an argument register into its own home slot.
    Spill,
    /// Loads an argument's home slot back into a register.
    Load(Register),
    /// Takes the address of a home slot: `va_start`.
    VaStart,
}

/// Tracks the Microsoft x64 home slots, or the System V register save
/// area, through a prologue.
///
/// It follows where the stack pointer stands and which registers alias
/// it, so a store to `[rsp+8+8k]`, to `[rax+8+8k]` after `mov rax, rsp`
/// or to `[rbp+K]` after `mov rbp, rsp` is seen as the home of argument
/// `k`.
///
/// A variadic function homes every argument register from the first
/// variable one through `r9` and takes the address of the first variable
/// slot for `va_start`; a function that homes its arguments for their
/// addresses stops short of `r9` unless it has four.
///
/// System V has no home slots: a variadic function stores the argument
/// registers from the first variable one through `r9` into a save area of
/// its own frame, eight bytes apiece in register order, and the vector
/// ones (`xmm0` to `xmm7`, sixteen bytes apiece) after them behind a `test
/// al, al`, since `al` counts the vector registers its caller filled.
pub(super) struct Homes {
    /// Whether the convention has home slots at all.
    pub(super) active: bool,
    /// Whether the convention has a register save area instead (System V
    /// x64).
    save_area: bool,
    /// Where each argument register, by slot, was first stored, in bytes
    /// from the entry stack pointer.
    saved: BTreeMap<usize, i64>,
    /// Where each vector argument register, by position, was first stored.
    saved_vectors: BTreeMap<usize, i64>,
    /// The vector argument registers in order.
    vectors: Vec<Register>,
    /// A `test al, al` was seen: the count of vector arguments was read.
    counts_vectors: bool,
    /// Bytes the stack pointer stands below its entry value.
    pub(super) below: i64,
    /// Bytes below the entry stack pointer that `rax` stands for.
    pub(super) rax: Option<i64>,
    /// Bytes below the entry stack pointer that `rbp` stands for.
    pub(super) rbp: Option<i64>,
    /// Argument registers by slot.
    pub(super) args: Vec<Register>,
    /// The register last stored into each home slot: the slot's own
    /// argument register for `va_start`, or any other, `xmm0` for a float
    /// argument parked to be read back as bits.
    pub(super) stored: BTreeMap<usize, Register>,
    /// The lowest slot whose address was taken: on System V, the first
    /// stack word, where `va_start` points the list's stack part.
    pub(super) va_start: Option<usize>,
    /// The places a `lea` took the address of in the frame, in bytes from
    /// the entry stack pointer: the register save area's, which `va_start`
    /// keeps in the list.
    taken: BTreeSet<i64>,
}

impl Homes {
    /// Starts tracking at a function's entry.
    ///
    /// # Arguments
    ///
    /// * `bitness` - 32 or 64.
    /// * `conv` - The callee's convention.
    pub(super) fn new(bitness: u32, conv: &Conv) -> Homes {
        Homes {
            active: bitness == 64 && conv.shadow > 0,
            save_area: bitness == 64 && conv.float_seq,
            saved: BTreeMap::new(),
            saved_vectors: BTreeMap::new(),
            vectors: conv.float_args.to_vec(),
            counts_vectors: false,
            below: 0,
            rax: None,
            rbp: None,
            args: conv.args.to_vec(),
            stored: BTreeMap::new(),
            va_start: None,
            taken: BTreeSet::new(),
        }
    }

    /// Follows one instruction.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `bitness` - 32 or 64.
    ///
    /// # Returns
    ///
    /// What it did with a home slot, if anything.
    pub(super) fn step(&mut self, i: &Instruction, bitness: u32) -> Option<Home> {
        if self.save_area {
            self.save(i, bitness);
        } else if !self.active {
            return None;
        }
        let word = 8i64;
        let base_below = |h: &Homes, r: Register| -> Option<i64> {
            match r.full_register() {
                Register::RSP => Some(h.below),
                Register::RAX => h.rax,
                Register::RBP => h.rbp,
                _ => None,
            }
        };
        let arg_slot = |h: &Homes, i: &Instruction| -> Option<usize> {
            if i.memory_index() != Register::None {
                return None;
            }
            let entry_rel =
                crate::disasm::displacement(i, bitness) - base_below(h, i.memory_base())?;
            let k = (entry_rel - word) / word;
            (entry_rel >= word && (entry_rel - word) % word == 0 && k >= 0)
                .then(|| usize::try_from(k).ok())
                .flatten()
                .filter(|k| *k <= h.args.len())
        };
        let slot_of = |h: &Homes, i: &Instruction| arg_slot(h, i).filter(|k| *k < h.args.len());
        let mut out = None;
        let is_mov = self.active && i.mnemonic() == Mnemonic::Mov;
        let is_store = self.active
            && matches!(
                i.mnemonic(),
                Mnemonic::Mov | Mnemonic::Movss | Mnemonic::Movsd | Mnemonic::Movd | Mnemonic::Movq
            );
        if is_store && i.op0_kind() == OpKind::Memory && i.op1_kind() == OpKind::Register {
            if let Some(k) = slot_of(self, i) {
                let r = i.op1_register().full_register();
                self.stored.insert(k, r);
                if r == self.args[k] {
                    out = Some(Home::Spill);
                }
            }
        } else if is_mov && i.op0_kind() == OpKind::Register && i.op1_kind() == OpKind::Memory {
            if let Some(k) = slot_of(self, i) {
                out = Some(Home::Load(
                    self.stored.get(&k).copied().unwrap_or(self.args[k]),
                ));
            }
        } else if (self.active || self.save_area)
            && i.mnemonic() == Mnemonic::Lea
            && i.op0_kind() == OpKind::Register
            && let Some(k) = arg_slot(self, i)
        {
            self.va_start = Some(self.va_start.map_or(k, |v| v.min(k)));
            out = Some(Home::VaStart);
        }
        let signed_imm = |i: &Instruction| match i.op1_kind() {
            OpKind::Immediate32 => i64::from(i.immediate32().cast_signed()),
            OpKind::Immediate16 => i64::from(i.immediate16().cast_signed()),
            _ => i.immediate(1).cast_signed(),
        };
        match i.mnemonic() {
            Mnemonic::Push => self.below += word,
            Mnemonic::Pop => self.below -= word,
            Mnemonic::Sub
                if i.op0_register().full_register() == Register::RSP && is_imm(i.op1_kind()) =>
            {
                self.below += signed_imm(i);
            }
            Mnemonic::Add
                if i.op0_register().full_register() == Register::RSP && is_imm(i.op1_kind()) =>
            {
                self.below -= signed_imm(i);
            }
            _ => {}
        }
        let sets = |i: &Instruction, r: Register| {
            i.op0_kind() == OpKind::Register && i.op0_register().full_register() == r
        };
        let (below, rax, rbp) = (self.below, self.rax, self.rbp);
        let alias_of = |i: &Instruction| -> Option<i64> {
            match (i.mnemonic(), i.op1_kind()) {
                (Mnemonic::Mov, OpKind::Register) => {
                    base_below_of(below, rax, rbp, i.op1_register())
                }
                (Mnemonic::Lea, OpKind::Memory) if i.memory_index() == Register::None => {
                    base_below_of(below, rax, rbp, i.memory_base())
                        .map(|b| b - crate::disasm::displacement(i, bitness))
                }
                _ => None,
            }
        };
        if sets(i, Register::RAX) {
            self.rax = alias_of(i);
        }
        if sets(i, Register::RBP) {
            self.rbp = alias_of(i);
        }
        out
    }

    /// The fixed argument count when the function is variadic: it took the
    /// address of the first variable argument (`va_start`) and stored
    /// every argument register from there on home, so the list continues
    /// in memory; with every register argument fixed, the address is the
    /// first stack argument's and the last register is homed beside it. A
    /// function that only parks its parameters home, for their addresses
    /// or a debug build's habit, takes no address past them and is not
    /// variadic.
    ///
    /// On System V the save area says it ([`Homes::save_area_fixed`]).
    pub(super) fn fixed(&self) -> Option<usize> {
        if self.save_area {
            return self.save_area_fixed();
        }
        let first = self.va_start?;
        let own = |k: usize| self.stored.get(&k) == self.args.get(k);
        let last = self.args.len().checked_sub(1)?;
        ((first..self.args.len()).all(own) && (first <= last || own(last))).then_some(first)
    }

    /// Notes a store of an argument register into what may be the System V
    /// register save area, and the `test al, al` that guards its vector
    /// half.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `bitness` - 32 or 64.
    fn save(&mut self, i: &Instruction, bitness: u32) {
        if i.mnemonic() == Mnemonic::Test
            && i.op0_kind() == OpKind::Register
            && i.op1_kind() == OpKind::Register
            && i.op0_register() == Register::AL
            && i.op1_register() == Register::AL
        {
            self.counts_vectors = true;
            return;
        }
        if i.mnemonic() == Mnemonic::Lea
            && i.memory_index() == Register::None
            && let Some(base) = base_below_of(self.below, self.rax, self.rbp, i.memory_base())
        {
            self.taken
                .insert(crate::disasm::displacement(i, bitness) - base);
            return;
        }
        if i.op0_kind() != OpKind::Memory
            || i.op1_kind() != OpKind::Register
            || i.memory_index() != Register::None
        {
            return;
        }
        let Some(base) = base_below_of(self.below, self.rax, self.rbp, i.memory_base()) else {
            return;
        };
        let at = crate::disasm::displacement(i, bitness) - base;
        let r = i.op1_register();
        let (bank, found) = match i.mnemonic() {
            Mnemonic::Mov => (&mut self.saved, self.args.iter().position(|a| *a == r)),
            Mnemonic::Movaps
            | Mnemonic::Movups
            | Mnemonic::Movdqa
            | Mnemonic::Movdqu
            | Mnemonic::Vmovaps
            | Mnemonic::Vmovups => (
                &mut self.saved_vectors,
                self.vectors.iter().position(|v| *v == r),
            ),
            _ => return,
        };
        if let Some(k) = found {
            bank.entry(k).or_insert(at);
        }
    }

    /// The fixed argument count a System V register save area shows.
    ///
    /// The integer registers from the first variable one through `r9` are
    /// stored eight bytes apart in register order, the last two at least,
    /// and the vector half is there too: `al` was tested for it, or a
    /// vector register was stored where the area puts it, past the integer
    /// ones, or the address of the list's stack part was taken for
    /// `va_start`: GCC leaves the vector half out when every variable
    /// argument is an integer (gnulib's `rpl_fcntl`). With all six
    /// integer registers fixed the area holds the vector half alone:
    /// `xmm0` to `xmm7` sixteen bytes apart behind `test al, al`, the
    /// caller's count of them, which no parameter is (openssh's `sshlog`).
    /// A function whose `va_start` follows a branch may save only the
    /// registers its `va_arg` reads, short of `r9`: then the run at the
    /// address `va_start` takes for the list's register part, with the
    /// address of its stack part taken too, says where the list starts.
    /// A function that spills its own parameters for a debug build
    /// stores them in no such run and tests no `al`.
    fn save_area_fixed(&self) -> Option<usize> {
        /// Bytes of one vector register's place in the save area.
        const VECTOR: i64 = 16;
        let step = |n: usize, size: i64| i64::try_from(n).ok().map(|n| n * size);
        let last = self.args.len().checked_sub(1)?;
        let vector_at =
            |base: i64, j: usize, o: i64| step(j, VECTOR).is_some_and(|s| o == base + s);
        let Some(r9) = self.saved.get(&last) else {
            let partial = self.taken.iter().find_map(|&area| {
                let run: Vec<usize> = self
                    .saved
                    .iter()
                    .filter(|&(k, o)| step(*k, GPR).is_some_and(|s| *o == area + s))
                    .map(|(k, _)| *k)
                    .collect();
                let (first, end) = (*run.first()?, *run.last()?);
                (run.len() == end - first + 1).then_some(first)
            });
            if let Some(first) = partial.filter(|_| self.va_start.is_some()) {
                return Some(first);
            }
            let base = *self.saved_vectors.get(&0)?;
            let whole = (0..self.vectors.len()).all(|j| {
                self.saved_vectors
                    .get(&j)
                    .is_some_and(|o| vector_at(base, j, *o))
            });
            return (self.counts_vectors && whole).then_some(self.args.len());
        };
        let area = r9 - step(last, GPR)?;
        let at = |k: usize| step(k, GPR).is_some_and(|o| self.saved.get(&k) == Some(&(area + o)));
        let first = (0..=last).rev().take_while(|k| at(*k)).last()?;
        let vectors = step(self.args.len(), GPR)? + area;
        (first < last
            && (self.counts_vectors
                || self.va_start.is_some()
                || self
                    .saved_vectors
                    .iter()
                    .any(|(j, o)| vector_at(vectors, *j, *o))))
        .then_some(first)
    }
}

/// Bytes below the entry stack pointer that a base register stands for.
///
/// # Arguments
///
/// * `below` - Where the stack pointer stands.
/// * `rax` - What `rax` aliases, if the stack pointer.
/// * `rbp` - What `rbp` aliases, if the stack pointer.
/// * `r` - The register asked about.
pub(super) fn base_below_of(
    below: i64,
    rax: Option<i64>,
    rbp: Option<i64>,
    r: Register,
) -> Option<i64> {
    match r.full_register() {
        Register::RSP => Some(below),
        Register::RAX => rax,
        Register::RBP => rbp,
        _ => None,
    }
}

/// Returns the fixed argument count of a variadic function whose `va_start` follows its first call.
///
/// A prologue scan that stops at the call misses it: gnulib's
/// `open_safer` saves only `rdx`, and takes the list's addresses in the
/// branch that reads the mode, past `call open`.
///
/// The function's first instructions are read in address order on
/// through its calls, each block after the entry's starting where the
/// entry left the stack pointer, and the full shape is asked for: the
/// stores into the save area ([`Homes::fixed`]) and both addresses
/// `va_start` takes, of the list's stack part and of the area's start. A
/// lone store or a lone `lea` past a call proves nothing, and neither does
/// a `test al, al` there, which tests some byte rather than the caller's
/// count of vector arguments: openssh's `process_server_config_line_depth`
/// spills `rdx` to `r9` in order for want of registers and tests a
/// character. Nothing is read unless the scan before the call saw an
/// argument register stored in the frame.
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the decoder.
/// * `conv` - The convention whose argument registers are looked for.
/// * `t` - The function's entry.
/// * `early` - What the scan before the first call saw.
///
/// # Returns
///
/// The fixed count, or `None` when the function shows no such list.
pub(super) fn late_fixed(ctx: &Ctx<'_>, conv: &Conv, t: u64, early: &Homes) -> Option<usize> {
    /// Most instructions read from the entry, as the scan before the call reads.
    const INSTRS_MAX: usize = 64;
    if !early.save_area || early.saved.is_empty() {
        return None;
    }
    let f = ctx.analysis.function(t)?;
    let mut homes = Homes::new(ctx.bitness, conv);
    let mut frame = None;
    let mut seen = 0usize;
    for b in &f.blocks {
        homes.below = frame.unwrap_or(homes.below);
        let mut va = b.start;
        while va < b.end && seen < INSTRS_MAX {
            let i = ctx.decode(va)?;
            homes.step(&i, ctx.bitness);
            seen += 1;
            va = i.next_ip();
        }
        frame = frame.or(Some(homes.below));
    }
    let first = homes.fixed()?;
    let area = homes.saved.get(&first)? - i64::try_from(first).ok()? * GPR;
    (homes.va_start.is_some() && homes.taken.contains(&area)).then_some(first)
}
