//! x87 and vector instructions: the floating-point stack, float writes and
//! masks.

use super::*;

/// Bytes of an x87 extended-precision value in memory (`tword`).
const EXTENDED_BYTES: u64 = 10;

impl<'a> Exec<'_, 'a> {
    /// Records the scalar float type a vector register holds after `instr`.
    ///
    /// The first type seen becomes the register's declaration type.
    ///
    /// # Arguments
    ///
    /// * `instr` - An instruction whose operand 0 may be a vector register.
    /// * `ty` - [`Ty::F32`] or [`Ty::F64`].
    pub(super) fn note_reg_ty(&mut self, instr: &Instruction, ty: Ty) {
        if instr.op0_kind() == OpKind::Register && instr.op0_register().is_vector_register() {
            let key = self.canon(instr.op0_register());
            self.ctx.reg_ty.entry(key).or_insert(ty);
        }
    }

    /// Sets the scalar type a vector register holds, replacing one already noted.
    ///
    /// A sign or magnitude mask leaves integer bits, not the float the
    /// register held before the mask. The first type would declare that
    /// float and a later store would convert the bits.
    ///
    /// # Arguments
    ///
    /// * `instr` - An instruction whose operand 0 may be a vector register.
    /// * `ty` - The type the result has, [`Ty::U64`] for a mask's bits.
    pub(super) fn stamp_reg_ty(&mut self, instr: &Instruction, ty: Ty) {
        if instr.op0_kind() == OpKind::Register && instr.op0_register().is_vector_register() {
            let key = self.canon(instr.op0_register());
            self.ctx.reg_ty.insert(key, ty);
        }
    }

    /// Writes a scalar float result to operand 0 and types the destination register.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `v` - The value.
    /// * `ty` - Its type.
    pub(super) fn float_write(&mut self, instr: &Instruction, v: Expr, ty: Ty) {
        self.note_reg_ty(instr, ty);
        self.write_op0(instr, v);
    }

    /// Writes a scalar float, keeping bit 63 when `upper` still has it.
    ///
    /// A scalar single replaces the low lane and leaves the bits above it.
    /// A broadcast sign mask set bit 63 of a zero-extended single, so the
    /// result keeps that bit. Any other value whose bits above the lane
    /// this function did not clear, including a double, keeps bits 63:32
    /// beside the new lane. The wrapped value is integer bits: a 32-bit
    /// store is the new lane, and a 64-bit store still has the half above
    /// it. A double lane is the whole low qword, so this does not wrap it.
    ///
    /// # Arguments
    ///
    /// * `instr` - The scalar instruction.
    /// * `low` - The low lane it computed.
    /// * `ty` - That lane's type.
    /// * `upper` - The register whose bits above the lane survive. The
    ///   destination for a legacy opcode, the first source for AVX.
    pub(super) fn write_scalar_lane(
        &mut self,
        instr: &Instruction,
        low: Expr,
        ty: Ty,
        upper: &Expr,
    ) {
        if ty == Ty::F32 && !lane_zeros_above(upper) {
            self.stamp_reg_ty(instr, Ty::U64);
            let kept = if sign_above_low(upper).is_some() {
                with_sign_above(low)
            } else if let Some((high, _)) = merged_parts(upper) {
                merge_low_lane(high.clone(), low)
            } else {
                merge_low_lane(upper.clone(), low)
            };
            self.write_op0(instr, kept);
            return;
        }
        self.float_write(instr, low, ty);
    }

    /// Lifts an x87 instruction against a modelled register stack.
    ///
    /// The eight registers are held as `st0` to `st7`, a load pushes the
    /// others down, a store with `p` pops them back up, and arithmetic
    /// rewrites `st0` or the register named. A single is widened first, so
    /// `fld dword [a]; fmul dword [a+4]; fstp dword [a+8]` is
    /// `(double)*(float*)a * (double)*(float*)(a + 4)` stored as a float:
    /// the product is the double one, and the single store rounds it once.
    /// A store that pops pops before it writes: the
    /// value leaves the stack with the instruction, so it is stored, never
    /// first written out to the register it leaves. Integer loads and
    /// stores carry the casts. `fxch` swaps `st0` with its last operand:
    /// the decoder lists `st0` first, bare `fxch` as `st0, st1` included. A
    /// compare that writes the flags (`fcomi`) sets them as `comisd` does
    /// and `fcmovcc` selects on them; one that writes the status word
    /// (`fcom`, `fcompp`) is remembered for the `fnstsw ax; sahf` that moves
    /// it into the flags, and the stack is kept right either way. `frndint`
    /// is `rint`, which rounds to nearest, ties to even, as the default
    /// control word says. `fist` and `fistp` store a cast of that rounding;
    /// `fisttp` truncates toward zero. A value the width cannot hold is the
    /// indefinite integer, the most negative value of that width. `fsincos` leaves
    /// the sine in place and pushes the cosine, `fptan` the tangent and a
    /// `1.0`, as both do for any operand below 2^63, the one they take. A
    /// control-word instruction or another transcendental one is left to
    /// the general path. A ten-byte extended value has no C type here, so its load and
    /// store are the calls `x87_load80(p)` and `x87_store80(p, v)`, never a
    /// `double` that would drop two of its bytes.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    ///
    /// # Returns
    ///
    /// Whether the instruction was an x87 one this method handled.
    pub(super) fn x87(&mut self, instr: &Instruction) -> bool {
        use Mnemonic as M;
        let mn = instr.mnemonic();
        let reg_of = |instr: &Instruction, op: u32| st_depth(instr.op_register(op));
        let extended = instr.op_count() > 0
            && instr.op0_kind() == OpKind::Memory
            && instr.memory_size() == MemorySize::Float80;
        self.entered_loaded(instr);
        match mn {
            M::Fld if extended => {
                let addr = self.addr(instr, 0);
                self.settle_frame_region(&addr, Some(&Expr::Const(EXTENDED_BYTES)), false, false);
                self.push_st(Expr::Call("x87_load80".to_owned(), vec![addr]));
                let st0 = Key::Reg(st_register(0));
                self.materialize(st0, &mut Vec::new(), None);
            }
            M::Fstp if extended => {
                let mut addr = self.addr(instr, 0);
                let mut v = self.st(0);
                self.pop_st();
                self.settle_frame_region(&addr, Some(&Expr::Const(EXTENDED_BYTES)), false, true);
                let word = self.word_ty();
                self.protect_memory_around(&mut [(&mut addr, word), (&mut v, Ty::F64)]);
                if let Some(p) = &mut self.ctx.probe {
                    p.asm();
                }
                let n = self.names();
                emit_line!(
                    self,
                    format!("x87_store80({}, {});", addr.render(&n), v.render(&n))
                );
                self.record(EffectKind::Unmodeled);
            }
            M::Fld => {
                let v = self.x87_operand(instr, 0, false);
                self.push_st(v);
            }
            M::Fld1 => self.push_st(Expr::FConst(1.0f64.to_bits(), Ty::F64)),
            M::Fldz => self.push_st(Expr::FConst(0, Ty::F64)),
            M::Fldpi => self.push_st(Expr::FConst(std::f64::consts::PI.to_bits(), Ty::F64)),
            M::Fild => {
                let v = self.x87_operand(instr, 0, true);
                self.push_st(v);
            }
            M::Fst | M::Fstp if instr.op0_kind() == OpKind::Memory => {
                let v = self.st(0);
                let v = if Self::mem_ty(instr) == Ty::F32 {
                    self.single(instr, v)
                } else {
                    v
                };
                if mn == M::Fstp {
                    self.pop_st();
                }
                self.store(instr, v);
            }
            M::Fst | M::Fstp => {
                let v = self.st(0);
                if let Some(i) = reg_of(instr, 0) {
                    self.set_st(i, v);
                }
                if mn == M::Fstp {
                    self.pop_st();
                }
            }
            M::Fist | M::Fistp | M::Fisttp if instr.op0_kind() == OpKind::Memory => {
                let st = self.st(0);
                let ty = Self::mem_ty(instr);
                let v = if mn == M::Fisttp {
                    Expr::Cast(Box::new(st), ty)
                } else {
                    Expr::Cast(Box::new(Expr::Call("rint".to_owned(), vec![st])), ty)
                };
                if mn != M::Fist {
                    self.pop_st();
                }
                self.store(instr, v);
            }
            M::Fadd
            | M::Fsub
            | M::Fsubr
            | M::Fmul
            | M::Fdiv
            | M::Fdivr
            | M::Faddp
            | M::Fsubp
            | M::Fsubrp
            | M::Fmulp
            | M::Fdivp
            | M::Fdivrp
            | M::Fiadd
            | M::Fisub
            | M::Fisubr
            | M::Fimul
            | M::Fidiv
            | M::Fidivr => {
                let op = match mn {
                    M::Fadd | M::Faddp | M::Fiadd => Op::FAdd,
                    M::Fmul | M::Fmulp | M::Fimul => Op::FMul,
                    M::Fdiv | M::Fdivr | M::Fdivp | M::Fdivrp | M::Fidiv | M::Fidivr => Op::FDiv,
                    _ => Op::FSub,
                };
                let reversed = matches!(
                    mn,
                    M::Fsubr | M::Fsubrp | M::Fdivr | M::Fdivrp | M::Fisubr | M::Fidivr
                );
                let integer = matches!(
                    mn,
                    M::Fiadd | M::Fisub | M::Fisubr | M::Fimul | M::Fidiv | M::Fidivr
                );
                let pops = matches!(
                    mn,
                    M::Faddp | M::Fsubp | M::Fsubrp | M::Fmulp | M::Fdivp | M::Fdivrp
                );
                let (dest, src) = if instr.op_count() == 0 {
                    (1, self.st(0))
                } else if instr.op0_kind() == OpKind::Memory {
                    (0, self.x87_operand(instr, 0, integer))
                } else {
                    let Some(d) = reg_of(instr, 0) else {
                        return false;
                    };
                    let s = if instr.op_count() > 1 {
                        reg_of(instr, 1).map_or(Expr::Var(Key::Reg(Register::ST0)), |i| self.st(i))
                    } else {
                        self.st(0)
                    };
                    (d, s)
                };
                let d = Self::widened(self.st(dest));
                let src = Self::widened(src);
                let v = if reversed {
                    fold(op, src, d, 64)
                } else {
                    fold(op, d, src, 64)
                };
                self.set_st(dest, v);
                if pops {
                    self.pop_st();
                }
            }
            M::Fchs => {
                let v = Expr::Un(UnOp::Neg, Box::new(self.st(0)));
                self.set_st(0, v);
            }
            M::Fabs => {
                let v = Expr::Call("fabs".to_owned(), vec![self.st(0)]);
                self.set_st(0, v);
            }
            M::Fsqrt => {
                let v = Expr::Un(UnOp::Sqrt, Box::new(Self::widened(self.st(0))));
                self.set_st(0, v);
            }
            M::Frndint => {
                let v = Expr::Call("rint".to_owned(), vec![self.st(0)]);
                self.set_st(0, v);
            }
            M::Fsincos | M::Fptan => {
                let x = self.st(0);
                let (below, top) = if mn == M::Fsincos {
                    (
                        Expr::Call("sin".to_owned(), vec![x.clone()]),
                        Expr::Call("cos".to_owned(), vec![x]),
                    )
                } else {
                    (
                        Expr::Call("tan".to_owned(), vec![x]),
                        Expr::FConst(1.0f64.to_bits(), Ty::F64),
                    )
                };
                self.set_st(0, below);
                self.push_st(top);
            }
            M::Fxch => {
                let i = match instr.op_count() {
                    0 => Some(1),
                    n => reg_of(instr, n - 1),
                };
                let Some(i) = i else {
                    return false;
                };
                let (a, b) = (self.st(0), self.st(i));
                self.set_st(0, b);
                self.set_st(i, a);
            }
            M::Fcom
            | M::Fcomp
            | M::Fcompp
            | M::Fucom
            | M::Fucomp
            | M::Fucompp
            | M::Ficom
            | M::Ficomp
            | M::Fcomi
            | M::Fcomip
            | M::Fucomi
            | M::Fucomip => {
                let integer = matches!(mn, M::Ficom | M::Ficomp);
                let src = if instr.op_count() == 0 {
                    self.st(1)
                } else if instr.op0_kind() == OpKind::Memory {
                    self.x87_operand(instr, 0, integer)
                } else {
                    let last = instr.op_count() - 1;
                    reg_of(instr, last).map_or_else(|| self.st(1), |i| self.st(i))
                };
                let st0 = self.st(0);
                if matches!(mn, M::Fcomi | M::Fcomip | M::Fucomi | M::Fucomip) {
                    self.flags = Flags::Cmp(st0, src, 64);
                } else {
                    self.env.fpu_cmp = Some((st0, src));
                }
                let pops = match mn {
                    M::Fcompp | M::Fucompp => 2,
                    M::Fcomp | M::Fucomp | M::Ficomp | M::Fcomip | M::Fucomip => 1,
                    _ => 0,
                };
                for _ in 0..pops {
                    self.pop_st();
                }
            }
            M::Fcmovb
            | M::Fcmove
            | M::Fcmovbe
            | M::Fcmovu
            | M::Fcmovnb
            | M::Fcmovne
            | M::Fcmovnbe
            | M::Fcmovnu => {
                if self.flags == Flags::Unknown {
                    return false;
                }
                let Some(i) = reg_of(instr, instr.op_count() - 1) else {
                    return false;
                };
                let cc = match mn {
                    M::Fcmovb => ConditionCode::b,
                    M::Fcmove => ConditionCode::e,
                    M::Fcmovbe => ConditionCode::be,
                    M::Fcmovu => ConditionCode::p,
                    M::Fcmovnb => ConditionCode::ae,
                    M::Fcmovne => ConditionCode::ne,
                    M::Fcmovnbe => ConditionCode::a,
                    _ => ConditionCode::np,
                };
                let cond = Cond {
                    cc: Cc(cc),
                    flags: self.flags.clone(),
                };
                let (taken, kept) = (self.st(i), self.st(0));
                let v = crate::analysis::decompile::expr::ternary(cond, taken, kept);
                self.set_st(0, v);
            }
            _ => return false,
        }
        true
    }

    /// The value `fst dword [m]` stores: the register rounded to single
    /// precision.
    ///
    /// A constant is rounded here, so a slot that holds it holds the
    /// single's bits (a `movsd` copying the slot as a dword copies
    /// `0x3f800000` for 1.0, not the low half of the double); any other
    /// value bound for a slot carries the conversion as a cast. A store
    /// through a pointer prints as an assignment to a `float`, which C
    /// rounds the same way.
    ///
    /// # Arguments
    ///
    /// * `instr` - The store, whose operand 0 is a dword in memory.
    /// * `v` - The register's value.
    pub(super) fn single(&self, instr: &Instruction, v: Expr) -> Expr {
        match v {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "rounding to single precision is what the store does"
            )]
            Expr::FConst(bits, Ty::F64) => {
                Expr::FConst(u64::from((f64::from_bits(bits) as f32).to_bits()), Ty::F32)
            }
            Expr::FConst(..) => v,
            other if matches!(self.addr(instr, 0), Expr::Sp(_)) => {
                Expr::Cast(Box::new(other), Ty::F32)
            }
            other => other,
        }
    }

    /// Reads an x87 instruction's operand: a stack register or a memory
    /// operand, an integer one sign-extended and cast to `double`.
    ///
    /// `fild` and the `fi` arithmetic read a signed integer. An unsigned
    /// cast of `0xffffffff` is not `-1.0`. A writable single is not left as
    /// the named global: that name carries no lane, so two of them would
    /// multiply at single precision. It is the `float` at that address,
    /// which an operation then widens.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `op` - The operand.
    /// * `integer` - The memory operand holds an integer the instruction converts.
    pub(super) fn x87_operand(&mut self, instr: &Instruction, op: u32, integer: bool) -> Expr {
        if instr.op_kind(op) == OpKind::Register {
            let i = st_depth(instr.op_register(op)).unwrap_or(0);
            return self.st(i);
        }
        let v = self.mem_read(instr, op);
        if integer {
            let bits = Self::mem_ty(instr).bits();
            return Expr::Cast(Box::new(sign_extend(v, bits)), Ty::F64);
        }
        if let Expr::Var(Key::Global(addr, _)) = v
            && Self::mem_ty(instr) == Ty::F32
            && self.ctx.program.section_at(addr).is_some()
        {
            return Expr::deref(Expr::Const(addr), Ty::F32);
        }
        v
    }

    /// A single widened to the precision an x87 operation uses.
    ///
    /// The stack holds a double. Multiplying two singles at single
    /// precision, then keeping the product as a double, is a different
    /// number. A later store to a single rounds this result once.
    ///
    /// # Arguments
    ///
    /// * `v` - The operand.
    fn widened(v: Expr) -> Expr {
        if float_lane(&v) == Some(32) {
            Expr::Cast(Box::new(v), Ty::F64)
        } else {
            v
        }
    }

    /// The value in x87 register `st(i)`, or the register itself when
    /// nothing was loaded there.
    ///
    /// # Arguments
    ///
    /// * `i` - The register's depth from the top.
    pub(super) fn st(&self, i: usize) -> Expr {
        let k = Key::Reg(st_register(i));
        self.env.vals.get(&k).cloned().unwrap_or(Expr::Var(k))
    }

    /// Sets x87 register `st(i)`.
    ///
    /// # Arguments
    ///
    /// * `i` - The register's depth from the top.
    /// * `v` - The value.
    pub(super) fn set_st(&mut self, i: usize, v: Expr) {
        let key = Key::Reg(st_register(i));
        self.written_here.insert(key);
        self.env.set(key, v);
    }

    /// Marks every x87 register the entry block has not loaded as empty.
    ///
    /// A function is entered with the x87 stack empty (both conventions
    /// require it at a call), so in the entry block a register no x87
    /// instruction of the block wrote, and holding no value, holds nothing
    /// ([`Env::unset`]). Run before each instruction of the entry block, so
    /// the block's successors inherit the empty registers it left alone.
    pub(super) fn empty_x87_at_entry(&mut self) {
        for i in 0..8 {
            let key = Key::Reg(st_register(i));
            if !self.written_here.contains(&key) && !self.env.vals.contains_key(&key) {
                self.env.unset.insert(key);
            }
        }
    }

    /// Forgets which x87 registers are empty.
    ///
    /// An instruction without a model that moves the stack's top
    /// (`fpatan`, `fninit`) leaves the positions where
    /// the model cannot follow; each one then reads as its own text
    /// variable, as a register of unknown content does.
    pub(super) fn forget_empty_x87(&mut self) {
        for i in 0..8 {
            self.env.unset.remove(&Key::Reg(st_register(i)));
        }
    }

    /// Loads the x87 registers an instruction of the entry block reads
    /// while they count as empty, and every register above them.
    ///
    /// Such a function was entered with values on the stack (`_ftol` takes
    /// its operand in `st0`, `_CIpow` two), not with the empty stack a call
    /// leaves; the registers below the deepest one read stay empty.
    ///
    /// # Arguments
    ///
    /// * `instr` - The x87 instruction about to run.
    fn entered_loaded(&mut self, instr: &Instruction) {
        if !self.entry {
            return;
        }
        let Some(deepest) = self
            .info
            .info(instr)
            .used_registers()
            .iter()
            .filter(|u| {
                matches!(
                    u.access(),
                    OpAccess::Read
                        | OpAccess::CondRead
                        | OpAccess::ReadWrite
                        | OpAccess::ReadCondWrite
                ) && self.env.unset.contains(&Key::Reg(u.register()))
            })
            .filter_map(|u| st_depth(u.register()))
            .max()
        else {
            return;
        };
        for i in 0..=deepest {
            let key = Key::Reg(st_register(i));
            self.written_here.insert(key);
            self.env.unset.remove(&key);
        }
    }

    /// What x87 register `st(i)` holds for a push or pop to move, `None`
    /// when it is empty.
    ///
    /// # Arguments
    ///
    /// * `i` - The register's depth from the top.
    fn st_held(&self, i: usize) -> Option<Expr> {
        let key = Key::Reg(st_register(i));
        (!self.env.unset.contains(&key)).then(|| self.st(i))
    }

    /// Pushes a value onto the x87 stack: every register moves one down.
    ///
    /// The registers are positional text variables, so a register with no
    /// pending value moves as its text variable: after a push `st1` holds
    /// what the text's `st0` holds, never the text's own `st1`. An empty
    /// register moves as empty, so a push never makes a deeper register
    /// read a text variable no instruction wrote.
    ///
    /// # Arguments
    ///
    /// * `v` - The new `st0`.
    pub(super) fn push_st(&mut self, v: Expr) {
        for i in (0..7).rev() {
            let moved = self.st_held(i);
            self.move_st(i + 1, moved);
        }
        self.set_st(0, v);
    }

    /// Pops the x87 stack: every register moves one up, and the bottom one
    /// is empty.
    pub(super) fn pop_st(&mut self) {
        for i in 0..7 {
            let moved = self.st_held(i + 1);
            self.move_st(i, moved);
        }
        self.move_st(7, None);
    }

    /// Sets `st(i)` to what a push or pop moves into it: nothing pending
    /// when it is the register's own text variable, and empty
    /// ([`Env::unset`]) when the register it came from was.
    ///
    /// # Arguments
    ///
    /// * `i` - The register's depth from the top.
    /// * `v` - The value moved in, `None` for an empty register.
    fn move_st(&mut self, i: usize, v: Option<Expr>) {
        let key = Key::Reg(st_register(i));
        self.written_here.insert(key);
        match v {
            None => {
                self.env.vals.remove(&key);
                self.env.unset.insert(key);
            }
            Some(v) if v == Expr::Var(key) => {
                self.env.vals.remove(&key);
                self.env.unset.remove(&key);
            }
            Some(v) => self.env.set(key, v),
        }
    }

    /// Recognizes the sign and magnitude masks scalar float code applies with
    /// `xorps`/`andps` on a constant.
    ///
    /// # Arguments
    ///
    /// * `instr` - A two-operand `xorps`, `xorpd`, `andps` or `andpd` with a memory source.
    ///
    /// # Returns
    ///
    /// `(absolute, ty, broadcast)`. `absolute` is the magnitude mask
    /// (`0x7fff...`); a sign mask (`0x8000...`) is `false`. `ty` follows the
    /// lane width. `broadcast` is `Some(true)` when every later lane repeats
    /// the mask, `Some(false)` when every later lane is zero, and `None` when
    /// the lanes mix the two. A mixed mask still negates or clears lane zero;
    /// the bits above it are not one shape. `None` for the whole option is any
    /// other constant or a non-constant address.
    pub(super) fn float_mask(&self, instr: &Instruction) -> Option<(bool, Ty, Option<bool>)> {
        let Expr::Const(a) = self.addr(instr, 1) else {
            return None;
        };
        let bytes = self.ctx.program.read_va(a, 16)?;
        let lanes32: Vec<u32> = bytes
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
            .collect();
        let lanes64: Vec<u64> = bytes
            .chunks_exact(8)
            .map(|c| u64::from_le_bytes([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]))
            .collect();
        let fill = |same: bool, zero: bool| {
            if same {
                Some(true)
            } else if zero {
                Some(false)
            } else {
                None
            }
        };
        let later32 = |m: u32| {
            let rest = &lanes32[1..];
            lanes32[0] == m && rest.iter().all(|l| *l == m || *l == 0)
        };
        let later64 = |m: u64| {
            let rest = &lanes64[1..];
            lanes64[0] == m && rest.iter().all(|l| *l == m || *l == 0)
        };
        let xor = matches!(instr.mnemonic(), Mnemonic::Xorps | Mnemonic::Xorpd);
        if later32(0x8000_0000) && xor {
            let rest = &lanes32[1..];
            let kind = fill(
                rest.iter().all(|l| *l == 0x8000_0000),
                rest.iter().all(|l| *l == 0),
            );
            return Some((false, Ty::F32, kind));
        }
        if later32(0x7fff_ffff) && !xor {
            let rest = &lanes32[1..];
            let kind = fill(
                rest.iter().all(|l| *l == 0x7fff_ffff),
                rest.iter().all(|l| *l == 0),
            );
            return Some((true, Ty::F32, kind));
        }
        if later64(0x8000_0000_0000_0000) && xor {
            let rest = &lanes64[1..];
            let kind = fill(
                rest.iter().all(|l| *l == 0x8000_0000_0000_0000),
                rest.iter().all(|l| *l == 0),
            );
            return Some((false, Ty::F64, kind));
        }
        if later64(0x7fff_ffff_ffff_ffff) && !xor {
            let rest = &lanes64[1..];
            let kind = fill(
                rest.iter().all(|l| *l == 0x7fff_ffff_ffff_ffff),
                rest.iter().all(|l| *l == 0),
            );
            return Some((true, Ty::F64, kind));
        }
        None
    }

    /// Tells whether an otherwise unmodeled instruction is a vector operation
    /// that can be lifted as an intrinsic call.
    ///
    /// The destination must be a register, some operand a vector register,
    /// no flags may change, no memory may be written, and the instruction
    /// must not be a conditional form.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    pub(super) fn is_vector_op(&mut self, instr: &Instruction) -> bool {
        if instr.op_count() < 2
            || instr.op0_kind() != OpKind::Register
            || instr.rflags_modified() != 0
            || instr.condition_code() != ConditionCode::None
        {
            return false;
        }
        let any_vector = (0..instr.op_count()).any(|i| {
            instr.op_kind(i) == OpKind::Register && instr.op_register(i).is_vector_register()
        });
        if !any_vector {
            return false;
        }
        let info = self.info.info(instr);
        !info.used_memory().iter().any(|m| {
            matches!(
                m.access(),
                OpAccess::Write
                    | OpAccess::CondWrite
                    | OpAccess::ReadWrite
                    | OpAccess::ReadCondWrite
            )
        })
    }

    /// Lifts a vector instruction as `dst = mnemonic(sources...)`.
    ///
    /// The destination is a source too when the instruction reads it
    /// (two-operand SSE forms); AVX three-operand forms list their sources only.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction ([`Exec::is_vector_op`] holds).
    pub(super) fn vector_op(&mut self, instr: &Instruction) {
        let reads_dst = matches!(
            self.info.info(instr).op0_access(),
            OpAccess::Read | OpAccess::CondRead | OpAccess::ReadWrite | OpAccess::ReadCondWrite
        );
        let first = if reads_dst { 0 } else { 1 };
        let args: Vec<Expr> = (first..instr.op_count())
            .map(|i| self.val(instr, i))
            .collect();
        let name = format!("{:?}", instr.mnemonic()).to_lowercase();
        self.write_op0(instr, Expr::Call(name, args));
    }

    /// Writes `v` to operand 0, a register or memory destination.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `v` - The value.
    pub(super) fn write_op0(&mut self, instr: &Instruction, v: Expr) {
        match instr.op0_kind() {
            OpKind::Register => self.reg_write(instr.op0_register(), v),
            OpKind::Memory => self.store(instr, v),
            _ => self.unmodeled(instr),
        }
    }
}
