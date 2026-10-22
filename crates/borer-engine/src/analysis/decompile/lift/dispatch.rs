//! Calls that go through a dispatch thunk or a read-only pointer: where
//! they lead, and the register they jump through.

use super::*;

impl Ctx<'_> {
    /// The register a call reads as its target when it goes into a
    /// dispatch thunk ([`Ctx::dispatch`]): the CFG dispatcher's `jmp rax`
    /// makes `call __guard_dispatch_icall_fptr` a call through `rax`.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    pub(super) fn jumps_through(&self, instr: &Instruction) -> Option<(Key, u8)> {
        match self.dispatch(instr)? {
            Dispatch::Through(r) => Some((Key::Reg(canon(r, self.bitness)), 64)),
            Dispatch::Nothing(_) => None,
        }
    }

    /// Follows a call into a dispatch thunk or through a read-only pointer.
    ///
    /// Up to four hops are followed from the call's target: a direct jump,
    /// or a jump through a pointer that read-only data holds (an import
    /// slot is the import's, and ends the walk). A jump through a register
    /// ends it as a dispatch through that register; a `ret` that pops
    /// nothing ends it as a call that does nothing, but only behind a
    /// pointer: a direct call to a function that only returns is left to
    /// [`Exec::returns_at_once`], which keeps a named one.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call: a direct one, or one through a memory operand
    ///   naming the pointer outright.
    ///
    /// # Returns
    ///
    /// Where the call goes, or `None` when it is no dispatch.
    pub(super) fn dispatch(&self, instr: &Instruction) -> Option<Dispatch> {
        /// Most jumps and pointers followed from the call's target.
        const HOPS: usize = 4;
        let (mut at, behind_pointer) = match instr.op0_kind() {
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
                (instr.near_branch_target(), false)
            }
            OpKind::Memory => (self.read_only_pointer(Exec::import_slot(instr)?)?, true),
            _ => return None,
        };
        for _ in 0..HOPS {
            let i = self.decode(at)?;
            match (i.flow_control(), i.op0_kind()) {
                (FlowControl::Return, _)
                    if behind_pointer && (i.op_count() == 0 || i.immediate16() == 0) =>
                {
                    return Some(Dispatch::Nothing(at));
                }
                (FlowControl::UnconditionalBranch, _) => at = near_target(&i)?,
                (FlowControl::IndirectBranch, OpKind::Register) => {
                    let r = i.op0_register();
                    return (r.full_register() != Register::RSP).then_some(Dispatch::Through(r));
                }
                (FlowControl::IndirectBranch, OpKind::Memory) => {
                    at = self.read_only_pointer(Exec::import_slot(&i)?)?;
                }
                _ => return None,
            }
        }
        None
    }

    /// Reads the code address a pointer in read-only data holds.
    ///
    /// # Arguments
    ///
    /// * `slot` - The pointer's address.
    ///
    /// # Returns
    ///
    /// The address it holds, or `None` when the slot is an import's, sits in
    /// writable or executable memory, or holds no address of code.
    pub(super) fn read_only_pointer(&self, slot: u64) -> Option<u64> {
        let program = self.program;
        let section = program.section_at(slot)?;
        if section.writable || section.executable || self.names().import_at(slot).is_some() {
            return None;
        }
        let word = usize::try_from(self.conv.word).ok()?;
        let mut bytes = [0u8; 8];
        bytes
            .get_mut(..word)?
            .copy_from_slice(program.read_va(slot, word)?);
        let to = u64::from_le_bytes(bytes);
        program
            .section_at(to)
            .is_some_and(|s| s.executable)
            .then_some(to)
    }
}
