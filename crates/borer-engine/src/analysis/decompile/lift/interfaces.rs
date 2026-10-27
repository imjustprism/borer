//! Calls through a COM interface ([`crate::analysis::sdk::Interface`]).
//!
//! A call through slot `k` of an object the code shows to be an SDK COM
//! interface is that interface's method `k`. The evidence is a declaration
//! only: an import declared to return `Iface *` (`Direct3DCreate9`), a
//! parameter declared `Iface **` (`D3D11CreateDevice`,
//! `IDirect3D9::CreateDevice`), or a `void **` beside a `REFIID` argument
//! that is the address of an IID the SDK defines (`CoCreateInstance`,
//! `QueryInterface`). The local such a call writes holds that interface;
//! an object nothing shows the interface of keeps `vtable[k]`.

use super::*;
use crate::analysis::sdk::{self, Method, Out};

impl Exec<'_, '_> {
    /// Returns the COM method a call through slot `slot` of `recv`'s
    /// vtable reaches, when the code shows `recv` is an SDK interface.
    ///
    /// # Arguments
    ///
    /// * `recv` - The receiver.
    /// * `slot` - The vtable slot.
    pub(super) fn com_method(&self, recv: &Expr, slot: usize) -> Option<&'static Method> {
        sdk::interface(&self.class_of_expr(recv)?)?
            .methods
            .get(slot)
    }

    /// Returns the class of the object the word stack slot `slot` holds
    /// points at, from the type the slot's object was given
    /// ([`Env::slot_types`]): `T` for a smart pointer `X<T>`, `Iface` for
    /// an `Iface *`.
    ///
    /// # Arguments
    ///
    /// * `slot` - The slot's offset.
    pub(super) fn held_class(&self, slot: i64) -> Option<String> {
        let ty = self.env.slot_types.get(&slot)?;
        smart_pointee(ty)
            .or_else(|| sdk::pointed_interface(ty, 1).map(|i| i.name))
            .map(str::to_owned)
    }

    /// Returns how a call through vtable slot `slot` of a receiver with no
    /// class of the program's renders: the method of the SDK COM interface
    /// the receiver is shown to be, `delete` for a destructor's slot passed
    /// only `1`, else `vtable[slot]`.
    ///
    /// # Arguments
    ///
    /// * `recv` - The receiver.
    /// * `slot` - The vtable slot.
    /// * `shown` - The receiver as the call shows it.
    /// * `rendered` - The receiver's own text.
    /// * `args` - The other arguments; `delete` takes the receiver instead.
    pub(super) fn slot_callee(
        &self,
        recv: &Expr,
        slot: usize,
        shown: &str,
        rendered: String,
        args: &mut Vec<String>,
    ) -> String {
        match self.com_method(recv, slot) {
            Some(m) => format!("{shown}->{}", m.name),
            None if self.ctx.analysis.classes.dtor_slots.contains(&slot) && *args == ["1"] => {
                *args = vec![rendered];
                "delete".to_owned()
            }
            None => format!("{shown}->vtable[{slot}]"),
        }
    }

    /// Returns the class of the object a call's result points at: the
    /// declared result of a function of the program
    /// ([`Exec::returned_class`]), else the SDK COM interface an import is
    /// declared to return a pointer to (`Direct3DCreate9` gives
    /// `IDirect3D9`).
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call names a function.
    /// * `reached` - The callee's entry or the import slot the call goes
    ///   through.
    /// * `arg0_class` - The class of the first argument's object, if known.
    pub(super) fn result_class(
        &self,
        target: Option<u64>,
        reached: Option<u64>,
        arg0_class: Option<&str>,
    ) -> Option<String> {
        if let Some(c) = target.and_then(|t| self.returned_class(t, arg0_class)) {
            return Some(c);
        }
        let decl = library_decl(self.ctx, reached)?;
        sdk::pointed_interface(decl.ret, 1).map(|i| i.name.to_owned())
    }

    /// Returns how many registers a 32-bit call nothing states the
    /// convention of passes: `this` in `ecx` for a call through a vtable or
    /// to a method of the caller's class, none for any other, and none for
    /// a call through an SDK COM interface, which is `__stdcall` and pushes
    /// `this` first.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    /// * `method` - The callee is a method of the caller's class.
    pub(super) fn this_in_ecx(&self, target: Option<u64>, method: bool) -> usize {
        let com = self
            .receiver
            .as_ref()
            .and_then(|r| self.class_of_expr(r))
            .is_some_and(|c| sdk::interface(&c).is_some());
        usize::from((target.is_none() && !com) || method)
    }

    /// Returns the slots whose address a call takes, each with the
    /// interface the call hands back through it: an out-parameter of a COM
    /// method or of a declared import names it, and any other slot's
    /// address may be written with anything, so it gets none.
    ///
    /// The receiver's own slot may be among them, so the call is named
    /// before [`Exec::type_com_outputs`] applies what this returns.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    /// * `reached` - The callee's entry or the import slot the call goes
    ///   through.
    pub(super) fn com_outputs(
        &mut self,
        instr: &Instruction,
        reached: Option<u64>,
    ) -> Vec<(i64, Option<&'static str>)> {
        let regs = if self.bitness() == 64 {
            self.ctx.conv.args
        } else {
            &[]
        };
        let mut args: Vec<Option<Expr>> = regs
            .iter()
            .map(|r| self.env.vals.get(&Key::Reg(*r)).cloned())
            .collect();
        args.extend(self.outgoing_stack_args(reached).into_iter().map(Some));
        let method = self
            .vtable_shape(instr)
            .and_then(|(recv, slot)| self.com_method(&recv, slot));
        let (outs, lead) = match (method, library_decl(self.ctx, reached)) {
            (Some(m), _) => (m.outs.clone(), 1),
            (None, Some(d)) => (
                sdk::outs_of(&d.params.iter().map(|p| p.ty).collect::<Vec<_>>()),
                0,
            ),
            (None, None) => (Vec::new(), 0),
        };
        let iface = |i: usize| {
            let (_, out) = outs.iter().find(|(k, _)| k + lead == i)?;
            match out {
                Out::Iface(name) => Some(*name),
                Out::ByIid(j) => self.iid_arg(args.get(j + lead)?.as_ref()?),
            }
        };
        args.iter()
            .enumerate()
            .filter_map(|(i, arg)| match *arg {
                Some(Expr::Sp(slot)) => Some((slot, iface(i))),
                _ => None,
            })
            .collect()
    }

    /// Types the locals a call hands a COM object back through: each slot
    /// [`Exec::com_outputs`] names an interface for holds it from then on,
    /// and the others hold none. A slot also seen at a position the callee
    /// may not read (a 64-bit argument register left over from earlier
    /// code) keeps the interface its out-parameter names.
    ///
    /// # Arguments
    ///
    /// * `outputs` - The slots and their interfaces.
    pub(super) fn type_com_outputs(&mut self, outputs: &[(i64, Option<&'static str>)]) {
        for &(slot, iface) in outputs {
            match iface {
                Some(name) => {
                    let ty = format!("{name} *");
                    self.ctx.frame.hold(slot, &ty);
                    self.env.slot_types.insert(slot, ty);
                }
                None if outputs.iter().any(|(s, i)| *s == slot && i.is_some()) => {}
                None => self.forget_interface(slot),
            }
        }
    }

    /// Forgets the COM interface a slot held once something else may have
    /// written it: the code stored another value there, or a call took its
    /// address for no out-parameter of a known interface. The slot's
    /// declaration then says no interface either.
    ///
    /// # Arguments
    ///
    /// * `slot` - The slot's offset.
    pub(super) fn forget_interface(&mut self, slot: i64) {
        let com = self.env.slot_types.get(&slot);
        if com.is_some_and(|t| sdk::pointed_interface(t, 1).is_some()) {
            self.env.slot_types.remove(&slot);
            self.ctx.frame.unhold(slot);
        }
    }

    /// Returns the interface whose IID an argument is the address of.
    ///
    /// # Arguments
    ///
    /// * `arg` - The argument's value.
    fn iid_arg(&self, arg: &Expr) -> Option<&'static str> {
        let Expr::Const(addr) = *arg else {
            return None;
        };
        let bytes = self.ctx.program.read_va(addr, 16)?;
        sdk::interface_of_iid(bytes).map(|i| i.name)
    }
}
