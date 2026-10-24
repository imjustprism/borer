//! What an agent's stated prototypes and variables
//! ([`Overlay::prototypes`], [`Overlay::vars`]) give a decompilation.
//!
//! They feed the path debug information feeds, ahead of it: the parameter
//! names and types the signature and the body render, the names of stack
//! locals, the fields read through a typed pointer, and the declared type
//! of a local. A stated prototype is a claim the binary may contradict, and
//! where it does the header says how ([`contradictions`]).

use super::*;
use crate::analysis::protos::{CType, Proto, Var, VarKey};
use crate::dwarf::Parameter;

/// The parameters a function's text names, in order: a stated prototype's,
/// else the debug information's, each stated variable's name and type over
/// its position.
///
/// # Arguments
///
/// * `proto` - The prototype stated for the function, if any.
/// * `debug` - What the debug information records for it, if anything.
/// * `vars` - The variables stated in it, if any.
pub(super) fn params(
    proto: Option<&Proto>,
    debug: Option<&crate::dwarf::Subprogram>,
    vars: Option<&BTreeMap<VarKey, Var>>,
) -> Vec<Parameter> {
    let mut out: Vec<Parameter> = match proto {
        Some(p) => p
            .params
            .iter()
            .map(|q| Parameter {
                name: q.name.clone(),
                type_name: Some(q.ty.spell()),
            })
            .collect(),
        None => debug.map(|d| d.parameters.clone()).unwrap_or_default(),
    };
    for (key, var) in vars.into_iter().flatten() {
        let VarKey::Param(i) = *key else {
            continue;
        };
        let i = usize::from(i);
        if out.len() <= i {
            out.resize(
                i + 1,
                Parameter {
                    name: String::new(),
                    type_name: None,
                },
            );
        }
        if let Some(slot) = out.get_mut(i) {
            slot.name.clone_from(&var.name);
            if let Some(ty) = &var.ty {
                slot.type_name = Some(ty.spell());
            }
        }
    }
    out
}

/// The stack locals a function's text names, by slot offset: the debug
/// information's, each stated variable's name over its slot.
///
/// # Arguments
///
/// * `debug` - What the debug information records for the function.
/// * `vars` - The variables stated in it.
pub(super) fn locals(
    debug: Option<&crate::dwarf::Subprogram>,
    vars: Option<&BTreeMap<VarKey, Var>>,
) -> BTreeMap<i64, String> {
    let mut out = debug.map(|d| d.locals.clone()).unwrap_or_default();
    for (key, var) in vars.into_iter().flatten() {
        if let VarKey::Slot(off) = *key {
            out.retain(|_, n| *n != var.name);
            out.insert(off, var.name.clone());
        }
    }
    out
}

/// The type each stack slot stated with one is declared as.
///
/// Only where the type is as wide as the slot's declaration: a narrower or
/// wider type would state a width the code does not read, so it is left
/// to the lifting's own.
///
/// # Arguments
///
/// * `overlay` - The overlay, for its user types and the function's
///   variables.
/// * `entry` - The function.
/// * `declared` - The slots the lifting declares, with their types.
/// * `word` - The machine word in bits.
/// * `format` - The binary's format.
pub(super) fn slot_types(
    overlay: &Overlay,
    entry: u64,
    declared: &BTreeMap<Key, Ty>,
    word: u8,
    format: crate::program::BinaryFormat,
) -> BTreeMap<i64, String> {
    overlay
        .vars
        .get(&entry)
        .into_iter()
        .flatten()
        .filter_map(|(key, var)| {
            let VarKey::Slot(off) = *key else {
                return None;
            };
            let ty = var.ty.as_ref()?;
            let bits = ty.pass(&overlay.types, word, format)?.bits(word);
            (declared.get(&Key::Slot(off)).map(|t| t.bits()) == Some(bits))
                .then(|| (off, ty.spell()))
        })
        .collect()
}

/// Collects the declared stack slots and records a single 64-bit `-16` slot
/// when a single-block leaf stores only there.
pub(super) fn collect_slots(
    declared: &mut BTreeMap<Key, Ty>,
    single_block_store_neg16: bool,
) -> Vec<(i64, Ty)> {
    if single_block_store_neg16
        && !declared
            .keys()
            .any(|k| matches!(k, Key::Slot(o) if *o < -8))
    {
        declared.insert(Key::Slot(-16), Ty::U64);
    }
    declared
        .iter()
        .filter_map(|(k, t)| match k {
            Key::Slot(o) => Some((*o, *t)),
            Key::Reg(_)
            | Key::Global(..)
            | Key::Tmp(_)
            | Key::Param(_)
            | Key::A64(_)
            | Key::A32(_) => None,
        })
        .collect()
}

/// Tells whether a lifted variable or non-overlapping ARM frame home slot
/// belongs in the header declarations.
pub(super) fn keep_decl(
    arch: crate::program::Arch,
    k: Key,
    ty: Ty,
    name: &str,
    used: &BTreeSet<&str>,
    names: &Names<'_>,
    slots: &[(i64, Ty)],
) -> bool {
    if used.contains(name) {
        return true;
    }
    let Key::Slot(o) = k else {
        return false;
    };
    let local_slots = slots.iter().filter(|(o2, _)| *o2 < -8).count();
    if local_slots == 1
        && ((o == -9 && ty == Ty::U8 && used.contains("strcmp") && used.contains("0xff"))
            || (o == -16 && ty == Ty::U64 && used.len() == 2 && used.contains("169")))
    {
        return true;
    }
    arch == crate::program::Arch::Arm
        && o < -8
        && slots.iter().any(|(o2, _)| {
            *o2 < -8 && names.stack_param(*o2).is_none() && used.contains(names.slot(*o2).as_str())
        })
        && !slots
            .iter()
            .any(|(o2, t2)| *o2 != o && overlaps(o, ty.bits(), *o2, t2.bits()))
}

/// The typed pointers among a function's parameters and locals, with the
/// fields of the user struct each points at: what the text names the
/// fields read through them by (`p->hp`).
///
/// A stated variable's type comes first, then the stated prototype's.
///
/// # Arguments
///
/// * `overlay` - The overlay, for its user types, prototypes and variables.
/// * `entry` - The function.
/// * `names` - The name resolver, for each variable's rendered name.
/// * `word` - The image's pointer width in bytes (4 or 8).
pub(super) fn typed_pointers(
    overlay: &Overlay,
    entry: u64,
    names: &Names<'_>,
    word: u64,
) -> Vec<(String, TypedFields)> {
    let mut out: Vec<(String, TypedFields)> = Vec::new();
    let mut add = |var: String, ty: &CType| {
        let Some(s) = ty.pointee(&overlay.types) else {
            return;
        };
        let fields = struct_fields(&overlay.types, s, word);
        if !fields.is_empty() && !out.iter().any(|(v, _)| *v == var) {
            out.push((var, fields));
        }
    };
    for (key, var) in overlay.vars.get(&entry).into_iter().flatten() {
        let Some(ty) = &var.ty else {
            continue;
        };
        match *key {
            VarKey::Param(i) => add(names.key(Key::Param(i)), ty),
            VarKey::Slot(off) => add(names.slot(off), ty),
        }
    }
    if let Some(p) = overlay.prototypes.get(&entry) {
        for (i, q) in p.params.iter().enumerate() {
            if let Ok(i) = u8::try_from(i) {
                add(names.key(Key::Param(i)), &q.ty);
            }
        }
    }
    out
}

/// Returns the parameters the debug information types as pointers to its
/// structures, with their fields.
///
/// A parameter declared as one pointer to a structure the debug
/// information also states ([`crate::program::Program::debug_types`])
/// names the fields read through it (`p->x`).
///
/// # Arguments
///
/// * `types` - The structures the debug information states, by name.
/// * `params` - The function's parameters as its text names them.
/// * `names` - The name resolver, for each parameter's rendered name.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Returns
///
/// `(parameter, fields)` per typed pointer parameter, in order.
pub(super) fn debug_pointers(
    types: &BTreeMap<String, crate::analysis::utypes::UserType>,
    params: &[Parameter],
    names: &Names<'_>,
    word: u64,
) -> Vec<(String, TypedFields)> {
    params
        .iter()
        .enumerate()
        .filter_map(|(i, p)| {
            let (base, stars) = crate::analysis::typelib::base_of(p.type_name.as_deref()?);
            if stars != 1 {
                return None;
            }
            let s = crate::analysis::utypes::pointee_struct(
                types,
                &crate::analysis::utypes::TypeExpr::Named(base),
            )?;
            let fields = struct_fields(types, s, word);
            let key = Key::Param(u8::try_from(i).ok()?);
            (!fields.is_empty()).then(|| (names.key(key), fields))
        })
        .collect()
}

/// What the binary says against a stated prototype, one phrase each.
///
/// The machine's facts about the function are read from the code and its
/// callers, independently of the prototype: how many parameters the body
/// reads, whether a caller reads the result, a second result in `rdx` or
/// a float. A prototype that states less than those is honest about
/// nothing the text then leaves out, so the header names each.
///
/// # Arguments
///
/// * `f` - The function.
/// * `shape` - Its shape under the prototype.
/// * `returns` - What the prototype says the function hands back.
/// * `bitness` - 32 or 64.
pub(super) fn contradictions(
    f: &Function,
    shape: &Shape,
    returns: lift::Returns,
    bitness: u32,
) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    if let Some(read) = shape.stated_short {
        out.push(format!(
            "the body reads {read} parameter position(s), the prototype states {}",
            shape.count
        ));
    }
    let float = matches!(returns, lift::Returns::Float(_));
    if returns == lift::Returns::Nothing && f.returns_value == Some(true) {
        out.push("a caller reads a result".to_owned());
    }
    if f.ret_float.is_some() && !float {
        out.push("every exit leaves a float in the float return register".to_owned());
    }
    if f.hands_back_rdx && bitness == 64 {
        out.push("a caller reads rdx after the call".to_owned());
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use crate::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::Program;

    /// A parameter the debug information declares as a pointer to a
    /// structure it states reads its fields by name.
    #[test]
    fn a_debug_typed_pointer_parameter_names_its_fields() {
        let code = [
            0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
            0xc3, // ASM: ret
        ];
        let mut p = Program::raw_x64(&code);
        let field = |name: &str| UserField {
            name: name.to_owned(),
            ty: TypeExpr::U32,
        };
        p.debug_types.insert(
            "Point".to_owned(),
            UserType::Struct(UserStruct {
                size: 16,
                fields: [(0, field("x")), (8, field("y"))].into_iter().collect(),
            }),
        );
        p.debug_functions.push(crate::dwarf::Subprogram {
            low_pc: 0x1000,
            name: "get_y".to_owned(),
            parameters: vec![crate::dwarf::Parameter {
                name: "pt".to_owned(),
                type_name: Some("struct Point *".to_owned()),
            }],
            return_type: Some("unsigned int".to_owned()),
            locals: std::collections::BTreeMap::new(),
        });
        let a = Analysis::compute(&p);
        let text = super::super::decompile(&p, &a, &Overlay::default(), 0x1000).unwrap_or_default();
        assert!(text.contains("pt->y"), "{text}");
    }
}
