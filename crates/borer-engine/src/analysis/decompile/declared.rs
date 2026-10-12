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
        let fields = struct_fields(overlay, s, word);
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
