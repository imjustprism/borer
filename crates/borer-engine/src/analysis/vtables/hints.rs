//! The class a value holds: return summaries, value hints, and the class
//! of a call's receiver, a parameter or a member.

use std::collections::{BTreeMap, BTreeSet};

use super::members::FirstMembers;
use super::scan::ancestry;
use super::{ClassInfo, Scan, Tracked};
use crate::analysis::classes::class_of;
use crate::analysis::descriptors::unanimous;
use crate::analysis::{Analysis, Function, single};

/// Classes found by [`return_summaries`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct Summaries {
    /// Function entry to the class its result points at.
    pub(super) results: Vec<(u64, String)>,
    /// Global address to the class the word there points at.
    pub(super) globals: Vec<(u64, String)>,
    /// `(class, offset)` to the class the pointer field there points at.
    pub(super) fields: Vec<((String, u64), String)>,
}

/// Types results, globals and fields by what a function hands back or
/// stores.
///
/// A function that stores no table and returns the result of a call to a
/// constructor of class `C`, to a function declared or hinted to return a
/// `C`, the word of a global hinted `C` or the word of a field of its own
/// class hinted `C`, returns a `C` (a creator, a wrapper, a singleton
/// getter, a field getter); a global or a field of the storing function's
/// class that only ever receives results of class `C` holds a `C`.
///
/// # Arguments
///
/// * `analysis` - Functions with their signatures.
/// * `scans` - Scans of the functions examined so far.
/// * `vtables` - Table address to class name.
/// * `ret_hints` - Result classes known so far.
/// * `global_hints` - Global classes known so far.
/// * `field_hints` - Pointer field classes known so far.
/// * `this_class` - The class a function's `this` belongs to, when known.
///
/// # Returns
///
/// The new result, global and field classes.
pub(super) fn return_summaries(
    analysis: &Analysis,
    scans: &BTreeMap<u64, Scan>,
    vtables: &BTreeMap<u64, String>,
    ret_hints: &BTreeMap<u64, String>,
    global_hints: &BTreeMap<u64, String>,
    field_hints: &BTreeMap<(String, u64), String>,
    this_class: &dyn Fn(u64) -> Option<String>,
) -> Summaries {
    let result_class = |callee: u64| -> Option<String> {
        if let Some(c) = ret_hints.get(&callee) {
            return Some(c.clone());
        }
        let f = analysis.function(callee)?;
        if let Some(sig) = &f.signature {
            return crate::analysis::decompile::pointee_class(&sig.ret).map(str::to_owned);
        }
        let stored: BTreeSet<u64> = scans.get(&callee)?.stores.iter().copied().collect();
        vtables.get(&single(stored)?).cloned()
    };
    let results: Vec<(u64, String)> = scans
        .iter()
        .filter(|(e, s)| {
            s.stores.is_empty()
                && !ret_hints.contains_key(e)
                && analysis
                    .function(**e)
                    .is_some_and(|f| f.signature.is_none())
        })
        .filter_map(|(&e, s)| {
            let class = s
                .returns_result
                .and_then(result_class)
                .or_else(|| s.returns_global.and_then(|g| global_hints.get(&g).cloned()))
                .or_else(|| {
                    let off = s.returns_field?;
                    field_hints.get(&(this_class(e)?, off)).cloned()
                })?;
            Some((e, class))
        })
        .collect();
    let mut votes: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for (addr, callee) in scans.values().flat_map(|s| s.global_result_stores.iter()) {
        if global_hints.contains_key(addr) {
            continue;
        }
        if let Some(c) = result_class(*callee) {
            votes.entry(*addr).or_default().insert(c);
        }
    }
    let globals: Vec<(u64, String)> = unanimous(votes).into_iter().collect();
    let mut field_votes: BTreeMap<(String, u64), BTreeSet<String>> = BTreeMap::new();
    for (&entry, scan) in scans {
        if scan.field_result_stores.is_empty() {
            continue;
        }
        let Some(class) = this_class(entry) else {
            continue;
        };
        for &(off, callee) in &scan.field_result_stores {
            let key = (class.clone(), off);
            if field_hints.contains_key(&key) {
                continue;
            }
            if let Some(c) = result_class(callee) {
                field_votes.entry(key).or_default().insert(c);
            }
        }
    }
    Summaries {
        results,
        globals,
        fields: unanimous(field_votes).into_iter().collect(),
    }
}

/// Types call results and fields by the calls they are passed to.
///
/// In a member method of class `K`, every direct call argument that is the
/// result of an earlier call `F`, the word loaded from `[this + off]` or the
/// address `this + off` casts a vote: passed as the callee's `this`, the
/// value is the callee's receiver class (its own class when it is a member,
/// else its hinted first parameter); passed for a declared parameter, a
/// result or loaded field is the class the parameter type points at and a
/// field address is the parameter's object type. Votes resolve like
/// parameter hints: classes to the nearest common ancestor, object types
/// when unanimous, and of an object and the member it starts with, the
/// object ([`FirstMembers`]).
///
/// # Arguments
///
/// * `analysis` - Functions, names and signatures.
/// * `classes` - Classes with their parents.
/// * `scans` - Scans of every class-named function.
/// * `renames` - Names chosen by this pass.
/// * `hints` - Parameter hints chosen by this pass.
/// * `statics` - Class-named functions whose first argument is not `this`
///   (creators).
/// * `held` - The classes others hold at offset 0.
///
/// # Returns
///
/// The result, pointer-field and embedded-object classes the votes agree
/// on.
pub(super) fn value_hints(
    analysis: &Analysis,
    classes: &BTreeMap<String, ClassInfo>,
    scans: &BTreeMap<u64, Scan>,
    renames: &BTreeMap<u64, String>,
    hints: &BTreeMap<u64, BTreeMap<u8, String>>,
    statics: &BTreeSet<u64>,
    held: &FirstMembers,
) -> ValueHints {
    let member_of = |entry: u64| -> Option<String> {
        let f = analysis.function(entry)?;
        if statics.contains(&entry) {
            return None;
        }
        let name = renames.get(&entry).cloned().or_else(|| f.name.clone())?;
        let class = class_of(&name)?;
        let member = match (&f.signature, scans.get(&entry)) {
            (Some(sig), Some(scan)) => {
                sig.is_const || scan.args_read > sig.params.len() + usize::from(sig.by_pointer)
            }
            (Some(_), None) => false,
            (None, _) => true,
        };
        member.then(|| class.to_owned())
    };
    let receiver_class = |entry: u64| -> Option<String> {
        member_of(entry).or_else(|| hints.get(&entry)?.get(&0).cloned())
    };
    let mut ret_votes: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    let mut field_votes: BTreeMap<(String, u64), BTreeSet<String>> = BTreeMap::new();
    let mut type_votes: BTreeMap<(String, u64), BTreeSet<String>> = BTreeMap::new();
    for f in &analysis.functions {
        let Some(class) = member_of(f.entry) else {
            continue;
        };
        let Some(scan) = scans.get(&f.entry) else {
            continue;
        };
        for (target, pos, val) in &scan.calls {
            let pos = usize::from(*pos);
            let callee = analysis.function(*target);
            let lead = usize::from(member_of(*target).is_some())
                + usize::from(
                    callee
                        .and_then(|c| c.signature.as_ref())
                        .is_some_and(|s| s.by_pointer),
                );
            let declared = callee
                .and_then(|c| c.signature.as_ref())
                .and_then(|s| pos.checked_sub(lead).and_then(|i| s.params.get(i)));
            let (points_at, embedded) = if pos == 0 {
                let recv = receiver_class(*target);
                (recv.clone(), recv)
            } else if let Some(ty) = declared {
                (
                    crate::analysis::decompile::pointee_class(ty).map(str::to_owned),
                    Some(object_type(ty)).filter(|t| !t.is_empty()),
                )
            } else {
                (None, None)
            };
            match (val, points_at, embedded) {
                (Tracked::Result(callee), Some(c), _) => {
                    ret_votes.entry(*callee).or_default().insert(c);
                }
                (Tracked::Field(off), Some(c), _) => {
                    field_votes
                        .entry((class.clone(), *off))
                        .or_default()
                        .insert(c);
                }
                (Tracked::FieldAddr(off), _, Some(t)) => {
                    type_votes
                        .entry((class.clone(), *off))
                        .or_default()
                        .insert(t);
                }
                _ => {}
            }
        }
    }
    ValueHints {
        results: ret_votes
            .into_iter()
            .filter_map(|(e, v)| common_class(classes, &held.outermost(v)).map(|c| (e, c)))
            .collect(),
        fields: field_votes
            .into_iter()
            .filter_map(|(k, v)| common_class(classes, &held.outermost(v)).map(|c| (k, c)))
            .collect(),
        types: unanimous(
            type_votes
                .into_iter()
                .map(|(k, v)| (k, held.outermost(v)))
                .collect(),
        ),
    }
}

/// What [`value_hints`] returns.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct ValueHints {
    /// Function entry to the class its result points at.
    pub(super) results: BTreeMap<u64, String>,
    /// `(class, offset)` to the class the pointer field there points at.
    pub(super) fields: BTreeMap<(String, u64), String>,
    /// `(class, offset)` to the type of the object embedded at the field.
    pub(super) types: BTreeMap<(String, u64), String>,
}

/// Returns the object type a declared parameter type denotes: `const Foo &`,
/// `Foo &`, `Foo *` and `Foo` all give `Foo`.
///
/// # Arguments
///
/// * `ty` - The declared type text.
pub(in crate::analysis) fn object_type(ty: &str) -> String {
    ty.trim_start_matches("const ")
        .trim_end_matches(['&', '*', ' '])
        .to_owned()
}

/// The class a member function's `this` belongs to: the class its name
/// qualifies it with, unless it is a creator or its signature declares
/// every argument it reads (a static).
///
/// # Arguments
///
/// * `target` - The function.
/// * `renames` - Names chosen by this pass.
/// * `statics` - Class-named functions whose first argument is not `this`.
/// * `scans` - Scans, for how many arguments the function reads.
pub(super) fn receiver_class<'a>(
    target: &'a Function,
    renames: &'a BTreeMap<u64, String>,
    statics: &'a BTreeSet<u64>,
    scans: &BTreeMap<u64, Scan>,
) -> Option<&'a str> {
    let name = match renames.get(&target.entry) {
        Some(renamed) => renamed.as_str(),
        None => target.name.as_deref()?,
    };
    let class = class_of(name)?;
    if statics.contains(&target.entry) {
        return None;
    }
    match &target.signature {
        None => Some(class),
        Some(sig) => {
            let reads_this = sig.is_const
                || scans
                    .get(&target.entry)
                    .is_some_and(|s| s.args_read > sig.params.len() + usize::from(sig.by_pointer));
            reads_this.then_some(class)
        }
    }
}

/// Returns the class a function's own name gives it, else the class its
/// first parameter was hinted, without asking whether it is a member of
/// the class ([`receiver_class`] does).
///
/// # Arguments
///
/// * `analysis` - The functions.
/// * `renames` - Names chosen by this pass.
/// * `statics` - Class-named functions whose first argument is not `this`.
/// * `hints` - Parameter classes chosen by this pass.
/// * `entry` - The function's entry.
pub(super) fn named_class(
    analysis: &Analysis,
    renames: &BTreeMap<u64, String>,
    statics: &BTreeSet<u64>,
    hints: &BTreeMap<u64, BTreeMap<u8, String>>,
    entry: u64,
) -> Option<String> {
    let f = analysis.function(entry)?;
    if statics.contains(&entry) {
        return None;
    }
    renames
        .get(&entry)
        .map_or(f.name.as_deref(), |n| Some(n.as_str()))
        .and_then(class_of)
        .map(str::to_owned)
        .or_else(|| hints.get(&entry)?.get(&0).cloned())
}

/// The class a function's parameter `n` is known to point at.
///
/// A declared signature names it; otherwise a hint an earlier round
/// established does. The hidden `this` and return-pointer parameters come
/// before the declared ones, so the signature is indexed past them.
///
/// # Arguments
///
/// * `f` - The function the parameter belongs to.
/// * `hints` - Parameter classes established so far.
/// * `n` - The parameter's position among the argument registers.
pub(super) fn param_class(
    f: &Function,
    hints: &BTreeMap<u64, BTreeMap<u8, String>>,
    n: u8,
) -> Option<String> {
    if let Some(sig) = &f.signature {
        let lead = usize::from(class_of(&sig.name).is_some()) + usize::from(sig.by_pointer);
        let at = usize::from(n).checked_sub(lead)?;
        return sig
            .params
            .get(at)
            .and_then(|t| crate::analysis::decompile::pointee_class(t))
            .filter(|c| c.contains("::"))
            .map(str::to_owned);
    }
    hints.get(&f.entry)?.get(&n).cloned()
}

/// Returns the class every voter is or derives from: the single voter, or
/// the nearest ancestor (following parent links) common to all of them.
///
/// # Arguments
///
/// * `classes` - Classes with their parents.
/// * `voters` - The classes of the callers.
pub(super) fn common_class(
    classes: &BTreeMap<String, ClassInfo>,
    voters: &BTreeSet<String>,
) -> Option<String> {
    let mut it = voters.iter();
    let mut common = ancestry(classes, it.next()?);
    for v in it {
        let theirs = ancestry(classes, v);
        common.retain(|c| theirs.contains(c));
    }
    common.into_iter().next()
}

/// Returns the voter every other voter is or is an ancestor of: the most
/// derived class when all of them lie on one line of descent.
///
/// # Arguments
///
/// * `classes` - Classes with their parents.
/// * `voters` - The classes the callees accept.
///
/// # Returns
///
/// That class, or `None` when two voters lie on separate lines.
pub(super) fn deepest_class(
    classes: &BTreeMap<String, ClassInfo>,
    voters: &BTreeSet<String>,
) -> Option<String> {
    voters
        .iter()
        .find(|v| {
            let line = ancestry(classes, v);
            voters.iter().all(|w| line.contains(w))
        })
        .cloned()
}

/// Returns a type and every type its template arguments name, at any
/// depth, keeping the qualified ones: `A::B<C::D,int>` gives itself and
/// `C::D`.
///
/// # Arguments
///
/// * `name` - The type's name.
pub(super) fn type_parts(name: &str) -> BTreeSet<String> {
    let mut parts = BTreeSet::new();
    let mut todo = vec![name.trim()];
    while let Some(n) = todo.pop() {
        if n.contains("::") {
            parts.insert(n.to_owned());
        }
        let (Some(open), Some(close)) = (n.find('<'), n.rfind('>')) else {
            continue;
        };
        let Some(inner) = n.get(open + 1..close) else {
            continue;
        };
        let mut depth = 0usize;
        let mut start = 0;
        for (i, ch) in inner.char_indices() {
            match ch {
                '<' => depth += 1,
                '>' => depth = depth.saturating_sub(1),
                ',' if depth == 0 => {
                    todo.extend(inner.get(start..i).map(str::trim));
                    start = i + 1;
                }
                _ => {}
            }
        }
        todo.extend(inner.get(start..).map(str::trim));
    }
    parts
}

/// A class the callees a parameter is handed to bound it by.
#[derive(Clone, Copy)]
pub(super) struct Bound {
    /// Every callee giving it was only given it as the common ancestor of
    /// its votes.
    pub(super) wide: bool,
    /// Some callee's name or declared signature gives it: the callee uses
    /// the parameter as one.
    pub(super) used: bool,
}
