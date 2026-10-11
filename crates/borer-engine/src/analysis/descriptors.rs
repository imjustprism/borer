//! Class descriptors: the static object per class that an engine's factory
//! registers and its creators allocate from.
//!
//! Engines with their own reflection (Nebula's `Core::Rtti`, Unreal's
//! `UClass`, Qt's `QMetaObject`) keep one writable object per class and touch
//! it from three kinds of function: a registration that also spells the
//! class name as a string literal, a creator that allocates the instance and
//! calls the constructor, and an initializer that stores the parent class's
//! descriptor beside its own (spelling the name again). The first names the
//! object, the second links it to the constructor's vtable, so a table no
//! signature string names still gets its class name, and the third links
//! the class to its parent.

use std::collections::{BTreeMap, BTreeSet};

use super::{Analysis, data_referrers, single};
use crate::program::Program;
use crate::strings::cstr_at;

/// Longest class name read from a literal.
const NAME_MAX: usize = 200;
/// Parent links followed when looking for a common ancestor.
const ANCESTORS_MAX: usize = 16;

/// A set of things per referencing function.
type ByFunction<T> = BTreeMap<u64, BTreeSet<T>>;

/// What the descriptors of an image tell.
pub(super) struct Descriptors {
    /// Object address to class name.
    pub names: BTreeMap<u64, String>,
    /// Class name to the name of its parent class.
    pub parents: BTreeMap<String, String>,
}

/// Names the descriptor objects and links classes to their parents.
///
/// A function that references exactly one qualified-name literal and exactly
/// one writable data object that holds no string votes the literal as the
/// object's name; objects whose votes agree on one name keep it. A function
/// that references one literal and exactly two objects, one of them named
/// already and not by that literal (an initializer storing the parent's
/// descriptor beside its own), names the other with the literal, so a class
/// no registration spells is still named, round after round from the roots
/// down as each parent gets its name; then an initializer whose two
/// objects are both named, one by its literal, votes the other's name as
/// the class's parent; classes whose votes agree keep the link.
///
/// # Arguments
///
/// * `program` - Sections and bytes.
/// * `analysis` - Reference sites by target.
pub(super) fn find(program: &Program, analysis: &Analysis) -> Descriptors {
    let (names_by_fn, objects_by_fn) = references(program, analysis);
    let mut votes: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for (f, names) in &names_by_fn {
        let Some(name) = single(names) else {
            continue;
        };
        let Some(objects) = objects_by_fn.get(f) else {
            continue;
        };
        let Some(&object) = single(objects) else {
            continue;
        };
        votes.entry(object).or_default().insert(name.clone());
    }
    let mut names = unanimous(votes);
    // INVARIANT: a registration names its class beside its parent's, and the
    // parent is only known once its own registration was read, so the rule
    // runs from the roots down until a round names nothing new.
    for _ in 0..ANCESTORS_MAX {
        let mut own_votes: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
        for (f, literals) in &names_by_fn {
            let Some(literal) = single(literals) else {
                continue;
            };
            let Some(objects) = objects_by_fn.get(f) else {
                continue;
            };
            let mut objects = objects.iter();
            let (Some(&a), Some(&b), None) = (objects.next(), objects.next(), objects.next())
            else {
                continue;
            };
            let own = match (names.get(&a), names.get(&b)) {
                (None, Some(nb)) if nb != literal => a,
                (Some(na), None) if na != literal => b,
                _ => continue,
            };
            own_votes.entry(own).or_default().insert(literal.clone());
        }
        let before = names.len();
        for (object, name) in unanimous(own_votes) {
            names.entry(object).or_insert(name);
        }
        if names.len() == before {
            break;
        }
    }
    let mut parent_votes: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (f, literals) in &names_by_fn {
        let Some(literal) = single(literals) else {
            continue;
        };
        let Some(objects) = objects_by_fn.get(f) else {
            continue;
        };
        let mut objects = objects.iter();
        let (Some(a), Some(b), None) = (objects.next(), objects.next(), objects.next()) else {
            continue;
        };
        let (Some(na), Some(nb)) = (names.get(a), names.get(b)) else {
            continue;
        };
        let parent = match (na == literal, nb == literal) {
            (true, false) => nb,
            (false, true) => na,
            _ => continue,
        };
        parent_votes
            .entry(literal.clone())
            .or_default()
            .insert(parent.clone());
    }
    Descriptors {
        names,
        parents: unanimous(parent_votes),
    }
}

/// Keeps the entries whose votes name exactly one thing.
///
/// # Arguments
///
/// * `votes` - Candidates per key.
pub(super) fn unanimous<K: Ord, V: Ord>(votes: BTreeMap<K, BTreeSet<V>>) -> BTreeMap<K, V> {
    votes
        .into_iter()
        .filter_map(|(k, mut v)| {
            let first = v.pop_first()?;
            v.is_empty().then_some((k, first))
        })
        .collect()
}

/// Collects, per function, the qualified-name literals and the writable
/// string-free objects it references.
///
/// # Arguments
///
/// * `program` - Sections and bytes.
/// * `analysis` - Reference sites by target.
///
/// # Returns
///
/// Literals by function and object addresses by function.
fn references(program: &Program, analysis: &Analysis) -> (ByFunction<String>, ByFunction<u64>) {
    let mut names_by_fn: ByFunction<String> = BTreeMap::new();
    let mut objects_by_fn: ByFunction<u64> = BTreeMap::new();
    for (&target, sites) in &analysis.xrefs {
        let Some(section) = program.section_at(target) else {
            continue;
        };
        if section.executable || !section.readable {
            continue;
        }
        let text = cstr_at(program, target, 4, NAME_MAX).map(|(_, t)| t);
        let name = text.as_deref().and_then(|t| {
            if is_qualified_name(t) {
                Some(t)
            } else {
                analysis.classes.registered_as.get(t).map(String::as_str)
            }
        });
        let object = section.writable && text.is_none();
        if name.is_none() && !object {
            continue;
        }
        for from in data_referrers(sites) {
            if let Some(n) = name {
                names_by_fn.entry(from).or_default().insert(n.to_owned());
            }
            if object {
                objects_by_fn.entry(from).or_default().insert(target);
            }
        }
    }
    (names_by_fn, objects_by_fn)
}

/// Indexes the named objects by the function referencing them.
///
/// # Arguments
///
/// * `analysis` - Reference sites by target.
/// * `named` - Object names from [`find`].
///
/// # Returns
///
/// Function entry to the named objects it references.
pub(super) fn objects_by_function(
    analysis: &Analysis,
    named: &BTreeMap<u64, String>,
) -> BTreeMap<u64, BTreeSet<u64>> {
    let mut out: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
    for &object in named.keys() {
        for from in data_referrers(analysis.xrefs_to(object)) {
            out.entry(from).or_default().insert(object);
        }
    }
    out
}

/// Names the class of a table from the descriptors its creators reference.
///
/// A creator is a caller of one of the table's constructors that stores no
/// table itself (a derived constructor calling its base is none).
///
/// # Arguments
///
/// * `analysis` - Functions with their callers.
/// * `named` - Object names from [`find`].
/// * `parents` - Class parents from [`find`].
/// * `described` - Named objects by function from [`objects_by_function`].
/// * `ctors` - The constructors storing the table.
/// * `is_ctor` - Whether a function stores a table.
///
/// # Returns
///
/// The class name when every creator's descriptor agrees on one or, when
/// they name several, the one every other descends from (a derived class's
/// creator inlines its own constructor and calls the base's, so it votes
/// for the base's table too).
pub(super) fn class_name(
    analysis: &Analysis,
    named: &BTreeMap<u64, String>,
    parents: &BTreeMap<String, String>,
    described: &BTreeMap<u64, BTreeSet<u64>>,
    ctors: &[u64],
    is_ctor: &dyn Fn(u64) -> bool,
) -> Option<String> {
    let mut found: BTreeSet<&str> = BTreeSet::new();
    for &ctor in ctors {
        let Some(f) = analysis.function(ctor) else {
            continue;
        };
        for &caller in &f.callers {
            if is_ctor(caller) {
                continue;
            }
            for object in described.get(&caller).into_iter().flatten() {
                if let Some(n) = named.get(object) {
                    found.insert(n);
                }
            }
        }
    }
    let found: Vec<&str> = found.into_iter().collect();
    match found.as_slice() {
        [name] => Some((*name).to_owned()),
        [] => None,
        several => common_ancestor(several, parents).map(str::to_owned),
    }
}

/// The class every other one descends from, when exactly one does.
///
/// # Arguments
///
/// * `classes` - Class names.
/// * `parents` - Class name to parent name.
fn common_ancestor<'a>(classes: &[&'a str], parents: &BTreeMap<String, String>) -> Option<&'a str> {
    let descends = |from: &str, to: &str| {
        let mut at = parents.get(from);
        for _ in 0..ANCESTORS_MAX {
            match at {
                Some(p) if p == to => return true,
                Some(p) => at = parents.get(p),
                None => return false,
            }
        }
        false
    };
    let mut roots = classes
        .iter()
        .copied()
        .filter(|c| classes.iter().all(|v| v == c || descends(v, c)));
    let root = roots.next()?;
    roots.next().is_none().then_some(root)
}

/// Names the class of a table from the descriptors its creators reference
/// themselves.
///
/// A factory that constructs the instance in place references the one
/// descriptor it allocates from; a creator referencing several named
/// descriptors (a type check beside an allocation) votes nowhere, and the
/// voters must agree on one name.
///
/// # Arguments
///
/// * `named` - Object names from [`find`].
/// * `described` - Named objects by function from [`objects_by_function`].
/// * `creators` - The creators storing the table.
pub(super) fn creator_name(
    named: &BTreeMap<u64, String>,
    described: &BTreeMap<u64, BTreeSet<u64>>,
    creators: &[u64],
) -> Option<String> {
    let mut found: BTreeSet<&str> = BTreeSet::new();
    for creator in creators {
        let names = described
            .get(creator)
            .into_iter()
            .flatten()
            .filter_map(|object| named.get(object));
        if let Some(n) = single(names) {
            found.insert(n);
        }
    }
    single(found).map(str::to_owned)
}

/// Qualifies the bare class names registrations spelled.
///
/// A class registered from inside its namespace spells only its own name
/// (`ActorCommand`, `'ACCO'`), where signatures, templates and other
/// registrations call it `Commands::ActorCommand`. Every qualified name the
/// function names and the registrations carry, and each class prefix of
/// one, is indexed by its last component; a bare registered name exactly
/// one of them ends in takes that name in
/// [`ClassFacts::ids`](super::ClassFacts::ids), and
/// [`ClassFacts::registered_as`](super::ClassFacts::registered_as) keeps
/// the spelling for the descriptors a registration names. A bare name no
/// qualified name ends in, or several do, stays as it is.
///
/// # Arguments
///
/// * `analysis` - Function names and registrations; rewritten in place.
pub(super) fn qualify_registrations(analysis: &mut Analysis) {
    let names = analysis.functions.iter().filter_map(|f| f.name.as_deref());
    let renames = qualified_registrations(names, &analysis.classes.ids);
    for (bare, qualified) in renames {
        if let Some(code) = analysis.classes.ids.remove(&bare) {
            analysis.classes.ids.insert(qualified.clone(), code);
            analysis.classes.registered_as.insert(bare, qualified);
        }
    }
}

/// The qualified name each bare registered class name takes
/// ([`qualify_registrations`]), bare name first.
///
/// # Arguments
///
/// * `names` - The function names in the program.
/// * `class_ids` - The registered classes.
fn qualified_registrations<'a>(
    names: impl Iterator<Item = &'a str>,
    class_ids: &BTreeMap<String, u32>,
) -> BTreeMap<String, String> {
    let mut by_last: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut add = |q: &str| {
        if let Some((_, last)) = q.rsplit_once("::")
            && !last.is_empty()
        {
            by_last
                .entry(last.to_owned())
                .or_default()
                .insert(q.to_owned());
        }
    };
    for name in names {
        for run in qualified_runs(name) {
            add(run);
            if let Some(class) = super::classes::class_of(run) {
                add(class);
            }
        }
    }
    for key in class_ids.keys().filter(|k| k.contains("::")) {
        add(key);
    }
    let mut out = BTreeMap::new();
    for name in class_ids.keys().filter(|k| !k.contains("::")) {
        if let Some(qualified) = by_last.get(name).and_then(single)
            && !class_ids.contains_key(qualified)
        {
            out.insert(name.clone(), qualified.clone());
        }
    }
    out
}

/// The qualified names spelled in a function's name.
///
/// Every run of identifier characters and `::` that joins two or more
/// components counts, so `Core::Ptr<Commands::ActorCommand>::operator ->`
/// spells `Core::Ptr` and `Commands::ActorCommand`.
///
/// # Arguments
///
/// * `name` - A function name.
fn qualified_runs(name: &str) -> impl Iterator<Item = &str> {
    name.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == ':'))
        .map(|run| run.trim_matches(':'))
        .filter(|run| is_qualified_name(run))
}

/// Tells whether a literal is a qualified class name: two or more
/// identifier components joined by `::`.
///
/// # Arguments
///
/// * `text` - The literal.
fn is_qualified_name(text: &str) -> bool {
    let mut parts = text.split("::").peekable();
    let mut count = 0;
    while let Some(part) = parts.next() {
        let mut chars = part.chars();
        let head = chars
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_');
        if !head || !chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return false;
        }
        count += 1;
        if parts.peek().is_none() {
            break;
        }
    }
    count >= 2
}

#[cfg(test)]
mod tests {
    use super::is_qualified_name;
    use std::collections::BTreeMap;

    /// A bare registered name takes the one qualified name the program
    /// spells for it, in a template argument or a method's class; a name
    /// two namespaces spell, or none, stays bare.
    ///
    /// # Panics
    ///
    /// When a name is qualified against the rule.
    #[test]
    fn bare_registered_names_take_their_qualified_name() {
        let runs: Vec<&str> =
            super::qualified_runs("Core::Ptr<Commands::ActorCommand>::operator ->").collect();
        assert_eq!(runs, vec!["Core::Ptr", "Commands::ActorCommand"]);
        let names = [
            "Core::Ptr<Commands::ActorCommand>::operator ->",
            "Game::Inventory::GetItems",
            "UI::Widget::Load",
            "Game::Widget::Load",
        ];
        let ids: BTreeMap<String, u32> = [
            ("ActorCommand".to_owned(), 1),
            ("Inventory".to_owned(), 2),
            ("Widget".to_owned(), 3),
            ("Lonely".to_owned(), 4),
        ]
        .into();
        let out = super::qualified_registrations(names.into_iter(), &ids);
        assert_eq!(
            out,
            [
                (
                    "ActorCommand".to_owned(),
                    "Commands::ActorCommand".to_owned()
                ),
                ("Inventory".to_owned(), "Game::Inventory".to_owned()),
            ]
            .into()
        );
    }

    /// Qualified names have two or more identifier components; prose,
    /// signatures and single identifiers do not qualify.
    ///
    /// # Panics
    ///
    /// When a literal is classified against its expectation.
    #[test]
    fn qualified_names_are_recognized() {
        assert!(is_qualified_name("Properties::HeroLightProperty"));
        assert!(is_qualified_name("A::B::C_1"));
        assert!(!is_qualified_name("Thing"));
        assert!(!is_qualified_name("Ns::"));
        assert!(!is_qualified_name("void __cdecl A::B(void)"));
        assert!(!is_qualified_name("Ns::9x"));
    }
}
