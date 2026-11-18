//! Class families: the classes whose tables hold the same function at the
//! same slot, and the slot names one member gives the others.
//!
//! Two tables of one slot count that hold one function at one index hold
//! the same virtual there: neither class overrode it, so both inherit it
//! from a base whose table reaches that index, and every slot up to it is
//! that base's virtual in both, unless the function is a stub: one the
//! tables hold at several indexes or in more than [`BUCKET_MAX`] tables,
//! or one named as the pure-call handler. Tables that agree so at
//! [`ANCHORS_MIN`] indexes are one family. A member's name for slot `k` is a hint for
//! another member's slot `k` only when `k` is below the table of a parent
//! the constructors name for both, or, with no such parent known, when the
//! two share an anchor at `k` or above: past that, two siblings' slots `k`
//! may be each one's own new virtual. The guards of
//! [`super::propagate_slot_names`] hold too: a name the class already
//! gives another slot does not travel, nor one whose
//! function differs in shape from nearly every function at that slot. A
//! slot keeps a hint only when every member that gives one agrees;
//! disagreement is reported, not resolved, and nothing is renamed.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::Arc;

use super::ClassInfo;
use super::names::method_part;
use crate::analysis::{Analysis, Overlay, name_of, slot_name_of};
use crate::sets::Sets;

/// Fewest indexes two tables must hold one function at to be one family.
const ANCHORS_MIN: usize = 2;
/// Most tables one `(index, function)` may be shared by and still link them.
///
/// A function more tables hold at one index is a common stub (an error
/// handler, a folded `return 0`), not a sign of one hierarchy.
const BUCKET_MAX: usize = 64;
/// Most pair counts the linking adds up over the whole program.
const PAIR_WORK_MAX: usize = 1 << 22;
/// Most members a family line names.
const MEMBERS_SHOWN: usize = 8;
/// Most classes a slot note names as spelling one name.
const SPELLERS_SHOWN: usize = 3;

/// The program's families, each sorted, by class.
#[derive(Debug, Default)]
struct Families {
    /// Each family's members, sorted; every family has two or more.
    groups: Vec<Vec<String>>,
    /// The family index of each member.
    of: BTreeMap<String, usize>,
    /// The linking stopped at [`PAIR_WORK_MAX`], so a family may miss
    /// members.
    capped: bool,
    /// The functions no table holds as an anchor: [`slot_stubs`] and the
    /// ones named as the pure-call handler ([`reports_pure_call`]).
    stubs: BTreeSet<u64>,
}

/// The members that spell a slot one way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spellers {
    /// The first [`SPELLERS_SHOWN`] of them, in name order.
    pub shown: Vec<String>,
    /// How many there are.
    pub count: usize,
}

/// What a family says of one slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlotName {
    /// Every member that names the slot names it so: the method and the
    /// members that spell it.
    Agreed(String, Spellers),
    /// Members spell the slot differently: the first [`MEMBERS_SHOWN`]
    /// methods with their members, and how many methods there are.
    Disputed(Vec<(String, Spellers)>, usize),
}

/// One class's family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Family {
    /// The first [`MEMBERS_SHOWN`] other members in name order, each with
    /// how many anchors (a function each table holds at that index alone)
    /// it shares with the class's own.
    pub members: Vec<(String, usize)>,
    /// How many other members there are.
    pub member_count: usize,
    /// The slot count every member's table has.
    pub slots: usize,
    /// The linking stopped at its work cap, so members may be missing.
    pub capped: bool,
    /// What the family names each slot, by index; a slot no member names
    /// is absent.
    pub names: BTreeMap<usize, SlotName>,
}

/// Returns the functions no table holds as an anchor: each one the
/// tables hold at two or more slot indexes, or more than `tables_max`
/// tables hold.
///
/// A virtual a hierarchy shares sits at one index in every table that
/// inherits it; the stub of a pure virtual slot, or a folded `return 0`,
/// fills slots at any index in unrelated classes.
///
/// # Arguments
///
/// * `classes` - Classes with their tables.
/// * `tables_max` - Most tables one function may be held by and still be
///   an anchor.
pub(crate) fn slot_stubs(
    classes: &BTreeMap<String, ClassInfo>,
    tables_max: usize,
) -> BTreeSet<u64> {
    let mut seen: BTreeMap<u64, (BTreeSet<usize>, usize)> = BTreeMap::new();
    for info in classes.values() {
        for (i, &f) in info.slots.iter().enumerate() {
            let (at, held) = seen.entry(f).or_default();
            at.insert(i);
            *held += 1;
        }
    }
    seen.into_iter()
        .filter(|(_, (at, held))| at.len() >= 2 || *held > tables_max)
        .map(|(f, _)| f)
        .collect()
}

/// Tells whether a function's name says it reports a pure virtual call
/// (`_purecall`).
///
/// # Arguments
///
/// * `name` - The function's name.
pub(crate) fn reports_pure_call(name: &str) -> bool {
    name.to_ascii_lowercase().contains("purecall")
}

/// Returns the functions a table holds that it can share as anchors:
/// none of the program's stubs ([`slot_stubs`]), and no `0`, which is
/// data.
///
/// # Arguments
///
/// * `slots` - The table's slots.
/// * `stubs` - The program's stubs.
fn anchors(slots: &[u64], stubs: &BTreeSet<u64>) -> BTreeSet<u64> {
    slots
        .iter()
        .copied()
        .filter(|f| *f != 0 && !stubs.contains(f))
        .collect()
}

/// Groups the classes into families.
///
/// # Arguments
///
/// * `analysis` - Classes with their tables, and function names.
/// * `overlay` - User names, which may name the pure-call handler.
fn families(analysis: &Analysis, overlay: &Overlay) -> Families {
    let classes = &analysis.classes.by_name;
    let names: Vec<&String> = classes.keys().collect();
    let mut stubs = slot_stubs(classes, BUCKET_MAX);
    let slots: BTreeSet<u64> = classes
        .values()
        .flat_map(|c| c.slots.iter().copied())
        .collect();
    stubs.extend(
        slots
            .into_iter()
            .filter(|&f| f != 0 && reports_pure_call(&name_of(analysis, overlay, f))),
    );
    let mut held: Vec<(usize, usize, u64, usize)> = Vec::new();
    for (at, info) in classes.values().enumerate() {
        if info.vtable.is_none() {
            continue;
        }
        let once = anchors(&info.slots, &stubs);
        for (k, &f) in info.slots.iter().enumerate() {
            if once.contains(&f) {
                held.push((info.slots.len(), k, f, at));
            }
        }
    }
    held.sort_unstable();
    let mut pairs: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    let mut work = 0usize;
    let mut capped = false;
    for bucket in held.chunk_by(|x, y| (x.0, x.1, x.2) == (y.0, y.1, y.2)) {
        if !(2..=BUCKET_MAX).contains(&bucket.len()) {
            continue;
        }
        for (i, a) in bucket.iter().enumerate() {
            for b in bucket.iter().skip(i + 1) {
                work += 1;
                if work > PAIR_WORK_MAX {
                    capped = true;
                    break;
                }
                *pairs.entry((a.3, b.3)).or_default() += 1;
            }
        }
    }
    let mut sets = Sets::new(names.len());
    let mut linked: BTreeSet<usize> = BTreeSet::new();
    for (&(a, b), _) in pairs.iter().filter(|&(_, &n)| n >= ANCHORS_MIN) {
        sets.union(a, b);
        linked.extend([a, b]);
    }
    let mut grouped: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for &at in &linked {
        if let Some(name) = names.get(at) {
            grouped
                .entry(sets.find(at))
                .or_default()
                .push((*name).clone());
        }
    }
    let mut out = Families {
        capped,
        stubs,
        ..Families::default()
    };
    for members in grouped.into_values() {
        for m in &members {
            out.of.insert(m.clone(), out.groups.len());
        }
        out.groups.push(members);
    }
    out
}

/// Returns the family of `class`, with the names its members give each
/// slot.
///
/// A member's name counts for slot `k` when the function its table holds
/// there has a method name ([`method_part`]) that is not a `vfunc_` index
/// name (constructors, destructors and disambiguated names do not count),
/// the member reaches `k` ([`reach`]), the class gives that method name to
/// no other slot, and the function is not the odd shape out at its slot
/// ([`super::names::dominant_shapes`]).
///
/// # Arguments
///
/// * `analysis` - Classes and function names.
/// * `overlay` - User names, which count as a member's names.
/// * `class` - The class.
///
/// # Returns
///
/// The family, shared with the memo, or `None` when the class shares no
/// family.
#[must_use]
pub fn family_of(analysis: &Analysis, overlay: &Overlay, class: &str) -> Option<Arc<Family>> {
    let built = analysis.derived.get_or_build_item(
        "vtable_family",
        overlay.fingerprint(),
        class.to_owned(),
        || build_family(analysis, overlay, class).map(Arc::new),
        |fam| fam.as_deref().map_or(0, weight),
    );
    (*built).clone()
}

/// Returns the bytes a family holds beyond its own size.
///
/// # Arguments
///
/// * `fam` - The family.
fn weight(fam: &Family) -> usize {
    let spelled = |s: &Spellers| {
        s.shown.capacity() * size_of::<String>()
            + s.shown.iter().map(String::capacity).sum::<usize>()
    };
    let slot = |v: &SlotName| match v {
        SlotName::Agreed(m, s) => m.capacity() + spelled(s),
        SlotName::Disputed(all, _) => {
            all.capacity() * size_of::<(String, Spellers)>()
                + all
                    .iter()
                    .map(|(m, s)| m.capacity() + spelled(s))
                    .sum::<usize>()
        }
    };
    size_of::<Family>()
        + fam.members.capacity() * size_of::<(String, usize)>()
        + fam.members.iter().map(|(m, _)| m.capacity()).sum::<usize>()
        + fam
            .names
            .values()
            .map(|v| size_of::<(usize, SlotName)>() + slot(v))
            .sum::<usize>()
}

/// Returns the first [`SPELLERS_SHOWN`] of some members, with their count.
///
/// # Arguments
///
/// * `by` - The members, in name order.
fn spellers(by: &[&str]) -> Spellers {
    Spellers {
        shown: by
            .iter()
            .take(SPELLERS_SHOWN)
            .map(|m| (*m).to_owned())
            .collect(),
        count: by.len(),
    }
}

/// Builds what [`family_of`] returns.
///
/// # Arguments
///
/// * `analysis`, `overlay`, `class` - As for [`family_of`].
fn build_family(analysis: &Analysis, overlay: &Overlay, class: &str) -> Option<Family> {
    let classes = &analysis.classes.by_name;
    let all =
        analysis
            .derived
            .get_or_build_named("vtable_families", overlay.fingerprint(), (), || {
                families(analysis, overlay)
            });
    let group = all.groups.get(*all.of.get(class)?)?;
    let own = classes.get(class)?;
    let shapes = analysis.derived.get_or_build("vtable_slot_shapes", (), || {
        super::names::dominant_shapes(analysis, classes)
    });
    let method_at = |f: u64| {
        (f != 0)
            .then(|| method_part(Some(&name_of(analysis, overlay, f))))
            .flatten()
            .filter(|m| !m.starts_with("vfunc_"))
    };
    let own_methods: Vec<Option<String>> = own.slots.iter().map(|&f| method_at(f)).collect();
    let mut votes: BTreeMap<usize, BTreeMap<String, Vec<&str>>> = BTreeMap::new();
    let mut members = Vec::new();
    let mut member_count = 0usize;
    let own_anchors = anchors(&own.slots, &all.stubs);
    for m in group.iter().filter(|m| *m != class) {
        let Some(info) = classes.get(m) else {
            continue;
        };
        let theirs = anchors(&info.slots, &all.stubs);
        let anchor = |f: u64| own_anchors.contains(&f) && theirs.contains(&f);
        let shared = info
            .slots
            .iter()
            .zip(&own.slots)
            .filter(|(a, b)| a == b && anchor(**a))
            .count();
        member_count += 1;
        if members.len() < MEMBERS_SHOWN {
            members.push((m.clone(), shared));
        }
        let limit = reach(classes, own, info, &anchor);
        for (k, &f) in info.slots.iter().enumerate().take(limit) {
            let Some(method) = method_at(f) else {
                continue;
            };
            let elsewhere = own_methods
                .iter()
                .enumerate()
                .any(|(j, o)| j != k && o.as_deref() == Some(method.as_str()));
            let odd = shapes
                .get(&(super::names::introducer(classes, m, k), k))
                .is_some_and(|&shape| analysis.function(f).is_some_and(|x| x.shape_hash != shape));
            if elsewhere || odd {
                continue;
            }
            votes
                .entry(k)
                .or_default()
                .entry(method)
                .or_default()
                .push(m.as_str());
        }
    }
    let names = votes
        .into_iter()
        .map(|(k, spelled)| {
            let count = spelled.len();
            let mut spelled = spelled.into_iter().map(|(m, by)| (m, spellers(&by)));
            let verdict = match (count, spelled.next()) {
                (1, Some((method, by))) => SlotName::Agreed(method, by),
                (_, first) => SlotName::Disputed(
                    first
                        .into_iter()
                        .chain(spelled)
                        .take(MEMBERS_SHOWN)
                        .collect(),
                    count,
                ),
            };
            (k, verdict)
        })
        .collect();
    Some(Family {
        members,
        member_count,
        slots: own.slots.len(),
        capped: all.capped,
        names,
    })
}

/// Returns how many of `own`'s slots `member`'s names are hints for.
///
/// That is the length of a parent's table the constructors name for both,
/// which also bounds what they inherit: an anchor past it is a function
/// each added on its own. With no such parent known, it is up to and
/// including the last index the two tables share an anchor at. A stub
/// shares nothing ([`slot_stubs`],
/// [`reports_pure_call`]): two siblings each fill their own new slots with
/// it.
///
/// # Arguments
///
/// * `classes` - Classes with their tables and parents.
/// * `own` - The class being named.
/// * `member` - The member whose names would travel.
/// * `anchor` - Whether a function is an anchor of both tables
///   ([`anchors`]).
fn reach(
    classes: &BTreeMap<String, ClassInfo>,
    own: &ClassInfo,
    member: &ClassInfo,
    anchor: &dyn Fn(u64) -> bool,
) -> usize {
    let shared = member
        .slots
        .iter()
        .zip(&own.slots)
        .rposition(|(a, b)| a == b && anchor(*a))
        .map_or(0, |k| k + 1);
    let parent = own
        .parent
        .as_ref()
        .filter(|p| member.parent.as_ref() == Some(*p) || **p == member.name)
        .and_then(|p| classes.get(p))
        .filter(|p| p.vtable.is_some())
        .map(|p| p.slots.len());
    parent.unwrap_or(shared)
}

/// Renders a class's table for its layout: a line per slot, the first
/// `shown`, each with what its family names it.
///
/// A slot whose own function has no method name shows, as a hint, the name
/// the members that reach it agree on ([`family_of`]); a slot they spell
/// two ways shows every spelling. The family line before the slots says
/// who the members are and how many slots each shares.
///
/// # Arguments
///
/// * `analysis` - Classes and names.
/// * `overlay` - User names.
/// * `info` - The class.
/// * `shown` - Most slots listed.
///
/// # Returns
///
/// The lines, empty when the class has no table.
#[must_use]
pub fn render_slots(
    analysis: &Analysis,
    overlay: &Overlay,
    info: &ClassInfo,
    shown: usize,
) -> String {
    let mut out = String::new();
    let Some(v) = info.vtable else {
        return out;
    };
    let _ = writeln!(out, "vftable: {v:#x} ({} slots)", info.slots.len());
    let family = family_of(analysis, overlay, &info.name);
    if let Some(fam) = &family {
        let listed: Vec<String> = fam
            .members
            .iter()
            .map(|(m, n)| format!("{m} ({n} shared)"))
            .collect();
        let more = fam.member_count.saturating_sub(fam.members.len());
        let _ = writeln!(
            out,
            "family: {}{}; each {}-slot table holds the same function at the shared slots, so a member's name for a slot at or below the last one it shares is a hint for this one",
            listed.join(", "),
            if more > 0 {
                format!(", +{more}")
            } else {
                String::new()
            },
            fam.slots
        );
        if fam.capped {
            out.push_str(
                "family: the linking stopped at its work cap, so members may be missing\n",
            );
        }
    }
    for (i, &s) in info.slots.iter().enumerate().take(shown) {
        let own = slot_name_of(analysis, overlay, s);
        let note = family
            .as_ref()
            .and_then(|fam| fam.names.get(&i))
            .and_then(|verdict| slot_note(verdict, &own))
            .unwrap_or_default();
        let _ = writeln!(out, "  [{i}] {own}{note}");
    }
    if info.slots.len() > shown {
        let _ = writeln!(out, "  ... {} more", info.slots.len() - shown);
    }
    out
}

/// Returns the note a slot line ends with, `None` when the family adds
/// nothing to the slot's own name.
///
/// # Arguments
///
/// * `verdict` - What the family names the slot.
/// * `own` - The slot's own name.
fn slot_note(verdict: &SlotName, own: &str) -> Option<String> {
    let by = |s: &Spellers| {
        let more = s.count.saturating_sub(s.shown.len());
        let tail = if more > 0 {
            format!(", +{more}")
        } else {
            String::new()
        };
        format!("{}{tail}", s.shown.join(", "))
    };
    match verdict {
        SlotName::Agreed(method, members) => {
            let named = method_part(Some(own)).is_some_and(|m| !m.starts_with("vfunc_"));
            let verb = if members.count == 1 { "names" } else { "name" };
            (!named).then(|| format!("  {} {verb} this slot {method}", by(members)))
        }
        SlotName::Disputed(spelled, count) => {
            let list: Vec<String> = spelled
                .iter()
                .map(|(m, members)| format!("{m} ({})", by(members)))
                .collect();
            let more = count.saturating_sub(spelled.len());
            let tail = if more > 0 {
                format!(", +{more} more")
            } else {
                String::new()
            };
            Some(format!(
                "  members name this slot differently: {}{tail}",
                list.join(", ")
            ))
        }
    }
}
