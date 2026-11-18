//! Class families: the classes whose tables hold the same function at the
//! same slot, and the slot names one member gives the others.
//!
//! Two tables of one slot count that hold one function at one index hold
//! the same virtual there: neither class overrode it, so both inherit it
//! from a base whose table reaches that index, and every slot up to it is
//! that base's virtual in both. Tables that agree so at [`ANCHORS_MIN`]
//! indexes are one family. A member's name for slot `k` is a hint for
//! another member's slot `k` only when the two share a function at `k` or
//! above, or `k` is below the table of a parent the constructors name for
//! both: past that, two siblings' slots `k` may be each one's own new
//! virtual. The guards of [`super::propagate_slot_names`] hold too: a name
//! the class already gives another slot does not travel, nor one whose
//! function differs in shape from nearly every function at that slot. A
//! slot keeps a hint only when every member that gives one agrees;
//! disagreement is reported, not resolved, and nothing is renamed.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

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
}

/// What a family says of one slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlotName {
    /// Every member that names the slot names it so: the method and the
    /// members that spell it.
    Agreed(String, Vec<String>),
    /// Members spell the slot differently: each method with its members.
    Disputed(Vec<(String, Vec<String>)>),
}

/// One class's family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Family {
    /// The other members, each with how many anchors (a function each
    /// table holds at that index alone) it shares with the class's own.
    pub members: Vec<(String, usize)>,
    /// The slot count every member's table has.
    pub slots: usize,
    /// The linking stopped at its work cap, so members may be missing.
    pub capped: bool,
    /// What the family names each slot, by index; a slot no member names
    /// is absent.
    pub names: BTreeMap<usize, SlotName>,
}

/// Returns the functions a table holds at one index only, the anchors it
/// can share: a function at two indexes is a stub, and a `0` is data.
///
/// # Arguments
///
/// * `slots` - The table's slots.
fn anchors(slots: &[u64]) -> BTreeSet<u64> {
    let mut seen: BTreeMap<u64, usize> = BTreeMap::new();
    for &f in slots {
        *seen.entry(f).or_default() += 1;
    }
    seen.into_iter()
        .filter(|&(f, n)| f != 0 && n == 1)
        .map(|(f, _)| f)
        .collect()
}

/// Groups the classes into families.
///
/// # Arguments
///
/// * `classes` - Classes with their tables.
fn families(classes: &BTreeMap<String, ClassInfo>) -> Families {
    let names: Vec<&String> = classes.keys().collect();
    let mut held: Vec<(usize, usize, u64, usize)> = Vec::new();
    for (at, info) in classes.values().enumerate() {
        if info.vtable.is_none() {
            continue;
        }
        let once = anchors(&info.slots);
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
/// The family, or `None` when the class shares no family.
#[must_use]
pub fn family_of(analysis: &Analysis, overlay: &Overlay, class: &str) -> Option<Family> {
    let built = analysis.derived.get_or_build_named(
        "vtable_family",
        overlay.fingerprint(),
        class.to_owned(),
        || build_family(analysis, overlay, class),
    );
    (*built).clone()
}

/// Builds what [`family_of`] returns.
///
/// # Arguments
///
/// * `analysis`, `overlay`, `class` - As for [`family_of`].
fn build_family(analysis: &Analysis, overlay: &Overlay, class: &str) -> Option<Family> {
    let classes = &analysis.classes.by_name;
    let all = analysis
        .derived
        .get_or_build("vtable_families", (), || families(classes));
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
    let mut votes: BTreeMap<usize, BTreeMap<String, Vec<String>>> = BTreeMap::new();
    let mut members = Vec::new();
    let own_anchors = anchors(&own.slots);
    for m in group.iter().filter(|m| *m != class) {
        let Some(info) = classes.get(m) else {
            continue;
        };
        let theirs = anchors(&info.slots);
        let shared = info
            .slots
            .iter()
            .zip(&own.slots)
            .filter(|(a, b)| a == b && own_anchors.contains(a) && theirs.contains(a))
            .count();
        members.push((m.clone(), shared));
        let limit = reach(classes, own, info);
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
                .push(m.clone());
        }
    }
    let names = votes
        .into_iter()
        .map(|(k, spelled)| {
            let mut spelled: Vec<(String, Vec<String>)> = spelled.into_iter().collect();
            let verdict = match spelled.len() {
                1 => {
                    let (method, by) = spelled.remove(0);
                    SlotName::Agreed(method, by)
                }
                _ => SlotName::Disputed(spelled),
            };
            (k, verdict)
        })
        .collect();
    Some(Family {
        members,
        slots: own.slots.len(),
        capped: all.capped,
        names,
    })
}

/// Returns how many of `own`'s slots `member`'s names are hints for.
///
/// That is up to and including the last index the two tables hold one
/// function at, or the length of a parent's table the constructors name
/// for both, the larger.
///
/// # Arguments
///
/// * `classes` - Classes with their tables and parents.
/// * `own` - The class being named.
/// * `member` - The member whose names would travel.
fn reach(classes: &BTreeMap<String, ClassInfo>, own: &ClassInfo, member: &ClassInfo) -> usize {
    let shared = member
        .slots
        .iter()
        .zip(&own.slots)
        .rposition(|(a, b)| *a != 0 && a == b)
        .map_or(0, |k| k + 1);
    let parent = own
        .parent
        .as_ref()
        .filter(|p| member.parent.as_ref() == Some(*p) || **p == member.name)
        .and_then(|p| classes.get(p))
        .map_or(0, |p| p.slots.len());
    shared.max(parent)
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
            .take(MEMBERS_SHOWN)
            .map(|(m, n)| format!("{m} ({n} shared)"))
            .collect();
        let more = fam.members.len().saturating_sub(MEMBERS_SHOWN);
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
    let by = |members: &[String]| {
        let s: Vec<&str> = members
            .iter()
            .take(SPELLERS_SHOWN)
            .map(String::as_str)
            .collect();
        let more = members.len().saturating_sub(SPELLERS_SHOWN);
        let tail = if more > 0 {
            format!(", +{more}")
        } else {
            String::new()
        };
        format!("{}{tail}", s.join(", "))
    };
    match verdict {
        SlotName::Agreed(method, members) => {
            let named = method_part(Some(own)).is_some_and(|m| !m.starts_with("vfunc_"));
            let verb = if members.len() == 1 { "names" } else { "name" };
            (!named).then(|| format!("  {} {verb} this slot {method}", by(members)))
        }
        SlotName::Disputed(spelled) => {
            let list: Vec<String> = spelled
                .iter()
                .map(|(m, members)| format!("{m} ({})", by(members)))
                .collect();
            Some(format!(
                "  members name this slot differently: {}",
                list.join(", ")
            ))
        }
    }
}
