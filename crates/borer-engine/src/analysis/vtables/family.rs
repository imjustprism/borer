//! Class families: the classes whose tables hold the same function at the
//! same slot, and the slot names one member gives the others.
//!
//! Two tables of one slot count that hold one function at one index hold
//! the same virtual there: neither class overrode it. Tables that agree so
//! at [`ANCHORS_MIN`] indexes are aligned slot for slot, so a name any
//! member gives index `k` names slot `k` in all of them, the abstract
//! base's included, whose own entry is a stub no assert names. This finds
//! siblings the constructors never link: the parent links of
//! [`super::propagate_slot_names`] join tables of different lengths, a
//! family joins tables of one length. A slot keeps a name only when every
//! member that spells one agrees; disagreement is reported, not resolved,
//! and nothing is renamed.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::ClassInfo;
use super::names::method_part;
use crate::analysis::{Analysis, Overlay, name_of, slot_name_of};

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
    /// The other members, each with how many indexes its table holds the
    /// same function at as the class's own.
    pub members: Vec<(String, usize)>,
    /// The slot count every member's table has.
    pub slots: usize,
    /// What the family names each slot, by index; a slot no member names
    /// is absent.
    pub names: BTreeMap<usize, SlotName>,
}

/// Groups the classes into families.
///
/// # Arguments
///
/// * `classes` - Classes with their tables.
fn families(classes: &BTreeMap<String, ClassInfo>) -> Families {
    let names: Vec<&String> = classes.keys().collect();
    let mut buckets: BTreeMap<(usize, usize, u64), Vec<usize>> = BTreeMap::new();
    for (at, info) in classes.values().enumerate() {
        if info.vtable.is_none() {
            continue;
        }
        let mut seen: BTreeMap<u64, usize> = BTreeMap::new();
        for &f in &info.slots {
            *seen.entry(f).or_default() += 1;
        }
        for (k, &f) in info.slots.iter().enumerate() {
            if f != 0 && seen.get(&f) == Some(&1) {
                buckets
                    .entry((info.slots.len(), k, f))
                    .or_default()
                    .push(at);
            }
        }
    }
    let mut pairs: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    let mut work = 0usize;
    for members in buckets
        .values()
        .filter(|m| (2..=BUCKET_MAX).contains(&m.len()))
    {
        for (i, &a) in members.iter().enumerate() {
            for &b in members.iter().skip(i + 1) {
                work += 1;
                if work > PAIR_WORK_MAX {
                    break;
                }
                *pairs.entry((a, b)).or_default() += 1;
            }
        }
    }
    let mut parent: Vec<usize> = (0..names.len()).collect();
    let root = |parent: &[usize], mut at: usize| {
        while parent.get(at).is_some_and(|&up| up != at) {
            at = parent.get(at).copied().unwrap_or(at);
        }
        at
    };
    let mut linked: BTreeSet<usize> = BTreeSet::new();
    for (&(a, b), _) in pairs.iter().filter(|&(_, &n)| n >= ANCHORS_MIN) {
        let (ra, rb) = (root(&parent, a), root(&parent, b));
        if let Some(up) = parent.get_mut(ra.max(rb)) {
            *up = ra.min(rb);
        }
        linked.extend([a, b]);
    }
    let mut grouped: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for &at in &linked {
        if let Some(name) = names.get(at) {
            grouped
                .entry(root(&parent, at))
                .or_default()
                .push((*name).clone());
        }
    }
    let mut out = Families::default();
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
/// A member's name counts for a slot when the function its table holds
/// there has a method name ([`method_part`]) that is not a `vfunc_` index
/// name; constructors, destructors and disambiguated names do not count.
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
    let all = analysis.derived.get_or_build("vtable_families", (), || {
        families(&analysis.classes.by_name)
    });
    let group = all.groups.get(*all.of.get(class)?)?;
    let own = analysis.classes.by_name.get(class)?;
    let mut votes: BTreeMap<usize, BTreeMap<String, Vec<String>>> = BTreeMap::new();
    let mut members = Vec::new();
    for m in group {
        let Some(info) = analysis.classes.by_name.get(m) else {
            continue;
        };
        if m != class {
            let shared = info
                .slots
                .iter()
                .zip(&own.slots)
                .filter(|(a, b)| **a != 0 && a == b)
                .count();
            members.push((m.clone(), shared));
        }
        for (k, &f) in info.slots.iter().enumerate() {
            let Some(method) = (f != 0)
                .then(|| method_part(Some(&name_of(analysis, overlay, f))))
                .flatten()
                .filter(|m| !m.starts_with("vfunc_"))
            else {
                continue;
            };
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
        names,
    })
}

/// Renders a class's table for its layout: a line per slot, the first
/// `shown`, each with what its family names it.
///
/// A slot whose own function has no method name shows the name its family
/// agrees on; a slot the family spells two ways shows every spelling, and
/// stays unnamed. The family line before the slots says who the members
/// are and how many slots each shares.
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
            "family: {}{}; each {}-slot table holds the same function at those slots, so a name one member gives a slot names it in all",
            listed.join(", "),
            if more > 0 {
                format!(", +{more}")
            } else {
                String::new()
            },
            fam.slots
        );
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
            (!named).then(|| format!("  family names it {method} (spelled by {})", by(members)))
        }
        SlotName::Disputed(spelled) => {
            let list: Vec<String> = spelled
                .iter()
                .map(|(m, members)| format!("{m} ({})", by(members)))
                .collect();
            Some(format!(
                "  family disagrees: {}; left unnamed",
                list.join(", ")
            ))
        }
    }
}
