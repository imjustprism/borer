//! Senders: for every class that answers a vtable slot with a constant,
//! the functions that construct it, which is where a client sends each
//! command.
//!
//! A command travels from the code that decides to send it to the wire
//! through its factory: one function calls `Move::create`, another calls
//! `Ping::create`. Joining the slot
//! constants with the callers of each class's factories and constructors
//! answers "who sends this" for a whole protocol in one table, opcode by
//! opcode, without a search per class.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use super::vtables::slot_constants;
use super::{Analysis, Overlay, RefKind, name_of};
use crate::program::Program;

/// Most senders spelled out on one row.
const SENDERS_MAX: usize = 8;
/// Factories followed above a constructor: `create` calls the
/// constructor, a caller of `create` sends.
const FACTORY_DEPTH: usize = 3;

/// One class with the functions constructing it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sender {
    /// The constant the class answers the slot with.
    pub value: u64,
    /// The qualified class name.
    pub class: String,
    /// The outermost factory of the class's own: the function a sender
    /// calls to get an instance.
    pub factory: Option<u64>,
    /// Entries of the functions outside the class calling a factory or a
    /// constructor, sorted.
    pub senders: Vec<u64>,
    /// The call sites those functions send from: `(site, function entry)`,
    /// sorted by site.
    pub sites: Vec<(u64, u64)>,
}

/// Who constructs one class, as [`constructed_by`] finds them.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Constructed {
    /// The outermost factory of the class's own: the function a sender
    /// calls to get an instance.
    pub factory: Option<u64>,
    /// Entries of the functions outside the class calling a factory or a
    /// constructor, sorted.
    pub senders: Vec<u64>,
    /// The call sites those functions send from: `(site, function entry)`,
    /// sorted by site.
    pub sites: Vec<(u64, u64)>,
}

/// The call sites of any of `targets` in functions other than `own`, as
/// `(function entry, site)`.
///
/// # Arguments
///
/// * `analysis` - Discovery results with the cross-references.
/// * `targets` - The factories and constructors.
/// * `own` - Functions already accounted for.
fn callers_of(analysis: &Analysis, targets: &[u64], own: &BTreeSet<u64>) -> BTreeSet<(u64, u64)> {
    let mut out: BTreeSet<(u64, u64)> = BTreeSet::new();
    for target in targets {
        let Some(sites) = analysis.xrefs.get(target) else {
            continue;
        };
        out.extend(
            sites
                .iter()
                .filter(|site| site.kind == RefKind::Call)
                .filter_map(|site| site.from_entry.map(|from| (from, site.va)))
                .filter(|(from, _)| !own.contains(from)),
        );
    }
    out
}

/// Who constructs one class: its constructors' callers, a caller that is
/// a method of the class itself (`create`) being a factory followed in
/// turn rather than a sender.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `class` - The qualified class name.
///
/// # Returns
///
/// The outermost factory, the senders sorted, and their call sites; all
/// empty for a class the analysis does not know.
pub(crate) fn constructed_by(analysis: &Analysis, overlay: &Overlay, class: &str) -> Constructed {
    let Some(info) = analysis.classes.by_name.get(class) else {
        return Constructed::default();
    };
    let prefix = format!("{class}::");
    let mut own: BTreeSet<u64> = info
        .creators
        .iter()
        .chain(&info.ctors)
        .chain(&info.slots)
        .copied()
        .collect();
    let mut frontier: Vec<u64> = info.creators.iter().chain(&info.ctors).copied().collect();
    let mut factory = info.creators.first().or(info.ctors.first()).copied();
    let mut senders: BTreeSet<u64> = BTreeSet::new();
    let mut sites: BTreeSet<(u64, u64)> = BTreeSet::new();
    for _ in 0..FACTORY_DEPTH {
        if frontier.is_empty() {
            break;
        }
        let callers = callers_of(analysis, &frontier, &own);
        let mut next = Vec::new();
        for (caller, site) in callers {
            if name_of(analysis, overlay, caller).starts_with(&prefix) {
                if own.insert(caller) {
                    factory = Some(caller);
                    next.push(caller);
                }
            } else {
                senders.insert(caller);
                sites.insert((site, caller));
            }
        }
        for caller in &next {
            own.insert(*caller);
        }
        frontier = next;
    }
    Constructed {
        factory,
        senders: senders.into_iter().collect(),
        sites: sites.into_iter().collect(),
    }
}

/// Every class answering `slot` with a constant, with who constructs it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
/// * `slot` - The vtable index the constant sits in, zero-based.
///
/// # Returns
///
/// The rows ordered by constant, then class.
#[must_use]
pub fn senders(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    slot: usize,
) -> Vec<Sender> {
    let mut rows: Vec<Sender> = slot_constants(program, analysis, slot)
        .into_iter()
        .map(|c| {
            let built = constructed_by(analysis, overlay, &c.class);
            Sender {
                value: c.value,
                class: c.class,
                factory: built.factory,
                senders: built.senders,
                sites: built.sites,
            }
        })
        .collect();
    rows.sort_by(|a, b| a.value.cmp(&b.value).then_with(|| a.class.cmp(&b.class)));
    rows
}

/// Spells a list of names on one row: the first `max` and a count of the
/// rest, `-` for none.
///
/// # Arguments
///
/// * `names` - The names, in order.
/// * `max` - Most names spelled out.
pub(crate) fn spell(names: &[String], max: usize) -> String {
    if names.is_empty() {
        return "-".to_owned();
    }
    let mut text = names
        .iter()
        .take(max)
        .cloned()
        .collect::<Vec<_>>()
        .join(", ");
    if names.len() > max {
        let _ = write!(text, " +{} more", names.len() - max);
    }
    text
}

/// Renders every class answering `slot` with a constant and the functions
/// constructing it: where a client sends each command, as one table.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
/// * `slot` - The vtable index the constant sits in, zero-based.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn senders_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    slot: usize,
    filter: &str,
    limit: usize,
) -> String {
    let q = filter.to_lowercase();
    let rows: Vec<Sender> = senders(program, analysis, overlay, slot)
        .into_iter()
        .filter(|r| q.is_empty() || r.class.to_lowercase().contains(&q))
        .collect();
    let total = rows.len();
    let sent = rows.iter().filter(|r| !r.senders.is_empty()).count();
    let distinct: BTreeSet<u64> = rows
        .iter()
        .flat_map(|r| r.senders.iter().copied())
        .collect();
    let shown = total.min(limit);
    let mut out = format!(
        "# {total} classes answer virtual {slot} with a constant, {sent} of them are constructed by {} functions, showing {shown}\n",
        distinct.len()
    );
    out.push_str("value\tclass\tfactory\tsenders\n");
    for r in rows.into_iter().take(limit) {
        let factory = r
            .factory
            .map_or_else(|| "-".to_owned(), |f| name_of(analysis, overlay, f));
        let names: Vec<String> = r
            .senders
            .iter()
            .map(|&s| name_of(analysis, overlay, s))
            .collect();
        let _ = writeln!(
            out,
            "{:#x}\t{}\t{factory}\t{}",
            r.value,
            r.class,
            spell(&names, SENDERS_MAX)
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A row spells its first senders and counts the rest, and a class
    /// nobody constructs shows a dash.
    ///
    /// # Panics
    ///
    /// When the spelling differs.
    #[test]
    fn senders_are_spelled_with_a_cap() {
        assert_eq!(spell(&[], SENDERS_MAX), "-");
        let two = vec!["A::Send".to_owned(), "B::Tick".to_owned()];
        assert_eq!(spell(&two, SENDERS_MAX), "A::Send, B::Tick");
        let many: Vec<String> = (0..11).map(|i| format!("f{i}")).collect();
        assert_eq!(
            spell(&many, SENDERS_MAX),
            "f0, f1, f2, f3, f4, f5, f6, f7 +3 more"
        );
    }

    /// An image with no classes yields an empty table with its header.
    ///
    /// # Panics
    ///
    /// When the header differs.
    #[test]
    fn an_image_without_classes_has_an_empty_table() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let text = senders_tsv(&p, &a, &Overlay::default(), 3, "", 10);
        assert!(
            text.starts_with(
                "# 0 classes answer virtual 3 with a constant, 0 of them are constructed by 0 functions, showing 0\n"
            ),
            "{text}"
        );
        assert_eq!(text.lines().nth(1), Some("value\tclass\tfactory\tsenders"));
    }
}
