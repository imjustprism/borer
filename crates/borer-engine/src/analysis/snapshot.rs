//! Snapshots: a program's semantics written down by stable names, and what
//! changed between one build and the next.
//!
//! After a client update the question is not which of a hundred thousand
//! functions moved but which commands, packet layouts, attributes and
//! message routes changed. A snapshot records each of those by a name that
//! survives a rebuild (a class, an attribute, a component and a message)
//! with the facts about it; comparing the snapshot of the old build with
//! the current binary lists every one added, removed or changed, so an
//! update is one short report instead of a diff of every function.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::encode::{compact_writes, encoding_for_class};
use super::schema::{compact_fields, schema_for_class};
use super::vtables::slot_constants;
use super::{Analysis, Overlay};
use crate::program::Program;

/// First line of a snapshot file, with its format version.
const HEADER: &str = "# borer snapshot v1";
/// Slots tried for the one classes answer with their wire constant.
const SLOTS_TRIED: usize = 16;
/// Fewest distinct constants that make a slot the protocol's.
const PROTOCOL_MIN: usize = 16;
/// Fewest workers' worth of classes before the protocol rows are striped.
const PAR_MIN: usize = 8;
/// Most changed rows listed per kind.
const CHANGES_MAX: usize = 400;

/// One fact about one named thing: its kind, its stable key, and the value
/// that is compared between builds.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fact {
    /// `cmd`, `attr`, `route` or `msg`.
    pub kind: String,
    /// The stable name: a class, an attribute, `component message`.
    pub key: String,
    /// What is compared: tab-separated fields.
    pub value: String,
}

/// The slot the most classes answer with distinct constants: where a
/// protocol keeps each command's wire id.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
fn protocol_slot(program: &Program, analysis: &Analysis) -> Option<usize> {
    (0..SLOTS_TRIED)
        .map(|slot| {
            let values: BTreeSet<u64> = slot_constants(program, analysis, slot)
                .into_iter()
                .map(|c| c.value)
                .collect();
            (values.len(), slot)
        })
        .filter(|&(n, _)| n >= PROTOCOL_MIN)
        .max_by_key(|&(n, slot)| (n, std::cmp::Reverse(slot)))
        .map(|(_, slot)| slot)
}

/// A handler's name as a snapshot records it: an address-derived name is
/// not stable across builds and is recorded as `-`.
///
/// # Arguments
///
/// * `name` - The name.
fn stable(name: &str) -> String {
    let own = name.rsplit("::").next().unwrap_or(name);
    if own.starts_with("sub_") || own.starts_with("vfunc_") || name.starts_with("class_") {
        "-".to_owned()
    } else {
        name.to_owned()
    }
}

/// Every fact the snapshot records about the program, sorted.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
#[must_use]
pub fn facts(program: &Program, analysis: &Analysis, overlay: &Overlay) -> Vec<Fact> {
    let mut out: Vec<Fact> = Vec::new();
    if let Some(slot) = protocol_slot(program, analysis) {
        let rows = slot_constants(program, analysis, slot);
        let layouts = super::striped_with(
            &rows,
            PAR_MIN,
            || (),
            |(), c| {
                (
                    encoding_for_class(program, analysis, overlay, &c.class)
                        .map_or_else(|| "-".to_owned(), |(_, e)| compact_writes(&e.fields)),
                    schema_for_class(program, analysis, overlay, &c.class)
                        .map_or_else(|| "-".to_owned(), |(_, s)| compact_fields(&s.fields)),
                )
            },
        );
        for (c, found) in rows.into_iter().zip(layouts) {
            let (encodes, decodes) = found.unwrap_or_else(|| ("-".to_owned(), "-".to_owned()));
            out.push(Fact {
                kind: "cmd".to_owned(),
                key: c.class,
                value: format!("{:#x}\t{encodes}\t{decodes}", c.value),
            });
        }
    }
    let key = overlay.fingerprint();
    let attrs = analysis.derived.get_or_build_named("attrs", key, (), || {
        super::attributes::catalog(program, analysis, overlay)
    });
    for a in &attrs.attrs {
        let ty = match a.type_code {
            Some(code) => attrs
                .type_names
                .get(&code)
                .cloned()
                .unwrap_or_else(|| format!("type{code}")),
            None if a.variant => "Variant".to_owned(),
            None => "?".to_owned(),
        };
        out.push(Fact {
            kind: "attr".to_owned(),
            key: a.name.clone(),
            value: format!("{:#010x}\t{ty}\t{}\t{}", a.code, a.access, a.default),
        });
    }
    let routes = analysis.derived.get_or_build_named("ports", key, (), || {
        super::ports::routes(program, analysis, overlay)
    });
    for r in routes.iter() {
        out.push(Fact {
            kind: "route".to_owned(),
            key: format!("{} {}", r.class, r.message),
            value: stable(&r.handler_label(analysis, overlay)),
        });
    }
    for (class, code) in &analysis.classes.ids {
        out.push(Fact {
            kind: "msg".to_owned(),
            key: class.clone(),
            value: format!("{code:#010x}"),
        });
    }
    out.sort();
    out.dedup_by(|a, b| a.kind == b.kind && a.key == b.key);
    out
}

/// Writes facts as a snapshot file's text.
///
/// # Arguments
///
/// * `facts` - The facts, sorted.
#[must_use]
pub fn write(facts: &[Fact]) -> String {
    let mut out = format!("{HEADER}\n# {} facts\n", facts.len());
    for f in facts {
        let _ = writeln!(out, "{}\t{}\t{}", f.kind, f.key, f.value);
    }
    out
}

/// Reads a snapshot file's text back into facts.
///
/// # Arguments
///
/// * `text` - The file.
///
/// # Errors
///
/// When the text is not a snapshot, or a line has no kind and key.
pub fn read(text: &str) -> Result<Vec<Fact>, String> {
    let mut lines = text.lines();
    if lines.next().map(str::trim_end) != Some(HEADER) {
        return Err(format!("not a snapshot: the first line is not `{HEADER}`"));
    }
    let mut out = Vec::new();
    for (i, line) in lines.enumerate() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let mut cols = line.splitn(3, '\t');
        let (Some(kind), Some(key)) = (cols.next(), cols.next()) else {
            return Err(format!("line {}: not a fact", i + 2));
        };
        out.push(Fact {
            kind: kind.to_owned(),
            key: key.to_owned(),
            value: cols.next().unwrap_or("").to_owned(),
        });
    }
    Ok(out)
}

/// What became of one fact between two builds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Change {
    /// The fact is new.
    Added,
    /// The fact is gone.
    Removed,
    /// The fact's value differs.
    Changed,
}

impl Change {
    /// The change as the summary line marks it: `+`, `-` or `~`.
    fn mark(self) -> char {
        match self {
            Change::Added => '+',
            Change::Removed => '-',
            Change::Changed => '~',
        }
    }

    /// The change as a row spells it.
    fn word(self) -> &'static str {
        match self {
            Change::Added => "added",
            Change::Removed => "removed",
            Change::Changed => "changed",
        }
    }
}

/// One changed fact: what became of it, its key, and its values before and
/// after (empty where it did not exist).
#[derive(Debug, Clone, PartialEq, Eq)]
struct ChangedFact {
    /// What became of it.
    change: Change,
    /// The stable name.
    key: String,
    /// The value in the earlier build; empty when added.
    was: String,
    /// The value in the current build; empty when removed.
    now: String,
}

/// Compares an earlier build's facts with the current ones: per kind, the
/// facts added, removed and changed, as a `#`-headed table.
///
/// The header's count is every change; each kind lists at most
/// [`CHANGES_MAX`] rows and ends in a `# N more` line for the rest, and
/// when that cuts anything the header says how many rows are listed, so
/// the count, the rows and the tails always add up from the header alone.
///
/// A snapshot of another program shares no command, attribute, route or
/// message with this one, and comparing the two lists everything as added
/// and removed: a report that reads as a vast update. When both sides
/// hold facts and none names the same thing, a warning line opens the
/// answer. Facts and not a hash of the bytes decide it, because the bytes
/// of every new build differ and the next build is what a snapshot is
/// compared against.
///
/// # Arguments
///
/// * `before` - The earlier build's facts.
/// * `after` - The current build's facts.
#[must_use]
pub fn changes_tsv(before: &[Fact], after: &[Fact]) -> String {
    let index = |facts: &[Fact]| -> BTreeMap<(String, String), String> {
        facts
            .iter()
            .map(|f| ((f.kind.clone(), f.key.clone()), f.value.clone()))
            .collect()
    };
    let old = index(before);
    let new = index(after);
    let mut rows: BTreeMap<String, Vec<ChangedFact>> = BTreeMap::new();
    for ((kind, key), value) in &new {
        match old.get(&(kind.clone(), key.clone())) {
            None => rows.entry(kind.clone()).or_default().push(ChangedFact {
                change: Change::Added,
                key: key.clone(),
                was: String::new(),
                now: value.clone(),
            }),
            Some(was) if was != value => rows.entry(kind.clone()).or_default().push(ChangedFact {
                change: Change::Changed,
                key: key.clone(),
                was: was.clone(),
                now: value.clone(),
            }),
            Some(_) => {}
        }
    }
    for ((kind, key), value) in &old {
        if !new.contains_key(&(kind.clone(), key.clone())) {
            rows.entry(kind.clone()).or_default().push(ChangedFact {
                change: Change::Removed,
                key: key.clone(),
                was: value.clone(),
                now: String::new(),
            });
        }
    }
    let count = |kind: &str, change: Change| {
        rows.get(kind)
            .map_or(0, |r| r.iter().filter(|f| f.change == change).count())
    };
    let kinds: BTreeSet<&str> = old
        .keys()
        .chain(new.keys())
        .map(|(k, _)| k.as_str())
        .collect();
    let summary: Vec<String> = kinds
        .iter()
        .map(|k| {
            format!(
                "{k} {}{} {}{} {}{}",
                Change::Added.mark(),
                count(k, Change::Added),
                Change::Removed.mark(),
                count(k, Change::Removed),
                Change::Changed.mark(),
                count(k, Change::Changed)
            )
        })
        .collect();
    let total: usize = rows.values().map(Vec::len).sum();
    let listed: usize = rows.values().map(|r| r.len().min(CHANGES_MAX)).sum();
    let mut out = if !old.is_empty() && !new.is_empty() && !old.keys().any(|k| new.contains_key(k))
    {
        format!(
            "# warning: the snapshot is of another program: none of its {} facts names anything this one has\n",
            old.len()
        )
    } else {
        String::new()
    };
    let _ = writeln!(
        out,
        "# {total} changes across {} facts before and {} after: {}{}",
        before.len(),
        after.len(),
        if summary.is_empty() {
            "nothing recorded".to_owned()
        } else {
            summary.join(", ")
        },
        if listed < total {
            format!(
                "; listing {listed}, {CHANGES_MAX} a kind at most, the rest counted on # more lines"
            )
        } else {
            String::new()
        }
    );
    out.push_str("kind\tchange\tkey\tbefore\tafter\n");
    for (kind, list) in &rows {
        for f in list.iter().take(CHANGES_MAX) {
            let _ = writeln!(
                out,
                "{kind}\t{}\t{}\t{}\t{}",
                f.change.word(),
                f.key,
                f.was.replace('\t', " | "),
                f.now.replace('\t', " | ")
            );
        }
        if list.len() > CHANGES_MAX {
            let _ = writeln!(out, "# {} more {kind} changes", list.len() - CHANGES_MAX);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A snapshot reads back as written, refuses what is not one, and two
    /// builds compare to their additions, removals and changes.
    ///
    /// # Panics
    ///
    /// When a fact or a change differs.
    #[test]
    fn snapshots_round_trip_and_compare() {
        let fact = |kind: &str, key: &str, value: &str| Fact {
            kind: kind.to_owned(),
            key: key.to_owned(),
            value: value.to_owned(),
        };
        let before = vec![
            fact("attr", "Health", "0x4849504f\tInt\trw\t0"),
            fact("cmd", "Commands::MoveCommand", "0x5f\tu32@+0x20\t-"),
            fact("route", "Mover Messaging::Tick", "Mover::OnTick"),
        ];
        let text = write(&before);
        assert_eq!(read(&text).expect("reads"), before);
        assert!(read("hello\n").is_err());
        let after = vec![
            fact("attr", "Health", "0x4849504f\tInt64\trw\t0"),
            fact("cmd", "Commands::MoveCommand", "0x5f\tu32@+0x20\t-"),
            fact("cmd", "Commands::JumpCommand", "0x60\tbit@+0x20\t-"),
        ];
        let report = changes_tsv(&before, &after);
        assert!(
            report.starts_with("# 3 changes across 3 facts before and 3 after: attr +0 -0 ~1, cmd +1 -0 ~0, route +0 -1 ~0\n"),
            "{report}"
        );
        assert!(
            report.contains(
                "attr\tchanged\tHealth\t0x4849504f | Int | rw | 0\t0x4849504f | Int64 | rw | 0\n"
            ),
            "{report}"
        );
        assert!(
            report.contains("cmd\tadded\tCommands::JumpCommand\t\t0x60 | bit@+0x20 | -\n"),
            "{report}"
        );
        assert!(
            report.contains("route\tremoved\tMover Messaging::Tick\tMover::OnTick\t\n"),
            "{report}"
        );
        assert_eq!(stable("Mover::sub_140001000"), "-");
        assert_eq!(stable("Mover::OnTick"), "Mover::OnTick");
    }

    /// Builds a fact.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind.
    /// * `key` - The stable name.
    /// * `value` - The value compared.
    fn fact(kind: &str, key: &str, value: &str) -> Fact {
        Fact {
            kind: kind.to_owned(),
            key: key.to_owned(),
            value: value.to_owned(),
        }
    }

    /// A kind with more changes than a kind lists ends in a tail, and the
    /// header's count is the rows listed plus every tail, with the number
    /// listed in the header once anything is cut.
    ///
    /// # Panics
    ///
    /// When the rows and the tails do not add up to the header's count.
    #[test]
    fn the_change_count_is_the_rows_plus_the_tails() {
        let before: Vec<Fact> = std::iter::once(fact("cmd", "Commands::Move", "0x5f"))
            .chain((0..5).map(|i| fact("route", &format!("Mover Tick{i}"), "Mover::OnTick")))
            .collect();
        let after: Vec<Fact> = std::iter::once(fact("cmd", "Commands::Move", "0x60"))
            .chain((0..1000).map(|i| fact("attr", &format!("Attr{i:04}"), "0x1\tInt\trw\t0")))
            .collect();
        let report = changes_tsv(&before, &after);
        let header = report.lines().next().expect("a header");
        assert!(
            header.starts_with("# 1006 changes across 6 facts before and 1001 after: "),
            "{header}"
        );
        assert!(
            header.contains("; listing 406, 400 a kind at most"),
            "{header}"
        );
        let rows = report
            .lines()
            .skip(2)
            .filter(|l| !l.starts_with('#'))
            .count();
        let tails: usize = report
            .lines()
            .filter_map(|l| {
                l.strip_prefix("# ")?
                    .split_once(" more ")?
                    .0
                    .parse::<usize>()
                    .ok()
            })
            .sum();
        assert_eq!((rows, tails), (406, 600), "{report}");
        assert_eq!(rows + tails, 1006);
        assert!(report.contains("# 600 more attr changes\n"), "{report}");

        let whole = changes_tsv(&before[..1], &after[..1]);
        assert!(
            !whole.contains("listing"),
            "nothing cut, nothing said: {whole}"
        );
    }

    /// Comparing against a snapshot that names nothing this program has
    /// opens with one warning line; one sharing a single fact, or an empty
    /// side, does not warn.
    ///
    /// # Panics
    ///
    /// When another program's snapshot goes unwarned, or a build of this one
    /// is warned about.
    #[test]
    fn a_snapshot_of_another_program_is_warned_about() {
        let theirs = vec![
            fact("cmd", "Their::Jump", "0x1"),
            fact("msg", "Their::Ping", "0x50494e47"),
        ];
        let ours = vec![
            fact("cmd", "Ours::Walk", "0x1"),
            fact("msg", "Ours::Ping", "0x50494e47"),
        ];
        let report = changes_tsv(&theirs, &ours);
        let mut lines = report.lines();
        assert_eq!(
            lines.next(),
            Some(
                "# warning: the snapshot is of another program: none of its 2 facts names anything this one has"
            )
        );
        assert!(
            lines.next().is_some_and(|l| l.starts_with("# 4 changes ")),
            "{report}"
        );
        assert_eq!(report.matches("# warning").count(), 1);

        let next_build = vec![
            fact("cmd", "Their::Jump", "0x2"),
            fact("cmd", "New::One", "0x3"),
        ];
        for quiet in [
            changes_tsv(&theirs, &next_build),
            changes_tsv(&[], &ours),
            changes_tsv(&theirs, &[]),
        ] {
            assert!(!quiet.contains("warning"), "{quiet}");
        }
    }
}
