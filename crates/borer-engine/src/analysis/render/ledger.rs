//! The session's ledger: the names, stated fields, findings and open
//! questions an overlay holds, as `annotations` and `borer://annotations`
//! list them.

use std::fmt::Write as _;

use crate::analysis::{Overlay, edit};
use crate::text::Filter;

/// Rows one page of the ledger holds when no limit is asked.
pub const LEDGER_ROWS_DEFAULT: usize = 200;

/// Most rows one page of the ledger holds.
pub const LEDGER_ROWS_MAX: usize = 1000;

/// Lists an overlay's entries: names, then the fields stated of classes,
/// then findings, then open questions, a page at a time.
///
/// A comment opening with a question mark is a hypothesis, not a finding.
/// Separating the two is what makes the overlay a ledger an agent can
/// return to: a conclusion it proved is worth building on, and one it
/// guessed at is worth checking before it does. The ledger grows with the
/// session, so it pages like every list: the header says `showing N of M`
/// of the rows the filter keeps, and only the page asked for is held while
/// the rows are counted.
///
/// # Arguments
///
/// * `o` - The overlay.
/// * `filter` - Keeps the rows holding it.
/// * `offset` - Rows the filter keeps to skip.
/// * `limit` - Most rows shown.
/// * `count_only` - The count line alone.
#[must_use]
pub fn annotations_tsv(
    o: &Overlay,
    filter: &Filter,
    offset: usize,
    limit: usize,
    count_only: bool,
) -> String {
    let (open, settled): (Vec<_>, Vec<_>) = o
        .comments
        .iter()
        .partition(|(_, c)| edit::open_question(c).is_some());
    let fields = o.fields.iter().flat_map(|(class, fields)| {
        fields.iter().map(move |(off, field)| {
            let at = format!("{class}+{off:#x}");
            format!("{at:<12} field: {}", field.spell())
        })
    });
    let stated: usize = o.fields.values().map(std::collections::BTreeMap::len).sum();
    let rows = o
        .names
        .iter()
        .map(|(va, name)| format!("{:<12} name: {name}", format!("{va:#x}")))
        .chain(fields)
        .chain(
            settled
                .iter()
                .map(|(va, c)| format!("{:<12} found: {c}", format!("{va:#x}"))),
        )
        .chain(open.iter().map(|(va, c)| {
            let claim = c.trim_start().trim_start_matches('?').trim_start();
            format!("{:<12} open:  {claim}", format!("{va:#x}"))
        }))
        .filter(|row| filter.accepts(row));
    let (mut total, mut shown) = (0usize, Vec::new());
    for row in rows {
        if total >= offset && shown.len() < limit {
            shown.push(row);
        }
        total += 1;
    }
    let counts = format!(
        "{} names, {} findings, {} open question(s){}",
        o.names.len(),
        settled.len(),
        open.len(),
        match stated {
            0 => String::new(),
            n => format!(", {n} stated field(s)"),
        }
    );
    if count_only {
        return format!("# {total} annotations ({counts})\n");
    }
    let mut out = format!(
        "# showing {} of {total} annotations ({counts})\n# addr annotation\n",
        shown.len()
    );
    for row in shown {
        let _ = writeln!(out, "{row}");
    }
    if !o.comments.is_empty() {
        out.push_str(
            "# a comment opening with ? is an open question; drop the ? once it is proved\n",
        );
    }
    out
}
