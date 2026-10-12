//! Plain-text listings read back: notes, a column header and rows.
//!
//! Every listing borer answers is lines. A note opens with `#` (`%%` in a
//! mermaid graph) and says what the rows are, how many there are and how
//! to get the rest; a blank line is a note too. At most one column header
//! names the columns: a line of tab-separated lowercase names right before
//! the first row (`va\tfunction\top`), or the last note before the first
//! row when its fields are tab-separated (`# functions\tfield\tclasses`).
//! Every other line is a row. A listing written in padded columns names
//! its columns in a note this does not read, so its rows are whole lines.
//!
//! Paging a listing ([`page`]) and a script's `rows` ([`records`]) both
//! read it this way, so a listing pages the same rows a script sees.

use std::fmt::Write as _;

/// What one line of a listing is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Line {
    /// A `#` or `%%` note, or a blank line.
    Note,
    /// The column header: tab-separated lowercase names before any row.
    Header,
    /// A row.
    Row,
}

/// Whether a line is a note: blank, or opening with `#` or `%%`.
///
/// # Arguments
///
/// * `line` - One line of a listing.
fn is_note(line: &str) -> bool {
    line.trim().is_empty() || line.starts_with('#') || line.starts_with("%%")
}

/// Whether a word is a column name: a lowercase letter, then lowercase
/// letters, digits or underscores.
///
/// # Arguments
///
/// * `word` - The word.
fn is_name(word: &str) -> bool {
    word.starts_with(|c: char| c.is_ascii_lowercase())
        && word
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
}

/// The column names a line spells: at least two tab-separated fields, each
/// opening with a name, which is the column's.
///
/// # Arguments
///
/// * `line` - The candidate header, its `# ` taken off when it is a note.
/// * `whole` - Whether each field must be a name and nothing else, as a
///   header that is not a note must; a note's field may go on in prose.
///
/// # Returns
///
/// The names, or `None` when the line is not a header.
fn names(line: &str, whole: bool) -> Option<Vec<String>> {
    let fields: Vec<&str> = line.split('\t').collect();
    if fields.len() < 2 {
        return None;
    }
    fields
        .iter()
        .map(|f| {
            let word = if whole {
                *f
            } else {
                f.split(' ').next().unwrap_or_default()
            };
            is_name(word).then(|| word.to_owned())
        })
        .collect()
}

/// Classifies every line of a listing.
///
/// # Arguments
///
/// * `text` - The listing.
///
/// # Returns
///
/// Each line with what it is, in order.
#[must_use]
pub fn classify(text: &str) -> Vec<(Line, &str)> {
    let mut out: Vec<(Line, &str)> = Vec::new();
    let mut opened = false;
    for line in text.lines() {
        let kind = if is_note(line) {
            Line::Note
        } else if !opened && names(line, true).is_some() {
            opened = true;
            Line::Header
        } else {
            opened = true;
            Line::Row
        };
        out.push((kind, line));
    }
    out
}

/// The column names of a listing, from its header line or from the
/// tab-separated note right before its first row.
///
/// # Arguments
///
/// * `text` - The listing.
///
/// # Returns
///
/// The names, or `None` when the listing names no columns this reads.
#[must_use]
pub fn columns(text: &str) -> Option<Vec<String>> {
    let lines = classify(text);
    if let Some((_, header)) = lines.iter().find(|(k, _)| *k == Line::Header) {
        return names(header, true);
    }
    let first = lines.iter().position(|(k, _)| *k == Line::Row)?;
    let (_, note) = lines[..first]
        .iter()
        .rev()
        .find(|(_, l)| !l.trim().is_empty())?;
    names(note.strip_prefix("# ")?, false)
}

/// The rows of a listing as records: each cell under its column's name,
/// or the whole line under `text` when the listing names no columns.
///
/// A row with more tabs than there are columns keeps the rest in its last
/// cell; one with fewer has empty cells for the columns it lacks.
///
/// # Arguments
///
/// * `text` - The listing.
///
/// # Returns
///
/// One record per row, in order, each a list of `(column, cell)` pairs.
///
/// # Examples
///
/// ```
/// use borer_engine::table::records;
///
/// let text = "# 2 sites\nva\tfunction\n0x10\tmain\n0x20\tf\n";
/// let rows = records(text);
/// assert_eq!(rows[1], vec![("va".to_owned(), "0x20".to_owned()), ("function".to_owned(), "f".to_owned())]);
/// assert_eq!(records("# a note\nplain line\n")[0], vec![("text".to_owned(), "plain line".to_owned())]);
/// ```
#[must_use]
pub fn records(text: &str) -> Vec<Vec<(String, String)>> {
    let columns = columns(text);
    classify(text)
        .into_iter()
        .filter(|(k, _)| *k == Line::Row)
        .map(|(_, line)| match &columns {
            Some(names) => {
                let mut cells = line.splitn(names.len(), '\t');
                names
                    .iter()
                    .map(|name| (name.clone(), cells.next().unwrap_or_default().to_owned()))
                    .collect()
            }
            None => vec![("text".to_owned(), line.to_owned())],
        })
        .collect()
}

/// One page of a listing's rows, under a `# showing N of M from K` line.
///
/// The notes before the first row (what the listing is, its legend, its
/// column header) and after the last (what it left out) stay; a note
/// among the rows stays when the row after it is on the page, since it
/// heads that row. Under the page, when rows are left, a line names the
/// URI that reads the next page ([`next_page`]).
///
/// # Arguments
///
/// * `text` - The listing.
/// * `offset` - Rows to skip.
/// * `limit` - Most rows to keep.
/// * `again` - The URI that read the listing, without its offset.
///
/// # Returns
///
/// The page.
///
/// # Examples
///
/// ```
/// use borer_engine::table::page;
///
/// let text = "# 3 things\nname\tsize\na\t1\nb\t2\nc\t3\n# end\n";
/// assert_eq!(
///     page(text, 1, 1, "borer://things"),
///     "# showing 1 of 3 from 1\n# 3 things\nname\tsize\nb\t2\n# end\n# 1 more; borer://things!offset=2 for the next page\n"
/// );
/// ```
#[must_use]
pub fn page(text: &str, offset: usize, limit: usize, again: &str) -> String {
    let lines = classify(text);
    let total = lines.iter().filter(|(k, _)| *k == Line::Row).count();
    let start = offset.min(total);
    let end = start.saturating_add(limit).min(total);
    let mut out = format!("# showing {} of {total} from {offset}\n", end - start);
    let mut pending: Vec<&str> = Vec::new();
    let mut row = 0usize;
    for (kind, line) in lines {
        if kind != Line::Row {
            pending.push(line);
            continue;
        }
        if row == 0 || (start..end).contains(&row) {
            for note in pending.drain(..) {
                let _ = writeln!(out, "{note}");
            }
        } else {
            pending.clear();
        }
        if (start..end).contains(&row) {
            let _ = writeln!(out, "{line}");
        }
        row += 1;
    }
    for note in pending {
        let _ = writeln!(out, "{note}");
    }
    out.push_str(&next_page(total, end, again));
    out
}

/// Reads the rows a page skips, as a URI writes them.
///
/// # Arguments
///
/// * `text` - The digits after `offset=`.
///
/// # Errors
///
/// When the text is not a row count, with the form it takes.
pub fn row_offset(text: &str) -> Result<usize, String> {
    text.trim().parse().map_err(|_| {
        format!(
            "offset={} is not a row count; skip rows with offset=<n>",
            crate::text::quoted(text)
        )
    })
}

/// Reads the most rows a page shows, as a URI writes them: one or more.
///
/// # Arguments
///
/// * `text` - The digits after `limit=`.
///
/// # Errors
///
/// When the text is not a count of one row or more, with the form it
/// takes.
pub fn row_limit(text: &str) -> Result<usize, String> {
    text.trim()
        .parse::<usize>()
        .ok()
        .filter(|n| *n > 0)
        .ok_or_else(|| {
            format!(
                "limit={} is not a row count; show 1 or more rows with limit=<n>",
                crate::text::quoted(text)
            )
        })
}

/// The rows a listing that pages itself shows, and the URI that reads the
/// next page.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Window<'a> {
    /// Rows to skip.
    pub skip: usize,
    /// Most rows shown.
    pub limit: usize,
    /// The URI that read the listing, without its offset, for the line
    /// naming the next page; `None` for no such line, as the CLI pages by
    /// its own flags.
    pub again: Option<&'a str>,
}

impl Window<'_> {
    /// The first `limit` rows and no line naming the next page.
    ///
    /// # Arguments
    ///
    /// * `limit` - Most rows shown.
    #[must_use]
    pub fn first(limit: usize) -> Self {
        Window {
            skip: 0,
            limit,
            again: None,
        }
    }

    /// The line under a page of this window that showed `shown` of `total`
    /// rows ([`next_page`]); nothing without a URI to name.
    ///
    /// # Arguments
    ///
    /// * `total` - Rows in the listing.
    /// * `shown` - Rows the page showed.
    #[must_use]
    pub fn next_page(&self, total: usize, shown: usize) -> String {
        self.again.map_or_else(String::new, |again| {
            next_page(total, self.skip.saturating_add(shown), again)
        })
    }
}

/// The line under a page naming the URI that reads the next one.
///
/// # Arguments
///
/// * `total` - Rows in the listing.
/// * `next` - The first row not shown.
/// * `again` - The URI that read the listing, without its offset.
///
/// # Returns
///
/// `# R more; <again>!offset=<next> for the next page`, or nothing when
/// no row is left.
#[must_use]
pub fn next_page(total: usize, next: usize, again: &str) -> String {
    if next >= total {
        return String::new();
    }
    format!(
        "# {} more; {again}!offset={next} for the next page\n",
        total - next
    )
}

#[cfg(test)]
mod tests {
    use super::{Line, classify, columns, page, records};

    /// A header is the tab-separated line of names before the first row,
    /// or the tab-separated note right before it; a padded listing has
    /// none, and its rows are whole lines.
    ///
    /// # Panics
    ///
    /// When a line is read as the wrong kind or a column is misnamed.
    #[test]
    fn a_listing_reads_as_notes_a_header_and_rows() {
        let plain = "# 2 rows\nva\tfunction\n0x1\tf\n0x2\tg\n";
        let kinds: Vec<Line> = classify(plain).into_iter().map(|(k, _)| k).collect();
        assert_eq!(kinds, [Line::Note, Line::Header, Line::Row, Line::Row]);
        assert_eq!(
            columns("# 1 field\n# functions\tfield\tclasses (the ones)\n3\thp\tPlayer\n"),
            Some(vec![
                "functions".to_owned(),
                "field".to_owned(),
                "classes".to_owned()
            ])
        );
        let padded = "# site     caller\n0x10       main\n";
        assert_eq!(columns(padded), None);
        assert_eq!(
            records(padded),
            [vec![("text".to_owned(), "0x10       main".to_owned())]]
        );
        assert_eq!(
            records("a\tb\nx\ty\tz\nw\n"),
            [
                vec![
                    ("a".to_owned(), "x".to_owned()),
                    ("b".to_owned(), "y\tz".to_owned())
                ],
                vec![
                    ("a".to_owned(), "w".to_owned()),
                    ("b".to_owned(), String::new())
                ]
            ]
        );
    }

    /// Page one and page two hold the first rows of the whole listing in
    /// order, a note among the rows goes with the row it heads, and the
    /// last page names no next one.
    ///
    /// # Panics
    ///
    /// When a page drops, repeats or reorders a row.
    #[test]
    fn two_pages_hold_the_first_rows_in_order() {
        let text: String = std::iter::once("# 9 rows\nn\tsquare\n".to_owned())
            .chain((0..9).map(|n| {
                let note = if n == 5 { "# the second half\n" } else { "" };
                format!("{note}{n}\t{}\n", n * n)
            }))
            .collect();
        let rows = |t: &str| -> Vec<String> {
            classify(t)
                .into_iter()
                .filter(|(k, _)| *k == Line::Row)
                .map(|(_, l)| l.to_owned())
                .collect()
        };
        let one = page(&text, 0, 4, "borer://sq");
        let two = page(&text, 4, 4, "borer://sq");
        let both: Vec<String> = rows(&one).into_iter().chain(rows(&two)).collect();
        assert_eq!(both, rows(&text)[..8]);
        assert!(
            one.ends_with("# 5 more; borer://sq!offset=4 for the next page\n"),
            "{one}"
        );
        assert!(two.contains("# the second half\n5\t25\n"), "{two}");
        assert!(!one.contains("second half"), "{one}");
        let last = page(&text, 8, 4, "borer://sq");
        assert!(last.starts_with("# showing 1 of 9 from 8\n"), "{last}");
        assert!(!last.contains("for the next page"), "{last}");
        assert_eq!(page(&text, 3, 2, "x"), page(&text, 3, 2, "x"));
    }
}
