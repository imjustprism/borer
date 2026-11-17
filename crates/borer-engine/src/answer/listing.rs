//! An answer read once into the lines a front end draws as a table.

use std::ops::Range;

use crate::table::{self, Line};

/// An answer's text with its lines read once: notes, at most one column
/// header and rows, each row's fields, and the total the engine's pager
/// counted when it paged the answer.
///
/// This is a bridge. Answers are written as text for agents, and a
/// listing reads that text back with the reader paging uses
/// ([`table::classify`]), so a front end draws the rows without a reader of
/// its own. When a producer builds its rows typed, it builds its listing
/// from them, and once no producer is read back this read mode is deleted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Listing {
    /// The answer as an agent reads it.
    text: String,
    /// Each line's kind and where it lies in [`Listing::text`], in order.
    lines: Vec<(Line, Range<usize>)>,
    /// The index in [`Listing::lines`] of each row, in order.
    rows: Vec<usize>,
    /// The column names, `None` for an answer whose rows are whole lines.
    columns: Option<Vec<String>>,
    /// The rows of the whole answer, as the engine's pager counted them;
    /// `None` when it did not page the answer.
    total: Option<usize>,
}

impl Listing {
    /// Reads an answer's lines once.
    ///
    /// # Arguments
    ///
    /// * `text` - The answer.
    /// * `total` - The rows the engine's pager counted, `None` when it did
    ///   not page the answer.
    pub(crate) fn read(text: String, total: Option<usize>) -> Listing {
        let classified = table::classify(&text);
        let columns = table::columns_of(&classified);
        let mut at = 0usize;
        let lines: Vec<(Line, Range<usize>)> = classified
            .iter()
            .zip(text.split_inclusive('\n'))
            .map(|(&(kind, line), piece)| {
                let range = at..at.saturating_add(line.len());
                at = at.saturating_add(piece.len());
                (kind, range)
            })
            .collect();
        let rows = lines
            .iter()
            .enumerate()
            .filter(|(_, (kind, _))| *kind == Line::Row)
            .map(|(i, _)| i)
            .collect();
        Listing {
            text,
            lines,
            rows,
            columns,
            total,
        }
    }

    /// Returns the answer as an agent reads it, byte for byte.
    #[must_use]
    pub fn spell(&self) -> &str {
        &self.text
    }

    /// Returns the column names, `None` for an answer whose rows are whole
    /// lines (one written in padded columns, or in prose).
    #[must_use]
    pub fn columns(&self) -> Option<&[String]> {
        self.columns.as_deref()
    }

    /// Returns how many rows the whole answer holds, as the engine's pager
    /// counted them when it cut this page.
    ///
    /// # Returns
    ///
    /// The count, `None` when the engine did not page the answer: it was
    /// read whole, or it pages itself and says its count in a note.
    #[must_use]
    pub fn total(&self) -> Option<usize> {
        self.total
    }

    /// Returns each line with what it is, in order.
    pub fn lines(&self) -> impl Iterator<Item = (Line, &str)> {
        self.lines
            .iter()
            .map(|(kind, range)| (*kind, self.text.get(range.clone()).unwrap_or_default()))
    }

    /// Returns how many rows this answer shows.
    #[must_use]
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// Returns whether this answer shows no row.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Returns one row's fields: its tab-separated cells, one per column,
    /// the last keeping any tab past them; the whole line for an answer
    /// with no columns.
    ///
    /// # Arguments
    ///
    /// * `row` - The row, from 0.
    ///
    /// # Returns
    ///
    /// The fields, `None` past the last row.
    #[must_use]
    pub fn fields(&self, row: usize) -> Option<Vec<&str>> {
        let line = self.row(row)?;
        Some(match &self.columns {
            Some(names) => line.splitn(names.len(), '\t').collect(),
            None => vec![line],
        })
    }

    /// Returns one row's line.
    ///
    /// # Arguments
    ///
    /// * `row` - The row, from 0.
    fn row(&self, row: usize) -> Option<&str> {
        let (_, range) = self.lines.get(*self.rows.get(row)?)?;
        self.text.get(range.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::Listing;

    /// A listing spells its text as it was given, padded columns, a
    /// carriage return and a missing last newline included, and reads a
    /// padded row as one field.
    ///
    /// # Panics
    ///
    /// When the spelling or a field differs.
    #[test]
    fn a_listing_keeps_its_text_verbatim() {
        let text = "# site       caller\r\n0x10         main\n\n0x20         f";
        let read = Listing::read(text.to_owned(), None);
        assert_eq!(read.spell(), text);
        assert_eq!(read.fields(1), Some(vec!["0x20         f"]));
        let tabbed = Listing::read("va\tname\n0x10\tmain\tmore\n".to_owned(), Some(4));
        assert_eq!(tabbed.fields(0), Some(vec!["0x10", "main\tmore"]));
        assert_eq!(tabbed.total(), Some(4));
    }
}
