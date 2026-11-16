//! The function table's columns: one table of them says which show, how a row fills each
//! cell, where its text sits and how wide it is, so headers and cells cannot drift apart.

use borer_engine::analysis::render::FunctionRow;
use borer_engine::num::from_usize;
use gpui::{Pixels, SharedString};

/// Where a cell's text sits in its column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Align {
    /// Against the column's left edge.
    Start,
    /// Against the column's right edge, as numbers are.
    End,
}

/// How wide a column is.
#[derive(Debug, Clone, Copy)]
pub enum Fit {
    /// As wide as its header or its widest cell, which is the cell of the row with the
    /// largest key, so the column is never ellipsized.
    Widest(fn(&FunctionRow) -> u64),
    /// What the other columns leave of the table.
    Fill,
}

/// One column of the function table.
#[derive(Debug, Clone, Copy)]
pub struct Column {
    /// The header's text.
    pub header: &'static str,
    /// Formats a row's cell from the engine's row, deriving no fact of its own.
    pub cell: fn(&FunctionRow) -> SharedString,
    /// Where the header and the cells sit.
    pub align: Align,
    /// How wide the column is.
    pub fit: Fit,
}

/// Every column the table can show, the brief ones first.
pub const COLUMNS: [Column; 8] = [
    Column {
        header: "entry",
        cell: |row| format!("{:#x}", row.entry).into(),
        align: Align::Start,
        fit: Fit::Widest(|row| row.entry),
    },
    Column {
        header: "name",
        cell: |row| row.name.clone().into(),
        align: Align::Start,
        fit: Fit::Fill,
    },
    Column {
        header: "size",
        cell: |row| row.size.to_string().into(),
        align: Align::End,
        fit: Fit::Widest(|row| row.size),
    },
    Column {
        header: "callers",
        cell: |row| row.callers.to_string().into(),
        align: Align::End,
        fit: Fit::Widest(|row| from_usize(row.callers)),
    },
    Column {
        header: "blocks",
        cell: |row| row.blocks.to_string().into(),
        align: Align::End,
        fit: Fit::Widest(|row| from_usize(row.blocks)),
    },
    Column {
        header: "instrs",
        cell: |row| row.instrs.to_string().into(),
        align: Align::End,
        fit: Fit::Widest(|row| from_usize(row.instrs)),
    },
    Column {
        header: "callees",
        cell: |row| row.callees.to_string().into(),
        align: Align::End,
        fit: Fit::Widest(|row| from_usize(row.callees)),
    },
    Column {
        header: "src",
        cell: |row| row.src.code().into(),
        align: Align::Start,
        fit: Fit::Widest(|row| from_usize(row.src.code().len())),
    },
];

/// How many of [`COLUMNS`] the brief columns are.
const BRIEF_COLS: usize = 4;

/// Which columns the function table shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Columns {
    /// Entry, name, size and callers.
    Brief,
    /// The brief columns, then blocks, instrs, callees and src.
    Full,
}

impl Columns {
    /// Returns the columns shown, in order.
    #[must_use]
    pub fn shown(self) -> &'static [Column] {
        match self {
            Self::Brief => &COLUMNS[..BRIEF_COLS],
            Self::Full => &COLUMNS,
        }
    }

    /// Returns the other set of columns.
    #[must_use]
    pub const fn toggled(self) -> Self {
        match self {
            Self::Brief => Self::Full,
            Self::Full => Self::Brief,
        }
    }
}

/// Formats one [`FunctionRow`] into the cells of `columns`, in order.
///
/// # Arguments
///
/// * `row` - Engine [`FunctionRow`] to format.
/// * `columns` - The columns shown.
///
/// # Returns
///
/// One cell per column of [`Columns::shown`].
#[must_use]
pub fn row_cells(row: &FunctionRow, columns: Columns) -> Vec<SharedString> {
    columns
        .shown()
        .iter()
        .map(|column| (column.cell)(row))
        .collect()
}

/// Fewest characters the fill column gets; past it the table scrolls sideways.
const FILL_MIN_CHARS: usize = 24;

impl Column {
    /// Returns how many characters wide the column must be to show its header and every
    /// cell of `rows` whole, `None` for a [`Fit::Fill`] column.
    ///
    /// # Arguments
    ///
    /// * `rows` - Every row the table shows; one pass.
    #[must_use]
    pub fn chars(&self, rows: &[FunctionRow]) -> Option<usize> {
        let Fit::Widest(key) = self.fit else {
            return None;
        };
        let widest = rows.iter().max_by_key(|row| key(row));
        let cell = widest.map_or(0, |row| (self.cell)(row).chars().count());
        Some(cell.max(self.header.chars().count()))
    }
}

/// Returns the width of each column `columns` shows, in order.
///
/// A fitted column holds its characters with one to spare, and the fill column takes what
/// the others leave of `table`, but never under [`FILL_MIN_CHARS`].
///
/// # Arguments
///
/// * `columns` - The columns shown.
/// * `rows` - Every row the table shows.
/// * `ch` - Advance of one character of the table's font.
/// * `pad` - Horizontal padding of a cell, both sides together.
/// * `table` - Width of the table.
#[must_use]
pub fn column_widths(
    columns: Columns,
    rows: &[FunctionRow],
    ch: Pixels,
    pad: Pixels,
    table: Pixels,
) -> Vec<Pixels> {
    let width = |chars: usize| ch * (chars + 1) + pad;
    let fitted: Vec<Option<Pixels>> = columns
        .shown()
        .iter()
        .map(|column| column.chars(rows).map(width))
        .collect();
    let rest = table - fitted.iter().flatten().sum::<Pixels>();
    let fill = rest.max(width(FILL_MIN_CHARS));
    fitted.into_iter().map(|w| w.unwrap_or(fill)).collect()
}

#[cfg(test)]
mod tests {
    use borer_engine::analysis::render::{FunctionRow, RowSource};
    use gpui::{Pixels, SharedString, px};

    use super::{Align, COLUMNS, Column, Columns, FILL_MIN_CHARS, column_widths, row_cells};

    /// Returns a row at `entry` whose counts are `n`.
    ///
    /// # Panics
    ///
    /// Panics if `n` does not fit a size.
    fn row(entry: u64, n: usize) -> FunctionRow {
        FunctionRow {
            entry,
            size: u64::try_from(n).unwrap(),
            blocks: n,
            instrs: n,
            callers: n,
            callees: n,
            src: RowSource::User,
            name: format!("f{n}"),
        }
    }

    /// The brief columns are entry, name, size and callers, the full ones add blocks,
    /// instrs, callees and src, every cell follows its header, and counts sit right.
    ///
    /// # Panics
    ///
    /// Panics if a header, cell or alignment differs.
    #[test]
    fn one_table_drives_headers_cells_and_alignment() {
        let headers = |c: Columns| c.shown().iter().map(|c| c.header).collect::<Vec<_>>();
        assert_eq!(
            headers(Columns::Brief),
            ["entry", "name", "size", "callers"]
        );
        let full = [
            "entry", "name", "size", "callers", "blocks", "instrs", "callees", "src",
        ];
        assert_eq!(headers(Columns::Full), full);
        let r = row(0x1000, 7);
        let want = ["0x1000", "f7", "7", "7", "7", "7", "7", "usr"].map(SharedString::from);
        assert_eq!(row_cells(&r, Columns::Full), want);
        assert_eq!(row_cells(&r, Columns::Brief), want[..4]);
        let right = COLUMNS
            .iter()
            .filter(|c| c.align == Align::End)
            .map(|c| c.header);
        let right: Vec<_> = right.collect();
        assert_eq!(right, ["size", "callers", "blocks", "instrs", "callees"]);
    }

    /// Every fitted column is as wide as its widest cell or its header, whichever is wider,
    /// the name column fills what is left down to its floor, and each width belongs to its
    /// own column.
    ///
    /// # Panics
    ///
    /// Panics if a column's width differs from its widest cell.
    #[test]
    fn columns_fit_their_widest_cell() {
        let rows = [row(0x1000, 3), row(0x1_4000_1000, 12345), row(0x20, 9)];
        assert_eq!(COLUMNS[0].chars(&rows), Some("0x140001000".len()));
        assert_eq!(COLUMNS[1].chars(&rows), None);
        for column in &COLUMNS[2..] {
            let cells = rows.iter().map(|r| (column.cell)(r).chars().count());
            let widest = cells.chain([column.header.len()]).max();
            assert_eq!(column.chars(&rows), widest, "{}", column.header);
            assert_eq!(column.chars(&[]), Some(column.header.len()));
        }
        let (ch, pad) = (px(8.0), px(4.0));
        let fit = |column: &Column| ch * (column.chars(&rows).unwrap() + 1) + pad;
        for columns in [Columns::Brief, Columns::Full] {
            let widths = column_widths(columns, &rows, ch, pad, px(2000.0));
            assert_eq!(widths.len(), columns.shown().len());
            let fixed: Pixels = columns
                .shown()
                .iter()
                .filter(|c| c.chars(&rows).is_some())
                .map(fit)
                .sum();
            for (column, width) in columns.shown().iter().zip(&widths) {
                match column.chars(&rows) {
                    Some(_) => assert_eq!(*width, fit(column), "{}", column.header),
                    None => assert_eq!(*width, px(2000.0) - fixed),
                }
            }
            let narrow = column_widths(columns, &rows, ch, pad, px(10.0));
            assert_eq!(narrow[1], ch * (FILL_MIN_CHARS + 1) + pad);
        }
    }
}
