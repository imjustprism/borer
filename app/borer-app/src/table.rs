//! The columns of a table of the engine's rows, for every rows panel.
//!
//! One table of them says how a row fills each cell, where its text sits, what color it
//! draws in and how wide it is, so headers and cells cannot drift apart.

use gpui::prelude::FluentBuilder as _;
use gpui::{Div, IntoElement, ParentElement as _, Pixels, SharedString, Styled as _, div};

/// Where a cell's text sits in its column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Align {
    /// Against the column's left edge.
    Start,
    /// Against the column's right edge, as numbers are.
    End,
}

/// What a column's cells are, which picks the theme color they draw in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ink {
    /// An address, in the theme's `borer.address` color.
    Address,
    /// A function's name, in the theme's `function` color.
    Function,
    /// A count or a code, in the theme's muted text color.
    Muted,
}

/// How wide a column of rows `R` is.
#[derive(Debug)]
pub enum Fit<R> {
    /// As wide as its header or its widest cell, which is the cell of the row with the
    /// largest key, so the column is never ellipsized.
    Widest(fn(&R) -> u64),
    /// What the other columns leave of the table.
    Fill,
}

/// One column of a table of rows `R`.
#[derive(Debug)]
pub struct Column<R> {
    /// The header's text.
    pub header: &'static str,
    /// Formats a row's cell from the engine's row, deriving no fact of its own.
    pub cell: fn(&R) -> SharedString,
    /// Where the header and the cells sit.
    pub align: Align,
    /// What the cells are, which picks their color.
    pub ink: Ink,
    /// How wide the column is.
    pub fit: Fit<R>,
}

/// Which of a kind's columns a table shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Columns {
    /// The few that identify a row.
    Brief,
    /// Every column the kind has.
    Full,
}

impl Columns {
    /// Returns the other set.
    #[must_use]
    pub const fn toggled(self) -> Self {
        match self {
            Self::Brief => Self::Full,
            Self::Full => Self::Brief,
        }
    }
}

/// Fewest characters the fill column gets; past it the table scrolls sideways.
pub const FILL_MIN_CHARS: usize = 24;

impl<R> Column<R> {
    /// Returns how many characters wide the column must be to show its header and every
    /// cell of `rows` whole, `None` for a [`Fit::Fill`] column.
    ///
    /// # Arguments
    ///
    /// * `rows` - Every row the table shows; one pass.
    #[must_use]
    pub fn chars(&self, rows: &[R]) -> Option<usize> {
        let Fit::Widest(key) = self.fit else {
            return None;
        };
        let widest = rows.iter().max_by_key(|row| key(row));
        let cell = widest.map_or(0, |row| (self.cell)(row).chars().count());
        Some(cell.max(self.header.chars().count()))
    }
}

/// Returns one cell of `row` per column of `shown`, in order.
///
/// # Arguments
///
/// * `row` - The engine's row.
/// * `shown` - The columns shown.
#[must_use]
pub fn cells<R>(row: &R, shown: &[Column<R>]) -> Vec<SharedString> {
    shown.iter().map(|column| (column.cell)(row)).collect()
}

/// Returns the width of each column of `shown`, in order.
///
/// A fitted column holds its characters with one to spare, and the fill column takes what
/// the others leave of `table`, but never under [`FILL_MIN_CHARS`].
///
/// # Arguments
///
/// * `shown` - The columns shown.
/// * `rows` - Every row the table shows.
/// * `ch` - Advance of one character of the table's font.
/// * `pad` - Horizontal padding of a cell, both sides together.
/// * `table` - Width of the table.
#[must_use]
pub fn widths<R>(
    shown: &[Column<R>],
    rows: &[R],
    ch: Pixels,
    pad: Pixels,
    table: Pixels,
) -> Vec<Pixels> {
    let width = |chars: usize| ch * (chars + 1) + pad;
    let fitted: Vec<Option<Pixels>> = shown
        .iter()
        .map(|column| column.chars(rows).map(width))
        .collect();
    let rest = table - fitted.iter().flatten().sum::<Pixels>();
    let fill = rest.max(width(FILL_MIN_CHARS));
    fitted.into_iter().map(|w| w.unwrap_or(fill)).collect()
}

/// Returns `child` as the content of a table cell, filling it and sitting where `align`
/// says.
///
/// # Arguments
///
/// * `align` - Where the content sits in its column.
/// * `child` - The cell's text or label.
pub fn aligned(align: Align, child: impl IntoElement) -> Div {
    div()
        .w_full()
        .flex()
        .when(align == Align::End, Div::justify_end)
        .child(child)
}
