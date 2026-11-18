//! The whole image as one listing in address order, paged by address in
//! both directions.
//!
//! Every byte of the image's mapped range belongs to one item, each from a
//! fact the engine holds: the instructions discovered blocks cover, written
//! by the function listing's own renderer ([`RowCtx`]) so a line here is
//! the line there; a string the walk found; a value of a type the user
//! applied or the debug information states; a word in data discovery
//! resolved to a function or another address; the bytes a data symbol
//! names; the bytes no fact covers, as hex rows under a line that says why
//! nothing covers them; and the gaps between sections. A section's first
//! row carries its header, a function's entry its header.
//!
//! The overview band ([`band`]) splits the same range into equal buckets,
//! each named by the kind of fact holding most of its bytes.
//!
//! A row is the lines one address shows, and a page is a run of rows from
//! where it starts. Pages count rows, not lines, and every row start is
//! found by lookup ([`Cx::row_start`]), never by walking from afar, so a
//! page is a pure function of its start, its direction and its row count,
//! and the page before a page is the one whose `next` it is.
//!
//! Where blocks overlap, the block that starts last owns each byte it
//! covers ([`stretches`]): a block entered in the middle of another's
//! instruction starts its own rows at its start.

use std::collections::BTreeMap;
use std::ops::Range;
use std::sync::Arc;

use super::disasm_view::{Bytes, RowCtx, hex_byte, hex_prefixed};
use super::typed::one_value;
use super::{Analysis, Overlay, RefKind, name_of, pointee_name};
use crate::analysis::utypes::{TypeExpr, width_of};
use crate::analysis::{BasicBlock, pointer_size, syscalls};
use crate::cancel::Cancel;
use crate::disasm;
use crate::isa::Isa;
use crate::num::from_usize;
use crate::program::{Feature, Program, SymbolKind};
use crate::strings::walk::for_each_walked;
use crate::strings::{DISPLAY_MAX, Encoding, RawStringSpan, escape_text};
use crate::text::plural;
use crate::view::{Builder, Kind, Ref, Sink, Unlinked, View};

/// Most rows one page holds: a request for more is cut to it.
pub const LINES_MAX: usize = 4096;

/// Bytes one hex row of an uncovered range shows.
const ROW_BYTES: u64 = 16;

/// Hex rows an uncovered range shows before one line skips the rest.
const RANGE_ROWS: u64 = 16;

/// Most instructions one block's row table holds; one row past them says
/// how far the block runs on.
const BLOCK_ROWS_MAX: usize = 1 << 16;

/// Most lines one row spends on the applied types it covers; one more line
/// counts the rest.
const LOST_LINES_MAX: usize = 8;

/// Instructions an ARM32 row decodes before its own, so the conditions of
/// an `IT` instruction, which reach at most four, reach it.
const IT_REACH: usize = 4;

/// The most bytes one x86 instruction spans.
const INSN_MAX: u64 = 15;

/// Most cells one band holds: a request for more is cut to it.
pub const CELLS_MAX: usize = 4096;

/// Which way a page runs from the address it is asked at.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dir {
    /// From the row holding the address onward.
    Next,
    /// The rows that end where the row holding the address starts.
    Prev,
}

/// What one row of a page shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowKind {
    /// An instruction of a discovered block.
    Instruction,
    /// Where a block runs on past the instructions its row table holds.
    Cut,
    /// The end of an instruction that starts in the section before.
    Spill,
    /// A string the walk found.
    String,
    /// A value of a type the user applied or the debug information states.
    Value,
    /// A word in data holding an address discovery resolved.
    Pointer,
    /// Hex bytes a name the file states names.
    Named,
    /// Hex bytes no fact covers.
    Unexplored,
    /// The rest of an uncovered range, past the hex rows it shows.
    Skipped,
    /// Bytes a section maps that the file holds none of.
    Unbacked,
    /// Addresses between two sections.
    Unmapped,
}

/// One row of a page: what it shows and the addresses it covers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    /// What the row shows.
    pub kind: RowKind,
    /// The row's address up to the next row's.
    pub span: Range<u64>,
}

/// One page of the linear listing.
#[derive(Debug, Clone)]
pub struct LinearPage {
    /// The page's lines; every line answers its row's address
    /// ([`View::address`]).
    pub view: View,
    /// The page's rows in address order, for a reader that lays them out.
    pub rows: Vec<Row>,
    /// The address of the page's first row.
    pub first: u64,
    /// Where the next page starts, `None` when this one reaches the image's
    /// end.
    pub next: Option<u64>,
    /// Where the page before this one starts, `None` when this one starts
    /// the image.
    pub prev: Option<u64>,
    /// The request was cancelled ([`Cancel::raised`]) before the page was
    /// whole: it holds the rows written by then, and its last line says so.
    pub cancelled: bool,
}

/// What holds the most bytes of one cell of the band.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CellKind {
    /// Instructions of discovered blocks.
    Code,
    /// A typed value, a pointer, or bytes a name the file states names.
    Data,
    /// A string the walk found.
    String,
    /// Bytes inside a section no fact covers, the file's or zero-filled.
    Unexplored,
    /// Addresses between two sections.
    Unmapped,
}

impl CellKind {
    /// Every kind, in the order a tie between them goes to.
    const ALL: [Self; 5] = [
        Self::Code,
        Self::Data,
        Self::String,
        Self::Unexplored,
        Self::Unmapped,
    ];

    /// Returns the kind's place in [`CellKind::ALL`].
    fn slot(self) -> usize {
        match self {
            Self::Code => 0,
            Self::Data => 1,
            Self::String => 2,
            Self::Unexplored => 3,
            Self::Unmapped => 4,
        }
    }
}

/// One cell of the overview band.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cell {
    /// The first address of its bucket.
    pub first: u64,
    /// The kind holding the most bytes of the bucket.
    pub kind: CellKind,
}

/// What covers one span of the image.
#[derive(Debug, Clone)]
enum Fact {
    /// Instructions of discovered blocks ([`Map::stretches`] says whose).
    Code,
    /// The end of the instruction at the address held, which starts in the
    /// section before.
    Spill(u64),
    /// A string the walk found ([`for_each_walked`]), with its terminator.
    Text(RawStringSpan),
    /// A value of a stated type.
    Typed(Typed),
    /// A word in data holding the address it names: a function's entry
    /// ([`RefKind::Table`]) or another address ([`RefKind::Ptr`]).
    Pointer(u64),
    /// Bytes a data symbol, or a debug global of no type the engine sizes,
    /// names: of no size the engine knows, they run to the next fact.
    Named(Named),
    /// File bytes inside a section that no fact covers.
    Unexplored,
    /// Bytes a section states the file holds that a truncated file lost.
    Missing,
    /// Bytes a section maps that the file holds none of.
    Unbacked,
    /// Addresses between two sections.
    Unmapped,
}

impl Fact {
    /// Returns the band's kind of the fact.
    fn cell(&self) -> CellKind {
        match self {
            Self::Code | Self::Spill(_) => CellKind::Code,
            Self::Text(_) => CellKind::String,
            Self::Typed(_) | Self::Pointer(_) | Self::Named(_) => CellKind::Data,
            Self::Unexplored | Self::Missing | Self::Unbacked => CellKind::Unexplored,
            Self::Unmapped => CellKind::Unmapped,
        }
    }
}

/// Where a typed value's type is stated, held as a place, not a copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Typed {
    /// A type the user applied at the span's start ([`Overlay::applied`]);
    /// `sized` when the engine knows its size, else it is laid over one
    /// byte.
    User {
        /// The engine knows the type's size.
        sized: bool,
    },
    /// A debug global, by its place in [`Program::debug_globals`].
    Debug(u32),
}

/// Where the name of a span of named bytes comes from, held as a place.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Named {
    /// A data symbol, by its place in [`Program::symbols`].
    Symbol(u32),
    /// A debug global of no type the engine sizes, by its place in
    /// [`Program::debug_globals`].
    Global(u32),
}

/// One stretch of the image and what covers it.
#[derive(Debug, Clone)]
struct Span {
    /// Its first address.
    start: u64,
    /// One past its last address.
    end: u64,
    /// What covers it.
    fact: Fact,
}

/// A stretch of code and the block whose instructions own it.
#[derive(Debug, Clone, Copy)]
struct Stretch {
    /// Its first address.
    start: u64,
    /// One past its last address.
    end: u64,
    /// The owning function, by its place in [`Analysis::functions`].
    func: u32,
    /// The owning block, by its place in that function's blocks.
    block: u32,
    /// The end of the last stretch the owning block owns, where its row
    /// table stops decoding.
    last: u64,
}

/// One section's stretch of the image, cut where another section already
/// maps it.
#[derive(Debug, Clone, Copy)]
struct Region {
    /// Its first address.
    start: u64,
    /// One past its last address.
    end: u64,
    /// One past the last address the file holds bytes for.
    backed: u64,
    /// One past the last address the section states file bytes for: those
    /// from [`Region::backed`] on are missing from a truncated file
    /// ([`crate::program::Section::lost`]), not zero-filled.
    missing: u64,
    /// The section, by its place in [`Program::sections`].
    section: usize,
}

/// The image's spans in address order, touching and disjoint from the first
/// section's start to the last one's end, with the code's owners.
#[derive(Debug)]
struct Map {
    /// The spans.
    spans: Vec<Span>,
    /// The code spans' stretches and their owners, in address order.
    stretches: Vec<Stretch>,
    /// The sections' regions, in address order.
    regions: Vec<Region>,
    /// The addresses of types the user applied that an earlier fact, code
    /// or no section covers, so the row showing those bytes says so.
    lost: Vec<u64>,
}

/// The rows of one block: the offsets from its start of the instructions
/// it decodes to, at most [`BLOCK_ROWS_MAX`], and where it runs on past
/// them.
#[derive(Debug, Default)]
struct BlockRows {
    /// Each instruction's offset from the block's start, ascending.
    offs: Vec<u32>,
    /// The address past the last instruction listed, when the block runs
    /// on past [`BLOCK_ROWS_MAX`] of them.
    cut: Option<u64>,
}

impl BlockRows {
    /// Returns the block's row starts in address order.
    ///
    /// # Arguments
    ///
    /// * `base` - The block's start.
    fn starts(&self, base: u64) -> impl DoubleEndedIterator<Item = u64> + '_ {
        let offs = self
            .offs
            .iter()
            .map(move |&o| base.saturating_add(u64::from(o)));
        offs.chain(self.cut)
    }

    /// Returns the last row start at or before `va`.
    ///
    /// # Arguments
    ///
    /// * `base` - The block's start.
    /// * `va` - Any address.
    fn at_or_before(&self, base: u64, va: u64) -> Option<u64> {
        if let Some(cut) = self.cut.filter(|&c| c <= va) {
            return Some(cut);
        }
        let k = self
            .offs
            .partition_point(|&o| base.saturating_add(u64::from(o)) <= va);
        self.starts(base).nth(k.checked_sub(1)?)
    }

    /// Returns the first row start at or after `va`.
    ///
    /// # Arguments
    ///
    /// * `base` - The block's start.
    /// * `va` - Any address.
    fn at_or_after(&self, base: u64, va: u64) -> Option<u64> {
        let k = self
            .offs
            .partition_point(|&o| base.saturating_add(u64::from(o)) < va);
        self.starts(base).skip(k).find(|&at| at >= va)
    }

    /// Returns the last row start of a stretch the block owns at or before
    /// `va`: an instruction of the table, or the stretch's own start when it
    /// lies past the table's cut and so starts a row of its own.
    ///
    /// # Arguments
    ///
    /// * `base` - The block's start.
    /// * `s` - The stretch.
    /// * `va` - An address of the stretch.
    fn before_in(&self, base: u64, s: &Stretch, va: u64) -> Option<u64> {
        if self.cut.is_some_and(|c| c < s.start) {
            return Some(s.start).filter(|&at| at <= va);
        }
        self.at_or_before(base, va).filter(|&at| at >= s.start)
    }

    /// Returns the first row start of a stretch the block owns at or after
    /// `va`, as [`BlockRows::before_in`] counts them.
    ///
    /// # Arguments
    ///
    /// * `base` - The block's start.
    /// * `s` - The stretch.
    /// * `va` - Any address.
    fn after_in(&self, base: u64, s: &Stretch, va: u64) -> Option<u64> {
        if self.cut.is_some_and(|c| c < s.start) {
            return Some(s.start).filter(|&at| at >= va);
        }
        self.at_or_after(base, va.max(s.start))
            .filter(|&at| at < s.end)
    }

    /// Returns the heap bytes the table holds.
    fn bytes(&self) -> usize {
        self.offs.capacity().saturating_mul(size_of::<u32>())
    }
}

impl Map {
    /// Builds the map of a program under an overlay.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded image.
    /// * `a` - The analysis, for the blocks, the references and the strings.
    /// * `o` - The overlay, whose applied types are facts.
    fn build(p: &Program, a: &Analysis, o: &Overlay) -> Self {
        let regions = regions(p);
        let raw = stretches(a);
        let mut lost = Vec::new();
        let mut data = data_facts(p, a, o, &raw, &mut lost).into_iter().peekable();
        let isa = p.isa_for(Feature::Disasm).ok();
        let mut spans: Vec<Span> = Vec::with_capacity(raw.len().saturating_mul(2));
        let mut kept: Vec<Stretch> = Vec::with_capacity(raw.len());
        let mut reach: Option<u64> = None;
        for r in &regions {
            if let Some(end) = reach.filter(|&e| e < r.start) {
                spans.push(Span {
                    start: end,
                    end: r.start,
                    fact: Fact::Unmapped,
                });
            }
            let mut here =
                isa.map_or_else(Vec::new, |isa| code_in(p, a, o, isa, &raw, r, &mut kept));
            while let Some(f) = data.next_if(|f| f.start < r.end) {
                if f.start >= r.start {
                    let end = f.end.min(r.end);
                    here.push(Span { end, ..f });
                } else {
                    lose(&f, &mut lost);
                }
            }
            here.sort_by_key(|s| s.start);
            let mut cur = r.start;
            for s in here {
                hole(&mut spans, r, cur, s.start);
                cur = s.end;
                spans.push(s);
            }
            hole(&mut spans, r, cur, r.end);
            reach = Some(r.end);
        }
        data.for_each(|f| lose(&f, &mut lost));
        lost.sort_unstable();
        Self {
            spans,
            stretches: kept,
            regions,
            lost,
        }
    }

    /// Returns the span holding `va`, `None` outside the image.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    fn span(&self, va: u64) -> Option<&Span> {
        let k = self
            .spans
            .partition_point(|s| s.start <= va)
            .checked_sub(1)?;
        self.spans.get(k).filter(|s| va < s.end)
    }

    /// Returns the place of the stretch holding `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    fn stretch(&self, va: u64) -> Option<usize> {
        let k = self
            .stretches
            .partition_point(|s| s.start <= va)
            .checked_sub(1)?;
        self.stretches.get(k).filter(|s| va < s.end).map(|_| k)
    }

    /// Returns the region holding `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    fn region(&self, va: u64) -> Option<&Region> {
        let k = self
            .regions
            .partition_point(|r| r.start <= va)
            .checked_sub(1)?;
        self.regions.get(k).filter(|r| va < r.end)
    }

    /// Returns the image's first address and one past its last, `None` for
    /// an image with no section.
    fn bounds(&self) -> Option<(u64, u64)> {
        Some((self.spans.first()?.start, self.spans.last()?.end))
    }
}

/// Returns the block that owns a stretch.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `s` - The stretch.
fn owner<'a>(a: &'a Analysis, s: &Stretch) -> Option<&'a BasicBlock> {
    let f = a.functions.get(usize::try_from(s.func).ok()?)?;
    f.blocks.get(usize::try_from(s.block).ok()?)
}

/// Returns the code spans of one region, pushing their stretches to `kept`.
///
/// A stretch the region cuts in the middle of an instruction starts its
/// code at the instruction after; the bytes before it are a
/// [`Fact::Spill`] of the instruction they end.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay in force.
/// * `isa` - The instruction set.
/// * `raw` - The code's stretches, uncut.
/// * `r` - The region.
/// * `kept` - Receives the region's stretches.
fn code_in(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    isa: Isa,
    raw: &[Stretch],
    r: &Region,
    kept: &mut Vec<Stretch>,
) -> Vec<Span> {
    let mut here: Vec<Span> = Vec::new();
    let k = raw.partition_point(|s| s.end <= r.start);
    for s in raw.iter().skip(k).take_while(|s| s.start < r.end) {
        let piece = Stretch {
            start: s.start.max(r.start),
            end: s.end.min(r.end),
            ..*s
        };
        let mut start = piece.start;
        if start > s.start {
            let Some(b) = owner(a, s) else {
                continue;
            };
            let rows = block_rows(p, a, o, isa, b, s.last);
            let first = rows.after_in(b.start, &piece, start);
            if first != Some(start) {
                let from = rows.at_or_before(b.start, start).unwrap_or(s.start);
                let end = first.unwrap_or(piece.end);
                here.push(Span {
                    start,
                    end,
                    fact: Fact::Spill(from),
                });
                start = end;
            }
        }
        if start >= piece.end {
            continue;
        }
        kept.push(Stretch { start, ..piece });
        match here.last_mut() {
            Some(last) if last.end == start && matches!(last.fact, Fact::Code) => {
                last.end = piece.end;
            }
            _ => here.push(Span {
                start,
                end: piece.end,
                fact: Fact::Code,
            }),
        }
    }
    here
}

/// Notes a fact no region places: a type the user applied there goes to
/// `lost`, so the row over its address says so; any other is dropped, its
/// bytes left to what holds them.
///
/// # Arguments
///
/// * `f` - The fact.
/// * `lost` - The addresses of the types left out.
fn lose(f: &Span, lost: &mut Vec<u64>) {
    if matches!(f.fact, Fact::Typed(Typed::User { .. })) {
        lost.push(f.start);
    }
}

/// Returns the code's stretches in address order, each owned by the block
/// that starts last among those covering it, a tie going to the one listed
/// last.
///
/// # Arguments
///
/// * `a` - The analysis.
fn stretches(a: &Analysis) -> Vec<Stretch> {
    let mut blocks: Vec<(u64, u64, u32, u32)> = a
        .functions
        .iter()
        .zip(0u32..)
        .flat_map(|(f, func)| {
            f.blocks
                .iter()
                .zip(0u32..)
                .filter(|(b, _)| b.start < b.end)
                .map(move |(b, block)| (b.start, b.end, func, block))
        })
        .collect();
    blocks.sort_unstable();
    let mut out: Vec<Stretch> = Vec::with_capacity(blocks.len());
    let mut open: Vec<(u64, u32, u32)> = Vec::new();
    let mut cur = 0u64;
    let last = (u64::MAX, u64::MAX, u32::MAX, u32::MAX);
    for (start, end, func, block) in blocks.into_iter().chain([last]) {
        while let Some(&(top, f, b)) = open.last() {
            let stop = top.min(start);
            if cur < stop {
                match out.last_mut() {
                    Some(l) if l.end == cur && (l.func, l.block) == (f, b) => l.end = stop,
                    _ => out.push(Stretch {
                        start: cur,
                        end: stop,
                        func: f,
                        block: b,
                        last: stop,
                    }),
                }
                cur = stop;
            }
            if top <= start {
                open.pop();
            } else {
                break;
            }
        }
        cur = cur.max(start);
        open.push((end, func, block));
    }
    let mut last: BTreeMap<(u32, u32), u64> = BTreeMap::new();
    for s in &out {
        last.insert((s.func, s.block), s.end);
    }
    for s in &mut out {
        s.last = last.get(&(s.func, s.block)).copied().unwrap_or(s.end);
    }
    out
}

/// Returns one block's row table, built once per block and kept in the
/// analysis's budgeted memo: its instructions' lengths alone, decoded from
/// its start no further than the last stretch it owns.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay in force, whose names key the memo.
/// * `isa` - The instruction set.
/// * `b` - The block.
/// * `last` - The end of the last stretch the block owns.
fn block_rows(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    isa: Isa,
    b: &BasicBlock,
    last: u64,
) -> Arc<BlockRows> {
    a.derived.get_or_build_item(
        "linear_rows",
        o.fingerprint(),
        (b.start, b.end, last),
        || {
            let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(usize::MAX);
            let Some(code) = p.read_va_upto(b.start, len.max(1)) else {
                return BlockRows::default();
            };
            let mut offs = Vec::new();
            let mut after = b.start;
            disasm::lengths(p, code, b.start, isa, last, BLOCK_ROWS_MAX, |va, size| {
                if let Ok(off) = u32::try_from(va.saturating_sub(b.start)) {
                    offs.push(off);
                }
                after = va.saturating_add(from_usize(size.max(1)));
            });
            let cut = (offs.len() >= BLOCK_ROWS_MAX && after < last).then_some(after);
            BlockRows { offs, cut }
        },
        BlockRows::bytes,
    )
}

/// Returns the sections' regions in address order.
///
/// File-backed sections come first, each cut to start where an earlier one ends; a section the
/// file holds no bytes for (`.bss`) fills only what none of them maps. A
/// thread-local `.tbss` takes no image addresses ([`crate::program::Section::span`])
/// and makes no region.
///
/// # Arguments
///
/// * `p` - The loaded image.
fn regions(p: &Program) -> Vec<Region> {
    let len = from_usize(p.bytes.len());
    let mut all: Vec<(bool, u64, u64, usize, u64, u64)> = p
        .sections
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let start = s.va.0;
            let held = s.file_size.min(len.saturating_sub(s.file_off.0));
            let end = s.span().end;
            let stated = s.file_size.saturating_add(s.lost).max(held);
            let (held, stated) = (start.saturating_add(held), start.saturating_add(stated));
            (held == start, start, end, i, held, stated)
        })
        .filter(|&(_, start, end, ..)| start < end)
        .collect();
    all.sort_unstable();
    let (mut backed, mut bare): (Vec<Region>, Vec<Region>) = (Vec::new(), Vec::new());
    for (no_bytes, start, end, section, held, stated) in all {
        let into = if no_bytes { &mut bare } else { &mut backed };
        let start = into.last().map_or(start, |r| start.max(r.end));
        if start < end {
            into.push(Region {
                start,
                end,
                backed: held.max(start).min(end),
                missing: stated.max(start).min(end),
                section,
            });
        }
    }
    let mut pieces: Vec<Region> = Vec::new();
    for r in &bare {
        let mut cur = r.start;
        let k = backed.partition_point(|b| b.end <= cur);
        for b in backed.iter().skip(k).take_while(|b| b.start < r.end) {
            if cur < b.start {
                pieces.push(Region {
                    start: cur,
                    end: b.start,
                    backed: cur,
                    ..*r
                });
            }
            cur = cur.max(b.end);
        }
        if cur < r.end {
            pieces.push(Region {
                start: cur,
                backed: cur,
                ..*r
            });
        }
    }
    backed.extend(pieces);
    backed.sort_unstable_by_key(|r| r.start);
    backed
}

/// Pushes the uncovered stretch `from..to` of a region.
///
/// The part the file holds is [`Fact::Unexplored`], the part a truncated
/// file lost [`Fact::Missing`], the rest [`Fact::Unbacked`]. The bytes a [`Fact::Named`] span names run on into the part the file holds.
///
/// # Arguments
///
/// * `spans` - The spans so far.
/// * `r` - The region.
/// * `from` - The stretch's first address.
/// * `to` - One past its last.
fn hole(spans: &mut Vec<Span>, r: &Region, mut from: u64, to: u64) {
    let cut = r.backed.max(from).min(to);
    if let Some(named) = spans.last_mut().filter(|s| {
        s.start >= r.start && s.end == from && from < cut && matches!(s.fact, Fact::Named(_))
    }) {
        named.end = cut;
        from = cut;
    }
    let lost = r.missing.max(cut).min(to);
    for (start, end, fact) in [
        (from, cut, Fact::Unexplored),
        (cut, lost, Fact::Missing),
        (lost, to, Fact::Unbacked),
    ] {
        if start < end {
            spans.push(Span { start, end, fact });
        }
    }
}

/// Returns the facts of data in address order, each overlapping no code and
/// no fact before it, one vector from the string walk on; each type the
/// user applied that loses that way goes to `lost`.
///
/// At one address they win in the order [`rank`] gives: a type the user
/// applied, a debug global, a pointer, a string with its terminator, a data
/// symbol.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The types the user applied.
/// * `code` - The code's stretches, disjoint and in address order.
/// * `lost` - Receives the address of each applied type left out.
fn data_facts(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    code: &[Stretch],
    lost: &mut Vec<u64>,
) -> Vec<Span> {
    let word = pointer_size(p);
    let span = |start: u64, width: u64, fact: Fact| Span {
        start,
        end: start.saturating_add(width.max(1)),
        fact,
    };
    let mut out = Vec::new();
    for_each_walked(p, a, |s| {
        let len = from_usize(s.raw_bytes(&p.bytes).len());
        if let Some(va) = p.offset_to_va(s.off).filter(|_| len > 0) {
            out.push(span(
                va,
                len.saturating_add(terminator(p, s, len)),
                Fact::Text(s),
            ));
        }
    });
    for (&va, ty) in &o.applied {
        let width = width_of(&o.types, ty, word);
        let fact = Fact::Typed(Typed::User {
            sized: width.is_some(),
        });
        out.push(span(va, width.unwrap_or(1), fact));
    }
    for (g, i) in p.debug_globals.iter().zip(0u32..) {
        let Some(va) = g.addr else {
            continue;
        };
        let width =
            g.ty.as_ref()
                .and_then(|ty| width_of(&p.debug_types, ty, word));
        out.push(match width {
            Some(width) => span(va, width, Fact::Typed(Typed::Debug(i))),
            None => span(va, 1, Fact::Named(Named::Global(i))),
        });
    }
    for (&target, sites) in &a.xrefs {
        for s in sites
            .iter()
            .filter(|s| matches!(s.kind, RefKind::Table | RefKind::Ptr))
        {
            out.push(span(s.va, word, Fact::Pointer(target)));
        }
    }
    for (sym, i) in p.symbols.iter().zip(0u32..) {
        if sym.kind == SymbolKind::Data {
            out.push(span(sym.addr, 1, Fact::Named(Named::Symbol(i))));
        }
    }
    out.sort_by_key(|f| (f.start, rank(&f.fact)));
    let mut reach: Option<u64> = None;
    out.retain(|f| {
        let k = code.partition_point(|s| s.end <= f.start);
        let on_code = code.get(k).is_some_and(|s| s.start < f.end);
        let free = !on_code && reach.is_none_or(|end| end <= f.start);
        if free {
            reach = Some(f.end);
        } else {
            lose(f, lost);
        }
        free
    });
    out
}

/// Returns where a fact stands among the facts at one address: lower wins.
///
/// # Arguments
///
/// * `f` - The fact.
fn rank(f: &Fact) -> u8 {
    match f {
        Fact::Typed(Typed::User { .. }) => 0,
        Fact::Typed(Typed::Debug(_)) => 1,
        Fact::Pointer(_) => 2,
        Fact::Text(_) => 3,
        Fact::Named(_) => 4,
        Fact::Code
        | Fact::Spill(_)
        | Fact::Unexplored
        | Fact::Missing
        | Fact::Unbacked
        | Fact::Unmapped => 5,
    }
}

/// Returns the bytes of the NUL that ends a string, none when no NUL
/// follows its text.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `s` - The string.
/// * `len` - The bytes of its text.
fn terminator(p: &Program, s: RawStringSpan, len: u64) -> u64 {
    let unit: u64 = match s.encoding {
        Encoding::Ascii => 1,
        Encoding::Utf16 | Encoding::DotnetUs => 2,
    };
    let at = s.off.saturating_add(len);
    let nul = usize::try_from(at)
        .ok()
        .and_then(|at| {
            p.bytes
                .get(at..at.checked_add(usize::try_from(unit).ok()?)?)
        })
        .is_some_and(|b| b.iter().all(|&x| x == 0));
    if nul { unit } else { 0 }
}

/// Returns the program's map under an overlay's types, built once and kept
/// in the analysis's memo, outside the item budget, while those names are in
/// force: a page never builds it again.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay, whose applied types are facts of the map.
fn map(p: &Program, a: &Analysis, o: &Overlay) -> Arc<Map> {
    a.derived
        .get_or_build_named("linear_map", o.fingerprint(), (), || Map::build(p, a, o))
}

/// Returns where the hex rows of an uncovered span stop and one line skips
/// the rest.
///
/// # Arguments
///
/// * `s` - The span.
fn skip_at(s: &Span) -> u64 {
    (s.start & !(ROW_BYTES - 1)).saturating_add(ROW_BYTES * RANGE_ROWS)
}

/// A sink that marks every line it writes as showing one address, so every
/// line of the linear listing answers [`View::address`].
struct Addressed<'s, S> {
    /// Where the lines go.
    out: &'s mut S,
    /// The address the next line shows.
    va: u64,
    /// The open line has had its address marked.
    marked: bool,
}

impl<S: Sink> Sink for Addressed<'_, S> {
    fn put(&mut self, piece: &str, kind: Kind, link: Option<Ref>) {
        if !self.marked {
            self.out.at(self.va);
            self.marked = true;
        }
        self.out.put(piece, kind, link);
    }

    fn define(&mut self) {
        self.out.define();
    }

    fn at(&mut self, va: u64) {
        self.out.at(va);
    }

    fn end_line(&mut self) {
        self.marked = false;
        self.out.end_line();
    }
}

/// What one page reads.
struct Cx<'a> {
    /// The loaded image.
    p: &'a Program,
    /// The analysis.
    a: &'a Analysis,
    /// User names and comments.
    o: &'a Overlay,
    /// The image's spans.
    map: &'a Map,
    /// The function listing's instruction renderer.
    rows: RowCtx<'a>,
    /// The instruction set.
    isa: Isa,
}

impl Cx<'_> {
    /// Returns the row table of the block owning a stretch.
    ///
    /// # Arguments
    ///
    /// * `k` - The stretch's place.
    fn table(&self, k: usize) -> Option<(&Stretch, &BasicBlock, Arc<BlockRows>)> {
        let s = self.map.stretches.get(k)?;
        let b = owner(self.a, s)?;
        Some((
            s,
            b,
            block_rows(self.p, self.a, self.o, self.isa, b, s.last),
        ))
    }

    /// Returns the address of the row holding `va`: the last row start at
    /// or before it.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address of the image.
    fn row_start(&self, va: u64) -> u64 {
        let Some(s) = self.map.span(va) else {
            return va;
        };
        match s.fact {
            Fact::Code => self.code_row_start(va, s.start),
            Fact::Unexplored | Fact::Named(_) => hex_row_start(s, va),
            Fact::Spill(_)
            | Fact::Text(_)
            | Fact::Typed(_)
            | Fact::Pointer(_)
            | Fact::Missing
            | Fact::Unbacked
            | Fact::Unmapped => s.start,
        }
    }

    /// Returns the last instruction row at or before `va` in a code span:
    /// in the stretch holding it, else in the stretches before it, else the
    /// span's start.
    ///
    /// # Arguments
    ///
    /// * `va` - An address in the span.
    /// * `floor` - The span's start, itself a row.
    fn code_row_start(&self, va: u64, floor: u64) -> u64 {
        let mut k = self.map.stretch(va);
        let mut x = va;
        while let Some((s, b, rows)) = k.and_then(|k| self.table(k)) {
            if Cancel::raised() {
                break;
            }
            if let Some(at) = rows.before_in(b.start, s, x) {
                return at.max(floor);
            }
            if s.start <= floor {
                break;
            }
            x = s.start.saturating_sub(1);
            k = k.and_then(|k| k.checked_sub(1));
        }
        floor
    }

    /// Returns the first instruction row after `va` in a code span, or the
    /// span's end.
    ///
    /// # Arguments
    ///
    /// * `va` - A row of the span.
    /// * `end` - The span's end.
    fn code_row_after(&self, va: u64, end: u64) -> u64 {
        let mut k = self.map.stretch(va);
        let mut x = va.saturating_add(1);
        while let Some((s, b, rows)) = k.and_then(|k| self.table(k)) {
            if s.start >= end || Cancel::raised() {
                break;
            }
            if let Some(at) = rows.after_in(b.start, s, x) {
                return at.min(end);
            }
            x = s.end;
            k = k.map(|k| k.saturating_add(1));
        }
        end
    }

    /// Returns where the `n` rows that end at `end` start, or the image's
    /// start when fewer rows come before it.
    ///
    /// # Arguments
    ///
    /// * `end` - A row's address.
    /// * `n` - How many rows.
    ///
    /// # Returns
    ///
    /// The start, and whether the request was cancelled before it went all
    /// the way back, which leaves the start nearer `end`.
    fn back(&self, mut end: u64, n: usize) -> (u64, bool) {
        let lo = self.map.bounds().map_or(end, |(lo, _)| lo);
        for _ in 0..n {
            if end <= lo {
                break;
            }
            if Cancel::raised() {
                return (end, true);
            }
            end = self.row_start(end - 1);
        }
        (end, false)
    }

    /// Writes `n` rows from the row at `from`, or fewer at the image's end.
    ///
    /// # Arguments
    ///
    /// * `from` - A row's address.
    /// * `n` - Most rows written.
    /// * `out` - The destination sink.
    ///
    /// # Returns
    ///
    /// The rows written, the address of the first row not written, and
    /// whether the request was cancelled first, which the last line says.
    fn write<S: Sink>(&self, from: u64, n: usize, out: &mut S) -> (Vec<Row>, u64, bool) {
        let mut out = Addressed {
            out,
            va: from,
            marked: false,
        };
        let mut fmt = disasm::X86Format::new();
        let mut rows = Vec::with_capacity(n);
        let mut cur = from;
        while rows.len() < n {
            let Some(s) = self.map.span(cur) else {
                break;
            };
            if Cancel::raised() {
                out.va = cur;
                comment(
                    &mut out,
                    "; cancelled: the page stops here, short of its rows",
                );
                return (rows, cur, true);
            }
            out.va = cur;
            if let Some(r) = self.map.region(cur).filter(|r| r.start == cur) {
                self.section_line(r, &mut out);
            }
            let (kind, next) = self.row(s, cur, &mut fmt, &mut out);
            self.lost_lines(cur, next, &mut out);
            rows.push(Row {
                kind,
                span: cur..next,
            });
            if next <= cur {
                break;
            }
            cur = next;
        }
        (rows, cur, false)
    }

    /// Writes the lines of the row at `cur` of a span.
    ///
    /// # Arguments
    ///
    /// * `s` - The span.
    /// * `cur` - The row's address.
    /// * `fmt` - The x86 formatter, kept across a page's instructions.
    /// * `out` - The destination sink.
    ///
    /// # Returns
    ///
    /// What the row shows and the address of the next row.
    fn row<S: Sink>(
        &self,
        s: &Span,
        cur: u64,
        fmt: &mut disasm::X86Format,
        out: &mut S,
    ) -> (RowKind, u64) {
        match &s.fact {
            Fact::Code => {
                let kind = self.instruction(cur, fmt, out);
                (kind, self.code_row_after(cur, s.end))
            }
            Fact::Spill(from) => {
                let why = format!("the end of the instruction at {from:#x}, in the section before");
                comment(out, &range_text("code", s, &why));
                (RowKind::Spill, s.end)
            }
            Fact::Text(text) => {
                self.text_line(s, *text, out);
                (RowKind::String, s.end)
            }
            Fact::Typed(t) => {
                self.typed_line(s, *t, out);
                (RowKind::Value, s.end)
            }
            Fact::Pointer(target) => {
                self.pointer_line(cur, *target, out);
                (RowKind::Pointer, s.end)
            }
            Fact::Named(named) => {
                if cur == s.start {
                    let what = format!("data {}", self.name_of_named(*named));
                    let why = "a name the file states, of no size the engine knows";
                    comment(out, &range_text(&what, s, why));
                }
                self.hex_row(s, cur, RowKind::Named, out)
            }
            Fact::Unexplored => {
                if cur == s.start {
                    comment(out, &range_text("unexplored", s, &self.reason(s)));
                }
                self.hex_row(s, cur, RowKind::Unexplored, out)
            }
            Fact::Missing => {
                let why = "the file is cut short before the bytes its header states";
                comment(out, &range_text("missing", s, why));
                (RowKind::Unbacked, s.end)
            }
            Fact::Unbacked => {
                let why = "the file holds no bytes for it";
                comment(out, &range_text("zero-filled", s, why));
                (RowKind::Unbacked, s.end)
            }
            Fact::Unmapped => {
                comment(out, &range_text("unmapped", s, "no section maps it"));
                (RowKind::Unmapped, s.end)
            }
        }
    }

    /// Writes a section's header line.
    ///
    /// # Arguments
    ///
    /// * `r` - The section's region.
    /// * `out` - The destination sink.
    fn section_line<S: Sink>(&self, r: &Region, out: &mut S) {
        let Some(s) = self.p.sections.get(r.section) else {
            return;
        };
        let file = self
            .p
            .va_to_offset(r.start)
            .filter(|_| r.backed > r.start)
            .map_or_else(
                || "no file bytes".to_owned(),
                |off| format!("file offset {off:#x}"),
            );
        comment(
            out,
            &format!(
                "; section {} {} {:#x}..{:#x} ({:#x} bytes), {file}",
                s.name,
                s.perms(),
                r.start,
                r.end,
                r.end.saturating_sub(r.start)
            ),
        );
    }

    /// Writes one instruction row: its function's header or its block's
    /// label, then the instruction as the function listing writes it, or
    /// the line saying where a block runs on past its row table.
    ///
    /// The instruction decodes from its own address; on ARM32 from at most
    /// [`IT_REACH`] rows before it, whose `IT` conditions it may carry.
    ///
    /// # Arguments
    ///
    /// * `va` - The row's address.
    /// * `fmt` - The x86 formatter.
    /// * `out` - The destination sink.
    ///
    /// # Returns
    ///
    /// What the row shows.
    fn instruction<S: Sink>(&self, va: u64, fmt: &mut disasm::X86Format, out: &mut S) -> RowKind {
        let Some((s, b, rows)) = self.map.stretch(va).and_then(|k| self.table(k)) else {
            comment(out, "; no block owns these bytes");
            return RowKind::Instruction;
        };
        if rows.cut.is_some_and(|c| c <= va) {
            let more = s.end.saturating_sub(va);
            comment(
                out,
                &format!(
                    "; {more:#x} bytes of the block to {:#x} are past the {BLOCK_ROWS_MAX} instructions a block lists",
                    s.end
                ),
            );
            return RowKind::Cut;
        }
        self.head(va, b.start, out);
        let mut shown = false;
        match self.isa {
            Isa::X86 { bits } => {
                let len = usize::try_from(b.end.saturating_sub(va).min(INSN_MAX)).unwrap_or(0);
                let code = self.p.read_va_upto(va, len.max(1)).unwrap_or_default();
                disasm::decode_x86(code, va, bits, 1, |d| {
                    self.rows.x86_row(fmt, &d, out);
                    shown = true;
                });
            }
            isa @ (Isa::A64 | Isa::A32 | Isa::Rv(_)) => {
                let k = rows
                    .offs
                    .partition_point(|&o| b.start.saturating_add(u64::from(o)) < va);
                let back = if matches!(isa, Isa::A32) {
                    IT_REACH.min(k)
                } else {
                    0
                };
                let from = rows.starts(b.start).nth(k - back).unwrap_or(va);
                let len = usize::try_from(b.end.saturating_sub(from)).unwrap_or(0);
                let code = self.p.read_va_upto(from, len.max(1)).unwrap_or_default();
                let lines = disasm::disassemble_program(self.p, code, from, isa, back + 1);
                for l in lines.iter().filter(|l| l.va == va) {
                    self.rows.isa_row(l, isa, out);
                    shown = true;
                }
            }
        }
        if !shown {
            comment(out, "; the bytes here do not decode");
        }
        RowKind::Instruction
    }

    /// Writes what heads an instruction's row: its function's header at an
    /// entry, else its block's `L_<addr>:` label at a block's start, as the
    /// function listing spells it.
    ///
    /// # Arguments
    ///
    /// * `va` - The instruction's address.
    /// * `block` - The start of the block owning it.
    /// * `out` - The destination sink.
    fn head<S: Sink>(&self, va: u64, block: u64, out: &mut S) {
        let mut buf = [0u8; 18];
        if let Some(f) = self.a.function(va) {
            out.put("; function ", Kind::Comment, None);
            out.put(
                &name_of(self.a, self.o, va),
                Kind::Function,
                Some(Ref::Function(va)),
            );
            out.define();
            let source = if self.o.names.contains_key(&va) {
                "user"
            } else {
                f.name_source.code()
            };
            let n = f.callers.len();
            out.put(
                &format!(": name {source}, {n} caller{}", plural(n)),
                Kind::Comment,
                None,
            );
            out.end_line();
        } else if va == block {
            out.put(
                hex_prefixed(b"L_", va, &mut buf),
                Kind::Label,
                Some(Ref::Address(va)),
            );
            out.define();
            out.put(":", Kind::Punct, None);
            out.end_line();
        }
    }

    /// Writes a line for each type the user applied inside `cur..next` that
    /// an earlier fact, code or no section covers, so none is left out
    /// unsaid: at most [`LOST_LINES_MAX`], then one line counting the rest.
    ///
    /// # Arguments
    ///
    /// * `cur` - The row's address.
    /// * `next` - The next row's address.
    /// * `out` - The destination sink.
    fn lost_lines<S: Sink>(&self, cur: u64, next: u64, out: &mut S) {
        let lost = &self.map.lost;
        let from = lost.partition_point(|&va| va < cur);
        let to = lost.partition_point(|&va| va < next).max(from);
        for &va in lost
            .get(from..to)
            .unwrap_or_default()
            .iter()
            .take(LOST_LINES_MAX)
        {
            let ty = self
                .o
                .applied
                .get(&va)
                .map_or_else(String::new, TypeExpr::spell);
            comment(
                out,
                &format!(
                    "; the type {ty} applied at {va:#x} is not laid out: what this row shows covers it"
                ),
            );
        }
        let more = to.saturating_sub(from).saturating_sub(LOST_LINES_MAX);
        if more > 0 {
            comment(
                out,
                &format!("; and {more} more types applied under this row, not laid out"),
            );
        }
    }

    /// Returns the name a span of named bytes goes by.
    ///
    /// # Arguments
    ///
    /// * `named` - Where the name comes from.
    fn name_of_named(&self, named: Named) -> &str {
        let at = |i: u32| usize::try_from(i).unwrap_or(usize::MAX);
        let name = match named {
            Named::Symbol(i) => self.p.symbols.get(at(i)).map(|s| s.name.as_str()),
            Named::Global(i) => self.p.debug_globals.get(at(i)).map(|g| g.name.as_str()),
        };
        name.unwrap_or("?")
    }

    /// Writes one hex row of a span of bytes no fact sizes: 16 bytes, or
    /// past [`RANGE_ROWS`] rows one line skipping the rest.
    ///
    /// # Arguments
    ///
    /// * `s` - The span.
    /// * `cur` - The row's address.
    /// * `kind` - What its hex rows show.
    /// * `out` - The destination sink.
    ///
    /// # Returns
    ///
    /// What the row shows and the address of the next row.
    fn hex_row<S: Sink>(&self, s: &Span, cur: u64, kind: RowKind, out: &mut S) -> (RowKind, u64) {
        let skip = skip_at(s);
        if cur >= skip {
            comment(
                out,
                &format!(
                    "; {:#x} more bytes not shown; the range ends at {:#x}",
                    s.end.saturating_sub(cur),
                    s.end
                ),
            );
            return (RowKind::Skipped, s.end);
        }
        let end = (cur & !(ROW_BYTES - 1))
            .saturating_add(ROW_BYTES)
            .min(s.end);
        let mut buf = [0u8; 18];
        out.put(hex_prefixed(b"0x", cur, &mut buf), Kind::Address, None);
        out.put(" ", Kind::Space, None);
        let len = usize::try_from(end.saturating_sub(cur)).unwrap_or(0);
        let mut pair = [0u8; 2];
        for &byte in self.p.read_va_upto(cur, len).unwrap_or_default() {
            out.put(" ", Kind::Space, None);
            out.put(hex_byte(byte, &mut pair), Kind::Number, None);
        }
        out.end_line();
        (kind, end)
    }

    /// Returns a string's text as a literal, decoded from no more of its
    /// bytes than the display cap shows.
    ///
    /// # Arguments
    ///
    /// * `text` - The string.
    fn literal(&self, text: RawStringSpan) -> String {
        let cap =
            u32::try_from(DISPLAY_MAX.saturating_add(1).saturating_mul(2)).unwrap_or(u32::MAX);
        let shown = RawStringSpan {
            len: text.len.min(cap),
            ..text
        };
        format!("\"{}\"", escape_text(&shown.text(&self.p.bytes)))
    }

    /// Writes a string's line: its text as a literal, linked as the
    /// string at its address, then its encoding and length; a string a
    /// section's end cuts shows the characters the section holds and says
    /// so.
    ///
    /// # Arguments
    ///
    /// * `s` - The string's span.
    /// * `text` - The string.
    /// * `out` - The destination sink.
    fn text_line<S: Sink>(&self, s: &Span, text: RawStringSpan, out: &mut S) {
        let unit: u64 = match text.encoding {
            Encoding::Ascii => 1,
            Encoding::Utf16 | Encoding::DotnetUs => 2,
        };
        let held = u32::try_from(s.end.saturating_sub(s.start) / unit).unwrap_or(u32::MAX);
        let shown = RawStringSpan {
            len: text.len.min(held),
            ..text
        };
        address(out, s.start);
        out.put(
            &self.literal(shown),
            Kind::String,
            Some(Ref::String(s.start)),
        );
        out.define();
        let mut note = format!("  ; {} {}", text.encoding.name(), text.len);
        if shown.len < text.len {
            note.push_str(&format!(", cut to {} where the section ends", shown.len));
        }
        out.put(&note, Kind::Comment, None);
        out.end_line();
    }

    /// Writes a typed value's line: the global's name, the type, the value
    /// as a typed read spells it ([`one_value`]) or, for a struct or an
    /// array of values, its size, then who stated the type.
    ///
    /// # Arguments
    ///
    /// * `s` - The value's span.
    /// * `t` - Where its type is stated.
    /// * `out` - The destination sink.
    fn typed_line<S: Sink>(&self, s: &Span, t: Typed, out: &mut S) {
        let global = match t {
            Typed::User { .. } => None,
            Typed::Debug(i) => usize::try_from(i)
                .ok()
                .and_then(|i| self.p.debug_globals.get(i)),
        };
        let (ty, known, sized, by) = match (t, global) {
            (Typed::User { sized }, _) => (
                self.o.applied.get(&s.start),
                &*self.o.types,
                sized,
                "  ; a type the user applied",
            ),
            (Typed::Debug(_), g) => (
                g.and_then(|g| g.ty.as_ref()),
                &self.p.debug_types,
                true,
                "  ; a type the debug information states",
            ),
        };
        address(out, s.start);
        if let Some(g) = global {
            out.put(&g.name, Kind::Global, Some(Ref::Global(s.start)));
            out.define();
            out.put(" ", Kind::Space, None);
        }
        let Some(ty) = ty else {
            comment(out, "; the type stated here is gone");
            return;
        };
        out.put(&ty.spell(), Kind::Type, None);
        out.put(" = ", Kind::Punct, None);
        let value = if sized {
            one_value(self.p, self.a, self.o, known, s.start, ty)
                .unwrap_or_else(|| format!("{{{:#x} bytes}}", s.end.saturating_sub(s.start)))
        } else {
            "(of no size: the type names nothing defined)".to_owned()
        };
        out.put(&value, Kind::Text, None);
        out.put(by, Kind::Comment, None);
        out.end_line();
    }

    /// Writes a pointer's line: the address it holds, then what is there,
    /// linked: the function starting there, else the string, else the
    /// name of what holds it, unlinked.
    ///
    /// # Arguments
    ///
    /// * `va` - Where the pointer is.
    /// * `target` - The address it holds.
    /// * `out` - The destination sink.
    fn pointer_line<S: Sink>(&self, va: u64, target: u64, out: &mut S) {
        address(out, va);
        out.put("ptr", Kind::Keyword, None);
        out.put(" ", Kind::Space, None);
        let string = self
            .map
            .span(target)
            .filter(|s| s.start == target)
            .and_then(|s| {
                if let Fact::Text(text) = s.fact {
                    Some(text)
                } else {
                    None
                }
            });
        let function = self.a.function(target).is_some();
        let link = if function {
            Some(Ref::Function(target))
        } else {
            string.map(|_| Ref::String(target))
        };
        let mut buf = [0u8; 18];
        out.put(
            hex_prefixed(b"0x", target, &mut buf),
            Kind::Address,
            link.clone(),
        );
        out.put("  ; -> ", Kind::Comment, None);
        if function {
            out.put(&name_of(self.a, self.o, target), Kind::Function, link);
        } else if let Some(text) = string {
            out.put(&self.literal(text), Kind::String, link);
        } else {
            let name = pointee_name(self.p, Some(self.a), self.o, target);
            out.put(name.as_deref().unwrap_or("(unmapped)"), Kind::Comment, None);
        }
        out.end_line();
    }

    /// Returns why no fact covers an uncovered span, in the engine's terms:
    /// a recorded reference into it that nothing typed, else that no
    /// reference the engine recorded reaches it, and that discovery ran out
    /// of fuel when it did and the span is in executable memory.
    ///
    /// Discovery keeps no reason a walk stopped at an address; its fuel
    /// running out ([`Analysis::incomplete`]) is the one it records.
    ///
    /// # Arguments
    ///
    /// * `s` - The span.
    fn reason(&self, s: &Span) -> String {
        let referenced = self
            .a
            .xrefs
            .range(s.start..s.end)
            .find_map(|(&target, sites)| Some((target, sites.first()?.va)));
        let mut why = referenced.map_or_else(
            || "no reference the engine recorded reaches it".to_owned(),
            |(target, site)| {
                format!("{target:#x} is referenced from {site:#x}, and no fact says what it holds")
            },
        );
        let executable = self
            .map
            .region(s.start)
            .and_then(|r| self.p.sections.get(r.section))
            .is_some_and(|sec| sec.executable);
        if self.a.incomplete && executable {
            why.push_str("; discovery ran out of fuel before it finished");
        }
        why
    }
}

/// Returns the hex row of an uncovered span holding `va`: its first row at
/// the span's start, then one every [`ROW_BYTES`] aligned, then the skip
/// line's.
///
/// # Arguments
///
/// * `s` - The span.
/// * `va` - An address in it.
fn hex_row_start(s: &Span, va: u64) -> u64 {
    let skip = skip_at(s);
    if va >= skip {
        skip
    } else {
        (va & !(ROW_BYTES - 1)).max(s.start)
    }
}

/// Writes the address that starts a line of data and the two spaces after
/// it, as an instruction line starts.
///
/// # Arguments
///
/// * `out` - The destination sink.
/// * `va` - The address.
fn address<S: Sink>(out: &mut S, va: u64) {
    let mut buf = [0u8; 18];
    out.put(hex_prefixed(b"0x", va, &mut buf), Kind::Address, None);
    out.put("  ", Kind::Space, None);
}

/// Returns the line naming a span: `; <what> <start>..<end> (<n> bytes): <why>`.
///
/// # Arguments
///
/// * `what` - What covers it.
/// * `s` - The span.
/// * `why` - What the engine says of it.
fn range_text(what: &str, s: &Span, why: &str) -> String {
    format!(
        "; {what} {:#x}..{:#x} ({:#x} bytes): {why}",
        s.start,
        s.end,
        s.end.saturating_sub(s.start)
    )
}

/// Writes one comment line.
///
/// # Arguments
///
/// * `out` - The destination sink.
/// * `text` - The line.
fn comment<S: Sink>(out: &mut S, text: &str) {
    out.put(text, Kind::Comment, None);
    out.end_line();
}

/// Returns one page of the image as one listing in address order.
///
/// The page starts at the row holding `at` (an address inside an
/// instruction backs up to its start) and runs `lines` rows on, or ends
/// `lines` rows before it. A row is the lines one address shows: a
/// section's header, a function's header or a block's label, a user's
/// name, then the instruction or the bytes; it counts once however many
/// lines it has. Instruction lines are the function listing's
/// ([`super::disasm_view()`]) without the bytes column, byte for byte. A
/// page decodes only the instructions it shows, and finds every row start
/// in a block's memoized row table.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names, comments and applied types.
/// * `at` - Any address; one outside the image is moved to its nearer end.
/// * `dir` - Which way the page runs from `at`.
/// * `lines` - Rows the page holds, 1 to [`LINES_MAX`]; a page ending at
///   the image's end holds fewer.
///
/// # Returns
///
/// The page, or `None` when the image has no section or the architecture
/// has no disassembler. A request cancelled before the page is whole
/// answers the rows written by then, none when it was cancelled from the
/// start, and is marked [`LinearPage::cancelled`]; a map built under a
/// raised cancel is not kept.
#[must_use]
pub fn linear(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    at: u64,
    dir: Dir,
    lines: usize,
) -> Option<LinearPage> {
    let isa = p.isa_for(Feature::Disasm).ok()?;
    let map = map(p, a, o);
    let (lo, hi) = map.bounds()?;
    let n = lines.clamp(1, LINES_MAX);
    let sites = syscalls::syscall_sites(p, a);
    let cx = Cx {
        p,
        a,
        o,
        map: &map,
        rows: RowCtx {
            program: p,
            analysis: a,
            overlay: o,
            sites: &sites,
            bytes: Bytes::Hidden,
        },
        isa,
    };
    let held = cx.row_start(at.max(lo).min(hi.saturating_sub(1)));
    let (first, early) = match dir {
        Dir::Next => (held, false),
        Dir::Prev => cx.back(held, n),
    };
    let mut b = Builder::default();
    let (rows, end, cut) = cx.write(first, n, &mut b);
    let (prev, late) = if first > lo {
        let (prev, late) = cx.back(first, n);
        (Some(prev), late)
    } else {
        (None, false)
    };
    Some(LinearPage {
        view: b.finish(Unlinked::default())?,
        rows,
        first,
        next: (end < hi).then_some(end),
        prev,
        cancelled: early || cut || late,
    })
}

/// Returns the image's overview band.
///
/// The band is its range from the first section's start to the last one's
/// end in equal address buckets, each with the kind
/// of fact holding the most of its bytes, a tie going to the kind first in
/// [`CellKind`]'s order.
///
/// Built once per count under the overlay's names from the linear
/// listing's own facts, and kept in the analysis's budgeted memo.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay, whose applied types are facts.
/// * `cells` - Buckets wanted, 1 to [`CELLS_MAX`].
///
/// # Returns
///
/// The cells in address order, at most as many as asked: buckets of one
/// whole number of bytes each, the last cut at the range's end, so a range
/// that does not divide evenly gets fewer; empty for an image with no
/// section or a request cancelled before the band was read.
#[must_use]
pub fn band(p: &Program, a: &Analysis, o: &Overlay, cells: usize) -> Vec<Cell> {
    let cells = cells.clamp(1, CELLS_MAX);
    if Cancel::raised() {
        return Vec::new();
    }
    a.derived
        .get_or_build_item(
            "linear_band",
            o.fingerprint(),
            cells,
            || buckets(&map(p, a, o), cells),
            |c| c.capacity().saturating_mul(size_of::<Cell>()),
        )
        .to_vec()
}

/// Splits the map's range into `cells` equal buckets and names each by the
/// kind holding the most of its bytes.
///
/// # Arguments
///
/// * `map` - The image's spans.
/// * `cells` - Buckets wanted, at least 1.
fn buckets(map: &Map, cells: usize) -> Vec<Cell> {
    let Some((lo, hi)) = map.bounds() else {
        return Vec::new();
    };
    let width = hi.saturating_sub(lo).div_ceil(from_usize(cells)).max(1);
    let count = usize::try_from(hi.saturating_sub(lo).div_ceil(width))
        .unwrap_or(cells)
        .min(cells);
    let mut bytes = vec![[0u64; CellKind::ALL.len()]; count];
    for s in &map.spans {
        let slot = s.fact.cell().slot();
        let mut at = s.start;
        while at < s.end {
            let i = at.saturating_sub(lo) / width;
            let to = i
                .saturating_add(1)
                .saturating_mul(width)
                .saturating_add(lo)
                .min(s.end);
            let Some(held) = usize::try_from(i)
                .ok()
                .and_then(|i| bytes.get_mut(i))
                .and_then(|b| b.get_mut(slot))
            else {
                break;
            };
            *held = held.saturating_add(to.saturating_sub(at));
            if to <= at {
                break;
            }
            at = to;
        }
    }
    bytes
        .iter()
        .zip(0u64..)
        .map(|(held, i)| Cell {
            first: lo.saturating_add(i.saturating_mul(width)),
            kind: CellKind::ALL.into_iter().fold(CellKind::Code, |best, k| {
                if held[k.slot()] > held[best.slot()] {
                    k
                } else {
                    best
                }
            }),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{Stretch, stretches};
    use crate::analysis::render::listing::tests::bare;
    use crate::analysis::{Analysis, BasicBlock, BlockTerm};

    /// Returns a block over `start..end`.
    ///
    /// # Arguments
    ///
    /// * `start` - Its first address.
    /// * `end` - One past its last.
    fn block(start: u64, end: u64) -> BasicBlock {
        BasicBlock {
            start,
            end,
            term: BlockTerm::Ret,
            successors: smallvec::SmallVec::new(),
        }
    }

    /// Returns the stretches as `(start, end, block)` triples.
    ///
    /// # Arguments
    ///
    /// * `out` - The stretches.
    fn spans(out: &[Stretch]) -> Vec<(u64, u64, u32)> {
        out.iter().map(|s| (s.start, s.end, s.block)).collect()
    }

    /// Nested blocks each own their bytes up to the next one inside.
    ///
    /// Three blocks nested inside one another each own the bytes from their
    /// start until the one inside them starts, and each outer block resumes
    /// where the inner one ends, its row table decoding to the end of the
    /// last stretch it owns.
    ///
    /// # Panics
    ///
    /// When a byte has another owner.
    #[test]
    fn the_block_that_starts_last_owns_each_byte() {
        let mut f = bare(0x10, None);
        f.blocks = vec![block(0x10, 0x20), block(0x12, 0x18), block(0x14, 0x16)];
        let mut a = Analysis::default();
        a.functions.push(f);
        let out = stretches(&a);
        assert_eq!(
            spans(&out),
            [
                (0x10, 0x12, 0),
                (0x12, 0x14, 1),
                (0x14, 0x16, 2),
                (0x16, 0x18, 1),
                (0x18, 0x20, 0),
            ]
        );
        let last: Vec<u64> = out.iter().map(|s| s.last).collect();
        assert_eq!(last, [0x20, 0x18, 0x16, 0x18, 0x20]);
    }

    /// Overlapping blocks of two functions each own their bytes.
    ///
    /// Two functions' blocks that overlap at a byte, the later one entered
    /// inside the earlier's instruction, own their own bytes from where each
    /// starts; an identical shared block goes to the function listed last.
    ///
    /// # Panics
    ///
    /// When a byte has another owner.
    #[test]
    fn a_block_entered_mid_instruction_owns_from_its_start() {
        let (mut f, mut g) = (bare(0x10, None), bare(0x11, None));
        f.blocks = vec![block(0x10, 0x12), block(0x20, 0x24)];
        g.blocks = vec![block(0x11, 0x14), block(0x20, 0x24)];
        let mut a = Analysis::default();
        a.functions.extend([f, g]);
        let out = stretches(&a);
        let owners: Vec<(u64, u64, u32)> = out.iter().map(|s| (s.start, s.end, s.func)).collect();
        assert_eq!(owners, [(0x10, 0x11, 0), (0x11, 0x14, 1), (0x20, 0x24, 1)]);
    }
}
