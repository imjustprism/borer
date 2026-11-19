//! Runs a search spec ([`super::spec`]) over the program and writes its
//! hits as a table, each saying how it matched.
//!
//! The places `in=` names are resolved first, and every find an `and in=`
//! follows scans only inside them. Bytes and texts walk each file byte
//! once and report a hit at every address a section maps the byte to (an
//! `in=` scope walks each address it holds), values each address of a
//! section once, in chunks of
//! at most [`CHUNK`] bytes that overlap by the length a match may run on:
//! the request's cancel flag is read before each and the progress in
//! force counts each, so a search over a large file reports how far it is
//! and stops at its deadline with a refusal, never a partial answer. Hits
//! come in address order, then those in bytes no section maps in file
//! order; a clause holds at most [`HELD_MAX`] of them, so set operations
//! work on whole sets, merged in one pass.

use std::collections::BTreeMap;

use super::spec::{Clause, Find, Order, Sign, Spec, Step, Text, Value};
use super::{Finder, HITS_MAX, Hit, Hits, Pattern, Span, Spelling, text_hits};
use crate::analysis::{Analysis, Overlay, name_of, resolve_suggesting};
use crate::num::{from_usize, saturating_usize};
use crate::program::{Program, Section};
use crate::table::Window;

/// Most bytes one chunk of a scan covers.
pub const CHUNK: usize = 1 << 20;

/// Pattern bytes per [`CHUNK`] shrink: a match test costs time in
/// proportion to the pattern, so a chunk of a long pattern is shorter and
/// the deadline is read about as often.
const PATTERN_STEP: usize = 64;

/// Fewest bytes a chunk covers, however long the pattern.
const CHUNK_MIN: usize = 4 << 10;

/// Returns the bytes one chunk covers for a match that may run `reach`
/// bytes past its first.
///
/// That is [`CHUNK`], cut for a long pattern so that each chunk's work
/// stays about [`CHUNK`] times [`PATTERN_STEP`] byte tests.
///
/// # Arguments
///
/// * `reach` - Bytes past a match's first it may cover.
fn chunk_len(reach: usize) -> usize {
    (CHUNK / (reach / PATTERN_STEP + 1)).max(CHUNK_MIN)
}

/// Most hits one clause holds; a clause finding more is refused.
pub const HELD_MAX: usize = 1 << 18;

/// Most distinct addresses one file byte may be mapped to before a byte
/// or text search refuses the file.
const MAPPINGS_MAX: usize = 8;

/// One hit of a search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Found {
    /// Its address; `None` in bytes no section maps.
    pub va: Option<u64>,
    /// Its file offset; `None` for an address the file holds no byte of.
    pub off: Option<u64>,
    /// How it matched.
    pub matched: Matched,
}

/// How a hit matched.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Matched {
    /// A byte pattern.
    Bytes,
    /// A text, in the spelling found.
    Text(Spelling),
    /// A data word in a section that is not executable.
    Data {
        /// The word's bytes.
        width: u8,
        /// Its byte order.
        order: Order,
    },
    /// An immediate operand of an instruction in a discovered function;
    /// the hit's address is the instruction's.
    Immediate {
        /// The operand's place in assembly order, from 0.
        operand: u8,
    },
    /// An immediate with the shift its instruction applies folded in
    /// (`movt`, `movk`, `lui`, an `lsl #n` operand).
    Shifted {
        /// The operand's place in assembly order, from 0.
        operand: u8,
    },
    /// A memory operand's encoded displacement, searched with `disp`.
    Displacement {
        /// The operand's place in assembly order, from 0.
        operand: u8,
    },
    /// The address a PC-relative memory operand reaches, searched with
    /// `disp`.
    Address {
        /// The operand's place in assembly order, from 0.
        operand: u8,
    },
}

impl Found {
    /// Returns where the hit is for ordering and set operations: its
    /// address, else its file offset after every address.
    fn place(&self) -> (bool, u64) {
        self.va
            .map_or((true, self.off.unwrap_or(0)), |va| (false, va))
    }

    /// Returns the key hits are ordered by: place, then offset and match.
    fn key(&self) -> ((bool, u64), Option<u64>, Matched) {
        (self.place(), self.off, self.matched)
    }
}

/// Addresses as sorted, disjoint, half-open ranges.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct Ranges(Vec<(u64, u64)>);

impl Ranges {
    /// Returns the ranges covering `ranges`, sorted and merged.
    ///
    /// # Arguments
    ///
    /// * `ranges` - Half-open ranges in any order; empty ones are dropped.
    fn of(mut ranges: Vec<(u64, u64)>) -> Self {
        ranges.retain(|r| r.0 < r.1);
        ranges.sort_unstable();
        let mut out: Vec<(u64, u64)> = Vec::with_capacity(ranges.len());
        for (lo, hi) in ranges {
            match out.last_mut() {
                Some(last) if lo <= last.1 => last.1 = last.1.max(hi),
                _ => out.push((lo, hi)),
            }
        }
        Ranges(out)
    }

    /// Tells whether an address lies in the ranges.
    ///
    /// # Arguments
    ///
    /// * `va` - The address.
    pub(super) fn holds(&self, va: u64) -> bool {
        let i = self.0.partition_point(|r| r.1 <= va);
        self.0.get(i).is_some_and(|r| r.0 <= va)
    }

    /// Returns the addresses both hold.
    ///
    /// # Arguments
    ///
    /// * `other` - The other ranges.
    fn and(&self, other: &Ranges) -> Ranges {
        let (mut i, mut j, mut out) = (0, 0, Vec::new());
        while let (Some(a), Some(b)) = (self.0.get(i), other.0.get(j)) {
            let (lo, hi) = (a.0.max(b.0), a.1.min(b.1));
            if lo < hi {
                out.push((lo, hi));
            }
            if a.1 < b.1 {
                i += 1;
            } else {
                j += 1;
            }
        }
        Ranges(out)
    }

    /// Returns the parts of `lo..hi` the ranges hold, ascending.
    ///
    /// # Arguments
    ///
    /// * `lo` - The first address.
    /// * `hi` - The address past the last.
    pub(super) fn clip(&self, lo: u64, hi: u64) -> impl Iterator<Item = (u64, u64)> + '_ {
        let from = self.0.partition_point(|r| r.1 <= lo);
        self.0
            .get(from..)
            .unwrap_or_default()
            .iter()
            .take_while(move |r| r.0 < hi)
            .map(move |r| (r.0.max(lo), r.1.min(hi)))
    }
}

/// One run of bytes a find walks.
#[derive(Debug, Clone)]
struct Piece<'p> {
    /// Address of its first byte; `None` where no section maps it.
    va: Option<u64>,
    /// The other addresses sections map its first byte to, ascending.
    also: Vec<u64>,
    /// File offset of its first byte.
    off: u64,
    /// Its length in bytes.
    len: usize,
    /// Its bytes, then those after it a match may run on into, to the end
    /// of what it is read from.
    bytes: &'p [u8],
}

impl<'p> Piece<'p> {
    /// Returns the part of the piece from `skip` bytes in, `len` long.
    ///
    /// # Arguments
    ///
    /// * `skip` - Bytes of the piece left out before the part.
    /// * `len` - The part's length; the piece holds it.
    fn part(&self, skip: usize, len: usize) -> Piece<'p> {
        let by = from_usize(skip);
        Piece {
            va: self.va.map(|va| va.saturating_add(by)),
            also: self.also.iter().map(|va| va.saturating_add(by)).collect(),
            off: self.off.saturating_add(by),
            len,
            bytes: self.bytes.get(skip..).unwrap_or_default(),
        }
    }

    /// Returns the piece's parts a scope holds: the whole piece without a
    /// scope; with one, the parts each of its addresses keeps, one address
    /// each, and nothing of an unmapped piece.
    ///
    /// # Arguments
    ///
    /// * `clip` - The scope, if any.
    fn clipped<'a>(&'a self, clip: Option<&'a Ranges>) -> impl Iterator<Item = Piece<'p>> + 'a {
        let whole = clip.is_none().then(|| self.clone());
        let bases = clip.into_iter().flat_map(move |r| {
            self.va
                .into_iter()
                .chain(self.also.iter().copied())
                .map(move |b| (r, b))
        });
        let parts = bases.flat_map(move |(r, base)| {
            r.clip(base, base.saturating_add(from_usize(self.len)))
                .filter_map(move |(lo, hi)| {
                    let skip = saturating_usize(lo.checked_sub(base)?);
                    let mut part = self.part(skip, saturating_usize(hi - lo));
                    part.va = Some(lo);
                    part.also.clear();
                    Some(part)
                })
        });
        whole.into_iter().chain(parts)
    }

    /// Returns the piece's chunks of at most [`chunk_len`] bytes, each with
    /// the `reach` bytes after it a match starting in it may cover.
    ///
    /// # Arguments
    ///
    /// * `reach` - Bytes past a chunk's end a match may cover.
    fn chunks(&self, reach: usize) -> impl Iterator<Item = Span<'p>> + '_ {
        let step = chunk_len(reach);
        (0..self.len.div_ceil(step)).filter_map(move |k| {
            let from = k.checked_mul(step)?;
            let len = step.min(self.len.checked_sub(from)?);
            let to = from
                .saturating_add(len)
                .saturating_add(reach)
                .min(self.bytes.len());
            Some(Span {
                data: self.bytes.get(from..to)?,
                own: from_usize(len),
                off: self.off.saturating_add(from_usize(from)),
                va: self.va.map(|va| va.saturating_add(from_usize(from))),
            })
        })
    }
}

/// The parts of a line of offsets or addresses already walked.
#[derive(Debug, Default)]
struct Covered(BTreeMap<u64, u64>);

impl Covered {
    /// Marks `lo..hi` walked and returns its parts not walked before,
    /// ascending.
    ///
    /// # Arguments
    ///
    /// * `lo` - The first offset.
    /// * `hi` - The offset past the last.
    fn fresh(&mut self, lo: u64, hi: u64) -> Vec<(u64, u64)> {
        let from = self.0.range(..=lo).next_back().map_or(lo, |(&s, _)| s);
        let near: Vec<(u64, u64)> = self
            .0
            .range(from..hi)
            .map(|(&s, &e)| (s, e))
            .filter(|&(_, e)| e >= lo)
            .collect();
        let (mut at, mut parts) = (lo, Vec::new());
        for &(s, e) in &near {
            if s > at {
                parts.push((at, s.min(hi)));
            }
            at = at.max(e);
        }
        if at < hi {
            parts.push((at, hi));
        }
        let merged = near
            .iter()
            .fold((lo, hi), |(l, h), &(s, e)| (l.min(s), h.max(e)));
        for (s, _) in near {
            self.0.remove(&s);
        }
        self.0.insert(merged.0, merged.1);
        parts
    }
}

/// One run of file offsets every section mapping it maps alike: the
/// distinct shifts from a file offset to an address that its sections
/// apply ([`mapped_runs`]).
#[derive(Debug)]
struct Mapped {
    /// The first file offset.
    lo: u64,
    /// The file offset past the last.
    hi: u64,
    /// Each distinct `address - offset`, wrapping, ascending.
    shifts: Vec<u64>,
}

/// Returns the runs of file offsets the sections map, each with the
/// distinct shifts its sections apply, in offset order: one sweep over the
/// sections' starts and ends.
///
/// # Arguments
///
/// * `p` - The program.
/// * `keep` - Which sections count.
///
/// # Errors
///
/// When some byte is mapped to more than [`MAPPINGS_MAX`] addresses.
fn mapped_runs(p: &Program, keep: impl Fn(&Section) -> bool) -> Result<Vec<Mapped>, String> {
    let mut events: Vec<(u64, bool, u64)> = Vec::new();
    for s in p.sections.iter().filter(|s| s.file_size > 0 && keep(s)) {
        if p.section_bytes(s).is_some() {
            let (lo, shift) = (s.file_off.0, s.va.0.wrapping_sub(s.file_off.0));
            events.push((lo, true, shift));
            events.push((lo.saturating_add(s.file_size), false, shift));
        }
    }
    events.sort_unstable();
    let mut active: BTreeMap<u64, usize> = BTreeMap::new();
    let mut out: Vec<Mapped> = Vec::new();
    let mut at = 0;
    for run in events.chunk_by(|x, y| x.0 == y.0) {
        let Some(&(pos, _, _)) = run.first() else {
            continue;
        };
        if pos > at && !active.is_empty() {
            let shifts: Vec<u64> = active.keys().copied().collect();
            match out.last_mut() {
                Some(last) if last.hi == at && last.shifts == shifts => last.hi = pos,
                _ => out.push(Mapped {
                    lo: at,
                    hi: pos,
                    shifts,
                }),
            }
        }
        for &(_, opens, shift) in run {
            if opens {
                *active.entry(shift).or_default() += 1;
            } else if let Some(n) = active.get_mut(&shift) {
                *n -= 1;
                if *n == 0 {
                    active.remove(&shift);
                }
            }
        }
        if active.len() > MAPPINGS_MAX {
            return Err(format!(
                "the file maps one byte at more than {MAPPINGS_MAX} addresses; a search refuses it rather than walk each byte once per address"
            ));
        }
        at = pos;
    }
    Ok(out)
}

/// Returns the runs of the file a byte or text find walks, each file byte
/// once.
///
/// Each section's file bytes come in declaration order, a byte already
/// walked left out, each run with every other address sections map it to;
/// then the bytes no section maps.
///
/// # Arguments
///
/// * `p` - The program.
///
/// # Errors
///
/// As [`mapped_runs`].
fn file_pieces(p: &Program) -> Result<Vec<Piece<'_>>, String> {
    let file = p.bytes.as_slice();
    let runs = mapped_runs(p, |_| true)?;
    let mut covered = Covered::default();
    let mut out = Vec::new();
    for s in p.sections.iter().filter(|s| s.file_size > 0) {
        if p.section_bytes(s).is_none() {
            continue;
        }
        let (lo, shift) = (s.file_off.0, s.va.0.wrapping_sub(s.file_off.0));
        for (a, b) in covered.fresh(lo, lo.saturating_add(s.file_size)) {
            let first = runs.partition_point(|r| r.hi <= a);
            for r in runs
                .get(first..)
                .unwrap_or_default()
                .iter()
                .take_while(|r| r.lo < b)
            {
                let (x, y) = (a.max(r.lo), b.min(r.hi));
                out.push(Piece {
                    va: Some(x.wrapping_add(shift)),
                    also: r
                        .shifts
                        .iter()
                        .filter(|&&d| d != shift)
                        .map(|&d| x.wrapping_add(d))
                        .collect(),
                    off: x,
                    len: saturating_usize(y - x),
                    bytes: file.get(saturating_usize(x)..).unwrap_or_default(),
                });
            }
        }
    }
    for (off, run) in p.unmapped() {
        let hi = off.saturating_add(from_usize(run.len()));
        for (a, b) in covered.fresh(off, hi) {
            out.push(Piece {
                va: None,
                also: Vec::new(),
                off: a,
                len: saturating_usize(b - a),
                bytes: file.get(saturating_usize(a)..).unwrap_or_default(),
            });
        }
    }
    Ok(out)
}

/// Returns the runs a value's data words are read from: the file bytes of
/// each section that is not executable as the image holds them
/// (relocated), an address already walked left out.
///
/// Each address is read, so a file byte that such sections map at more
/// than [`MAPPINGS_MAX`] addresses is refused, as a byte search refuses
/// it ([`mapped_runs`]).
///
/// # Errors
///
/// As [`mapped_runs`].
///
/// # Arguments
///
/// * `p` - The program.
fn data_pieces(p: &Program) -> Result<Vec<Piece<'_>>, String> {
    mapped_runs(p, |s| !s.executable)?;
    let mut covered = Covered::default();
    let mut out = Vec::new();
    for s in p
        .sections
        .iter()
        .filter(|s| !s.executable && s.file_size > 0)
    {
        let Some(bytes) = p.section_bytes(s) else {
            continue;
        };
        let va = s.va.0;
        for (a, b) in covered.fresh(va, va.saturating_add(from_usize(bytes.len()))) {
            let skip = saturating_usize(a - va);
            out.push(Piece {
                va: Some(a),
                also: Vec::new(),
                off: s.file_off.0.saturating_add(a - va),
                len: saturating_usize(b - a),
                bytes: bytes.get(skip..).unwrap_or_default(),
            });
        }
    }
    Ok(out)
}

/// Where a scan puts its hits.
pub(super) trait Sink {
    /// Takes one hit.
    ///
    /// # Arguments
    ///
    /// * `hit` - The hit.
    fn push(&mut self, hit: Found);

    /// Whether the sink took more hits than it holds.
    fn full(&self) -> bool;

    /// How many more hits are worth finding before the sink is full: one
    /// past its room, so that filling it shows.
    fn room(&self) -> usize;
}

/// The hits one clause found, at most [`HELD_MAX`].
#[derive(Debug, Default)]
pub(super) struct Held {
    /// The hits, in the order found.
    hits: Vec<Found>,
    /// Whether a hit past the cap was dropped.
    over: bool,
}

impl Sink for Held {
    /// Keeps a hit, or notes one past the cap.
    fn push(&mut self, hit: Found) {
        if self.hits.len() < HELD_MAX {
            self.hits.push(hit);
        } else {
            self.over = true;
        }
    }

    /// Whether a hit was dropped at the cap.
    fn full(&self) -> bool {
        self.over
    }

    /// The hits left under the cap, and one more.
    fn room(&self) -> usize {
        (HELD_MAX + 1).saturating_sub(self.hits.len())
    }
}

impl Held {
    /// Returns the hits in order, each once.
    pub(super) fn sorted(mut self) -> Vec<Found> {
        self.hits.sort_unstable_by_key(Found::key);
        self.hits.dedup();
        self.hits
    }
}

/// One page of hits in scan order and the count of all of them.
#[derive(Debug)]
struct Pager {
    /// Hits to skip before the page.
    offset: usize,
    /// The page.
    hits: Hits,
}

impl Sink for Pager {
    /// Counts a hit and keeps it when it falls on the page.
    fn push(&mut self, hit: Found) {
        if self.hits.total >= self.offset && self.hits.hits.len() < HITS_MAX {
            self.hits.hits.push(Hit {
                va: hit.va,
                file_off: hit.off.unwrap_or(0),
            });
        }
        self.hits.total = self.hits.total.saturating_add(1);
    }

    /// Never: a page counts every hit.
    fn full(&self) -> bool {
        false
    }

    /// Every hit: a page counts them all.
    fn room(&self) -> usize {
        usize::MAX
    }
}

/// A search running: the chunks done and the progress they count into.
pub(super) struct Run<'s> {
    /// Chunks scanned.
    done: usize,
    /// Chunks the whole search scans.
    total: usize,
    /// The progress report of the chunks.
    sweep: crate::progress::Sweep,
    /// Asked before each chunk, with the chunks done: `true` stops.
    stop: &'s mut dyn FnMut(usize) -> bool,
}

impl<'s> Run<'s> {
    /// Starts a search of `total` chunks.
    ///
    /// # Arguments
    ///
    /// * `total` - The chunks it scans.
    /// * `stop` - Asked before each chunk.
    fn new(total: usize, stop: &'s mut dyn FnMut(usize) -> bool) -> Self {
        Run {
            done: 0,
            total,
            sweep: crate::progress::Sweep::start(total),
            stop,
        }
    }

    /// Runs one chunk's work unless the search is to stop, and counts it.
    ///
    /// # Arguments
    ///
    /// * `work` - The chunk's scan.
    ///
    /// # Errors
    ///
    /// When the search is to stop, saying how far it got.
    pub(super) fn chunk(&mut self, work: impl FnOnce()) -> Result<(), String> {
        if (self.stop)(self.done) {
            return Err(format!(
                "the search stopped at the request's deadline after {} of its {} chunks; nothing was answered",
                self.done, self.total
            ));
        }
        work();
        self.done = self.done.saturating_add(1);
        self.sweep.add(1);
        Ok(())
    }
}

/// Returns the refusal of a clause with more hits than a search holds.
pub(super) fn over() -> String {
    format!(
        "the clause finds more than the {HELD_MAX} hits a search holds; narrow it: give a value a width (value:1,width=4), a range or align=, a pattern more bytes, or add a scope (value:1,width=4 and in=.data)"
    )
}

/// What a byte walk looks for.
#[derive(Debug, Clone, Copy)]
pub enum Needle<'a> {
    /// A masked byte pattern.
    Bytes(&'a Pattern),
    /// A text, ASCII case folded, as UTF-8 and as UTF-16LE.
    Text(&'a Text),
}

impl Needle<'_> {
    /// Returns the bytes past a match's first it may cover: a pattern's
    /// length less one, a text's longer spelling's less one.
    fn reach(self) -> usize {
        match self {
            Needle::Bytes(pt) => pt.reach(),
            Needle::Text(t) => {
                let wide = t.as_str().encode_utf16().count().saturating_mul(2);
                t.as_str().len().max(wide).saturating_sub(1)
            }
        }
    }
}

/// Walks the file for a needle, chunk by chunk, into a sink.
///
/// # Arguments
///
/// * `p` - The program.
/// * `needle` - What to find.
/// * `pieces` - The runs walked ([`file_pieces`]), cut to `clip`.
/// * `clip` - The scope the walk keeps to, if any.
/// * `run` - The search running.
/// * `sink` - Where the hits go.
///
/// # Errors
///
/// When the search stops, or the sink fills.
fn walk_needle(
    p: &Program,
    needle: Needle<'_>,
    (pieces, clip): (&[Piece<'_>], Option<&Ranges>),
    run: &mut Run<'_>,
    sink: &mut impl Sink,
) -> Result<(), String> {
    let (finder, narrow, wide) = match needle {
        Needle::Bytes(pt) => (
            Some(Finder::new(pt, p.bytes.as_slice())),
            &[][..],
            Vec::new(),
        ),
        Needle::Text(t) => (
            None,
            t.as_str().as_bytes(),
            t.as_str()
                .encode_utf16()
                .flat_map(u16::to_le_bytes)
                .collect(),
        ),
    };
    let reach = needle.reach();
    for piece in pieces.iter().flat_map(|piece| piece.clipped(clip)) {
        for span in piece.chunks(reach) {
            let room = sink.room();
            let from = span.off.saturating_sub(piece.off);
            let also: Vec<u64> = piece.also.iter().map(|b| b.saturating_add(from)).collect();
            let mut at = |i: u64, matched| {
                let off = Some(span.off.saturating_add(i));
                let va = span.va.map(|va| va.saturating_add(i));
                sink.push(Found { va, off, matched });
                for b in &also {
                    let va = Some(b.saturating_add(i));
                    sink.push(Found { va, off, matched });
                }
            };
            run.chunk(|| match &finder {
                Some(f) => f.each(&span, |i| at(i, Matched::Bytes)),
                None => {
                    for (i, spelling) in text_hits(&span, narrow, &wide, room) {
                        at(i, Matched::Text(spelling));
                    }
                }
            })?;
            if sink.full() {
                return Err(over());
            }
        }
    }
    Ok(())
}

/// Returns how many chunks a walk of pieces cut to a scope takes.
///
/// # Arguments
///
/// * `pieces` - The runs.
/// * `clip` - The scope, if any.
/// * `reach` - Bytes past a match's first it may cover.
fn chunk_count(pieces: &[Piece<'_>], clip: Option<&Ranges>, reach: usize) -> usize {
    pieces
        .iter()
        .flat_map(|piece| piece.clipped(clip))
        .map(|piece| piece.len.div_ceil(chunk_len(reach)))
        .fold(0, usize::saturating_add)
}

/// Returns a page of a needle's hits in the order the file is walked, and
/// their count: what the `search` tool answers.
///
/// # Arguments
///
/// * `p` - The program.
/// * `needle` - What to find.
/// * `offset` - Hits to skip before the page.
/// * `stop` - Asked with the chunks done before each chunk; `true` stops.
///
/// # Returns
///
/// The page, at most [`HITS_MAX`] hits, and the total.
///
/// # Errors
///
/// When some file byte is mapped at more than 8 addresses (the search
/// refuses rather than walk it once per address), or when `stop` stops
/// the walk.
pub fn page(
    p: &Program,
    needle: Needle<'_>,
    offset: usize,
    stop: &mut dyn FnMut(usize) -> bool,
) -> Result<Hits, String> {
    let pieces = file_pieces(p)?;
    let mut run = Run::new(chunk_count(&pieces, None, needle.reach()), stop);
    let mut pager = Pager {
        offset,
        hits: Hits::default(),
    };
    walk_needle(p, needle, (&pieces, None), &mut run, &mut pager)?;
    Ok(pager.hits)
}

/// Hands `hit` each aligned word of a chunk of data whose number lies in
/// the value's range.
///
/// # Arguments
///
/// * `span` - The chunk: bytes of a section that is not executable.
/// * `v` - The value sought.
/// * `hit` - Called with each word's offset in the chunk.
fn data_words(span: &Span<'_>, (v, order): (&Value, Order), mut hit: impl FnMut(u64)) {
    let Some(va) = span.va else {
        return;
    };
    let width = usize::from(v.width.bytes());
    let align = v.align.max(1);
    let skip = (align - va % align) % align;
    for i in (saturating_usize(skip)..saturating_usize(span.own)).step_by(saturating_usize(align)) {
        let Some(bytes) = span.data.get(i..i.saturating_add(width)) else {
            break;
        };
        if bytes.len() == width && (v.lo..=v.hi).contains(&word(bytes, order, v.sign)) {
            hit(from_usize(i));
        }
    }
}

/// Walks the data words of a value, chunk by chunk, into a sink.
///
/// # Arguments
///
/// * `v` - The value.
/// * `pieces` - The runs walked ([`data_pieces`]), cut to `clip`.
/// * `clip` - The scope the walk keeps to, if any.
/// * `run` - The search running.
/// * `sink` - Where the hits go.
///
/// # Errors
///
/// When the search stops, or the sink fills.
fn walk_data(
    (v, order): (&Value, Order),
    (pieces, clip): (&[Piece<'_>], Option<&Ranges>),
    run: &mut Run<'_>,
    sink: &mut Held,
) -> Result<(), String> {
    let matched = Matched::Data {
        width: v.width.bytes(),
        order,
    };
    let reach = usize::from(v.width.bytes()).saturating_sub(1);
    for piece in pieces.iter().flat_map(|piece| piece.clipped(clip)) {
        for span in piece.chunks(reach) {
            run.chunk(|| {
                data_words(&span, (v, order), |i| {
                    sink.push(Found {
                        va: span.va.map(|va| va.saturating_add(i)),
                        off: Some(span.off.saturating_add(i)),
                        matched,
                    });
                });
            })?;
            if sink.full() {
                return Err(over());
            }
        }
    }
    Ok(())
}

/// Returns the program's own byte order, read from its file header: big
/// for an ELF that says so and a big-endian Mach-O, little otherwise.
///
/// # Arguments
///
/// * `p` - The program.
fn file_order(p: &Program) -> Order {
    match p.bytes.get(..6) {
        Some([0x7f, b'E', b'L', b'F', _, 2] | [0xfe, 0xed, 0xfa, 0xce | 0xcf, ..]) => Order::Be,
        _ => Order::Le,
    }
}

/// Reads a data word as a number.
///
/// # Arguments
///
/// * `bytes` - The word: 1 to 8 bytes.
/// * `order` - Its byte order.
/// * `sign` - How it is read.
fn word(bytes: &[u8], order: Order, sign: Sign) -> i128 {
    let mut b = [0u8; 8];
    let n = bytes.len().min(8);
    let raw = match order {
        Order::Le => {
            b[..n].copy_from_slice(&bytes[..n]);
            u64::from_le_bytes(b)
        }
        Order::Be => {
            b[8 - n..].copy_from_slice(&bytes[..n]);
            u64::from_be_bytes(b)
        }
    };
    number(raw, u32::try_from(n * 8).unwrap_or(64), sign)
}

/// Reads `bits` low bits of `raw` as a number.
///
/// # Arguments
///
/// * `raw` - The bits, zero above `bits`.
/// * `bits` - Their width: 8 to 64.
/// * `sign` - Zero- or sign-extended.
pub(super) fn number(raw: u64, bits: u32, sign: Sign) -> i128 {
    match sign {
        Sign::Unsigned => i128::from(raw),
        Sign::Signed => {
            let sh = 64u32.saturating_sub(bits.clamp(1, 64));
            i128::from((raw << sh).cast_signed() >> sh)
        }
    }
}

/// Resolves a place to the addresses it covers.
///
/// `<lo>..<hi>` covers both ends; a section's name covers every section
/// of that name by the extent its rows name it for
/// ([`crate::program::Section::span`]); anything else, the blocks of the
/// function holding the address the place resolves to.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `o` - The names in force.
/// * `place` - The place as written.
///
/// # Returns
///
/// The addresses.
///
/// # Errors
///
/// When an address does not resolve, a range ends below its start, or
/// no section is so named and no function holds the place.
fn scope(p: &Program, a: &Analysis, o: &Overlay, place: &str) -> Result<Ranges, String> {
    if let Some((lo, hi)) = place.split_once("..") {
        let (lo, hi) = (
            resolve_suggesting(p, a, o, lo)?,
            resolve_suggesting(p, a, o, hi)?,
        );
        if lo > hi {
            return Err(format!("in={place}: the range ends below its start"));
        }
        return Ok(Ranges::of(vec![(lo, hi.saturating_add(1))]));
    }
    let named: Vec<(u64, u64)> = p
        .sections
        .iter()
        .filter(|s| s.name == place)
        .map(|s| (s.span().start, s.span().end))
        .collect();
    if !named.is_empty() {
        return Ok(Ranges::of(named));
    }
    let va = resolve_suggesting(p, a, o, place)?;
    let f = a.function_at(va).ok_or_else(|| {
        format!("in={place}: no section is named so and no function holds {va:#x}")
    })?;
    Ok(Ranges::of(
        f.blocks.iter().map(|b| (b.start, b.end)).collect(),
    ))
}

/// Keeps the hits of `left` whose address `right` hits too, or, with
/// `keep` false, those it does not; both sorted.
///
/// # Arguments
///
/// * `left` - The hits so far.
/// * `right` - The clause's hits.
/// * `keep` - `true` for `and`, `false` for `minus`.
fn meet(left: Vec<Found>, right: &[Found], keep: bool) -> Vec<Found> {
    let mut j = 0;
    left.into_iter()
        .filter(|h| {
            let at = h.place();
            while right.get(j).is_some_and(|r| r.place() < at) {
                j += 1;
            }
            right.get(j).is_some_and(|r| r.place() == at) == keep
        })
        .collect()
}

/// Merges two sorted hit lists by address, a hit of `right` at an address
/// `left` hits left out.
///
/// # Arguments
///
/// * `left` - The hits so far.
/// * `right` - The clause's hits.
fn join(left: Vec<Found>, right: Vec<Found>) -> Vec<Found> {
    let mut out = Vec::with_capacity(left.len().saturating_add(right.len()));
    let mut right = right.into_iter().peekable();
    for h in left {
        while let Some(r) = right.next_if(|r| r.place() < h.place()) {
            out.push(r);
        }
        while right.next_if(|r| r.place() == h.place()).is_some() {}
        out.push(h);
    }
    out.extend(right);
    out
}

/// Runs a spec, reading the request's cancel flag before each chunk.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis; an empty one finds no code.
/// * `o` - The names in force, for `in=`.
/// * `spec` - The spec.
///
/// # Returns
///
/// Every hit, in address order then file order.
///
/// # Errors
///
/// When a place does not resolve, a clause holds more than [`HELD_MAX`]
/// hits, or the request's deadline passes.
pub fn search(p: &Program, a: &Analysis, o: &Overlay, spec: &Spec) -> Result<Vec<Found>, String> {
    search_with(p, a, o, spec, &mut |_| crate::cancel::Cancel::raised())
}

/// Returns the scope each find keeps to, in the order [`Spec::finds`]
/// gives them: the addresses every later `and in=` names.
///
/// # Arguments
///
/// * `spec` - The spec.
/// * `scopes` - Each step's resolved place, `None` for a find.
fn clips(spec: &Spec, scopes: &[Option<Ranges>]) -> Vec<Option<Ranges>> {
    let mut acc: Option<Ranges> = None;
    let mut out = Vec::new();
    for (step, scope) in spec.steps.iter().zip(scopes).rev() {
        match (step, scope) {
            (Step::And(Clause::In(_)), Some(s)) => {
                acc = Some(acc.map_or_else(|| s.clone(), |a| a.and(s)));
            }
            (Step::And(Clause::Find(_)) | Step::Or(_) | Step::Minus(Clause::Find(_)), _) => {
                out.push(acc.clone());
            }
            (Step::And(Clause::In(_)) | Step::Minus(Clause::In(_)), _) => {}
        }
    }
    out.push(acc);
    out.reverse();
    out
}

/// Runs a spec, asking `stop` before each chunk.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `o` - The names in force.
/// * `spec` - The spec.
/// * `stop` - Asked with the chunks done; `true` stops the search.
///
/// # Returns
///
/// Every hit, in address order then file order.
///
/// # Errors
///
/// As [`search`].
pub(crate) fn search_with(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    spec: &Spec,
    stop: &mut dyn FnMut(usize) -> bool,
) -> Result<Vec<Found>, String> {
    let scopes = spec
        .steps
        .iter()
        .map(|step| match step {
            Step::And(Clause::In(place)) | Step::Minus(Clause::In(place)) => {
                scope(p, a, o, place).map(Some)
            }
            Step::And(Clause::Find(_)) | Step::Or(_) | Step::Minus(Clause::Find(_)) => Ok(None),
        })
        .collect::<Result<Vec<_>, String>>()?;
    let clips = clips(spec, &scopes);
    let finds: Vec<(&Find, Option<&Ranges>)> =
        spec.finds().zip(clips.iter().map(Option::as_ref)).collect();
    let finds_bytes = finds
        .iter()
        .any(|(f, _)| matches!(f, Find::Bytes(_) | Find::Text(_)));
    let file = if finds_bytes {
        file_pieces(p)?
    } else {
        Vec::new()
    };
    let data = if finds.iter().any(|(f, _)| matches!(f, Find::Value(_))) {
        data_pieces(p)?
    } else {
        Vec::new()
    };
    let code = super::code::plan(p, a, &finds);
    let total = finds
        .iter()
        .map(|&(f, clip)| match f {
            Find::Bytes(pt) => chunk_count(&file, clip, Needle::Bytes(pt).reach()),
            Find::Text(t) => chunk_count(&file, clip, Needle::Text(t).reach()),
            Find::Value(v) => chunk_count(&data, clip, usize::from(v.width.bytes()) - 1),
        })
        .fold(code.chunks(), usize::saturating_add);
    let mut run = Run::new(total, stop);
    let mut constants = super::code::walk(p, &code, &finds, &mut run)?.into_iter();
    let mut found = finds
        .iter()
        .map(|&(f, clip)| -> Result<Vec<Found>, String> {
            let mut held = Held::default();
            match f {
                Find::Bytes(pt) => {
                    walk_needle(p, Needle::Bytes(pt), (&file, clip), &mut run, &mut held)?;
                }
                Find::Text(t) => {
                    walk_needle(p, Needle::Text(t), (&file, clip), &mut run, &mut held)?;
                }
                Find::Value(v) => {
                    held = constants.next().unwrap_or_default();
                    walk_data(
                        (v, v.order(file_order(p))),
                        (&data, clip),
                        &mut run,
                        &mut held,
                    )?;
                }
            }
            Ok(held.sorted())
        });
    let mut hits = found.next().transpose()?.unwrap_or_default();
    for (step, scope) in spec.steps.iter().zip(&scopes) {
        match (step, scope) {
            (Step::And(Clause::Find(_)), _) => {
                hits = meet(hits, &found.next().transpose()?.unwrap_or_default(), true);
            }
            (Step::Minus(Clause::Find(_)), _) => {
                hits = meet(hits, &found.next().transpose()?.unwrap_or_default(), false);
            }
            (Step::Or(_), _) => hits = join(hits, found.next().transpose()?.unwrap_or_default()),
            (Step::Minus(Clause::In(_)), Some(s)) => {
                hits.retain(|h| !h.va.is_some_and(|va| s.holds(va)));
            }
            (Step::And(Clause::In(_)) | Step::Minus(Clause::In(_)), _) => {}
        }
    }
    Ok(hits)
}

/// Spells how a hit matched, for a row.
///
/// # Arguments
///
/// * `m` - The match.
fn spelled(m: Matched) -> String {
    match m {
        Matched::Bytes => "bytes".to_owned(),
        Matched::Text(Spelling::Utf8) => "text".to_owned(),
        Matched::Text(Spelling::Utf16) => "text utf16".to_owned(),
        Matched::Data { width, order } => format!(
            "data width={width} order={}",
            match order {
                Order::Le => "le",
                Order::Be => "be",
            }
        ),
        Matched::Immediate { operand } => format!("immediate operand={operand}"),
        Matched::Shifted { operand } => format!("immediate operand={operand} shifted"),
        Matched::Displacement { operand } => format!("displacement operand={operand}"),
        Matched::Address { operand } => format!("address operand={operand}"),
    }
}

/// The note under a value search's header: what it searches and what it
/// does not.
const VALUE_NOTE: &str = "# a value is sought as aligned words of the image (relocated) in sections that are not executable, in the program's byte order unless order= says, and as the value each immediate of an instruction in a discovered function contributes, any shift the instruction applies folded in (movt, movk, lui, lsl #n: such a hit says shifted); with disp also memory displacements and the address a PC-relative operand reaches; data inside executable sections (literal pools, jump tables), bytes outside every section, code outside the functions, arm64 PC-relative literals, ARM32 ldr =imm literal-pool values and a value code builds across instructions are not searched";

/// Answers `borer://search/<spec>`: the hits of a spec as rows of address,
/// file offset, function, section and how each matched, a page at a time.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis; an empty one finds no code.
/// * `o` - The names in force.
/// * `text` - The spec ([`super::spec`]).
/// * `window` - The page shown.
///
/// # Returns
///
/// A header counting every hit with the page's place, a note for a value
/// search, the column header and the rows.
///
/// # Errors
///
/// When the spec does not read or the search refuses ([`search`]).
pub fn search_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    text: &str,
    window: Window<'_>,
) -> Result<String, String> {
    use std::fmt::Write as _;
    let spec = super::spec::parse(text)?;
    let hits = search(p, a, o, &spec)?;
    let page: Vec<&Found> = hits.iter().skip(window.skip).take(window.limit).collect();
    let mut out = format!(
        "# search {}: {} hits, showing {} of {} from {}\n",
        crate::text::one_line(text),
        hits.len(),
        page.len(),
        hits.len(),
        window.skip
    );
    if spec.finds().any(|f| matches!(f, Find::Value(_))) {
        out.push_str(VALUE_NOTE);
        out.push('\n');
    }
    out.push_str("va\toff\tfunction\tsection\tmatched\n");
    let shown = |n: Option<u64>| n.map_or_else(|| "-".to_owned(), |n| format!("{n:#x}"));
    for h in &page {
        let function =
            h.va.and_then(|va| a.function_at(va))
                .map_or_else(|| "-".to_owned(), |f| name_of(a, o, f.entry));
        let section =
            h.va.and_then(|va| p.section_at(va))
                .map_or("-", |s| s.name.as_str());
        let _ = writeln!(
            out,
            "{}\t{}\t{function}\t{section}\t{}",
            shown(h.va),
            shown(h.off),
            spelled(h.matched)
        );
    }
    out.push_str(&window.next_page(hits.len(), page.len()));
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::search_with;
    use crate::analysis::{Analysis, Overlay};
    use crate::num::from_usize;
    use crate::program::{Arch, Program, Section};

    /// Returns a program of one 32 MiB data section of zeros.
    fn large() -> Program {
        let size = 32usize << 20;
        Program::raw(
            vec![0u8; size],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![Section::mapped(
                ".data",
                0x1000,
                0,
                from_usize(size),
                true,
                false,
            )],
        )
    }

    /// A search over one 32 MiB section stopped after its first chunk
    /// refuses, having asked twice, and the progress counts that one chunk
    /// of 32: the flag is read per chunk, not per section.
    ///
    /// # Panics
    ///
    /// When the search runs on, or the count differs.
    #[test]
    fn a_search_stops_between_chunks() {
        let p = large();
        let spec = super::super::spec::parse("bytes:01").expect("reads");
        let progress = crate::progress::Progress::new();
        let mut asked = 0;
        let got = progress.within(|| {
            search_with(
                &p,
                &Analysis::default(),
                &Overlay::default(),
                &spec,
                &mut |done| {
                    asked += 1;
                    done >= 1
                },
            )
        });
        let why = got.expect_err("stopped");
        assert!(why.contains("after 1 of its 32 chunks"), "{why}");
        assert_eq!(asked, 2);
        let seen = progress.snapshot();
        assert_eq!((seen.done, seen.total), (1, 32));
    }

    /// Two value clauses read one walk of the code: the search takes one
    /// chunk of code and one chunk of data per clause.
    ///
    /// # Panics
    ///
    /// When the code is walked once per clause.
    #[test]
    fn value_clauses_share_one_walk_of_the_code() {
        let mut bytes = vec![0u8; 0x200];
        bytes[..6].copy_from_slice(&[0xb8, 1, 0, 0, 0, 0xc3]);
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![
                Section::mapped(".text", 0x1000, 0, 0x100, false, true),
                Section::mapped(".data", 0x2000, 0x100, 0x100, true, false),
            ],
        );
        let a = Analysis::compute(&p);
        let spec = super::super::spec::parse("value:1 or value:2").expect("reads");
        let progress = crate::progress::Progress::new();
        let got = progress.within(|| super::search(&p, &a, &Overlay::default(), &spec));
        assert!(got.is_ok_and(|h| h.len() == 1));
        assert_eq!(progress.snapshot().total, 3);
    }

    /// A raised cancel flag stops a search before its first chunk.
    ///
    /// # Panics
    ///
    /// When the search runs.
    #[test]
    fn a_raised_flag_stops_a_search() {
        let p = large();
        let spec = super::super::spec::parse("value:7").expect("reads");
        let flag = crate::cancel::Cancel::new();
        flag.raise();
        let got =
            flag.within(|| super::search(&p, &Analysis::default(), &Overlay::default(), &spec));
        assert!(got.is_err_and(|why| why.contains("after 0 of its 32 chunks")));
    }
}
