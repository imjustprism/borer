//! Runs a search spec ([`super::spec`]) over the program and writes its
//! hits as a table, each saying how it matched.
//!
//! Every clause scans in chunks of at most [`CHUNK`] bytes: the request's
//! cancel flag is read before each and the progress in force counts each,
//! so a search over a large file reports how far it is and stops at its
//! deadline with a refusal, never a partial answer. Hits come in address
//! order, then those in bytes no section maps in file order; a clause
//! holds at most [`HELD_MAX`] of them, so set operations work on whole
//! sets.

use std::collections::BTreeSet;

use super::spec::{Clause, Find, Op, Order, Sign, Spec, Value};
use super::{Finder, Span, Spelling, section_spans, spans, text_hits};
use crate::analysis::{Analysis, Overlay, name_of, resolve_suggesting};
use crate::num::{from_usize, saturating_usize};
use crate::program::Program;
use crate::table::Window;

/// Most bytes one chunk of a scan covers.
pub const CHUNK: usize = 1 << 20;

/// Most hits one clause holds; a clause finding more is refused.
pub const HELD_MAX: usize = 1 << 18;

/// One hit of a search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Found {
    /// Its address; `None` in bytes no section maps.
    pub va: Option<u64>,
    /// Its file offset.
    pub off: u64,
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
}

impl Found {
    /// Returns where the hit is for ordering and set operations: its
    /// address, else its file offset after every address.
    fn place(&self) -> (bool, u64) {
        self.va.map_or((true, self.off), |va| (false, va))
    }
}

/// The hits one clause found, at most [`HELD_MAX`].
#[derive(Debug, Default)]
struct Held {
    /// The hits, in the order found.
    hits: Vec<Found>,
    /// Whether a hit past the cap was dropped.
    over: bool,
}

impl Held {
    /// Keeps a hit, or notes one past the cap.
    ///
    /// # Arguments
    ///
    /// * `hit` - The hit.
    fn push(&mut self, hit: Found) {
        if self.hits.len() < HELD_MAX {
            self.hits.push(hit);
        } else {
            self.over = true;
        }
    }
}

/// A search running: the chunks done and the progress they count into.
struct Run<'s> {
    /// Chunks scanned.
    done: usize,
    /// Chunks the whole search scans.
    total: usize,
    /// The progress report of the chunks.
    sweep: crate::progress::Sweep,
    /// Asked before each chunk, with the chunks done: `true` stops.
    stop: &'s mut dyn FnMut(usize) -> bool,
}

impl Run<'_> {
    /// Runs one chunk's work unless the search is to stop, and counts it.
    ///
    /// # Arguments
    ///
    /// * `work` - The chunk's scan.
    ///
    /// # Errors
    ///
    /// When the search is to stop, saying how far it got.
    fn chunk(&mut self, work: impl FnOnce()) -> Result<(), String> {
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

/// The chunks one find scans.
struct Plan<'p> {
    /// The byte runs, each at most [`CHUNK`] bytes long.
    runs: Vec<Span<'p>>,
}

/// Returns the chunks a find scans.
///
/// # Arguments
///
/// * `p` - The program.
/// * `find` - The find.
fn plan<'p>(p: &'p Program, find: &Find) -> Plan<'p> {
    let (whole, reach) = match find {
        Find::Bytes(lanes) => (spans(p, lanes.len().saturating_sub(1)), 0),
        Find::Text(text) => {
            let wide = text.encode_utf16().count().saturating_mul(2);
            (spans(p, text.len().max(wide).saturating_sub(1)), 0)
        }
        Find::Value(v) => (
            section_spans(p, 0, |s| !s.executable),
            usize::from(v.width).saturating_sub(1),
        ),
    };
    let runs = whole
        .into_iter()
        .flat_map(|span| chunked(span, reach))
        .collect();
    Plan { runs }
}

/// Splits a run into chunks of at most [`CHUNK`] bytes, each with the
/// bytes after it a match may cover, cut at the run's own bytes.
///
/// # Arguments
///
/// * `span` - The run.
/// * `reach` - Bytes past a chunk a match may cover, besides those the run
///   already carries.
fn chunked(span: Span<'_>, reach: usize) -> impl Iterator<Item = Span<'_>> {
    let own = saturating_usize(span.own);
    let tail = span.data.len().saturating_sub(own);
    (0..own.div_ceil(CHUNK)).filter_map(move |k| {
        let from = k.checked_mul(CHUNK)?;
        let len = CHUNK.min(own.checked_sub(from)?);
        let to = from
            .saturating_add(len)
            .saturating_add(reach.max(tail))
            .min(span.data.len());
        Some(Span {
            data: span.data.get(from..to)?,
            own: from_usize(len),
            off: span.off.saturating_add(from_usize(from)),
            va: span.va.map(|va| va.saturating_add(from_usize(from))),
        })
    })
}

/// Scans the chunks of one find.
///
/// # Arguments
///
/// * `p` - The program.
/// * `find` - The find.
/// * `plan` - Its chunks.
/// * `run` - The search running.
///
/// # Returns
///
/// The hits, in address order then file order.
///
/// # Errors
///
/// When the search stops, or the find holds more than [`HELD_MAX`] hits.
fn scan(
    p: &Program,
    find: &Find,
    plan: &Plan<'_>,
    run: &mut Run<'_>,
) -> Result<Vec<Found>, String> {
    let mut held = Held::default();
    let finder = match find {
        Find::Bytes(lanes) => Some(Finder::new(lanes, p.bytes.as_slice())),
        Find::Text(_) | Find::Value(_) => None,
    };
    let wide: Vec<u8> = match find {
        Find::Text(text) => text.encode_utf16().flat_map(u16::to_le_bytes).collect(),
        Find::Bytes(_) | Find::Value(_) => Vec::new(),
    };
    for span in &plan.runs {
        let at = |i: u64, matched| Found {
            va: span.va.map(|va| va.saturating_add(i)),
            off: span.off.saturating_add(i),
            matched,
        };
        run.chunk(|| match find {
            Find::Bytes(_) => {
                if let Some(f) = &finder {
                    f.each(span, |i| held.push(at(i, Matched::Bytes)));
                }
            }
            Find::Text(text) => {
                for (i, spelling) in text_hits(span, text.as_bytes(), &wide) {
                    held.push(at(i, Matched::Text(spelling)));
                }
            }
            Find::Value(v) => data_words(span, v, |i, m| held.push(at(i, m))),
        })?;
        if held.over {
            return Err(format!(
                "the clause finds more than the {HELD_MAX} hits a search holds; narrow it with a longer pattern, a range, align= or in="
            ));
        }
    }
    held.hits.sort_by_key(|h| (h.place(), h.off, h.matched));
    held.hits.dedup();
    Ok(held.hits)
}

/// Hands `hit` each aligned word of a chunk of data whose number lies in
/// the value's range.
///
/// # Arguments
///
/// * `span` - The chunk: bytes of a section that is not executable.
/// * `v` - The value sought.
/// * `hit` - Called with each word's offset in the chunk and its match.
fn data_words(span: &Span<'_>, v: &Value, mut hit: impl FnMut(u64, Matched)) {
    let Some(va) = span.va else {
        return;
    };
    let width = usize::from(v.width);
    let skip = v.align.wrapping_sub(va % v.align.max(1)) % v.align.max(1);
    let step = saturating_usize(v.align).max(1);
    let matched = Matched::Data {
        width: v.width,
        order: v.order,
    };
    for i in (saturating_usize(skip)..saturating_usize(span.own)).step_by(step) {
        let Some(bytes) = span.data.get(i..i.saturating_add(width)) else {
            break;
        };
        if bytes.len() == width && (v.lo..=v.hi).contains(&word(bytes, v.order, v.sign)) {
            hit(from_usize(i), matched);
        }
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
pub(crate) fn number(raw: u64, bits: u32, sign: Sign) -> i128 {
    match sign {
        Sign::Unsigned => i128::from(raw),
        Sign::Signed => {
            let sh = 64u32.saturating_sub(bits.clamp(1, 64));
            i128::from((raw << sh).cast_signed() >> sh)
        }
    }
}

/// A place a hit is in, an `in=` resolved.
#[derive(Debug, Clone, Copy)]
enum Scope {
    /// Addresses from the first to the second, both included.
    Within(u64, u64),
    /// The function with this entry, by [`Analysis::function_at`].
    Function(u64),
}

impl Scope {
    /// Resolves a place: a section's name, `<lo>..<hi>`, or a function.
    ///
    /// # Arguments
    ///
    /// * `p` - The program.
    /// * `a` - Its analysis.
    /// * `o` - The names in force.
    /// * `place` - The place as written.
    ///
    /// # Errors
    ///
    /// When an address does not resolve, a range ends below its start, or
    /// no function holds the place.
    fn read(p: &Program, a: &Analysis, o: &Overlay, place: &str) -> Result<Self, String> {
        if let Some((lo, hi)) = place.split_once("..") {
            let (lo, hi) = (
                resolve_suggesting(p, a, o, lo)?,
                resolve_suggesting(p, a, o, hi)?,
            );
            if lo > hi {
                return Err(format!("in={place}: the range ends below its start"));
            }
            return Ok(Scope::Within(lo, hi));
        }
        if let Some(s) = p.sections.iter().find(|s| s.name == place) {
            return Ok(match s.vsize.checked_sub(1) {
                Some(last) => Scope::Within(s.va.0, s.va.0.saturating_add(last)),
                None => Scope::Within(1, 0),
            });
        }
        let va = resolve_suggesting(p, a, o, place)?;
        a.function_at(va)
            .map(|f| Scope::Function(f.entry))
            .ok_or_else(|| {
                format!("in={place}: no section is named so and no function holds {va:#x}")
            })
    }

    /// Whether a hit is in the place; one in bytes no section maps never is.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis.
    /// * `hit` - The hit.
    fn holds(self, a: &Analysis, hit: &Found) -> bool {
        hit.va.is_some_and(|va| match self {
            Scope::Within(lo, hi) => (lo..=hi).contains(&va),
            Scope::Function(entry) => a.function_at(va).is_some_and(|f| f.entry == entry),
        })
    }
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
    let plans: Vec<Plan<'_>> = spec.finds().map(|f| plan(p, f)).collect();
    let total = plans.iter().map(|pl| pl.runs.len()).sum();
    let mut run = Run {
        done: 0,
        total,
        sweep: crate::progress::Sweep::start(total),
        stop,
    };
    let mut plans = plans.iter();
    let mut next = |find: &Find, run: &mut Run<'_>| match plans.next() {
        Some(plan) => scan(p, find, plan, run),
        None => Err("a clause lost its plan".to_owned()),
    };
    let mut hits = next(&spec.first, &mut run)?;
    for (op, clause) in &spec.rest {
        let inside: Vec<bool> = match clause {
            Clause::In(place) => {
                let scope = Scope::read(p, a, o, place)?;
                hits.iter().map(|h| scope.holds(a, h)).collect()
            }
            Clause::Find(find) => {
                let right = next(find, &mut run)?;
                if *op == Op::Or {
                    let left: BTreeSet<(bool, u64)> = hits.iter().map(Found::place).collect();
                    hits.extend(right.into_iter().filter(|h| !left.contains(&h.place())));
                    hits.sort_by_key(|h| (h.place(), h.off, h.matched));
                    continue;
                }
                let at: BTreeSet<(bool, u64)> = right.iter().map(Found::place).collect();
                hits.iter().map(|h| at.contains(&h.place())).collect()
            }
        };
        let want = match op {
            Op::And => true,
            Op::Minus => false,
            Op::Or => return Err("in= follows and or minus, never or".to_owned()),
        };
        let mut inside = inside.into_iter();
        hits.retain(|_| inside.next() == Some(want));
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
    }
}

/// The note under a value search's header: what it searches and what it
/// cannot.
const VALUE_NOTE: &str = "# a value is sought as aligned words in the sections that are not executable; executable bytes are never data hits";

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
    for h in &page {
        let va = h.va.map_or_else(|| "-".to_owned(), |va| format!("{va:#x}"));
        let function =
            h.va.and_then(|va| a.function_at(va))
                .map_or_else(|| "-".to_owned(), |f| name_of(a, o, f.entry));
        let section =
            h.va.and_then(|va| p.section_at(va))
                .map_or("-", |s| s.name.as_str());
        let _ = writeln!(
            out,
            "{va}\t{:#x}\t{function}\t{section}\t{}",
            h.off,
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
