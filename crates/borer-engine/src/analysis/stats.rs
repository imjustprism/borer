//! Chart series as answers: values the engine owns, each point or bar
//! carrying its exact range, so a chart scales and paints and never bins,
//! sums or measures for itself.
//!
//! Every value is an integer and every series is memoized in
//! [`Analysis::derived`], keyed by the inputs it was made with: the same
//! program and the same inputs give the same bytes on every host and at any
//! thread count. Entropy is computed in fixed point ([`log2_fixed`]), not
//! with `f64::log2`, whose rounding no platform's libm promises to share.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::hash::Hash;
use std::sync::Arc;

use crate::analysis::render::{Selection, select_functions};
use crate::analysis::{Analysis, Overlay};
use crate::entropy::{ByteCounts, WINDOW_DEFAULT, WINDOW_MIN};
use crate::num::{from_usize, saturating_usize};
use crate::program::{Feature, Program};
use crate::table::{self, Line, Window};
use crate::text;

/// Most points a profile holds; a file that needs more grows the window
/// ([`window_for`]).
pub const PROFILE_POINTS_MAX: usize = 4096;
/// Largest window a profile uses, in bytes, so a point's length fits a
/// `u32`; a file over 8 TiB would need more than [`PROFILE_POINTS_MAX`]
/// points at it.
const WINDOW_MAX: u64 = 1 << 31;
/// Fractional bits of [`log2_fixed`]'s answer.
const FRAC: u32 = 32;
/// Most counts [`Terms`] holds `c * log2(c)` for; a larger count, which
/// only a run over 64 KiB holds, is computed on its own.
const TERMS_MAX: u64 = 1 << 16;
/// The entropy of a window where every byte value is equally likely, in
/// millibits.
const MILLIBITS_MAX: u128 = 8000;

/// One window of a profile: a run of the file's bytes and the series'
/// value over it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Point {
    /// File offset of the window's first byte.
    pub off: u64,
    /// Bytes in the window: the profile's window, or fewer for the last.
    pub len: u32,
    /// Where the first byte loads ([`Program::offset_to_va`]); `None` for
    /// bytes no section maps (headers, gaps, an overlay).
    pub va: Option<u64>,
    /// Index in [`Program::sections`] of the section that maps the first
    /// byte ([`Program::offset_mapping`]); `None` when `va` is.
    pub section: Option<usize>,
    /// The series' value: millibits of entropy (0 to 8000) in
    /// [`entropy_profile`], bytes inside strings in [`string_density`].
    pub value: u32,
}

/// A series over the file's bytes in file order: windows that tile the
/// file with no gap or overlap.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Profile {
    /// Window size in bytes the points use, which may exceed the one asked
    /// for ([`window_for`]).
    pub window: u64,
    /// The windows, from offset 0, at most [`PROFILE_POINTS_MAX`].
    pub points: Vec<Point>,
}

/// Returns a series kept in the analysis's item memo, under its byte
/// budget, so asking for many windows or bins cannot grow memory without
/// bound.
///
/// A series reads no names, so every one is kept under the empty overlay,
/// which is always in force.
///
/// # Arguments
///
/// * `a` - The analysis whose memo keeps it.
/// * `kind` - The series' name.
/// * `key` - The inputs it was made with, as used (not as asked).
/// * `make` - Builds it.
/// * `weigh` - The heap bytes it holds.
fn kept<K, T>(
    a: &Analysis,
    kind: &'static str,
    key: K,
    make: impl FnOnce() -> T,
    weigh: impl FnOnce(&T) -> usize,
) -> Arc<T>
where
    K: Hash + Eq + Send + 'static,
    T: Send + Sync + 'static,
{
    a.derived
        .get_or_build_item(kind, Overlay::default().fingerprint(), key, make, weigh)
}

/// Returns the heap bytes a profile holds.
///
/// # Arguments
///
/// * `profile` - The profile.
fn profile_bytes(profile: &Profile) -> usize {
    profile.points.capacity() * size_of::<Point>()
}

/// Returns `log2(x)` in fixed point with [`FRAC`] fractional bits,
/// rounded down, by an integer algorithm alone.
///
/// The integer part is the top set bit; the fraction comes a bit at a time
/// from squaring the mantissa, held in Q62 so a square fits a `u128`. Each
/// squaring's truncation moves the answer by under `2^-60`, so the result
/// is within `2^-32 + 2^-60` of the true value, below it.
///
/// # Arguments
///
/// * `x` - The value; `0`, whose logarithm does not exist, answers `0`.
///
/// # Returns
///
/// `floor(log2(x) * 2^32)`, at most `64 * 2^32`.
fn log2_fixed(x: u64) -> u64 {
    if x == 0 {
        return 0;
    }
    let int = u64::from(x.ilog2());
    let mut m = if int <= 62 {
        u128::from(x) << (62 - int)
    } else {
        u128::from(x >> 1)
    };
    let mut frac = 0u64;
    for bit in (0..FRAC).rev() {
        m = (m * m) >> 62;
        if m >= 1 << 63 {
            frac |= 1 << bit;
            m >>= 1;
        }
    }
    (int << FRAC) | frac
}

/// Returns `c * log2(c)` in the fixed point of [`log2_fixed`].
///
/// # Arguments
///
/// * `c` - How many times a byte value occurs.
fn term(c: u64) -> u128 {
    u128::from(c) * u128::from(log2_fixed(c))
}

/// The terms `c * log2(c)` of the counts a run of bytes can hold, built
/// once per series so a run's entropy is 256 lookups.
#[derive(Debug)]
struct Terms(Vec<u128>);

impl Terms {
    /// Returns the terms of every count up to `max`, at most
    /// [`TERMS_MAX`].
    ///
    /// # Arguments
    ///
    /// * `max` - The longest run measured, the largest count it holds.
    fn upto(max: u64) -> Self {
        Self((0..=max.min(TERMS_MAX)).map(term).collect())
    }

    /// Returns the term of `c`, from the table when it holds it.
    ///
    /// # Arguments
    ///
    /// * `c` - How many times a byte value occurs.
    fn of(&self, c: usize) -> u128 {
        self.0
            .get(c)
            .copied()
            .unwrap_or_else(|| term(from_usize(c)))
    }
}

/// Returns the Shannon entropy of `bytes` in millibits per byte, in
/// integer fixed point.
///
/// `1000 * (log2(n) - sum(c * log2(c)) / n)` over the counts `c` of the
/// `n` bytes ([`ByteCounts`], what [`crate::entropy::shannon`] counts),
/// rounded to the nearest. Each logarithm is under `2^-32` from the true
/// value ([`log2_fixed`]) and the sum's division drops under `2^-32` more,
/// so before rounding the answer is within `2^-30` bits of the exact
/// entropy: it is `round(1000 * shannon)` but where `1000 * shannon` lies
/// within a millionth of a millibit of a half, and then one off. Zeros and
/// a single byte value answer exactly 0, and every value equally often
/// exactly 8000.
///
/// # Arguments
///
/// * `bytes` - The bytes measured; none answer 0.
/// * `terms` - The terms of the counts the caller's runs hold.
fn millibits(bytes: &[u8], terms: &Terms) -> u16 {
    let n = from_usize(bytes.len());
    if n == 0 {
        return 0;
    }
    let sum: u128 = ByteCounts::of(bytes).of.iter().map(|&c| terms.of(c)).sum();
    let bits = u128::from(log2_fixed(n)).saturating_sub(sum / u128::from(n));
    let milli = (bits * 1000 + (1 << (FRAC - 1))) >> FRAC;
    u16::try_from(milli.min(MILLIBITS_MAX)).unwrap_or(u16::MAX)
}

/// Returns the window a profile of `len` bytes uses.
///
/// # Arguments
///
/// * `len` - The file's length in bytes.
/// * `asked` - The window asked for, held to [`WINDOW_MIN`] and
///   [`WINDOW_MAX`].
///
/// # Returns
///
/// `asked`, or when the file would need more than [`PROFILE_POINTS_MAX`]
/// windows of it, `ceil(len / PROFILE_POINTS_MAX)` rounded up to a power of
/// two.
fn window_for(len: u64, asked: u64) -> u64 {
    let asked = asked.clamp(from_usize(WINDOW_MIN), WINDOW_MAX);
    let need = len.div_ceil(from_usize(PROFILE_POINTS_MAX));
    if asked >= need {
        asked
    } else {
        need.next_power_of_two().min(WINDOW_MAX)
    }
}

/// The file extents of a program's sections, cut wherever one begins or
/// ends, each run under the first-declared section covering it: what
/// [`Program::offset_mapping`] answers, found by binary search.
#[derive(Debug)]
struct Owners(Vec<(u64, u64, usize)>);

impl Owners {
    /// Returns the runs of `p`'s sections, `(start, end, section)` in file
    /// order, end exclusive, from one sweep over their edges.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    fn of(p: &Program) -> Self {
        let mut edges: Vec<(u64, bool, usize)> = p
            .sections
            .iter()
            .enumerate()
            .filter(|(_, s)| s.file_off.0.saturating_add(s.file_size) > s.file_off.0)
            .flat_map(|(i, s)| {
                let end = s.file_off.0.saturating_add(s.file_size);
                [(s.file_off.0, true, i), (end, false, i)]
            })
            .collect();
        edges.sort_unstable();
        let mut open = BTreeSet::new();
        let mut runs = Vec::new();
        let mut at = 0;
        for (pos, opens, i) in edges {
            if let Some(&first) = open.first()
                && pos > at
            {
                runs.push((at, pos, first));
            }
            at = pos;
            if opens {
                open.insert(i);
            } else {
                open.remove(&i);
            }
        }
        Self(runs)
    }

    /// Returns what [`Program::offset_mapping`] answers for `off`.
    ///
    /// # Arguments
    ///
    /// * `p` - The program the runs were made of.
    /// * `off` - A file offset.
    fn at(&self, p: &Program, off: u64) -> Option<(usize, u64)> {
        let k = self.0.partition_point(|&(_, end, _)| end <= off);
        let &(start, _, i) = self.0.get(k)?;
        if start > off {
            return None;
        }
        let s = p.sections.get(i)?;
        match s.va.0.checked_add(off - s.file_off.0) {
            Some(va) => Some((i, va)),
            None => p.offset_mapping(off),
        }
    }
}

/// Returns the windows of a profile of the program's file, every value 0:
/// one grid, so two series at one window align point for point.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `window` - The window used ([`window_for`]).
///
/// # Returns
///
/// The points, each placed where [`Program::offset_mapping`] places it.
fn grid(p: &Program, window: u64) -> Vec<Point> {
    let len = from_usize(p.bytes.len());
    let owners = Owners::of(p);
    (0..len.div_ceil(window))
        .map(|k| {
            let off = k * window;
            let (section, va) = owners.at(p, off).unzip();
            Point {
                off,
                len: u32::try_from(window.min(len - off)).unwrap_or(u32::MAX),
                va,
                section,
                value: 0,
            }
        })
        .collect()
}

/// Returns the file bytes a point covers.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `point` - One of its profile's points.
fn bytes_of<'a>(p: &'a Program, point: &Point) -> &'a [u8] {
    let start = saturating_usize(point.off);
    let end = start.saturating_add(saturating_usize(u64::from(point.len)));
    p.bytes.get(start..end).unwrap_or(&[])
}

/// Returns the entropy profile of the program's file: every window's
/// entropy in millibits, in file order.
///
/// Reads every file byte once, as the file holds it (not relocated), and
/// keeps the profile in the analysis's memo, keyed by the window used.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the profile.
/// * `window` - Window asked for in bytes ([`window_for`]).
///
/// # Returns
///
/// The profile, at most [`PROFILE_POINTS_MAX`] points, each valued in
/// millibits ([`millibits`]); none for an empty file.
#[must_use]
pub fn entropy_profile(p: &Program, a: &Analysis, window: u64) -> Arc<Profile> {
    let window = window_for(from_usize(p.bytes.len()), window);
    let make = || {
        let mut points = grid(p, window);
        let terms = Terms::upto(window);
        for point in &mut points {
            point.value = u32::from(millibits(bytes_of(p, point), &terms));
        }
        Profile { window, points }
    };
    kept(a, "entropy_profile", window, make, profile_bytes)
}

/// How a histogram cuts its range into bars.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Bins {
    /// One bar per power of two: `[0, 1)`, `[1, 2)`, `[2, 4)`, ... up to
    /// the bar holding the largest value.
    Log2,
    /// This many bars of one width from 0, wide enough that the last
    /// holds the largest value; held to 1 to [`LINEAR_BINS_MAX`].
    Linear(u32),
}

/// Most bars a [`Bins::Linear`] histogram cuts.
pub const LINEAR_BINS_MAX: u32 = 1024;
/// Most members a bar lists; [`Bar::count`] counts them all.
pub const MEMBERS_MAX: usize = 256;

/// One bar of a histogram: a range and what falls in it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bar {
    /// Smallest value the bar holds.
    pub lo: u64,
    /// One past the largest value it holds: a value `v` is in the bar when
    /// `lo <= v < hi`.
    pub hi: u64,
    /// How many fall in it.
    pub count: usize,
    /// The first [`MEMBERS_MAX`] of them, by function entry in address
    /// order.
    pub members: Vec<u64>,
}

/// The functions by size: bars in increasing order that tile `0..` with
/// no gap or overlap, each function in exactly one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Histogram {
    /// How the range was cut, as used: a [`Bins::Linear`] count held to
    /// its bounds.
    pub bins: Bins,
    /// The bars, lowest first.
    pub bars: Vec<Bar>,
    /// Import thunks, counted apart and in no bar.
    pub thunks: usize,
    /// Exception funclets, counted apart and in no bar.
    pub funclets: usize,
}

/// Returns the edges of the bars `bins` cuts for values up to `max`: each
/// bar runs from one edge to the next.
///
/// # Arguments
///
/// * `bins` - How the range is cut, a linear count already held to its
///   bounds.
/// * `max` - The largest value a bar must hold.
fn edges(bins: Bins, max: u64) -> Vec<u64> {
    match bins {
        Bins::Log2 => std::iter::once(0)
            .chain((0..64).map(|k| 1u64 << k))
            .take_while(|&lo| lo <= max)
            .chain([max
                .checked_add(1)
                .and_then(u64::checked_next_power_of_two)
                .unwrap_or(u64::MAX)])
            .collect(),
        Bins::Linear(n) => {
            let n = u64::from(n);
            let width = (max / n.max(1)).saturating_add(1);
            (0..=n).map(|k| k.saturating_mul(width)).collect()
        }
    }
}

/// Returns the program's functions by size, as the function table reports a
/// size ([`crate::analysis::Function::size`]).
///
/// It counts bars of entries, with the import thunks and exception funclets the
/// table leaves out counted apart.
///
/// Reads no bytes: the sizes are the analysis's. Kept in its memo, keyed
/// by the bins used.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `bins` - How the sizes are cut into bars.
///
/// # Returns
///
/// The histogram; one empty bar when no function is listed.
#[must_use]
pub fn function_sizes(a: &Analysis, bins: Bins) -> Arc<Histogram> {
    let bins = match bins {
        Bins::Log2 => Bins::Log2,
        Bins::Linear(n) => Bins::Linear(n.clamp(1, LINEAR_BINS_MAX)),
    };
    let make = || {
        let Selection {
            functions,
            left_out,
            ..
        } = select_functions(a, &Overlay::default(), None);
        let max = functions.iter().map(|f| f.size()).max().unwrap_or(0);
        let edges = edges(bins, max);
        let mut bars: Vec<Bar> = edges
            .iter()
            .zip(edges.iter().skip(1))
            .map(|(&lo, &hi)| Bar {
                lo,
                hi,
                count: 0,
                members: Vec::new(),
            })
            .collect();
        for f in functions {
            let size = f.size();
            let at = bars.partition_point(|b| b.hi <= size);
            if let Some(bar) = bars.get_mut(at) {
                bar.count += 1;
                if bar.members.len() < MEMBERS_MAX {
                    bar.members.push(f.entry);
                }
            }
        }
        Histogram {
            bins,
            bars,
            thunks: left_out.thunks,
            funclets: left_out.funclets,
        }
    };
    let weigh = |h: &Histogram| {
        let members: usize = h.bars.iter().map(|b| b.members.capacity() * 8).sum();
        members + h.bars.capacity() * size_of::<Bar>()
    };
    kept(a, "function_sizes", bins, make, weigh)
}

/// Returns the string density of the program's file: how many bytes of
/// each window lie inside a string, in the grid [`entropy_profile`] uses
/// at the same window, so the two align point for point.
///
/// The strings are those the `strings` table lists by default, read off
/// the same memoized walk ([`crate::strings::walk::string_extents`]), so a
/// session walks its bytes once; a byte two strings cover counts once.
/// Kept in the analysis's memo, keyed by the window used.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the walk and the profile.
/// * `window` - Window asked for in bytes ([`window_for`]).
///
/// # Returns
///
/// The profile, each point valued in bytes, at most its `len`.
#[must_use]
pub fn string_density(p: &Program, a: &Analysis, window: u64) -> Arc<Profile> {
    let len = from_usize(p.bytes.len());
    let window = window_for(len, window);
    let make = || {
        let mut points = grid(p, window);
        let mut counted = 0u64;
        for (start, end) in crate::strings::walk::string_extents(p, a) {
            let (mut at, end) = (start.max(counted), end.min(len));
            counted = counted.max(end);
            while at < end {
                let stop = end.min((at / window + 1).saturating_mul(window));
                if let Some(point) = points.get_mut(saturating_usize(at / window)) {
                    let bytes = u32::try_from(stop - at).unwrap_or(u32::MAX);
                    point.value = point.value.saturating_add(bytes);
                }
                at = stop;
            }
        }
        Profile { window, points }
    };
    kept(a, "string_density", window, make, profile_bytes)
}

/// How many times over the file's length the section entropies may read
/// in all; the sections past it, which only overlapping ones reach, are
/// left unmeasured.
const SECTION_READ_PASSES: u64 = 2;

/// Returns each section's entropy in millibits, in [`Program::sections`]
/// order, over the bytes of its file extent as the image holds them,
/// relocated ([`Program::section_bytes`]).
///
/// Kept in the analysis's memo.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the answer.
///
/// # Returns
///
/// One value per section ([`millibits`]); `None` for a section the file
/// holds no bytes of, one whose extent runs past the end of the file, or
/// one past the read budget ([`SECTION_READ_PASSES`]).
#[must_use]
pub fn section_millibits(p: &Program, a: &Analysis) -> Arc<Vec<Option<u16>>> {
    let make = || {
        let mut budget = from_usize(p.bytes.len()).saturating_mul(SECTION_READ_PASSES);
        let largest = p.sections.iter().map(|s| s.file_size).max().unwrap_or(0);
        let terms = Terms::upto(largest);
        p.sections
            .iter()
            .map(|s| {
                let bytes = p.section_bytes(s).filter(|b| !b.is_empty())?;
                budget = budget.checked_sub(from_usize(bytes.len()))?;
                Some(millibits(bytes, &terms))
            })
            .collect()
    };
    let weigh = |v: &Vec<Option<u16>>| v.capacity() * size_of::<Option<u16>>();
    kept(a, "section_millibits", (), make, weigh)
}

/// The kinds [`stats_tsv`] answers and the settings they take.
const KINDS: &str = "kinds: entropy and strings (window=<bytes>), sizes (bins=<n>), sections; each takes filter=<text> and count";
/// Most members a row of the `sizes` table spells; [`Bar::members`] keeps
/// more.
const MEMBERS_SHOWN: usize = 8;

/// What a `borer://stats` spec asks for, read once.
#[derive(Debug, Default)]
struct Spec<'a> {
    /// Window asked for, in bytes.
    window: Option<u64>,
    /// Linear bins asked for.
    bins: Option<u32>,
    /// Text a row must contain, any case.
    filter: Option<&'a str>,
    /// Only the count of rows.
    count: bool,
}

impl<'a> Spec<'a> {
    /// Reads the settings after the kind.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind, which says which settings it takes.
    /// * `words` - The settings, each once.
    ///
    /// # Errors
    ///
    /// When a setting is not one the kind takes, is given twice, or its
    /// number is not decimal.
    fn read(kind: &str, words: impl Iterator<Item = &'a str>) -> Result<Self, String> {
        let mut spec = Spec::default();
        let mut seen: Vec<&str> = Vec::new();
        for word in words {
            let (key, value) = word.split_once('=').unwrap_or((word, ""));
            if seen.contains(&key) {
                return Err(format!("{} is given twice", text::one_line(key)));
            }
            seen.push(key);
            let number = || {
                value
                    .parse::<u64>()
                    .map_err(|_| format!("{}: not a decimal number", text::one_line(word)))
            };
            match (kind, key) {
                ("entropy" | "strings", "window") => spec.window = Some(number()?),
                ("sizes", "bins") => spec.bins = Some(u32::try_from(number()?).unwrap_or(u32::MAX)),
                (_, "filter") => spec.filter = Some(value),
                (_, "count") if value.is_empty() => spec.count = true,
                _ => return Err(format!("{kind} takes no {}; {KINDS}", text::one_line(word))),
            }
        }
        Ok(spec)
    }
}

/// Returns one chart series as the `borer://stats/<kind>` table, the rows
/// a filter keeps, a page at a time.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the series; an empty one serves
///   every kind but `sizes`.
/// * `spec` - The kind, then comma-separated settings, each once:
///   `entropy` or `strings` take `window=<bytes>` ([`WINDOW_DEFAULT`] by
///   default), `sizes` takes `bins=<n>` for `n` bins of one width (one per
///   power of two by default), and every kind takes `filter=<text>` (rows
///   containing it, any case) and `count` (the count of rows alone).
/// * `window` - The page shown.
///
/// # Returns
///
/// The page: a `# showing` line, a note saying what the table holds and
/// which bytes it read, a column header and one row per point, bar or
/// section.
///
/// # Errors
///
/// When the kind is not one of [`KINDS`], a setting is not one the kind
/// takes or is given twice, a number is not decimal, or `sizes` is asked of
/// an architecture whose code is not discovered.
pub fn stats_tsv(
    p: &Program,
    a: &Analysis,
    spec: &str,
    window: Window<'_>,
) -> Result<String, String> {
    let mut words = spec.split(',').map(str::trim).filter(|w| !w.is_empty());
    let kind = words.next().unwrap_or_default();
    if !matches!(kind, "entropy" | "strings" | "sizes" | "sections") {
        return Err(format!("no stats kind {}; {KINDS}", text::one_line(kind)));
    }
    let asked = Spec::read(kind, words)?;
    let size = asked.window.unwrap_or(from_usize(WINDOW_DEFAULT));
    let whole = match kind {
        "entropy" => profile_tsv(
            p,
            &entropy_profile(p, a, size),
            "millibits",
            "1000 x the bits per byte of the window's bytes as the file holds them, not relocated (0 to 8000, integer)",
        ),
        "strings" => profile_tsv(
            p,
            &string_density(p, a, size),
            "bytes",
            "the window's file bytes inside strings of 5 or more characters outside code, the windows of entropy at this window",
        ),
        "sizes" => {
            if let Some(why) = p.refuses(Feature::Discover) {
                return Err(why);
            }
            sizes_tsv(&function_sizes(
                a,
                asked.bins.map_or(Bins::Log2, Bins::Linear),
            ))
        }
        _ => sections_tsv(p, &section_millibits(p, a)),
    };
    Ok(shaped(&whole, asked.filter, asked.count, window))
}

/// Returns the rows of a table a filter keeps, paged, or their count.
///
/// # Arguments
///
/// * `whole` - The table.
/// * `filter` - Text a row must contain, any case; `None` keeps every row.
/// * `count` - Answer the table's note and the count of rows alone.
/// * `window` - The page shown.
fn shaped(whole: &str, filter: Option<&str>, count: bool, window: Window<'_>) -> String {
    let needle = filter.map(str::to_lowercase);
    let lines = table::classify(whole);
    let keeps = |kind: Line, line: &str| {
        kind != Line::Row
            || needle
                .as_deref()
                .is_none_or(|n| line.to_lowercase().contains(n))
    };
    if count {
        let rows = lines
            .iter()
            .filter(|&&(kind, line)| kind == Line::Row && keeps(kind, line))
            .count();
        let note = whole.lines().next().unwrap_or_default();
        return format!("{note}\n# {rows} rows\n");
    }
    let mut kept = String::new();
    for (kind, line) in lines {
        if keeps(kind, line) {
            kept.push_str(line);
            kept.push('\n');
        }
    }
    table::page(
        &kept,
        window.skip,
        window.limit,
        window.again.unwrap_or_default(),
    )
}

/// Returns a profile as a table, a row per window.
///
/// # Arguments
///
/// * `p` - The loaded program, for the sections' names.
/// * `profile` - The series.
/// * `column` - The value column's name.
/// * `means` - What the value is and which bytes it read, for the note.
fn profile_tsv(p: &Program, profile: &Profile, column: &str, means: &str) -> String {
    let mut out = format!(
        "# {} windows of {} bytes over {} file bytes, in file order; {column} is {means}\noff\tlen\tva\tsection\t{column}\n",
        profile.points.len(),
        profile.window,
        p.bytes.len()
    );
    for q in &profile.points {
        let va = q.va.map_or_else(String::new, |va| format!("{va:#x}"));
        let section = q
            .section
            .and_then(|i| p.sections.get(i))
            .map_or_else(String::new, |s| text::one_line(&s.name));
        let _ = writeln!(out, "{:#x}\t{}\t{va}\t{section}\t{}", q.off, q.len, q.value);
    }
    out
}

/// Returns a histogram of function sizes as a table, a row per bar.
///
/// # Arguments
///
/// * `h` - The histogram.
fn sizes_tsv(h: &Histogram) -> String {
    let counted: usize = h.bars.iter().map(|b| b.count).sum();
    let cut = match h.bins {
        Bins::Log2 => "one per power of two",
        Bins::Linear(_) => "of one width",
    };
    let mut out = format!(
        "# {counted} functions by bytes of code in {} bins {cut}, lo <= size < hi; {} import thunks and {} exception funclets apart; members are entries in address order, the first {MEMBERS_SHOWN} shown\nlo\thi\tcount\tmembers\n",
        h.bars.len(),
        h.thunks,
        h.funclets
    );
    for b in &h.bars {
        let shown: Vec<String> = b
            .members
            .iter()
            .take(MEMBERS_SHOWN)
            .map(|e| format!("{e:#x}"))
            .collect();
        let more = b.count.saturating_sub(shown.len());
        let more = if more > 0 {
            format!(" +{more} more")
        } else {
            String::new()
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}{more}",
            b.lo,
            b.hi,
            b.count,
            shown.join(",")
        );
    }
    out
}

/// Returns the sections with their entropy as a table, a row per section.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `measured` - Each section's millibits ([`section_millibits`]).
fn sections_tsv(p: &Program, measured: &[Option<u16>]) -> String {
    let mut out = format!(
        "# {} sections in table order; millibits is 1000 x the bits per byte of the section's bytes as the image holds them, relocated (0 to 8000, integer), empty where none were read\nname\tva\tvsize\toff\tsize\trwx\tmillibits\n",
        p.sections.len()
    );
    for (s, m) in p.sections.iter().zip(measured) {
        let _ = writeln!(
            out,
            "{}\t{:#x}\t{:#x}\t{:#x}\t{:#x}\t{}\t{}",
            text::one_line(&s.name),
            s.va.0,
            s.vsize,
            s.file_off.0,
            s.file_size,
            s.perms(),
            m.map_or_else(String::new, |m| m.to_string())
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::Function;
    use crate::entropy::shannon;
    use crate::num::as_f64;
    use crate::program::{Arch, Section};

    /// Returns the bytes of a seeded xorshift stream: the same on every
    /// host.
    ///
    /// # Arguments
    ///
    /// * `seed` - Any nonzero seed.
    /// * `len` - Bytes wanted.
    fn noise(seed: u64, len: usize) -> Vec<u8> {
        let mut x = seed | 1;
        (0..len)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x.to_le_bytes()[0]
            })
            .collect()
    }

    /// The fixed-point logarithm is within `2^-31` of the float one across
    /// small values, powers of two and their neighbours, and the top of the
    /// range: a coarser fixed point (16 fractional bits) is not.
    ///
    /// # Panics
    ///
    /// When a logarithm is further off.
    #[test]
    fn the_fixed_point_logarithm_is_within_its_bound() {
        let shifts = (1..64).flat_map(|k| {
            let p = 1u64 << k;
            [p - 1, p, p + 1]
        });
        let values =
            (1..5000u64)
                .chain(shifts)
                .chain([u64::MAX, 0xdead_beef, 1_000_003, 999_999_937]);
        for x in values {
            let fixed = as_f64(log2_fixed(x)) / as_f64(1 << FRAC);
            let error = (fixed - as_f64(x).log2()).abs();
            assert!(error < 1.0 / as_f64(1 << 31), "log2({x}) off by {error}");
        }
        assert_eq!(log2_fixed(0), 0);
        assert_eq!(log2_fixed(1 << 40), 40 << FRAC);
    }

    /// Integer entropy is within one millibit of the float entropy for 200
    /// seeded buffers of every shape, and exact at the extremes.
    ///
    /// # Panics
    ///
    /// When a buffer's millibits stray, or an extreme is not exact.
    #[test]
    fn integer_entropy_agrees_with_the_float_one() {
        let text = b"The quick brown fox jumps over the lazy dog, again and again. ";
        for k in 0..200usize {
            let len = 1 + k * 37;
            let bytes: Vec<u8> = match k % 5 {
                0 => vec![0; len],
                1 => vec![0x41; len],
                2 => (0..len).map(|i| i.to_le_bytes()[0]).collect(),
                3 => text.iter().copied().cycle().take(len).collect(),
                _ => noise(from_usize(k), len),
            };
            let got = millibits(&bytes, &Terms::upto(from_usize(len)));
            let want = (1000.0 * shannon(&bytes)).round();
            assert!(
                (f64::from(got) - want).abs() <= 1.0,
                "buffer {k}: {got} against {want}"
            );
        }
        let uniform: Vec<u8> = (0..256 * 40).map(|i: usize| i.to_le_bytes()[0]).collect();
        assert_eq!(millibits(&uniform, &Terms::upto(64)), 8000);
        assert_eq!(millibits(&[7; 5000], &Terms::upto(64)), 0);
        assert_eq!(millibits(&[], &Terms::upto(64)), 0);
        assert_eq!(millibits(&[9], &Terms::upto(1)), 0);
    }

    /// Builds the profile test's program: headers, three sections (the
    /// last with a zero-filled tail) and an overlay past them.
    fn three_sections() -> Program {
        let mut bytes = noise(3, 0x5000);
        bytes[0x1000..0x2000].fill(0);
        let text = Section::mapped(".text", 0x40_1000, 0x400, 0x1c00, false, true);
        let data = Section::mapped(".data", 0x40_3000, 0x2000, 0x1000, true, false);
        let mut bss = Section::mapped(".bss", 0x40_4000, 0x3000, 0x800, true, false);
        bss.vsize = 0x4000;
        Program::raw(bytes, Arch::X86_64, 0x40_0000, None, vec![text, data, bss])
    }

    /// The section runs answer what the program's linear scan answers for
    /// every offset, where sections overlap, nest, sit empty or map past
    /// the top of the address space.
    ///
    /// # Panics
    ///
    /// When a run names another section or address than the scan.
    #[test]
    fn section_runs_answer_what_the_scan_answers() {
        let far = Section::mapped("far", u64::MAX - 0x10, 0x200, 0x80, false, false);
        let sections = vec![
            Section::mapped("b", 0x9000, 0x80, 0x180, false, false),
            Section::mapped("a", 0x1000, 0, 0x100, false, false),
            Section::mapped("c", 0x5000, 0x40, 0x20, false, false),
            Section::mapped("empty", 0x7000, 0x60, 0, false, false),
            far,
            Section::mapped("d", 0xa000, 0x1c0, 0x80, false, false),
        ];
        let p = Program::raw(vec![0; 0x300], Arch::X86_64, 0, None, sections);
        let owners = Owners::of(&p);
        for off in 0..0x300 {
            assert_eq!(owners.at(&p, off), p.offset_mapping(off), "{off:#x}");
        }
    }

    /// A profile's points tile the file with no gap or overlap, each placed
    /// where the program maps its first byte.
    ///
    /// A file too large for the window asked gets a grown power-of-two window
    /// and at most [`PROFILE_POINTS_MAX`] points.
    ///
    /// # Panics
    ///
    /// When a point leaves a gap, overlaps, or is placed elsewhere than the
    /// program maps it, or the large file's profile outgrows its cap.
    #[test]
    fn a_profile_tiles_the_file_where_the_program_maps_it() {
        let p = three_sections();
        let a = Analysis::default();
        let profile = entropy_profile(&p, &a, 1024);
        assert_eq!(profile.window, 1024);
        let mut next = 0u64;
        for point in &profile.points {
            assert_eq!(point.off, next, "{point:?}");
            next += u64::from(point.len);
            assert_eq!(point.va, p.offset_to_va(point.off), "{point:?}");
            let at = point.va.and_then(|va| p.section_at(va));
            let held = point.section.map(|i| &p.sections[i]);
            assert!(
                held.map(std::ptr::from_ref) == at.map(std::ptr::from_ref),
                "{point:?}"
            );
            assert!(point.value <= 8000, "{point:?}");
        }
        assert_eq!(next, from_usize(p.bytes.len()));
        assert_eq!(profile.points.len(), 20);
        assert_eq!(
            (profile.points[0].va, profile.points[0].section),
            (None, None)
        );
        assert_eq!(profile.points[1].section, Some(0));
        assert_eq!(profile.points[5].value, 0, "the zeroed run");
        assert_eq!(profile.points[19].section, None, "the overlay");
        assert!(Arc::ptr_eq(&profile, &entropy_profile(&p, &a, 1024)));
        let big = Program::raw(vec![0; 100 << 20], Arch::X86_64, 0, None, Vec::new());
        let held = Analysis::default();
        let profile = entropy_profile(&big, &held, 1024);
        assert_eq!(profile.window, 32 << 10);
        assert_eq!(profile.points.len(), 3200);
        assert!(profile.points.len() <= PROFILE_POINTS_MAX);
        let builds = held.derived.builds();
        assert!(Arc::ptr_eq(&profile, &entropy_profile(&big, &held, 4096)));
        assert_eq!(
            held.derived.builds(),
            builds,
            "a window grown to the same one is one key"
        );
    }

    /// A loop over many windows keeps the series within the memo's item
    /// budget: each is an item, weighed and let go like any other.
    ///
    /// # Panics
    ///
    /// When the series held outgrow the budget.
    #[test]
    fn many_windows_stay_within_the_memo_budget() {
        /// The budget the loop runs under, in bytes.
        const BUDGET: usize = 64 << 10;
        let p = three_sections();
        let a = Analysis::default();
        a.derived.set_budget(BUDGET);
        for window in 64..400 {
            let _profile = entropy_profile(&p, &a, window);
            let _density = string_density(&p, &a, window);
            assert!(a.derived.item_bytes() <= BUDGET, "window {window}");
        }
        assert!(a.derived.held("entropy_profile") < 336);
    }

    /// Builds a program of three functions: `0x1000` calls `0x1010` and
    /// `0x1020`, of 11, 3 and 4 bytes.
    fn three_functions() -> Program {
        let mut code = vec![0xcc; 0x30];
        // ASM: call 0x1010; call 0x1020; ret
        code[..11].copy_from_slice(&[0xe8, 0x0b, 0, 0, 0, 0xe8, 0x16, 0, 0, 0, 0xc3]);
        // ASM: xor eax,eax; ret
        code[0x10..0x13].copy_from_slice(&[0x31, 0xc0, 0xc3]);
        // ASM: mov rax,rcx; ret
        code[0x20..0x24].copy_from_slice(&[0x48, 0x89, 0xc8, 0xc3]);
        let text = Section::mapped(".text", 0x1000, 0, 0x30, false, true);
        Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text])
    }

    /// Asserts what every histogram holds: bars that tile `0..` in order,
    /// each member's size in its bar, and every listed function in exactly
    /// one bar, the counts summing to them.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis the histogram was made of.
    /// * `h` - The histogram.
    ///
    /// # Panics
    ///
    /// When a bar leaves a gap, a member lies outside its bar, or a
    /// function is in no bar or in two.
    fn holds_every_function_once(a: &Analysis, h: &Histogram) {
        let mut next = 0;
        for bar in &h.bars {
            assert_eq!((bar.lo, bar.lo < bar.hi), (next, true), "{bar:?}");
            next = bar.hi;
            assert_eq!(bar.members.len(), bar.count.min(MEMBERS_MAX), "{bar:?}");
            assert!(bar.members.is_sorted(), "{bar:?}");
            for &entry in &bar.members {
                let size = a.function(entry).map_or(u64::MAX, Function::size);
                assert!(
                    (bar.lo..bar.hi).contains(&size),
                    "{entry:#x} {size} {bar:?}"
                );
            }
        }
        let listed: Vec<&Function> = a
            .functions
            .iter()
            .filter(|f| f.thunk.is_none() && f.funclet.is_none())
            .collect();
        for f in &listed {
            let holding = h
                .bars
                .iter()
                .filter(|b| (b.lo..b.hi).contains(&f.size()))
                .count();
            assert_eq!(holding, 1, "{:#x}", f.entry);
        }
        let counted: usize = h.bars.iter().map(|b| b.count).sum();
        assert_eq!(counted + h.thunks + h.funclets, a.functions.len());
        assert_eq!(counted, listed.len());
    }

    /// The functions of a discovered program and of a synthetic analysis of
    /// 100,000 functions each sit in exactly one bar of either kind, a size on
    /// a boundary in the bar it opens.
    ///
    /// Members stop at [`MEMBERS_MAX`] while the count goes on, and thunks are
    /// counted apart.
    ///
    /// # Panics
    ///
    /// When a function is in no bar or two, a member is out of its bar, or
    /// the cap loses a count.
    #[test]
    fn every_function_is_in_exactly_one_bar() {
        let p = three_functions();
        let a = Analysis::compute(&p);
        let sizes: Vec<u64> = a.functions.iter().map(Function::size).collect();
        assert_eq!(sizes, [11, 3, 4]);
        let log2 = function_sizes(&a, Bins::Log2);
        holds_every_function_once(&a, &log2);
        let counts: Vec<(u64, usize)> = log2.bars.iter().map(|b| (b.lo, b.count)).collect();
        assert_eq!(counts, [(0, 0), (1, 0), (2, 1), (4, 1), (8, 1)]);
        assert!(Arc::ptr_eq(&log2, &function_sizes(&a, Bins::Log2)));
        let template = a.functions[0].clone();
        let mut many = Analysis::default();
        many.functions = (0..100_000u64)
            .map(|i| {
                let mut f = template.clone();
                f.entry = 0x10_0000 + i * 0x100;
                let mut block = template.blocks[0].clone();
                (block.start, block.end) = (f.entry, f.entry + i % 5000);
                f.blocks = vec![block];
                f.thunk = (i % 97 == 0).then_some(0x2000);
                f
            })
            .collect();
        many.entry_index = many
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.entry, i))
            .collect();
        for bins in [
            Bins::Log2,
            Bins::Linear(7),
            Bins::Linear(0),
            Bins::Linear(5000),
        ] {
            let h = function_sizes(&many, bins);
            holds_every_function_once(&many, &h);
            assert_eq!(h.thunks, 1031, "{bins:?}");
        }
        let capped = function_sizes(&many, Bins::Log2);
        assert!(capped.bars.iter().any(|b| b.count > MEMBERS_MAX));
        assert_eq!(function_sizes(&many, Bins::Linear(0)).bars.len(), 1);
        assert_eq!(
            function_sizes(&many, Bins::Linear(5000)).bars.len(),
            usize::try_from(LINEAR_BINS_MAX).unwrap_or(0)
        );
    }

    /// Builds a file of zeros holding an ASCII string across the first
    /// window boundary (2 bytes before it, 8 after) and a UTF-16 string of
    /// 22 bytes in the third window.
    fn strings_program() -> Program {
        let mut bytes = vec![0; 0x1000];
        bytes[0x3fe..0x408].copy_from_slice(b"abcdefghij");
        for (k, &b) in b"wide string".iter().enumerate() {
            bytes[0x900 + 2 * k] = b;
        }
        Program::raw(bytes, Arch::X86_64, 0, None, Vec::new())
    }

    /// String density counts each window's bytes inside strings on the
    /// grid of the entropy profile at the same window, splitting a string
    /// across the windows it spans.
    ///
    /// # Panics
    ///
    /// When a point's extent differs between the two series, or a window's
    /// string bytes are miscounted.
    #[test]
    fn string_density_aligns_with_the_entropy_profile() {
        let p = strings_program();
        let a = Analysis::default();
        let density = string_density(&p, &a, 1024);
        let entropy = entropy_profile(&p, &a, 1024);
        let extent = |profile: &Profile| -> Vec<(u64, u32)> {
            profile.points.iter().map(|q| (q.off, q.len)).collect()
        };
        assert_eq!(extent(&density), extent(&entropy));
        assert_eq!(density.window, entropy.window);
        let values: Vec<u32> = density.points.iter().map(|q| q.value).collect();
        assert_eq!(values, [2, 8, 22, 0]);
        let p = three_sections();
        let a = Analysis::default();
        assert_eq!(
            extent(&string_density(&p, &a, 300)),
            extent(&entropy_profile(&p, &a, 300))
        );
    }

    /// String density reads the walk the strings table keeps: asked first,
    /// it builds that walk, and the table read after it walks nothing.
    ///
    /// # Panics
    ///
    /// When the density walks the bytes on its own, or the table walks
    /// again.
    #[test]
    fn string_density_shares_the_strings_walk() {
        let p = strings_program();
        let a = Analysis::default();
        let _density = string_density(&p, &a, 1024);
        assert_eq!(a.derived.held("string_walks"), 1);
        let builds = a.derived.builds();
        let rows = crate::strings::walk::string_rows(
            &p,
            &a,
            crate::strings::walk::StringEncoding::Both,
            crate::strings::walk::WALK_MIN,
            None,
            0,
            10,
        );
        assert_eq!(rows.total, 2, "{rows:?}");
        assert_eq!(a.derived.builds(), builds, "the table walks nothing");
    }

    /// Each section's entropy is the integer entropy of its file bytes; a
    /// section with none, one past the end of the file and one past the
    /// read budget answer none.
    ///
    /// # Panics
    ///
    /// When a section's millibits differ from its bytes', or one that
    /// cannot be measured has a value.
    #[test]
    fn sections_are_measured_within_the_read_budget() {
        let p = three_sections();
        let measured = section_millibits(&p, &Analysis::default());
        assert_eq!(measured.len(), 3);
        for (s, &got) in p.sections.iter().zip(measured.iter()) {
            let bytes = p.section_bytes(s).unwrap_or(&[]);
            assert_eq!(got, Some(millibits(bytes, &Terms::upto(0))), "{}", s.name);
        }
        assert_eq!(
            measured[1].map(|m| m > 7000),
            Some(true),
            "the noise of .data"
        );
        let whole = |name: &str| Section::mapped(name, 0x1000, 0, 0x1000, false, false);
        let mut sections = vec![whole("a"), whole("b"), whole("c")];
        sections.push(Section::mapped("past", 0x9000, 0x800, 0x1000, false, false));
        sections.push(Section::mapped("bss", 0xa000, 0, 0, true, false));
        let p = Program::raw(noise(5, 0x1000), Arch::X86_64, 0, None, sections);
        let measured = section_millibits(&p, &Analysis::default());
        let some: Vec<bool> = measured.iter().map(Option::is_some).collect();
        assert_eq!(some, [true, true, false, false, false]);
    }

    /// Each kind's table spells its series under a note and a column
    /// header, and a kind or setting the tables do not know is refused
    /// with the kinds listed.
    ///
    /// # Panics
    ///
    /// When a table misspells its series, or a bad spec answers.
    #[test]
    fn the_stats_tables_spell_each_series() {
        let p = three_functions();
        let a = Analysis::compute(&p);
        let whole = Window::first(usize::MAX);
        let table = |spec: &str| stats_tsv(&p, &a, spec, whole).unwrap_or_else(|e| e);
        let sizes = table("sizes");
        assert!(
            sizes.starts_with(
                "# showing 5 of 5 from 0\n# 3 functions by bytes of code in 5 bins one per power of two"
            ),
            "{sizes}"
        );
        assert!(
            sizes.contains("\nlo\thi\tcount\tmembers\n0\t1\t0\t\n"),
            "{sizes}"
        );
        assert!(sizes.contains("\n2\t4\t1\t0x1010\n"), "{sizes}");
        let linear = table("sizes,bins=2");
        assert!(
            linear.contains("\n0\t6\t2\t0x1010,0x1020\n6\t12\t1\t0x1000\n"),
            "{linear}"
        );
        let entropy = table("entropy, window=64");
        assert!(
            entropy.contains("\n# 1 windows of 64 bytes over 48 file bytes"),
            "{entropy}"
        );
        assert!(
            entropy.contains("as the file holds them, not relocated"),
            "{entropy}"
        );
        assert!(
            entropy.contains("\noff\tlen\tva\tsection\tmillibits\n0x0\t48\t0x1000\t.text\t"),
            "{entropy}"
        );
        assert!(
            table("strings")
                .contains("\noff\tlen\tva\tsection\tbytes\n0x0\t48\t0x1000\t.text\t0\n")
        );
        let sections = table("sections");
        assert!(
            sections.contains("\n.text\t0x1000\t0x30\t0x0\t0x30\tr-x\t"),
            "{sections}"
        );
        assert!(
            sections.contains("as the image holds them, relocated"),
            "{sections}"
        );
        let kept = table("sizes,filter=0X1010");
        assert!(kept.starts_with("# showing 1 of 1 from 0\n"), "{kept}");
        assert!(kept.contains("\n2\t4\t1\t0x1010\n"), "{kept}");
        assert_eq!(
            table("sizes,count"),
            "# 3 functions by bytes of code in 5 bins one per power of two, lo <= size < hi; 0 import thunks and 0 exception funclets apart; members are entries in address order, the first 8 shown\n# 5 rows\n"
        );
        let again = Window {
            skip: 1,
            limit: 2,
            again: Some("borer://stats/sizes"),
        };
        let paged = stats_tsv(&p, &a, "sizes", again).unwrap_or_default();
        assert!(paged.starts_with("# showing 2 of 5 from 1\n"), "{paged}");
        assert!(
            paged.ends_with("# 2 more; borer://stats/sizes!offset=3 for the next page\n"),
            "{paged}"
        );
        for (spec, refusal) in [
            ("nosuch", "no stats kind nosuch; kinds: "),
            ("sizes,window=64", "sizes takes no window=64; kinds: "),
            ("entropy,window=0x40", "window=0x40: not a decimal number"),
            ("sections,bins=2", "sections takes no bins=2"),
            ("entropy,window=64,window=128", "window is given twice"),
            ("sizes,count=1", "sizes takes no count=1"),
        ] {
            let refused = stats_tsv(&p, &a, spec, whole).err().unwrap_or_default();
            assert!(refused.starts_with(refusal), "{spec}: {refused}");
        }
    }

    /// An empty file, a one-byte file and a file whose sections all point
    /// past its end answer every table, with series as short as their
    /// bytes, and measure no section.
    ///
    /// # Panics
    ///
    /// When a table is refused or a series is longer than its file.
    #[test]
    fn hostile_files_answer_short_series() {
        let past = |name: &str| Section::mapped(name, 0x1000, 0x10_0000, 0x1000, false, true);
        for (bytes, sections, points) in [
            (Vec::new(), Vec::new(), 0),
            (vec![0x90], Vec::new(), 1),
            (vec![0xcc; 300], vec![past(".text"), past(".data")], 5),
        ] {
            let p = Program::raw(bytes, Arch::X86_64, 0, None, sections);
            let a = Analysis::compute(&p);
            for spec in [
                "entropy",
                "strings",
                "sizes",
                "sections",
                "entropy,window=0",
                "strings,window=18446744073709551615",
                "sizes,bins=4294967296",
            ] {
                let table = stats_tsv(&p, &a, spec, Window::first(usize::MAX));
                assert!(table.is_ok(), "{spec}");
            }
            let profile = entropy_profile(&p, &a, 64);
            assert_eq!(profile.points.len(), points);
            assert!(profile.points.iter().all(|q| q.va.is_none()));
            assert_eq!(string_density(&p, &a, 64).points.len(), points);
            assert!(section_millibits(&p, &a).iter().all(Option::is_none));
        }
    }
}
