//! Finding values in a process, and narrowing what was found.
//!
//! A first scan reads the process's readable regions (all of them, a
//! module's, or the heaps) and keeps every address holding a value: an
//! integer, a float within a tolerance, a string, or bytes with wildcards
//! ([`Needle`]). A next scan reads only those addresses again and keeps
//! the ones whose value changed, stayed, rose, fell, or now equals a value
//! ([`Compare`]), which is how a value seen on screen is pinned to the one
//! address that holds it. Hits are kept in address order, so the same
//! memory gives the same answer.

use std::cmp::Ordering;
use std::fmt::Write as _;
use std::ops::ControlFlow;

use super::{CHUNK, Memory, Module, PAGE, SCAN_MAX};
use crate::cancel::Cancel;
use crate::memory::{Kind, le_word, scalar_text};
use crate::num::{as_f64, from_usize, lo8, lo16, lo32};

/// Most hits a result set keeps.
pub const STORE_HITS: usize = 1 << 21;

/// Most bytes of values a result set keeps; a wide needle keeps fewer hits.
const STORE_BYTES: usize = 16 << 20;

/// Longest byte pattern or string a scan takes, in bytes.
pub const PATTERN_MAX: usize = 256;

/// Most bytes between two hits a next scan reads in one piece rather than
/// two.
const GAP: u64 = 0x1000;

/// Why a sweep of a process's memory stopped before its end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stop {
    /// It collected as many hits as it keeps.
    Full,
    /// It read [`SCAN_MAX`] bytes.
    Budget,
    /// The request's deadline passed.
    Deadline,
}

/// What a sweep read.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Swept {
    /// Bytes read.
    pub bytes: u64,
    /// Ranges (regions, or their part in a module) read.
    pub regions: usize,
    /// Pages listed readable that did not read when the sweep came to them.
    pub unread_pages: u64,
    /// Why the sweep stopped early; `None` when it read everything.
    pub stop: Option<Stop>,
}

impl Swept {
    /// Adds another sweep's counts, keeping the first stop.
    ///
    /// # Arguments
    ///
    /// * `other` - The later sweep.
    pub fn add(&mut self, other: Swept) {
        self.bytes = self.bytes.saturating_add(other.bytes);
        self.regions = self.regions.saturating_add(other.regions);
        self.unread_pages = self.unread_pages.saturating_add(other.unread_pages);
        self.stop = self.stop.or(other.stop);
    }

    /// Says what was read, for an answer's header.
    ///
    /// # Arguments
    ///
    /// * `left_out` - Committed regions the process lists as not readable
    ///   (guard or no-access pages), never read.
    pub fn line(&self, left_out: usize) -> String {
        let mut out = format!(
            "# read {:.1} MiB in {} regions; {} committed regions left out as guard or no-access",
            as_f64(self.bytes) / as_f64(1 << 20),
            self.regions,
            left_out
        );
        if self.unread_pages > 0 {
            let _ = write!(
                out,
                "; {} pages did not read when reached",
                self.unread_pages
            );
        }
        out.push('\n');
        out
    }
}

/// Reads ranges of a process a piece at a time.
///
/// Each piece is at most [`CHUNK`] bytes plus `overlap`, so a value that
/// starts in one piece and ends in the next is whole in the first; a page
/// that does not read is stepped over. The sweep stops at [`SCAN_MAX`]
/// bytes, when the request's deadline passes, or when `visit` breaks.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `ranges` - `(start, end)` address ranges, in address order.
/// * `overlap` - Bytes read past each piece: the needle's width less one.
/// * `visit` - Called with each piece's address, its bytes, and how many
///   of its first bytes are its own (a value starting past them belongs to
///   the next piece); breaking stops the sweep as full.
pub(crate) fn sweep(
    mem: &dyn Memory,
    ranges: &[(u64, u64)],
    overlap: usize,
    mut visit: impl FnMut(u64, &[u8], usize) -> ControlFlow<()>,
) -> Swept {
    let mut swept = Swept::default();
    'ranges: for &(start, end) in ranges {
        swept.regions += 1;
        let mut at = start;
        while at < end {
            if Cancel::raised() {
                swept.stop = Some(Stop::Deadline);
                break 'ranges;
            }
            if swept.bytes >= SCAN_MAX {
                swept.stop = Some(Stop::Budget);
                break 'ranges;
            }
            let want = usize::try_from(end - at)
                .unwrap_or(usize::MAX)
                .min(CHUNK.saturating_add(overlap));
            let Some(bytes) = mem.read(at, want).filter(|b| !b.is_empty()) else {
                swept.unread_pages += 1;
                at = (at | (PAGE - 1)).saturating_add(1);
                continue;
            };
            let got = bytes.len();
            let own = if got == want && want > CHUNK {
                CHUNK
            } else {
                got
            };
            swept.bytes = swept.bytes.saturating_add(from_usize(own));
            if visit(at, &bytes, own).is_break() {
                swept.stop = Some(Stop::Full);
                break 'ranges;
            }
            at = at.saturating_add(from_usize(own));
        }
    }
    swept
}

/// What a scan looks for.
#[derive(Debug, Clone, PartialEq)]
pub enum Needle {
    /// An integer kind (`U8`..`I64`) and its value's bits, matched exactly
    /// at addresses aligned to its width.
    Int {
        /// The integer kind.
        kind: Kind,
        /// The value, two's complement, in the kind's width.
        bits: u64,
    },
    /// A float kind (`F32`, `F64`) matched within a tolerance at addresses
    /// aligned to its width.
    Float {
        /// The float kind.
        kind: Kind,
        /// The value.
        value: f64,
        /// Largest difference that still matches, at least zero.
        tolerance: f64,
    },
    /// A string's bytes (`CStr` UTF-8, `WStr` UTF-16LE), no terminator,
    /// matched exactly at any address.
    Text {
        /// The string kind.
        kind: Kind,
        /// The encoded bytes, 1 to [`PATTERN_MAX`].
        bytes: Vec<u8>,
    },
    /// Bytes, `None` a wildcard, at any address; at least one is fixed.
    Bytes(Vec<Option<u8>>),
}

impl Needle {
    /// Parses a value of a kind as an agent typed it.
    ///
    /// An integer is decimal (a sign for a signed kind) or `0x` hex, and
    /// must fit the kind. A float's tolerance, when none is given, is half
    /// a unit of its last digit (`100` matches 99.5 to 100.5, `1.25` 1.245
    /// to 1.255), as a game shows a value rounded. A string is matched as
    /// its bytes, case and all.
    ///
    /// # Arguments
    ///
    /// * `kind` - Any [`Kind`] but `Ptr`.
    /// * `text` - The value.
    /// * `tolerance` - For a float, the largest difference that matches.
    ///
    /// # Errors
    ///
    /// When the text does not read as the kind, does not fit it, a string
    /// is empty or longer than [`PATTERN_MAX`] bytes, a tolerance is
    /// negative or given for another kind, or the kind is `Ptr`.
    pub fn parse(kind: Kind, text: &str, tolerance: Option<f64>) -> Result<Needle, String> {
        let float = matches!(kind, Kind::F32 | Kind::F64);
        if tolerance.is_some() && !float {
            return Err("tolerance applies to f32 and f64 only".to_owned());
        }
        match kind {
            Kind::U8 | Kind::U16 | Kind::U32 | Kind::U64 => {
                let t = text.trim();
                let v = t
                    .strip_prefix("0x")
                    .or_else(|| t.strip_prefix("0X"))
                    .map_or_else(|| t.parse::<u64>(), |h| u64::from_str_radix(h, 16))
                    .map_err(|_| format!("{t} is not an unsigned integer (decimal or 0x hex)"))?;
                let bits = 8 * kind.size(8);
                if bits < 64 && v >> bits != 0 {
                    return Err(format!("{t} does not fit {bits} bits"));
                }
                Ok(Needle::Int { kind, bits: v })
            }
            Kind::I8 | Kind::I16 | Kind::I32 | Kind::I64 => {
                let t = text.trim();
                let v = t
                    .parse::<i64>()
                    .map_err(|_| format!("{t} is not a signed decimal integer"))?;
                let bits = 8 * kind.size(8);
                let lo = i64::MIN >> (64 - bits);
                if v < lo || v > !lo {
                    return Err(format!("{t} does not fit a signed {bits}-bit integer"));
                }
                let mask = if bits == 64 {
                    u64::MAX
                } else {
                    (1 << bits) - 1
                };
                Ok(Needle::Int {
                    kind,
                    bits: v.cast_unsigned() & mask,
                })
            }
            Kind::F32 | Kind::F64 => float_needle(kind, text.trim(), tolerance),
            Kind::CStr | Kind::WStr => {
                let bytes: Vec<u8> = if kind == Kind::CStr {
                    text.as_bytes().to_vec()
                } else {
                    text.encode_utf16().flat_map(u16::to_le_bytes).collect()
                };
                if bytes.is_empty() || bytes.len() > PATTERN_MAX {
                    return Err(format!(
                        "a string to scan for is 1 to {PATTERN_MAX} bytes; this one is {}",
                        bytes.len()
                    ));
                }
                Ok(Needle::Text { kind, bytes })
            }
            Kind::Ptr => Err(
                "scan for a pointer as u32 or u64, or find chains to an address with live_path"
                    .to_owned(),
            ),
        }
    }

    /// Parses an array of bytes: hex pairs, `??` (or a lone `?`) a
    /// wildcard, spaces optional between pairs (`48 8b ?? 05`, `488B??05`).
    ///
    /// # Arguments
    ///
    /// * `text` - The pattern.
    ///
    /// # Errors
    ///
    /// When a pair is not hex, the pattern is empty, all wildcards, or
    /// longer than [`PATTERN_MAX`] bytes.
    pub fn aob(text: &str) -> Result<Needle, String> {
        let mut out = Vec::new();
        for token in text.split_whitespace() {
            if token == "?" {
                out.push(None);
                continue;
            }
            let units = token.as_bytes();
            if units.len() % 2 != 0 {
                return Err(format!("{token}: bytes are hex pairs, a wildcard ??"));
            }
            for pair in units.chunks_exact(2) {
                let pair = std::str::from_utf8(pair).unwrap_or("");
                if pair == "??" {
                    out.push(None);
                } else {
                    let b = u8::from_str_radix(pair, 16)
                        .map_err(|_| format!("{pair} in {token} is not a hex byte"))?;
                    out.push(Some(b));
                }
            }
        }
        if out.len() > PATTERN_MAX || out.iter().all(Option::is_none) {
            return Err(format!(
                "a byte pattern holds 1 to {PATTERN_MAX} bytes, at least one not a wildcard"
            ));
        }
        Ok(Needle::Bytes(out))
    }

    /// The bytes a value takes.
    #[must_use]
    pub fn width(&self) -> usize {
        match self {
            Needle::Int { kind, .. } | Needle::Float { kind, .. } => kind.size(8),
            Needle::Text { bytes, .. } => bytes.len(),
            Needle::Bytes(p) => p.len(),
        }
    }

    /// The alignment a value's address has: a number's width, else one.
    fn align(&self) -> usize {
        match self {
            Needle::Int { .. } | Needle::Float { .. } => self.width(),
            Needle::Text { .. } | Needle::Bytes(_) => 1,
        }
    }

    /// A fixed byte and its place in the needle, for a needle matched at
    /// any address: where a search looks first.
    fn anchor(&self) -> Option<(usize, u8)> {
        match self {
            Needle::Int { .. } | Needle::Float { .. } => None,
            Needle::Text { bytes, .. } => bytes.first().map(|b| (0, *b)),
            Needle::Bytes(p) => p.iter().enumerate().find_map(|(i, b)| b.map(|b| (i, b))),
        }
    }

    /// Whether a value's bytes match.
    ///
    /// # Arguments
    ///
    /// * `b` - Exactly [`Needle::width`] bytes.
    #[must_use]
    pub fn matches(&self, b: &[u8]) -> bool {
        match self {
            Needle::Int { bits, .. } => bits.to_le_bytes().get(..b.len()) == Some(b),
            Needle::Float {
                kind,
                value,
                tolerance,
            } => float_of(*kind, b).is_some_and(|v| (v - value).abs() <= *tolerance),
            Needle::Text { bytes, .. } => b == bytes.as_slice(),
            Needle::Bytes(p) => p
                .iter()
                .zip(b)
                .all(|(want, got)| want.is_none_or(|w| w == *got)),
        }
    }

    /// The kind values read as, for a next scan's value and the rows;
    /// `None` for a byte pattern.
    #[must_use]
    pub fn kind(&self) -> Option<Kind> {
        match self {
            Needle::Int { kind, .. } | Needle::Float { kind, .. } | Needle::Text { kind, .. } => {
                Some(*kind)
            }
            Needle::Bytes(_) => None,
        }
    }

    /// Spells the needle for a header: `u32 100`, `f32 100 +- 0.5`,
    /// `string "hp"`, `bytes 48 8b ?? 05`.
    #[must_use]
    pub fn describe(&self) -> String {
        match self {
            Needle::Int { kind, bits } => format!(
                "{} {}",
                kind_name(*kind),
                value_text(*kind, &bits.to_le_bytes()[..kind.size(8)])
            ),
            Needle::Float {
                kind,
                value,
                tolerance,
            } => format!("{} {value:?} +- {tolerance:?}", kind_name(*kind)),
            Needle::Text { kind, bytes } => {
                format!("{} {}", kind_name(*kind), value_text(*kind, bytes))
            }
            Needle::Bytes(p) => format!(
                "bytes {}",
                p.iter()
                    .map(|b| b.map_or_else(|| "??".to_owned(), |b| format!("{b:02x}")))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

/// Parses a float needle, with the tolerance its digits imply when none is
/// given.
///
/// # Arguments
///
/// * `kind` - `F32` or `F64`.
/// * `t` - The value, trimmed.
/// * `tolerance` - The tolerance given, if any.
///
/// # Errors
///
/// When the text is not a finite number or the tolerance is negative.
fn float_needle(kind: Kind, t: &str, tolerance: Option<f64>) -> Result<Needle, String> {
    let value = if kind == Kind::F32 {
        t.parse::<f32>().map(f64::from)
    } else {
        t.parse::<f64>()
    }
    .ok()
    .filter(|v| v.is_finite())
    .ok_or_else(|| format!("{t} is not a finite number"))?;
    let tolerance = match tolerance {
        Some(tol) if tol >= 0.0 && tol.is_finite() => tol,
        Some(tol) => return Err(format!("tolerance {tol} must be a number at least 0")),
        None => {
            let mantissa = t.split(['e', 'E']).next().unwrap_or(t);
            let digits = mantissa.split_once('.').map_or(0, |(_, f)| f.len());
            0.5 / 10f64.powi(i32::try_from(digits).unwrap_or(i32::MAX))
        }
    };
    Ok(Needle::Float {
        kind,
        value,
        tolerance,
    })
}

/// A float kind's value from its bytes; `None` for NaN or another kind.
///
/// # Arguments
///
/// * `kind` - `F32` or `F64`.
/// * `b` - The value's bytes.
fn float_of(kind: Kind, b: &[u8]) -> Option<f64> {
    let v = match kind {
        Kind::F32 => f64::from(f32::from_bits(lo32(le_word(b)))),
        Kind::F64 => f64::from_bits(le_word(b)),
        Kind::U8
        | Kind::U16
        | Kind::U32
        | Kind::U64
        | Kind::I8
        | Kind::I16
        | Kind::I32
        | Kind::I64
        | Kind::Ptr
        | Kind::CStr
        | Kind::WStr => return None,
    };
    (!v.is_nan()).then_some(v)
}

/// An integer kind's value from its bytes, signed or not as the kind is.
///
/// # Arguments
///
/// * `kind` - An integer kind.
/// * `b` - The value's bytes.
fn int_of(kind: Kind, b: &[u8]) -> i128 {
    let raw = le_word(b);
    match kind {
        Kind::I8 => i128::from(lo8(raw).cast_signed()),
        Kind::I16 => i128::from(lo16(raw).cast_signed()),
        Kind::I32 => i128::from(lo32(raw).cast_signed()),
        Kind::I64 => i128::from(raw.cast_signed()),
        Kind::U8
        | Kind::U16
        | Kind::U32
        | Kind::U64
        | Kind::F32
        | Kind::F64
        | Kind::Ptr
        | Kind::CStr
        | Kind::WStr => i128::from(raw),
    }
}

/// A kind's name as `live_scan` takes it.
///
/// # Arguments
///
/// * `kind` - The kind.
fn kind_name(kind: Kind) -> &'static str {
    match kind {
        Kind::U8 => "u8",
        Kind::U16 => "u16",
        Kind::U32 => "u32",
        Kind::U64 => "u64",
        Kind::I8 => "i8",
        Kind::I16 => "i16",
        Kind::I32 => "i32",
        Kind::I64 => "i64",
        Kind::F32 => "f32",
        Kind::F64 => "f64",
        Kind::Ptr => "ptr",
        Kind::CStr => "string",
        Kind::WStr => "wstring",
    }
}

/// Renders a value's bytes as its kind reads: an integer in decimal, a
/// float, a string quoted.
///
/// # Arguments
///
/// * `kind` - The kind.
/// * `b` - The value's bytes.
fn value_text(kind: Kind, b: &[u8]) -> String {
    match kind {
        Kind::U8 | Kind::U16 | Kind::U32 | Kind::U64 => le_word(b).to_string(),
        Kind::CStr => format!("{:?}", String::from_utf8_lossy(b)),
        Kind::WStr => {
            let units: Vec<u16> = b
                .chunks_exact(2)
                .map(|p| u16::from_le_bytes([p[0], p[1]]))
                .collect();
            format!("{:?}", String::from_utf16_lossy(&units))
        }
        Kind::I8 | Kind::I16 | Kind::I32 | Kind::I64 | Kind::F32 | Kind::F64 | Kind::Ptr => {
            scalar_text(kind, le_word(b)).0
        }
    }
}

/// Where a scan reads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Scope {
    /// Every readable region.
    All,
    /// The writable regions no module maps: heaps, stacks, mappings.
    Heap,
    /// The regions of the module with this file name (case ignored; the
    /// extension may be left off).
    Module(String),
}

/// The address ranges a scope covers, in address order.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `scope` - Where to read.
///
/// # Errors
///
/// When no module has the name a module scope gives; the message lists
/// some that do exist.
pub fn ranges(mem: &dyn Memory, scope: &Scope) -> Result<Vec<(u64, u64)>, String> {
    let regions = mem.regions();
    let span = |r: &super::Region| (r.base, r.base.saturating_add(r.size));
    Ok(match scope {
        Scope::All => regions.iter().map(span).collect(),
        Scope::Heap => regions
            .iter()
            .filter(|r| r.writable && !r.image)
            .map(span)
            .collect(),
        Scope::Module(name) => {
            let modules = mem.modules();
            let m = module_named(&modules, name)?;
            let end = m.base.saturating_add(m.size);
            regions
                .iter()
                .map(span)
                .filter(|(s, e)| *s < end && *e > m.base)
                .map(|(s, e)| (s.max(m.base), e.min(end)))
                .collect()
        }
    })
}

/// The module with a file name, case ignored and the extension optional.
///
/// # Arguments
///
/// * `modules` - The process's modules.
/// * `name` - The name asked for.
///
/// # Errors
///
/// When none has it; the message lists the first few modules.
pub fn module_named<'m>(modules: &'m [Module], name: &str) -> Result<&'m Module, String> {
    let want = name.trim().to_lowercase();
    modules
        .iter()
        .find(|m| {
            let n = m.name.to_lowercase();
            n == want || n.rsplit_once('.').is_some_and(|(stem, _)| stem == want)
        })
        .ok_or_else(|| {
            let some: Vec<&str> = modules.iter().take(8).map(|m| m.name.as_str()).collect();
            format!(
                "no module is named {name}; the process has {} modules, among them {}",
                modules.len(),
                some.join(", ")
            )
        })
}

/// A result set: the addresses a scan found and their values as last read.
#[derive(Debug, Clone, PartialEq)]
pub struct Found {
    /// What the first scan looked for; its kind reads every later value.
    pub needle: Needle,
    /// The addresses, in address order.
    pub hits: Vec<u64>,
    /// Each hit's value as last read, [`Needle::width`] bytes each, in the
    /// order of `hits`.
    pub values: Vec<u8>,
    /// What the first scan read.
    pub swept: Swept,
}

impl Found {
    /// The most hits a set of this needle keeps.
    fn cap(&self) -> usize {
        STORE_HITS.min(STORE_BYTES / self.needle.width().max(1))
    }

    /// The value of the hit at an index.
    ///
    /// # Arguments
    ///
    /// * `i` - An index into `hits`.
    fn value(&self, i: usize) -> &[u8] {
        let w = self.needle.width();
        self.values
            .get(i.saturating_mul(w)..i.saturating_add(1).saturating_mul(w))
            .unwrap_or(&[])
    }
}

/// Scans ranges of a process for a needle.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `needle` - What to look for.
/// * `ranges` - Where, from [`ranges`].
///
/// # Returns
///
/// The set, at most [`STORE_HITS`] hits (fewer for a wide needle, so it
/// keeps at most 16 MiB of values); `swept.stop` says when it stopped
/// short.
#[must_use]
pub fn scan(mem: &dyn Memory, needle: Needle, ranges: &[(u64, u64)]) -> Found {
    let mut found = Found {
        needle,
        hits: Vec::new(),
        values: Vec::new(),
        swept: Swept::default(),
    };
    let cap = found.cap();
    let w = found.needle.width();
    let align = found.needle.align();
    let anchor = found.needle.anchor();
    let needle = found.needle.clone();
    let (mut hits, mut values) = (Vec::new(), Vec::new());
    let swept = sweep(mem, ranges, w.saturating_sub(1), |at, bytes, own| {
        let mut take = |off: usize| {
            let Some(b) = bytes.get(off..off.saturating_add(w)) else {
                return ControlFlow::Continue(());
            };
            if needle.matches(b) {
                hits.push(at.saturating_add(from_usize(off)));
                values.extend_from_slice(b);
                if hits.len() >= cap {
                    return ControlFlow::Break(());
                }
            }
            ControlFlow::Continue(())
        };
        match anchor {
            Some((i, b)) => {
                let mut from = 0usize;
                while from < own {
                    let lo = from.saturating_add(i);
                    let hi = own.saturating_add(i).min(bytes.len());
                    let Some(p) = bytes
                        .get(lo..hi)
                        .and_then(|s| s.iter().position(|x| *x == b))
                    else {
                        break;
                    };
                    let start = from + p;
                    take(start)?;
                    from = start + 1;
                }
            }
            None => {
                let skew = usize::try_from(at % from_usize(align)).unwrap_or(0);
                let first = (align - skew) % align;
                let end = own.saturating_add(align - 1).min(bytes.len());
                let starts_here = bytes.get(first..end).unwrap_or_default();
                for (k, value) in starts_here.chunks_exact(align).enumerate() {
                    if needle.matches(value) {
                        take(first + k * align)?;
                    }
                }
            }
        }
        ControlFlow::Continue(())
    });
    found.hits = hits;
    found.values = values;
    found.swept = swept;
    found
}

/// How a next scan keeps a hit, comparing its value now with its value at
/// the last scan.
#[derive(Debug, Clone, PartialEq)]
pub enum Compare {
    /// The bytes differ.
    Changed,
    /// The bytes are the same.
    Unchanged,
    /// The number is larger.
    Increased,
    /// The number is smaller.
    Decreased,
    /// The value now matches this needle, of the set's kind.
    Equal(Needle),
}

/// What a next scan kept.
#[derive(Debug, Clone, PartialEq)]
pub struct Narrowed {
    /// The set with only the hits kept, their values as read now.
    pub found: Found,
    /// Hits that did not read now, dropped.
    pub unreadable: usize,
}

/// Reads a set's hits again and keeps those the comparison holds for.
///
/// Neighbouring hits are read in one piece. The set's first-scan counts
/// stay as they were.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `found` - The set.
/// * `compare` - Which hits to keep.
///
/// # Errors
///
/// When the comparison needs numbers and the set holds bytes or text, the
/// value compared with has another width, or the request's deadline passes
/// (the set is then left as it was).
pub fn narrow(mem: &dyn Memory, found: &Found, compare: &Compare) -> Result<Narrowed, String> {
    let w = found.needle.width();
    let numeric = matches!(found.needle, Needle::Int { .. } | Needle::Float { .. });
    match compare {
        Compare::Increased | Compare::Decreased if !numeric => {
            return Err(format!(
                "increased and decreased compare numbers; this set holds {}",
                found.needle.describe()
            ));
        }
        Compare::Equal(n) if n.width() != w => {
            return Err(format!(
                "the value is {} bytes and this set's are {w}",
                n.width()
            ));
        }
        _ => {}
    }
    let mut out = Found {
        needle: found.needle.clone(),
        hits: Vec::new(),
        values: Vec::new(),
        swept: found.swept,
    };
    let mut unreadable = 0usize;
    let span_end = |h: u64| h.saturating_add(from_usize(w));
    let hits = &found.hits;
    let mut i = 0usize;
    while i < hits.len() {
        if Cancel::raised() {
            return Err(format!(
                "the request's deadline passed after re-reading {i} of {} hits; the set is kept as it was",
                hits.len()
            ));
        }
        let start = hits[i];
        let mut j = i + 1;
        while j < hits.len()
            && hits[j].saturating_sub(hits[j - 1]) <= GAP
            && span_end(hits[j]).saturating_sub(start) <= from_usize(CHUNK)
        {
            j += 1;
        }
        let len = usize::try_from(span_end(hits[j - 1]) - start).unwrap_or(CHUNK);
        let bytes = mem.read(start, len).unwrap_or_default();
        for (k, &hit) in hits.iter().enumerate().take(j).skip(i) {
            let off = usize::try_from(hit - start).unwrap_or(usize::MAX);
            let Some(now) = bytes.get(off..off.saturating_add(w)) else {
                unreadable += 1;
                continue;
            };
            if keeps(&found.needle, compare, found.value(k), now) {
                out.hits.push(hit);
                out.values.extend_from_slice(now);
            }
        }
        i = j;
    }
    Ok(Narrowed {
        found: out,
        unreadable,
    })
}

/// Whether a comparison holds between a value then and now.
///
/// # Arguments
///
/// * `needle` - The set's needle, whose kind reads the numbers.
/// * `compare` - The comparison.
/// * `was` - The bytes at the last scan.
/// * `now` - The bytes now.
fn keeps(needle: &Needle, compare: &Compare, was: &[u8], now: &[u8]) -> bool {
    let order = || match needle {
        Needle::Int { kind, .. } => Some(int_of(*kind, now).cmp(&int_of(*kind, was))),
        Needle::Float { kind, .. } => float_of(*kind, now)?.partial_cmp(&float_of(*kind, was)?),
        Needle::Text { .. } | Needle::Bytes(_) => None,
    };
    match compare {
        Compare::Changed => was != now,
        Compare::Unchanged => was == now,
        Compare::Increased => order() == Some(Ordering::Greater),
        Compare::Decreased => order() == Some(Ordering::Less),
        Compare::Equal(n) => n.matches(now),
    }
}

/// Renders a page of a set: one row per hit with its value and the module
/// it is in.
///
/// # Arguments
///
/// * `found` - The set.
/// * `title` - What the header calls the set (its name and how it came).
/// * `notes` - Lines put after the header (what was read, what was kept).
/// * `modules` - The process's modules, to place each hit.
/// * `offset` - Hits to skip first.
/// * `limit` - Most rows.
/// * `count_only` - The header alone.
///
/// # Returns
///
/// A `# showing N of M` header (`at least M` when the scan stopped short),
/// then `address value where` rows.
#[must_use]
pub fn found_page(
    found: &Found,
    title: &str,
    notes: &str,
    modules: &[Module],
    offset: usize,
    limit: usize,
    count_only: bool,
) -> String {
    let total = match found.swept.stop {
        Some(_) => format!("at least {}", found.hits.len()),
        None => found.hits.len().to_string(),
    };
    if count_only {
        return format!("# {total} hits {title}\n{notes}");
    }
    let rows: Vec<usize> = (0..found.hits.len()).skip(offset).take(limit).collect();
    let mut out = format!("# showing {} of {total} hits {title}\n{notes}", rows.len());
    out.push_str("# address value where\n");
    for i in rows {
        let at = found.hits[i];
        let value = match found.needle.kind() {
            Some(kind) => value_text(kind, found.value(i)),
            None => found
                .value(i)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<Vec<_>>()
                .join(" "),
        };
        let place = modules
            .iter()
            .find(|m| at >= m.base && at - m.base < m.size)
            .map_or_else(
                || "-".to_owned(),
                |m| format!("{}+{:#x}", m.name, at - m.base),
            );
        let _ = writeln!(out, "{at:#x} {value} {place}");
    }
    out
}

/// Says why a sweep stopped short, for a line after a header; empty when
/// it did not.
///
/// # Arguments
///
/// * `stop` - The sweep's stop.
/// * `cap` - What a full set holds, for the message.
#[must_use]
pub fn stop_line(stop: Option<Stop>, cap: &str) -> String {
    match stop {
        None => String::new(),
        Some(Stop::Full) => {
            format!(
                "# stopped: full at {cap}; what lies past it is not kept, so narrow the search\n"
            )
        }
        Some(Stop::Budget) => format!(
            "# stopped: read {} GiB, the most one search reads; narrow it\n",
            SCAN_MAX >> 30
        ),
        Some(Stop::Deadline) => {
            "# stopped: the request's deadline passed; the answer holds what was found before it\n"
                .to_owned()
        }
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
pub(crate) mod tests {
    use std::cell::RefCell;

    use super::*;
    use crate::live::Region;

    /// A process of buffers at addresses, each a region, with modules.
    pub(crate) struct Pages {
        /// `(base, bytes, writable, image)` per region, in address order.
        pub(crate) regions: Vec<(u64, RefCell<Vec<u8>>, bool, bool)>,
        /// The modules it says are loaded.
        pub(crate) modules: Vec<Module>,
    }

    impl Pages {
        /// The region holding an address, with the address's offset in it.
        fn at(&self, va: u64) -> Option<(&RefCell<Vec<u8>>, usize)> {
            self.regions.iter().find_map(|(base, data, ..)| {
                let off = usize::try_from(va.checked_sub(*base)?).ok()?;
                (off < data.borrow().len()).then_some((data, off))
            })
        }

        /// Writes bytes at an address inside a region.
        pub(crate) fn put(&self, va: u64, bytes: &[u8]) {
            let (data, off) = self.at(va).expect("inside a region");
            data.borrow_mut()[off..off + bytes.len()].copy_from_slice(bytes);
        }
    }

    impl Memory for Pages {
        fn read(&self, va: u64, len: usize) -> Option<Vec<u8>> {
            let (data, off) = self.at(va)?;
            let data = data.borrow();
            Some(data[off..off.saturating_add(len).min(data.len())].to_vec())
        }

        fn regions(&self) -> Vec<Region> {
            self.regions
                .iter()
                .map(|(base, data, writable, image)| Region {
                    base: *base,
                    size: from_usize(data.borrow().len()),
                    writable: *writable,
                    executable: false,
                    image: *image,
                })
                .collect()
        }

        fn modules(&self) -> Vec<Module> {
            self.modules.clone()
        }
    }

    /// A heap at `0x10000` of `len` zero bytes and an image `game.exe` at
    /// `0x400000` of one page.
    pub(crate) fn process(len: usize) -> Pages {
        Pages {
            regions: vec![
                (0x10000, RefCell::new(vec![0; len]), true, false),
                (0x40_0000, RefCell::new(vec![0; 0x1000]), true, true),
            ],
            modules: vec![Module {
                name: "game.exe".to_owned(),
                path: r"C:\game\game.exe".to_owned(),
                base: 0x40_0000,
                size: 0x1000,
            }],
        }
    }

    /// Scans every region of a process for a needle.
    fn scan_all(mem: &Pages, needle: Needle) -> Found {
        let all = ranges(mem, &Scope::All).expect("all regions");
        scan(mem, needle, &all)
    }

    /// A number is found at addresses aligned to its width only, a signed
    /// one by its two's complement, a float within the tolerance its digits
    /// imply, and a value is refused when it does not fit its kind.
    #[test]
    fn numbers_are_found_aligned_and_in_tolerance() {
        let mem = process(0x2000);
        mem.put(0x10010, &100u32.to_le_bytes());
        mem.put(0x10021, &100u32.to_le_bytes());
        mem.put(0x40_0100, &100u32.to_le_bytes());
        let found = scan_all(&mem, Needle::parse(Kind::U32, "100", None).expect("u32"));
        assert_eq!(found.hits, vec![0x10010, 0x40_0100]);
        assert_eq!(found.swept.bytes, 0x3000);
        mem.put(0x10040, &(-7i16).to_le_bytes());
        let found = scan_all(&mem, Needle::parse(Kind::I16, "-7", None).expect("i16"));
        assert_eq!(found.hits, vec![0x10040]);
        mem.put(0x10080, &99.7f32.to_le_bytes());
        let found = scan_all(&mem, Needle::parse(Kind::F32, "100", None).expect("f32"));
        assert_eq!(found.hits, vec![0x10080]);
        let exact = Needle::parse(Kind::F32, "100.0", None).expect("f32");
        assert!(scan_all(&mem, exact).hits.is_empty(), "100.0 is +- 0.05");
        for (kind, text) in [(Kind::U8, "256"), (Kind::I8, "-129"), (Kind::U16, "-1")] {
            assert!(Needle::parse(kind, text, None).is_err(), "{text}");
        }
        assert!(Needle::parse(Kind::U32, "1", Some(0.5)).is_err());
        assert!(Needle::parse(Kind::Ptr, "1", None).is_err());
    }

    /// A string and a byte pattern match at any address, wildcards match
    /// anything, and a value that starts in one piece of the sweep and
    /// ends in the next is found once.
    #[test]
    fn text_and_patterns_match_anywhere_and_across_pieces() {
        let mem = process(CHUNK + 0x1000);
        mem.put(0x10003, b"Hero");
        let wide: Vec<u8> = "Hero".encode_utf16().flat_map(u16::to_le_bytes).collect();
        mem.put(0x10101, &wide);
        let edge = 0x10000 + from_usize(CHUNK) - 2;
        mem.put(edge, &[0x48, 0x8b, 0x05, 0x11]);
        let text = scan_all(&mem, Needle::parse(Kind::CStr, "Hero", None).expect("text"));
        assert_eq!(text.hits, vec![0x10003]);
        let wtext = scan_all(&mem, Needle::parse(Kind::WStr, "Hero", None).expect("wide"));
        assert_eq!(wtext.hits, vec![0x10101]);
        let aob = scan_all(&mem, Needle::aob("48 8b ?? 11").expect("aob"));
        assert_eq!(aob.hits, vec![edge]);
        let packed = scan_all(&mem, Needle::aob("??8B05").expect("aob"));
        assert_eq!(packed.hits, vec![edge]);
        assert!(Needle::aob("?? ??").is_err());
        assert!(Needle::aob("4").is_err());
    }

    /// A module scope reads only that module, the heap scope only the
    /// writable regions no module maps, and an unknown module is named.
    #[test]
    fn a_scope_limits_the_regions_read() {
        let mem = process(0x1000);
        assert_eq!(
            ranges(&mem, &Scope::Module("GAME".to_owned())).expect("by stem"),
            vec![(0x40_0000, 0x40_1000)]
        );
        assert_eq!(
            ranges(&mem, &Scope::Heap).expect("heap"),
            vec![(0x10000, 0x11000)]
        );
        let none = ranges(&mem, &Scope::Module("x.dll".to_owned())).expect_err("unknown");
        assert!(none.contains("among them game.exe"), "{none}");
    }

    /// A next scan keeps the hits whose value changed, stayed, rose, fell,
    /// or equals a value, reading each again, and refuses a comparison the
    /// set's kind cannot make.
    #[test]
    fn a_next_scan_narrows_by_how_the_value_moved() {
        let mem = process(0x1000);
        for at in [0x10000u64, 0x10010, 0x10020, 0x10030] {
            mem.put(at, &50i32.to_le_bytes());
        }
        let found = scan_all(&mem, Needle::parse(Kind::I32, "50", None).expect("i32"));
        assert_eq!(found.hits.len(), 4);
        mem.put(0x10010, &49i32.to_le_bytes());
        mem.put(0x10020, &(-3i32).to_le_bytes());
        mem.put(0x10030, &60i32.to_le_bytes());
        let kept = |c: Compare| narrow(&mem, &found, &c).expect("narrowed").found.hits;
        assert_eq!(kept(Compare::Unchanged), vec![0x10000]);
        assert_eq!(kept(Compare::Changed), vec![0x10010, 0x10020, 0x10030]);
        assert_eq!(kept(Compare::Decreased), vec![0x10010, 0x10020]);
        assert_eq!(kept(Compare::Increased), vec![0x10030]);
        let equal = Needle::parse(Kind::I32, "-3", None).expect("i32");
        assert_eq!(kept(Compare::Equal(equal)), vec![0x10020]);
        let page = found_page(&found, "in \"hp\"", "", &mem.modules, 1, 2, false);
        assert_eq!(
            page,
            "# showing 2 of 4 hits in \"hp\"\n# address value where\n0x10010 50 -\n0x10020 50 -\n"
        );
        let text = scan_all(&mem, Needle::aob("32 00").expect("aob"));
        assert!(narrow(&mem, &text, &Compare::Increased).is_err());
    }
}
