//! Go's function table: the `pclntab` every Go binary carries, stripped or
//! not.
//!
//! The Go runtime walks its own stacks, so the linker keeps a table of
//! every function's entry and name in the image whatever `strip` removes:
//! a stripped Go binary still names `main.main` and
//! `net/http.(*Client).Do`. The table is found by its section
//! (`.gopclntab` in an ELF, `__gopclntab` in a Mach-O) or, where no
//! section names it (a PE's `.rdata`, an ELF stripped of its section
//! table), by the magic its header starts with and a validation of the
//! whole table: the header's fields, every entry in address order inside
//! an executable section, every function record agreeing with its entry,
//! and every name readable. A table that fails any of it is refused rather
//! than half read. The names join the program's symbols the way the
//! DWARF names do, and [`Pclntab`] stays on the program as their
//! provenance and as the mark of which functions are Go: from Go 1.17 on
//! (`pclntab` 1.18 and later here) those take their arguments in
//! registers, which the decompiler reads them by. From Go 1.16 on the
//! same header also names the file and line runs each function's record
//! points at, so a listed function says the source it starts at
//! ([`Pclntab::source_of`]).

use crate::num::{from_usize, saturating_usize, u32_le, word_le};
use crate::program::{Section, Symbol, SymbolKind};

/// Most functions read from one table, whatever its header claims.
const FUNCS_MAX: usize = 1 << 20;

/// Longest function name read; a longer run is a corrupt table.
const NAME_MAX: usize = 4096;

/// Most bytes searched for the header's magic when no section names the
/// table.
const SCAN_MAX: u64 = 1 << 30;

/// The table layout, named for the first Go release that wrote it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GoVersion {
    /// Go 1.2 to 1.15: magic `0xfffffffb`, absolute entries.
    V1_2,
    /// Go 1.16 and 1.17: magic `0xfffffffa`, a name table of its own.
    V1_16,
    /// Go 1.18 and 1.19: magic `0xfffffff0`, entries relative to the text.
    V1_18,
    /// Go 1.20 and later: magic `0xfffffff1`.
    V1_20,
}

impl GoVersion {
    /// Reads the layout a header's magic names.
    ///
    /// # Arguments
    ///
    /// * `magic` - The header's first word.
    fn of(magic: u32) -> Option<Self> {
        match magic {
            0xffff_fffb => Some(Self::V1_2),
            0xffff_fffa => Some(Self::V1_16),
            0xffff_fff0 => Some(Self::V1_18),
            0xffff_fff1 => Some(Self::V1_20),
            _ => None,
        }
    }

    /// The Go releases that write this layout.
    #[must_use]
    pub fn releases(self) -> &'static str {
        match self {
            Self::V1_2 => "Go 1.2-1.15",
            Self::V1_16 => "Go 1.16-1.17",
            Self::V1_18 => "Go 1.18-1.19",
            Self::V1_20 => "Go 1.20+",
        }
    }

    /// Whether every release writing this layout passes Go arguments in
    /// registers (`ABIInternal`, Go 1.17 on amd64): 1.16's layout is
    /// written by 1.16 too, which passed them on the stack.
    #[must_use]
    pub fn register_abi(self) -> bool {
        match self {
            Self::V1_2 | Self::V1_16 => false,
            Self::V1_18 | Self::V1_20 => true,
        }
    }
}

/// The Go function table a program carries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pclntab {
    /// The layout, which says which Go releases wrote it.
    pub version: GoVersion,
    /// The header's address.
    pub at: u64,
    /// Every function's entry, sorted and unique.
    pub entries: Vec<u64>,
    /// The file and line sub-tables a 1.16-or-later header named;
    /// `None` for the 1.2 layout, which carries none.
    pub(crate) lines: Option<Lines>,
}

impl Pclntab {
    /// Whether the table lists a function starting at `entry`.
    ///
    /// # Arguments
    ///
    /// * `entry` - A function's entry.
    #[must_use]
    pub fn lists(&self, entry: u64) -> bool {
        self.entries.binary_search(&entry).is_ok()
    }

    /// Reads the file and line the table states a listed function starts
    /// at.
    ///
    /// A 1.16-or-later header names the sub-tables the runtime's
    /// traceback walks: each `_func` record points at two delta-encoded
    /// runs, one naming the file its code came from and one the line, and
    /// the first run of each is the function's start. Earlier layouts
    /// carry no file table, and code the compiler wrote no runs for has
    /// none, so both answer `None`.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The bytes of the section the table was read from.
    /// * `entry` - A function's entry.
    ///
    /// # Returns
    ///
    /// The `(file, line)` the runs at the entry state, or `None` when
    /// the table does not list `entry`, predates the file table, or its
    /// runs do not decode.
    #[must_use]
    pub fn source_of(&self, bytes: &[u8], entry: u64) -> Option<(String, u32)> {
        let l = self.lines?;
        let v = View {
            bytes,
            word: l.word,
        };
        let i = self.entries.binary_search(&entry).ok()?;
        let record_off = match self.version {
            GoVersion::V1_2 => return None,
            GoVersion::V1_16 => {
                let row = l.functab.checked_add(i.checked_mul(2 * l.word)?)?;
                v.word(row.checked_add(l.word)?)?
            }
            GoVersion::V1_18 | GoVersion::V1_20 => {
                let row = l.functab.checked_add(i.checked_mul(8)?)?;
                u64::from(v.u32(row.checked_add(4)?)?)
            }
        };
        let record = l.functab.checked_add(saturating_usize(record_off))?;
        let (fileno, line) = (
            pcvalue(
                v,
                l,
                saturating_usize(u64::from(v.u32(record.checked_add(l.pcfile_at)?)?)),
            )?,
            pcvalue(
                v,
                l,
                saturating_usize(u64::from(v.u32(record.checked_add(l.pcline_at)?)?)),
            )?,
        );
        if fileno < 0 || line < 0 {
            return None;
        }
        let cu = v.u32(record.checked_add(l.cu_at)?)?;
        if cu == u32::MAX {
            return None;
        }
        let slot = usize::try_from(cu)
            .ok()?
            .checked_add(usize::try_from(fileno).ok()?)?;
        let at = l.cutab.checked_add(slot.checked_mul(4)?)?;
        if l.filetab < at.checked_add(4)? {
            return None;
        }
        let file_off = v.u32(at)?;
        if file_off == u32::MAX {
            return None;
        }
        let path = v.name(
            l.filetab
                .checked_add(saturating_usize(u64::from(file_off)))?,
        )?;
        Some((path.to_owned(), u32::try_from(line).ok()?))
    }

    /// Renders the table as a summary line.
    pub(crate) fn render(&self) -> String {
        format!(
            "go:      pclntab of {} at {:#x}: {} functions named\n",
            self.version.releases(),
            self.at,
            self.entries.len()
        )
    }
}

/// The file and line sub-tables a 1.16-or-later header names, as offsets
/// into the section carrying the table.
///
/// The linker emits them in the order the header lists them - the
/// per-compilation-unit file index table, the name blob, the pc-value
/// runs - so each region ends where the next begins, and a table whose
/// offsets disagree with that order is refused whole.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Lines {
    /// The pc quantum the pc-value runs' deltas count in, in bytes.
    min_lc: u32,
    /// The pointer width in bytes, 4 or 8, which the 1.16 layout's
    /// function table rows and records are laid out by.
    word: usize,
    /// The function table's and the records' offset: rows of (entry,
    /// record offset), then the records themselves.
    functab: usize,
    /// The file index table's offset, in `u32` slots of a compilation
    /// unit's file numbers into the name blob.
    cutab: usize,
    /// The file name blob's offset, of NUL-separated paths.
    filetab: usize,
    /// The pc-value runs' offset, which the records' `pcfile` and
    /// `pcline` offsets count from.
    pctab: usize,
    /// The offset of the record's `pcfile` run within it.
    pcfile_at: usize,
    /// The offset of the record's `pcline` run within it.
    pcline_at: usize,
    /// The offset of the record's compilation-unit slot within it.
    cu_at: usize,
}

impl Lines {
    /// Records the sub-tables a header names, checked against the order
    /// the linker emits them in.
    ///
    /// # Arguments
    ///
    /// * `word` - The pointer width in bytes, 4 or 8.
    /// * `min_lc` - The pc quantum from the header, in bytes.
    /// * `cutab` - The file index table's offset in the section.
    /// * `filetab` - The file name blob's offset in it.
    /// * `pctab` - The pc-value runs' offset in it.
    /// * `functab` - The function table's offset in it.
    /// * `record` - The `(pcfile, pcln, cuOffset)` offsets within a
    ///   record.
    ///
    /// # Returns
    ///
    /// The sub-tables, or `None` when the regions lie out of emission
    /// order, which no Go linker writes.
    fn new(
        word: usize,
        min_lc: u8,
        cutab: usize,
        filetab: usize,
        pctab: usize,
        functab: usize,
        record: (usize, usize, usize),
    ) -> Option<Self> {
        (cutab <= filetab && filetab <= pctab && pctab <= functab).then_some(Self {
            min_lc: u32::from(min_lc),
            word,
            functab,
            cutab,
            filetab,
            pctab,
            pcfile_at: record.0,
            pcline_at: record.1,
            cu_at: record.2,
        })
    }
}

/// Decodes the value a pc-value run states at a function's entry.
///
/// A run ([`Lines::pctab`]) is a sequence of pairs, a zigzag varint of
/// how the value changes and a varint of how far the pc then moves in
/// [`Lines::min_lc`]-byte steps, the new value holding from that pc on,
/// ended by a zero value delta. The entry's value is the first pair's.
///
/// # Arguments
///
/// * `v` - The section's bytes.
/// * `l` - The sub-tables the header named.
/// * `off` - The run's offset from [`Lines::pctab`], 0 meaning none.
///
/// # Returns
///
/// The value in effect at the entry, or `None` when the run is absent,
/// runs past the pc-value region, or never covers the entry.
fn pcvalue(v: View<'_>, l: Lines, off: usize) -> Option<i64> {
    if off == 0 {
        return None;
    }
    let mut p = l.pctab.checked_add(off)?;
    let (mut pc, mut val) = (0u64, -1i64);
    loop {
        let (uv, after_uv) = varint(v.bytes, l.functab, p)?;
        if uv == 0 && pc != 0 {
            return None;
        }
        let (delta, after) = varint(v.bytes, l.functab, after_uv)?;
        val += i64::from(uv >> 1) ^ -i64::from(uv & 1);
        pc = pc.checked_add(u64::from(delta).checked_mul(u64::from(l.min_lc))?)?;
        p = after;
        if pc > 0 {
            return Some(val);
        }
    }
}

/// Reads a little-endian base-128 varint from a bounded region.
///
/// # Arguments
///
/// * `bytes` - The bytes the runs live in.
/// * `end` - The region's end, an offset into `bytes`.
/// * `at` - The varint's first byte's offset.
///
/// # Returns
///
/// The value and the offset of the byte after it, or `None` when the
/// region ends first or five bytes (all a `u32` holds) continue.
fn varint(bytes: &[u8], end: usize, at: usize) -> Option<(u32, usize)> {
    let mut v = 0u32;
    for k in 0..5 {
        let i = at.checked_add(k)?;
        if i >= end {
            return None;
        }
        let b = bytes[i];
        v |= u32::from(b & 0x7f) << (k * 7);
        if b < 0x80 {
            return Some((v, i + 1));
        }
    }
    None
}

/// A view of one section's bytes, read by offset from its start.
#[derive(Debug, Clone, Copy)]
struct View<'a> {
    /// The bytes, from the section's start.
    bytes: &'a [u8],
    /// The pointer width in bytes, 4 or 8.
    word: usize,
}

impl<'a> View<'a> {
    /// Reads a little-endian `u32`.
    ///
    /// # Arguments
    ///
    /// * `at` - Offset into the view.
    fn u32(&self, at: usize) -> Option<u32> {
        u32_le(self.bytes, at)
    }

    /// Reads a little-endian pointer-width word.
    ///
    /// # Arguments
    ///
    /// * `at` - Offset into the view.
    fn word(&self, at: usize) -> Option<u64> {
        word_le(self.bytes, at, self.word)
    }

    /// Reads a pointer-width word as an offset into the view.
    ///
    /// # Arguments
    ///
    /// * `at` - Offset of the word.
    fn offset(&self, at: usize) -> Option<usize> {
        usize::try_from(self.word(at)?).ok()
    }

    /// Reads a NUL-terminated name: printable ASCII or UTF-8, not empty.
    ///
    /// # Arguments
    ///
    /// * `at` - Offset of its first byte.
    fn name(&self, at: usize) -> Option<&'a str> {
        let rest = self.bytes.get(at..)?;
        let len = rest.iter().take(NAME_MAX).position(|b| *b == 0)?;
        let text = std::str::from_utf8(rest.get(..len)?).ok()?;
        (!text.is_empty() && !text.chars().any(char::is_control)).then_some(text)
    }
}

/// What [`parse`] reads from one table.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Parsed<'a> {
    /// The layout, which says which Go releases wrote it.
    version: GoVersion,
    /// The file and line sub-tables the header named, `None` for the
    /// 1.2 layout, which carries none.
    lines: Option<Lines>,
    /// Every function's `(entry, name)`, in table order.
    funcs: Vec<(u64, &'a str)>,
}

/// Reads a table whose header starts at `head` in a view.
///
/// # Arguments
///
/// * `v` - The section's bytes.
/// * `head` - The header's offset in them.
/// * `code` - Whether an address is in an executable section.
///
/// # Returns
///
/// The layout, the file and line sub-tables it names and every
/// function's `(entry, name)` in table order, or `None` when any field,
/// entry or name does not hold.
fn parse<'a>(v: View<'a>, head: usize, code: &dyn Fn(u64) -> bool) -> Option<Parsed<'a>> {
    let version = GoVersion::of(v.u32(head)?)?;
    let (pad, min_lc, ptr) = (
        v.bytes.get(head.checked_add(4)?..head.checked_add(6)?)?,
        *v.bytes.get(head.checked_add(6)?)?,
        *v.bytes.get(head.checked_add(7)?)?,
    );
    if pad != [0, 0] || !matches!(min_lc, 1 | 2 | 4) || usize::from(ptr) != v.word {
        return None;
    }
    let w = v.word;
    let field = |k: usize| head.checked_add(8)?.checked_add(k.checked_mul(w)?);
    let nfunc = v.offset(field(0)?)?;
    if nfunc == 0 || nfunc > FUNCS_MAX {
        return None;
    }
    let at = |k: usize| head.checked_add(v.offset(field(k)?)?);
    let (text, names, table, records, lines) = match version {
        GoVersion::V1_18 | GoVersion::V1_20 => {
            let functab = at(7)?;
            (
                Some(v.word(field(2)?)?),
                at(3)?,
                functab,
                functab,
                Some(Lines::new(
                    v.word,
                    min_lc,
                    at(4)?,
                    at(5)?,
                    at(6)?,
                    functab,
                    (20, 24, 32),
                )?),
            )
        }
        GoVersion::V1_16 => {
            let functab = at(6)?;
            (
                None,
                at(2)?,
                functab,
                functab,
                Some(Lines::new(
                    v.word,
                    min_lc,
                    at(3)?,
                    at(4)?,
                    at(5)?,
                    functab,
                    (w + 16, w + 20, w + 28),
                )?),
            )
        }
        GoVersion::V1_2 => (None, head, field(1)?, head, None),
    };
    let (stride, half) = if text.is_some() { (8, 4) } else { (2 * w, w) };
    let entry_at = |at: usize| match text {
        Some(t) => t.checked_add(u64::from(v.u32(at)?)),
        None => v.word(at),
    };
    let mut funcs = Vec::with_capacity(nfunc);
    for k in 0..=nfunc {
        let row = table.checked_add(k.checked_mul(stride)?)?;
        let entry = entry_at(row)?;
        if k == nfunc {
            funcs.push((entry, ""));
            break;
        }
        let off = match text {
            Some(_) => saturating_usize(u64::from(v.u32(row.checked_add(4)?)?)),
            None => v.offset(row.checked_add(w)?)?,
        };
        let record = records.checked_add(off)?;
        if entry_at(record)? != entry {
            return None;
        }
        let name_off = saturating_usize(u64::from(v.u32(record.checked_add(half)?)?));
        funcs.push((entry, v.name(names.checked_add(name_off)?)?));
    }
    let end = funcs.pop()?.0;
    let ordered =
        funcs.windows(2).all(|p| p[0].0 < p[1].0) && funcs.last().is_some_and(|last| last.0 <= end);
    (ordered && funcs.iter().all(|(entry, _)| code(*entry))).then_some(Parsed {
        version,
        lines,
        funcs,
    })
}

/// Finds and reads the Go function table of an image.
///
/// A section the toolchain names is read first; the rest are searched for
/// the magic at every four-byte boundary, the first table that validates
/// whole winning, up to [`SCAN_MAX`] bytes.
///
/// # Arguments
///
/// * `sections` - The mapped sections.
/// * `bytes` - Reads a section's bytes as the image holds them.
/// * `word` - The pointer width in bytes, 4 or 8.
///
/// # Returns
///
/// The table and its functions as `(entry, name)` in address order, or
/// `None` when the image carries no table that validates.
pub(crate) fn find<'a>(
    sections: &'a [Section],
    bytes: impl Fn(&'a Section) -> Option<&'a [u8]>,
    word: usize,
) -> Option<(Pclntab, Vec<(u64, &'a str)>)> {
    let spans = crate::program::Spans::of(
        sections
            .iter()
            .filter(|s| s.executable)
            .map(|s| (s.va.0, s.va.0.saturating_add(s.vsize.max(s.file_size)))),
    );
    let code = |va: u64| spans.holds(va);
    let named = |s: &Section| s.name == ".gopclntab" || s.name.ends_with("__gopclntab");
    let read = |s: &'a Section, head: usize| {
        let parsed = parse(
            View {
                bytes: bytes(s)?,
                word,
            },
            head,
            &code,
        )?;
        let table = Pclntab {
            version: parsed.version,
            at: s.va.0.checked_add(from_usize(head))?,
            entries: parsed.funcs.iter().map(|f| f.0).collect(),
            lines: parsed.lines,
        };
        Some((table, parsed.funcs))
    };
    if let Some(found) = sections
        .iter()
        .filter(|s| named(s))
        .find_map(|s| read(s, 0))
    {
        return Some(found);
    }
    let mut budget = SCAN_MAX;
    for s in sections.iter().filter(|s| !named(s)) {
        let Some(data) = bytes(s) else {
            continue;
        };
        for head in (0..data.len().saturating_sub(8)).step_by(4) {
            if budget == 0 {
                return None;
            }
            budget -= 4;
            let Some(magic) = data.get(head..).and_then(<[u8]>::first_chunk::<4>) else {
                break;
            };
            if GoVersion::of(u32::from_le_bytes(*magic)).is_some()
                && let Some(found) = read(s, head)
            {
                return Some(found);
            }
        }
    }
    None
}

/// The symbols a table's names make: each function's name at its entry,
/// where no other symbol already names the address.
///
/// # Arguments
///
/// * `funcs` - The table's `(entry, name)` pairs.
/// * `symbols` - The symbols the file states, which win.
///
/// # Returns
///
/// The new symbols, as local functions, in address order.
pub(crate) fn symbols(funcs: &[(u64, &str)], symbols: &[Symbol]) -> Vec<Symbol> {
    let named: std::collections::BTreeSet<u64> = symbols
        .iter()
        .filter(|s| s.kind != SymbolKind::Data)
        .map(|s| s.addr)
        .collect();
    funcs
        .iter()
        .filter(|(entry, _)| !named.contains(entry))
        .map(|(entry, name)| Symbol {
            name: crate::text::one_line(name),
            addr: *entry,
            kind: SymbolKind::Local,
        })
        .collect()
}
