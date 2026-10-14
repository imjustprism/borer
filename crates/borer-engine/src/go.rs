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
//! registers, which the decompiler reads them by.

use crate::num::{from_usize, saturating_usize};
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
        let b = self.bytes.get(at..at.checked_add(4)?)?;
        Some(u32::from_le_bytes(b.try_into().ok()?))
    }

    /// Reads a little-endian pointer-width word.
    ///
    /// # Arguments
    ///
    /// * `at` - Offset into the view.
    fn word(&self, at: usize) -> Option<u64> {
        let b = self.bytes.get(at..at.checked_add(self.word)?)?;
        let mut le = [0u8; 8];
        le.get_mut(..b.len())?.copy_from_slice(b);
        Some(u64::from_le_bytes(le))
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
/// The layout and every function's `(entry, name)` in table order, or
/// `None` when any field, entry or name does not hold.
fn parse<'a>(
    v: View<'a>,
    head: usize,
    code: &dyn Fn(u64) -> bool,
) -> Option<(GoVersion, Vec<(u64, &'a str)>)> {
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
    // SPEC: Go's runtime/symtab.go `pcHeader`, `functab` and `_func` per
    // release: 1.18 on store each entry and record offset as 32 bits from
    // the header's text start, earlier layouts as absolute words, and 1.2
    // counts its record and name offsets from the header itself.
    let at = |k: usize| head.checked_add(v.offset(field(k)?)?);
    let (text, names, table, records) = match version {
        GoVersion::V1_18 | GoVersion::V1_20 => (Some(v.word(field(2)?)?), at(3)?, at(7)?, at(7)?),
        GoVersion::V1_16 => (None, at(2)?, at(6)?, at(6)?),
        GoVersion::V1_2 => (None, head, field(1)?, head),
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
    (ordered && funcs.iter().all(|(entry, _)| code(*entry))).then_some((version, funcs))
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
    let code = |va: u64| {
        sections
            .iter()
            .any(|s| s.executable && va >= s.va && va - s.va < s.vsize.max(s.file_size))
    };
    let named = |s: &Section| s.name == ".gopclntab" || s.name.ends_with("__gopclntab");
    let read = |s: &'a Section, head: usize| {
        let (version, funcs) = parse(
            View {
                bytes: bytes(s)?,
                word,
            },
            head,
            &code,
        )?;
        let table = Pclntab {
            version,
            at: s.va.checked_add(from_usize(head))?,
            entries: funcs.iter().map(|f| f.0).collect(),
        };
        Some((table, funcs))
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
