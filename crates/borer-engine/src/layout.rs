//! Caller-stated layouts: raw code, a firmware blob or a memory dump,
//! mapped at the addresses the caller names, since no header states them.
//!
//! Both steps are pure: [`Layout::parse`] reads the words a layout is
//! stated in, and [`Layout::program`] checks every number against the
//! file's bytes and builds the [`Program`]. Nothing here reads a file.

use std::path::PathBuf;

use anyhow::{Context as _, anyhow, bail};

use crate::analysis::parse_addr;
use crate::program::{Arch, FileOff, Program, Section, Va};
use crate::text::quoted;

/// Most regions one layout maps.
pub const REGIONS_MAX: usize = 256;

/// One past the last address of 32-bit x86.
const X86_TOP: u64 = 1 << 32;

/// Most regions an error message lists before `... N more`.
const SPANS_SHOWN: usize = 8;

/// The grammar of one region, as an error message teaches it.
const REGION_GRAMMAR: &str = "VA@OFF:LEN[:PERMS], e.g. 0x10000@0:0x2000:rx";

/// The [`crate::headers::Headers::kind`] of a program mapped by a layout.
pub const KIND: &str = "stated layout";

/// One run of file bytes mapped at an address.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Region {
    /// Virtual address of the region's first byte.
    pub va: u64,
    /// File offset of the region's first byte.
    pub off: u64,
    /// Bytes mapped, in the file and in memory alike; at least one.
    pub len: u64,
    /// Mapped readable.
    pub readable: bool,
    /// Mapped writable.
    pub writable: bool,
    /// Mapped executable.
    pub executable: bool,
}

/// Where a headerless file's bytes go, as the caller states it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Layout {
    /// The instruction set the code is written in.
    pub arch: Arch,
    /// Where the whole file maps when no region is stated.
    pub base: u64,
    /// The entry point; `None` takes the first executable byte mapped.
    pub entry: Option<u64>,
    /// The parts of the file mapped instead of the whole of it, in stated
    /// order; empty maps the whole file at [`Layout::base`].
    pub regions: Vec<Region>,
}

/// Reads an architecture as a caller names it.
///
/// # Arguments
///
/// * `word` - `x86`, `x64` (or `x86-64`, `x86_64`, `amd64`) or `arm64`
///   (or `aarch64`), in any case.
///
/// # Returns
///
/// The architecture the word names.
///
/// # Errors
///
/// When the word names none of them; the message lists the accepted ones.
pub fn parse_arch(word: &str) -> anyhow::Result<Arch> {
    match word.trim().to_ascii_lowercase().as_str() {
        "x86" => Ok(Arch::X86),
        "x64" | "x86-64" | "x86_64" | "amd64" => Ok(Arch::X86_64),
        "arm64" | "aarch64" => Ok(Arch::Arm64),
        _ => bail!(
            "arch {}: a stated layout takes x86, x64 or arm64",
            quoted(word)
        ),
    }
}

impl Layout {
    /// Reads a layout from the words a caller states it in.
    ///
    /// Numbers take any form [`parse_addr`] reads. A region is
    /// `VA@OFF:LEN[:PERMS]`: `LEN` bytes of the file from offset `OFF`,
    /// mapped at `VA`, with `PERMS` some of `r`, `w` and `x` (`-` is
    /// skipped, so `r-x` reads as `rx`), `rwx` when left out. Regions are
    /// joined by commas, at most [`REGIONS_MAX`].
    ///
    /// # Arguments
    ///
    /// * `arch` - The instruction set, `None` when none is stated.
    /// * `base` - Where the whole file maps (default `0`).
    /// * `entry` - The entry address (default the first executable byte).
    /// * `regions` - The regions to map instead of the whole file.
    ///
    /// # Returns
    ///
    /// `None` when nothing is stated: the file's own headers are read, as
    /// when no layout exists.
    ///
    /// # Errors
    ///
    /// When `base`, `entry` or `regions` come without `arch`, `arch` is
    /// [`Arch::Unknown`], `base` comes with `regions`, a number does not
    /// parse, or a region is malformed, empty, or one too many.
    pub fn parse(
        arch: Option<Arch>,
        base: Option<&str>,
        entry: Option<&str>,
        regions: Option<&str>,
    ) -> anyhow::Result<Option<Layout>> {
        let Some(arch) = arch else {
            if base.is_some() || entry.is_some() || regions.is_some() {
                bail!(
                    "base, entry and regions state where raw bytes go and need arch (x86, x64 or arm64); without arch the file's own headers are read"
                );
            }
            return Ok(None);
        };
        if arch.isa().is_none() {
            bail!(
                "arch {} names no instruction set; a stated layout takes x86, x64 or arm64",
                arch.name()
            );
        }
        if base.is_some() && regions.is_some() {
            bail!(
                "base and regions both say where the bytes go: base maps the whole file, regions name each part's address; give one"
            );
        }
        Ok(Some(Layout {
            arch,
            base: base.map(|b| number("base", b)).transpose()?.unwrap_or(0),
            entry: entry.map(|e| number("entry", e)).transpose()?,
            regions: regions.map(parse_regions).transpose()?.unwrap_or_default(),
        }))
    }

    /// Maps a file's bytes where the layout says, as a program.
    ///
    /// With no region the whole file is one readable, writable, executable
    /// section `raw` at [`Layout::base`]; otherwise each region is a
    /// section `regionN`, `N` its place in the stated order, and the image
    /// base is the lowest region's address. The entry defaults to the
    /// first executable region's first byte, in stated order. The program
    /// has no symbols, imports or debug information, and its kind is
    /// [`KIND`]; a file whose first bytes name a container (`MZ`, an ELF
    /// magic) carries a warning that its headers went unread.
    ///
    /// # Arguments
    ///
    /// * `path` - Recorded as [`Program::path`]; not opened.
    /// * `bytes` - The whole file, moved into the program.
    ///
    /// # Errors
    ///
    /// When the file is empty, a region runs past the end of the file or
    /// the top of the address space (4 GiB for x86), two regions overlap,
    /// or the entry is in no region or in one that is not executable. Each
    /// message names the region and its numbers.
    pub fn program(&self, path: PathBuf, bytes: Vec<u8>) -> anyhow::Result<Program> {
        let file_len = crate::num::from_usize(bytes.len());
        if file_len == 0 {
            bail!("the file is empty: there is nothing to map");
        }
        let whole = [Region {
            va: self.base,
            off: 0,
            len: file_len,
            readable: true,
            writable: true,
            executable: true,
        }];
        let regions = if self.regions.is_empty() {
            &whole[..]
        } else {
            &self.regions[..]
        };
        let top = if self.arch == Arch::X86 {
            X86_TOP
        } else {
            u64::MAX
        };
        let what = |i: usize| {
            if self.regions.is_empty() {
                "the file".to_owned()
            } else {
                format!("region {i}")
            }
        };
        for (i, r) in regions.iter().enumerate() {
            if r.off.checked_add(r.len).is_none_or(|end| end > file_len) {
                bail!(
                    "{} (offset {:#x}, length {:#x}) runs past the end of the file at {file_len:#x}",
                    what(i),
                    r.off,
                    r.len
                );
            }
            if r.va.checked_add(r.len).is_none_or(|end| end > top) {
                bail!(
                    "{} at {:#x} with {:#x} bytes runs past the top of the {} address space",
                    what(i),
                    r.va,
                    r.len,
                    self.arch.name()
                );
            }
        }
        let mut order: Vec<(usize, &Region)> = regions.iter().enumerate().collect();
        order.sort_unstable_by_key(|&(i, r)| (r.va, i));
        if let Some([(i, a), (j, b)]) = order
            .windows(2)
            .find(|w| matches!(w, [(_, a), (_, b)] if a.va.saturating_add(a.len) > b.va))
        {
            bail!(
                "region {i} ({}) and region {j} ({}) overlap: an address maps one byte",
                span(a),
                span(b)
            );
        }
        let entry = match self.entry {
            Some(e) => {
                let Some((i, home)) = regions
                    .iter()
                    .enumerate()
                    .find(|(_, r)| e >= r.va && e - r.va < r.len)
                else {
                    let more = regions.len().saturating_sub(SPANS_SHOWN);
                    bail!(
                        "entry {e:#x} is in no mapped region; mapped: {}",
                        regions
                            .iter()
                            .take(SPANS_SHOWN)
                            .map(span)
                            .chain((more > 0).then(|| format!("... {more} more")))
                            .collect::<Vec<_>>()
                            .join(" ")
                    );
                };
                if !home.executable {
                    bail!(
                        "entry {e:#x} is in {}, which is not executable; add x to its permissions or name an entry in code",
                        what(i)
                    );
                }
                Some(e)
            }
            None => regions.iter().find(|r| r.executable).map(|r| r.va),
        };
        let sections = regions
            .iter()
            .enumerate()
            .map(|(i, r)| Section {
                name: if self.regions.is_empty() {
                    "raw".to_owned()
                } else {
                    format!("region{i}")
                },
                va: Va(r.va),
                vsize: r.len,
                file_off: FileOff(r.off),
                file_size: r.len,
                readable: r.readable,
                writable: r.writable,
                executable: r.executable,
            })
            .collect();
        let image_base = regions.iter().map(|r| r.va).min().unwrap_or(self.base);
        let magic = crate::program::file::magic_name(&bytes);
        let mut program = Program::raw(bytes, self.arch, image_base, entry, sections);
        program.path = path;
        program.headers.kind = Some(KIND);
        if let Some(kind) = magic {
            program.headers.lenient.push(format!(
                "the file starts like {kind}; mapped as raw bytes at the stated layout with its headers unread (load without arch to parse them)"
            ));
        }
        Ok(program)
    }
}

/// Reads one number of a layout.
///
/// # Arguments
///
/// * `what` - What the number is, for the message.
/// * `text` - The number as stated.
///
/// # Errors
///
/// When the text is no number [`parse_addr`] reads.
fn number(what: &str, text: &str) -> anyhow::Result<u64> {
    parse_addr(text).with_context(|| {
        format!(
            "{what} {}: not a number that fits 64 bits (0x-hex or decimal)",
            quoted(text)
        )
    })
}

/// Reads a comma-joined list of regions.
///
/// # Arguments
///
/// * `text` - The regions as stated.
///
/// # Errors
///
/// When there are more than [`REGIONS_MAX`], or one does not read
/// ([`region`]); the message names the region by its place.
fn parse_regions(text: &str) -> anyhow::Result<Vec<Region>> {
    let count = text.split(',').count();
    if count > REGIONS_MAX {
        bail!("{count} regions stated; at most {REGIONS_MAX}");
    }
    text.split(',')
        .enumerate()
        .map(|(i, piece)| {
            region(piece.trim()).with_context(|| format!("region {i} {}", quoted(piece)))
        })
        .collect()
}

/// Reads one region, `VA@OFF:LEN[:PERMS]`.
///
/// # Arguments
///
/// * `text` - The region as stated, trimmed.
///
/// # Errors
///
/// When the text does not have that shape, a number does not read, the
/// length is zero, or the permissions do not read ([`perms`]).
fn region(text: &str) -> anyhow::Result<Region> {
    let shape = || anyhow!("expected {REGION_GRAMMAR}");
    let (va, rest) = text.split_once('@').ok_or_else(shape)?;
    let mut parts = rest.split(':');
    let (Some(off), Some(len), rights, None) =
        (parts.next(), parts.next(), parts.next(), parts.next())
    else {
        return Err(shape());
    };
    let va = number("address", va)?;
    let off = number("offset", off)?;
    let len = number("length", len)?;
    if len == 0 {
        bail!("length 0: a region maps at least one byte");
    }
    let (readable, writable, executable) = rights.map_or(Ok((true, true, true)), perms)?;
    Ok(Region {
        va,
        off,
        len,
        readable,
        writable,
        executable,
    })
}

/// Reads a region's permissions.
///
/// # Arguments
///
/// * `text` - Some of `r`, `w` and `x`, each at most once; `-` is skipped.
///
/// # Returns
///
/// Readable, writable and executable.
///
/// # Errors
///
/// When a letter is none of those, repeats, or none is given.
fn perms(text: &str) -> anyhow::Result<(bool, bool, bool)> {
    let (mut r, mut w, mut x) = (false, false, false);
    for c in text.chars() {
        let bit = match c {
            'r' => &mut r,
            'w' => &mut w,
            'x' => &mut x,
            '-' => continue,
            _ => bail!("permissions {}: {c:?} is none of r, w and x", quoted(text)),
        };
        if *bit {
            bail!("permissions {}: {c:?} given twice", quoted(text));
        }
        *bit = true;
    }
    if !(r || w || x) {
        bail!(
            "permissions {}: name at least one of r, w and x",
            quoted(text)
        );
    }
    Ok((r, w, x))
}

/// Renders a region's addresses as `start..end`.
///
/// # Arguments
///
/// * `r` - The region.
fn span(r: &Region) -> String {
    format!("{:#x}..{:#x}", r.va, r.va.saturating_add(r.len))
}
