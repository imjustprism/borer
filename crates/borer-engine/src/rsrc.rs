//! The PE resource tree, walked from the file's bytes to each resource.
//!
//! What an installer, a script compiler or a runtime stores there is how it
//! is named, so the walk keeps each leaf's type and name.
//!
//! The bytes are untrusted: the walk reads three levels and no more, at most
//! [`ENTRIES_MAX`] entries a directory and [`LEAVES_MAX`] leaves in all, and
//! every read is bounds-checked.

use crate::num::{from_usize, saturating_usize, u16_le, u32_le};
use crate::program::{BinaryFormat, Program};

/// Most entries one resource directory is read for.
const ENTRIES_MAX: usize = 4096;
/// Most leaves one walk keeps.
const LEAVES_MAX: usize = 4096;
/// Most directory entries one walk reads at every level together, so a
/// tree whose subdirectories all point back at one directory stays small.
const VISITS_MAX: usize = 1 << 16;
/// Most UTF-16 units of a resource name read.
const NAME_MAX: usize = 64;
/// The high bit of a directory entry's word: a name offset, or a subdirectory.
const HIGH: u32 = 0x8000_0000;
/// `RT_RCDATA`, raw data a program reads back itself.
pub const RCDATA: &str = "10";

/// One resource: its type and name as the directory spells them, and where
/// its bytes are in the file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Resource {
    /// The type: a decimal `RT_*` id (`10` for raw data) or its name.
    pub kind: String,
    /// The name: `#` and a decimal id, or the name the directory spells.
    pub name: String,
    /// The file offset of its bytes.
    pub off: u64,
    /// How many bytes.
    pub len: u64,
}

/// The file offset of a PE image's resource directory, read from the
/// optional header's data directory.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// `None` for a file that is not PE, holds no resource directory, or whose
/// directory maps to no file bytes.
fn directory(p: &Program) -> Option<usize> {
    if p.format != BinaryFormat::Pe {
        return None;
    }
    let bytes = p.bytes.as_slice();
    let pe = saturating_usize(u64::from(u32_le(bytes, 0x3c)?));
    if bytes.get(pe..pe.checked_add(4)?)? != b"PE\0\0" {
        return None;
    }
    let opt = pe.checked_add(24)?;
    let (count_at, dirs) = match u16_le(bytes, opt)? {
        0x10b => (opt + 92, opt + 96),
        0x20b => (opt + 108, opt + 112),
        _ => return None,
    };
    if u32_le(bytes, count_at)? < 3 {
        return None;
    }
    let rva = u32_le(bytes, dirs + 16)?;
    if rva == 0 {
        return None;
    }
    let off = p.va_to_offset(p.image_base.checked_add(u64::from(rva))?)?;
    Some(saturating_usize(off))
}

/// The entries of one resource directory, as `(name word, data word)`
/// pairs, each taken from a budget the whole walk shares.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `dir` - This directory's file offset.
/// * `budget` - Entries the walk may still read; reduced by those read here.
fn entries(bytes: &[u8], dir: usize, budget: &mut usize) -> Vec<(u32, u32)> {
    let count = [12, 14]
        .iter()
        .filter_map(|o| u16_le(bytes, dir.saturating_add(*o)))
        .map(usize::from)
        .sum::<usize>()
        .min(ENTRIES_MAX)
        .min(*budget);
    *budget -= count;
    (0..count)
        .map_while(|i| {
            let e = dir.checked_add(16 + i * 8)?;
            Some((u32_le(bytes, e)?, u32_le(bytes, e + 4)?))
        })
        .collect()
}

/// A directory entry's label: its name, or `#` and its id.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `base` - The resource directory's file offset.
/// * `name` - The entry's first word.
fn label(bytes: &[u8], base: usize, name: u32) -> String {
    if name & HIGH == 0 {
        return format!("#{name}");
    }
    let at = base.saturating_add(saturating_usize(u64::from(name & !HIGH)));
    let len = u16_le(bytes, at).map_or(0, usize::from).min(NAME_MAX);
    let units: Vec<u16> = (0..len)
        .map_while(|i| u16_le(bytes, at + 2 + i * 2))
        .collect();
    String::from_utf16_lossy(&units)
}

/// Every resource of a PE image, in directory order.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// The resources whose bytes lie in the file; empty for an image with none
/// or a file that is not PE.
#[must_use]
pub fn resources(p: &Program) -> Vec<Resource> {
    let Some(base) = directory(p) else {
        return Vec::new();
    };
    let bytes = p.bytes.as_slice();
    let sub = |word: u32| {
        (word & HIGH != 0).then(|| base.saturating_add(saturating_usize(u64::from(word & !HIGH))))
    };
    let mut out = Vec::new();
    let mut budget = VISITS_MAX;
    for (kind, word) in entries(bytes, base, &mut budget) {
        let Some(names) = sub(word) else { continue };
        let kind = label(bytes, base, kind);
        for (name, word) in entries(bytes, names, &mut budget) {
            let Some(langs) = sub(word) else { continue };
            let name = label(bytes, base, name);
            for (_, word) in entries(bytes, langs, &mut budget) {
                if out.len() >= LEAVES_MAX {
                    return out;
                }
                if word & HIGH != 0 {
                    continue;
                }
                let leaf = base.saturating_add(saturating_usize(u64::from(word)));
                let (Some(rva), Some(len)) = (u32_le(bytes, leaf), u32_le(bytes, leaf + 4)) else {
                    continue;
                };
                let Some(off) = p
                    .image_base
                    .checked_add(u64::from(rva))
                    .and_then(|va| p.va_to_offset(va))
                else {
                    continue;
                };
                if off.saturating_add(u64::from(len)) <= from_usize(bytes.len()) {
                    out.push(Resource {
                        kind: kind.trim_start_matches('#').to_owned(),
                        name: name.clone(),
                        off,
                        len: u64::from(len),
                    });
                }
            }
        }
    }
    out
}
