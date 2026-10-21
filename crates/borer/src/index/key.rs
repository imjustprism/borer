//! The key an index is stored under: the program's bytes, and everything
//! besides them that changes the text an index holds.

use std::fmt::Write as _;
use std::time::UNIX_EPOCH;

use borer_engine::pack::Packs;
use borer_engine::program::Program;

use super::{FNV_SEED, FORMAT, IndexKey, fnv1a, program_key};

/// Returns the key an index for `program` is stored under.
///
/// That is the program's bytes, then the borer executable's size and
/// modification time, the file format, the packs the analysis ran with,
/// and what the load made of the bytes. The executable goes in because the text is what the decompiler of that
/// build renders; a newer borer must not read an older one's index. The
/// packs go in because they change the names the text uses. The load goes
/// in because one file loaded another way is another program: a raw load's
/// `arch`, `base` and `regions`, an `entry_file_offset`, and a companion
/// PDB applied or not move every address, name and type the text shows
/// while the bytes stay the same; it is the architecture, base, entry,
/// section table, symbols, function ranges, and the functions and types
/// debug information gave, hashed whole, since a PDB can name and type
/// what was already there without adding to any count. All are kept apart from the program's half, so a new index finds
/// and replaces the stale ones of its program by name.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `packs` - The packs the analysis ran with.
#[must_use]
pub fn index_key(program: &Program, packs: &Packs) -> IndexKey {
    let mut h = fnv1a(FNV_SEED, &FORMAT.to_le_bytes());
    for pack in &packs.packs {
        for e in &pack.entries {
            for part in [&e.section, &e.key, &e.value] {
                h = fnv1a(h, part.as_bytes());
                h = fnv1a(h, &[0]);
            }
        }
        for (_, code) in &pack.scripts {
            h = fnv1a(h, code.as_bytes());
            h = fnv1a(h, &[0]);
        }
    }
    let mut load = Fnv(h);
    let _ = write!(
        load,
        "{:?} {:#x} {:?} {:?} {:?} {:?} {:?} {:?}",
        program.arch,
        program.image_base,
        program.entry,
        program.sections,
        program.symbols,
        program.function_ranges,
        program.debug_functions,
        program.debug_types
    );
    let mut h = load.0;
    if let Ok(exe) = std::env::current_exe()
        && let Ok(meta) = std::fs::metadata(exe)
    {
        h = fnv1a(h, &meta.len().to_le_bytes());
        let modified = meta
            .modified()
            .ok()
            .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
            .map_or(0, |d| d.as_secs());
        h = fnv1a(h, &modified.to_le_bytes());
    }
    IndexKey {
        program: program_key(&program.bytes),
        engine: h,
    }
}

/// An FNV-1a hash that text is written into a piece at a time, so a long
/// rendering is hashed without being built whole.
struct Fnv(u64);

impl std::fmt::Write for Fnv {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0 = fnv1a(self.0, s.as_bytes());
        Ok(())
    }
}
