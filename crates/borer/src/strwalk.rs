//! The string-walk cache: one program's ASCII and UTF-16LE runs, walked
//! once and held for every `strings` call of the session.
//!
//! The `strings` tool answers from rows a walk already produced, and a
//! session asks more than once - another encoding, another filter, another
//! page - while the bytes it walked never change: `load_binary` is the only
//! event that can, and it resets the cache. The entry is still keyed by the
//! program's bytes (pointer and length), so a walk can only be served to
//! the allocation it was walked from, the way the decompile index is keyed
//! per program (`index::index_key`) with the session in place of the file.

use std::sync::{Arc, RwLock};

use borer_engine::program::Program;
use borer_engine::strings::{StringHit, find_strings, find_wide_strings};

use crate::params::StringEncoding;
use crate::{read_lock, write_lock};

/// Shortest run the cached walks keep: the `strings` default, so every
/// default call's rows are one filter away.
///
/// The tool clamps `min_length` to 4, but a floor call is not worth the
/// rows: a 44 MB image holds about thirteen times as many four-character
/// runs as five-character ones, all of them noise. The tool walks a floor
/// call itself instead of asking the cache.
pub(crate) const WALK_MIN: usize = 5;

/// One program's string rows, in offset order per encoding.
#[derive(Debug)]
pub(crate) struct StringWalks {
    /// The program's bytes the rows were walked from, by pointer and
    /// length: an entry is served only while those still name the loaded
    /// program's allocation.
    key: (usize, usize),
    /// ASCII runs of at least [`WALK_MIN`] bytes.
    ascii: Vec<StringHit>,
    /// UTF-16LE runs of at least [`WALK_MIN`] code units.
    utf16: Vec<StringHit>,
}

impl StringWalks {
    /// The rows one encoding asks for, cut to runs of `min` or more.
    ///
    /// # Arguments
    ///
    /// * `encoding` - Which walks' rows, or both merged by offset.
    /// * `min` - Shortest run kept, at least [`WALK_MIN`] so the filter
    ///   only drops rows the caller's own minimum excludes.
    ///
    /// # Returns
    ///
    /// The rows in offset order, an ASCII row before a UTF-16LE one at the
    /// same offset.
    pub(crate) fn rows(&self, encoding: StringEncoding, min: usize) -> Vec<&StringHit> {
        /// The rows of one walk, cut to runs of `min` or more.
        fn picked(rows: &[StringHit], min: usize) -> Vec<&StringHit> {
            rows.iter().filter(|h| h.len >= min).collect()
        }
        match encoding {
            StringEncoding::Ascii => picked(&self.ascii, min),
            StringEncoding::Utf16 => picked(&self.utf16, min),
            StringEncoding::Both => {
                let mut all = picked(&self.ascii, min);
                all.extend(picked(&self.utf16, min));
                all.sort_by_key(|h| h.off);
                all
            }
        }
    }
}

/// Returns the loaded program's string rows, walking and caching them on
/// first use.
///
/// Two calls that race both walk and the later store wins; the rows are a
/// pure function of the bytes, so either answer is the same one.
///
/// # Arguments
///
/// * `cache` - The server's walk cache, reset by `load_binary`.
/// * `program` - The loaded image.
///
/// # Returns
///
/// The walks, shared with every later `strings` call of the session.
pub(crate) fn load_or_build(
    cache: &RwLock<Option<Arc<StringWalks>>>,
    program: &Program,
) -> Arc<StringWalks> {
    let key = (program.bytes.as_ptr() as usize, program.bytes.len());
    if let Some(walks) = read_lock(cache).as_ref().filter(|w| w.key == key) {
        return Arc::clone(walks);
    }
    let walks = Arc::new(StringWalks {
        key,
        ascii: find_strings(&program.bytes, WALK_MIN),
        utf16: find_wide_strings(&program.bytes, WALK_MIN),
    });
    *write_lock(cache) = Some(Arc::clone(&walks));
    walks
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A raw program whose bytes carry the shapes the cache must keep.
    ///
    /// Runs at the cached minimum, runs above it, and runs the minimum
    /// excludes: a 4-byte ASCII run and a 4-unit wide run.
    fn program() -> Program {
        let mut bytes: Vec<u8> = Vec::new();
        bytes.extend_from_slice(b"abcdefgh\x00"); // 8, kept at any min
        bytes.extend_from_slice(b"abcd\x00"); // 4, below the cached minimum
        bytes.extend_from_slice(b"ijklmno\x00"); // 7
        for b in b"wide string" {
            bytes.extend_from_slice(&[*b, 0]);
        }
        bytes.extend_from_slice(&[b'x', 0, b'y', 0, b'z', 0, b'w', 0]); // 4 units, below it
        bytes.push(0);
        Program::raw(
            bytes,
            borer_engine::program::Arch::X86_64,
            0,
            None,
            Vec::new(),
        )
    }

    /// The cached rows answer what walking the bytes at the caller's own
    /// minimum answers, for every encoding.
    ///
    /// # Panics
    ///
    /// When a cached page disagrees with a fresh walk.
    #[test]
    fn rows_answer_what_a_walk_at_the_minimum_answers() {
        let walks = StringWalks {
            key: (0, 0),
            ascii: find_strings(&program().bytes, WALK_MIN),
            utf16: find_wide_strings(&program().bytes, WALK_MIN),
        };
        for encoding in [
            StringEncoding::Ascii,
            StringEncoding::Utf16,
            StringEncoding::Both,
        ] {
            for min in WALK_MIN..9 {
                let cached: Vec<(u64, usize)> = walks
                    .rows(encoding, min)
                    .iter()
                    .map(|h| (h.off, h.len))
                    .collect();
                let walked: Vec<(u64, usize)> = match encoding {
                    StringEncoding::Ascii => find_strings(&program().bytes, min),
                    StringEncoding::Utf16 => find_wide_strings(&program().bytes, min),
                    StringEncoding::Both => {
                        let mut all = find_strings(&program().bytes, min);
                        all.extend(find_wide_strings(&program().bytes, min));
                        all.sort_by_key(|h| h.off);
                        all
                    }
                }
                .iter()
                .map(|h| (h.off, h.len))
                .collect();
                assert_eq!(cached, walked, "{encoding:?} min {min}");
            }
        }
    }

    /// The second call shares the first's walks, and a load resets them.
    ///
    /// # Panics
    ///
    /// When a cached walk is rebuilt or survives its program.
    #[test]
    fn load_or_build_builds_once_and_resets_with_the_program() {
        let cache: RwLock<Option<Arc<StringWalks>>> = RwLock::new(None);
        let p = program();
        let first = load_or_build(&cache, &p);
        let second = load_or_build(&cache, &p);
        assert!(
            Arc::ptr_eq(&first, &second),
            "the second call walks nothing"
        );
        *write_lock(&cache) = None;
        let third = load_or_build(&cache, &p);
        assert!(
            !Arc::ptr_eq(&first, &third),
            "a reset program walks again, sharing nothing with the stale rows"
        );
    }
}
