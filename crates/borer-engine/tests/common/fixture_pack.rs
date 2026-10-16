//! A pack the tests load, standing in for a file a user passes with `--pack`.
//!
//! The repository ships no target packs. This text is only the two lines the
//! fixture needs: the singleton static's name, and `Network::` as a stream.

use borer_engine::pack::{Pack, Packs};
use std::sync::Arc;

/// The pack text. A real pack is a file outside this tree.
const PACK: &str = "\
pack fixture 1
about test pack: the singleton static's name, and Network:: as a stream

[naming]
singleton Singleton

[types]
stream Network::
";

/// The test pack, read the way a user's `--pack` is read.
///
/// # Returns
///
/// The pack set an analysis takes; empty when the pack does not parse.
///
/// # Panics
///
/// When the pack parses with warnings.
pub(crate) fn fixture_pack() -> Arc<Packs> {
    let packs = Pack::parse(PACK, "fixture.borer")
        .map(|(pack, warnings)| {
            assert!(warnings.is_empty(), "{warnings:?}");
            vec![pack]
        })
        .unwrap_or_default();
    Arc::new(Packs { packs })
}
