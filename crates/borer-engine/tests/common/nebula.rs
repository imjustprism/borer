//! The Nebula pack borer ships, for tests of what a pack adds to an
//! analysis.

use borer_engine::pack::{Pack, Packs};
use std::sync::Arc;

/// The Nebula pack borer ships, read as a user's `--pack` reads it.
///
/// # Returns
///
/// The pack set an analysis takes; empty when the pack does not parse.
///
/// # Panics
///
/// When the pack parses with warnings.
pub(crate) fn nebula() -> Arc<Packs> {
    let text = include_str!("../../../../packs/nebula.borer");
    let packs = Pack::parse(text, "nebula.borer")
        .map(|(pack, warnings)| {
            assert!(warnings.is_empty(), "{warnings:?}");
            vec![pack]
        })
        .unwrap_or_default();
    Arc::new(Packs { packs })
}
