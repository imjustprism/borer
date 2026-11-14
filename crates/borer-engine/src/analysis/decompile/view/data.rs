//! String-literal and data candidates a function's reference sites bear out.

use std::collections::{BTreeMap, BTreeSet};

use crate::program::Program;

/// Builds the string-literal candidates a function's reference targets spell.
///
/// Each target in `refs` is spelled with [`super::super::literal::literal_at`];
/// the first address spelling a literal records `Some(addr)`, and a second
/// distinct address spelling the same literal marks it `None` so the caller
/// counts it as ambiguous.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `own` - Bare name of the function whose text is read.
/// * `refs` - Reference targets of that function.
pub(super) fn candidate_strings(
    program: &Program,
    own: &str,
    refs: &BTreeSet<u64>,
) -> BTreeMap<String, Option<u64>> {
    let mut by: BTreeMap<String, Option<u64>> = BTreeMap::new();
    for &v in refs {
        let Some(spelled) = super::super::literal::literal_at(program, v, own) else {
            continue;
        };
        by.entry(spelled)
            .and_modify(|prev| *prev = None)
            .or_insert(Some(v));
    }
    by
}
