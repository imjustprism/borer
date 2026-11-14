//! String-literal and data candidates a function's reference sites bear out.

use std::collections::{BTreeMap, BTreeSet};

use super::super::expr::{Key, tls_slot};
use super::super::line::is_global_name;
use crate::analysis::{Analysis, Overlay, reads};
use crate::program::{BinaryFormat, Program};

/// Tells whether `va` is a mapped image or zero-filled data address.
///
/// Covers file-backed sections, zero-filled `.bss` sections and a PE's mapped
/// headers or image base, while rejecting unmapped constants and synthetic
/// thread-local slots.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - Candidate virtual address.
pub(crate) fn is_mapped_data(program: &Program, va: u64) -> bool {
    program.section_at(va).is_some()
        || program.zero_fill_at(va).is_some()
        || program.in_headers(va)
        || (program.format == BinaryFormat::Pe && va == program.image_base)
}

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

/// Tells whether `spelled` is a named global spelling handled outside
/// `g<bits>_<hex>` address tokens and string or selector literals.
///
/// # Arguments
///
/// * `spelled` - Candidate identifier text.
fn usable_data_spelling(spelled: &str) -> bool {
    !spelled.is_empty()
        && !spelled.starts_with(['"', '@'])
        && !spelled.starts_with("L\"")
        && !spelled.contains('(')
        && !is_global_name(spelled)
        && !crate::winconst::is_constant(spelled)
}

/// Records `(spelled, va)` in `by`, marking a second distinct address `None`.
///
/// # Arguments
///
/// * `by` - Candidate map under construction.
/// * `spelled` - Rendered global name.
/// * `va` - Referenced data address.
fn record_data(by: &mut BTreeMap<String, Option<u64>>, spelled: &str, va: u64) {
    if !usable_data_spelling(spelled) {
        return;
    }
    match by.get_mut(spelled) {
        Some(prev) => {
            if *prev != Some(va) {
                *prev = None;
            }
        }
        None => {
            by.insert(spelled.to_owned(), Some(va));
        }
    }
}

/// Builds the named-data candidates a function's reference targets spell.
///
/// Probing runs inside [`reads::unnoted`] so whole overlay tables are not
/// noted, then each referenced data address is noted individually in
/// [`Overlay::names`].
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - Function entry being read.
/// * `refs` - Reference targets of that function.
pub(super) fn candidate_data(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    refs: &BTreeSet<u64>,
) -> BTreeMap<String, Option<u64>> {
    let (by, noted) = reads::unnoted(|| {
        let names = super::super::sites::standalone_names(program, analysis, overlay, entry);
        let word_bits = u8::try_from(names.word.saturating_mul(8)).unwrap_or(64);
        let mut by: BTreeMap<String, Option<u64>> = BTreeMap::new();
        let mut noted = Vec::new();
        for &v in refs {
            if !is_mapped_data(program, v)
                || analysis.function(v).is_some()
                || names.import_at(v).is_some()
            {
                continue;
            }
            noted.push(v);
            if let Some(raw) = names.const_name(v, false) {
                let spelled = raw.strip_prefix('&').unwrap_or(&raw);
                record_data(&mut by, spelled, v);
            }
            if tls_slot(v).is_none() {
                let key_name = names.key(Key::Global(v, word_bits));
                record_data(&mut by, &key_name, v);
            }
        }
        (by, noted)
    });
    for v in noted {
        _ = overlay.names.contains_key(&v);
    }
    by
}
