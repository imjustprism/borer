//! The protocol as one table: for every class answering a vtable slot
//! with a constant, who sends it, what it writes onto the wire, and what
//! it reads back.
//!
//! The pieces exist on their own (`senders`, `encodes`, `schemas`); an
//! agent asking "what is opcode 0x5f, who sends it and what is in it"
//! wants them on one row rather than three reads joined by hand. The
//! function handling a class once decoded (`HandleKillCommand`, named
//! from the "Command handler for type" assertion it carries) sits on
//! the row as well, since for a message the server sends that is what a
//! client-side hook goes on.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::encode::{compact_writes, encoding_for_class};
use super::schema::{compact_fields, schema_for_class};
use super::senders::{senders, spell};
use super::{Analysis, Overlay, name_of};
use crate::program::Program;

/// Most senders spelled out on one row of the joined table.
const SENDERS_MAX: usize = 4;
/// Fewest classes worth a worker each when the table is built.
const PAR_MIN: usize = 8;

/// One row of the joined protocol table.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ProtocolRow {
    /// The constant the class answers the slot with.
    value: u64,
    /// The class.
    class: String,
    /// Its senders, spelled.
    senders: String,
    /// Its handlers, spelled.
    handler: String,
    /// What it writes onto the wire, compact.
    encodes: String,
    /// What it reads off the wire, compact.
    decodes: String,
}

/// Every function whose own name is `Handle<Something>`, by that name: the
/// handlers the assertion strings named, and those a class names so.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
fn handler_index(analysis: &Analysis, overlay: &Overlay) -> BTreeMap<String, Vec<u64>> {
    let mut out: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for f in &analysis.functions {
        let name = name_of(analysis, overlay, f.entry);
        let own = name.rsplit("::").next().unwrap_or(&name);
        if own.starts_with("Handle") && own.len() > "Handle".len() {
            out.entry(own.to_owned()).or_default().push(f.entry);
        }
    }
    out
}

/// Renders every class answering `slot` with a constant with its senders,
/// its handler, its encoding and its decoding on one row, ordered by the
/// constant.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
/// * `slot` - The vtable index the constant sits in, zero-based.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn protocol_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    slot: usize,
    filter: &str,
    limit: usize,
) -> String {
    let q = filter.to_lowercase();
    let rows: Vec<_> = senders(program, analysis, overlay, slot)
        .into_iter()
        .filter(|r| q.is_empty() || r.class.to_lowercase().contains(&q))
        .collect();
    let total = rows.len();
    let handlers = handler_index(analysis, overlay);
    let mut lines: Vec<ProtocolRow> = Vec::with_capacity(total);
    let mut sent = 0usize;
    let mut handled = 0usize;
    let mut encoded = 0usize;
    let mut decoded = 0usize;
    let shown: Vec<_> = rows.into_iter().take(limit).collect();
    let records = super::striped_with(
        &shown,
        PAR_MIN,
        || (),
        |(), r| {
            (
                encoding_for_class(program, analysis, overlay, &r.class)
                    .map_or_else(|| "-".to_owned(), |(_, e)| compact_writes(&e.fields)),
                schema_for_class(program, analysis, overlay, &r.class)
                    .map_or_else(|| "-".to_owned(), |(_, s)| compact_fields(&s.fields)),
            )
        },
    );
    for (r, record) in shown.into_iter().zip(records) {
        let (encodes, decodes) = record.unwrap_or_else(|| ("-".to_owned(), "-".to_owned()));
        let names: Vec<String> = r
            .senders
            .iter()
            .map(|&s| name_of(analysis, overlay, s))
            .collect();
        sent += usize::from(!names.is_empty());
        let short = r.class.rsplit("::").next().unwrap_or(&r.class);
        let handler: Vec<String> = handlers
            .get(&format!("Handle{short}"))
            .map(|entries| {
                entries
                    .iter()
                    .map(|&e| name_of(analysis, overlay, e))
                    .collect()
            })
            .unwrap_or_default();
        handled += usize::from(!handler.is_empty());
        encoded += usize::from(encodes != "-");
        decoded += usize::from(decodes != "-");
        lines.push(ProtocolRow {
            value: r.value,
            class: r.class,
            senders: spell(&names, SENDERS_MAX),
            handler: spell(&handler, SENDERS_MAX),
            encodes,
            decodes,
        });
    }
    let mut out = format!(
        "# {total} classes answer virtual {slot} with a constant: {sent} sent by code, {handled} handled, {encoded} encode a record, {decoded} decode one, showing {}\n",
        lines.len()
    );
    out.push_str("value\tclass\tsenders\thandler\tencodes\tdecodes\n");
    for row in lines {
        let _ = writeln!(
            out,
            "{:#x}\t{}\t{}\t{}\t{}\t{}",
            row.value, row.class, row.senders, row.handler, row.encodes, row.decodes
        );
    }
    out
}

/// Spells addresses with the function each sits in, the first few and a
/// count of the rest, `-` for none.
///
/// # Arguments
///
/// * `analysis` - For the function names.
/// * `overlay` - Names in force.
/// * `sites` - `(site, function entry)` pairs.
fn spell_sites(analysis: &Analysis, overlay: &Overlay, sites: &[(u64, u64)]) -> String {
    if sites.is_empty() {
        return "-".to_owned();
    }
    let mut text = sites
        .iter()
        .take(SENDERS_MAX)
        .map(|&(site, from)| format!("{site:#x}@{}", name_of(analysis, overlay, from)))
        .collect::<Vec<_>>()
        .join(", ");
    if sites.len() > SENDERS_MAX {
        let _ = write!(text, " +{} more", sites.len() - SENDERS_MAX);
    }
    text
}

/// Renders, for every class answering `slot` with a constant, the addresses
/// a binding hooks: the encoder, the decoder, the handler, and each call
/// site the client sends from.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
/// * `slot` - The vtable index the constant sits in, zero-based.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn hooks_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    slot: usize,
    filter: &str,
    limit: usize,
) -> String {
    let q = filter.to_lowercase();
    let rows: Vec<_> = senders(program, analysis, overlay, slot)
        .into_iter()
        .filter(|r| q.is_empty() || r.class.to_lowercase().contains(&q))
        .collect();
    let total = rows.len();
    let handlers = handler_index(analysis, overlay);
    let shown: Vec<_> = rows.into_iter().take(limit).collect();
    let entries = super::striped_with(
        &shown,
        PAR_MIN,
        || (),
        |(), r| {
            (
                encoding_for_class(program, analysis, overlay, &r.class).map(|(e, _)| e),
                schema_for_class(program, analysis, overlay, &r.class).map(|(e, _)| e),
            )
        },
    );
    let hex = |e: Option<u64>| e.map_or_else(|| "-".to_owned(), |e| format!("{e:#x}"));
    let mut lines: Vec<String> = Vec::with_capacity(shown.len());
    let (mut encoders, mut decoders, mut handled, mut sending) = (0usize, 0usize, 0usize, 0usize);
    for (r, found) in shown.into_iter().zip(entries) {
        let (encoder, decoder) = found.unwrap_or((None, None));
        let short = r.class.rsplit("::").next().unwrap_or(&r.class);
        let handler = handlers
            .get(&format!("Handle{short}"))
            .and_then(|entries| entries.first().copied());
        encoders += usize::from(encoder.is_some());
        decoders += usize::from(decoder.is_some());
        handled += usize::from(handler.is_some());
        sending += usize::from(!r.sites.is_empty());
        lines.push(format!(
            "{:#x}\t{}\t{}\t{}\t{}\t{}",
            r.value,
            r.class,
            hex(encoder),
            hex(decoder),
            hex(handler),
            spell_sites(analysis, overlay, &r.sites)
        ));
    }
    let mut out = format!(
        "# {total} classes answer virtual {slot} with a constant: {encoders} with an encoder, {decoders} with a decoder, {handled} with a handler, {sending} sent from a call site, showing {}\n",
        lines.len()
    );
    out.push_str("value\tclass\tencoder\tdecoder\thandler\tsend_sites\n");
    for line in lines {
        out.push_str(&line);
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An image with no classes yields an empty hooks table with its header.
    ///
    /// # Panics
    ///
    /// When the header differs.
    #[test]
    fn an_image_without_classes_has_an_empty_hooks_table() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let text = hooks_tsv(&p, &a, &Overlay::default(), 3, "", 10);
        assert!(
            text.starts_with(
                "# 0 classes answer virtual 3 with a constant: 0 with an encoder, 0 with a decoder, 0 with a handler, 0 sent from a call site, showing 0\n"
            ),
            "{text}"
        );
        assert_eq!(
            text.lines().nth(1),
            Some("value\tclass\tencoder\tdecoder\thandler\tsend_sites")
        );
        assert_eq!(spell_sites(&a, &Overlay::default(), &[]), "-");
        assert_eq!(
            spell_sites(&a, &Overlay::default(), &[(0x1005, 0x1000)]),
            "0x1005@sub_1000"
        );
    }

    /// An image with no classes yields an empty table with its header.
    ///
    /// # Panics
    ///
    /// When the header differs.
    #[test]
    fn an_image_without_classes_has_an_empty_protocol() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let text = protocol_tsv(&p, &a, &Overlay::default(), 3, "", 10);
        assert!(
            text.starts_with(
                "# 0 classes answer virtual 3 with a constant: 0 sent by code, 0 handled, 0 encode a record, 0 decode one, showing 0\n"
            ),
            "{text}"
        );
        assert_eq!(
            text.lines().nth(1),
            Some("value\tclass\tsenders\thandler\tencodes\tdecodes")
        );
        assert_eq!(spell(&["a".to_owned()], SENDERS_MAX), "a");
        let many: Vec<String> = (0..6).map(|i| format!("f{i}")).collect();
        assert_eq!(spell(&many, SENDERS_MAX), "f0, f1, f2, f3 +2 more");
    }
}
