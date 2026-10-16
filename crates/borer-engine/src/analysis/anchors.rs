//! Anchors: the facts a binding layer pins against a binary, re-derived and
//! judged after the binary changes.
//!
//! An SDK over a game client keeps hundreds of offsets, ids and addresses
//! it proved once, and re-proves each by hand when the client updates. A
//! manifest names each fact the way it was proved (a field of a class by
//! name, a constant a class answers from a vtable slot, a function by its
//! recovered name, the wire layout a class encodes or decodes) with the
//! value expected; every anchor is derived again from the new binary and
//! reported held, moved to a new value, changed to a new layout, or gone.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::encode::{compact_writes, encoding_for_class};
use super::naming::{in_data, parse_signature};
use super::schema::{compact_fields, named_field_offset, schema_for_class};
use super::vtables::slot_constants;
use super::{Analysis, Overlay, data_referrers, dedup_sorted, resolve};
use crate::program::Program;
use crate::strings::cstr_at;

/// Longest signature string read.
const SIG_MAX: usize = 512;
/// Shortest text considered a signature.
const SIG_MIN: usize = 8;

/// Entries of the functions referencing a signature string that parses to
/// each of `names`: how a binding proves a function by the `__FUNCSIG__`
/// it carries, whatever the analysis chose to call it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the cross-references.
/// * `names` - The qualified names wanted.
fn signature_referrers(
    program: &Program,
    analysis: &Analysis,
    names: &BTreeSet<&str>,
) -> BTreeMap<String, Vec<u64>> {
    let mut out: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    if names.is_empty() {
        return out;
    }
    for (&target, sites) in &analysis.xrefs {
        if !in_data(program, target) {
            continue;
        }
        let Some(sig) =
            cstr_at(program, target, SIG_MIN, SIG_MAX).and_then(|(_, text)| parse_signature(&text))
        else {
            continue;
        };
        if !names.contains(sig.name.as_str()) {
            continue;
        }
        let list = out.entry(sig.name.clone()).or_default();
        list.extend(data_referrers(sites));
        dedup_sorted(list);
    }
    out
}

/// What an anchor pins.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AnchorKind {
    /// A field of a class, by the name its class gives it: the offset.
    Field,
    /// The constant a class answers from a vtable slot: the value.
    Vconst,
    /// A function by its recovered name: the RVA.
    Function,
    /// What a class writes onto the wire, in the compact form `encodes`
    /// prints: the layout.
    Encode,
    /// What a class reads off the wire, in the compact form `schemas`
    /// prints: the layout.
    Decode,
}

impl AnchorKind {
    /// The kind's name in a manifest.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            AnchorKind::Field => "field",
            AnchorKind::Vconst => "vconst",
            AnchorKind::Function => "function",
            AnchorKind::Encode => "encode",
            AnchorKind::Decode => "decode",
        }
    }

    /// Whether the anchor pins a text (a layout) rather than a number.
    #[must_use]
    pub fn is_text(self) -> bool {
        matches!(self, AnchorKind::Encode | AnchorKind::Decode)
    }
}

/// One pinned fact.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Anchor {
    /// What is pinned.
    pub kind: AnchorKind,
    /// The class (field, vconst) or the function name (function).
    pub subject: String,
    /// The field name (field) or the slot index (vconst); empty otherwise.
    pub member: String,
    /// The value proved before; `0` for a layout.
    pub expected: u64,
    /// The layout proved before, for an encode or decode anchor; empty
    /// otherwise.
    pub layout: String,
}

/// What became of an anchor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Verdict {
    /// Derived again to the same value or layout.
    Held,
    /// Derived again to another value.
    Moved(u64),
    /// Derived again to another layout.
    Changed(String),
    /// Not derivable from this binary.
    Gone,
}

impl Verdict {
    /// The verdict as listings print it.
    #[must_use]
    pub fn word(&self) -> &'static str {
        match self {
            Verdict::Held => "held",
            Verdict::Moved(_) => "moved",
            Verdict::Changed(_) => "changed",
            Verdict::Gone => "gone",
        }
    }
}

/// Parses a manifest: one anchor per line, `#` comments and blank lines
/// skipped, columns separated by tabs or spaces.
///
/// Lines read `field <class> <name> <offset>`, `vconst <slot> <class> <value>`,
/// `function <name> <rva>`, `encode <class> <layout...>` or `decode <class>
/// <layout...>`; numbers are hex with `0x` or decimal, and a layout is the
/// rest of the line as `encodes` or `schemas` printed it.
///
/// # Arguments
///
/// * `text` - The manifest.
///
/// # Errors
///
/// The first line that is not an anchor, quoted with its number.
pub fn parse_manifest(text: &str) -> Result<Vec<Anchor>, String> {
    let mut out = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let cols: Vec<&str> = line.split_whitespace().collect();
        let bad = || {
            format!(
                "line {}: not an anchor: {}",
                i + 1,
                crate::text::quoted(line)
            )
        };
        let number = |s: &str| super::parse_addr(s).ok_or_else(bad);
        let layout_of = |kind: AnchorKind, class: &str| {
            let rest = line
                .split_whitespace()
                .skip(2)
                .collect::<Vec<_>>()
                .join(" ");
            if rest.is_empty() {
                return Err(bad());
            }
            Ok(Anchor {
                kind,
                subject: class.to_owned(),
                member: String::new(),
                expected: 0,
                layout: rest,
            })
        };
        let anchor = match cols.as_slice() {
            ["field", class, name, expected] => Anchor {
                kind: AnchorKind::Field,
                subject: (*class).to_owned(),
                member: (*name).to_owned(),
                expected: number(expected)?,
                layout: String::new(),
            },
            ["vconst", slot, class, expected] => {
                number(slot)?;
                Anchor {
                    kind: AnchorKind::Vconst,
                    subject: (*class).to_owned(),
                    member: (*slot).to_owned(),
                    expected: number(expected)?,
                    layout: String::new(),
                }
            }
            ["function", name, expected] => Anchor {
                kind: AnchorKind::Function,
                subject: (*name).to_owned(),
                member: String::new(),
                expected: number(expected)?,
                layout: String::new(),
            },
            ["encode", class, _, ..] => layout_of(AnchorKind::Encode, class)?,
            ["decode", class, _, ..] => layout_of(AnchorKind::Decode, class)?,
            _ => return Err(bad()),
        };
        out.push(anchor);
    }
    Ok(out)
}

/// Derives one anchor's value from the binary; see [`derive_layout`] for
/// the layouts.
///
/// A function the analysis calls by another name is still found through the
/// signature string it carries: the referrer at the expected address holds,
/// else the first referrer is where it moved.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `anchor` - The anchor.
/// * `signatures` - Referrers of the signature strings the manifest's
///   unresolved function names parse to.
///
/// # Returns
///
/// The value, or `None` when nothing in the binary answers to the anchor.
fn derive(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    anchor: &Anchor,
    signatures: &BTreeMap<String, Vec<u64>>,
) -> Option<u64> {
    match anchor.kind {
        AnchorKind::Field => {
            named_field_offset(program, analysis, overlay, &anchor.subject, &anchor.member)
        }
        AnchorKind::Vconst => {
            let slot = usize::try_from(super::parse_addr(&anchor.member)?).ok()?;
            slot_constants(program, analysis, slot)
                .into_iter()
                .find(|c| c.class == anchor.subject)
                .map(|c| c.value)
        }
        AnchorKind::Function => resolve(program, analysis, overlay, &anchor.subject)
            .ok()
            .map(|va| va.wrapping_sub(program.image_base))
            .or_else(|| {
                let referrers = signatures.get(&anchor.subject)?;
                let rvas: Vec<u64> = referrers
                    .iter()
                    .map(|va| va.wrapping_sub(program.image_base))
                    .collect();
                rvas.iter()
                    .copied()
                    .find(|rva| *rva == anchor.expected)
                    .or_else(|| rvas.first().copied())
            }),
        AnchorKind::Encode | AnchorKind::Decode => None,
    }
}

/// Derives a layout anchor's layout from the binary, in the compact form
/// the protocol tables print.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `anchor` - An encode or decode anchor.
///
/// # Returns
///
/// The layout, or `None` when no virtual of the class touches a stream.
fn derive_layout(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    anchor: &Anchor,
) -> Option<String> {
    match anchor.kind {
        AnchorKind::Encode => encoding_for_class(program, analysis, overlay, &anchor.subject)
            .map(|(_, e)| compact_writes(&e.fields)),
        AnchorKind::Decode => schema_for_class(program, analysis, overlay, &anchor.subject)
            .map(|(_, s)| compact_fields(&s.fields)),
        AnchorKind::Field | AnchorKind::Vconst | AnchorKind::Function => None,
    }
}

/// Judges every anchor against the binary.
///
/// A function anchor states an RVA; one that states the virtual address
/// instead means the same place.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `anchors` - The manifest's anchors.
#[must_use]
pub fn verify(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    anchors: &[Anchor],
) -> Vec<(Anchor, Verdict)> {
    let wanted: BTreeSet<&str> = anchors
        .iter()
        .filter(|a| a.kind == AnchorKind::Function)
        .filter(|a| resolve(program, analysis, overlay, &a.subject).is_err())
        .map(|a| a.subject.as_str())
        .collect();
    let signatures = signature_referrers(program, analysis, &wanted);
    anchors
        .iter()
        .map(|a| {
            let verdict = if a.kind.is_text() {
                match derive_layout(program, analysis, overlay, a) {
                    Some(l) if l == a.layout => Verdict::Held,
                    Some(l) => Verdict::Changed(l),
                    None => Verdict::Gone,
                }
            } else {
                let expected = if a.kind == AnchorKind::Function
                    && a.expected >= program.image_base
                    && a.expected - program.image_base < program.bytes.len() as u64
                {
                    a.expected - program.image_base
                } else {
                    a.expected
                };
                match derive(program, analysis, overlay, a, &signatures) {
                    Some(v) if v == expected => Verdict::Held,
                    Some(v) => Verdict::Moved(v),
                    None => Verdict::Gone,
                }
            };
            (a.clone(), verdict)
        })
        .collect()
}

/// Renders the verdicts as a `#`-headed table, and says whether every
/// anchor held.
///
/// The counts cover every anchor. Past `limit` rows the held ones are left
/// out first, since a held anchor says only what the manifest already
/// says, and the header says how many rows it shows.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `anchors` - The manifest's anchors.
/// * `limit` - Most rows listed.
///
/// # Returns
///
/// The table, and `true` when every anchor held.
#[must_use]
pub fn verify_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    anchors: &[Anchor],
    limit: usize,
) -> (String, bool) {
    let judged = verify(program, analysis, overlay, anchors);
    let held = judged.iter().filter(|(_, v)| *v == Verdict::Held).count();
    let moved = judged
        .iter()
        .filter(|(_, v)| matches!(v, Verdict::Moved(_)))
        .count();
    let changed = judged
        .iter()
        .filter(|(_, v)| matches!(v, Verdict::Changed(_)))
        .count();
    let gone = judged.len() - held - moved - changed;
    let mut held_room = limit.saturating_sub(judged.len() - held);
    let shown: Vec<&(Anchor, Verdict)> = judged
        .iter()
        .filter(|(_, v)| {
            if *v != Verdict::Held {
                return true;
            }
            let room = held_room > 0;
            held_room = held_room.saturating_sub(1);
            room
        })
        .take(limit)
        .collect();
    let mut out = format!(
        "# {} anchors: {held} held, {moved} moved, {changed} changed, {gone} gone",
        judged.len()
    );
    if shown.len() < judged.len() {
        let _ = write!(
            out,
            ", showing {} of {}, held ones left out first",
            shown.len(),
            judged.len()
        );
    }
    out.push('\n');
    out.push_str("kind\tsubject\tmember\texpected\tfound\tverdict\n");
    for (a, v) in shown {
        let expected = if a.kind.is_text() {
            a.layout.clone()
        } else {
            format!("{:#x}", a.expected)
        };
        let found = match v {
            Verdict::Held => expected.clone(),
            Verdict::Moved(n) => format!("{n:#x}"),
            Verdict::Changed(l) => l.clone(),
            Verdict::Gone => "-".to_owned(),
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{expected}\t{found}\t{}",
            a.kind.name(),
            a.subject,
            a.member,
            v.word()
        );
    }
    (out, held == judged.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A manifest parses its five kinds, skips comments, keeps a layout
    /// as the rest of its line, and refuses a line that is none of them
    /// with its number.
    ///
    /// # Panics
    ///
    /// When a parse disagrees with its expectation.
    #[test]
    fn manifests_parse_and_refuse_garbage() {
        let text = "# pins\nfield Msg::Open Id 0x20\nvconst 3 Cmd::Open 0x60\n\nfunction App::World::Update 0x1da5b4\nencode Cmd::Ping u32@+0x20\ndecode Cmd::Open string@+0x20=~Id u8@+0xe0\n";
        let anchors = parse_manifest(text).expect("parses");
        assert_eq!(anchors.len(), 5);
        assert_eq!(anchors[0].kind, AnchorKind::Field);
        assert_eq!(anchors[0].expected, 0x20);
        assert_eq!(anchors[1].member, "3");
        assert_eq!(anchors[2].subject, "App::World::Update");
        assert_eq!(anchors[3].kind, AnchorKind::Encode);
        assert_eq!(anchors[3].layout, "u32@+0x20");
        assert_eq!(anchors[4].layout, "string@+0x20=~Id u8@+0xe0");
        let err = parse_manifest("encode Cmd::X\n").expect_err("refused");
        assert!(err.contains("line 1"), "{err}");
        let err = parse_manifest("field only two\n").expect_err("refused");
        assert!(err.starts_with("line 1: not an anchor"), "{err}");
        let err = parse_manifest("function f notanumber\n").expect_err("refused");
        assert!(err.contains("line 1"), "{err}");
    }

    /// A function anchor holds at its entry, moves when the expectation is
    /// off, and is gone when nothing has the name; a layout anchor on a
    /// class the image lacks is gone too.
    ///
    /// # Panics
    ///
    /// When a verdict disagrees with the hand-built image.
    #[test]
    fn function_anchors_are_judged() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let anchors = parse_manifest(
            "function sub_1000 0x1000\nfunction sub_1000 0x1010\nfunction nosuch 0x1\nencode No::Class u32@+0x20\n",
        )
        .expect("parses");
        let (text, all_held) = verify_tsv(&p, &a, &Overlay::default(), &anchors, 100);
        assert!(!all_held);
        assert!(
            text.starts_with("# 4 anchors: 1 held, 1 moved, 0 changed, 2 gone\n"),
            "{text}"
        );
        assert!(
            text.contains("encode\tNo::Class\t\tu32@+0x20\t-\tgone\n"),
            "{text}"
        );
        assert!(
            text.contains("function\tsub_1000\t\t0x1010\t0x1000\tmoved\n"),
            "{text}"
        );
        assert!(
            text.contains("function\tnosuch\t\t0x1\t-\tgone\n"),
            "{text}"
        );
    }

    /// Past the row limit the table says how many rows it shows and leaves
    /// the held anchors out first, while the counts still cover every
    /// anchor; it listed every row of any manifest.
    ///
    /// # Panics
    ///
    /// When the cap is not stated, a held row beats one that moved, or a
    /// row past the limit is listed.
    #[test]
    fn the_verdict_table_is_capped_held_rows_first() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let anchors = parse_manifest(
            "function sub_1000 0x1000\nfunction sub_1000 0x1010\nfunction nosuch 0x1\nfunction gone2 0x2\n",
        )
        .expect("parses");
        let (text, _) = verify_tsv(&p, &a, &Overlay::default(), &anchors, 2);
        assert!(
            text.starts_with(
                "# 4 anchors: 1 held, 1 moved, 0 changed, 2 gone, showing 2 of 4, held ones left out first\n"
            ),
            "{text}"
        );
        assert_eq!(text.lines().count(), 4, "{text}");
        assert!(text.contains("\t0x1010\t0x1000\tmoved\n"), "{text}");
        assert!(text.contains("\tnosuch\t"), "{text}");
        assert!(!text.contains("\theld\n"), "{text}");
    }
}
