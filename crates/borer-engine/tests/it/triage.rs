//! The triage as values: each producer's first line is its summary, the
//! report is spelled from the summaries, and each reason it gives to read
//! a function is one the engine holds.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{self, Basis, Reason, Summary};
use borer_engine::analysis::{Analysis, Overlay, bare_name};
use borer_engine::crypto::Storage;
use borer_engine::program::Program;

use crate::common::fixture;

/// Returns a report's first line without its `# `.
///
/// # Arguments
///
/// * `text` - The report.
fn first_line(text: &str) -> &str {
    let line = text.lines().next().unwrap_or("");
    line.strip_prefix("# ").unwrap_or(line)
}

/// Returns each producer the triage reads, by name, with its text and its
/// summary.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its analysis.
/// * `o` - Names in force.
fn producers(p: &Program, a: &Analysis, o: &Overlay) -> Vec<(&'static str, String, Summary)> {
    vec![
        (
            "protection",
            render::protection_tsv(p, a),
            render::protection_summary(p, a),
        ),
        (
            "anti-analysis",
            render::anti_analysis_tsv(p, a, o),
            render::anti_analysis_summary(p, a),
        ),
        (
            "crypto",
            render::crypto_tsv(p, a, o, 0, 1),
            render::crypto_summary(p, a),
        ),
        (
            "dynamic imports",
            render::dynamic_imports_tsv(p, a, o),
            render::dynamic_imports_summary(p, a, o),
        ),
        (
            "checks",
            render::license_checks_tsv(p, a, o),
            render::license_checks_summary(p, a, o),
        ),
        (
            "capabilities",
            render::capability_map_tsv(p, Some(a)),
            render::capability_summary(p, Some(a)),
        ),
    ]
}

/// Requires each producer's first line to be its summary's headline, and
/// each summary's addresses to be ascending, distinct and capped.
///
/// # Arguments
///
/// * `p` - The loaded image.
fn producers_agree(p: &Program) {
    let a = Analysis::compute(p);
    let o = Overlay::default();
    for (name, text, summary) in producers(p, &a, &o) {
        assert_eq!(first_line(&text), summary.headline, "{name}:\n{text}");
        assert!(summary.at.len() <= render::SUMMARY_AT_MAX, "{name}");
        assert!(
            summary.at.windows(2).all(|w| w[0] < w[1]),
            "{name}: {:?}",
            summary.at
        );
    }
}

/// The fixture's producers, a check and an input reader among them, each
/// spell their first line from their summary.
#[test]
fn each_producer_spells_its_first_line_from_its_summary() {
    producers_agree(&fixture());
}

/// A file with no imports and no code found still spells every first line
/// from its summary: the zero cases have a headline too.
#[test]
fn an_empty_program_spells_its_first_lines_from_its_summaries() {
    let mut p = fixture();
    p.symbols.clear();
    p.bytes.iter_mut().for_each(|b| *b = 0);
    producers_agree(&p);
}

/// The license checks summary counts the checks it names, at their entries.
#[test]
fn the_checks_summary_points_at_the_checks() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let s = render::license_checks_summary(&p, &a, &o);
    assert_eq!(s.at.len(), s.count.min(render::SUMMARY_AT_MAX), "{s:?}");
    assert!(
        s.at.iter().all(|e| a.function(*e).is_some()),
        "a check is a function: {s:?}"
    );
}

/// A file read without code analysis spells its capability map's first
/// line from the same summary.
#[test]
fn the_capability_summary_holds_without_an_analysis() {
    let p = fixture();
    assert_eq!(
        first_line(&render::capability_map_tsv(&p, None)),
        render::capability_summary(&p, None).headline
    );
}

/// The labels of the triage's section lines, in the order its text prints
/// them.
const ORDER: [&str; 8] = [
    "protection",
    "anti-analysis",
    "crypto",
    "dynamic imports",
    "checks",
    "generated strings",
    "capabilities",
    "iocs",
];

/// Requires the triage's text to be its values spelled, each section line
/// to repeat its producer's first line, in [`ORDER`], and each function on
/// the reading list to be a discovered function.
///
/// # Arguments
///
/// * `p` - The loaded image.
fn spelled_from_values(p: &Program) {
    let a = Analysis::compute(p);
    let o = Overlay::default();
    let triage = render::triage(p, &a, &o);
    let text = render::triage_tsv(p, &a, &o);
    assert_eq!(triage.spell(), text);
    let kinds: Vec<&str> = triage.sections.iter().map(|s| s.kind.label()).collect();
    assert_eq!(kinds, ORDER, "{text}");
    let lines: Vec<&str> = text.lines().collect();
    let at = |label: &str| {
        lines
            .iter()
            .position(|l| l.starts_with(&format!("# {label}: ")))
    };
    let places: Vec<Option<usize>> = ORDER.iter().map(|label| at(label)).collect();
    assert!(
        places.iter().all(Option::is_some) && places.windows(2).all(|w| w[0] < w[1]),
        "{places:?}\n{text}"
    );
    for (name, report, _) in producers(p, &a, &o) {
        let head = first_line(&report);
        let said = head.strip_prefix(&format!("{name}: ")).unwrap_or(head);
        let line = at(name).and_then(|i| lines.get(i)).copied();
        assert_eq!(line, Some(format!("# {name}: {said}").as_str()), "{name}");
    }
    assert!(triage.read_first.len() <= triage.candidates, "{text}");
    for r in &triage.read_first {
        assert!(
            a.function(r.entry).is_some(),
            "{:#x} is not a function entry:\n{text}",
            r.entry
        );
    }
}

/// The fixture's triage is its values spelled, its sections repeat their
/// producers in order and its reading list names functions.
#[test]
fn the_triage_is_spelled_from_its_values() {
    let p = fixture();
    spelled_from_values(&p);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert!(
        !render::triage(&p, &a, &o).read_first.is_empty(),
        "the fixture has functions worth reading"
    );
}

/// A program with no imports and its bytes zeroed is spelled from its
/// values too: every section has a line when it found nothing.
#[test]
fn an_empty_triage_is_spelled_from_its_values() {
    let mut p = fixture();
    p.symbols.clear();
    p.bytes.iter_mut().for_each(|b| *b = 0);
    spelled_from_values(&p);
}

/// A TLS callback raises a blind spot the values hold and the text prints.
#[test]
fn a_blind_spot_is_a_value_the_text_prints() {
    let mut p = fixture();
    p.headers.tls_callbacks.push(0x1_4000_1000);
    spelled_from_values(&p);
    let a = Analysis::compute(&p);
    let triage = render::triage(&p, &a, &Overlay::default());
    assert!(
        triage
            .blind_spots
            .iter()
            .any(|s| s.contains("TLS callback")),
        "{:?}",
        triage.blind_spots
    );
}

/// Two analyses of one program give equal triages.
#[test]
fn the_triage_is_the_same_value_from_two_analyses() {
    let p = fixture();
    let o = Overlay::default();
    let one = render::triage(&p, &Analysis::compute(&p), &o);
    let two = render::triage(&p, &Analysis::compute(&p), &o);
    assert_eq!(one, two);
}

/// Each section names the resource that answers more, the crypto
/// constants aside, which only a tool lists.
#[test]
fn each_section_names_where_more_is() {
    let p = fixture();
    let a = Analysis::compute(&p);
    for s in &render::triage(&p, &a, &Overlay::default()).sections {
        let uri = s.kind.uri();
        if s.kind == render::SectionKind::Crypto {
            assert_eq!(uri, None);
        } else {
            assert!(
                uri.is_some_and(|u| u.starts_with("borer://")),
                "{:?}",
                s.kind
            );
        }
    }
}

/// Requires every reason on the reading list to be one the engine holds.
///
/// A built string by a recovery of this function, a call by a callee of
/// this function the symbol tables name so, a held constant by an address
/// inside this function.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its analysis.
/// * `triage` - The triage of the two.
fn corroborated(p: &Program, a: &Analysis, triage: &render::Triage) {
    let built = render::generated_strings(p, a, "");
    for r in &triage.read_first {
        let callees = a.function(r.entry).map(|f| f.callees.clone());
        assert!(callees.is_some(), "{:#x} is no function", r.entry);
        for why in &r.reasons {
            match why {
                Reason::Builds { written_at, text } => assert!(
                    built.found.iter().any(|g| g.built_by == r.entry
                        && g.written_at == *written_at
                        && g.text == *text),
                    "{why}"
                ),
                Reason::Calls { callee, name } => {
                    assert!(
                        callees.as_ref().is_some_and(|c| c.contains(callee)),
                        "{why}"
                    );
                    assert_eq!(
                        a.symbol_at(p, *callee)
                            .or_else(|| a.symbol_at(p, a.function(*callee)?.thunk?))
                            .map(|s| bare_name(&s.name)),
                        Some(name.as_str()),
                        "{why}"
                    );
                }
                Reason::Holds { at, .. } => {
                    assert_eq!(a.function_at(*at).map(|f| f.entry), Some(r.entry), "{why}");
                }
                Reason::References { strings, imports } => {
                    assert!(strings + imports >= 3, "{why}");
                }
            }
        }
    }
}

/// The fixture with its imports renamed to the injection surface lists its
/// callers for the calls, and every reason it gives is one the engine
/// holds.
#[test]
fn each_reason_on_the_reading_list_is_corroborated() {
    let mut p = fixture();
    for s in &mut p.symbols {
        s.name = s
            .name
            .replace("ExitProcess", "CreateRemoteThread")
            .replace("ReportAssertFailure", "WriteProcessMemory");
    }
    let a = Analysis::compute(&p);
    let triage = render::triage(&p, &a, &Overlay::default());
    corroborated(&p, &a, &triage);
    assert!(
        triage
            .read_first
            .iter()
            .flat_map(|r| &r.reasons)
            .any(|why| matches!(why, Reason::Calls { .. })),
        "{}",
        triage.spell()
    );
    let plain = fixture();
    let a = Analysis::compute(&plain);
    corroborated(&plain, &a, &render::triage(&plain, &a, &Overlay::default()));
}

/// Each reason says how it is known, and prints as the list has always
/// printed it.
#[test]
fn each_reason_says_how_it_is_known() {
    let cases = [
        (
            Reason::Builds {
                written_at: 0x10,
                text: "a\"b".to_owned(),
            },
            Basis::Observed,
            "builds \"a\\\"b\"",
        ),
        (
            Reason::Calls {
                callee: 0x20,
                name: "connect".to_owned(),
            },
            Basis::Static,
            "calls connect",
        ),
        (
            Reason::Holds {
                at: 0x30,
                name: "AES S-box",
                storage: Storage::Xored(0x5a),
            },
            Basis::Pattern,
            "holds AES S-box (xor 0x5a)",
        ),
        (
            Reason::References {
                strings: 4,
                imports: 2,
            },
            Basis::Static,
            "references 4 strings and 2 imports",
        ),
    ];
    for (why, basis, text) in cases {
        assert_eq!(why.basis(), basis, "{why}");
        assert_eq!(why.to_string(), text);
    }
}
