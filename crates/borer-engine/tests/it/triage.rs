//! The triage as values: each producer's first line is its summary, and
//! the summary keeps the addresses it is about.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{self, Summary};
use borer_engine::analysis::{Analysis, Overlay};
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
