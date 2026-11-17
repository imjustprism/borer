//! A script run with no front end reads the resources the engine answers
//! as the engine answers them, page suffixes included.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::num::NonZeroUsize;
use std::sync::Arc;

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::answer::{Page, read};
use borer_engine::program::{Arch, Program, Section};
use borer_engine::script::run;

/// Builds a one-section x64 image at 0x1000 from `bytes`, padded to a page,
/// with its analysis.
///
/// # Arguments
///
/// * `bytes` - The section's first bytes.
fn image(mut bytes: Vec<u8>) -> (Arc<Program>, Arc<Analysis>) {
    bytes.resize(0x1000, 0xcc);
    let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
    let program = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text]);
    let analysis = Analysis::compute(&program);
    (Arc::new(program), Arc::new(analysis))
}

/// Says what a script printing `query(uri)` prints, and what the engine
/// answers for `core` read with `page`, as lines.
///
/// # Arguments
///
/// * `image` - The program and its analysis.
/// * `uri` - The URI the script queries, suffixes and all.
/// * `core` - The URI without its suffixes.
/// * `page` - The page the suffixes ask.
#[expect(clippy::expect_used, reason = "a failed read fails the test")]
fn both(
    (program, analysis): &(Arc<Program>, Arc<Analysis>),
    uri: &str,
    core: &str,
    page: Page<'_>,
) -> (Vec<String>, Vec<String>) {
    let code = format!(r#"print(query("{uri}"));"#);
    let ran = run(
        Arc::clone(program),
        Arc::clone(analysis),
        Arc::default(),
        &code,
        &[],
    )
    .expect("the query answers");
    let want = read(program, Some(analysis), &Overlay::default(), core, page)
        .expect("the engine answers it")
        .expect("it reads");
    let lines = want
        .strip_suffix('\n')
        .unwrap_or(&want)
        .split('\n')
        .map(str::to_owned)
        .collect();
    (ran.output, lines)
}

/// `!limit=` pages a listing the script queries, with or without a filter,
/// where it reached the filter as text.
#[test]
fn a_script_query_reads_its_page_suffixes() {
    let mut bytes = vec![0xc3; 0x10];
    for s in [
        "aHR0cHM6Ly9leGFtcGxlLmNvbS9maXJzdC9wYXRo",
        "aHR0cHM6Ly9leGFtcGxlLm9yZy9zZWNvbmQvcGF0aA==",
    ] {
        bytes.extend(s.as_bytes());
        bytes.push(0);
    }
    let image = image(bytes);
    let one = NonZeroUsize::new(1);
    for (uri, core) in [
        ("borer://encoded!limit=1", "borer://encoded"),
        ("borer://encoded/http!limit=1", "borer://encoded/http"),
    ] {
        let page = Page {
            offset: None,
            limit: one,
            again: uri,
        };
        let (ran, want) = both(&image, uri, core, page);
        assert_eq!(ran, want, "{uri}");
        assert!(want[0].starts_with("# showing "), "{uri}: {want:?}");
    }
}

/// The URI a `fieldrefs` page names for the next one reads in a script.
#[test]
fn a_script_query_reads_the_next_page_a_listing_names() {
    let mut bytes: Vec<u8> = std::iter::repeat_n([0x48u8, 0x8b, 0x41, 0x10], 250)
        .flatten()
        .collect();
    bytes.push(0xc3);
    let image = image(bytes);
    let core = "borer://fieldrefs/0x10";
    let page = Page {
        offset: Some(200),
        limit: None,
        again: core,
    };
    let (ran, want) = both(&image, "borer://fieldrefs/0x10!offset=200", core, page);
    assert_eq!(ran, want);
    assert!(
        want[0].starts_with("# 250 sites touch [reg+0x10], showing 50 from 200"),
        "{want:?}"
    );
}

/// With no front end, `help("query")` lists every resource the engine
/// answers, and a URI it does not answer is refused with the names nearest
/// it, where both pointed at the MCP server.
#[test]
fn a_script_with_no_front_end_names_what_it_reads() {
    let (program, analysis) = image(vec![0xc3; 0x10]);
    let script = |code: &str| {
        run(
            Arc::clone(&program),
            Arc::clone(&analysis),
            Arc::default(),
            code,
            &[],
        )
    };
    let help = script(r#"print(help("query"));"#)
        .map(|run| run.output.join("\n"))
        .unwrap_or_default();
    for name in borer_engine::answer::names() {
        assert!(
            help.contains(&format!("borer://{name}\n"))
                || help.ends_with(&format!("borer://{name}")),
            "{name}: {help}"
        );
    }
    let refused = script(r#"query("borer://triag");"#)
        .err()
        .unwrap_or_default();
    assert!(refused.contains("query is not available here"), "{refused}");
    assert!(refused.contains("nearest: borer://triage"), "{refused}");
}

/// With no front end, a script reads `find` and `stats` as the server
/// answered them: the search over every place a name or text lives, and a
/// chart series a page at a time.
#[test]
fn a_script_reads_find_and_stats_with_no_front_end() {
    use borer_engine::analysis::find::{Query, everywhere};
    use borer_engine::analysis::stats::stats_tsv;
    let mut bytes = vec![0xc3; 0x10];
    bytes.extend(b"decrypt the payload\0");
    let (program, analysis) = image(bytes);
    let o = Overlay::default();
    let lines = |text: &str| -> Vec<String> {
        text.strip_suffix('\n')
            .unwrap_or(text)
            .split('\n')
            .map(str::to_owned)
            .collect()
    };
    let stats = "borer://stats/entropy";
    for (uri, want) in [
        (
            "borer://find/crypt",
            everywhere(&program, &analysis, &o, &Query::parse("crypt"), usize::MAX).spell(),
        ),
        (
            stats,
            stats_tsv(
                &program,
                &analysis,
                "entropy",
                Page::whole(stats).window(200),
            )
            .expect("entropy reads"),
        ),
    ] {
        let ran = run(
            Arc::clone(&program),
            Arc::clone(&analysis),
            Arc::default(),
            &format!(r#"print(query("{uri}"));"#),
            &[],
        )
        .expect("the query answers");
        assert_eq!(ran.output, lines(&want), "{uri}");
    }
    assert!(
        lines(&everywhere(&program, &analysis, &o, &Query::parse("crypt"), usize::MAX).spell())
            .iter()
            .any(|l| l.contains("decrypt the payload")),
        "the needle is found"
    );
}
