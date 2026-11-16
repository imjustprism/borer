//! The triage as values: each producer's first line is its summary, the
//! report is spelled from the summaries, and each reason it gives to read
//! a function is one the engine holds.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{
    self, Basis, Packer, Packing, Reason, Resistance, SectionKind, Summary,
};
use borer_engine::analysis::{Analysis, Overlay, bare_name};
use borer_engine::crypto::Storage;
use borer_engine::program::{Arch, Program};

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
        if s.kind == SectionKind::Crypto {
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

/// A string built from a block seed is credited to its function.
///
/// A generator whose entry branches past its mixer is recovered by a run
/// from the mixer's block, so the reading list names the function once and
/// never the block.
#[test]
fn a_string_built_from_a_block_seed_is_credited_to_its_function() {
    let code = [
        0x48, 0x81, 0xf9, 0x34, 0x12, 0x00, 0x00, // ASM: cmp rcx, 0x1234
        0x75, 0x19, // ASM: jne 0x401022
        0x48, 0xb8, 0x15, 0x7c, 0x4a, 0x7f, 0xb9, 0x79, 0x37,
        0x9e, // ASM: mov rax, golden gamma
        0x48, 0xb8, b's', b'e', b'c', b'r', b'e', b't', b'!',
        b'!', // ASM: mov rax, "secret!!"
        0x48, 0x89, 0x44, 0x24, 0xf0, // ASM: mov [rsp-0x10], rax
        0xc3, // ASM: ret
    ];
    let p = crate::raw::image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let built = render::generated_strings(&p, &a, "");
    assert!(
        built
            .found
            .iter()
            .any(|g| g.text == "secret!!" && g.built_by == 0x401000),
        "{:?}",
        built.found
    );
    assert!(built.found.iter().all(|g| a.function(g.built_by).is_some()));
    let hidden = render::hidden_strings_tsv(&p, &a, &Overlay::default(), "");
    let said = hidden
        .strip_prefix("# ")
        .and_then(|l| l.split(' ').next())
        .and_then(|n| n.parse::<usize>().ok());
    assert_eq!(
        Some(render::generated_summary(&p, &a).count),
        said,
        "{hidden}"
    );
    let triage = render::triage(&p, &a, &Overlay::default());
    assert!(
        triage
            .read_first
            .iter()
            .all(|r| a.function(r.entry).is_some()),
        "{}",
        triage.spell()
    );
    assert_eq!(
        triage
            .read_first
            .iter()
            .filter(|r| r.entry == 0x401000)
            .count(),
        1,
        "{}",
        triage.spell()
    );
}

/// Most check rows the checks listing names, as its own constant says.
const CHECK_ROWS: usize = 200;

/// Returns an image of `n` functions that each mention `bad serial number`
/// and compare against a telling constant, all called from the entry.
///
/// # Arguments
///
/// * `n` - Check functions, at most 0x100 a page of code holds twice.
fn many_checks(n: u32) -> Program {
    /// Where the check functions start.
    const FIRST: u32 = 0x40_1400;
    /// Bytes each check function takes.
    const EACH: u32 = 16;
    /// Where the phrase sits.
    const PHRASE: u32 = 0x40_3000;
    let mut bytes = vec![0xccu8; 0x3000];
    for i in 0..n {
        let call = usize::try_from(i * 5).unwrap_or(0);
        let next = 0x40_1000 + i * 5 + 5;
        let f = FIRST + i * EACH;
        bytes[call] = 0xe8;
        bytes[call + 1..call + 5].copy_from_slice(&(f - next).to_le_bytes());
        let at = usize::try_from(f - 0x40_1000).unwrap_or(0);
        let lea = PHRASE - (f + 7);
        bytes[at..at + 3].copy_from_slice(&[0x48, 0x8d, 0x05]);
        bytes[at + 3..at + 7].copy_from_slice(&lea.to_le_bytes());
        bytes[at + 7..at + 13].copy_from_slice(&[0x81, 0xf9, 0x44, 0x43, 0x42, 0x41]);
        bytes[at + 13] = 0xc3;
    }
    bytes[usize::try_from(n * 5).unwrap_or(0)] = 0xc3;
    let phrase = b"bad serial number\0";
    bytes[0x2000..0x2000 + phrase.len()].copy_from_slice(phrase);
    Program::raw(
        bytes,
        Arch::X86_64,
        0x40_0000,
        Some(0x40_1000),
        vec![
            borer_engine::program::Section::mapped(".text", 0x40_1000, 0, 0x2000, false, true),
            borer_engine::program::Section::mapped(
                ".rdata", 0x40_3000, 0x2000, 0x1000, false, false,
            ),
        ],
    )
}

/// More checks than the listing names are all counted, in the headline
/// and the summary alike, and the listing says how many it left out.
#[test]
fn the_checks_headline_counts_every_check() {
    let p = many_checks(201);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let s = render::license_checks_summary(&p, &a, &o);
    assert!(s.count > CHECK_ROWS, "{s:?}");
    assert_eq!(s.at.len(), render::SUMMARY_AT_MAX, "{s:?}");
    assert_eq!(s.at_total, s.count, "{s:?}");
    assert!(
        s.headline
            .starts_with(&format!("{} functions judge", s.count)),
        "{s:?}"
    );
    assert!(
        render::license_checks_tsv(&p, &a, &o).contains("checks not listed"),
        "{s:?}"
    );
}

/// Returns the protection and anti-analysis verdicts the triage holds.
///
/// # Arguments
///
/// * `triage` - The triage.
fn verdicts(triage: &render::Triage) -> (Option<Packing>, Option<Resistance>) {
    let mut found = (None, None);
    for s in &triage.sections {
        match &s.kind {
            SectionKind::Protection(packing) => found.0 = Some(packing.clone()),
            SectionKind::AntiAnalysis(resistance) => found.1 = Some(*resistance),
            SectionKind::Crypto
            | SectionKind::DynamicImports
            | SectionKind::Checks
            | SectionKind::GeneratedStrings
            | SectionKind::Capabilities(_)
            | SectionKind::Iocs => {}
        }
    }
    found
}

/// A protector named by its sections is a typed verdict, a plain image's
/// is plain, and each section line is spelled from its verdict.
#[test]
fn the_protection_verdict_is_a_value() {
    use crate::protection::{data, pe, sec};
    let mut code = vec![0xcc; 0x200];
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let vmp = pe(
        &[
            data(".vmp0", 0x1000, vec![0x41; 0x200]),
            sec(".vmp1", 0x3000, code.clone()),
        ],
        0x3000,
    );
    let plain = pe(&[sec(".text", 0x1000, code)], 0x1000);
    for (bytes, protected) in [(vmp, true), (plain, false)] {
        let p = Program::from_bytes(std::path::PathBuf::from("v.exe"), bytes)
            .unwrap_or_else(|e| panic!("a PE loads: {e}"));
        spelled_from_values(&p);
        let a = Analysis::compute(&p);
        let triage = render::triage(&p, &a, &Overlay::default());
        let (packing, resistance) = verdicts(&triage);
        let packing = packing.unwrap_or_else(|| panic!("no protection section"));
        if protected {
            assert_eq!(
                packing,
                Packing::Protected(vec![Packer::Named("VMProtect")])
            );
        } else {
            assert!(
                matches!(
                    packing,
                    Packing::Plain | Packing::PlainWeak | Packing::PlainOneMark
                ),
                "{packing:?}"
            );
        }
        assert_eq!(
            first_line(&render::protection_tsv(&p, &a)),
            packing.to_string()
        );
        let resistance = resistance.unwrap_or_else(|| panic!("no anti-analysis section"));
        assert_eq!(
            render::anti_analysis_summary(&p, &a).headline,
            resistance.to_string()
        );
    }
}

/// The capability map holds its note and its rows as values, and its text
/// is the two spelled under its first line.
#[test]
fn the_capability_map_is_its_note_and_rows() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let triage = render::triage(&p, &a, &Overlay::default());
    let Some(map) = triage.sections.iter().find_map(|s| {
        if let SectionKind::Capabilities(map) = &s.kind {
            Some(map)
        } else {
            None
        }
    }) else {
        panic!("no capabilities section");
    };
    assert!(
        map.note.is_some_and(|n| n.starts_with("few imports")),
        "{map:?}"
    );
    assert!(map.rows.iter().all(|r| !r.named.is_empty()), "{map:?}");
    let mut expected = format!("# {}\n", render::capability_summary(&p, Some(&a)).headline);
    for line in map
        .note
        .map(|n| format!("# {n}"))
        .into_iter()
        .chain(map.rows.iter().map(ToString::to_string))
    {
        expected.push_str(&line);
        expected.push('\n');
    }
    assert_eq!(render::capability_map_tsv(&p, Some(&a)), expected);
}
