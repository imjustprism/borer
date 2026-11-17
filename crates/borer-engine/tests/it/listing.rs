//! Every answer the engine gives read as a listing: the same bytes, its
//! rows counted by the engine's pager.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::answer::catalog::{RESOURCE_TEMPLATES, RESOURCES, example, resource_name};
use borer_engine::answer::{Listing, Suffixed, listing, names, read};
use borer_engine::program::{Arch, Program};

use crate::common::fixture;
use crate::raw::image;

/// The pages each URI is read at besides whole.
const PAGES: [&str; 2] = ["!limit=2", "!offset=1!limit=2"];

/// The programs the answers are read over, each with its analysis: the
/// shared fixture, one function reading a field, and the same bytes on an
/// architecture borer does not disassemble.
fn programs() -> Vec<(Program, Analysis)> {
    let code = [
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0xc3, // ASM: ret
    ];
    [
        fixture(),
        image(Arch::X86_64, &code, b"hello, listing\0"),
        image(Arch::Unknown, &code, &[]),
    ]
    .into_iter()
    .map(|p| {
        let a = Analysis::compute(&p);
        (p, a)
    })
    .collect()
}

/// Every URI of the catalog the engine answers, a template's filled from
/// the program ([`example`]).
///
/// # Arguments
///
/// * `p` - The program the examples are filled from.
fn uris(p: &Program) -> Vec<String> {
    let fixed = RESOURCES.iter().map(|r| r.0.to_owned());
    let templated = RESOURCE_TEMPLATES.iter().map(|t| example(t.2, Some(p)));
    fixed
        .chain(templated)
        .filter(|uri| names().any(|n| n == resource_name(uri)))
        .collect()
}

/// Reads a URI as [`read`] does, its suffixes read off first.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `uri` - The URI, suffixes and all.
///
/// # Errors
///
/// The refusal of a suffix or of the read.
fn text(p: &Program, a: &Analysis, uri: &str) -> Result<String, String> {
    let asked = Suffixed::read(uri)?;
    let again = asked.again();
    read(
        p,
        Some(a),
        &Overlay::default(),
        asked.core,
        asked.page(&again),
    )
    .expect("the engine answers it")
}

/// Reads a URI as a listing.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `uri` - The URI, suffixes and all.
///
/// # Errors
///
/// The refusal of a suffix or of the read.
fn listed(p: &Program, a: &Analysis, uri: &str) -> Result<Listing, String> {
    listing(p, Some(a), &Overlay::default(), uri)
}

/// A listing spells the text `read` gives byte for byte, whole and paged,
/// and refuses what `read` refuses with the same sentence; every resource
/// the engine answers is read.
#[test]
fn every_answer_spells_its_listing_back() {
    let mut reached = std::collections::BTreeSet::new();
    for (p, a) in programs() {
        for uri in uris(&p) {
            reached.insert(resource_name(&uri).to_owned());
            for paged in std::iter::once(String::new()).chain(PAGES.map(str::to_owned)) {
                let asked = format!("{uri}{paged}");
                let spelled = listed(&p, &a, &asked).map(|l| l.spell().to_owned());
                assert_eq!(spelled, text(&p, &a, &asked), "{asked}");
            }
        }
    }
    for name in names() {
        assert!(reached.contains(name), "no URI reaches borer://{name}");
    }
}

/// A paged answer's total is the number of rows its pages hold when read
/// one after another to the end, and some answer read has more rows than
/// one page shows.
#[test]
fn a_listing_total_is_the_pagers_count() {
    let mut longer = 0;
    for (p, a) in programs() {
        for uri in uris(&p) {
            let Ok(Some(total)) = listed(&p, &a, &format!("{uri}!limit=1")).map(|l| l.total())
            else {
                continue;
            };
            let mut rows = 0;
            for _ in 0..=total {
                let page = listed(&p, &a, &format!("{uri}!offset={rows}!limit=2"))
                    .expect("a page of an answer that paged reads");
                assert_eq!(page.total(), Some(total), "{uri} from {rows}");
                if page.is_empty() {
                    break;
                }
                rows += page.len();
            }
            assert_eq!(rows, total, "{uri}");
            longer += usize::from(total > 1);
        }
    }
    assert!(longer > 0, "no paged answer has two rows");
}

/// What a renderer writes in a place cell that holds no address: nothing,
/// or `-`.
const EMPTY_MARKS: [&str; 2] = ["", "-"];

/// How a renderer writes bytes no section maps, by their file offset
/// (`off=0x2bc00`), which is no address to go to.
const OFF: &str = "off=";

/// Every cell of a place an answer states is an address inside a section
/// the program maps, or an empty mark, or bytes no section maps; and some
/// stated cell read is an address.
#[test]
fn every_stated_place_is_an_address_the_program_maps() {
    let mut addresses = 0;
    for (p, a) in programs() {
        for uri in uris(&p) {
            let Ok(l) = listed(&p, &a, &uri) else {
                continue;
            };
            for row in 0..l.len() {
                for &at in l.places() {
                    if let Some(va) = l.place(row, at) {
                        assert!(p.section_at(va).is_some(), "{uri} row {row}: {va:#x}");
                        addresses += 1;
                        continue;
                    }
                    let cell = l.cell(row, at).unwrap_or_default();
                    assert!(
                        EMPTY_MARKS.contains(&cell) || cell.starts_with(OFF),
                        "{uri} row {row} {at:?}: {cell:?}"
                    );
                }
            }
        }
    }
    assert!(addresses > 0, "no stated place holds an address");
}
