//! Mach-O fixups applied to the image.
//!
//! A chained-fixups image holds each pointer as its encoding: a rebase
//! reads as its target once applied, the target is discovered and the slot
//! is its cross-reference; a bind names its slot after the import and
//! reads zero; an arm64e pointer reads with its authentication bits
//! stripped. The older dyld info opcodes rebase and bind the same way, a
//! lazy pointer's slot going to its bind. A hostile table is cut and
//! counted, never followed into a panic or a hang.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use crate::machogen::{self, ARM64, CODE, PIE, R, RW, RX, Sect, Seg, Starts, X86_64};
use borer_engine::analysis::render::xrefs_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Program, SymbolKind};

/// Where `__TEXT` is mapped: the image base.
const TEXT: u64 = 0x1_0000_0000;
/// The entry: `xor eax, eax; ret` (x86-64) or `ret` (arm64).
const MAIN: u64 = TEXT + 0x400;
/// Reached only through a rebased slot: `mov eax, 42; ret`.
const TABLED: u64 = TEXT + 0x410;
/// Where the data segment is mapped.
const DATA: u64 = TEXT + 0x1000;
/// `LC_DYLD_CHAINED_FIXUPS`.
const LC_DYLD_CHAINED_FIXUPS: u32 = 0x8000_0034;
/// `DYLD_CHAINED_PTR_64_OFFSET`.
const PTR_64_OFFSET: u16 = 6;
/// `DYLD_CHAINED_PTR_ARM64E`.
const PTR_ARM64E: u16 = 1;

/// A `DYLD_CHAINED_PTR_64_OFFSET` rebase word.
///
/// # Arguments
///
/// * `target` - The target's offset from the image base.
/// * `next` - The next word's distance in 4-byte strides.
fn rebase64(target: u64, next: u64) -> u64 {
    target | (next << 51)
}

/// A `DYLD_CHAINED_PTR_64` bind word.
///
/// # Arguments
///
/// * `ordinal` - The import's index.
/// * `next` - The next word's distance in 4-byte strides.
fn bind64(ordinal: u64, next: u64) -> u64 {
    ordinal | (next << 51) | (1 << 63)
}

/// The image's `__TEXT`: the header's room, then x86-64 code at [`MAIN`]
/// and [`TABLED`].
fn x86_text() -> Seg {
    let mut bytes = vec![0u8; 0x1000];
    bytes[0x400..0x403].copy_from_slice(&[0x31, 0xc0, 0xc3]); // ASM: xor eax, eax; ret
    bytes[0x410..0x416].copy_from_slice(&[0xb8, 0x2a, 0, 0, 0, 0xc3]); // ASM: mov eax, 42; ret
    Seg {
        name: "__TEXT",
        vmaddr: TEXT,
        fileoff: 0,
        bytes,
        prot: RX,
        sections: vec![Sect {
            name: "__text",
            addr: MAIN,
            size: 0x20,
            flags: CODE,
        }],
    }
}

/// A data segment at [`DATA`] holding `words` from its start in one
/// `__const` section.
///
/// # Arguments
///
/// * `name` - The segment's name.
/// * `len` - Its size in bytes.
/// * `words` - `(offset, word)` pairs.
fn data(name: &'static str, len: usize, words: &[(usize, u64)]) -> Seg {
    let mut bytes = vec![0u8; len];
    for (at, w) in words {
        bytes[*at..at + 8].copy_from_slice(&w.to_le_bytes());
    }
    Seg {
        name,
        vmaddr: DATA,
        fileoff: 0x1000,
        bytes,
        prot: RW,
        sections: vec![Sect {
            name: "__const",
            addr: DATA,
            size: u64::try_from(len).expect("fits"),
            flags: 0,
        }],
    }
}

/// `__LINKEDIT` holding `payload`, mapped well past the data.
///
/// # Arguments
///
/// * `at` - Its file offset.
/// * `payload` - Its bytes.
fn linkedit(at: u64, payload: Vec<u8>) -> Seg {
    Seg {
        name: "__LINKEDIT",
        vmaddr: TEXT + 0x10_0000 + at,
        fileoff: at,
        bytes: payload,
        prot: R,
        sections: Vec::new(),
    }
}

/// Builds and loads a PIE.
///
/// # Arguments
///
/// * `cpu` - The CPU type.
/// * `segs` - The segments.
/// * `extra` - The load commands past the segments and `LC_MAIN`.
fn load(cpu: u32, segs: &[Seg], extra: Vec<Vec<u8>>) -> Program {
    let mut commands = vec![
        machogen::main(MAIN - TEXT),
        machogen::dylib("/usr/lib/libSystem.B.dylib"),
    ];
    commands.extend(extra);
    let bytes = machogen::build(cpu, PIE, segs, &commands);
    Program::from_bytes(PathBuf::from("fixups.macho"), bytes).expect("the image loads")
}

/// Builds an x86-64 PIE whose chained fixups are `payload`, with the
/// data segment holding `words`.
///
/// # Arguments
///
/// * `data_len` - The data segment's size.
/// * `words` - The data segment's words.
/// * `payload` - The `LC_DYLD_CHAINED_FIXUPS` payload.
/// * `stated` - The payload size the command states, `None` for its own.
fn chained_x86(
    data_len: usize,
    words: &[(usize, u64)],
    payload: Vec<u8>,
    stated: Option<usize>,
) -> Program {
    let at = 0x1000 + u64::try_from(data_len).expect("fits");
    let size = stated.unwrap_or(payload.len());
    load(
        X86_64,
        &[
            x86_text(),
            data("__DATA_CONST", data_len, words),
            linkedit(at, payload),
        ],
        vec![machogen::linkedit(LC_DYLD_CHAINED_FIXUPS, at, size)],
    )
}

/// Reads the word at `va` as the image holds it.
///
/// # Arguments
///
/// * `p` - The program.
/// * `va` - The word's address.
fn word(p: &Program, va: u64) -> u64 {
    let b = p.read_va(va, 8).expect("the word is mapped");
    u64::from_le_bytes(b.try_into().expect("eight bytes"))
}

/// The slots named after `name`, as imports.
///
/// # Arguments
///
/// * `p` - The program.
/// * `name` - The import's name.
fn import_slots(p: &Program, name: &str) -> Vec<u64> {
    p.symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.name == name)
        .map(|s| s.addr)
        .collect()
}

/// A chained rebase reads as its target, which is discovered and xref'd.
///
/// The `64_OFFSET` slot read as its encoding on disk, `0x...410`, which no
/// section maps, so nothing pointed at the function and nothing found it.
/// The bind after it in the chain names its slot `malloc` and reads zero.
#[test]
fn a_chained_rebase_reads_as_its_target_and_a_bind_names_its_slot() {
    let payload = machogen::chained(
        3,
        &[Starts {
            segment: 1,
            format: PTR_64_OFFSET,
            offset: DATA - TEXT,
            page_size: 0x1000,
            pages: vec![0],
        }],
        &[(1, false, "_malloc")],
    );
    let p = chained_x86(
        0x20,
        &[(0, rebase64(0x410, 2)), (8, bind64(0, 0))],
        payload,
        None,
    );
    assert_eq!(word(&p, DATA), TABLED);
    assert_eq!(
        word(&p, DATA + 8),
        0,
        "a bind reads as the address the image cannot know"
    );
    assert_eq!(
        p.bytes[0x1000..0x1008],
        rebase64(0x410, 2).to_le_bytes(),
        "the file's own bytes stay as they were read"
    );
    assert_eq!(import_slots(&p, "malloc"), vec![DATA + 8]);
    assert_eq!(p.relocated_words(), vec![DATA]);
    let a = Analysis::compute(&p);
    assert!(
        a.function(TABLED).is_some(),
        "{:#x?}",
        a.functions.iter().map(|f| f.entry).collect::<Vec<_>>()
    );
    let xrefs = xrefs_tsv(&p, &a, &Overlay::default(), TABLED, 0, 50, false);
    assert!(xrefs.contains(&format!("-: {DATA:#x} ")), "{xrefs}");
    let summary = p.summary();
    assert!(
        summary.contains(
            "fixups:  1 rebase(s) and 1 bind(s) applied to the image (chained fixups, DYLD_CHAINED_PTR_64_OFFSET)\n"
        ),
        "{summary}"
    );
}

/// An arm64e chain: an authenticated rebase reads as the image base plus
/// its offset with its key and diversity stripped, a plain rebase as the
/// address it holds, and an authenticated bind names its slot.
#[test]
fn arm64e_pointers_read_with_their_authentication_stripped() {
    /// A `ret`, the arm64 entry.
    const RET: u32 = 0xd65f_03c0;
    let auth_rebase = 0x400 | (0x1234 << 32) | (1 << 48) | (2 << 49) | (1 << 51) | (1 << 63);
    let rebase = (TEXT + 0x404) | (1 << 51);
    let auth_bind = (0x5678 << 32) | (1 << 62) | (1 << 63);
    let mut text = x86_text();
    text.bytes[0x400..0x404].copy_from_slice(&RET.to_le_bytes());
    text.bytes[0x404..0x408].copy_from_slice(&RET.to_le_bytes());
    let payload = machogen::chained(
        3,
        &[Starts {
            segment: 1,
            format: PTR_ARM64E,
            offset: DATA - TEXT,
            page_size: 0x4000,
            pages: vec![0],
        }],
        &[(1, false, "_free")],
    );
    let at = 0x1020;
    let p = load(
        ARM64,
        &[
            text,
            data(
                "__DATA_CONST",
                0x20,
                &[(0, auth_rebase), (8, rebase), (16, auth_bind)],
            ),
            linkedit(at, payload.clone()),
        ],
        vec![machogen::linkedit(
            LC_DYLD_CHAINED_FIXUPS,
            at,
            payload.len(),
        )],
    );
    assert_eq!(word(&p, DATA), TEXT + 0x400);
    assert_eq!(word(&p, DATA + 8), TEXT + 0x404);
    assert_eq!(word(&p, DATA + 16), 0);
    assert_eq!(import_slots(&p, "free"), vec![DATA + 16]);
    assert_eq!(p.relocated_words(), vec![DATA, DATA + 8]);
    let summary = p.summary();
    assert!(
        summary.contains(
            "fixups:  2 rebase(s) and 1 bind(s) applied to the image (chained fixups, DYLD_CHAINED_PTR_ARM64E); 2 authenticated\n"
        ),
        "{summary}"
    );
}

/// A firmware-style image lists its chain starts in a `__chain_starts`
/// section rather than a load command, and its chains apply the same.
#[test]
fn a_chain_starts_section_applies_its_chains() {
    /// `DYLD_CHAINED_PTR_64`, whose target is an address.
    const PTR_64: u64 = 2;
    let mut text = x86_text();
    let starts = [PTR_64, 1, DATA - TEXT];
    for (k, v) in starts.into_iter().enumerate() {
        let v = u32::try_from(v).expect("fits");
        text.bytes[0x800 + 4 * k..0x804 + 4 * k].copy_from_slice(&v.to_le_bytes());
    }
    text.sections.push(Sect {
        name: "__chain_starts",
        addr: TEXT + 0x800,
        size: 12,
        flags: 0,
    });
    let p = load(
        X86_64,
        &[
            text,
            data("__DATA_CONST", 0x20, &[(0, TABLED | (2 << 51)), (8, MAIN)]),
        ],
        Vec::new(),
    );
    assert_eq!(word(&p, DATA), TABLED);
    assert_eq!(word(&p, DATA + 8), MAIN);
    assert!(
        p.summary().contains(
            "fixups:  2 rebase(s) and 0 bind(s) applied to the image (chained fixups, DYLD_CHAINED_PTR_64)\n"
        ),
        "{}",
        p.summary()
    );
}

/// A hostile table is cut where it goes wrong, counted, and the load goes
/// on.
///
/// A chain only moves forward, so the one way round is a page start into
/// a chain another start walked: it is refused at the first word walked
/// twice. A chain stepping past its segment, a page start the 64-bit
/// formats never use, a page start past the segment's bytes, an absurd
/// segment count, an absurd import count and a payload past the end of
/// the file each count as refused, and the sound words still apply.
#[test]
fn a_hostile_chain_is_refused_cleanly() {
    let starts = Starts {
        segment: 1,
        format: PTR_64_OFFSET,
        offset: DATA - TEXT,
        page_size: 0x1000,
        pages: vec![0x1000, 0, 0x8001, 0xffff, 0x0ff8],
    };
    let words = [
        (0x1000, rebase64(0x410, 2)),
        (0x1008, rebase64(0x400, 0xfff)),
    ];
    let payload = machogen::chained(3, &[starts], &[]);
    let p = chained_x86(0x2000, &words, payload.clone(), None);
    assert_eq!(word(&p, DATA + 0x1000), TABLED);
    assert_eq!(word(&p, DATA + 0x1008), MAIN);
    assert_eq!(p.relocated_words(), vec![DATA + 0x1000, DATA + 0x1008]);
    let summary = p.summary();
    assert!(
        summary.contains("fixups:  2 rebase(s) and 0 bind(s) applied to the image (chained fixups, DYLD_CHAINED_PTR_64_OFFSET); 4 refused ("),
        "the chain past its segment, the page start into a walked chain, the multi-start page and the page past the bytes: {summary}"
    );
    Analysis::compute(&p);

    let mut absurd = payload.clone();
    absurd[32..36].copy_from_slice(&u32::MAX.to_le_bytes());
    absurd[16..20].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
    let p = chained_x86(0x2000, &words, absurd, None);
    assert_eq!(
        word(&p, DATA + 0x1000),
        TABLED,
        "the segments the table holds still apply"
    );
    assert!(p.summary().contains(" refused ("), "{}", p.summary());
    Analysis::compute(&p);

    let p = chained_x86(0x2000, &words, payload, Some(0x10_0000));
    assert_eq!(
        word(&p, DATA + 0x1000),
        rebase64(0x410, 2),
        "nothing applies"
    );
    assert!(
        p.summary().contains("fixups:  0 rebase(s) and 0 bind(s) applied to the image (chained fixups, no pointer format read); 1 refused ("),
        "{}",
        p.summary()
    );
    Analysis::compute(&p);
}

/// The dyld info opcodes rebase and bind as the chains do.
///
/// A rebased word, which already holds its target, is a pointer whose
/// target is discovered; a bound slot is named after its import; a lazy
/// pointer, rebased and lazily bound both, goes to its bind without a
/// refusal.
#[test]
fn dyld_info_opcodes_rebase_and_bind() {
    let rebase: Vec<u8> = vec![0x11, 0x21, 0x00, 0x51, 0x41, 0x51, 0x00];
    let mut bind: Vec<u8> = vec![0x11, 0x40];
    bind.extend_from_slice(b"_free\0");
    bind.extend_from_slice(&[0x51, 0x71, 0x08, 0x90, 0x00]);
    let mut lazy: Vec<u8> = vec![0x71, 0x10, 0x11, 0x40];
    lazy.extend_from_slice(b"_puts\0");
    lazy.extend_from_slice(&[0x90, 0x00]);
    let at = 0x1020u64;
    let mut payload = rebase.clone();
    payload.extend_from_slice(&bind);
    payload.extend_from_slice(&lazy);
    let rebase_at = (at, rebase.len());
    let bind_at = (at + u64::try_from(rebase.len()).expect("fits"), bind.len());
    let lazy_at = (
        bind_at.0 + u64::try_from(bind.len()).expect("fits"),
        lazy.len(),
    );
    let p = load(
        X86_64,
        &[
            x86_text(),
            data("__DATA", 0x20, &[(0, TABLED), (0x10, MAIN)]),
            linkedit(at, payload),
        ],
        vec![machogen::dyld_info(rebase_at, bind_at, lazy_at)],
    );
    assert_eq!(p.relocated_words(), vec![DATA]);
    assert_eq!(import_slots(&p, "free"), vec![DATA + 8]);
    assert_eq!(import_slots(&p, "puts"), vec![DATA + 0x10]);
    assert_eq!(
        word(&p, DATA + 0x10),
        MAIN,
        "an opcode bind leaves the word the file holds"
    );
    let summary = p.summary();
    assert!(
        summary.contains(
            "fixups:  1 rebase(s) and 2 bind(s) applied to the image (dyld info opcodes); 1 lazy\n"
        ),
        "{summary}"
    );
    let a = Analysis::compute(&p);
    assert!(a.function(TABLED).is_some());
}
