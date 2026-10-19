//! The Itanium LSDA reader: `.eh_frame` FDEs whose CIE names an `L`
//! encoding carry each function's call-site table, and its landing pads are
//! walked as the function's own code.

use borer_engine::analysis::Analysis;
use borer_engine::program::{Arch, Program, Section};

/// Where the fixture's one function lives.
const FUNC: u64 = 0x1000;
/// Where the `.eh_frame` section lives.
const EH: u64 = 0x2000;
/// Where the LSDA sits inside `.eh_frame`.
const LSDA: u64 = 0x2100;
/// The one landing pad both call sites name, inside the function.
const PAD: u64 = FUNC + 0x40;

/// Builds a 64-bit image whose `.text` is one throwing function and whose
/// `.eh_frame` ties it to a two-call-site LSDA.
///
/// The CIE augments `zRL` with the FDE fields and the LSDA pointer both
/// `sdata4` absolute (R's encoding before L's in the data, the order of the
/// letters); the LSDA omits the landing-pad base, carries its type table as
/// `sdata4` absolute, and keeps the call-site table in `uleb`, the encoding
/// GCC and Clang ship most.
///
/// # Arguments
///
/// * `eh_frame` - Whether the image carries the `.eh_frame` section at all.
///
/// # Panics
///
/// When the fixture layout arithmetic overflows a conversion.
#[expect(
    clippy::expect_used,
    reason = "a fixture that does not parse has no useful recovery"
)]
pub(crate) fn throwing(eh_frame: bool) -> Program {
    let mut text: Vec<u8> = vec![0xcc; 0x100];
    text[0..5].copy_from_slice(&[0xbf, 0x07, 0x00, 0x00, 0x00]); // ASM: mov edi,7
    text[5..10].copy_from_slice(&[0xe8, 0x20, 0x00, 0x00, 0x00]); // ASM: call +0x20
    text[10..16].copy_from_slice(&[0x31, 0xc0, 0xc3, 0x90, 0x90, 0x90]); // ASM: xor eax,eax; ret
    let pad_off = usize::try_from(PAD - FUNC).expect("fits");
    text[pad_off..pad_off + 6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret

    let mut eh: Vec<u8> = Vec::new();
    let cie: Vec<u8> = vec![
        0x01, b'z', b'R', b'L', 0x00, 0x01, 0x78, 0x1b, 0x02, 0x0b, 0x0b, 0x00,
    ];
    eh.extend_from_slice(&u32::try_from(cie.len() + 4).expect("fits").to_le_bytes());
    eh.extend_from_slice(&0u32.to_le_bytes());
    eh.extend_from_slice(&cie);
    let fde_at = 4 + 4 + cie.len();
    let mut fde: Vec<u8> = Vec::new();
    let cie_ptr = u32::try_from(fde_at + 4).expect("fits");
    debug_assert_eq!(cie_ptr as usize, fde_at + 4);
    fde.extend_from_slice(&cie_ptr.to_le_bytes());
    fde.extend_from_slice(&i32::try_from(FUNC).expect("fits").to_le_bytes());
    fde.extend_from_slice(&16u32.to_le_bytes());
    fde.push(4);
    fde.extend_from_slice(&i32::try_from(LSDA).expect("fits").to_le_bytes());
    eh.extend_from_slice(&u32::try_from(fde.len()).expect("fits").to_le_bytes());
    eh.extend_from_slice(&fde);
    eh.resize(usize::try_from(LSDA - EH).expect("fits"), 0);
    let sites: [[u64; 4]; 2] = [[0, 0x10, 0x40, 1], [0x10, 0x10, 0x40, 0]];
    let mut table: Vec<u8> = Vec::new();
    for s in &sites {
        for v in s {
            table.push(u8::try_from(*v).expect("fits"));
        }
    }
    let actions: [u8; 4] = [0x01, 0x01, 0x00, 0x00];
    let lsda_len = 4 + 1 + table.len() + actions.len();
    let base = LSDA + u64::try_from(lsda_len + 4).expect("fits");
    let ttype_off = u8::try_from(base - (LSDA + 3)).expect("fits");
    eh.push(0xff);
    eh.push(0x0b);
    eh.push(ttype_off);
    eh.push(0x01);
    eh.push(u8::try_from(table.len()).expect("fits"));
    eh.extend_from_slice(&table);
    eh.extend_from_slice(&actions);
    eh.extend_from_slice(&i32::try_from(base).expect("fits").to_le_bytes());
    eh.extend_from_slice(&EH.to_le_bytes());
    eh.extend_from_slice(&(base + 16).to_le_bytes());
    eh.extend_from_slice(b"N3foo3BarE\0");

    let text_sec = Section::mapped(".text", FUNC, 0, 0x100, false, true);
    let mut bytes = text.clone();
    bytes.extend_from_slice(&eh);
    let mut sections = vec![text_sec];
    if eh_frame {
        sections.push(Section::mapped(
            ".eh_frame",
            EH,
            u64::try_from(text.len()).expect("fits"),
            u64::try_from(eh.len()).expect("fits"),
            false,
            false,
        ));
    }
    Program::raw(bytes, Arch::X86_64, 0, Some(FUNC), sections)
}

/// The FDE's LSDA pointer names the table, and its call sites come back as
/// facts: the guarded ranges, the shared landing pad, and what each pad
/// catches through its action chain.
///
/// # Panics
///
/// When the sites do not come back exactly as the table states them.
#[test]
fn the_lsda_call_sites_come_back_as_facts() {
    let p = throwing(true);
    let a = Analysis::compute(&p);
    let sites = a
        .throw_sites
        .get(&FUNC)
        .unwrap_or_else(|| panic!("no sites for {FUNC:#x}: {:?}", a.throw_sites));
    assert_eq!(sites.len(), 2, "{sites:?}");
    assert_eq!(sites[0].start, FUNC, "{sites:?}");
    assert_eq!(sites[0].end, FUNC + 0x10, "{sites:?}");
    assert_eq!(sites[0].landing_pad, Some(PAD), "{sites:?}");
    assert_eq!(sites[0].catches, ["foo::Bar"], "{sites:?}");
    assert!(
        sites[0].cleanup,
        "the chain's second entry cleans up: {sites:?}"
    );
    assert_eq!(sites[1].start, FUNC + 0x10, "{sites:?}");
    assert_eq!(sites[1].catches, Vec::<String>::new(), "{sites:?}");
    assert!(!sites[1].cleanup, "{sites:?}");
}

/// A landing pad is a label no instruction reaches, so discovery walks it as
/// the function's own root: the pad's code is a block of the function.
///
/// # Panics
///
/// When the pad is not discovered as code.
#[test]
fn a_landing_pad_is_walked_as_the_function_s_code() {
    let p = throwing(true);
    let a = Analysis::compute(&p);
    let f = a
        .function(FUNC)
        .unwrap_or_else(|| panic!("the function was not found"));
    assert!(
        f.blocks.iter().any(|b| b.start <= PAD && PAD < b.end),
        "the pad {PAD:#x} is no block of the function: {:?}",
        f.blocks
    );
}

/// A CIE without the `L` augmentation leaves its FDE with no LSDA, and a
/// program without `.eh_frame` answers no sites at all.
///
/// # Panics
///
/// When sites appear where the file carries none.
#[test]
fn no_lsda_augmentation_names_no_sites() {
    let mut p = throwing(true);
    let aug = 0x100 + 4 + 4 + 1;
    assert_eq!(p.bytes[aug], b'z');
    assert_eq!(p.bytes[aug + 2], b'L');
    p.bytes[aug + 2] = 0x00;
    let a = Analysis::compute(&p);
    assert!(a.throw_sites.is_empty(), "{:?}", a.throw_sites);
    let stripped = throwing(false);
    let a = Analysis::compute(&stripped);
    assert!(a.throw_sites.is_empty(), "{:?}", a.throw_sites);
}

/// A table whose landing pad leaves executable code is refused whole: none
/// of its sites are reported, the absence of facts over a guess.
///
/// # Panics
///
/// When a broken table still yields sites.
#[test]
fn a_landing_pad_outside_code_refuses_the_table() {
    let mut p = throwing(true);
    let lsda_off = 0x100 + usize::try_from(LSDA - EH).expect("fits");
    let table_body = lsda_off + 4 + 1;
    let pad_field = table_body + 2;
    assert_eq!(p.bytes[pad_field], 0x40, "the pad field moved");
    let text_len = p
        .sections
        .iter()
        .find(|s| s.name == ".text")
        .expect("the text section")
        .file_size;
    let total = text_len + 0x8000;
    let mut v = total;
    let mut uleb = Vec::new();
    loop {
        let mut b = u8::try_from(v & 0x7f).expect("fits");
        v >>= 7;
        if v != 0 {
            b |= 0x80;
        }
        uleb.push(b);
        if v == 0 {
            break;
        }
    }
    let eh = p
        .sections
        .iter_mut()
        .find(|s| s.name == ".eh_frame")
        .expect("the eh_frame section");
    let extra = uleb.len() as u64;
    eh.vsize += extra;
    eh.file_size += extra;
    p.bytes.resize(
        usize::try_from(eh.file_off.0 + eh.file_size).expect("fits"),
        0,
    );
    for (k, b) in uleb.iter().enumerate() {
        p.bytes[pad_field + k] = *b;
    }
    let a = Analysis::compute(&p);
    assert!(a.throw_sites.is_empty(), "{:?}", a.throw_sites);
}

/// The summary carries what a function's throw sites catch, where a reader
/// looks first.
///
/// # Panics
///
/// When the throws line is missing or wrong.
#[test]
fn the_summary_says_what_the_throw_sites_catch() {
    let p = throwing(true);
    let a = Analysis::compute(&p);
    let s = borer_engine::analysis::render::function_summary(
        &p,
        &a,
        &borer_engine::analysis::Overlay::default(),
        FUNC,
    )
    .unwrap_or_else(|| panic!("no summary for {FUNC:#x}"));
    assert!(
        s.contains("throws:   2 throw sites catch foo::Bar and clean up\n"),
        "{s}"
    );
}
