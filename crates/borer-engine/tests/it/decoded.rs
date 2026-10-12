//! `borer://decoded` over hand-built images.
//!
//! A single-byte XOR decoder and a rolling-key decoder, each called from
//! five sites with planted ciphertext, recover all ten strings with their
//! sites; a `memcpy`-like copier called the same way yields nothing; and a
//! decoder fed a runaway length is stopped by the step budget.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::decoded_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section};

/// Where data is linked.
const DATA: u64 = 0x2000;

/// An in-place single-byte XOR decoder: `rcx` buffer, `rdx` length, key
/// `0x5a`.
const XOR_DECODE: &[u8] = &[
    0x48, 0x85, 0xd2, // ASM: test rdx, rdx
    0x74, 0x15, // ASM: je ret
    0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
    0x42, 0x8a, 0x04, 0x01, // ASM: mov al, [rcx+r8]
    0x34, 0x5a, // ASM: xor al, 0x5a
    0x42, 0x88, 0x04, 0x01, // ASM: mov [rcx+r8], al
    0x49, 0xff, 0xc0, // ASM: inc r8
    0x49, 0x39, 0xd0, // ASM: cmp r8, rdx
    0x72, 0xee, // ASM: jb loop
    0xc3, // ASM: ret
];

/// An in-place rolling-key decoder: `rcx` buffer, `rdx` length, key `0x11`
/// stepping by `0x07` each byte.
const ROLL_DECODE: &[u8] = &[
    0x48, 0x85, 0xd2, // ASM: test rdx, rdx
    0x74, 0x1d, // ASM: je ret
    0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
    0x41, 0xb1, 0x11, // ASM: mov r9b, 0x11
    0x42, 0x8a, 0x04, 0x01, // ASM: mov al, [rcx+r8]
    0x44, 0x30, 0xc8, // ASM: xor al, r9b
    0x42, 0x88, 0x04, 0x01, // ASM: mov [rcx+r8], al
    0x41, 0x80, 0xc1, 0x07, // ASM: add r9b, 0x07
    0x49, 0xff, 0xc0, // ASM: inc r8
    0x49, 0x39, 0xd0, // ASM: cmp r8, rdx
    0x72, 0xe9, // ASM: jb loop
    0xc3, // ASM: ret
];

/// A `memcpy`-like copier: `rcx` destination, `rdx` source, `r8` length.
const COPY: &[u8] = &[
    0x4d, 0x85, 0xc0, // ASM: test r8, r8
    0x74, 0x13, // ASM: je ret
    0x45, 0x31, 0xc9, // ASM: xor r9d, r9d
    0x42, 0x8a, 0x04, 0x0a, // ASM: mov al, [rdx+r9]
    0x42, 0x88, 0x04, 0x09, // ASM: mov [rcx+r9], al
    0x49, 0xff, 0xc1, // ASM: inc r9
    0x4d, 0x39, 0xc1, // ASM: cmp r9, r8
    0x72, 0xf0, // ASM: jb loop
    0xc3, // ASM: ret
];

/// Emits `mov ecx, rcx; mov edx, rdx; call target` into `code`, the bytes
/// so far placed at `base`, computing the call displacement.
fn site2(code: &mut Vec<u8>, base: u64, rcx: u32, rdx: u32, target: u64) {
    code.push(0xb9);
    code.extend(rcx.to_le_bytes());
    code.push(0xba);
    code.extend(rdx.to_le_bytes());
    emit_call(code, base, target);
}

/// Emits `mov ecx, rcx; mov edx, rdx; mov r8d, r8; call target`.
fn site3(code: &mut Vec<u8>, base: u64, rcx: u32, rdx: u32, r8: u32, target: u64) {
    code.push(0xb9);
    code.extend(rcx.to_le_bytes());
    code.push(0xba);
    code.extend(rdx.to_le_bytes());
    code.extend([0x41, 0xb8]);
    code.extend(r8.to_le_bytes());
    emit_call(code, base, target);
}

/// Emits `call target` (E8 rel32) at the current end of `code`.
fn emit_call(code: &mut Vec<u8>, base: u64, target: u64) {
    code.push(0xe8);
    let next = base + u64::try_from(code.len()).expect("small") + 4;
    let disp = i64::try_from(target).expect("va") - i64::try_from(next).expect("va");
    code.extend(i32::try_from(disp).expect("near call").to_le_bytes());
}

/// Places `body` at `va` in `bytes` and records its function range; the
/// image maps each section at a file offset equal to its address.
fn place(bytes: &mut [u8], ranges: &mut Vec<(u64, u64)>, va: u64, body: &[u8]) {
    data(bytes, va, body);
    ranges.push((va, va + u64::try_from(body.len()).expect("small")));
}

/// Writes `payload` into the image at the offset equal to `va`.
fn data(bytes: &mut [u8], va: u64, payload: &[u8]) {
    let off = usize::try_from(va).expect("va");
    bytes[off..off + payload.len()].copy_from_slice(payload);
}

/// The five plaintexts a decoder of `tag` hides.
fn plaintexts(tag: &str) -> Vec<String> {
    (1..=5)
        .map(|i| format!("http://{tag}{i}.test/c2"))
        .collect()
}

/// An image with an XOR decoder, a rolling-key decoder and a copier, each
/// called from five sites, with the ciphertext each site decodes planted.
fn decoders_image() -> Program {
    let mut bytes = vec![0xccu8; 0x3000];
    let mut ranges: Vec<(u64, u64)> = Vec::new();
    place(&mut bytes, &mut ranges, 0x1000, XOR_DECODE);
    place(&mut bytes, &mut ranges, 0x1100, ROLL_DECODE);
    place(&mut bytes, &mut ranges, 0x1200, COPY);

    // The XOR decoder's five ciphertexts at 0x2000, 0x20 apart; each byte is
    // the plaintext byte XOR 0x5a. The caller at 0x1300 decodes each.
    let xor = plaintexts("xor");
    let mut caller = Vec::new();
    for (i, text) in xor.iter().enumerate() {
        let at = DATA + u64::try_from(i).expect("fits") * 0x20;
        let ct: Vec<u8> = text.bytes().map(|b| b ^ 0x5a).collect();
        data(&mut bytes, at, &ct);
        let len = u32::try_from(text.len()).expect("fits");
        site2(
            &mut caller,
            0x1300,
            u32::try_from(at).expect("fits"),
            len,
            0x1000,
        );
    }
    caller.push(0xc3);
    place(&mut bytes, &mut ranges, 0x1300, &caller);

    // The rolling-key decoder's five ciphertexts at 0x2100; byte j is XOR
    // (0x11 + 7*j). The caller at 0x1500 decodes each.
    let roll = plaintexts("roll");
    let mut caller = Vec::new();
    for (i, text) in roll.iter().enumerate() {
        let at = 0x2100 + u64::try_from(i).expect("fits") * 0x20;
        let ct: Vec<u8> = text
            .bytes()
            .enumerate()
            .map(|(j, b)| {
                b ^ (0x11u8.wrapping_add(0x07u8.wrapping_mul(u8::try_from(j).expect("fits"))))
            })
            .collect();
        data(&mut bytes, at, &ct);
        let len = u32::try_from(text.len()).expect("fits");
        site2(
            &mut caller,
            0x1500,
            u32::try_from(at).expect("fits"),
            len,
            0x1100,
        );
    }
    caller.push(0xc3);
    place(&mut bytes, &mut ranges, 0x1500, &caller);

    // The copier's five sources at 0x2500 hold readable strings already; the
    // caller at 0x1700 copies each to a scratch buffer at 0x2700.
    let copy = plaintexts("copy");
    let mut caller = Vec::new();
    for (i, text) in copy.iter().enumerate() {
        let src = 0x2500 + u64::try_from(i).expect("fits") * 0x20;
        let dst = 0x2700 + u64::try_from(i).expect("fits") * 0x20;
        data(&mut bytes, src, text.as_bytes());
        let len = u32::try_from(text.len()).expect("fits");
        site3(
            &mut caller,
            0x1700,
            u32::try_from(dst).expect("fits"),
            u32::try_from(src).expect("fits"),
            len,
            0x1200,
        );
    }
    caller.push(0xc3);
    place(&mut bytes, &mut ranges, 0x1700, &caller);

    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".data", 0x2000, 0x2000, 0x1000, true, false),
        ],
    );
    p.function_ranges = ranges;
    p
}

/// Both decoders recover all ten strings with their call sites, and the
/// copier yields none.
#[test]
fn decoders_recover_their_strings_and_the_copier_none() {
    let p = decoders_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = decoded_tsv(&p, &a, &o, "").expect("decoded");
    for text in plaintexts("xor").iter().chain(&plaintexts("roll")) {
        assert!(out.contains(text), "missing {text}\n{out}");
    }
    for text in plaintexts("copy") {
        assert!(!out.contains(&text), "copier string listed: {text}\n{out}");
    }
    assert!(out.contains("# 10 decoded strings"), "{out}");
    // Each recovered row names the call that decoded it: the first site of
    // each caller is its call at offset 10, after the two argument moves.
    let row = |text: &str| {
        out.lines()
            .find(|l| l.contains(text))
            .unwrap_or_default()
            .to_owned()
    };
    assert!(
        row("http://xor1.test/c2").ends_with("0x130a in sub_1300"),
        "{out}"
    );
    assert!(
        row("http://roll1.test/c2").ends_with("0x150a in sub_1500"),
        "{out}"
    );
}

/// The listing is byte-identical across two runs.
#[test]
fn the_listing_is_deterministic() {
    let p = decoders_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        decoded_tsv(&p, &a, &o, "").expect("decoded"),
        decoded_tsv(&p, &a, &o, "").expect("decoded")
    );
}

/// A filter narrows by text, `limit=` pages with a line naming the next
/// page, and a count that is not one is refused.
#[test]
fn the_listing_filters_and_pages() {
    let p = decoders_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let roll = decoded_tsv(&p, &a, &o, "roll").expect("decoded");
    assert!(roll.starts_with("# 5 decoded strings"), "{roll}");
    assert!(!roll.contains("xor"), "{roll}");
    let page = decoded_tsv(&p, &a, &o, "limit=2").expect("decoded");
    assert!(page.contains("# showing 2 of 10 from 0"), "{page}");
    assert!(
        page.contains("# 8 more; borer://decoded/limit=2,offset=2 for the next page"),
        "{page}"
    );
    let bad = decoded_tsv(&p, &a, &o, "offset=x").expect_err("not a count");
    assert!(bad.contains("offset="), "{bad}");
}

/// A decoder fed a runaway length is bounded by the step budget and lists
/// nothing: the region it reads decodes to non-printable bytes.
#[test]
fn a_runaway_length_is_bounded_by_the_budget() {
    // A wide .data of 0x5a bytes: the XOR decoder turns each into a NUL, so
    // no printable string is produced however far it runs, and the step
    // budget stops it before it reaches the far end.
    const SPAN: usize = 0x40000;
    let mut bytes = vec![0xccu8; 0x2000 + SPAN];
    let mut ranges: Vec<(u64, u64)> = Vec::new();
    place(&mut bytes, &mut ranges, 0x1000, XOR_DECODE);
    for b in bytes.iter_mut().skip(0x2000) {
        *b = 0x5a;
    }
    // Three sites make it a candidate; each asks for a runaway length.
    let mut caller = Vec::new();
    for _ in 0..3 {
        site2(&mut caller, 0x1300, 0x2000, 0xffff_ffff, 0x1000);
    }
    caller.push(0xc3);
    place(&mut bytes, &mut ranges, 0x1300, &caller);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(
                ".data",
                0x2000,
                0x2000,
                u64::try_from(SPAN).expect("fits"),
                true,
                false,
            ),
        ],
    );
    p.function_ranges = ranges;
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = decoded_tsv(&p, &a, &o, "").expect("decoded");
    assert!(out.contains("# 0 decoded strings"), "{out}");
}
