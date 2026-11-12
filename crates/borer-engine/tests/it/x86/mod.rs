//! 32-bit x86 decompilation.
//!
//! The frame, the arguments and the calls of a `cdecl`/`stdcall`/`thiscall`
//! program, where every argument travels on the
//! stack, the return address is four bytes and `ecx` may be `this`.
//!
//! Every fixture is hand-assembled and lives in a raw image, so each test
//! states the exact instructions it decompiles.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::decompiled;
use crate::raw;

use borer_engine::analysis::decompile::{decompile, decompile_named};
use borer_engine::analysis::{Analysis, Overlay, RefKind, name_of};
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};
use decompiled::{decompiled, runs_agree};

mod arguments;
mod classes;
mod flags;
mod floats;
mod frames;
mod references;
mod text;

/// Builds a raw 32-bit image with `code` in `.text` at 0x401000, entered
/// there, and `data` in a read-only `.rdata` at 0x402000.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `data` - The bytes of `.rdata`.
fn image_with_data(code: &[u8], data: &[u8]) -> Program {
    raw::image(Arch::X86, code, data)
}

/// Builds a raw 32-bit image with `code` at 0x401000 and no data.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn image(code: &[u8]) -> Program {
    image_with_data(code, &[])
}

/// Decompiles `code` at 0x401000 with imports at the slots `imports` name.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `imports` - `(slot, name)` pairs, each an import symbol.
fn dc_with(code: &[u8], imports: &[(u64, &str)]) -> String {
    let mut p = image(code);
    p.symbols = imports
        .iter()
        .map(|(addr, name)| Symbol {
            name: (*name).to_owned(),
            addr: *addr,
            kind: SymbolKind::Import,
        })
        .collect();
    decompiled(&p, 0x401000)
}

/// Decompiles the function at 0x401000 of a raw image holding `code`.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn dc(code: &[u8]) -> String {
    decompiled(&image(code), 0x401000)
}

/// Decompiles `code` at 0x401000 with `data` at 0x402000 and the overlay
/// names given.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `data` - The bytes of `.rdata`.
/// * `names` - `(address, name)` pairs the overlay names.
fn dc_data(code: &[u8], data: &[u8], names: &[(u64, &str)]) -> String {
    let p = image_with_data(code, data);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    for (addr, name) in names {
        o.names.insert(*addr, (*name).to_owned());
    }
    decompile(&p, &a, &o, 0x401000).unwrap_or_default()
}

/// Builds an image whose 0x401000 references `"alpha one"` and `"beta two"`
/// and calls 0x401020, which references the middle of `L"widestring"`.
fn strings_image() -> Program {
    let mut code = vec![0u8; 0x26];
    code[..0x10].copy_from_slice(&[
        0xb8, 0x00, 0x20, 0x40, 0x00, 0xb9, 0x10, 0x20, 0x40, 0x00, 0xe8, 0x11, 0x00, 0x00, 0x00,
        0xc3,
    ]);
    code[0x20..0x26].copy_from_slice(&[0xba, 0x24, 0x20, 0x40, 0x00, 0xc3]);
    let mut data = vec![0u8; 0x40];
    data[..9].copy_from_slice(b"alpha one");
    data[0x10..0x18].copy_from_slice(b"beta two");
    for (k, b) in b"widestring".iter().enumerate() {
        data[0x20 + k * 2] = *b;
    }
    image_with_data(&code, &data)
}

/// Builds an image whose 0x401000 calls 0x401010, which calls the import
/// `GetTickCount` through its slot at 0x402000, with no thunk.
fn import_call_image() -> Program {
    let mut code = vec![0xcc; 0x17];
    code[..6].copy_from_slice(&[0xe8, 0x0b, 0x00, 0x00, 0x00, 0xc3]);
    code[0x10..0x17].copy_from_slice(&[0xff, 0x15, 0x00, 0x20, 0x40, 0x00, 0xc3]);
    let mut p = image_with_data(&code, &[0u8; 4]);
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!GetTickCount".to_owned(),
        addr: 0x402000,
        kind: SymbolKind::Import,
    }];
    p
}

/// Builds a parent at 0x401000 with exception funclets.
///
/// The parent takes the address of its handler thunk at 0x401030, `mov
/// eax, 0x402000; jmp 0x401040`, whose `FuncInfo` at 0x402000 has two
/// unwind states, actions at 0x401050 and 0x401060, and one try block with
/// one catch clause at 0x401070.
///
/// # Arguments
///
/// * `handler` - The code at 0x401040, where the thunk jumps.
fn funclet_image(handler: &[u8]) -> Program {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x83, 0xec, 0x08, 0xb8, 0x30, 0x10, 0x40, 0x00, 0x89, 0x45, 0xf8, 0x8b,
        0x45, 0xfc, 0xc9, 0xc3,
    ];
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x00, 0x20, 0x40, 0x00, 0xe9, 0x06, 0x00, 0x00, 0x00]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(handler);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x8b, 0x45, 0xfc, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8d, 0x4d, 0xf8, 0xc3]);
    code.resize(0x70, 0xcc);
    code.extend_from_slice(&[0x8b, 0x45, 0xf8, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x110];
    let words = |data: &mut Vec<u8>, at: usize, values: &[u32]| {
        for (k, v) in values.iter().enumerate() {
            data[at + k * 4..at + k * 4 + 4].copy_from_slice(&le(*v));
        }
    };
    words(
        &mut data,
        0,
        &[0x1993_0522, 2, 0x402030, 1, 0x402040, 0, 0, 0, 1],
    );
    words(&mut data, 0x30, &[0xffff_ffff, 0x401050, 0, 0x401060]);
    words(&mut data, 0x40, &[0, 1, 1, 1, 0x402060]);
    words(&mut data, 0x60, &[0x40, 0, 0, 0x401070]);
    image_with_data(&code, &data)
}

/// The CRT's `__SEH_prolog4`, byte for byte: `push -1; push eax;
/// mov eax,fs:[0]; push eax; mov eax,[esp+0xc]; mov fs:[0],esp;
/// mov [esp+0xc],ebp; lea ebp,[esp+0xc]; push eax; ret`.
const SEH_PROLOG4: [u8; 31] = [
    0x6a, 0xff, 0x50, 0x64, 0xa1, 0x00, 0x00, 0x00, 0x00, 0x50, 0x8b, 0x44, 0x24, 0x0c, 0x64, 0x89,
    0x25, 0x00, 0x00, 0x00, 0x00, 0x89, 0x6c, 0x24, 0x0c, 0x8d, 0x6c, 0x24, 0x0c, 0x50, 0xc3,
];

/// The CRT's `__SEH_prolog4` as later CRTs build it.
///
/// Byte for byte as `d3dx9_43` links it: `push __except_handler4; push
/// dword fs:[0]; mov eax,[esp+0x10]; mov [esp+0x10],ebp; lea
/// ebp,[esp+0x10]; sub esp,eax; push ebx; push esi; push edi; mov
/// eax,[__security_cookie]; xor [ebp-4],eax; xor eax,ebp; push eax; mov
/// [ebp-0x18],esp; push dword [ebp-8]; mov eax,[ebp-4]; mov dword
/// [ebp-4],-2; mov [ebp-8],eax; lea eax,[ebp-0x10]; mov fs:[0],eax; ret`,
/// the handler at 0x401100 and the cookie at 0x402000.
const SEH_PROLOG4_HANDLER: [u8; 69] = [
    0x68, 0x00, 0x11, 0x40, 0x00, 0x64, 0xff, 0x35, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x44, 0x24, 0x10,
    0x89, 0x6c, 0x24, 0x10, 0x8d, 0x6c, 0x24, 0x10, 0x2b, 0xe0, 0x53, 0x56, 0x57, 0xa1, 0x00, 0x20,
    0x40, 0x00, 0x31, 0x45, 0xfc, 0x33, 0xc5, 0x50, 0x89, 0x65, 0xe8, 0xff, 0x75, 0xf8, 0x8b, 0x45,
    0xfc, 0xc7, 0x45, 0xfc, 0xfe, 0xff, 0xff, 0xff, 0x89, 0x45, 0xf8, 0x8d, 0x45, 0xf0, 0x64, 0xa3,
    0x00, 0x00, 0x00, 0x00, 0xc3,
];

/// The CRT's `__SEH_epilog4`, byte for byte: `mov ecx,[ebp-0x10]; mov
/// fs:[0],ecx; pop ecx; pop edi; pop edi; pop esi; pop ebx; mov esp,ebp;
/// pop ebp; push ecx; ret`.
const SEH_EPILOG4: [u8; 20] = [
    0x8b, 0x4d, 0xf0, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x59, 0x5f, 0x5f, 0x5e, 0x5b, 0x8b,
    0xe5, 0x5d, 0x51, 0xc3,
];

/// The 32-bit values where a signed condition's overflow shows: the
/// extremes, their neighbours, and the small numbers around zero.
fn boundary_i32() -> [i32; 11] {
    [
        i32::MIN,
        i32::MIN + 1,
        -2,
        -1,
        0,
        1,
        2,
        5,
        i32::MAX - 1,
        i32::MAX,
        0x4000_0000,
    ]
}

/// The lifter and the emulator agree on every block of `code` at 0x401000,
/// for sixteen seeds of random registers and memory.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, one block ending in `ret`.
fn agrees_with_the_emulator(code: &[u8]) {
    image_agrees_with_the_emulator(&image(code));
}

/// The lifter and the emulator agree on every block of 64-bit `code` at
/// 0x401000, as [`agrees_with_the_emulator`] checks 32-bit code.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, one block ending in `ret`.
fn agrees_with_the_emulator_64(code: &[u8]) {
    image_agrees_with_the_emulator(&raw::image(Arch::X86_64, code, &[]));
}

/// The lifter and the emulator agree on the one block at 0x401000 of `p`,
/// which is checked, for sixteen seeds of random registers and memory.
///
/// # Arguments
///
/// * `p` - The image.
fn image_agrees_with_the_emulator(p: &Program) {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    let a = Analysis::compute(p);
    for seed in 1..=16 {
        let v = verify(p, &a, &[0x401000], seed);
        assert_eq!(v.checked, 1, "seed {seed}: {}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
    }
}

/// Fails when the text reads an x87 register no statement assigns.
///
/// # Arguments
///
/// * `text` - The pseudo-C.
fn assert_st_written(text: &str) {
    for i in 0..8 {
        let name = format!("st{i}");
        let read = text
            .match_indices(&name)
            .any(|(at, _)| !text[at + name.len()..].starts_with(" = "));
        assert!(
            !read || text.contains(&format!("{name} = ")),
            "{name} read, never written: {text}"
        );
    }
}

/// Decompiles 64-bit `code` at 0x401000 of a raw image.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn dc64(code: &[u8]) -> String {
    decompiled(&raw::image(Arch::X86_64, code, &[]), 0x401000)
}
