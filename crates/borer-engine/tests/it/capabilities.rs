//! Capability names match a whole stem, not a fragment of a longer API.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::program::{Arch, Symbol, SymbolKind};

use crate::common::fixture;
use crate::raw::image;

/// A longer name that only contains a filesystem or crypto stem is not that
/// capability, and `GetThreadContext` alone is not process injection.
#[test]
fn capability_fragments_match_a_name_boundary() {
    let mut p = fixture();
    let imports = |names: &[&str]| -> Vec<Symbol> {
        names
            .iter()
            .map(|n| Symbol {
                name: format!("KERNEL32.dll!{n}"),
                addr: 0,
                kind: SymbolKind::Import,
            })
            .collect()
    };
    p.symbols = imports(&[
        "InternetReadFile",
        "CreateFileMappingA",
        "DecryptFileW",
        "DuplicateEncryptionInfoFile",
        "GetOpenClipboardWindow",
        "GetThreadContext",
        "NtCreateFileMapping",
    ]);
    let text = borer_engine::analysis::render::capability_map_tsv(&p, None);
    assert!(!text.contains("filesystem"), "{text}");
    assert!(!text.contains("cryptography"), "{text}");
    assert!(!text.contains("clipboard"), "{text}");
    assert!(!text.contains("process injection"), "{text}");
    assert!(text.contains("anti-analysis"), "{text}");
    assert!(text.contains("GetThreadContext"), "{text}");
    p.symbols = imports(&[
        "ReadFile",
        "WriteFileEx",
        "CreateFileA",
        "CryptEncrypt",
        "BCryptOpenAlgorithmProvider",
        "NCryptEncrypt",
        "OpenClipboard",
        "SetThreadContext",
    ]);
    let text = borer_engine::analysis::render::capability_map_tsv(&p, None);
    assert!(text.contains("ReadFile"), "{text}");
    assert!(text.contains("WriteFileEx"), "{text}");
    assert!(text.contains("CreateFileA"), "{text}");
    assert!(text.contains("cryptography"), "{text}");
    assert!(text.contains("CryptEncrypt"), "{text}");
    assert!(text.contains("BCryptOpenAlgorithmProvider"), "{text}");
    assert!(text.contains("NCryptEncrypt"), "{text}");
    assert!(text.contains("OpenClipboard"), "{text}");
    assert!(text.contains("process injection"), "{text}");
    assert!(text.contains("SetThreadContext"), "{text}");
    p.symbols = imports(&[
        "EVP_EncryptInit",
        "AES_encrypt",
        "mbedtls_aes_crypt_cbc",
        "gcry_cipher_decrypt",
    ]);
    let text = borer_engine::analysis::render::capability_map_tsv(&p, None);
    assert!(text.contains("cryptography"), "{text}");
    assert!(text.contains("EVP_EncryptInit"), "{text}");
    assert!(text.contains("AES_encrypt"), "{text}");
    assert!(text.contains("mbedtls_aes_crypt_cbc"), "{text}");
    assert!(text.contains("gcry_cipher_decrypt"), "{text}");
    p.symbols = imports(&[
        "NtCreateFile",
        "ZwWriteFile",
        "ReadFileScatter",
        "WriteFileGather",
        "CreateFileTransactedW",
    ]);
    let text = borer_engine::analysis::render::capability_map_tsv(&p, None);
    assert!(text.contains("filesystem"), "{text}");
    assert!(text.contains("NtCreateFile"), "{text}");
    assert!(text.contains("ZwWriteFile"), "{text}");
    assert!(text.contains("ReadFileScatter"), "{text}");
    assert!(text.contains("WriteFileGather"), "{text}");
    assert!(text.contains("CreateFileTransactedW"), "{text}");
}

/// A runtime failure path is not an anti-analysis capability. A caller that
/// tests the result is.
#[test]
fn a_crt_import_is_a_capability_only_when_a_caller_checks_it() {
    let map = |code: &[u8], name: &str| {
        let mut p = image(Arch::X86_64, code, &[]);
        p.symbols.push(Symbol {
            name: format!("KERNEL32.dll!{name}"),
            addr: 0x402000,
            kind: SymbolKind::Import,
        });
        let a = Analysis::compute(&p);
        borer_engine::analysis::render::capability_map_tsv(&p, Some(&a))
    };
    let checked = [
        0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
        0x85, 0xc0, // ASM: test eax, eax
        0xc3, // ASM: ret
    ];
    let text = map(&checked, "IsDebuggerPresent");
    assert!(text.contains("IsDebuggerPresent"), "{text}");
    let indirect = [
        0xff, 0x15, 0xfa, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0xffa]
        0x85, 0xc0, // ASM: test eax, eax
        0xc3, // ASM: ret
    ];
    let text = map(&indirect, "IsDebuggerPresent");
    assert!(text.contains("IsDebuggerPresent"), "{text}");
    let bare = [
        0xff, 0x15, 0xfa, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0xffa]
        0xc3, // ASM: ret
    ];
    let text = map(&bare, "IsDebuggerPresent");
    assert!(!text.contains("IsDebuggerPresent"), "{text}");
    let fail = [
        0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
        0x85, 0xc0, // ASM: test eax, eax
        0xcd, 0x29, // ASM: int 0x29
        0xc3, // ASM: ret
    ];
    let text = map(&fail, "IsDebuggerPresent");
    assert!(!text.contains("anti-analysis"), "{text}");
    let once = [
        0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
        0xc3, // ASM: ret
    ];
    let text = map(&once, "QueryPerformanceCounter");
    assert!(!text.contains("anti-analysis"), "{text}");
    let twice = [
        0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x402000
        0xe8, 0xf6, 0x0f, 0x00, 0x00, // ASM: call 0x402000
        0xc3, // ASM: ret
    ];
    let text = map(&twice, "QueryPerformanceCounter");
    assert!(text.contains("QueryPerformanceCounter"), "{text}");
    let thunked = |check: bool| {
        let mut code = vec![0xcc_u8; 0x16];
        code[0] = 0xe8;
        code[1..5].copy_from_slice(&[0x0b, 0x00, 0x00, 0x00]); // ASM: call 0x401010
        if check {
            code[5] = 0x85; // ASM: test eax, eax
            code[6] = 0xc0;
            code[7] = 0xc3;
        } else {
            code[5] = 0xc3;
        }
        code[0x10..0x16].copy_from_slice(&[0xff, 0x25, 0xea, 0x0f, 0x00, 0x00]); // ASM: jmp qword [rip+0xfea]
        code
    };
    let text = map(&thunked(true), "IsDebuggerPresent");
    assert!(text.contains("IsDebuggerPresent"), "{text}");
    let text = map(&thunked(false), "IsDebuggerPresent");
    assert!(!text.contains("IsDebuggerPresent"), "{text}");
}

/// `Software\` settings are a registry write. A Run key or a service stays
/// persistence.
#[test]
fn settings_keys_are_a_registry_write_and_a_run_key_stays_persistence() {
    let map = |name: &str, data: &[u8]| {
        let mut p = image(Arch::X86_64, &[0xc3], data);
        p.symbols.push(Symbol {
            name: format!("ADVAPI32.dll!{name}"),
            addr: 0,
            kind: SymbolKind::Import,
        });
        borer_engine::analysis::render::capability_map_tsv(&p, None)
    };
    let settings = map("RegCreateKeyExW", b"Software\\Vendor\\App\0");
    assert!(settings.contains("registry write"), "{settings}");
    assert!(!settings.contains("persistence"), "{settings}");
    let run = map(
        "RegSetValueExW",
        b"Software\\Microsoft\\Windows\\CurrentVersion\\Run\0",
    );
    assert!(run.contains("persistence"), "{run}");
    assert!(!run.contains("registry write"), "{run}");
    let service = map("CreateServiceA", b"Software\\Vendor\\App\0");
    assert!(service.contains("persistence"), "{service}");
}
