//! Capability names match a whole stem, not a fragment of a longer API.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::program::{Symbol, SymbolKind};

use crate::common::fixture;

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
