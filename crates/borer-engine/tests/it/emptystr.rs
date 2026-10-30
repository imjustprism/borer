//! An empty wide string is `L""`, in a read and in the pseudo-C.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::function_strings_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::memory::{Kind, read_values};

use crate::decompiled::{decompiled, program64_with_data};

/// Padding after `L"*"` is an empty wide string.
///
/// A one-value `wstr` read returns it, the pseudo-C prints `L""`, and
/// `function_strings` lists the site. A longer read of a leading NUL still
/// refuses the address, and ASCII padding is not `L""`.
#[test]
fn an_empty_wide_string_is_a_literal() {
    let code = [
        0x48, 0x8d, 0x15, 0xfd, 0x0f, 0x00, 0x00, // ASM: lea rdx, [rip+0xffd]
        0x48, 0x89, 0xd0, // ASM: mov rax, rdx
        0xc3, // ASM: ret
    ];
    let mut data = vec![0u8; 16];
    data[..8].copy_from_slice(&[0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
    let program = program64_with_data(&code, &data);
    let entry = 0x1_4000_1000;
    let text = decompiled(&program, entry);
    assert!(text.contains("L\"\""), "{text}");
    let analysis = Analysis::compute(&program);
    let rows =
        function_strings_tsv(&program, &analysis, &Overlay::default(), entry).unwrap_or_default();
    assert!(rows.contains("L\"\""), "{rows}");
    let wide = read_values(&program, 0x1_4000_2004, Kind::WStr, 1).expect("empty wide");
    assert_eq!(wide[0].text, "L\"\" (len 0)");
    let narrow = read_values(&program, 0x1_4000_2002, Kind::CStr, 1).expect("empty narrow");
    assert_eq!(narrow[0].text, "\"\" (len 0)");
    let pool = [0x00, b'h', b'i', 0x00];
    let pooled = program64_with_data(&[0xc3], &pool);
    let err = read_values(&pooled, 0x1_4000_2000, Kind::CStr, 2).unwrap_err();
    assert!(err.contains("no CStr"), "{err}");
}
