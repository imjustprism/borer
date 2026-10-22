//! Guard clauses and returns: the arm that fails or returns early stays
//! the `if` body.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;

use crate::decompiled::{decompiled, program64, replays_clean};

/// A guard clause whose arm only fails writes that arm as the `if` body,
/// the code after it as what follows, whichever side the branch jumps to.
///
/// `f` tests `a1` and falls into a call to `abort`, which never returns,
/// else calls `x`: the text is `if (a1 == 0) { abort(); }` and then `x();`,
/// the shape of the source's guard, not the returning arm nested in the
/// `if` and the failure after it. `g` jumps to the failure and falls into
/// a lone `ret`, and its one caller reads no result: there the `return`
/// is the guard, `if (a1 != 0) return;`, before the failing call.
#[test]
fn a_guard_clause_keeps_its_failing_arm_in_the_if() {
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![
        0x85, 0xc9, // ASM: test ecx, ecx
        0x75, 0x05, // ASM: jne ok
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call abort
        0xe8, 0x42, 0x00, 0x00, 0x00, // ASM: ok: call x
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x01, // ASM: je fail
        0xc3, // ASM: ret
        0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: fail: call abort
    ]);
    code.resize(0x40, 0xcc);
    code.push(0xc3); // ASM: ret
    code.resize(0x50, 0xcc);
    code.push(0xc3); // ASM: ret
    code.resize(0x60, 0xcc);
    code.extend([
        0xe8, 0xbb, 0xff, 0xff, 0xff, // ASM: call g
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ]);
    let mut p = program64(&code);
    for (name, addr) in [("abort", 0x1_4000_1040), ("x", 0x1_4000_1050)] {
        p.symbols.push(Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Local,
        });
    }
    let f = decompiled(&p, 0x1_4000_1000);
    let body = f.split_once("if (").map_or("", |(_, b)| b);
    assert!(
        body.starts_with("a1 == 0) {\n  abort();\n}\nreturn x();"),
        "{f}"
    );
    let g = decompiled(&p, 0x1_4000_1020);
    let body = g.split_once("if (").map_or("", |(_, b)| b);
    assert!(
        body.starts_with("a1 != 0) {\n  return;\n}\nabort();"),
        "{g}"
    );
    let a = Analysis::compute(&p);
    replays_clean(&p, &a, &[0x1_4000_1000, 0x1_4000_1020]);
}
