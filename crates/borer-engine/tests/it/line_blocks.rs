//! Each line of a listing names the block it was written from
//! ([`View::block`]), so a reader grades a line by its own function's
//! block, not by whichever block an address index finds first.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::view::view;
use borer_engine::analysis::render::{Bytes, Dir, disasm_view, linear};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};
use borer_engine::view::{LineBlock, View};

/// Returns a raw x86-64 image of `code` at `0x1000`, int3 after it.
///
/// # Arguments
///
/// * `code` - The bytes at the image's start.
fn image(code: &[u8]) -> (Program, Analysis) {
    let len = code.len().next_multiple_of(0x100) + 0x100;
    let mut bytes = vec![0xcc; len];
    bytes[..code.len()].copy_from_slice(code);
    let size = u64::try_from(len).unwrap_or(u64::MAX);
    let text = Section::mapped(".text", 0x1000, 0, size, false, true);
    let mut p = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), vec![text]);
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    (p, a)
}

/// Returns the block of each line of `v` that shows text containing
/// `needle`, in line order.
///
/// # Arguments
///
/// * `v` - The view.
/// * `needle` - Text the lines hold.
fn blocks_of(v: &View, needle: &str) -> Vec<Option<LineBlock>> {
    (0..v.lines())
        .filter(|&i| v.line(i).is_some_and(|l| l.contains(needle)))
        .map(|i| v.block(i))
        .collect()
}

/// The block at `start` of the function at `function`.
const fn of(function: u64, start: u64) -> Option<LineBlock> {
    Some(LineBlock { function, start })
}

/// An instruction under a label is written from that label's block.
///
/// `jmp 0x1001` jumps into its own second byte, so `inc eax` sits under
/// `L_1001:` and is written from block `0x1001`, in the function listing
/// and in the linear listing alike; headers and labels are written from
/// no block.
#[test]
fn an_instruction_under_a_label_is_written_from_that_block() {
    // ASM: jmp 0x1001 (eb ff) ; from 0x1001: inc eax (ff c0) ; ret
    let (p, a) = image(&[0xeb, 0xff, 0xc0, 0xc3]);
    let o = Overlay::default();
    let v = disasm_view(&p, &a, &o, 0x1000, 100, Bytes::Shown).expect("a listing");
    assert_eq!(blocks_of(&v, "jmp"), [of(0x1000, 0x1000)], "{}", v.spell());
    assert_eq!(blocks_of(&v, "inc"), [of(0x1000, 0x1001)], "{}", v.spell());
    assert_eq!(blocks_of(&v, "ret"), [of(0x1000, 0x1001)], "{}", v.spell());
    assert_eq!(blocks_of(&v, "L_1001:"), [None]);
    assert_eq!(v.block(0), None, "the header");
    assert_eq!(v.line_for(&a, 0x1002), v.line_of(0x1001), "inside inc eax");
    let page = linear(&p, &a, &o, 0x1000, Dir::Next, 16).expect("a page");
    let lv = &page.view;
    assert_eq!(blocks_of(lv, "inc"), [of(0x1000, 0x1001)], "{}", lv.spell());
    assert_eq!(blocks_of(lv, "; function"), [None], "{}", lv.spell());
    assert_eq!(blocks_of(lv, "L_1001:"), [None], "{}", lv.spell());
    assert_eq!(blocks_of(lv, "; section"), [None], "{}", lv.spell());
}

/// Shared code: `F` at `0x1000` calls `G` at `0x1010` and runs on into
/// it, so `0x1010..0x1020` is a block of each. `F`'s listing writes
/// `0x1014` from `F`'s block `0x1005`, `G`'s from `G`'s own.
#[test]
fn shared_code_is_written_from_the_listed_function_block() {
    let mut code = vec![0xe8, 0x0b, 0x00, 0x00, 0x00]; // ASM: call 0x1010
    code.resize(0x1f, 0x90); // ASM: nop up to 0x101f
    code.push(0xc3); // ASM: ret
    let (p, a) = image(&code);
    let f = a.function(0x1000).expect("F");
    let shared = f
        .blocks
        .iter()
        .find(|b| b.start <= 0x1014 && 0x1014 < b.end);
    assert_eq!(shared.map(|b| (b.start, b.end)), Some((0x1005, 0x1020)));
    assert!(a.function(0x1010).is_some(), "G");
    let o = Overlay::default();
    let fv = disasm_view(&p, &a, &o, 0x1000, 100, Bytes::Shown).expect("F's listing");
    let gv = disasm_view(&p, &a, &o, 0x1010, 100, Bytes::Shown).expect("G's listing");
    let line = |v: &View| v.line_of(0x1014).expect("a line of 0x1014");
    assert_eq!(fv.block(line(&fv)), of(0x1000, 0x1005), "{}", fv.spell());
    assert_eq!(gv.block(line(&gv)), of(0x1010, 0x1010), "{}", gv.spell());
}

/// A decompiled line is written from its origin, as part of the text's
/// function; a line with no origin is written from no block.
#[test]
fn a_decompiled_line_is_written_from_its_origin() {
    // ASM: mov [rdx], rcx ; ret
    let (p, a) = image(&[0x48, 0x89, 0x0a, 0xc3]);
    let v = view(&p, &a, &Overlay::default(), 0x1000).expect("a decompile view");
    let mut written = 0;
    for i in 0..v.lines() {
        let want = v.origin(i).map(|start| LineBlock {
            function: 0x1000,
            start,
        });
        assert_eq!(v.block(i), want, "line {i}: {:?}", v.line(i));
        written += usize::from(want.is_some());
    }
    assert!(written > 0, "{}", v.spell());
    assert_eq!(v.block(0), None, "the header");
}

/// Finding the line that stands for an address is one pass over the lines.
///
/// On a function of 40,000 one-instruction blocks whose listing shows no
/// line at the address, it answers well inside 50 ms, where a search of
/// the function's blocks for each line takes hundreds.
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "a work bound on the UI thread's lookup, timed"
)]
fn finding_the_line_for_an_address_is_one_pass() {
    let n: u64 = 40_000;
    let mut code: Vec<u8> = (0..n).flat_map(|_| [0x74, 0x00]).collect(); // ASM: je +0
    code.push(0xc3); // ASM: ret
    let (p, a) = image(&code);
    let o = Overlay::default();
    let max = usize::try_from(2 * n).unwrap_or(usize::MAX);
    let v = disasm_view(&p, &a, &o, 0x1000, max, Bytes::Shown).expect("a listing");
    let last = 0x1000 + 2 * (n - 1);
    assert!(a.function(0x1000).is_some_and(|f| f.blocks.len() > 39_000));
    let started = std::time::Instant::now();
    let line = v.line_for(&a, last + 1);
    let took = started.elapsed();
    assert_eq!(line, v.line_of(last), "inside the last je");
    assert!(took.as_millis() < 50, "{took:?}");
}
