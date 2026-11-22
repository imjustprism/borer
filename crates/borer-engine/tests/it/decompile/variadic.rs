//! Variadic functions: the System V register save area of a `va_list`.

use super::*;
use borer_engine::analysis::decompile::checked_header;
use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};

/// Where the variadic function starts.
const ENTRY: u64 = 0x1_4000_1000;

/// Offset of the callee the function hands its list to.
const CALLEE: usize = 0x100;

/// The argument registers by slot, as `mov [rsp+disp32],r64` numbers them.
const GPRS: [u8; 6] = [7, 6, 2, 1, 8, 9];

/// The `test al, al` that reads the caller's count of vector arguments.
const TEST_AL: [u8; 2] = [0x84, 0xc0];

/// One GCC variadic prologue and its `va_start`, piece by piece, so a
/// test can change one piece.
///
/// The frame is `frame` bytes below the return address; the list sits at
/// `[rsp+8]`, the register save area at `[rsp+0x20]`, its integer half
/// first and its vector half from `[rsp+0x50]`.
struct Shape {
    /// The frame's size, eight more than a multiple of sixteen.
    frame: u32,
    /// Bytes right after `sub rsp`.
    pre: Vec<u8>,
    /// The first and one past the last integer slot saved.
    gprs: (usize, usize),
    /// The test before the `je` that skips the vector saves.
    test: [u8; 2],
    /// Bytes between one vector's place and the next.
    stride: u32,
    /// How many of `xmm0` up are saved.
    vectors: u8,
    /// The saving block's bytes in place of the vector saves.
    save: Option<Vec<u8>>,
    /// Bytes after the vector saves, in the same block.
    extra: Vec<u8>,
    /// Bytes right before the list's address is passed.
    before_call: Vec<u8>,
    /// Whether the list's `reg_save_area` takes the area's address.
    takes_area: bool,
    /// Whether a later block sets `al` and jumps back to the entry.
    loops_back: bool,
}

impl Default for Shape {
    /// `int f(const char *fmt, ...) { va_list ap; va_start(ap, fmt);
    /// return g(fmt, ap); }` as GCC builds it.
    fn default() -> Shape {
        Shape {
            frame: 0xd8,
            pre: Vec::new(),
            gprs: (1, 6),
            test: TEST_AL,
            stride: 16,
            vectors: 8,
            save: None,
            extra: Vec::new(),
            before_call: Vec::new(),
            takes_area: true,
            loops_back: false,
        }
    }
}

/// `mov [rsp+disp],r64`.
///
/// # Arguments
///
/// * `r` - The register's number.
/// * `disp` - The displacement.
fn store(r: u8, disp: u32) -> Vec<u8> {
    let mut b = vec![
        0x48 | if r >= 8 { 4 } else { 0 }, // ASM: rex.w, rex.r for r8 up
        0x89,                              // ASM: mov r/m64,r64
        0x84 | ((r & 7) << 3),             // ASM: modrm [sib+disp32]
        0x24,                              // ASM: sib rsp
    ];
    b.extend(disp.to_le_bytes());
    b
}

/// `movaps [rsp+disp],xmmj`.
///
/// # Arguments
///
/// * `j` - The vector register's number.
/// * `disp` - The displacement.
fn movaps(j: u8, disp: u32) -> Vec<u8> {
    let mut b = vec![
        0x0f,
        0x29,            // ASM: movaps m128,xmm
        0x84 | (j << 3), // ASM: modrm [sib+disp32]
        0x24,            // ASM: sib rsp
    ];
    b.extend(disp.to_le_bytes());
    b
}

/// `lea r64,[rsp+disp]`.
///
/// # Arguments
///
/// * `r` - The register's number, below 8.
/// * `disp` - The displacement.
fn lea(r: u8, disp: u32) -> Vec<u8> {
    let mut b = vec![
        0x48,
        0x8d,            // ASM: lea r64,m
        0x84 | (r << 3), // ASM: modrm [sib+disp32]
        0x24,            // ASM: sib rsp
    ];
    b.extend(disp.to_le_bytes());
    b
}

/// `mov dword [rsp+disp],imm`.
///
/// # Arguments
///
/// * `disp` - The displacement.
/// * `imm` - The value.
fn store_dword(disp: u32, imm: u32) -> Vec<u8> {
    let mut b = vec![0xc7, 0x84, 0x24]; // ASM: mov dword [rsp+disp32],imm32
    b.extend(disp.to_le_bytes());
    b.extend(imm.to_le_bytes());
    b
}

/// A 32-bit displacement from the end of an instruction at `end` to `to`.
///
/// # Arguments
///
/// * `end` - Where the instruction ends.
/// * `to` - Where it lands.
fn rel(end: usize, to: usize) -> [u8; 4] {
    let d = i32::try_from(to).unwrap_or(0) - i32::try_from(end).unwrap_or(0);
    d.to_le_bytes()
}

impl Shape {
    /// Assembles the function at [`ENTRY`] and its callee at [`CALLEE`],
    /// which reads both its arguments.
    fn code(&self) -> Vec<u8> {
        let frame = self.frame;
        let mut c = vec![0x48, 0x81, 0xec]; // ASM: sub rsp,imm32
        c.extend(frame.to_le_bytes());
        c.extend(&self.pre);
        for (k, r) in GPRS.iter().enumerate().take(self.gprs.1).skip(self.gprs.0) {
            c.extend(store(*r, 0x20 + 8 * u32::try_from(k).unwrap_or(0)));
        }
        c.extend(self.test);
        let save = self.save.clone().unwrap_or_else(|| {
            (0..self.vectors)
                .flat_map(|j| movaps(j, 0x50 + self.stride * u32::from(j)))
                .collect()
        });
        let len = save.len() + self.extra.len();
        c.extend([0x0f, 0x84]); // ASM: je rel32
        c.extend(rel(0, len));
        c.extend(save);
        c.extend(&self.extra);
        c.extend(lea(0, frame + 8));
        c.extend(store_dword(8, 8 * u32::try_from(self.gprs.0).unwrap_or(0)));
        c.extend(store_dword(0xc, 0x30));
        c.extend(store(0, 0x10));
        if self.takes_area {
            c.extend(lea(0, 0x20));
            c.extend(store(0, 0x18));
        }
        c.extend(&self.before_call);
        let jne = self.loops_back.then(|| {
            c.extend([0x48, 0x85, 0xff, 0x0f, 0x85]); // ASM: test rdi,rdi; jne rel32
            c.extend([0; 4]);
            c.len()
        });
        c.extend(lea(6, 8));
        c.push(0xe8); // ASM: call rel32
        c.extend(rel(c.len() + 4, CALLEE));
        c.extend([0x48, 0x81, 0xc4]); // ASM: add rsp,imm32
        c.extend(frame.to_le_bytes());
        c.push(0xc3); // ASM: ret
        if let Some(end) = jne {
            let back = c.len();
            c[end - 4..end].copy_from_slice(&rel(end, back));
            c.extend([0x48, 0x81, 0xc4]); // ASM: add rsp,imm32
            c.extend(frame.to_le_bytes());
            c.extend([0xb0, 0x01, 0xe9]); // ASM: mov al,1; jmp rel32
            c.extend(rel(c.len() + 4, 0));
        }
        c.resize(CALLEE, 0xcc);
        c.extend([
            0x48, 0x8b, 0x06, // ASM: mov rax,[rsi]
            0x48, 0x01, 0xf8, // ASM: add rax,rdi
            0xc3, // ASM: ret
        ]);
        c
    }
}

/// An ELF image of `code` at `0x140001000`, entered at its start.
///
/// # Arguments
///
/// * `code` - The bytes.
fn elf64(code: &[u8]) -> Program {
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(ENTRY),
        vec![Section::mapped(".text", ENTRY, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Elf;
    p
}

/// Decompiles the variadic function and checks its lift against the
/// emulator, the saving block included.
///
/// # Arguments
///
/// * `shape` - The function.
///
/// # Returns
///
/// The text and its `// checked vs binary:` header.
fn text_and_check(shape: &Shape) -> (String, String) {
    let p = elf64(&shape.code());
    let a = Analysis::compute(&p);
    for seed in 1..=8 {
        let v = verify(&p, &a, &[ENTRY], seed);
        assert!(v.checked >= 1, "seed {seed}: {}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
    }
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, ENTRY).unwrap_or_default();
    let header = checked_header(&p, &a, &o, ENTRY).unwrap_or_default();
    assert!(!header.contains("disagree"), "{header}\n{text}");
    (text, header)
}

/// Asserts the vector saves left the text, without a branch, an
/// unreachable block or a block the check of the text skipped.
///
/// # Arguments
///
/// * `shape` - The function.
fn folded(shape: &Shape) {
    let (text, header) = text_and_check(shape);
    assert!(!text.contains("= xmm0;"), "{text}");
    assert!(!text.contains("if ("), "{text}");
    assert!(text.contains("// folded: xmm0..xmm7 saves"), "{text}");
    assert!(text.contains("likely va_start's"), "{text}");
    assert!(text.contains("al-guarded"), "{text}");
    assert!(text.contains("address is taken"), "{text}");
    assert!(!text.contains("unreachable"), "{text}");
    assert!(!header.contains("not in text"), "{header}\n{text}");
    assert!(!header.contains("unknown"), "{header}\n{text}");
}

/// Asserts the guarded saves stay in the text as a branch.
///
/// # Arguments
///
/// * `shape` - The function.
fn kept(shape: &Shape) {
    let (text, _) = text_and_check(shape);
    assert!(text.contains("if ("), "{text}");
    assert!(!text.contains("va_start"), "{text}");
}

/// A variadic prologue's saves of the vector registers, behind the
/// caller's count of them in `al`, are no branch of the text.
///
/// The header says `va_start`'s saves are left out, no block is counted
/// unreachable, the lift still agrees with the emulator, the check of the
/// text still replays the saving block, and the list is still built and
/// passed.
#[test]
fn a_variadic_prologue_saves_its_vector_registers_without_a_branch() {
    let shape = Shape::default();
    folded(&shape);
    let (text, _) = text_and_check(&shape);
    assert!(text.contains("a1, ..."), "{text}");
    assert!(text.contains("= 48;"), "{text}");
}

/// A function whose six integer registers are all fixed saves only the
/// vector half of the area, behind `test al, al`, and that block leaves
/// the text as well: the list starts with `gp_offset` 48.
#[test]
fn an_area_of_vector_registers_alone_leaves_the_text_too() {
    folded(&Shape {
        gprs: (6, 6),
        ..Shape::default()
    });
}

/// The same saves behind a test of another register than `al` are a
/// branch the text keeps: only the caller's count of vector registers is
/// the `va_start` guard.
#[test]
fn vector_saves_behind_another_register_keep_their_branch() {
    kept(&Shape {
        test: [0x84, 0xc9],
        ..Shape::default()
    });
}

/// A save area that stops at `rcx` is no whole `va_start` area, and its
/// vector saves stay in the text with their branch.
#[test]
fn a_partial_save_area_keeps_its_vector_saves() {
    kept(&Shape {
        gprs: (1, 4),
        ..Shape::default()
    });
}

/// Stores through another pointer behind the test are no save area, even
/// when the frame's vector places were filled before the test: they write
/// 128 bytes the text must show.
#[test]
fn vector_stores_through_a_pointer_keep_their_branch() {
    let through_rdi: Vec<u8> = (0..8u8)
        .flat_map(|j| {
            [
                0x0f,
                0x11,            // ASM: movups m128,xmm
                0x47 | (j << 3), // ASM: modrm [rdi+disp8]
                j * 0x10,        // ASM: disp8
            ]
        })
        .collect();
    kept(&Shape {
        pre: (0..8u8)
            .flat_map(|j| movaps(j, 0x50 + 16 * u32::from(j)))
            .collect(),
        save: Some(through_rdi),
        ..Shape::default()
    });
}

/// Seven vector saves are not the whole area.
#[test]
fn seven_vector_saves_keep_their_branch() {
    kept(&Shape {
        vectors: 7,
        ..Shape::default()
    });
}

/// Vector saves 32 bytes apart are not the area's layout.
#[test]
fn vector_saves_32_bytes_apart_keep_their_branch() {
    kept(&Shape {
        frame: 0x158,
        stride: 32,
        ..Shape::default()
    });
}

/// A saving block with one instruction more than the saves keeps its
/// branch.
#[test]
fn a_saving_block_that_does_more_keeps_its_branch() {
    kept(&Shape {
        extra: vec![0x90], // ASM: nop
        ..Shape::default()
    });
}

/// An `al` the function wrote before testing it is no longer the caller's
/// count of vector arguments: with `al` set to 1 the branch folds the
/// other way, and the saves it then always runs stay in the text.
#[test]
fn an_al_written_before_the_test_keeps_the_saves() {
    let (text, _) = text_and_check(&Shape {
        pre: vec![0xb8, 0x01, 0x00, 0x00, 0x00], // ASM: mov eax,1
        ..Shape::default()
    });
    assert!(text.contains("= xmm0;"), "{text}");
    assert!(text.contains("= xmm7;"), "{text}");
    assert!(!text.contains("va_start"), "{text}");
}

/// A call before the test leaves `al` whatever the callee left.
#[test]
fn a_call_before_the_test_keeps_the_branch() {
    let mut pre = vec![0xe8]; // ASM: call rel32
    pre.extend(rel(12, CALLEE));
    kept(&Shape {
        pre,
        ..Shape::default()
    });
}

/// A later read of the high half of `xmm0`'s place reads the saved value
/// by name, so the saves stay in the text.
#[test]
fn a_second_reader_of_the_save_area_keeps_the_saves() {
    let mut before_call = vec![0x48, 0x8b, 0xbc, 0x24]; // ASM: mov rdi,[rsp+disp32]
    before_call.extend(0x58u32.to_le_bytes());
    kept(&Shape {
        before_call,
        ..Shape::default()
    });
}

/// A function that never takes the area's address starts no list there,
/// so its saves are not `va_start`'s.
#[test]
fn saves_with_no_list_pointing_at_them_keep_their_branch() {
    kept(&Shape {
        takes_area: false,
        ..Shape::default()
    });
}

/// An `al` copied from an argument before the test is no count of vector
/// arguments either, though nothing folds the branch.
#[test]
fn an_al_copied_from_an_argument_keeps_the_branch() {
    kept(&Shape {
        pre: vec![0x89, 0xf8], // ASM: mov eax,edi
        ..Shape::default()
    });
}

/// Eight `movsd` stores at the area's places write half of each vector:
/// no save area, so the branch stays.
#[test]
fn half_vector_stores_keep_their_branch() {
    let movsd: Vec<u8> = (0..8u8)
        .flat_map(|j| {
            let mut b = vec![
                0xf2,
                0x0f,
                0x11,            // ASM: movsd m64,xmm
                0x84 | (j << 3), // ASM: modrm [sib+disp32]
                0x24,            // ASM: sib rsp
            ];
            b.extend((0x50 + 16 * u32::from(j)).to_le_bytes());
            b
        })
        .collect();
    kept(&Shape {
        save: Some(movsd),
        ..Shape::default()
    });
}

/// GCC's stack probe, `push rax; pop rax`, before the saves gives `rax`
/// back unchanged, so `al` is still the caller's count and the saves
/// leave the text.
#[test]
fn a_stack_probe_before_the_test_still_folds() {
    folded(&Shape {
        pre: vec![0x50, 0x58], // ASM: push rax; pop rax
        ..Shape::default()
    });
}

/// A `pop rax` that follows no `push rax` loads some other word.
#[test]
fn a_pop_into_rax_keeps_the_branch() {
    kept(&Shape {
        pre: vec![0x51, 0x58], // ASM: push rcx; pop rax
        ..Shape::default()
    });
}

/// A later block that sets `al` and jumps back to the entry runs the test
/// on a value the function chose, so the branch stays.
#[test]
fn an_entry_entered_again_keeps_the_branch() {
    kept(&Shape {
        loops_back: true,
        ..Shape::default()
    });
}
