//! The equality a block starts under, held to the run into the block.
//!
//! An equality that does not hold is flagged at the branch, whatever
//! variable it is of, and a block no run bears it out for is not checked.

use super::super::term::{Term, narrow};
use super::super::tests::{agrees, claims, replayed_under, replayed_with};
use super::super::{Claim, Replayed, Witness, replay_tsv};
use super::{ASSUMED, start_term};
use crate::analysis::decompile::decompile;
use crate::analysis::decompile::expr::{Expr, Key, Op};
use crate::analysis::decompile::lift::EffectKind;
use crate::analysis::decompile::liveness::WHOLE;
use crate::analysis::{Analysis, Overlay};
use crate::isa::x86::Register;
use crate::num::lo32;
use crate::program::{Arch, Program, Section};

/// A loop that counts `r9` down to zero, summing what `rdx` walks.
const COUNTED: [u8; 18] = [
    0x49, 0x89, 0xc9, // ASM: mov r9, rcx
    0x31, 0xc0, // ASM: xor eax, eax
    0x48, 0x03, 0x02, // ASM: add rax, [rdx]
    0x48, 0x83, 0xc2, 0x08, // ASM: add rdx, 8
    0x49, 0x83, 0xe9, 0x01, // ASM: sub r9, 1
    0x75, 0xf3, // ASM: jne 0x1005
];

/// A read of `r9` to follow [`COUNTED`].
const READ: [u8; 8] = [
    0x45, 0x8d, 0x51, 0x08, // ASM: lea r10d, [r9+8]
    0x45, 0x89, 0x10, // ASM: mov [r8], r10d
    0xc3, // ASM: ret
];

/// Replays the function at 0x1000 told that its third block starts with
/// `r9` holding `c`.
///
/// # Arguments
///
/// * `p` - The image.
/// * `seed` - The states' seed.
/// * `c` - The constant.
fn told_r9(p: &Program, seed: u64, c: u64) -> Replayed {
    let told = |w: &mut Witness| w.assumes[2] = Some((Key::Reg(Register::R9), c, WHOLE));
    replayed_under(p, 0x1000, seed, |_| {}, told)
}

/// The disagreements, but for those of a lane only: claim, block, place,
/// text and machine.
fn rows(r: &Replayed) -> Vec<(Claim, u64, u64, u64, u64)> {
    r.wrong()
        .iter()
        .map(|d| (d.claim, d.block, d.at, d.text, d.machine))
        .collect()
}

/// How many blocks a replay left unchecked for an equality at their start
/// that no run bore out.
fn unborne(r: &Replayed) -> usize {
    r.skipped.get(ASSUMED).copied().unwrap_or(0)
}

/// A 64-bit image of code at 0x1000 and a page of zeroed data at 0x2000.
///
/// # Arguments
///
/// * `code` - The code.
fn with_data(code: &[u8]) -> Program {
    image(Arch::X86_64, code)
}

/// An image of code at 0x1000 and a page of zeroed data at 0x2000.
///
/// # Arguments
///
/// * `arch` - The instruction set.
/// * `code` - The code.
fn image(arch: Arch, code: &[u8]) -> Program {
    let mut bytes = vec![0xcc; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    bytes.resize(0x2000, 0);
    let sections = vec![
        Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
        Section::mapped(".data", 0x2000, 0x1000, 0x1000, true, false),
    ];
    Program::raw(bytes, arch, 0, Some(0x1000), sections)
}

/// The equality a block is said to start under is checked where the
/// machine takes the branch into it, and a block it is not borne out for
/// is not checked.
///
/// The loop is left with `r9` zero. Told that the block after it starts
/// with `r9` one, the value the loop's last test compared, the replay
/// tries the loop from that 1, sees the machine leave it and finds `r9`
/// zero there: the equality is flagged at the loop's branch, the 1 the
/// block is started from against the 0 the run leaves, and the block is
/// left unchecked. Told a 5 the loop does not leave from, nothing is
/// claimed of an edge the machine did not take, and the block is as
/// little checked. Told the zero the loop does leave with, nothing is
/// flagged on any seed, whether or not a state of the loop's own leaves.
#[test]
fn an_equality_the_branch_does_not_leave_is_flagged() {
    let p = Program::raw_x64(&[&COUNTED[..], &READ].concat());
    agrees(&p, 0x1000);
    let stale = [(Claim::Branch, 0x1005, 0x1010, 1, 0)];
    for seed in 1..=16 {
        let r = told_r9(&p, seed, 1);
        assert_eq!(rows(&r), stale, "seed {seed}: {}", replay_tsv(&r));
        assert_eq!((r.checked, unborne(&r)), (2, 1), "seed {seed}");
    }
    let r = told_r9(&p, 1, 5);
    assert_eq!(rows(&r), [], "{}", replay_tsv(&r));
    assert_eq!((r.checked, unborne(&r)), (2, 1), "{}", replay_tsv(&r));
    for seed in 1..=8 {
        let r = told_r9(&p, seed, 0);
        assert_eq!(rows(&r), [], "seed {seed}: {}", replay_tsv(&r));
    }
}

/// An equality that does not hold is flagged once, also where its block
/// lies below the branch into it and is checked first.
///
/// The loop of [`COUNTED`] is written after the block it leaves into: `L:
/// ..; sub r9,1; je E; jmp L` with `E` above it. The block is checked
/// first, which tries the loop from the 1 it is told and finds the 0 the
/// loop leaves; the loop's own states, checked after it, find the same
/// where one of them leaves, and say it no second time.
#[test]
fn an_equality_is_flagged_once_where_its_block_is_checked_first() {
    let code = [
        0x49, 0x89, 0xc9, // ASM: mov r9, rcx
        0x31, 0xc0, // ASM: xor eax, eax
        0xeb, 0x08, // ASM: jmp 0x100f
        0x45, 0x8d, 0x51, 0x08, // ASM: lea r10d, [r9+8]
        0x45, 0x89, 0x10, // ASM: mov [r8], r10d
        0xc3, // ASM: ret
        0x48, 0x03, 0x02, // ASM: add rax, [rdx]
        0x48, 0x83, 0xc2, 0x08, // ASM: add rdx, 8
        0x49, 0x83, 0xe9, 0x01, // ASM: sub r9, 1
        0x74, 0xeb, // ASM: je 0x1007
        0xeb, 0xf1, // ASM: jmp 0x100f
    ];
    let p = Program::raw_x64(&code);
    let told = |w: &mut Witness| w.assumes[1] = Some((Key::Reg(Register::R9), 1, WHOLE));
    for seed in 1..=16 {
        let r = replayed_under(&p, 0x1000, seed, |_| {}, told);
        let stale = [(Claim::Branch, 0x100f, 0x101a, 1, 0)];
        assert_eq!(rows(&r), stale, "seed {seed}: {}", replay_tsv(&r));
    }
}

/// An equality is of the text's variable, whatever its register holds by
/// the time the block is entered.
///
/// After `sub rsi,3; jne L` the next block reads `rsi` as the pending
/// `rsi - 3` under `rsi == 3` and returns 8: the register holds 0 there
/// and the variable 3, and both are right. After `mov rcx,rsi; mov
/// rsi,[rcx+8]; mov [rdx],rsi; test rcx,rcx; jne L` the equality is of the
/// `rsi` the test read, which the load then replaced in a register nothing
/// reads again. Neither is a disagreement, and both blocks are checked.
#[test]
fn an_equality_of_a_variable_alone_claims_nothing_of_its_register() {
    let pending = [
        0x48, 0x83, 0xee, 0x03, // ASM: sub rsi, 3
        0x75, 0x04, // ASM: jne 0x100a
        0x8d, 0x46, 0x08, // ASM: lea eax, [rsi+8]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&pending);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1000).expect("text");
    assert!(text.contains("\nreturn 8;\n"), "{text}");
    agrees(&p, 0x1000);
    let unread = [
        0x48, 0x89, 0xf1, // ASM: mov rcx, rsi
        0x48, 0x8b, 0x71, 0x08, // ASM: mov rsi, [rcx+8]
        0x48, 0x89, 0x32, // ASM: mov [rdx], rsi
        0x48, 0x85, 0xc9, // ASM: test rcx, rcx
        0x75, 0x06, // ASM: jne 0x1015
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    agrees(&Program::raw_x64(&unread), 0x1000);
}

/// No equality is handed on through a jump.
///
/// After `cmp rcx,5; jne` the block falling out of the branch starts under
/// `rcx == 5` and the block its jump lands on under nothing: an equality
/// handed on there would be one no branch into its block bears out.
#[test]
fn no_equality_is_handed_on_through_a_jump() {
    let passed = [
        0x48, 0x83, 0xf9, 0x05, // ASM: cmp rcx, 5
        0x75, 0x07, // ASM: jne 0x100d
        0xeb, 0x01, // ASM: jmp 0x1009
        0xcc, // ASM: int3
        0x8d, 0x41, 0x08, // ASM: lea eax, [rcx+8]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&passed);
    let mut given = Vec::new();
    let r = replayed_under(&p, 0x1000, 1, |_| {}, |w| given.clone_from(&w.assumes));
    assert_eq!(claims(&r), [], "{}", replay_tsv(&r));
    let five = Some((Key::Param(0), 5, WHOLE));
    assert_eq!(given, [None, five, None, None]);
}

/// An equality of more bits than the branch compared is flagged, of a
/// register and of a parameter alike.
///
/// `cmp esi,5; jne` compares the low half of `rsi`, and `cmp ecx,-1; jne`
/// that of the first argument. Told that the block after it starts with
/// the whole variable at the constant, the replay tries the branch from a
/// state whose low half holds the constant and whose upper half anything:
/// the machine goes on into the block, and the variable is not what the
/// block is started from. The difference is above bit 32 and no lane's,
/// since the equality says what those bits hold; the block is left
/// unchecked.
#[test]
fn an_equality_of_more_bits_than_the_branch_compared_is_flagged() {
    let register = [
        0x83, 0xfe, 0x05, // ASM: cmp esi, 5
        0x75, 0x06, // ASM: jne 0x100b
        0x48, 0x89, 0x32, // ASM: mov [rdx], rsi
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let argument = [
        0x83, 0xf9, 0xff, // ASM: cmp ecx, -1
        0x75, 0x06, // ASM: jne 0x100b
        0x48, 0x89, 0x0a, // ASM: mov [rdx], rcx
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let cases = [
        (&register, Key::Reg(Register::RSI), 5),
        (&argument, Key::Param(0), u64::MAX),
    ];
    for (code, k, c) in cases {
        let p = Program::raw_x64(code);
        agrees(&p, 0x1000);
        let whole = |w: &mut Witness| w.assumes[1] = Some((k, c, WHOLE));
        let r = replayed_under(&p, 0x1000, 1, |_| {}, whole);
        let wrong = r.wrong();
        let [d] = wrong.as_slice() else {
            panic!("{k:?}: {}", replay_tsv(&r));
        };
        let at = (d.claim, d.block, d.at, d.text);
        assert_eq!(at, (Claim::Branch, 0x1000, 0x1003, c), "{k:?}");
        assert_eq!(lo32(d.machine), lo32(c), "{k:?}: {}", replay_tsv(&r));
        assert_ne!(d.machine, c, "{k:?}: {}", replay_tsv(&r));
        assert_eq!((r.checked, unborne(&r)), (2, 1), "{k:?}");
    }
}

/// An equality of a value the branch did not compare is flagged from the
/// states the branch's block is tried from.
///
/// Both ways into `P: cmp rbx,5; jne U; mov rax,rdi; ret` leave `rbx` 5 and
/// the `rbx` the function was entered with in `rdi`, so the text assigns
/// no `rbx` and `P` compares two constants. Told that the block after `P`
/// starts with `rbx` 5, a state made to hold that holds it; but every
/// state `P` is tried from goes on into the block, with whatever `rbx`
/// the function was entered with. Told an equality of `es`, which the
/// replay cannot read, nothing is compared, and the block is not checked.
#[test]
fn an_equality_of_a_value_the_branch_did_not_compare_is_flagged() {
    let code = [
        0x48, 0x83, 0xf9, 0x05, // ASM: cmp rcx, 5
        0x74, 0x0a, // ASM: je 0x1010
        0x48, 0x89, 0xdf, // ASM: mov rdi, rbx
        0xbb, 0x05, 0x00, 0x00, 0x00, // ASM: mov ebx, 5
        0xeb, 0x06, // ASM: jmp 0x1016
        0x48, 0x89, 0xdf, // ASM: mov rdi, rbx
        0x48, 0x89, 0xcb, // ASM: mov rbx, rcx
        0x48, 0x83, 0xfb, 0x05, // ASM: cmp rbx, 5
        0x75, 0x04, // ASM: jne 0x1020
        0x48, 0x89, 0xf8, // ASM: mov rax, rdi
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&code);
    let plain = replayed_with(&p, 0x1000, 1, |_| {});
    assert_eq!(claims(&plain), [], "{}", replay_tsv(&plain));
    let named = |w: &mut Witness| w.assumes[4] = Some((Key::Reg(Register::RBX), 5, WHOLE));
    let r = replayed_under(&p, 0x1000, 1, |_| {}, named);
    let found: Vec<_> = r
        .wrong()
        .iter()
        .map(|d| (d.claim, d.block, d.at, d.text))
        .collect();
    assert_eq!(
        found,
        [(Claim::Branch, 0x1016, 0x101a, 5)],
        "{}",
        replay_tsv(&r)
    );
    let unread = |w: &mut Witness| w.assumes[4] = Some((Key::Reg(Register::ES), 0, WHOLE));
    let r = replayed_under(&p, 0x1000, 1, |_| {}, unread);
    assert_eq!((rows(&r), unborne(&r)), (vec![], 1), "{}", replay_tsv(&r));
}

/// An equality of a global is borne out through memory, and one the
/// machine never enters its block under leaves the block unchecked.
///
/// `cmp dword [g],5; jne X; mov eax,[g]; ret` returns the 5 it compared.
/// The branch is tried with `g` holding 5 and falls into the block, where
/// `g` is 5: the block is checked. Told that the block starts with `g` 7,
/// the replay tries the branch with 7 there, the machine goes to `X`, and
/// nothing bears the equality out.
#[test]
fn an_equality_of_a_global_is_tried_from_memory() {
    let code = [
        0x83, 0x3d, 0xf9, 0x0f, 0x00, 0x00, 0x05, // ASM: cmp dword [rip+0xff9], 5
        0x75, 0x07, // ASM: jne 0x1010
        0x8b, 0x05, 0xf1, 0x0f, 0x00, 0x00, // ASM: mov eax, [rip+0xff1]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = with_data(&code);
    agrees(&p, 0x1000);
    let g = Key::Global(0x2000, 32);
    let mut given = Vec::new();
    replayed_under(&p, 0x1000, 1, |_| {}, |w| given.clone_from(&w.assumes));
    assert_eq!(given, [None, Some((g, 5, WHOLE)), None]);
    let seven = |w: &mut Witness| w.assumes[1] = Some((g, 7, WHOLE));
    let r = replayed_under(&p, 0x1000, 1, |_| {}, seven);
    assert_eq!(rows(&r), [], "{}", replay_tsv(&r));
    assert_eq!((r.checked, unborne(&r)), (2, 1), "{}", replay_tsv(&r));
}

/// An equality holds its constant at the width of its variable.
///
/// `cmp dword [g],-1; jne X; mov eax,[g]; ret` compares four bytes with
/// all ones, and the decoder hands the immediate over extended to 64 bits.
/// Kept so, the equality was compared at the branch against the four
/// bytes the text reads there, `0xffffffff`: a right text was flagged and
/// its block left unchecked. The same of two bytes in 32-bit code, `cmp
/// word [g],-1`, which `movzx eax, word [g]` reads as `0xffff`.
#[test]
fn an_equality_holds_its_constant_at_the_variables_width() {
    let dword = [
        0x83, 0x3d, 0xf9, 0x0f, 0x00, 0x00, 0xff, // ASM: cmp dword [rip+0xff9], -1
        0x75, 0x07, // ASM: jne 0x1010
        0x8b, 0x05, 0xf1, 0x0f, 0x00, 0x00, // ASM: mov eax, [rip+0xff1]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let word = [
        0x66, 0x83, 0x3d, 0x00, 0x20, 0x00, 0x00, 0xff, // ASM: cmp word [0x2000], -1
        0x75, 0x08, // ASM: jne 0x1012
        0x0f, 0xb7, 0x05, 0x00, 0x20, 0x00, 0x00, // ASM: movzx eax, word [0x2000]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let cases = [
        (
            image(Arch::X86_64, &dword),
            Key::Global(0x2000, 32),
            0xffff_ffff,
        ),
        (image(Arch::X86, &word), Key::Global(0x2000, 16), 0xffff),
    ];
    for (p, g, ones) in cases {
        agrees(&p, 0x1000);
        let mut given = Vec::new();
        replayed_under(&p, 0x1000, 1, |_| {}, |w| given.clone_from(&w.assumes));
        assert_eq!(given, [None, Some((g, ones, WHOLE)), None]);
    }
}

/// A run the text of the branch's block does not follow bears no equality
/// out.
///
/// `mov [h],rcx; cmp dword [g],5; jne X; mov eax,[g]; ret`, with the store
/// made to store 0 in the text. The run that takes the branch with `g` 5
/// leaves in `h` what the text does not, so the equality the next block
/// starts under is one of a text the machine did not follow: the block is
/// left unchecked. The store itself is flagged from the states its own
/// block is tried from. Made to store the low half of `rcx`, the text
/// differs in a lane only, which is no disagreement in any state: the
/// block is checked.
#[test]
fn an_equality_is_not_borne_out_by_a_run_the_text_gets_wrong() {
    let code = [
        0x48, 0x89, 0x0d, 0x01, 0x10, 0x00, 0x00, // ASM: mov [rip+0x1001], rcx
        0x83, 0x3d, 0xf2, 0x0f, 0x00, 0x00, 0x05, // ASM: cmp dword [rip+0xff2], 5
        0x75, 0x07, // ASM: jne 0x1017
        0x8b, 0x05, 0xea, 0x0f, 0x00, 0x00, // ASM: mov eax, [rip+0xfea]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = with_data(&code);
    agrees(&p, 0x1000);
    let zero = |e: &mut crate::analysis::decompile::lift::Effect| {
        if let EffectKind::Store(s) = &mut e.kind {
            s.2 = Expr::Const(0);
        }
    };
    let r = replayed_with(&p, 0x1000, 1, zero);
    assert_eq!(claims(&r), [Claim::Memory], "{}", replay_tsv(&r));
    assert_eq!((r.checked, unborne(&r)), (2, 1), "{}", replay_tsv(&r));
    let half = |e: &mut crate::analysis::decompile::lift::Effect| {
        if let EffectKind::Store(s) = &mut e.kind {
            let low = Expr::Const(0xffff_ffff);
            s.2 = Expr::Bin(Op::And, Box::new(s.2.clone()), Box::new(low));
        }
    };
    let r = replayed_with(&p, 0x1000, 1, half);
    let lanes: Vec<_> = r.disagreements.iter().map(|d| (d.claim, d.lane)).collect();
    assert_eq!(lanes, [(Claim::Memory, true)], "{}", replay_tsv(&r));
    assert_eq!((r.checked, unborne(&r)), (3, 0), "{}", replay_tsv(&r));
}

/// An equality of the low half of a slot leaves the slot's upper half to
/// the state.
///
/// After `cmp dword [rsp+8],5; jne`, `mov rax,[rsp+8]; mov [rdx],rax`
/// stores the slot whole. Told that the block starts with the slot's low
/// half 5, the replay fixes four of its bytes: a text made to store 5
/// differs from the machine in the other four, which a slot fixed whole at
/// the constant never showed. The run into the block holds the equality,
/// so the block is checked.
///
/// The proof fixes as many. `cmp [rsp+8],r8; sete al` against
/// `0x100000005` is true in one state of the slot's upper half, which no
/// state tried holds: a text made to store 0 agrees in each, and is not
/// proved, as it was with the slot fixed whole at 5.
#[test]
fn an_equality_of_a_slots_low_half_fixes_four_bytes() {
    let stores = [
        0x83, 0x7c, 0x24, 0x08, 0x05, // ASM: cmp dword [rsp+8], 5
        0x75, 0x09, // ASM: jne 0x1010
        0x48, 0x8b, 0x44, 0x24, 0x08, // ASM: mov rax, [rsp+8]
        0x48, 0x89, 0x02, // ASM: mov [rdx], rax
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let tests = [
        0x83, 0x7c, 0x24, 0x08, 0x05, // ASM: cmp dword [rsp+8], 5
        0x75, 0x16, // ASM: jne 0x101d
        0x49, 0xb8, 0x05, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
        0x00, // ASM: mov r8, 0x100000005
        0x4c, 0x39, 0x44, 0x24, 0x08, // ASM: cmp [rsp+8], r8
        0x0f, 0x94, 0xc0, // ASM: sete al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let low = |w: &mut Witness| w.assumes[1] = Some((Key::Slot(8), 5, 32));
    let p = Program::raw_x64(&stores);
    agrees(&p, 0x1000);
    let five = |e: &mut crate::analysis::decompile::lift::Effect| {
        if let EffectKind::Store(s) = &mut e.kind {
            s.2 = Expr::Const(5);
        }
    };
    let r = replayed_under(&p, 0x1000, 1, five, low);
    let upper: Vec<_> = r.disagreements.iter().map(|d| (d.claim, d.lane)).collect();
    assert_eq!(upper, [(Claim::Memory, true)], "{}", replay_tsv(&r));
    assert_eq!(unborne(&r), 0, "{}", replay_tsv(&r));
    let p = Program::raw_x64(&tests);
    agrees(&p, 0x1000);
    let zero = |e: &mut crate::analysis::decompile::lift::Effect| {
        if let EffectKind::Return(Some(v)) = &mut e.kind {
            *v = Expr::Const(0);
        }
    };
    let r = replayed_under(&p, 0x1000, 1, zero, low);
    assert_eq!(claims(&r), [], "{}", replay_tsv(&r));
    assert_eq!((r.checked, r.proved), (3, 2), "{}", replay_tsv(&r));
}

/// The header counts a block whose entry equality no run bore out as
/// unknown, by that name.
///
/// `rdrand eax` has no model, so its block cannot be tried, and the block
/// its `cmp rcx,5; jne` falls into starts under `rcx == 5` on that
/// block's word alone: it is not counted as proved, or as checked at all.
#[test]
fn a_block_whose_entry_equality_is_unchecked_is_unknown() {
    use crate::analysis::decompile::checked_header;
    let code = [
        0x0f, 0xc7, 0xf0, // ASM: rdrand eax
        0x48, 0x83, 0xf9, 0x05, // ASM: cmp rcx, 5
        0x75, 0x04, // ASM: jne 0x100d
        0x8d, 0x41, 0x08, // ASM: lea eax, [rcx+8]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    let header = checked_header(&p, &a, &Overlay::default(), 0x1000).expect("checked");
    assert_eq!(
        header,
        "// checked vs binary: statements as emitted, 1/3 blocks: 1 proved, 2 unknown; unchecked: 1 entry equality, 1 unmodeled, C spelling, later text passes"
    );
}

/// A block under an equality of a register's low half is tried, and
/// proved, with the upper half free.
///
/// After `cmp esi,5; jne` the block knows the low half of `rsi`. Its text
/// is right to store `rsi` whole; made to store 5, it differs from the
/// machine in the upper four bytes wherever the state's upper half is not
/// zero, which a start from the constant alone never showed. The replay
/// counts a difference above bit 32 as a lane's, so it is no disagreement
/// of the header's, but the block is no longer proved. The proof starts
/// such a variable as the constant under a value no state fixes, and as
/// the constant alone only where the equality is of the whole variable.
#[test]
fn an_equality_of_a_low_half_leaves_the_upper_half_free() {
    let stores = [
        0x83, 0xfe, 0x05, // ASM: cmp esi, 5
        0x75, 0x06, // ASM: jne 0x100b
        0x48, 0x89, 0x32, // ASM: mov [rdx], rsi
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&stores);
    agrees(&p, 0x1000);
    let mut given = Vec::new();
    replayed_under(&p, 0x1000, 1, |_| {}, |w| given.clone_from(&w.assumes));
    let low = (Key::Reg(Register::RSI), 5, 32);
    assert_eq!(given, [None, Some(low), None]);
    let five = replayed_with(&p, 0x1000, 1, |e| {
        if let EffectKind::Store(s) = &mut e.kind {
            s.2 = Expr::Const(5);
        }
    });
    let upper: Vec<_> = five.disagreements.iter().map(|d| d.claim).collect();
    assert_eq!(upper, [Claim::Memory], "{}", replay_tsv(&five));
    assert_eq!(five.proved, 2, "{}", replay_tsv(&five));
    let start = |n| start_term(low.0, 0xffff_ffff_0000_0005, n, 64);
    assert_eq!(start(WHOLE), Term::Const(0xffff_ffff_0000_0005));
    assert_eq!(narrow(&start(32), 32), Term::Const(5));
    assert!(!matches!(start(32), Term::Const(_)), "{:?}", start(32));
}
