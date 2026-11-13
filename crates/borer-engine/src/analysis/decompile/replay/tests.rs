use crate::isa::x86::Register;

use super::{
    Claim, Replayed, Sampling, TextCheck, Witness, replay_effects, replay_function, replay_tsv,
};
use crate::analysis::decompile::expr::{Expr, Flags, Op, UnOp};
use crate::analysis::decompile::lift::{ArgAt, Effect, EffectKind};
use crate::analysis::decompile::{decompile, decompile_with};
use crate::analysis::{Analysis, Overlay};
use crate::emulate::Emulator;
use crate::program::{Arch, Program};

/// The claims the disagreements are about, in order, but for those
/// of a lane only.
pub(super) fn claims(r: &Replayed) -> Vec<Claim> {
    r.wrong().iter().map(|d| d.claim).collect()
}

/// Replays a function's effects after `change` rewrote them.
///
/// # Arguments
///
/// * `p` - The image.
/// * `entry` - The function.
/// * `seed` - The states' seed.
/// * `change` - Rewrites one effect.
pub(super) fn replayed_with(
    p: &Program,
    entry: u64,
    seed: u64,
    change: impl Fn(&mut Effect),
) -> Replayed {
    replayed_under(p, entry, seed, change, |_| {})
}

/// Replays a function's effects after `change` rewrote them, under the
/// lifter's witness after `told` rewrote it.
///
/// # Arguments
///
/// * `p` - The image.
/// * `entry` - The function.
/// * `seed` - The states' seed.
/// * `change` - Rewrites one effect.
/// * `told` - Rewrites the witness.
///
/// # Returns
///
/// What the replay found.
pub(super) fn replayed_under(
    p: &Program,
    entry: u64,
    seed: u64,
    change: impl Fn(&mut Effect),
    told: impl FnOnce(&mut Witness),
) -> Replayed {
    replayed_in(p, &Analysis::compute(p), entry, seed, change, told)
}

/// Replays a function's effects as [`replayed_under`] does, over an
/// analysis the caller computed.
///
/// # Arguments
///
/// * `p` - The image.
/// * `a` - Its analysis.
/// * `entry` - The function.
/// * `seed` - The states' seed.
/// * `change` - Rewrites one effect.
/// * `told` - Rewrites the witness.
///
/// # Returns
///
/// What the replay found.
pub(super) fn replayed_in(
    p: &Program,
    a: &Analysis,
    entry: u64,
    seed: u64,
    change: impl Fn(&mut Effect),
    told: impl FnOnce(&mut Witness),
) -> Replayed {
    let f = a.function(entry).expect("function");
    let d = decompile_with(p, a, &Overlay::default(), entry, true, &[], true).expect("text");
    let mut effects: Vec<Vec<Effect>> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| d.effects.block(i, b.start).expect("block"))
        .collect();
    effects.iter_mut().flatten().for_each(change);
    let template = Emulator::new(p, 0).expect("emulator");
    let mut w = d.take_witness().expect("witness");
    told(&mut w);
    replay_effects::<crate::analysis::decompile::arch::X86>(
        p,
        a,
        &Overlay::default(),
        &template,
        entry,
        seed,
        (&w, &d.live.succs),
        &effects,
        usize::MAX,
        Sampling::Every,
    )
}

/// Asserts that the text of the function at `entry` agrees with the
/// emulator on the states of eight seeds, every block checked.
///
/// # Arguments
///
/// * `p` - The image.
/// * `entry` - The function.
pub(super) fn agrees(p: &Program, entry: u64) {
    let a = Analysis::compute(p);
    let f = a.function(entry).expect("function");
    for seed in 1..=8 {
        let r = replay_function(p, &a, entry, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        assert_eq!(r.checked, f.blocks.len(), "seed {seed}: {}", replay_tsv(&r));
    }
}

/// A value parked in a temporary while a reader of its variable was
/// written out is written from the temporary.
///
/// Before the call, `rbx = (rax + rbx) * 100` is written out, and first
/// `rax = rax + rbx`, which reads `rbx`; that parks `rbx`'s value, which
/// reads `rax`, in `tmp_1`. Writing the value read before all this
/// gave `rax += rbx; rbx = (rax + rbx) * 100;`, which adds `rbx` twice.
#[test]
fn a_value_parked_for_its_reader_is_written_from_its_temporary() {
    let mut code = vec![
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
        0x8b, 0x19, // ASM: mov ebx, [rcx]
        0xe8, 0xf4, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0x01, 0xd8, // ASM: add eax, ebx
        0x6b, 0xd8, 0x64, // ASM: imul ebx, eax, 100
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx, 2
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0xf0, 0x00, 0x00, 0x00, // ASM: call 0x1110
        0x01, 0xd8, // ASM: add eax, ebx
        0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 0x20
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend([
        0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax, 5
        0xc3, // ASM: ret
    ]);
    code.resize(0x110, 0xcc);
    code.extend([
        0x8d, 0x04, 0x11, // ASM: lea eax, [rcx+rdx]
        0xc3, // ASM: ret
    ]);
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// An argument holding a dead register's value passes that value, not
/// the register: the register is not written out.
///
/// `cmovne rbx, rax; mov rdx, rbx` passes the selection in `rdx`, and
/// `rbx` is restored after the call. The argument was rewritten to read
/// `rbx`, whose value was then dropped as dead, so the call passed the
/// `rbx` from before the selection: `sub_1100(7, rbx)`.
#[test]
fn an_argument_holding_a_dead_register_s_value_passes_the_value() {
    let mut code = vec![
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
        0xe8, 0x06, 0x01, 0x00, 0x00, // ASM: call 0x1110
        0x48, 0x89, 0xc3, // ASM: mov rbx, rax
        0xe8, 0xfe, 0x00, 0x00, 0x00, // ASM: call 0x1110
        0x48, 0x8b, 0x43, 0x30, // ASM: mov rax, [rbx+0x30]
        0x48, 0x85, 0xc0, // ASM: test rax, rax
        0x48, 0x0f, 0x45, 0xd8, // ASM: cmovne rbx, rax
        0x48, 0x89, 0xda, // ASM: mov rdx, rbx
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
        0xe8, 0xd6, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 0x20
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend([
        0x48, 0x8d, 0x04, 0x11, // ASM: lea rax, [rcx+rdx]
        0xc3, // ASM: ret
    ]);
    code.resize(0x110, 0xcc);
    code.extend([
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
    ]);
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// A 32-bit image of `code` at `0x1000`.
///
/// # Arguments
///
/// * `code` - The bytes.
fn x86(code: &[u8]) -> Program {
    let mut p = Program::raw_x64(code);
    p.arch = Arch::X86;
    p.is_64 = false;
    p
}

/// Both halves of a widening multiply are computed from the operands
/// as they were before either is written.
///
/// The second `imul` writes `edx` out early for its size, and first
/// `eax = ebx`, which reads the old `edx`; `eax`'s new value, held
/// aside meanwhile, read `edx` too and so named the new one:
/// `edx = smulhi32(x, y); eax = x * y;` with `x` reading `edx`.
#[test]
fn a_widening_multiply_reads_its_operands_before_either_half_is_written() {
    let code = [
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x83, 0xec, 0x18, // ASM: sub esp, 0x18
        0x53, // ASM: push ebx
        0x57, // ASM: push edi
        0x8b, 0x4d, 0x08, // ASM: mov ecx, [ebp+8]
        0x8b, 0x55, 0x0c, // ASM: mov edx, [ebp+0xc]
        0x8b, 0x45, 0xf0, // ASM: mov eax, [ebp-0x10]
        0x8b, 0x5d, 0x08, // ASM: mov ebx, [ebp+8]
        0x8b, 0x5b, 0x0c, // ASM: mov ebx, [ebx+0xc]
        0x8b, 0x0c, 0x88, // ASM: mov ecx, [eax+ecx*4]
        0x8b, 0x04, 0x88, // ASM: mov eax, [eax+ecx*4]
        0x03, 0xc0, // ASM: add eax, eax
        0x8b, 0x54, 0xc2, 0x08, // ASM: mov edx, [edx+eax*8+8]
        0x8b, 0x04, 0xd3, // ASM: mov eax, [ebx+edx*8]
        0x2b, 0x45, 0x10, // ASM: sub eax, [ebp+0x10]
        0x8b, 0x5c, 0xd3, 0x04, // ASM: mov ebx, [ebx+edx*8+4]
        0xf7, 0x6d, 0x1c, // ASM: imul dword [ebp+0x1c]
        0x2b, 0x5d, 0x14, // ASM: sub ebx, [ebp+0x14]
        0x89, 0x45, 0xf8, // ASM: mov [ebp-8], eax
        0x8b, 0xfa, // ASM: mov edi, edx
        0x8b, 0xc3, // ASM: mov eax, ebx
        0xf7, 0x6d, 0x18, // ASM: imul dword [ebp+0x18]
        0x3b, 0xfa, // ASM: cmp edi, edx
        0x7c, 0x04, // ASM: jl 0x1045
        0x5f, // ASM: pop edi
        0x5b, // ASM: pop ebx
        0xc9, // ASM: leave
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x5f, // ASM: pop edi
        0x5b, // ASM: pop ebx
        0xc9, // ASM: leave
        0xc3, // ASM: ret
    ];
    agrees(&x86(&code), 0x1000);
}

/// A call's arguments read what the variables hold once the call has
/// written out what it must, not what they held before.
///
/// The counter whose address escaped is stored back before the call,
/// which may read it; the argument, computed from the counter before
/// the increment, was rendered before that store and so read the new
/// count: `local_28 += 1; sub_1110(a1 + (local_28 << 6));`.
#[test]
fn an_argument_reads_the_slot_as_it_was_before_the_call_stores_it() {
    let mut code = vec![
        0x55, // ASM: push rbp
        0x48, 0x83, 0xec, 0x50, // ASM: sub rsp, 0x50
        0x48, 0x8d, 0x6c, 0x24, 0x50, // ASM: lea rbp, [rsp+0x50]
        0x48, 0x89, 0x4d, 0xd8, // ASM: mov [rbp-0x28], rcx
        0x48, 0x8d, 0x4d, 0xe0, // ASM: lea rcx, [rbp-0x20]
        0xe8, 0xe9, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0x48, 0x8b, 0x45, 0xe0, // ASM: mov rax, [rbp-0x20]
        0x48, 0x8b, 0x4d, 0xd8, // ASM: mov rcx, [rbp-0x28]
        0x48, 0x89, 0xc2, // ASM: mov rdx, rax
        0x48, 0xc1, 0xe2, 0x06, // ASM: shl rdx, 6
        0x48, 0x01, 0xd1, // ASM: add rcx, rdx
        0x48, 0xff, 0xc0, // ASM: inc rax
        0x48, 0x89, 0x45, 0xe0, // ASM: mov [rbp-0x20], rax
        0xe8, 0xdb, 0x00, 0x00, 0x00, // ASM: call 0x1110
        0x48, 0x8b, 0x45, 0xe0, // ASM: mov rax, [rbp-0x20]
        0x48, 0x83, 0xc4, 0x50, // ASM: add rsp, 0x50
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend([
        0x48, 0xc7, 0x01, 0x00, 0x00, 0x00, 0x00, // ASM: mov qword [rcx], 0
        0xc3, // ASM: ret
    ]);
    code.resize(0x110, 0xcc);
    code.extend([
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
        0xc3, // ASM: ret
    ]);
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// An argument register the callee keeps is written out before the call
/// when its value reads memory, and the call then passes it by name.
///
/// `movzx r9d, word [r9+4]` before a call that leaves `r9` alone is
/// written out, the callee being free to change the memory it read;
/// the arguments, rendered before that, read the new `r9`: `r9 =
/// *(uint16_t*)(r9 + 4); sub_1100(.., *(uint16_t*)(r9 + 4), ..)`.
#[test]
fn an_argument_the_callee_keeps_is_passed_as_written_out() {
    let mut code = vec![
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x30, // ASM: sub rsp, 0x30
        0x48, 0x89, 0xcb, // ASM: mov rbx, rcx
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x03, // ASM: je 0x100f
        0x49, 0x89, 0xc9, // ASM: mov r9, rcx
        0x41, 0x0f, 0xb7, 0x41, 0x06, // ASM: movzx eax, word [r9+6]
        0x45, 0x0f, 0xb7, 0x49, 0x04, // ASM: movzx r9d, word [r9+4]
        0x66, 0x89, 0x44, 0x24, 0x20, // ASM: mov [rsp+0x20], ax
        0xe8, 0xdd, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0x44, 0x01, 0xc8, // ASM: add eax, r9d
        0x01, 0xd8, // ASM: add eax, ebx
        0x48, 0x83, 0xc4, 0x30, // ASM: add rsp, 0x30
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend([
        0x44, 0x89, 0xc8, // ASM: mov eax, r9d
        0x03, 0x44, 0x24, 0x28, // ASM: add eax, [rsp+0x28]
        0x01, 0xc8, // ASM: add eax, ecx
        0x01, 0xd0, // ASM: add eax, edx
        0x44, 0x01, 0xc0, // ASM: add eax, r8d
        0xc3, // ASM: ret
    ]);
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// A call through a register calls what the register holds when a
/// write-out before the call protects the readers of a variable the
/// target was loaded through.
///
/// `mov eax, [esi+0x1ac]; ...; mov dword [ebp+8], 0; mov eax, [eax+4];
/// call eax` with `&a1` pushed: the store to the escaped `a1` is written
/// out before the call, and `eax`, which read the old `a1`, was dropped
/// as a register nothing reads after the call: `(*eax)(..)` called a
/// register the text never set.
#[test]
fn a_call_through_a_register_keeps_the_register_s_value() {
    let code = [
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x56, // ASM: push esi
        0x8b, 0x75, 0x08, // ASM: mov esi, [ebp+8]
        0x8b, 0x86, 0xac, 0x01, 0x00, 0x00, // ASM: mov eax, [esi+0x1ac]
        0x8d, 0x4d, 0x08, // ASM: lea ecx, [ebp+8]
        0x51, // ASM: push ecx
        0xc7, 0x45, 0x08, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [ebp+8], 0
        0x8b, 0x40, 0x04, // ASM: mov eax, [eax+4]
        0x56, // ASM: push esi
        0xff, 0xd0, // ASM: call eax
        0x83, 0xc4, 0x08, // ASM: add esp, 8
        0x8b, 0x45, 0x08, // ASM: mov eax, [ebp+8]
        0x5e, // ASM: pop esi
        0x5d, // ASM: pop ebp
        0xc3, // ASM: ret
    ];
    agrees(&x86(&code), 0x1000);
}

/// A value the dataflow held in one of its own temporaries does not
/// reach a successor: the emission numbers its temporaries apart, so
/// the successor would read a variable the text never sets.
///
/// `xchg [rcx], al` parks the byte it reads in a temporary; both
/// successors of the compare on it read `al`, and the one that stores
/// it wrote `*(uint8_t*)rdx = tmp_1073741825;`.
#[test]
fn a_dataflow_temporary_stays_in_its_block() {
    let code = [
        0x31, 0xc0, // ASM: xor eax, eax
        0x86, 0x01, // ASM: xchg [rcx], al
        0x3c, 0x02, // ASM: cmp al, 2
        0x75, 0x03, // ASM: jne 0x100b
        0x88, 0x02, // ASM: mov [rdx], al
        0xc3, // ASM: ret
        0xfe, 0xc0, // ASM: inc al
        0xc3, // ASM: ret
    ];
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// A store a successor reads part of through another offset is written
/// out on the edge, not dropped as dead.
///
/// The dword stored at `[rsp+8]` is read back as its top byte, at
/// `[rsp+0xb]`, where three paths meet; slot liveness by offset saw no
/// read of `[rsp+8]` there and dropped the store, still pending, on the
/// two paths that skip the byte stores over it.
#[test]
fn a_store_read_through_another_offset_reaches_the_reader() {
    let code = [
        0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+8], 0
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x0e, // ASM: je 0x101a
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x0a, // ASM: je 0x101a
        0xc6, 0x44, 0x24, 0x08, 0x01, // ASM: mov byte [rsp+8], 1
        0xc6, 0x44, 0x24, 0x0b, 0x02, // ASM: mov byte [rsp+0xb], 2
        0x0f, 0xb6, 0x44, 0x24, 0x0b, // ASM: movzx eax, byte [rsp+0xb]
        0xc3, // ASM: ret
    ];
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// A bit count or byte swap of a 32-bit register counts or swaps 32
/// bits, whatever the 64-bit variable holding it holds above them.
///
/// `mov eax, 0x3f; bsr eax, ecx; xor eax, 0x1f` is the leading zeros of
/// `ecx`, and `bswap eax` after `mov eax, ecx` swaps its four bytes; both
/// read `rcx` whole: `lzcnt(a1)` counted from bit 63, `bswap(a1)` swapped
/// eight bytes.
#[test]
fn a_count_or_swap_of_a_32_bit_register_works_on_32_bits() {
    let code = [
        0xb8, 0x3f, 0x00, 0x00, 0x00, // ASM: mov eax, 0x3f
        0x0f, 0xbd, 0xc1, // ASM: bsr eax, ecx
        0x83, 0xf0, 0x1f, // ASM: xor eax, 0x1f
        0x89, 0x02, // ASM: mov [rdx], eax
        0x89, 0xc8, // ASM: mov eax, ecx
        0x0f, 0xc8, // ASM: bswap eax
        0x89, 0x42, 0x04, // ASM: mov [rdx+4], eax
        0xc3, // ASM: ret
    ];
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// A switch through a byte table switches on the index the table is
/// read at, the offset the code took from the value included.
///
/// `add eax, -2; cmp eax, 3; ja default; movzx eax, byte [eax+T]; jmp
/// [eax*4+J]`: the byte read's address folds the `-2` into `T`, and
/// taking the table's constant off the address left the switch on the
/// value from before the `-2`, with cases that count from after it.
#[test]
fn a_switch_through_a_byte_table_keeps_the_index_s_offset() {
    let mut code = vec![
        0x8b, 0xc1, // ASM: mov eax, ecx
        0x90, // ASM: nop
        0x90, // ASM: nop
        0x83, 0xc0, 0xfe, // ASM: add eax, -2
        0x83, 0xf8, 0x03, // ASM: cmp eax, 3
        0x77, 0x1f, // ASM: ja 0x102b
        0xb9, 0x03, 0x00, 0x00, 0x00, // ASM: mov ecx, 3
        0x0f, 0xb6, 0x80, 0x38, 0x10, 0x00, 0x00, // ASM: movzx eax, byte [eax+0x1038]
        0xff, 0x24, 0x85, 0x30, 0x10, 0x00, 0x00, // ASM: jmp [eax*4+0x1030]
        0xb8, 0x0a, 0x00, 0x00, 0x00, // ASM: mov eax, 10
        0xc3, // ASM: ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // ASM: mov eax, 20
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    code.resize(0x30, 0xcc);
    code.extend([0x1f, 0x10, 0x00, 0x00, 0x25, 0x10, 0x00, 0x00]);
    code.extend([0x00, 0x01, 0x01, 0x00]);
    agrees(&x86(&code), 0x1000);
}

/// A switch through a byte table switches on the byte table's index
/// when the byte it reads is written out for a case that reads it.
///
/// One case returns the byte the dispatch read into `eax`, so the read
/// is written out at the dispatch's end, `eax = *(uint8_t*)(eax + T)`,
/// and the switch, which read that same value, was rewritten to read
/// `eax`: `switch (eax)` on the byte, with cases that number the index.
#[test]
fn a_switch_through_a_byte_table_reads_the_index_not_the_byte() {
    let mut code = vec![
        0x8b, 0xc1, // ASM: mov eax, ecx
        0x90, // ASM: nop
        0x90, // ASM: nop
        0x83, 0xc0, 0xfe, // ASM: add eax, -2
        0x83, 0xf8, 0x03, // ASM: cmp eax, 3
        0x77, 0x19, // ASM: ja 0x1025
        0xb9, 0x03, 0x00, 0x00, 0x00, // ASM: mov ecx, 3
        0x0f, 0xb6, 0x80, 0x34, 0x10, 0x00, 0x00, // ASM: movzx eax, byte [eax+0x1034]
        0xff, 0x24, 0x85, 0x2c, 0x10, 0x00, 0x00, // ASM: jmp [eax*4+0x102c]
        0xb8, 0x0a, 0x00, 0x00, 0x00, // ASM: mov eax, 10
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    code.resize(0x2c, 0xcc);
    code.extend([0x1f, 0x10, 0x00, 0x00, 0x25, 0x10, 0x00, 0x00]);
    code.extend([0x01, 0x00, 0x00, 0x01]);
    agrees(&x86(&code), 0x1000);
}

/// A value that reads a variable a predecessor writes out at its end is
/// written out with it, not carried into the successor.
///
/// The store over `a1` is written out at the block's end for the path
/// that reads it, and so is `eax`, which read `a1` before the store;
/// `ecx`, which read the `eax` from before that, was carried into the
/// other successor as pending, where it read the new `eax`.
#[test]
fn a_reader_of_a_value_written_out_at_a_join_is_written_out_too() {
    let mut code = vec![
        0xe8, 0xfb, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0x8b, 0x08, // ASM: mov ecx, [eax]
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp+4]
        0xc7, 0x44, 0x24, 0x04, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [esp+4], 0
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x06, // ASM: je 0x101d
        0x01, 0xc8, // ASM: add eax, ecx
        0x89, 0x44, 0x24, 0x04, // ASM: mov [esp+4], eax
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp+4]
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend([
        0xb8, 0x00, 0x10, 0x00, 0x00, // ASM: mov eax, 0x1000
        0xc3, // ASM: ret
    ]);
    agrees(&x86(&code), 0x1000);
}

/// A value that reads one a predecessor writes out at its end only to
/// keep it right is written out with it too, and not carried on.
///
/// `ebx` is written out where the paths meet, and before it the store of
/// the old `ebx` over `a2`, which reads it, and before that `edx`, which
/// read `a2` before the store; `edx` was still carried into the join as
/// pending, where it read the new `a2`: `*a2` for the `*edx` the code
/// reads.
#[test]
fn a_value_written_out_for_a_reader_s_sake_is_not_carried_on() {
    let code = [
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x8b, 0x55, 0x0c, // ASM: mov edx, [ebp+0xc]
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x06, // ASM: je 0x1010
        0x89, 0x5d, 0x0c, // ASM: mov [ebp+0xc], ebx
        0x8b, 0x5d, 0x10, // ASM: mov ebx, [ebp+0x10]
        0x8b, 0x02, // ASM: mov eax, [edx]
        0x0f, 0xaf, 0xc3, // ASM: imul eax, ebx
        0x5d, // ASM: pop ebp
        0xc3, // ASM: ret
    ];
    agrees(&x86(&code), 0x1000);
}

/// A slot the text names reads at the width the text declares it.
///
/// The byte stored at `[rsp+7]` is written out for the join that reads
/// it, and the compare, which read the same byte, reads `local_11`, a
/// `uint8_t`; read as a whole word, the variable held the seven bytes
/// above it too and the branch went the other way.
#[test]
fn a_named_slot_reads_at_its_declared_width() {
    let code = [
        0x48, 0x83, 0xec, 0x18, // ASM: sub rsp, 0x18
        0xc6, 0x44, 0x24, 0x07, 0x09, // ASM: mov byte [rsp+7], 9
        0x4d, 0x85, 0xc0, // ASM: test r8, r8
        0x74, 0x0e, // ASM: je 0x101c
        0x8a, 0x01, // ASM: mov al, [rcx]
        0x88, 0x44, 0x24, 0x07, // ASM: mov [rsp+7], al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
        0x48, 0x39, 0xd0, // ASM: cmp rax, rdx
        0x73, 0x07, // ASM: jae 0x1023
        0x0f, 0xb6, 0x44, 0x24, 0x07, // ASM: movzx eax, byte [rsp+7]
        0xeb, 0x05, // ASM: jmp 0x1028
        0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax, 5
        0x48, 0x83, 0xc4, 0x18, // ASM: add rsp, 0x18
        0xc3, // ASM: ret
    ];
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// A slot the debug information names replays as the slot it names.
///
/// The check binds a declared variable to its frame offset by the
/// name's spelling, which `flag` carries none of; the function's own
/// debug record states it, so the machine still runs on the slot the
/// text means, at the width the text declares.
#[test]
fn a_debug_named_slot_still_checks_as_its_slot() {
    let code = [
        0x48, 0x83, 0xec, 0x18, // ASM: sub rsp, 0x18
        0xc6, 0x44, 0x24, 0x07, 0x09, // ASM: mov byte [rsp+7], 9
        0x4d, 0x85, 0xc0, // ASM: test r8, r8
        0x74, 0x0e, // ASM: je 0x101c
        0x8a, 0x01, // ASM: mov al, [rcx]
        0x88, 0x44, 0x24, 0x07, // ASM: mov [rsp+7], al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
        0x48, 0x39, 0xd0, // ASM: cmp rax, rdx
        0x73, 0x07, // ASM: jae 0x1023
        0x0f, 0xb6, 0x44, 0x24, 0x07, // ASM: movzx eax, byte [rsp+7]
        0xeb, 0x05, // ASM: jmp 0x1028
        0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax, 5
        0x48, 0x83, 0xc4, 0x18, // ASM: add rsp, 0x18
        0xc3, // ASM: ret
    ];
    use super::super::decompile;
    let mut p = Program::raw_x64(&code);
    p.debug_functions.push(crate::dwarf::Subprogram {
        low_pc: 0x1000,
        name: "probe".to_owned(),
        parameters: Vec::new(),
        return_type: None,
        locals: [(-0x11i64, "flag".to_owned())].into_iter().collect(),
    });
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1000).unwrap_or_default();
    assert!(text.contains("flag"), "the local does not render:\n{text}");
    assert!(
        !text.contains("local_11"),
        "the slot renders synthesized:\n{text}"
    );
    agrees(&p, 0x1000);
}

/// A branch on a value a block's end writes out reads it as it was,
/// whatever order the write-outs take.
///
/// `shl r8d, 16; or r11d, r8d; cmp r11d, 0xff`: the join writes out
/// `r8` and `r11`, the compare was moved onto `r8` for `r8 << 16` ahead
/// of `r8`'s write-out, and `r11`'s, which came first, parked it as
/// `tmp_1 = r11 | r8` while `r8` was still the old one.
#[test]
fn a_branch_on_values_written_out_at_a_join_reads_them_as_they_were() {
    let code = [
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x13, // ASM: je 0x1017
        0x41, 0xc1, 0xe0, 0x10, // ASM: shl r8d, 16
        0x45, 0x09, 0xc3, // ASM: or r11d, r8d
        0x41, 0x81, 0xfb, 0xff, 0x00, 0x00, 0x00, // ASM: cmp r11d, 0xff
        0x77, 0x03, // ASM: ja 0x1017
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0x4c, 0x89, 0xc0, // ASM: mov rax, r8
        0x4c, 0x01, 0xd8, // ASM: add rax, r11
        0xc3, // ASM: ret
    ];
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// A register's save beside a store the successor reads is no claim of
/// the text's.
///
/// `push esi` saves `esi` at `[esp-4]`, and `push edi`, with `edi`
/// written first, stores a value just below it that the successor
/// reads; the slot of the save, named later where `ecx` is pushed over
/// it, had its bytes held against the text as a store of the lifter's,
/// because a store lay within a word below them.
#[test]
fn a_save_beside_a_live_store_is_no_claim_of_the_text() {
    let code = [
        0x8b, 0xff, // ASM: mov edi, edi
        0x56, // ASM: push esi
        0x57, // ASM: push edi
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x01, // ASM: je 0x1009
        0x47, // ASM: inc edi
        0x5f, // ASM: pop edi
        0x5e, // ASM: pop esi
        0x51, // ASM: push ecx
        0x0f, 0xb6, 0x04, 0x24, // ASM: movzx eax, byte [esp]
        0x59, // ASM: pop ecx
        0xc3, // ASM: ret
    ];
    agrees(&x86(&code), 0x1000);
}

/// A call through a read-only pointer to a dispatch thunk calls what
/// the thunk jumps through, and the check follows it there.
///
/// `call [rip+X]` with `X` holding the address of `jmp rax` (the CFG
/// dispatcher) is a call through `rax`, as the text says; the check
/// knew the thunk only by a direct call's target, so it held the
/// thunk's own address against the text's target.
#[test]
fn a_call_through_a_pointer_to_a_dispatch_thunk_is_checked_through_it() {
    use crate::program::Section;
    let mut bytes = vec![0xcc; 0x2000];
    let code = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0xff, 0x15, 0xf3, 0x0f, 0x00, 0x00, // ASM: call [rip+0xff3]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    bytes[..code.len()].copy_from_slice(&code);
    bytes[0x20..0x22].copy_from_slice(&[0xff, 0xe0]); // ASM: jmp rax
    bytes[0x1000..0x1008].copy_from_slice(&0x1020u64.to_le_bytes());
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    agrees(&p, 0x1000);
}

/// A structure's zero fill, a vector register zeroed and stored sixteen
/// bytes wide, is checked, and so is its store pending at an edge.
///
/// The block was outside the integer subset and the pending bytes
/// unknown, so a text writing half the zeros the join reads half of
/// passed.
#[test]
fn a_zero_fill_is_checked_where_it_is_pending() {
    let code = [
        0x48, 0x83, 0xec, 0x38, // ASM: sub rsp, 0x38
        0x0f, 0x57, 0xc0, // ASM: xorps xmm0, xmm0
        0x0f, 0x11, 0x44, 0x24, 0x20, // ASM: movups [rsp+0x20], xmm0
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x05, // ASM: je 0x1015
        0x48, 0x89, 0x4c, 0x24, 0x20, // ASM: mov [rsp+0x20], rcx
        0x48, 0x8b, 0x44, 0x24, 0x28, // ASM: mov rax, [rsp+0x28]
        0x48, 0x83, 0xc4, 0x38, // ASM: add rsp, 0x38
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&code);
    agrees(&p, 0x1000);
    let r = replayed_with(&p, 0x1000, 1, |e| {
        if e.at == 0x100e
            && let EffectKind::Assign(_, _, bits @ 128) = &mut e.kind
        {
            *bits = 64;
        }
    });
    assert!(claims(&r).contains(&Claim::Slot), "{}", replay_tsv(&r));
}

/// A block entered from one side of a branch is tried only from states
/// on that side.
///
/// The text's `lzcnt(a1 - 1)` stands for `bsr` under the `a1 > 1` that
/// leads to it, and from `a1 == 1`, which never gets there, the
/// machine's `bsr` of zero left its destination as it was.
#[test]
fn a_block_runs_under_the_branch_into_it() {
    let code = [
        0x48, 0x83, 0xf9, 0x01, // ASM: cmp rcx, 1
        0x76, 0x0d, // ASM: jbe 0x1013
        0x48, 0x83, 0xe9, 0x01, // ASM: sub rcx, 1
        0x48, 0x0f, 0xbd, 0xc1, // ASM: bsr rax, rcx
        0x48, 0x83, 0xf0, 0x3f, // ASM: xor rax, 0x3f
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    for seed in 1..=64 {
        let r = replay_function(&p, &a, 0x1000, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        assert_eq!(r.checked, 3, "seed {seed}: {}", replay_tsv(&r));
    }
}

/// The branch a block runs under is found through a block that only
/// jumps to it: `cmp; jbe` falls into `jmp`, and the scan behind the
/// jump runs where the compare let it.
#[test]
fn a_block_runs_under_the_branch_a_jump_passes_on() {
    let code = [
        0x48, 0x83, 0xf9, 0x01, // ASM: cmp rcx, 1
        0x76, 0x02, // ASM: jbe 0x1008
        0xeb, 0x03, // ASM: jmp 0x100b
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0x48, 0x83, 0xe9, 0x01, // ASM: sub rcx, 1
        0x48, 0x0f, 0xbd, 0xc1, // ASM: bsr rax, rcx
        0x48, 0x83, 0xf0, 0x3f, // ASM: xor rax, 0x3f
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    for seed in 1..=64 {
        let r = replay_function(&p, &a, 0x1000, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
    }
}

/// A forward bit scan of zero leaves its destination as it was, so the
/// text's `bsf(a1)` of a zero `a1` says nothing, where it read as 64
/// on the side of the branch only a nonzero `a1` takes.
#[test]
fn a_forward_bit_scan_of_zero_is_undefined() {
    let code = [
        0x48, 0x89, 0x4c, 0x24, 0x08, // ASM: mov [rsp+8], rcx
        0x48, 0x83, 0xec, 0x18, // ASM: sub rsp, 0x18
        0x48, 0x8b, 0x44, 0x24, 0x20, // ASM: mov rax, [rsp+0x20]
        0x48, 0x0f, 0xbc, 0xc0, // ASM: bsf rax, rax
        0x89, 0x04, 0x24, // ASM: mov [rsp], eax
        0x0f, 0x95, 0xc0, // ASM: setne al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
        0x85, 0xc0, // ASM: test eax, eax
        0x74, 0x0a, // ASM: je 0x1029
        0x8b, 0x04, 0x24, // ASM: mov eax, [rsp]
        0x48, 0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8], rax
        0xeb, 0x09, // ASM: jmp 0x1032
        0x48, 0xc7, 0x44, 0x24, 0x08, 0x40, 0x00, 0x00, 0x00, // ASM: mov qword [rsp+8], 0x40
        0x48, 0x8b, 0x44, 0x24, 0x08, // ASM: mov rax, [rsp+8]
        0x48, 0x83, 0xc4, 0x18, // ASM: add rsp, 0x18
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    for seed in 1..=64 {
        let r = replay_function(&p, &a, 0x1000, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
    }
}

/// A float store is compared, not counted as unreadable, and a lifted
/// float with the wrong sign is flagged on every seed.
///
/// `movss`/`addss` leave a single in `xmm0` whose store the text
/// writes: the block was outside the checked subset and the store's
/// value unreadable, so a text storing the negation of the sum passed.
#[test]
fn a_float_store_is_compared_and_a_wrong_one_flagged() {
    let p = Program::raw_x64(&[
        0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
        0xf3, 0x0f, 0x58, 0x41, 0x04, // ASM: addss xmm0,[rcx+4]
        0xf3, 0x0f, 0x11, 0x41, 0x08, // ASM: movss [rcx+8],xmm0
        0xc3, // ASM: ret
    ]);
    for seed in 1..=8 {
        let a = Analysis::compute(&p);
        let r = replay_function(&p, &a, 0x1000, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        assert_eq!(r.checked, 1, "seed {seed}: {}", replay_tsv(&r));
        assert!(
            r.compared.get(&Claim::Memory).copied().unwrap_or(0) > 0,
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        assert_eq!(
            r.unreadable.get(&Claim::Memory).copied().unwrap_or(0),
            0,
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        let r = replayed_with(&p, 0x1000, seed, |e| {
            if let EffectKind::Store(s) = &mut e.kind {
                s.2 = Expr::Un(UnOp::Neg, Box::new(s.2.clone()));
            }
        });
        assert_eq!(
            claims(&r),
            [Claim::Memory],
            "seed {seed}: {}",
            replay_tsv(&r)
        );
    }
}

/// A branch on a float compare goes the machine's way, and the
/// successors reading the float register are compared at the width
/// its expression computes at.
///
/// `ucomiss` after a sum in `xmm0`, `ja` over two blocks that each
/// store the single: unordered on a NaN, the compare takes `ja` the
/// machine's way, and each successor's claim on `xmm0` reads the
/// single the machine's own `addss` rounding left.
#[test]
fn a_branch_on_a_float_compare_agrees_with_the_machine() {
    let p = Program::raw_x64(&[
        0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
        0xf3, 0x0f, 0x58, 0x41, 0x04, // ASM: addss xmm0,[rcx+4]
        0x0f, 0x2e, 0x41, 0x08, // ASM: ucomiss xmm0,[rcx+8]
        0x77, 0x0a, // ASM: ja 0x1019
        0xf3, 0x0f, 0x11, 0x00, // ASM: movss [rax],xmm0
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0xf3, 0x0f, 0x11, 0x00, // ASM: movss [rax],xmm0
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ]);
    for seed in 1..=8 {
        let a = Analysis::compute(&p);
        let r = replay_function(&p, &a, 0x1000, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        assert_eq!(r.checked, 3, "seed {seed}: {}", replay_tsv(&r));
        assert!(
            r.compared.get(&Claim::Branch).copied().unwrap_or(0) > 0,
            "seed {seed}: {}",
            replay_tsv(&r)
        );
    }
}

/// A float compare of parameters reads as float, although their
/// variables carry no float type for the condition's operands to see.
///
/// `ucomiss xmm0, xmm1; seta al; and al, 1` on two float arguments:
/// the lifter writes `Cmp` over the two bare parameters, which as
/// integers order differently than the floats the machine compares,
/// and the `and` after the `setcc` sets flags of its own that the
/// condition never read; the compare instruction is the witness.
#[test]
fn a_float_compare_of_parameters_reads_as_float() {
    let p = Program::raw_x64(&[
        0x0f, 0x2e, 0xc1, // ASM: ucomiss xmm0,xmm1
        0x0f, 0x97, 0xc0, // ASM: seta al
        0x24, 0x01, // ASM: and al,1
        0x0f, 0xb6, 0xc0, // ASM: movzx eax,al
        0xc3, // ASM: ret
    ]);
    for seed in 1..=8 {
        let a = Analysis::compute(&p);
        let r = replay_function(&p, &a, 0x1000, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        assert_eq!(r.checked, 1, "seed {seed}: {}", replay_tsv(&r));
        assert!(
            r.compared.get(&Claim::Return).copied().unwrap_or(0) > 0,
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        assert_eq!(
            r.unreadable.get(&Claim::Return).copied().unwrap_or(0),
            0,
            "seed {seed}: {}",
            replay_tsv(&r)
        );
    }
}

/// A one-block packed-integer fixture: its block is checked, not
/// counted as float/vector, its vector store is compared, and a store
/// of a lane the machine does not hold is flagged, on every seed.
///
/// # Arguments
///
/// * `code` - The function's bytes, at `0x1000`.
fn packed_agrees(code: &[u8]) {
    let p = Program::raw_x64(code);
    for seed in 1..=8 {
        let a = Analysis::compute(&p);
        let r = replay_function(&p, &a, 0x1000, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        assert_eq!(r.checked, 1, "seed {seed}: {}", replay_tsv(&r));
        assert!(
            r.compared.get(&Claim::Memory).copied().unwrap_or(0) > 0,
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        let r = replayed_with(&p, 0x1000, seed, |e| {
            if let EffectKind::Store(s) = &mut e.kind {
                s.2 = Expr::Call("pxor".to_owned(), vec![s.2.clone(), Expr::Const(1)]);
            }
        });
        assert_eq!(
            claims(&r),
            [Claim::Memory],
            "seed {seed}: {}",
            replay_tsv(&r)
        );
    }
}

/// A 128-bit vector move, sixteen bytes loaded and stored back through
/// memory, is checked against the machine.
#[test]
fn a_vector_move_is_compared_and_a_wrong_one_flagged() {
    packed_agrees(&[
        0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
        0xf3, 0x0f, 0x7f, 0x41, 0x10, // ASM: movdqu [rcx+0x10],xmm0
        0xc3, // ASM: ret
    ]);
}

/// The packed bitwise operations over whole lanes are checked against
/// the machine.
#[test]
fn packed_logic_is_compared_and_a_wrong_one_flagged() {
    packed_agrees(&[
        0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
        0xf3, 0x0f, 0x6f, 0x4a, 0x10, // ASM: movdqu xmm1,[rcx+0x10]
        0x66, 0x0f, 0xef, 0xc1, // ASM: pxor xmm0,xmm1
        0x66, 0x0f, 0xdb, 0xc1, // ASM: pand xmm0,xmm1
        0x66, 0x0f, 0xeb, 0xc1, // ASM: por xmm0,xmm1
        0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
        0xc3, // ASM: ret
    ]);
}

/// Lane-wise packed addition and subtraction, at every lane width, are
/// checked against the machine.
#[test]
fn packed_add_and_sub_are_compared_and_a_wrong_one_flagged() {
    packed_agrees(&[
        0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
        0xf3, 0x0f, 0x6f, 0x4a, 0x10, // ASM: movdqu xmm1,[rcx+0x10]
        0x66, 0x0f, 0xfc, 0xc1, // ASM: paddb xmm0,xmm1
        0x66, 0x0f, 0xfd, 0xc1, // ASM: paddw xmm0,xmm1
        0x66, 0x0f, 0xfe, 0xc1, // ASM: paddd xmm0,xmm1
        0x66, 0x0f, 0xd4, 0xc1, // ASM: paddq xmm0,xmm1
        0x66, 0x0f, 0xf8, 0xc1, // ASM: psubb xmm0,xmm1
        0x66, 0x0f, 0xf9, 0xc1, // ASM: psubw xmm0,xmm1
        0x66, 0x0f, 0xfa, 0xc1, // ASM: psubd xmm0,xmm1
        0x66, 0x0f, 0xfb, 0xc1, // ASM: psubq xmm0,xmm1
        0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
        0xc3, // ASM: ret
    ]);
}

/// The narrowing packs, signed and unsigned, are checked against the
/// machine.
#[test]
fn packed_narrowing_packs_are_compared_and_a_wrong_one_flagged() {
    packed_agrees(&[
        0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
        0xf3, 0x0f, 0x6f, 0x4a, 0x10, // ASM: movdqu xmm1,[rcx+0x10]
        0x66, 0x0f, 0x6b, 0xc1, // ASM: packssdw xmm0,xmm1
        0x66, 0x0f, 0x63, 0xc1, // ASM: packsswb xmm0,xmm1
        0x66, 0x0f, 0x67, 0xc1, // ASM: packuswb xmm0,xmm1
        0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
        0xc3, // ASM: ret
    ]);
}

/// The unpacks, low and high at every lane width, are checked against
/// the machine.
#[test]
fn packed_unpacks_are_compared_and_a_wrong_one_flagged() {
    packed_agrees(&[
        0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
        0xf3, 0x0f, 0x6f, 0x4a, 0x10, // ASM: movdqu xmm1,[rcx+0x10]
        0x66, 0x0f, 0x60, 0xc1, // ASM: punpcklbw xmm0,xmm1
        0x66, 0x0f, 0x61, 0xc1, // ASM: punpcklwd xmm0,xmm1
        0x66, 0x0f, 0x62, 0xc1, // ASM: punpckldq xmm0,xmm1
        0x66, 0x0f, 0x6c, 0xc1, // ASM: punpcklqdq xmm0,xmm1
        0x66, 0x0f, 0x68, 0xc1, // ASM: punpckhbw xmm0,xmm1
        0x66, 0x0f, 0x69, 0xc1, // ASM: punpckhwd xmm0,xmm1
        0x66, 0x0f, 0x6a, 0xc1, // ASM: punpckhdq xmm0,xmm1
        0x66, 0x0f, 0x6d, 0xc1, // ASM: punpckhqdq xmm0,xmm1
        0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
        0xc3, // ASM: ret
    ]);
}

/// A doubleword shuffle by immediate is checked against the machine.
#[test]
fn a_packed_shuffle_is_compared_and_a_wrong_one_flagged() {
    packed_agrees(&[
        0xf3, 0x0f, 0x6f, 0x0a, // ASM: movdqu xmm1,[rdx]
        0x66, 0x0f, 0x70, 0xc1, 0x1b, // ASM: pshufd xmm0,xmm1,0x1b
        0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
        0xc3, // ASM: ret
    ]);
}

/// The lane shifts by immediate, logical, arithmetic and by whole
/// bytes, are checked against the machine.
#[test]
fn packed_shifts_are_compared_and_a_wrong_one_flagged() {
    packed_agrees(&[
        0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
        0x66, 0x0f, 0x71, 0xf0, 0x03, // ASM: psllw xmm0,3
        0x66, 0x0f, 0x72, 0xf0, 0x04, // ASM: pslld xmm0,4
        0x66, 0x0f, 0x73, 0xf0, 0x05, // ASM: psllq xmm0,5
        0x66, 0x0f, 0x71, 0xd0, 0x06, // ASM: psrlw xmm0,6
        0x66, 0x0f, 0x72, 0xd0, 0x07, // ASM: psrld xmm0,7
        0x66, 0x0f, 0x73, 0xd0, 0x08, // ASM: psrlq xmm0,8
        0x66, 0x0f, 0x71, 0xe0, 0x09, // ASM: psraw xmm0,9
        0x66, 0x0f, 0x72, 0xe0, 0x0a, // ASM: psrad xmm0,10
        0x66, 0x0f, 0x73, 0xf8, 0x02, // ASM: pslldq xmm0,2
        0x66, 0x0f, 0x73, 0xd8, 0x03, // ASM: psrldq xmm0,3
        0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
        0xc3, // ASM: ret
    ]);
}

/// Three blocks: `cmp rcx, 1; jbe` to a `return 0` or a `return 1`.
const THREE_BLOCKS: [u8; 15] = [
    0x48, 0x83, 0xf9, 0x01, // ASM: cmp rcx, 1
    0x76, 0x06, // ASM: jbe 0x100c
    0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
    0xc3, // ASM: ret
    0x31, 0xc0, // ASM: xor eax, eax
    0xc3, // ASM: ret
];

/// An answer says what of it was checked against the binary, on its
/// second line, and the text every other reader parses says nothing.
///
/// The check reads the decompilation the text comes from: one is built,
/// its witness taken, and the memo keeps the text and the check.
#[test]
fn an_answer_says_what_of_it_was_checked() {
    use crate::analysis::decompile::{checked_header, decompile_named, with_header};
    let p = Program::raw_x64(&THREE_BLOCKS);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let header = checked_header(&p, &a, &o, 0x1000).expect("checked");
    assert_eq!(
        header,
        "// checked vs binary: statements as emitted, 3/3 blocks: 3 proved vs lift; unchecked: C spelling, later text passes"
    );
    let text = decompile_named(&p, &a, &o, 0x1000).expect("text");
    assert!(!text.contains("checked vs binary"), "{text}");
    let shown = with_header(&text, Some(&header));
    assert_eq!(shown.lines().next(), text.lines().next());
    assert_eq!(shown.lines().nth(1), Some(header.as_str()));
    assert_eq!(shown.lines().count(), text.lines().count() + 1);
    assert_eq!(a.derived.held("plain_text"), 1);
    assert_eq!(a.derived.held("text_check"), 1);
    let memo = crate::analysis::decompiled_cached(&p, &a, &o, o.fingerprint(), 0x1000);
    let d = memo.as_ref().as_ref().expect("memoized");
    assert!(d.take_witness().is_none(), "the check took the witness");
}

/// A block whose compare reaches a condition the text writes over
/// unknown flags is not counted as agreeing: the compare has no
/// statement, so nothing of it was checked.
///
/// `J2`'s `je` reads the zero flag of `cmp r9d, 9` on one edge and, past
/// `J1`'s `jb`, of `cmp edx, 5` or `cmp r8d, 7` on the other.
#[test]
fn a_compare_whose_flags_the_text_loses_is_unchecked() {
    use crate::analysis::decompile::{checked_header, decompile_named};
    let p = Program::raw_x64(&[
        0x85, 0xc9, // ASM: test ecx, ecx
        0x78, 0x0f, // ASM: js P3
        0x74, 0x05, // ASM: je P2
        0x83, 0xfa, 0x05, // ASM: P1: cmp edx, 5
        0xeb, 0x04, // ASM: jmp J1
        0x41, 0x83, 0xf8, 0x07, // ASM: P2: cmp r8d, 7
        0x72, 0x0b, // ASM: J1: jb OUT1
        0xeb, 0x04, // ASM: jmp J2
        0x41, 0x83, 0xf9, 0x09, // ASM: P3: cmp r9d, 9
        0x74, 0x09, // ASM: J2: je OUT2
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: OUT1: mov eax, 1
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: OUT2: mov eax, 2
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile_named(&p, &a, &o, 0x1000).expect("text");
    let header = checked_header(&p, &a, &o, 0x1000).expect("checked");
    assert!(text.contains("FLAGS_UNKNOWN"), "{text}");
    assert!(header.contains("6 flags across blocks"), "{header}\n{text}");
}

/// A block reading the thread block is counted unchecked as what it is,
/// not as a float or vector form.
#[test]
fn a_thread_block_read_is_no_float() {
    use crate::analysis::decompile::checked_header;
    let p = Program::raw_x64(&[
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[0x30]
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let header = checked_header(&p, &a, &Overlay::default(), 0x1000).expect("checked");
    assert!(header.contains("1 fs/gs access"), "{header}");
    assert!(!header.contains("float/vector"), "{header}");
}

/// A statement the machine does not bear out is named in the header by
/// its instruction, so a block compared and found wrong never reads as
/// agreement; past a few, the rest are counted.
#[test]
fn the_header_names_the_statements_the_binary_contradicts() {
    let check = TextCheck {
        blocks: 8,
        checked: 8,
        proved: 5,
        unchecked: Vec::new(),
        disagree: vec![0x404171],
    };
    assert_eq!(
        check.header(),
        "// checked vs binary: statements as emitted, 8/8 blocks: 5 proved vs lift, 3 tested x3 states; disagree at 0x404171; unchecked: C spelling, later text passes"
    );
    let many = TextCheck {
        blocks: 9,
        disagree: (0..6).map(|i| 0x401000 + i).collect(),
        unchecked: vec![("float/vector", 1)],
        ..check
    };
    assert_eq!(
        many.header(),
        "// checked vs binary: statements as emitted, 8/9 blocks: 5 proved vs lift, 3 tested x3 states, 1 unknown; disagree at 0x401000, 0x401001, 0x401002, 0x401003 (+2 more); unchecked: 1 float/vector, C spelling, later text passes"
    );
}

/// A float a function returns in `xmm0`, and one a successor reads
/// there, is proved in the low lane the claim compares: the same float
/// operations on the same operands on both sides.
#[test]
fn a_float_in_a_vector_register_is_proved_in_its_lane() {
    let p = Program::raw_x64(&[
        0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0, [rcx]
        0xf2, 0x0f, 0x58, 0x41, 0x08, // ASM: addsd xmm0, [rcx+8]
        0x66, 0x0f, 0x2e, 0xc1, // ASM: ucomisd xmm0, xmm1
        0x77, 0x04, // ASM: ja 0x1013
        0xf2, 0x0f, 0x59, 0xc0, // ASM: mulsd xmm0, xmm0
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    for seed in 1..=4 {
        let r = replay_function(&p, &a, 0x1000, seed);
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        assert!(r.checked >= 2, "seed {seed}: {}", replay_tsv(&r));
        assert_eq!(r.proved, r.checked, "seed {seed}: {}", replay_tsv(&r));
    }
}

/// The return address a call to the next instruction pushes is a frame
/// word the lift does not name; the proof holds it as no known value
/// and proves the rest.
#[test]
fn a_frame_word_the_lift_does_not_name_holds_no_known_value() {
    let p = x86(&[
        0xe8, 0x00, 0x00, 0x00, 0x00, // ASM: call 0x1005
        0x59, // ASM: pop ecx
        0x89, 0xc8, // ASM: mov eax, ecx
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let r = replay_function(&p, &a, 0x1000, 1);
    assert_eq!(claims(&r), [], "{}", replay_tsv(&r));
    assert_eq!((r.checked, r.proved), (1, 1), "{}", replay_tsv(&r));
}

/// Every block of a function whose text says what the binary does is
/// proved over every state, not only checked on the states tried.
#[test]
fn a_true_text_is_proved_over_every_state() {
    let p = Program::raw_x64(&THREE_BLOCKS);
    let a = Analysis::compute(&p);
    let r = replay_function(&p, &a, 0x1000, 1);
    assert_eq!((r.checked, r.proved), (3, 3), "{}", replay_tsv(&r));
    assert!(r.refuted.is_empty(), "{}", replay_tsv(&r));
}

/// A branch the text writes wrong for one value in two to the 31 is
/// refuted by a state the proof chose.
///
/// No state tried draws that value: `2 * x == 10` at 32 bits holds for
/// `x == 0x80000005` too, where `x == 5` does not.
#[test]
fn a_claim_no_state_tried_tells_apart_is_refuted() {
    let p = Program::raw_x64(&[
        0x83, 0xf9, 0x05, // ASM: cmp ecx, 5
        0x74, 0x06, // ASM: je 0x100b
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ]);
    for seed in 1..=4 {
        let r = replayed_with(&p, 0x1000, seed, |e| {
            if let EffectKind::Branch(c) = &mut e.kind
                && let Flags::Cmp(x, Expr::Const(5), w) = &c.flags
            {
                c.flags = Flags::Cmp(
                    Expr::Bin(Op::Mul, Box::new(x.clone()), Box::new(Expr::Const(2))),
                    Expr::Const(10),
                    *w,
                );
            }
        });
        assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        assert!(
            r.refuted
                .iter()
                .any(|d| d.claim == Claim::Branch && !d.lane),
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        assert_eq!(r.proved, r.checked - 1, "seed {seed}: {}", replay_tsv(&r));
    }
}

/// A block outside what the proof models is left to the states tried,
/// counted by why, never proved.
#[test]
fn a_block_the_proof_does_not_model_is_only_tested() {
    let p = Program::raw_x64(&[
        0x0f, 0xbc, 0xc1, // ASM: bsf eax, ecx
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let r = replay_function(&p, &a, 0x1000, 1);
    assert_eq!((r.checked, r.proved), (1, 0), "{}", replay_tsv(&r));
    assert_eq!(r.unproved.get("a bit scan"), Some(&1), "{}", replay_tsv(&r));
}

/// Blocks proved over every state are graded apart from those only the
/// states tried agree on, and a grade no block has is left out.
#[test]
fn the_header_grades_blocks_proved_tested_and_unknown() {
    let all = TextCheck {
        blocks: 4,
        checked: 4,
        proved: 4,
        unchecked: Vec::new(),
        disagree: Vec::new(),
    };
    assert_eq!(
        all.header(),
        "// checked vs binary: statements as emitted, 4/4 blocks: 4 proved vs lift; unchecked: C spelling, later text passes"
    );
    let none = TextCheck {
        checked: 3,
        proved: 0,
        unchecked: vec![("over budget", 1)],
        ..all
    };
    assert_eq!(
        none.header(),
        "// checked vs binary: statements as emitted, 3/4 blocks: 0 proved vs lift, 3 tested x3 states, 1 unknown; unchecked: 1 over budget, C spelling, later text passes"
    );
}

/// A text memoized before any answer's check, without the lifter's
/// witness, is checked all the same, and the check says the same.
#[test]
fn a_text_memoized_first_is_checked_the_same() {
    use crate::analysis::decompile::{checked_header, decompile_named};
    let p = Program::raw_x64(&THREE_BLOCKS);
    let o = Overlay::default();
    let first = Analysis::compute(&p);
    let header = checked_header(&p, &first, &o, 0x1000);
    let later = Analysis::compute(&p);
    assert!(decompile_named(&p, &later, &o, 0x1000).is_some());
    assert_eq!(checked_header(&p, &later, &o, 0x1000), header);
    assert!(header.is_some());
}

/// Blocks past the budget are counted unchecked, by that reason, and
/// the blocks before it are tried.
#[test]
fn blocks_past_the_budget_are_counted_unchecked() {
    let p = Program::raw_x64(&THREE_BLOCKS);
    let a = Analysis::compute(&p);
    let f = a.function(0x1000).expect("function");
    let d = decompile_with(&p, &a, &Overlay::default(), 0x1000, true, &[], true).expect("text");
    let effects: Vec<Vec<Effect>> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| d.effects.block(i, b.start).expect("block"))
        .collect();
    let template = Emulator::new(&p, 0).expect("emulator");
    let w = d.take_witness().expect("witness");
    let r = replay_effects::<crate::analysis::decompile::arch::X86>(
        &p,
        &a,
        &Overlay::default(),
        &template,
        0x1000,
        1,
        (&w, &d.live.succs),
        &effects,
        1,
        Sampling::UntilProved,
    );
    assert_eq!(
        TextCheck::of(&r).header(),
        "// checked vs binary: statements as emitted, 1/3 blocks: 1 proved vs lift, 2 unknown; unchecked: 2 over budget, C spelling, later text passes"
    );
}

/// A jump through a table of offsets from the table's own address, its
/// index unbounded, is a computed goto, not a tail call.
///
/// `rcx` holds the table's entry, no argument, which the text passed as
/// one, and a function returning nothing then dropped the call whole.
#[test]
fn an_unbounded_relative_jump_table_is_a_computed_goto() {
    let code = [
        0x48, 0x81, 0xec, 0x98, 0x00, 0x00, 0x00, // ASM: sub rsp, 0x98
        0x48, 0x8b, 0x09, // ASM: mov rcx, [rcx]
        0x48, 0x83, 0xe9, 0x02, // ASM: sub rcx, 2
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, 2
        0x48, 0x0f, 0x43, 0xc1, // ASM: cmovae rax, rcx
        0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, // ASM: mov [rsp+0x88], rax
        0x48, 0x8b, 0x8c, 0x24, 0x88, 0x00, 0x00, 0x00, // ASM: mov rcx, [rsp+0x88]
        0x48, 0x8d, 0x05, 0x26, 0x00, 0x00, 0x00, // ASM: lea rax, [rip+0x26]
        0x48, 0x63, 0x0c, 0x88, // ASM: movsxd rcx, dword [rax+rcx*4]
        0x48, 0x01, 0xc8, // ASM: add rax, rcx
        0xff, 0xe0, // ASM: jmp rax
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x48, 0x81, 0xc4, 0x98, 0x00, 0x00, 0x00, // ASM: add rsp, 0x98
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, 2
        0x48, 0x81, 0xc4, 0x98, 0x00, 0x00, 0x00, // ASM: add rsp, 0x98
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, // ASM: int3 (x3)
        0xe3, 0xff, 0xff, 0xff, 0xf0, 0xff, 0xff, 0xff,
    ];
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1000).expect("text");
    assert!(
        text.contains("goto *var1;") && !text.contains("return (*"),
        "{text}"
    );
    agrees(&p, 0x1000);
}

/// A computed goto's target, when more than a name or a number, is
/// parenthesized: `goto *T + x;` reads as a jump to `T` plus something.
#[test]
fn a_computed_goto_parenthesizes_its_target() {
    let code = [
        0x48, 0x8d, 0x05, 0x19, 0x00, 0x00, 0x00, // ASM: lea rax, [rip+0x19]
        0x48, 0x63, 0x0c, 0x88, // ASM: movsxd rcx, dword [rax+rcx*4]
        0x48, 0x01, 0xc8, // ASM: add rax, rcx
        0xff, 0xe0, // ASM: jmp rax
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, 2
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (x4)
        0xf0, 0xff, 0xff, 0xff, 0xf6, 0xff, 0xff, 0xff,
    ];
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1000).expect("text");
    assert!(text.contains("goto *(0x1020 + "), "{text}");
    agrees(&p, 0x1000);
}

/// A store pending at a block's start that no later read reaches is the
/// text's to drop, even inside a wider slot the successor reads part of.
///
/// The dword stored over the top half of the qword at `[rsp+0x10]` is
/// pending where the paths meet, and the join reads only the low dword;
/// the store's bytes were held against the text as bytes of the qword.
#[test]
fn a_dead_store_inside_a_wider_live_slot_is_the_text_s_to_drop() {
    let code = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x4c, 0x89, 0x44, 0x24, 0x10, // ASM: mov [rsp+0x10], r8
        0x89, 0x4c, 0x24, 0x14, // ASM: mov [rsp+0x14], ecx
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x05, // ASM: je 0x1016
        0x90, // ASM: nop
        0x90, // ASM: nop
        0x90, // ASM: nop
        0xeb, 0x08, // ASM: jmp 0x101e
        0xc7, 0x44, 0x24, 0x14, 0x07, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x14], 7
        0x8b, 0x44, 0x24, 0x10, // ASM: mov eax, [rsp+0x10]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    agrees(&Program::raw_x64(&code), 0x1000);
}

/// A value read through a computed frame address is written out before
/// a slot it may have read is.
///
/// `mov ecx, [ebp+ebx*4-0x10]` reads an array of the frame that reaches
/// `[ebp-4]`, stored right after it and written out where the paths
/// meet; `ecx`, carried as pending, read the slot's new value where
/// `ebx` indexes it.
#[test]
fn a_read_through_a_frame_address_is_written_out_before_the_slots_it_reads() {
    let code = [
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x83, 0xec, 0x10, // ASM: sub esp, 0x10
        0xba, 0x03, 0x00, 0x00, 0x00, // ASM: mov edx, 3
        0x8b, 0x4c, 0x9d, 0xf0, // ASM: mov ecx, [ebp+ebx*4-0x10]
        0x83, 0x65, 0xfc, 0x00, // ASM: and dword [ebp-4], 0
        0x85, 0xc0, // ASM: test eax, eax
        0x74, 0x09, // ASM: je 0x1020
        0x8b, 0xc1, // ASM: mov eax, ecx
        0xc7, 0x45, 0xfc, 0x05, 0x00, 0x00, 0x00, // ASM: mov dword [ebp-4], 5
        0x03, 0x45, 0xfc, // ASM: add eax, [ebp-4]
        0xc9, // ASM: leave
        0xc3, // ASM: ret
    ];
    agrees(&x86(&code), 0x1000);
}

/// The text as written agrees with the emulator on every state, and a
/// statement made false is flagged at its instruction.
///
/// A store of a wrong value, a branch on the inverted condition, a
/// return of the wrong value, a call passing a wrong argument.
#[test]
fn a_false_statement_is_flagged_where_it_stands() {
    let branchy = Program::raw_x64(&[
        0x89, 0x51, 0x08, // ASM: mov [rcx+8], edx
        0x83, 0xc2, 0x01, // ASM: add edx, 1
        0x83, 0xfa, 0x05, // ASM: cmp edx, 5
        0x7c, 0x03, // ASM: jl 0x100e
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ]);
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x8d, 0x4a, 0x07, // ASM: lea ecx, [rdx+7]
        0xe8, 0x14, 0x00, 0x00, 0x00, // ASM: call 0x1020
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0x8d, 0x41, 0x01, // ASM: lea eax, [rcx+1]
        0xc3, // ASM: ret
    ]);
    let caller = Program::raw_x64(&code);
    let a = Analysis::compute(&branchy);
    for seed in 1..=8 {
        for p in [&branchy, &caller] {
            let a = Analysis::compute(p);
            let r = replay_function(p, &a, 0x1000, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
            assert!(r.checked >= 2, "seed {seed}: {}", replay_tsv(&r));
        }
        let r = replay_function(&branchy, &a, 0x1000, seed);
        for claim in [Claim::Memory, Claim::Branch, Claim::Return] {
            assert!(
                r.compared.get(&claim).copied().unwrap_or(0) > 0,
                "seed {seed}: {}",
                replay_tsv(&r)
            );
        }
        let not = |e: &Expr| Expr::Un(UnOp::Not, Box::new(e.clone()));
        let r = replayed_with(&branchy, 0x1000, seed, |e| {
            if let EffectKind::Store(s) = &mut e.kind {
                s.2 = not(&s.2);
            }
        });
        assert_eq!(
            claims(&r),
            [Claim::Memory],
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        assert_eq!(r.disagreements[0].at, 0x1000);
        let r = replayed_with(&branchy, 0x1000, seed, |e| {
            if let EffectKind::Branch(c) = &mut e.kind {
                *c = c.invert();
            }
        });
        assert_eq!(
            claims(&r),
            [Claim::Branch],
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        assert_eq!(r.disagreements[0].at, 0x1009);
        let r = replayed_with(&branchy, 0x1000, seed, |e| {
            if let EffectKind::Return(Some(v)) = &mut e.kind {
                *v = not(v);
            }
        });
        assert_eq!(
            claims(&r),
            [Claim::Return, Claim::Return],
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        let r = replayed_with(&caller, 0x1000, seed, |e| {
            if let EffectKind::Call(c) = &mut e.kind {
                for (at, v) in &mut c.args {
                    if *at == ArgAt::Reg(Register::RCX) {
                        *v = Expr::Bin(Op::Add, Box::new(v.clone()), Box::new(Expr::Const(1)));
                    }
                }
            }
        });
        assert_eq!(
            claims(&r),
            [Claim::Argument],
            "seed {seed}: {}",
            replay_tsv(&r)
        );
        assert_eq!(r.disagreements[0].at, 0x1007);
    }
}

/// A call through a 32-bit address of 64-bit code is held to the target
/// at the address the machine wraps at 4 GiB.
///
/// `mov ecx,0xfffffffc; call [ecx+0x100c]` reads its target at 0x1008.
/// The replay summed the address at 64 bits, read nothing at
/// 0x100001008, and left the target unread. The proof summed it so too:
/// `call [ecx+8]` of any `rcx` was neither proved nor refuted.
#[test]
fn a_call_through_a_32_bit_address_reads_the_wrapped_target() {
    let code = [
        0xb9, 0xfc, 0xff, 0xff, 0xff, // ASM: mov ecx, 0xfffffffc
        0x67, 0xff, 0x91, 0x0c, 0x10, 0x00, 0x00, // ASM: call [ecx+0x100c]
        0xc3, // ASM: ret
    ];
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    let r = replay_function(&p, &a, 0x1000, 1);
    let read = |m: &std::collections::BTreeMap<Claim, usize>| m.get(&Claim::Target).copied();
    assert_eq!(
        (
            read(&r.compared).is_some_and(|n| n > 0),
            read(&r.unreadable)
        ),
        (true, None),
        "{}",
        replay_tsv(&r)
    );
    assert_eq!(claims(&r), [], "{}", replay_tsv(&r));
    let any = Program::raw_x64(&[
        0x67, 0xff, 0x51, 0x08, // ASM: call [ecx+8]
        0xc3, // ASM: ret
    ]);
    let r = replay_function(&any, &Analysis::compute(&any), 0x1000, 1);
    assert_eq!((r.proved, r.checked), (2, 2), "{}", replay_tsv(&r));
}
