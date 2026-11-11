use super::{
    Effect, Fact, Read, Sweep, Verified, in_parts, st_register, verify, verify_mir, verify_tsv,
};
use crate::analysis::decompile::expr::{Expr, Key, Op, Ty, UnOp};
use crate::analysis::{Analysis, Overlay};
use crate::isa::x86::Register;
use crate::program::{Arch, Program, Section, Symbol, SymbolKind};

/// Lists the kinds of the disagreements, in order.
fn kinds(out: &Verified) -> Vec<Fact> {
    out.mismatches.iter().map(|m| m.fact).collect()
}

/// Builds a raw x86-64 image with `code` at 0x1000 and a zeroed data
/// section at 0x2000.
///
/// The data section's first cell holds the module's TLS index the way
/// an unlinked image's `_tls_index` does: zero, the loader binding it
/// at runtime.
///
/// # Arguments
///
/// * `code` - The bytes placed at `0x1000`; at most one page.
fn tls_image(code: &[u8]) -> Program {
    let mut bytes = vec![0xcc; 0x1000];
    bytes.resize(0x2000, 0);
    bytes[..code.len()].copy_from_slice(code);
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".data", 0x2000, 0x1000, 0x1000, true, false),
        ],
    )
}

/// A part that panics fails the whole check, in one part and in eight
/// alike, and a check that ends counted every function it was handed.
///
/// A part whose thread panicked was once left out of the sum, which
/// then read as a check of fewer functions with nothing wrong.
#[test]
fn a_part_that_panics_fails_the_whole_check() {
    let count = |part: &[u64]| Verified {
        functions: part.len(),
        ..Verified::default()
    };
    for n in [64, 512] {
        let entries: Vec<u64> = (0..n).collect();
        assert_eq!(in_parts(&entries, count).functions, entries.len());
        let failed = std::panic::catch_unwind(|| {
            in_parts(&entries, |part| {
                assert!(!part.contains(&40), "function 40 does not check");
                count(part)
            })
        });
        assert!(failed.is_err(), "{n} functions summed with a part missing");
    }
}

/// Reading the lifted values through MIR compares what reading them
/// as expressions does.
///
/// Both agree with the emulator on every fact: 32-bit arithmetic wraps
/// at 32 bits and the branch compares the low halves.
#[test]
fn the_mir_reads_what_the_expressions_read() {
    let p = Program::raw_x64(&[
        0x89, 0xc8, // ASM: mov eax, ecx
        0x29, 0xd0, // ASM: sub eax, edx
        0x6b, 0xc0, 0x03, // ASM: imul eax, eax, 3
        0xc1, 0xf8, 0x02, // ASM: sar eax, 2
        0x0f, 0xaf, 0xc1, // ASM: imul eax, ecx
        0x83, 0xf8, 0x05, // ASM: cmp eax, 5
        0x7c, 0x01, // ASM: jl 0x1013
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    for seed in 1..=8 {
        let expr = verify(&p, &a, &[0x1000], seed);
        let mir = verify_mir(&p, &a, &[0x1000], seed);
        assert_eq!(mir, expr, "seed {seed}: {}", verify_tsv(&mir));
        assert!(
            mir.mismatches.is_empty(),
            "seed {seed}: {}",
            verify_tsv(&mir)
        );
        let branches = mir.facts.get(&Fact::Branch).map(|t| t.compared);
        assert_eq!(branches, Some(1), "seed {seed}: {}", verify_tsv(&mir));
    }
}

/// A value the evaluator cannot read is unreadable even when a load on
/// the way read memory the block wrote, as expressions and through MIR.
///
/// The block stores to `[rcx]`. `[rcx] + t` with `t` a temporary no
/// state holds reads the stored bytes, then fails: which of the two an
/// evaluator meets first is its own order, so the count must not hang
/// on it. `[rcx]` alone still reads as stale.
#[test]
fn an_unreadable_value_stays_unreadable_whatever_it_read() {
    let p = Program::raw_x64(&[
        0x48, 0x89, 0x11, // ASM: mov [rcx], rdx
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    let stored = Expr::Deref(Box::new(Expr::Var(Key::Reg(Register::RCX))), Ty::U64);
    let unknown = Expr::Var(Key::Tmp(u32::MAX));
    let sum = |l: &Expr, r: &Expr| Expr::Bin(Op::Add, Box::new(l.clone()), Box::new(r.clone()));
    for mir in [false, true] {
        let sweep = Sweep::new(&p, 1, mir).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        let ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        assert_eq!(ran.read(&stored), Read::Stale, "mir {mir}");
        for e in [sum(&stored, &unknown), sum(&unknown, &stored)] {
            assert_eq!(ran.read(&e), Read::Unreadable, "mir {mir}: {e:?}");
        }
    }
}

/// A lifting with a wrong stored value, or with its branch condition
/// flipped, is flagged on every seed.
///
/// Every register still agrees: the store and the branch are facts of
/// their own, which a check of registers alone passed.
#[test]
fn a_wrong_store_or_a_flipped_branch_is_flagged() {
    let p = Program::raw_x64(&[
        0x89, 0x51, 0x08, // ASM: mov [rcx+8], edx
        0x83, 0xc2, 0x01, // ASM: add edx, 1
        0x83, 0xfa, 0x05, // ASM: cmp edx, 5
        0x7c, 0x03, // ASM: jl 0x100e
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        let ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        ran.compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        for fact in [Fact::Store, Fact::Branch] {
            let compared = out.facts.get(&fact).map(|t| t.compared);
            assert_eq!(compared, Some(1), "seed {seed}: {}", verify_tsv(&out));
        }

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        for effect in &mut ran.effects {
            if let Effect::Store { value, .. } = effect {
                *value = Expr::Un(UnOp::Not, Box::new(value.clone()));
            }
        }
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Store],
            "seed {seed}: {}",
            verify_tsv(&out)
        );

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        if let Some((_, cond)) = &mut ran.branch {
            *cond = cond.invert();
        }
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Branch],
            "seed {seed}: {}",
            verify_tsv(&out)
        );
    }
}

/// The x87 stack a block leaves is compared, and a lifted sum the text
/// gets backwards is flagged on every seed.
///
/// `fadd` leaves its result in `st0`, so the block's end state, not a
/// store, carries what the lift computed; flipping the lifted value's
/// sign disagrees with the emulator's for every load the seeds plant.
#[test]
fn the_x87_stack_is_compared() {
    let p = Program::raw_x64(&[
        0xd9, 0x01, // ASM: fld dword [rcx]
        0xdc, 0x41, 0x08, // ASM: fadd qword [rcx+8]
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(
            out.facts.get(&Fact::X87).map(|t| t.compared),
            Some(1),
            "seed {seed}: {}",
            verify_tsv(&out)
        );

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        let key = Key::Reg(st_register(0));
        let v = ran.env.vals.get(&key).cloned().expect("st0 value");
        ran.env.vals.insert(key, Expr::Un(UnOp::Neg, Box::new(v)));
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::X87],
            "seed {seed}: {}",
            verify_tsv(&out)
        );
    }
}

/// The xmm lanes a block leaves are compared, and a lifted value the
/// text gets wrong is flagged on every seed.
///
/// `movss`/`addss` leave their single in `xmm0`'s low lane and `movq`
/// an integer in `xmm2`'s, so the block's end state, not a store,
/// carries what the lift computed: the single compares as the single
/// the machine's own `addss` rounding left, never as a double's bits
/// read over it, and negating it or flipping the integer lane's low bit
/// disagrees with the emulator for every load the seeds plant.
#[test]
fn the_xmm_registers_are_compared() {
    let p = Program::raw_x64(&[
        0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
        0xf3, 0x0f, 0x58, 0x41, 0x04, // ASM: addss xmm0,[rcx+4]
        0x66, 0x48, 0x0f, 0x6e, 0xd0, // ASM: movq xmm2,rax
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(
            out.facts.get(&Fact::Xmm).map(|t| t.compared),
            Some(16),
            "seed {seed}: {}",
            verify_tsv(&out)
        );

        for &(reg, flip) in &[(Register::XMM0, false), (Register::XMM2, true)] {
            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            let key = Key::Reg(reg);
            let v = ran.env.vals.get(&key).cloned().expect("xmm value");
            let wrong = if flip {
                Expr::Bin(Op::Xor, Box::new(v), Box::new(Expr::Const(1)))
            } else {
                Expr::Un(UnOp::Neg, Box::new(v))
            };
            ran.env.vals.insert(key, wrong);
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Xmm],
                "seed {seed}, {reg:?}: {}",
                verify_tsv(&out)
            );
        }
    }
}

/// A `movd` lane is lifted as the 32 bits the machine writes, so it
/// compares exactly wherever a seed puts bits above bit 31.
///
/// `movd xmm0, ecx` writes the low 32 bits of the lane and zeroes the
/// rest; the lift narrows `ecx` to those bits, so the whole-read
/// known roughness for a 32-bit source no longer reaches
/// the lane: every lane compares, the bucket the sweep counts apart
/// stays empty, and no seed disagrees.
#[test]
fn a_movd_lane_is_lifted_as_the_32_bits_the_machine_writes() {
    let p = Program::raw_x64(&[
        0x66, 0x0f, 0x6e, 0xc1, // ASM: movd xmm0,ecx
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        let t = out.facts.get(&Fact::Xmm).copied().unwrap_or_default();
        assert_eq!(t.compared, 16, "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(t.lane, 0, "seed {seed}: {}", verify_tsv(&out));
    }
}

/// The segment registers a block leaves are compared, and a lifted move
/// of one the text gets wrong is flagged on every seed.
///
/// `mov es, ecx` moves a selector and `mov eax, es` reads it back, so
/// the block's end state carries both what the lift wrote and what it
/// read back: the five registers nothing moved compare as the clear
/// values both sides start from, and negating the lifted `es` disagrees
/// with the emulator's for every seed the sweep plants.
#[test]
fn the_segment_registers_are_compared() {
    let p = Program::raw_x64(&[
        0x8e, 0xc1, // ASM: mov es,ecx
        0x8c, 0xc0, // ASM: mov eax,es
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(
            out.facts.get(&Fact::Segment).map(|t| t.compared),
            Some(6),
            "seed {seed}: {}",
            verify_tsv(&out)
        );

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        let key = Key::Reg(Register::ES);
        let v = ran.env.vals.get(&key).cloned().expect("es value");
        ran.env.vals.insert(key, Expr::Un(UnOp::Not, Box::new(v)));
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Segment],
            "seed {seed}: {}",
            verify_tsv(&out)
        );
    }
}

/// The TLS slots a block reads are compared through the address the
/// entry state walks the thread's TLS array to, and a lifted value the
/// text gets wrong is flagged on every seed.
///
/// `TR` walks `gs:[0x58]` to the TLS block, reads slot 0x10 into `rax`
/// and `rdx` and stores both reads; the lift folds each read to the
/// pseudo-global `TLS_BASE + 0x10` (the constructor `Tls::Tls` before
/// it registered its singleton there), which the evaluator reads at
/// the walked address so both sides see the same bytes: the two reads
/// compare equal and the stores of them compare, while the register
/// holding the block itself still names the segment selector and
/// counts as unreadable. Flipping a read's low bit disagrees on its
/// register, and flipping the stored values disagrees on both stores.
#[test]
fn tls_slot_reads_compare_through_the_walked_block() {
    let mut p = tls_image(&[
        0x48, 0x8b, 0xd9, // ASM: mov rbx,rcx
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, // ASM: mov rax,gs:[0x58]
        0x8b, 0x0d, 0xee, 0x0f, 0x00, 0x00, // ASM: mov ecx,[rip+0xfee] -> 0x2000 (the index)
        0x48, 0x8b, 0x04, 0xc8, // ASM: mov rax,[rax+rcx*8]
        0x48, 0x89, 0x58, 0x10, // ASM: mov [rax+0x10],rbx
        0xc3, // ASM: ret
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, // ASM: mov rax,gs:[0x58]
        0x8b, 0x0d, 0xd6, 0x0f, 0x00, 0x00, // ASM: mov ecx,[rip+0xfd6] -> 0x2000
        0x4c, 0x8b, 0x04, 0xc8, // ASM: mov r8,[rax+rcx*8]
        0x49, 0x8b, 0x40, 0x10, // ASM: mov rax,[r8+0x10]
        0x49, 0x8b, 0x50, 0x10, // ASM: mov rdx,[r8+0x10]
        0x48, 0x89, 0x07, // ASM: mov [rdi],rax
        0x48, 0x89, 0x57, 0x08, // ASM: mov [rdi+8],rdx
        0xc3, // ASM: ret
    ]);
    p.symbols.push(Symbol {
        name: "Tls::Tls".to_owned(),
        addr: 0x1000,
        kind: SymbolKind::Export,
    });
    p.symbols.push(Symbol {
        name: "Tls::Read".to_owned(),
        addr: 0x101b,
        kind: SymbolKind::Export,
    });
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let read = a.function(0x101b).expect("reader");
    let block = read
        .blocks
        .iter()
        .find(|b| b.start == 0x101b)
        .expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, read);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1017, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        let reg = out.facts.get(&Fact::Register).copied().unwrap_or_default();
        assert_eq!(reg.unreadable, 1, "seed {seed}: {}", verify_tsv(&out));
        let store = out.facts.get(&Fact::Store).copied().unwrap_or_default();
        assert_eq!(store.compared, 2, "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(store.unreadable, 0, "seed {seed}: {}", verify_tsv(&out));

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x101b, block, &mut out).expect("run");
        let key = Key::Reg(Register::RAX);
        let v = ran.env.vals.get(&key).cloned().expect("the slot's value");
        ran.env.vals.insert(
            key,
            Expr::Bin(Op::Xor, Box::new(v), Box::new(Expr::Const(1))),
        );
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Register],
            "seed {seed}: {}",
            verify_tsv(&out)
        );

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x101b, block, &mut out).expect("run");
        for effect in &mut ran.effects {
            if let Effect::Store { value, .. } = effect {
                *value = Expr::Un(UnOp::Not, Box::new(value.clone()));
            }
        }
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Store, Fact::Store],
            "seed {seed}: {}",
            verify_tsv(&out)
        );
    }
}

/// A store into a TLS slot compares at the walked block's address, and
/// a lifted value the text gets wrong is flagged on every seed.
///
/// `Tls::Tls` stores `this` at TLS offset 0x10 through the walked
/// block; the lift folds the store's address to the pseudo-global
/// `TLS_BASE + 0x10`, which the evaluator writes and reads at the
/// address the entry state walked to, so the machine's bytes there
/// compare with the stored register, and negating the lifted value
/// disagrees for every seed.
#[test]
fn a_tls_slot_store_compares_at_the_walked_block() {
    let mut p = tls_image(&[
        0x48, 0x8b, 0xd9, // ASM: mov rbx,rcx
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, // ASM: mov rax,gs:[0x58]
        0x8b, 0x0d, 0xee, 0x0f, 0x00, 0x00, // ASM: mov ecx,[rip+0xfee] -> 0x2000 (the index)
        0x48, 0x8b, 0x04, 0xc8, // ASM: mov rax,[rax+rcx*8]
        0x48, 0x89, 0x58, 0x10, // ASM: mov [rax+0x10],rbx
        0xc3, // ASM: ret
    ]);
    p.symbols.push(Symbol {
        name: "Tls::Tls".to_owned(),
        addr: 0x1000,
        kind: SymbolKind::Export,
    });
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("constructor");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        let store = out.facts.get(&Fact::Store).copied().unwrap_or_default();
        assert_eq!(store.compared, 1, "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(store.unreadable, 0, "seed {seed}: {}", verify_tsv(&out));

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        for effect in &mut ran.effects {
            if let Effect::Store { value, .. } = effect {
                *value = Expr::Un(UnOp::Not, Box::new(value.clone()));
            }
        }
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Store],
            "seed {seed}: {}",
            verify_tsv(&out)
        );
    }
}

/// An aligned entry block's stores are compared once the seed takes
/// the alignment's slack as zero.
///
/// `push rbp; mov rbp, rsp; and rsp, -16` leaves the stack pointer one
/// push below the alignment rounds to, a slack of eight the lifter
/// tracks as zero; seeding the checked run's stack pointer back by it
/// makes the machine's aligned frame the one the lifter tracks, so the
/// saved `rbp` the push wrote and the stores through `rsp` and through
/// the saved `rbp` compare, and a lifted slot value the text gets wrong
/// is flagged on every seed.
#[test]
fn an_aligned_entry_block_compares_its_stores() {
    let p = Program::raw_x64(&[
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp,rsp
        0x48, 0x83, 0xe4, 0xf0, // ASM: and rsp,-16
        0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8],eax
        0x89, 0x7d, 0xf8, // ASM: mov [rbp-8],edi
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(
            out.facts.get(&Fact::Slot).map(|t| t.compared),
            Some(3),
            "seed {seed}: {}",
            verify_tsv(&out)
        );

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        for (k, v) in &mut ran.env.vals {
            if matches!(k, Key::Slot(_)) {
                *v = Expr::Un(UnOp::Not, Box::new(v.clone()));
            }
        }
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Slot, Fact::Slot, Fact::Slot],
            "seed {seed}: {}",
            verify_tsv(&out)
        );
    }
}

/// A block whose alignment the seed cannot zero stays counted as
/// skipped, not run half-checked.
///
/// `mov rsp, rsi` leaves the lifter no frame offsets to track, so the
/// `and rsp, -16` after it rounds a pointer the lift cannot state: no
/// fact of that frame can be compared, and the block is counted under
/// the alignment reason.
#[test]
fn an_untracked_frame_alignment_stays_counted() {
    let p = Program::raw_x64(&[
        0x48, 0x89, 0xf4, // ASM: mov rsp,rsi
        0x48, 0x83, 0xe4, 0xf0, // ASM: and rsp,-16
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    for seed in 1..=4 {
        let v = verify(&p, &a, &[0x1000], seed);
        assert_eq!(v.checked, 0, "seed {seed}: {}", verify_tsv(&v));
        assert_eq!(
            v.skipped
                .get("a frame alignment whose slack the seed cannot zero"),
            Some(&1),
            "seed {seed}: {}",
            verify_tsv(&v)
        );
    }
}

/// A signed branch on a one-bit shift's overflow compares, once the
/// emulator computes the flag the SDM defines.
///
/// The lift reads `shl eax, 1` as the `add eax, eax` it is for the
/// flags, so `jl` after it is the sign of the doubled value; the
/// machine's `jl` is the sign flag against the overflow, whose SDM
/// value for a count of one is the result's sign xored with the carry
/// — the same bit. The branch used to come back undecided (the
/// emulator stopped on the jump); now every seed compares it, and a
/// lifted condition flipped is flagged on every seed.
#[test]
fn shl_by_one_then_jl_reads_the_overflow() {
    let p = Program::raw_x64(&[
        0x8b, 0x01, // ASM: mov eax,[rcx]
        0xd1, 0xe0, // ASM: shl eax,1
        0x7c, 0x05, // ASM: jl 0x100b
        0xb8, 0x00, 0x00, 0x00, 0x00, // ASM: mov eax,0
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: .taken: mov eax,1
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(out.undecided, 0, "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(
            out.facts.get(&Fact::Branch).map(|t| t.compared),
            Some(1),
            "seed {seed}: {}",
            verify_tsv(&out)
        );

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        if let Some((_, cond)) = &mut ran.branch {
            *cond = cond.invert();
        }
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Branch],
            "seed {seed}: {}",
            verify_tsv(&out)
        );
    }
}

/// A float binary operation evaluates, so the store of its result is
/// compared, not counted as unreadable, and a lifted one with the
/// wrong sign is flagged on every seed.
#[test]
fn a_float_binary_operation_is_compared() {
    let p = Program::raw_x64(&[
        0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
        0xf2, 0x0f, 0x58, 0x41, 0x08, // ASM: addsd xmm0,[rcx+8]
        0xf2, 0x0f, 0x11, 0x41, 0x10, // ASM: movsd [rcx+16],xmm0
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        let store = out.facts.get(&Fact::Store).copied().unwrap_or_default();
        assert_eq!(store.compared, 1, "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(store.unreadable, 0, "seed {seed}: {}", verify_tsv(&out));

        let mut out = Verified::default();
        let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
        for effect in &mut ran.effects {
            if let Effect::Store { value, .. } = effect {
                *value = Expr::Un(UnOp::Neg, Box::new(value.clone()));
            }
        }
        ran.compare(&mut out);
        assert_eq!(
            kinds(&out),
            [Fact::Store],
            "seed {seed}: {}",
            verify_tsv(&out)
        );
    }
}

/// A single's operation rounds at the operation, not at the store.
///
/// `1 - 2^-25` is halfway between the two singles around it and rounds
/// to `1` itself, so a compare against `1` and a store of the
/// difference agree with the emulator only when the subtraction
/// computes in a single: computed in a double it stays
/// `0.99999997`, which compares below `1` and stores as the low half
/// of a double's bits, as a chain of `subss` and `divss` in the corpus
/// once did.
#[test]
fn a_single_rounds_at_the_operation() {
    let p = Program::raw_x64(&[
        0xf3, 0x0f, 0x10, 0x0d, 0x28, 0x00, 0x00, 0x00, // ASM: movss xmm1,[rip+0x28]
        0xf3, 0x0f, 0x10, 0x05, 0x24, 0x00, 0x00, 0x00, // ASM: movss xmm0,[rip+0x24]
        0xf3, 0x0f, 0x5c, 0xc1, // ASM: subss xmm0,xmm1
        0x0f, 0x2e, 0x05, 0x1d, 0x00, 0x00, 0x00, // ASM: ucomiss xmm0,[rip+0x1d]
        0x0f, 0x93, 0xc0, // ASM: setae al
        0x24, 0x01, // ASM: and al,1
        0xf3, 0x0f, 0x11, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, // ASM: movss [rsp+0x90],xmm0
        0x88, 0x44, 0x24, 0x33, // ASM: mov [rsp+0x33],al
        0xc3, // ASM: ret
        0xcc, 0xcc, 0x00, 0x00, 0x00, 0x33, 0x00, 0x00, 0x80, 0x3f, 0x00, 0x00, 0x80, 0x3f,
    ]);
    let a = Analysis::compute(&p);
    let overlay = Overlay::default();
    let f = a.function(0x1000).expect("function");
    let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
    for seed in 1..=8 {
        let sweep = Sweep::new(&p, seed, false).expect("sweep");
        let mut ctx = sweep.ctx(&p, &a, &overlay, f);
        let mut out = Verified::default();
        sweep
            .run(&mut ctx, 0x1000, block, &mut out)
            .expect("run")
            .compare(&mut out);
        assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
        let slot = out.facts.get(&Fact::Slot).copied().unwrap_or_default();
        assert_eq!(slot.compared, 2, "seed {seed}: {}", verify_tsv(&out));
        assert_eq!(slot.unreadable, 0, "seed {seed}: {}", verify_tsv(&out));
    }
}

/// In 32-bit code a left shift's overflow is gone before a right shift
/// reads it, in the text and in the check.
///
/// `shrd eax, edx, 16` after `shl eax, 8` lifts as
/// `((x << 8) >> 16) | (edx << 16)` over `uint32_t` variables. Folded at
/// 64 bits, the top byte of `x` came back down into bits 16 to 23, and
/// most seeds reported the right lifting as a disagreement, as a byte
/// swap in a real game client did.
#[test]
fn a_32_bit_shift_chain_is_evaluated_at_32_bits() {
    let mut p = Program::raw_x64(&[
        0x8b, 0xc1, // ASM: mov eax, ecx
        0xc1, 0xe0, 0x08, // ASM: shl eax, 8
        0x0f, 0xac, 0xd0, 0x10, // ASM: shrd eax, edx, 16
        0xc3, // ASM: ret
    ]);
    p.arch = Arch::X86;
    p.is_64 = false;
    let a = Analysis::compute(&p);
    for seed in 1..=16 {
        let v = verify(&p, &a, &[0x1000], seed);
        assert_eq!(v.checked, 1, "seed {seed}: {}", verify_tsv(&v));
        assert!(v.compared > 0, "seed {seed}: {}", verify_tsv(&v));
        assert_eq!(kinds(&v), [], "seed {seed}: {}", verify_tsv(&v));
    }
}
