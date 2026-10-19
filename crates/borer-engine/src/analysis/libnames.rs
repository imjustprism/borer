//! Library names: the functions a program linked from a static library,
//! named by the library's own signatures.
//!
//! A pack's `[names]` `lib` lines ([`crate::libsig`], which `borer sigmake`
//! writes from a library's objects) each carry a function's first bytes
//! with the relocated ones masked, its name, and what each relocation
//! names. Matching them is FLIRT's idea with the linker's own masks:
//!
//! 1. A signature with enough fixed bytes names the one entry it matches.
//! 2. A shorter one, a thunk or a wrapper, names an entry when what the
//!    entry's instruction at a relocation's offset reaches (a call's
//!    target, an address it loads, an import slot) is already known by the
//!    name the library gives it, and nothing it reaches is known by
//!    another name. Many signatures the library shares between names (one
//!    template's instantiations) are told apart the same way.
//! 3. What a named function's relocations reach takes the names they give,
//!    where the bytes there fit that name's signature: a helper too small
//!    or too common to name by itself is named by its callers.
//!
//! The shipped sets ([`crate::libsets`]) apply to every program of their
//! format unasked, so their functions meet a stricter bar than a pack's.
//! One names an entry alone only with [`crate::libsets::SHIPPED_ALONE_MIN`]
//! fixed bytes: a whole function shorter than that (`vmovdqu ymm0, [rcx];
//! vpmovmskb eax, ymm0; vzeroupper; ret`) is as likely another library's
//! twin. A shorter one needs [`CALLED_MIN`] fixed bytes and every
//! reference resolved to the name the library gives it: a single `jmp`
//! (an incremental linker's thunk) and a wrapper loading a global the
//! program does not name before a common import (`lea rcx, [lock]; jmp
//! [AcquireSRWLockExclusive]`) name nothing.
//!
//! The steps repeat until a round names nothing. A signature matches an
//! entry only where the bytes after it fit the line's tail too
//! ([`crate::libsig::Tail`]), which tells apart functions whose first bytes
//! agree. An entry two names want in one round takes neither, since the
//! linker folds identical functions into one and either name would
//! mislead; it is listed as ambiguous with every name instead.

use std::fmt::Write as _;

use crate::isa::x86::{Decoder, DecoderOptions, OpKind, Register};

use super::sigs::{EntryIndex, apply_names};
use super::{Analysis, NameSource, single};
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::libsig::{LibFunction, parse_line, tail_hash};
use crate::program::{Program, SymbolKind};

/// Fewest fixed bytes that name a function by themselves.
const ALONE_MIN: usize = 12;
/// Fewest fixed bytes a function needs to be named by its callers: the
/// linker folds the tiny ones (`xor eax, eax; ret`) across names.
pub(crate) const CALLED_MIN: usize = 8;
/// Most rounds of matching.
const ROUNDS_MAX: usize = 16;
/// Most entries one signature is tried against; a shorter prefix than this
/// allows says too little to be worth checking.
const CANDIDATES_MAX: usize = 4096;

/// What the packs' `lib` lines named in a program.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LibraryNames {
    /// The entries named, with their names.
    pub named: Vec<(u64, String)>,
    /// Entries more than one name matched to the last byte the lines
    /// carry, so none names them: the entry and every name, sorted.
    pub ambiguous: Vec<(u64, Vec<String>)>,
    /// Entries a library name matched that the program names itself: the
    /// entry, the library's name and the program's.
    pub kept: Vec<(u64, String, String)>,
    /// How many `lib` lines the packs carry.
    pub signatures: usize,
    /// How many functions the shipped sets that fit the program carry
    /// ([`crate::libsets`]).
    pub shipped: usize,
    /// Lines that do not read.
    pub unreadable: usize,
}

/// A name as a reference compares it: the import prefix and, for 32-bit
/// C names, the underscore and the argument size dropped
/// (`__imp__HeapFree@12` and `HeapFree` agree).
///
/// # Arguments
///
/// * `name` - A symbol's name.
/// * `is_64` - Whether the program is 64-bit.
fn key(name: &str, is_64: bool) -> &str {
    let name = name.strip_prefix("__imp_").unwrap_or(name);
    if is_64 || name.starts_with('?') {
        return name;
    }
    let name = name
        .strip_prefix('_')
        .or_else(|| name.strip_prefix('@'))
        .unwrap_or(name);
    match name.rsplit_once('@') {
        Some((head, size)) if !size.is_empty() && size.bytes().all(|b| b.is_ascii_digit()) => head,
        _ => name,
    }
}

/// The name a function takes: demangled when decorated, the C
/// decorations dropped otherwise.
///
/// A demangled Rust type may quote an ABI (`unsafe extern "C" fn(*mut
/// u8)`); the quotes are dropped, since a function's name is never a
/// string in the text it heads.
///
/// # Arguments
///
/// * `name` - The library's name for it.
/// * `is_64` - Whether the program is 64-bit.
fn display(name: &str, is_64: bool) -> String {
    if name.starts_with('?') || name.starts_with("_Z") || name.starts_with("_R") {
        crate::search::demangled_name(name).replace('"', "")
    } else {
        key(name, is_64).to_owned()
    }
}

/// Where the instruction covering `at`, in the function at `entry`,
/// reaches: a branch target, a RIP-relative address, or an absolute
/// address it loads or pushes.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function's entry.
/// * `at` - An address inside one of its first instructions.
fn reaches(program: &Program, entry: u64, at: u64) -> Option<u64> {
    let bitness = program.arch.bitness()?;
    let len = usize::try_from(at.checked_sub(entry)?)
        .ok()?
        .checked_add(16)?;
    let bytes = program.read_va_upto(entry, len)?;
    let mut decoder = Decoder::with_ip(bitness, bytes, entry, DecoderOptions::NONE);
    for i in &mut decoder {
        if i.ip() > at {
            return None;
        }
        if at >= i.next_ip() {
            continue;
        }
        if i.is_ip_rel_memory_operand() {
            return Some(i.ip_rel_memory_address());
        }
        return (0..i.op_count()).find_map(|k| match i.op_kind(k) {
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
                Some(i.near_branch_target())
            }
            OpKind::Memory if i.memory_base() == Register::None => Some(i.memory_displacement64()),
            OpKind::Immediate32 => Some(u64::from(i.immediate32())),
            OpKind::Immediate64 => Some(i.immediate64()),
            _ => None,
        });
    }
    None
}

/// Whether the bytes after a signature matched at `va` fit its tail: the
/// fixed bytes the library has past its first [`crate::analysis::sigs::SIG_MAX`].
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `f` - The library function.
/// * `va` - The entry its signature matched.
fn tail_fits(program: &Program, f: &LibFunction, va: u64) -> bool {
    f.tail.is_none_or(|t| {
        let at = va.saturating_add(crate::num::from_usize(f.sig.len()));
        program
            .read_va(at, usize::from(t.len))
            .is_some_and(|bytes| tail_hash(bytes) == t.hash)
    })
}

/// Whether the bytes at `va` fit a signature.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `sig` - The signature.
/// * `va` - Where to compare.
fn fits(program: &Program, sig: &[Option<u8>], va: u64) -> bool {
    program.read_va_upto(va, sig.len()).is_some_and(|bytes| {
        bytes.len() == sig.len()
            && sig
                .iter()
                .zip(bytes)
                .all(|(p, b)| p.is_none_or(|p| p == *b))
    })
}

/// Finds the functions the packs' `lib` lines and the shipped sets name.
///
/// What the program names by itself, imports by their slots and symbols
/// by their addresses, is known before any round; the entries a round
/// names are kept by the signature that named them, and what their
/// references reach takes the names those references give.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions, and the packs.
#[must_use]
pub fn find_library_names(program: &Program, analysis: &Analysis) -> LibraryNames {
    find_with(program, analysis, &crate::libsets::for_program(program))
}

/// Finds the functions the packs' `lib` lines and the given shipped sets
/// name ([`find_library_names`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions, and the packs.
/// * `shipped` - Each shipped set that fits the program: its name and
///   functions.
fn find_with(
    program: &Program,
    analysis: &Analysis,
    shipped: &[(&str, &[LibFunction])],
) -> LibraryNames {
    let lines = analysis.packs.list("names", "lib");
    let mut out = LibraryNames {
        signatures: lines.len(),
        shipped: shipped.iter().map(|(_, set)| set.len()).sum(),
        ..LibraryNames::default()
    };
    if lines.is_empty() && out.shipped == 0 {
        return out;
    }
    let is_64 = program.is_64;
    let mut parsed: Vec<LibFunction> = Vec::with_capacity(lines.len());
    for line in lines {
        match parse_line(line) {
            Some(f) if f.fixed() > 0 => parsed.push(f),
            Some(_) => {}
            None => out.unreadable += 1,
        }
    }
    let strict: Vec<bool> = parsed
        .iter()
        .map(|_| false)
        .chain(shipped.iter().flat_map(|(_, set)| set.iter().map(|_| true)))
        .collect();
    let fns: Vec<&LibFunction> = parsed
        .iter()
        .chain(shipped.iter().flat_map(|(_, set)| set.iter()))
        .collect();
    let mut known: FxHashMap<u64, String> = FxHashMap::default();
    for s in &program.symbols {
        let name = match s.kind {
            SymbolKind::Import => super::bare_name(&s.name),
            _ => &s.name,
        };
        known
            .entry(s.addr)
            .or_insert_with(|| key(name, is_64).to_owned());
    }
    let mut by_key: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
    for (k, f) in fns.iter().enumerate() {
        by_key.entry(key(&f.name, is_64)).or_default().push(k);
    }
    let index = EntryIndex::build(program, analysis);
    let candidates: Vec<Vec<u64>> = fns
        .iter()
        .map(|f| {
            let found = index.matches(&f.sig);
            if found.len() > CANDIDATES_MAX {
                Vec::new()
            } else {
                found
                    .into_iter()
                    .filter(|&c| tail_fits(program, f, c))
                    .collect()
            }
        })
        .collect();
    let mut ambiguous: std::collections::BTreeMap<u64, std::collections::BTreeSet<String>> =
        std::collections::BTreeMap::new();
    let mut named: FxHashMap<u64, usize> = FxHashMap::default();
    let mut named_keys: FxHashSet<&str> = known.values().map(String::as_str).collect();
    let mut placed = vec![false; fns.len()];
    let name_at = |named: &FxHashMap<u64, usize>, va: u64| -> Option<&str> {
        named
            .get(&va)
            .map(|&k| key(&fns[k].name, is_64))
            .or_else(|| known.get(&va).map(String::as_str))
    };
    for _ in 0..ROUNDS_MAX {
        let mut want: FxHashMap<u64, FxHashSet<&str>> = FxHashMap::default();
        let mut picks: Vec<(usize, u64)> = Vec::new();
        for (k, f) in fns.iter().enumerate() {
            if placed[k] {
                continue;
            }
            let strict = strict[k];
            let alone = f.fixed()
                >= if strict {
                    crate::libsets::SHIPPED_ALONE_MIN
                } else {
                    ALONE_MIN
                };
            let known = |(_, t): &(u32, String)| named_keys.contains(key(t, is_64));
            let reachable = if strict {
                f.fixed() >= CALLED_MIN && !f.refs.is_empty() && f.refs.iter().all(known)
            } else {
                f.refs.iter().any(known)
            };
            if !alone && !reachable {
                continue;
            }
            let own = key(&f.name, is_64);
            let good = candidates[k].iter().copied().filter(|&c| {
                if name_at(&named, c).is_some_and(|n| n != own) {
                    return false;
                }
                let mut agree = 0;
                for (off, target) in &f.refs {
                    match reaches(program, c, c + u64::from(*off)).and_then(|t| name_at(&named, t))
                    {
                        Some(n) if n == key(target, is_64) => agree += 1,
                        Some(_) => return false,
                        None if strict && !alone => return false,
                        None => {}
                    }
                }
                alone || agree > 0
            });
            if let Some(c) = single(good) {
                want.entry(c).or_default().insert(own);
                picks.push((k, c));
            }
        }
        for (c, names) in want.iter().filter(|(_, names)| names.len() > 1) {
            ambiguous
                .entry(*c)
                .or_default()
                .extend(names.iter().map(|n| display(n, is_64)));
        }
        let mut progress = false;
        let mut fresh: Vec<(u64, usize)> = Vec::new();
        for (k, c) in picks {
            let Some(names) = want.get(&c) else {
                continue;
            };
            if names.len() != 1 {
                continue;
            }
            placed[k] = true;
            if let std::collections::hash_map::Entry::Vacant(v) = named.entry(c) {
                v.insert(k);
                named_keys.insert(key(&fns[k].name, is_64));
                fresh.push((c, k));
                progress = true;
            }
        }
        while let Some((entry, k)) = fresh.pop() {
            for (off, target) in &fns[k].refs {
                let Some(t) = reaches(program, entry, entry + u64::from(*off)) else {
                    continue;
                };
                if named.contains_key(&t)
                    || known.contains_key(&t)
                    || analysis.function(t).is_none()
                {
                    continue;
                }
                let tk = key(target, is_64);
                let Some(g) = by_key.get(tk).and_then(|gs| {
                    gs.iter()
                        .copied()
                        .find(|&g| fns[g].fixed() >= CALLED_MIN && fits(program, &fns[g].sig, t))
                }) else {
                    continue;
                };
                named.insert(t, g);
                named_keys.insert(tk);
                placed[g] = true;
                fresh.push((t, g));
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
    out.ambiguous = ambiguous
        .into_iter()
        .filter(|(entry, _)| !named.contains_key(entry))
        .map(|(entry, names)| (entry, names.into_iter().collect()))
        .collect();
    let mut named: Vec<(u64, String)> = named
        .into_iter()
        .map(|(entry, k)| (entry, display(&fns[k].name, is_64)))
        .collect();
    named.sort_unstable();
    out.named = named;
    out
}

/// Names the functions a program's `lib` lines found where borer left them
/// unnamed or named them by vtable slot; a match on a function the program
/// names itself moves to `kept`.
///
/// # Arguments
///
/// * `analysis` - The analysis, named in place.
/// * `found` - What [`find_library_names`] found.
pub fn apply_library_names(analysis: &mut Analysis, found: &mut LibraryNames) {
    found.named = apply_names(
        analysis,
        std::mem::take(&mut found.named),
        NameSource::Library,
        &mut found.kept,
    );
}

/// What the `lib` lines and the shipped sets found, as one `#` line;
/// empty when no pack has such lines and no shipped set fits.
///
/// # Arguments
///
/// * `found` - What [`find_library_names`] and [`apply_library_names`]
///   found.
#[must_use]
pub fn library_names_tsv(found: &LibraryNames) -> String {
    /// Ambiguous entries spelled out before the rest are counted.
    const AMBIGUOUS_SHOWN: usize = 8;
    if found.signatures == 0 && found.shipped == 0 {
        return String::new();
    }
    let same = found.kept.iter().filter(|(_, lib, own)| lib == own).count();
    let mut out = format!(
        "# library names: {} of {} signatures ({} from packs, {} shipped) named a function, {} matched one the program names itself ({same} by the same name), {} do not read\n",
        found.named.len(),
        found.signatures + found.shipped,
        found.signatures,
        found.shipped,
        found.kept.len(),
        found.unreadable
    );
    if !found.ambiguous.is_empty() {
        let shown: Vec<String> = found
            .ambiguous
            .iter()
            .take(AMBIGUOUS_SHOWN)
            .map(|(entry, names)| format!("{entry:#x} {}", names.join("|")))
            .collect();
        let more = found.ambiguous.len().saturating_sub(AMBIGUOUS_SHOWN);
        let _ = writeln!(
            out,
            "# library names ambiguous, so named neither: {}{}",
            shown.join(", "),
            if more > 0 {
                format!(", +{more} more")
            } else {
                String::new()
            }
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::key;
    use crate::analysis::{Analysis, NameSource};
    use crate::pack::{Pack, Packs};
    use crate::program::Program;

    /// Appends a `rel32` from the four bytes about to be written to `target`.
    fn rel(code: &mut Vec<u8>, target: usize) {
        let from = 0x1000 + code.len() + 4;
        let d = i32::try_from(0x1000 + target).unwrap_or(0) - i32::try_from(from).unwrap_or(0);
        code.extend(d.to_le_bytes());
    }

    /// Pads `code` with `int3` up to offset `to`.
    fn pad(code: &mut Vec<u8>, to: usize) {
        code.resize(to, 0xcc);
    }

    /// Every step names what it should.
    ///
    /// A distinctive helper by its bytes, a short caller by the helper its
    /// call reaches, a one-byte thunk by where it jumps (a second thunk
    /// jumping elsewhere is left alone), and a small callee two library
    /// names share by its caller's reference.
    ///
    /// # Panics
    ///
    /// When a function is named wrongly or not at all.
    #[test]
    fn library_signatures_name_by_bytes_and_references() {
        let mut code = vec![0x48, 0x83, 0xec, 0x28, 0xe8]; // ASM: sub rsp, 0x28; call helper
        rel(&mut code, 0x10);
        code.extend([0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 0x28; ret
        pad(&mut code, 0x10);
        code.extend([0x48, 0x8b, 0x05, 0x00, 0x01, 0x00, 0x00]); // ASM: mov rax, [rip+0x100]
        code.extend([0x69, 0xc0, 0x67, 0x45, 0x23, 0x01]); // ASM: imul eax, eax, 0x1234567
        code.extend([0x83, 0xc0, 0x42, 0x31, 0xd2]); // ASM: add eax, 0x42; xor edx, edx
        code.extend([0xb9, 0x07, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov ecx, 7; ret
        pad(&mut code, 0x30);
        code.push(0xe9); // ASM: jmp helper
        rel(&mut code, 0x10);
        pad(&mut code, 0x40);
        code.push(0xe9); // ASM: jmp caller
        rel(&mut code, 0x00);
        pad(&mut code, 0x50);
        code.extend([0x53, 0x48, 0x83, 0xec, 0x20, 0x8b, 0xd9, 0xe8]); // ASM: push rbx; sub rsp, 0x20; mov ebx, ecx; call deep
        rel(&mut code, 0x70);
        code.extend([0x03, 0xc3, 0x48, 0x83, 0xc4, 0x20, 0x5b, 0xc3]); // ASM: add eax, ebx; add rsp, 0x20; pop rbx; ret
        pad(&mut code, 0x70);
        code.extend([0x8d, 0x04, 0x09, 0x83, 0xc0, 0x05, 0x0f, 0xaf, 0xc1, 0xc3]); // ASM: lea eax, [rcx+rcx]; add eax, 5; imul eax, ecx; ret
        let program = Program::raw_x64(&code);
        let text = "pack crt 1
[names]
            lib 488B05????????69C06745230183C04231D2B907000000C3 ?helper@@YAXXZ
            lib 4883EC28E8????????4883C428C3 ?caller@@YAXXZ 5=?helper@@YAXXZ
            lib E9???????? thunk_to_helper 1=?helper@@YAXXZ
            lib 534883EC208BD9E8????????03C34883C4205BC3 caller2 8=deep_fn
            lib 8D040983C0050FAFC1C3 deep_fn
            lib 8D040983C0050FAFC1C3 deep_twin
";
        let (pack, warnings) = Pack::parse(text, "crt.borer").expect("the pack reads");
        assert!(warnings.is_empty(), "{warnings:?}");
        let a = Analysis::compute_with(&program, Arc::new(Packs { packs: vec![pack] }));
        let name = |va: u64| {
            a.function(va)
                .filter(|f| f.name_source == NameSource::Library)
                .and_then(|f| f.name.clone())
        };
        assert_eq!(name(0x1010).as_deref(), Some("helper"));
        assert_eq!(name(0x1000).as_deref(), Some("caller"));
        assert_eq!(name(0x1030).as_deref(), Some("thunk_to_helper"));
        assert_eq!(name(0x1040), None, "the other thunk jumps elsewhere");
        assert_eq!(name(0x1050).as_deref(), Some("caller2"));
        assert_eq!(name(0x1070).as_deref(), Some("deep_fn"));
        assert_eq!(a.library_names.signatures, 6);
    }

    /// A shipped set's function meets the stricter bar.
    ///
    /// A distinctive one names alone and a wrapper whose every reference resolves names by
    /// them, while a one-byte thunk, a wrapper with a reference the program
    /// does not name and a short whole function name nothing. The same
    /// lines in a pack name all three.
    ///
    /// # Panics
    ///
    /// When a function is named wrongly.
    #[test]
    fn shipped_signatures_meet_a_stricter_bar() {
        let mut code = vec![0x48, 0x8b, 0x05, 0x00, 0x01, 0x00, 0x00]; // ASM: mov rax, [rip+0x100]
        code.extend([0x69, 0xc0, 0x67, 0x45, 0x23, 0x01]); // ASM: imul eax, eax, 0x1234567
        code.extend([0x83, 0xc0, 0x42, 0x31, 0xd2]); // ASM: add eax, 0x42; xor edx, edx
        code.extend([0xb9, 0x07, 0x00, 0x00, 0x00]); // ASM: mov ecx, 7
        code.extend([0x45, 0x31, 0xc0, 0x45, 0x31, 0xc9, 0xc3]); // ASM: xor r8d, r8d; xor r9d, r9d; ret
        pad(&mut code, 0x20);
        code.extend([0x48, 0x83, 0xec, 0x28, 0xe8]); // ASM: sub rsp, 0x28; call helper
        rel(&mut code, 0x00);
        code.extend([0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 0x28; ret
        pad(&mut code, 0x30);
        code.push(0xe9); // ASM: jmp helper
        rel(&mut code, 0x00);
        pad(&mut code, 0x40);
        code.extend([0x48, 0x83, 0xec, 0x28, 0x48, 0x8d, 0x0d]); // ASM: sub rsp, 0x28; lea rcx, [rip+0x200]
        code.extend([0x00, 0x02, 0x00, 0x00, 0xe8]); // ASM: call helper
        rel(&mut code, 0x00);
        code.extend([0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 0x28; ret
        pad(&mut code, 0x60);
        code.extend([0x8d, 0x04, 0x09, 0x83, 0xc0, 0x05, 0x0f, 0xaf, 0xc1]); // ASM: lea eax, [rcx+rcx]; add eax, 5; imul eax, ecx
        code.extend([0x35, 0x5a, 0x5a, 0x5a, 0x5a, 0xc3]); // ASM: xor eax, 0x5a5a5a5a; ret
        let program = Program::raw_x64(&code);
        let lines = [
            "488B05????????69C06745230183C04231D2B9070000004531C04531C9C3 helper",
            "4883EC28E8????????4883C428C3 caller 5=helper",
            "E9???????? thunk 1=helper",
            "4883EC28488D0D????????E8????????4883C428C3 wrapper 7=lock_var c=helper",
            "8D040983C0050FAFC1355A5A5A5AC3 short_whole",
        ];
        let set: Vec<super::LibFunction> = lines
            .iter()
            .map(|l| super::parse_line(l).expect("the line reads"))
            .collect();
        let a = Analysis::compute(&program);
        let found = super::find_with(&program, &a, &[("test", set.as_slice())]);
        let names: Vec<(u64, &str)> = found
            .named
            .iter()
            .map(|(va, n)| (*va, n.as_str()))
            .collect();
        assert_eq!(names, [(0x1000, "helper"), (0x1020, "caller")]);
        let text = format!(
            "pack crt 1\n[names]\n{}\n",
            lines.map(|l| format!("lib {l}")).join("\n")
        );
        let (pack, warnings) = Pack::parse(&text, "crt.borer").expect("the pack reads");
        assert!(warnings.is_empty(), "{warnings:?}");
        let a = Analysis::compute_with(&program, Arc::new(Packs { packs: vec![pack] }));
        let named: Vec<u64> = a.library_names.named.iter().map(|(va, _)| *va).collect();
        assert_eq!(
            named,
            [0x1000, 0x1020, 0x1030, 0x1040, 0x1060],
            "a pack names them all"
        );
    }

    /// A demangled Rust name keeps no quote of the ABI its types name.
    ///
    /// # Panics
    ///
    /// When the quotes stay or the name is lost.
    #[test]
    fn a_rust_name_drops_the_quotes_of_an_abi() {
        let name = super::display(
            "_RNvMs3_NtCshajds5OUw33_5alloc7raw_vecINtB5_6RawVecTOhFUKCBN_EuENtNtCsfCRYEVunkyr_3std5alloc6SystemE8grow_oneB13_",
            true,
        );
        assert!(!name.contains('"'), "{name}");
        assert!(
            name.contains("extern C fn") && name.ends_with("::grow_one"),
            "{name}"
        );
    }

    /// A 32-bit C name compares without its decorations; a 64-bit one and
    /// a C++ name as they are.
    ///
    /// # Panics
    ///
    /// When a key is spelled wrongly.
    #[test]
    fn references_compare_without_c_decorations() {
        assert_eq!(key("__imp__HeapFree@12", false), "HeapFree");
        assert_eq!(key("_free", false), "free");
        assert_eq!(key("@fastcall_fn@8", false), "fastcall_fn");
        assert_eq!(key("__imp_HeapFree", true), "HeapFree");
        assert_eq!(key("_free_base", true), "_free_base");
        assert_eq!(key("?f@@YAXXZ", false), "?f@@YAXXZ");
    }
}
