//! The library signature sets borer ships: runtime libraries' functions,
//! read from their static libraries by [`crate::libsig::read`] and stored
//! compact, that name a program's copies without a pack.
//!
//! A program linked with a runtime (the compiler's builtins, the C++
//! standard library, the Rust standard library) carries its functions
//! without their names. A set holds what `borer sigmake` would write as a
//! pack's `lib` lines, in a binary form a fraction of the text's size
//! ([`encode`], [`decode`]), and [`crate::analysis::libnames`] matches the
//! sets that fit a program's format and machine ([`for_program`]) with
//! the packs' lines. `scripts/dev/libsets.py` writes the sets from the
//! libraries on a build machine and `manifest.tsv` beside them records
//! where each came from and its license; only libraries whose license
//! allows it are shipped.
//!
//! A set keeps a function only where it can name something, and a
//! reference only where its name can be known ([`compact`]): the matching
//! names the same functions either way.

use std::sync::LazyLock;

use crate::analysis::libnames::CALLED_MIN;
use crate::analysis::sigs::SIG_MAX;
use crate::libsig::{LibFunction, Tail};
use crate::program::{Arch, BinaryFormat, Program};

/// The bytes a set opens with.
const MAGIC: &[u8; 4] = b"BSIG";
/// The format's version, the byte after [`MAGIC`].
const VERSION: u8 = 1;
/// Most names or functions one set holds; a count past it is damage.
const ENTRIES_MAX: usize = 1 << 20;
/// Most references one function carries in a set.
const REFS_MAX: usize = 1 << 12;
/// Fewest fixed bytes that name a shipped set's function by themselves.
///
/// [`crate::analysis::libnames`] reads it: a whole function shorter than this
/// (`vmovdqu ymm0, [rcx]; vpmovmskb eax, ymm0; vzeroupper; ret` is
/// twelve) is as likely another library's twin.
pub(crate) const SHIPPED_ALONE_MIN: usize = 24;

/// One shipped set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Set {
    /// The set's name, its file's stem and its `manifest.tsv` row.
    pub name: &'static str,
    /// The format of the programs it names.
    pub format: BinaryFormat,
    /// The machine of the programs it names.
    pub arch: Arch,
    /// The set as [`encode`] wrote it.
    pub bytes: &'static [u8],
}

/// Every set borer ships.
pub const SETS: &[Set] = &[
    Set {
        name: "compiler-rt-22-x64-coff",
        format: BinaryFormat::Pe,
        arch: Arch::X86_64,
        bytes: include_bytes!("libsets/compiler-rt-22-x64-coff.bsig"),
    },
    Set {
        name: "msvc-stl-14.44-x64",
        format: BinaryFormat::Pe,
        arch: Arch::X86_64,
        bytes: include_bytes!("libsets/msvc-stl-14.44-x64.bsig"),
    },
    Set {
        name: "rust-1.96-x64-msvc",
        format: BinaryFormat::Pe,
        arch: Arch::X86_64,
        bytes: include_bytes!("libsets/rust-1.96-x64-msvc.bsig"),
    },
];

/// Where each set came from, its license and its size, as a table.
pub const MANIFEST: &str = include_str!("libsets/manifest.tsv");

/// Every set decoded, in [`SETS`] order; a set that does not decode is
/// empty, which a test rules out.
static DECODED: LazyLock<Vec<Vec<LibFunction>>> = LazyLock::new(|| {
    SETS.iter()
        .map(|s| decode(s.bytes).unwrap_or_default())
        .collect()
});

/// Returns the functions of the sets that fit a program: its format and
/// its machine.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// Each fitting set's name and functions, in [`SETS`] order; none for a
/// program no set fits, without decoding any.
#[must_use]
pub fn for_program(program: &Program) -> Vec<(&'static str, &'static [LibFunction])> {
    SETS.iter()
        .enumerate()
        .filter(|(_, s)| s.format == program.format && s.arch == program.arch)
        .filter_map(|(i, s)| Some((s.name, DECODED.get(i)?.as_slice())))
        .collect()
}

/// Whether a reference's name can ever be known in a program.
///
/// An import slot (`__imp_`) or a plain C identifier an import, an export
/// or a symbol may carry can be. String literals (`??_C@`), section labels
/// and compiler-local names never are, so a reference to one can neither
/// name a function nor reject a match.
///
/// # Arguments
///
/// * `name` - The name a relocation gives.
fn knowable(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

/// Drops what cannot name anything from library functions read for a set.
///
/// A function whose fixed bytes name it alone ([`SHIPPED_ALONE_MIN`])
/// keeps the references whose name is another of the functions' names or
/// [`knowable`]; a shorter one is named only where every reference
/// resolves, so it keeps them all. A function is kept where it names
/// itself alone, where it has [`CALLED_MIN`] fixed bytes and references
/// that can all be known, or where another function refers to it and its
/// fixed bytes are enough to be named so. Exact duplicates go; functions
/// alike in everything but the name all stay, so the matching still finds
/// them ambiguous and names none.
///
/// # Arguments
///
/// * `functions` - The functions, from [`crate::libsig::read`].
///
/// # Returns
///
/// The kept functions, sorted.
#[must_use]
pub fn compact(functions: Vec<LibFunction>) -> Vec<LibFunction> {
    let names: std::collections::BTreeSet<String> =
        functions.iter().map(|f| f.name.clone()).collect();
    let mut kept: Vec<LibFunction> = functions
        .into_iter()
        .map(|mut f| {
            if f.fixed() >= SHIPPED_ALONE_MIN {
                f.refs
                    .retain(|(_, t)| names.contains(t.as_str()) || knowable(t));
            }
            f
        })
        .collect();
    kept.sort_unstable();
    kept.dedup();
    let called: std::collections::BTreeSet<&str> = kept
        .iter()
        .flat_map(|f| f.refs.iter().map(|(_, t)| t.as_str()))
        .collect();
    let keep: Vec<bool> = kept
        .iter()
        .map(|f| {
            let fixed = f.fixed();
            let unknowable = f
                .refs
                .iter()
                .any(|(_, t)| !names.contains(t.as_str()) && !knowable(t));
            fixed >= SHIPPED_ALONE_MIN
                || (fixed >= CALLED_MIN
                    && ((!f.refs.is_empty() && !unknowable) || called.contains(f.name.as_str())))
        })
        .collect();
    kept.into_iter()
        .zip(keep)
        .filter_map(|(f, k)| k.then_some(f))
        .collect()
}

/// Appends a ULEB128.
///
/// # Arguments
///
/// * `out` - Where it goes.
/// * `v` - The value.
fn put_uleb(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let low = u8::try_from(v & 0x7f).unwrap_or(0);
        v >>= 7;
        if v == 0 {
            out.push(low);
            return;
        }
        out.push(low | 0x80);
    }
}

/// Appends a count as a ULEB128.
///
/// # Arguments
///
/// * `out` - Where it goes.
/// * `n` - The count.
fn put_len(out: &mut Vec<u8>, n: usize) {
    put_uleb(out, crate::num::from_usize(n));
}

/// Writes library functions as a set.
///
/// The names come first, sorted, each as the length it shares with the
/// one before and the rest; then each function in order: its name's
/// index, its signature's length, a bit per signature byte (set where the
/// byte is fixed, low bit first), the fixed bytes, the tail's length and
/// hash (a zero length for none), and each reference as its offset past
/// the one before and its name's index.
///
/// # Arguments
///
/// * `functions` - The functions; signatures longer than
///   [`crate::analysis::sigs::SIG_MAX`] keep their first bytes.
///
/// # Returns
///
/// The set's bytes, the same for the same functions in any order.
#[must_use]
pub fn encode(functions: &[LibFunction]) -> Vec<u8> {
    let mut sorted: Vec<&LibFunction> = functions.iter().collect();
    sorted.sort_unstable();
    sorted.dedup();
    let names: Vec<&str> = {
        let mut n: Vec<&str> = sorted
            .iter()
            .flat_map(|f| {
                std::iter::once(f.name.as_str()).chain(f.refs.iter().map(|(_, t)| t.as_str()))
            })
            .collect();
        n.sort_unstable();
        n.dedup();
        n
    };
    let index = |name: &str| names.binary_search(&name).unwrap_or(0);
    let mut out = MAGIC.to_vec();
    out.push(VERSION);
    put_len(&mut out, names.len());
    let mut before: &[u8] = &[];
    for name in &names {
        let shared = before
            .iter()
            .zip(name.as_bytes())
            .take_while(|(a, b)| a == b)
            .count();
        put_len(&mut out, shared);
        put_len(&mut out, name.len() - shared);
        out.extend_from_slice(&name.as_bytes()[shared..]);
        before = name.as_bytes();
    }
    put_len(&mut out, sorted.len());
    for f in sorted {
        let sig = &f.sig[..f.sig.len().min(SIG_MAX)];
        put_len(&mut out, index(&f.name));
        put_len(&mut out, sig.len());
        for chunk in sig.chunks(8) {
            out.push(
                chunk
                    .iter()
                    .enumerate()
                    .filter(|(_, b)| b.is_some())
                    .fold(0u8, |m, (i, _)| m | (1 << i)),
            );
        }
        out.extend(sig.iter().flatten());
        match f.tail {
            Some(t) => {
                out.push(t.len);
                out.extend_from_slice(&t.hash.to_le_bytes());
            }
            None => out.push(0),
        }
        put_len(&mut out, f.refs.len());
        let mut at = 0u32;
        for (off, target) in &f.refs {
            put_uleb(&mut out, u64::from(off.saturating_sub(at)));
            put_len(&mut out, index(target));
            at = *off;
        }
    }
    out
}

/// Reads a count written by [`put_len`], refusing one past `max`.
///
/// # Arguments
///
/// * `data` - The set.
/// * `at` - The offset, moved past the count.
/// * `max` - The largest count that is not damage.
fn get_len(data: &[u8], at: &mut usize, max: usize) -> Option<usize> {
    let n = usize::try_from(crate::macho::uleb(data, at)?).ok()?;
    (n <= max).then_some(n)
}

/// Reads `n` bytes.
///
/// # Arguments
///
/// * `data` - The set.
/// * `at` - The offset, moved past them.
/// * `n` - How many.
fn take<'d>(data: &'d [u8], at: &mut usize, n: usize) -> Option<&'d [u8]> {
    let bytes = data.get(*at..at.checked_add(n)?)?;
    *at += n;
    Some(bytes)
}

/// Reads a set written by [`encode`] back.
///
/// # Arguments
///
/// * `data` - The set's bytes.
///
/// # Returns
///
/// The functions in the order they were written, or `None` when the bytes
/// are not a set of this version or any field runs past the end, names a
/// name the set does not have, or is larger than a set allows.
#[must_use]
pub fn decode(data: &[u8]) -> Option<Vec<LibFunction>> {
    let mut at = 0;
    if take(data, &mut at, MAGIC.len())? != MAGIC || *take(data, &mut at, 1)?.first()? != VERSION {
        return None;
    }
    let count = get_len(data, &mut at, ENTRIES_MAX)?;
    let mut names: Vec<String> = Vec::with_capacity(count);
    for _ in 0..count {
        let shared = get_len(data, &mut at, usize::MAX)?;
        let rest = get_len(data, &mut at, data.len())?;
        let mut name = names
            .last()
            .map_or("", String::as_str)
            .get(..shared)?
            .to_owned();
        name.push_str(std::str::from_utf8(take(data, &mut at, rest)?).ok()?);
        names.push(name);
    }
    let count = get_len(data, &mut at, ENTRIES_MAX)?;
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        let name = names.get(get_len(data, &mut at, ENTRIES_MAX)?)?.clone();
        let len = get_len(data, &mut at, SIG_MAX)?;
        let mask = take(data, &mut at, len.div_ceil(8))?;
        let fixed: usize = mask
            .iter()
            .map(|b| usize::try_from(b.count_ones()).unwrap_or(0))
            .sum();
        let mut bytes = take(data, &mut at, fixed)?.iter();
        let sig: Vec<Option<u8>> = (0..len)
            .map(|i| {
                let set = mask.get(i / 8).is_some_and(|m| m & (1 << (i % 8)) != 0);
                if set { bytes.next().copied() } else { None }
            })
            .collect();
        let tail = match *take(data, &mut at, 1)?.first()? {
            0 => None,
            len => Some(Tail {
                len,
                hash: crate::num::u32_le(take(data, &mut at, 4)?, 0)?,
            }),
        };
        let refs_count = get_len(data, &mut at, REFS_MAX)?;
        let mut refs = Vec::with_capacity(refs_count);
        let mut off = 0u32;
        for _ in 0..refs_count {
            off = off.checked_add(u32::try_from(crate::macho::uleb(data, &mut at)?).ok()?)?;
            refs.push((
                off,
                names.get(get_len(data, &mut at, ENTRIES_MAX)?)?.clone(),
            ));
        }
        out.push(LibFunction {
            name,
            sig,
            tail,
            refs,
        });
    }
    (at == data.len()).then_some(out)
}

#[cfg(test)]
mod tests {
    use super::{LibFunction, MANIFEST, SETS, compact, decode, encode};
    use crate::libsig::{Tail, parse_line};

    /// A function from a pack line.
    ///
    /// # Panics
    ///
    /// When the line does not read.
    fn f(line: &str) -> LibFunction {
        parse_line(line).expect("the line reads")
    }

    /// A set reads back as the functions written, whatever their order,
    /// and damaged bytes read as no set.
    ///
    /// # Panics
    ///
    /// When a function changes on the way or damage is read.
    #[test]
    fn a_set_reads_back_as_written() {
        let mut functions = vec![
            f("4883EC28E8????????4883C428C3 ?caller@@YAXXZ 5=?helper@@YAXXZ"),
            f("488B05????????69C06745230183C04231D2B907000000C3 ?helper@@YAXXZ"),
            f("E9???????? thunk 1=?helper@@YAXXZ"),
        ];
        functions[1].tail = Some(Tail {
            len: 9,
            hash: 0xdead_beef,
        });
        let bytes = encode(&functions);
        let mut back = decode(&bytes).expect("the set reads");
        functions.sort_unstable();
        back.sort_unstable();
        assert_eq!(back, functions);
        functions.reverse();
        assert_eq!(encode(&functions), bytes, "the order does not matter");
        assert!(decode(&bytes[..bytes.len() - 1]).is_none(), "a cut set");
        assert!(decode(b"BSIG\x02").is_none(), "another version");
        assert!(decode(b"").is_none());
        for cut in 0..bytes.len() {
            assert!(decode(&bytes[..cut]).is_none(), "cut at {cut}");
        }
    }

    /// What cannot name a function goes and what can stays.
    ///
    /// Gone: a lone short function nobody calls, a short one whose reference can never be
    /// known, a long one's reference to a string literal, an exact
    /// duplicate.
    ///
    /// # Panics
    ///
    /// When a function or a reference is kept or dropped wrongly.
    #[test]
    fn compacting_keeps_what_can_name() {
        let long = "488D0D????????4883EC284889C84801D04C01C04C01C84831C04883C428E9????????";
        let kept = compact(vec![
            f("4883EC28E8????????4883C428C3 caller 5=helper"),
            f("8D040983C0050FAFC1 helper"),
            f("8D040983C0050FAFC1 helper_twin"),
            f("33C0C3 tiny"),
            f(
                "488D0D????????FF25???????? locked 3=??_C@_05ABC@hello@ 9=__imp_AcquireSRWLockExclusive",
            ),
            f(&format!("{long} lone 3=??_C@_05ABC@hello@ 1f=puts")),
            f(&format!("{long} lone 3=??_C@_05ABC@hello@ 1f=puts")),
        ]);
        let names: Vec<&str> = kept.iter().map(|k| k.name.as_str()).collect();
        assert_eq!(names, ["caller", "helper", "lone"]);
        assert_eq!(kept[2].refs, vec![(0x1f, "puts".to_owned())]);
        let ambiguous = compact(vec![
            f("4883EC28E8????????4883C428C3 caller 5=helper"),
            f("4883EC28E8????????4883C428C3 caller_twin 5=helper"),
        ]);
        assert_eq!(ambiguous.len(), 2, "twins both stay");
    }

    /// Every shipped set decodes, holds functions, and has its row in the
    /// manifest with its size and function count.
    ///
    /// # Panics
    ///
    /// When a set does not decode or the manifest misdescribes it.
    #[test]
    fn every_shipped_set_decodes_and_is_in_the_manifest() {
        for set in SETS {
            let functions = decode(set.bytes).expect("a shipped set decodes");
            assert!(!functions.is_empty(), "{}", set.name);
            let row = MANIFEST
                .lines()
                .map(|l| l.split('\t').collect::<Vec<_>>())
                .find(|r| r.first() == Some(&set.name))
                .unwrap_or_else(|| panic!("{} has no manifest row", set.name));
            assert_eq!(
                row.get(1).copied(),
                Some(functions.len().to_string().as_str()),
                "{}: functions",
                set.name
            );
            assert_eq!(
                row.get(2).copied(),
                Some(set.bytes.len().to_string().as_str()),
                "{}: bytes",
                set.name
            );
        }
    }
}
