//! API hashes: the 32-bit constants shellcode and malware compare export
//! names against instead of importing them, resolved to the names they
//! hash.
//!
//! Code that hides its imports walks a module's export table, hashes each
//! name and compares the hash with a constant it carries; the constant is
//! all a reader sees. The schemes in common use are hashed here over every
//! name borer knows (the program's own imports and the Windows and C
//! library functions [`super::prototypes`] and [`super::typelib`] declare):
//! ROR13 over the name with and without its terminating NUL, ROR13 over
//! the module's upper-case UTF-16 name added to the function's (the
//! Metasploit `block_api` form, `kernel32.dll!LoadLibraryA` is
//! `0x0726774c`), djb2, 32-bit FNV-1a and CRC-32.
//!
//! The 32-bit immediates of every x86 and x64 function and the aligned
//! words of the data sections are looked up. Nothing is named silently: a
//! constant is listed with every name and scheme it matches, and it is
//! corroborated only where another constant in the same function, or a
//! word within [`NEAR`] bytes of it in data, resolves under the same
//! scheme. A word in data is kept only when corroborated; a lone constant
//! in code is listed as unconfirmed. Values below [`VALUE_MIN`], with
//! fewer than three or more than 29 bits set, or that are addresses the
//! image maps are passed over: they are sizes, masks and pointers far more
//! often than hashes.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::{Arc, LazyLock};

use super::Analysis;
use crate::fxmap::FxHashMap;
use crate::isa::x86::{Decoder, DecoderOptions, OpKind};
use crate::program::{Program, SymbolKind};

/// Smallest value looked up.
const VALUE_MIN: u32 = 0x1_0000;
/// Most hits kept.
const HITS_MAX: usize = 4096;
/// Most bytes of data sections scanned.
const DATA_MAX: usize = 16 << 20;
/// Farthest apart two words in data may lie and corroborate each other.
const NEAR: u64 = 16;
/// The modules the module-and-function scheme is tried with, beside the
/// ones the program imports from.
const MODULES: &[&str] = &[
    "kernel32.dll",
    "ntdll.dll",
    "kernelbase.dll",
    "advapi32.dll",
    "user32.dll",
    "ws2_32.dll",
    "wininet.dll",
    "winhttp.dll",
    "urlmon.dll",
    "shell32.dll",
    "msvcrt.dll",
];

/// A hashing scheme.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Scheme {
    /// Rotate right by 13 and add each byte of the name, NUL left out.
    Ror13,
    /// Rotate right by 13 and add each byte of the name and its NUL.
    Ror13Nul,
    /// The module's upper-case UTF-16 name and its NUL under ROR13, added
    /// to the function's name and its NUL under ROR13.
    Ror13Module,
    /// djb2: start at 5381, multiply by 33 and add each byte.
    Djb2,
    /// 32-bit FNV-1a.
    Fnv1a,
    /// CRC-32 (IEEE 802.3, reflected) over the name.
    Crc32,
}

impl Scheme {
    /// The scheme's name in a listing.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Self::Ror13 => "ror13",
            Self::Ror13Nul => "ror13+nul",
            Self::Ror13Module => "ror13 module+name",
            Self::Djb2 => "djb2",
            Self::Fnv1a => "fnv1a-32",
            Self::Crc32 => "crc32",
        }
    }
}

/// ROR13 over bytes, from a starting value.
///
/// # Arguments
///
/// * `h` - The starting value.
/// * `bytes` - The bytes.
fn ror13(h: u32, bytes: impl Iterator<Item = u8>) -> u32 {
    bytes.fold(h, |h, b| h.rotate_right(13).wrapping_add(u32::from(b)))
}

/// Hashes a name under a scheme.
///
/// # Arguments
///
/// * `scheme` - The scheme.
/// * `module` - The module's file name, for [`Scheme::Ror13Module`];
///   ignored by the others.
/// * `name` - The function's name.
///
/// # Returns
///
/// The hash.
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::apihash::{Scheme, hash};
/// assert_eq!(hash(Scheme::Ror13Module, "kernel32.dll", "LoadLibraryA"), 0x0726_774c);
/// assert_eq!(hash(Scheme::Ror13, "", "LoadLibraryA"), 0xec0e_4e8e);
/// ```
#[must_use]
pub fn hash(scheme: Scheme, module: &str, name: &str) -> u32 {
    let bytes = name.bytes();
    match scheme {
        Scheme::Ror13 => ror13(0, bytes),
        Scheme::Ror13Nul => ror13(0, bytes.chain([0])),
        Scheme::Ror13Module => {
            let wide = module
                .encode_utf16()
                .chain([0])
                .map(|c| {
                    if (u16::from(b'a')..=u16::from(b'z')).contains(&c) {
                        c - 0x20
                    } else {
                        c
                    }
                })
                .flat_map(u16::to_le_bytes);
            ror13(0, wide).wrapping_add(ror13(0, bytes.chain([0])))
        }
        Scheme::Djb2 => bytes.fold(5381u32, |h, b| {
            h.wrapping_mul(33).wrapping_add(u32::from(b))
        }),
        Scheme::Fnv1a => bytes.fold(0x811c_9dc5u32, |h, b| {
            (h ^ u32::from(b)).wrapping_mul(0x0100_0193)
        }),
        Scheme::Crc32 => crate::carve::crc32(name.as_bytes()),
    }
}

/// The function names borer's API tables declare, sorted.
static API_NAMES: LazyLock<Vec<&'static str>> = LazyLock::new(|| {
    let mut names: Vec<&str> = include_str!("prototypes.tsv")
        .lines()
        .chain(include_str!("typelib.tsv").lines())
        .filter_map(|l| l.split('\t').next())
        .filter(|n| !n.is_empty())
        .collect();
    names.sort_unstable();
    names.dedup();
    names
});

/// One name a constant hashes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Candidate {
    /// The scheme.
    pub scheme: Scheme,
    /// The name: `module!function` for [`Scheme::Ror13Module`], the
    /// function alone for the others.
    pub name: String,
}

/// One constant that resolves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApiHash {
    /// The instruction carrying it, or the word in data.
    pub va: u64,
    /// The function the instruction belongs to; `None` for data.
    pub function: Option<u64>,
    /// The constant.
    pub value: u32,
    /// Every name and scheme it matches, sorted; more than one is an
    /// ambiguity to settle by reading the code.
    pub candidates: Vec<Candidate>,
    /// Whether another constant beside it resolves under one of its
    /// schemes.
    pub corroborated: bool,
}

/// Every hash of every known name, by value: what [`find_api_hashes`]
/// looks constants up in.
///
/// # Arguments
///
/// * `program` - The loaded image, whose imports and their modules join
///   the tables' names.
fn table(program: &Program) -> FxHashMap<u32, Vec<(Scheme, &str, &str)>> {
    let mut names: BTreeSet<&str> = API_NAMES.iter().copied().collect();
    let mut modules: BTreeSet<&str> = MODULES.iter().copied().collect();
    let mut pairs: BTreeSet<(&str, &str)> = BTreeSet::new();
    for s in program
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
    {
        if let Some((module, name)) = s.name.split_once('!') {
            names.insert(name);
            pairs.insert((module, name));
            modules.insert(module);
        } else {
            names.insert(&s.name);
        }
    }
    let mut out: FxHashMap<u32, Vec<(Scheme, &str, &str)>> = FxHashMap::default();
    for &name in &names {
        for scheme in [
            Scheme::Ror13,
            Scheme::Ror13Nul,
            Scheme::Djb2,
            Scheme::Fnv1a,
            Scheme::Crc32,
        ] {
            out.entry(hash(scheme, "", name))
                .or_default()
                .push((scheme, "", name));
        }
        for &module in &modules {
            out.entry(hash(Scheme::Ror13Module, module, name))
                .or_default()
                .push((Scheme::Ror13Module, module, name));
        }
    }
    for (module, name) in pairs {
        out.entry(hash(Scheme::Ror13Module, module, name))
            .or_default()
            .push((Scheme::Ror13Module, module, name));
    }
    out
}

/// Whether a value is worth looking up: large enough, neither nearly
/// empty nor nearly full of set bits, and no address the image maps.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `v` - The value.
fn plausible(program: &Program, v: u32) -> bool {
    let va = u64::from(v);
    v >= VALUE_MIN
        && (3..=29).contains(&v.count_ones())
        && !program
            .sections
            .iter()
            .any(|s| va >= s.va.0 && va - s.va.0 < s.vsize.max(s.file_size))
}

/// Finds the constants that hash a known API name.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
///
/// # Returns
///
/// The hits by address, at most [`HITS_MAX`]: every resolving immediate of
/// an x86 or x64 function, and every corroborated word of the data
/// sections. None for other machines' code. Decoding every function is
/// the cost and the hits are facts of the image, so they are found once
/// per analysis ([`Analysis::derived`]) and shared.
#[must_use]
pub fn find_api_hashes(program: &Program, analysis: &Analysis) -> Arc<Vec<ApiHash>> {
    analysis
        .derived
        .get_or_build("api_hashes", (), || scan(program, analysis))
}

/// Finds the constants that hash a known API name, as
/// [`find_api_hashes`] shares them.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
///
/// # Returns
///
/// The hits by address, as [`find_api_hashes`] describes them.
fn scan(program: &Program, analysis: &Analysis) -> Vec<ApiHash> {
    let Some(bitness) = program.arch.bitness() else {
        return Vec::new();
    };
    let table = table(program);
    let candidates = |v: u32| -> Option<Vec<Candidate>> {
        let found = table.get(&v)?;
        let mut c: Vec<Candidate> = found
            .iter()
            .map(|(scheme, module, name)| Candidate {
                scheme: *scheme,
                name: if module.is_empty() {
                    (*name).to_owned()
                } else {
                    format!("{module}!{name}")
                },
            })
            .collect();
        c.sort_unstable();
        c.dedup();
        Some(c)
    };
    let mut hits: BTreeMap<u64, ApiHash> = BTreeMap::new();
    for f in &analysis.functions {
        let mut found: Vec<u64> = Vec::new();
        for b in &f.blocks {
            let len = crate::num::saturating_usize(b.end.saturating_sub(b.start));
            let Some(bytes) = program.read_va(b.start, len) else {
                continue;
            };
            for i in Decoder::with_ip(bitness, bytes, b.start, DecoderOptions::NONE) {
                let v = (0..i.op_count()).find_map(|k| {
                    let kind = i.op_kind(k);
                    if kind == OpKind::Immediate32 {
                        Some(i.immediate32())
                    } else if kind == OpKind::Immediate32to64 {
                        Some(crate::num::lo32(i.immediate32to64().cast_unsigned()))
                    } else {
                        None
                    }
                });
                let Some(v) = v.filter(|v| plausible(program, *v)) else {
                    continue;
                };
                let Some(c) = candidates(v) else {
                    continue;
                };
                hits.insert(
                    i.ip(),
                    ApiHash {
                        va: i.ip(),
                        function: Some(f.entry),
                        value: v,
                        candidates: c,
                        corroborated: false,
                    },
                );
                found.push(i.ip());
                if hits.len() >= HITS_MAX {
                    break;
                }
            }
        }
        corroborate(&mut hits, &found, |_, _| true);
        if hits.len() >= HITS_MAX {
            return hits.into_values().collect();
        }
    }
    let mut data: Vec<u64> = Vec::new();
    let mut budget = DATA_MAX;
    for s in program.sections.iter().filter(|s| !s.executable) {
        let len = crate::num::saturating_usize(s.file_size).min(budget);
        let Some(bytes) = program.read_va(s.va.0, len) else {
            continue;
        };
        budget = budget.saturating_sub(bytes.len());
        for (k, word) in bytes.chunks_exact(4).enumerate() {
            let v = u32::from_le_bytes([word[0], word[1], word[2], word[3]]);
            if !plausible(program, v) {
                continue;
            }
            let Some(c) = candidates(v) else {
                continue;
            };
            let va = s.va.0 + crate::num::from_usize(k * 4);
            hits.insert(
                va,
                ApiHash {
                    va,
                    function: None,
                    value: v,
                    candidates: c,
                    corroborated: false,
                },
            );
            data.push(va);
            if hits.len() >= HITS_MAX {
                break;
            }
        }
    }
    corroborate(&mut hits, &data, |a, b| a.abs_diff(b) <= NEAR);
    for va in data {
        if hits.get(&va).is_some_and(|h| !h.corroborated) {
            hits.remove(&va);
        }
    }
    hits.into_values().collect()
}

/// Marks the hits among `group` that share a scheme with another hit of
/// it of a different value, where `near` allows the pair.
///
/// # Arguments
///
/// * `hits` - Every hit, by address.
/// * `group` - The addresses of the hits that may corroborate each other.
/// * `near` - Whether two addresses are close enough.
fn corroborate(hits: &mut BTreeMap<u64, ApiHash>, group: &[u64], near: impl Fn(u64, u64) -> bool) {
    let schemes = |va: u64, hits: &BTreeMap<u64, ApiHash>| -> (u32, BTreeSet<Scheme>) {
        hits.get(&va).map_or((0, BTreeSet::new()), |h| {
            (h.value, h.candidates.iter().map(|c| c.scheme).collect())
        })
    };
    let confirmed: Vec<u64> = group
        .iter()
        .copied()
        .filter(|&a| {
            let (va, sa) = schemes(a, hits);
            group.iter().any(|&b| {
                let (vb, sb) = schemes(b, hits);
                b != a && vb != va && near(a, b) && !sa.is_disjoint(&sb)
            })
        })
        .collect();
    for va in confirmed {
        if let Some(h) = hits.get_mut(&va) {
            h.corroborated = true;
        }
    }
}

/// Renders the hits as a table.
///
/// # Arguments
///
/// * `hits` - What [`find_api_hashes`] found.
/// * `limit` - Most rows listed.
///
/// # Returns
///
/// A `#` header counting the hits and the corroborated ones, then one
/// `va  function  value  confidence  scheme:name` row per hit, empty when
/// there is none.
#[must_use]
pub fn api_hashes_tsv(hits: &[ApiHash], limit: usize) -> String {
    if hits.is_empty() {
        return String::new();
    }
    let corroborated = hits.iter().filter(|h| h.corroborated).count();
    let mut out = format!(
        "# api hashes: {} constants hash a known export name, {corroborated} corroborated by another under the same scheme; showing {} of {}\n",
        hits.len(),
        hits.len().min(limit),
        hits.len()
    );
    out.push_str("# va          function     value       confidence   scheme:name\n");
    for h in hits.iter().take(limit) {
        let function = h
            .function
            .map_or_else(|| "data".to_owned(), |f| format!("{f:#x}"));
        let names: Vec<String> = h
            .candidates
            .iter()
            .map(|c| format!("{}:{}", c.scheme.word(), c.name))
            .collect();
        let _ = writeln!(
            out,
            "{:<12} {function:<12} {:#010x}  {:<12} {}",
            format!("{:#x}", h.va),
            h.value,
            if h.corroborated {
                "corroborated"
            } else {
                "unconfirmed"
            },
            names.join(" | ")
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{Scheme, api_hashes_tsv, find_api_hashes, hash};
    use crate::analysis::Analysis;
    use crate::program::Program;

    /// Two constants in one function that hash under one scheme confirm
    /// each other; a constant alone is listed as unconfirmed, and a small
    /// value is not looked up.
    ///
    /// # Panics
    ///
    /// When a constant is resolved, confirmed or skipped wrongly.
    #[test]
    fn constants_in_code_resolve_and_corroborate() {
        let pair = [
            0xb9, 0x4c, 0x77, 0x26, 0x07, // ASM: mov ecx,0x0726774c
            0xba, 0x49, 0xf7, 0x02, 0x78, // ASM: mov edx,0x7802f749
            0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax,5
            0xc3, // ASM: ret
        ];
        let p = Program::raw_x64(&pair);
        let hits = find_api_hashes(&p, &Analysis::compute(&p));
        assert_eq!(hits.len(), 2, "{hits:?}");
        assert!(hits.iter().all(|h| h.corroborated), "{hits:?}");
        assert_eq!(hits[0].candidates[0].name, "kernel32.dll!LoadLibraryA");
        let text = api_hashes_tsv(&hits, 10);
        assert!(
            text.contains("ror13 module+name:kernel32.dll!GetProcAddress"),
            "{text}"
        );
        let alone = [
            0xb9, 0x4c, 0x77, 0x26, 0x07, // ASM: mov ecx,0x0726774c
            0xc3, // ASM: ret
        ];
        let p = Program::raw_x64(&alone);
        let hits = find_api_hashes(&p, &Analysis::compute(&p));
        assert_eq!(hits.len(), 1, "{hits:?}");
        assert!(!hits[0].corroborated);
        assert!(api_hashes_tsv(&hits, 10).contains("unconfirmed"));
    }

    /// Each scheme gives the value published for it, and the module form
    /// ignores the module's case.
    ///
    /// # Panics
    ///
    /// When a scheme hashes wrongly.
    #[test]
    fn every_scheme_matches_its_published_values() {
        assert_eq!(
            hash(Scheme::Ror13Module, "kernel32.dll", "LoadLibraryA"),
            0x0726_774c
        );
        assert_eq!(
            hash(Scheme::Ror13Module, "KERNEL32.DLL", "GetProcAddress"),
            0x7802_f749
        );
        assert_eq!(
            hash(Scheme::Ror13Module, "ws2_32.dll", "WSAStartup"),
            0x006b_8029
        );
        assert_eq!(hash(Scheme::Ror13, "", "LoadLibraryA"), 0xec0e_4e8e);
        assert_eq!(hash(Scheme::Ror13, "", "GetProcAddress"), 0x7c0d_fcaa);
        assert_eq!(hash(Scheme::Ror13Nul, "", "LoadLibraryA"), 0x7477_6072);
        assert_eq!(hash(Scheme::Djb2, "", "LoadLibraryA"), 0x5fbf_f0fb);
        assert_eq!(hash(Scheme::Fnv1a, "", "LoadLibraryA"), 0x53b2_070f);
        assert_eq!(hash(Scheme::Crc32, "", "LoadLibraryA"), 0x3fc1_bd8d);
        assert_eq!(hash(Scheme::Crc32, "", "VirtualAlloc"), 0x09ce_0d4a);
    }
}
