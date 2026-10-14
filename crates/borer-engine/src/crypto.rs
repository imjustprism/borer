//! Known-constant scan: cryptographic tables, hash initial states and other
//! magic byte sequences that identify an algorithm at a glance.
//!
//! One linear pass over every mapped section and every byte no section maps;
//! candidates are keyed on their first byte, so the pass costs `O(bytes)`
//! regardless of the table size.

use std::ops::ControlFlow;

use crate::program::Program;

/// Hits [`find_crypto_constants`] keeps; a full listing pages through
/// [`scan`] instead.
pub const HITS_MAX: usize = 200;

/// `(algorithm, byte signature as it appears in memory, little-endian)`.
const SIGNATURES: &[(&str, &str)] = &[
    (
        "AES forward S-box",
        "63 7c 77 7b f2 6b 6f c5 30 01 67 2b fe d7 ab 76",
    ),
    (
        "AES inverse S-box",
        "52 09 6a d5 30 36 a5 38 bf 40 a3 9e 81 f3 d7 fb",
    ),
    (
        "AES Te0 T-table",
        "c6 63 63 a5 f8 7c 7c 84 ee 77 77 99 f6 7b 7b 8d",
    ),
    (
        "AES Td0 T-table",
        "51 f4 a7 50 7e 41 65 53 1a 17 a4 c3 3a 27 5e 96",
    ),
    (
        "AES round constants (rcon)",
        "01 02 04 08 10 20 40 80 1b 36",
    ),
    (
        "SHA-256 K constants",
        "98 2f 8a 42 91 44 37 71 cf fb c0 b5 a5 db b5 e9",
    ),
    (
        "SHA-256 initial hash",
        "67 e6 09 6a 85 ae 67 bb 72 f3 6e 3c 3a f5 4f a5",
    ),
    (
        "SHA-512 K constants",
        "22 ae 28 d7 98 2f 8a 42 cd 65 ef 23 91 44 37 71",
    ),
    (
        "SHA-512 / BLAKE2b initial hash",
        "08 c9 bc f3 67 e6 09 6a 3b a7 ca 84 85 ae 67 bb",
    ),
    (
        "MD5 / MD4 / RIPEMD initial state",
        "01 23 45 67 89 ab cd ef fe dc ba 98 76 54 32 10",
    ),
    (
        "SHA-1 initial state",
        "01 23 45 67 89 ab cd ef fe dc ba 98 76 54 32 10 f0 e1 d2 c3",
    ),
    (
        "MD5 T constants",
        "78 a4 6a d7 56 b7 c7 e8 db 70 20 24 ee ce bd c1",
    ),
    (
        "CRC-32 (IEEE 802.3) table",
        "00 00 00 00 96 30 07 77 2c 61 0e ee ba 51 09 99",
    ),
    (
        "CRC-32C (Castagnoli) table",
        "00 00 00 00 03 83 6b f2 f7 70 3b e1 f4 f3 50 13",
    ),
    (
        "ChaCha20 / Salsa20 sigma (\"expand 32-byte k\")",
        "65 78 70 61 6e 64 20 33 32 2d 62 79 74 65 20 6b",
    ),
    (
        "Salsa20 tau (\"expand 16-byte k\")",
        "65 78 70 61 6e 64 20 31 36 2d 62 79 74 65 20 6b",
    ),
    (
        "Blowfish P-array (pi digits)",
        "88 6a 3f 24 d3 08 a3 85 2e 8a 19 13 44 73 70 03",
    ),
    (
        "RC5 / RC6 magic constants (P32, Q32)",
        "63 51 e1 b7 b9 79 37 9e",
    ),
    ("xxHash64 PRIME64_1", "87 ca eb 85 b1 79 37 9e"),
    // A protector generates its strings rather than storing them, and the
    // generator is almost always one of these mixers. On a binary whose
    // endpoint is XORed against a splitmix64 keystream, these constants are
    // the only marks that say so: the cipher tables above protect nothing.
    (
        "splitmix64 multiplier 1 (string obfuscation)",
        "b9 e5 e4 1c 6d 47 58 bf",
    ),
    (
        "splitmix64 multiplier 2 (string obfuscation)",
        "eb 11 31 13 bb 49 d0 94",
    ),
    (
        "splitmix64 / xoshiro golden gamma",
        "15 7c 4a 7f b9 79 37 9e",
    ),
    ("xoshiro256 jump constant", "5b 01 9b 8d cd 27 0f 18"),
    ("PCG64 multiplier", "4d ec 89 5c 2f f7 f9 47"),
    ("MurmurHash3 x64 finalizer 1", "d1 d5 b5 f9 5b d0 6f ff"),
    ("MurmurHash3 x64 finalizer 2", "45 21 87 c2 17 c6 a5 c4"),
    ("FNV-1 64-bit offset basis", "25 23 22 84 e4 9c f2 cb"),
    ("FNV-1 64-bit prime", "b3 01 00 00 00 01 00 00"),
    (
        "SipHash initial state (\"somepseu\")",
        "75 65 73 70 65 6d 6f 73",
    ),
    (
        "SipHash initial state (\"dorandom\")",
        "6d 6f 64 6e 61 72 6f 64",
    ),
    (
        "Base64 alphabet",
        "41 42 43 44 45 46 47 48 49 4a 4b 4c 4d 4e 4f 50 51 52 53 54 55 56 57 58 59 5a 61 62 63 64 65 66 67 68 69 6a 6b 6c 6d 6e 6f 70 71 72 73 74 75 76 77 78 79 7a 30 31 32 33 34 35 36 37 38 39 2b 2f",
    ),
];

/// The width of one word of a signature's table, so the same table stored
/// the other way round is scanned too; byte tables and text constants
/// have no word order and return 0.
#[must_use]
pub fn word_of(name: &str) -> usize {
    /// Byte tables and text constants, whose bytes carry no word order.
    const BYTES: [&str; 7] = [
        "S-box",
        "rcon",
        "sigma",
        "tau",
        "somepseu",
        "dorandom",
        "Base64 alphabet",
    ];
    /// Tables of 64-bit words.
    const W64: [&str; 8] = [
        "SHA-512",
        "BLAKE2b",
        "xxHash64",
        "splitmix64",
        "xoshiro256",
        "PCG64",
        "MurmurHash3 x64",
        "FNV-1 64",
    ];
    if BYTES.iter().any(|k| name.contains(k)) {
        0
    } else if W64.iter().any(|k| name.contains(k)) {
        8
    } else {
        4
    }
}

/// How a table was stored when [`scan`] met it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Storage {
    /// The signature's own bytes, as the table writes them.
    #[default]
    Native,
    /// Each word of the table stored the other way round.
    Swapped,
    /// Every byte xored with one constant, which names it.
    Xored(u8),
    /// One constant added to every byte, which names it.
    Added(u8),
}

impl std::fmt::Display for Storage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Storage::Native => Ok(()),
            Storage::Swapped => write!(f, " (big-endian)"),
            Storage::Xored(k) => write!(f, " (xor {k:#04x})"),
            Storage::Added(k) => write!(f, " (add {k:#04x})"),
        }
    }
}

/// One recognized constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CryptoHit {
    /// Virtual address of the constant's first byte; `None` in bytes no
    /// section maps (an overlay, the headers).
    pub va: Option<u64>,
    /// File offset of the constant's first byte.
    pub file_off: u64,
    /// Algorithm name from [`SIGNATURES`].
    pub name: &'static str,
    /// How the table was stored, [`Storage::Native`] for the plain form.
    pub storage: Storage,
    /// Name of the section holding the constant, [`UNMAPPED`] for bytes no
    /// section maps.
    pub section: String,
}

/// The names of the slicing-by-N tables that may follow a CRC-32 table.
const CRC32_SLICES: [&str; 7] = [
    "CRC-32 slicing table 1",
    "CRC-32 slicing table 2",
    "CRC-32 slicing table 3",
    "CRC-32 slicing table 4",
    "CRC-32 slicing table 5",
    "CRC-32 slicing table 6",
    "CRC-32 slicing table 7",
];

/// Finds the slicing-by-N tables laid out after a CRC-32 table.
///
/// A slicing implementation keeps up to eight tables of 256 words back to
/// back, each derived from the one before: `t[k][i] = (t[k-1][i] >> 8) ^
/// t[0][t[k-1][i] & 0xff]`. Each following kilobyte is accepted while its
/// first eight entries satisfy that, so a table of another kind laid out
/// next is not taken for one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - Address of a CRC-32 table's first word.
///
/// # Returns
///
/// `(address, name)` per slicing table found, in order.
#[must_use]
pub fn crc32_slices(program: &Program, table: u64) -> Vec<(u64, &'static str)> {
    /// Entries of each table checked against the derivation.
    const CHECKED: usize = 8;
    let word = |at: u64| -> Option<u32> {
        let bytes = program.read_va(at, 4)?;
        Some(u32::from_le_bytes(bytes.try_into().ok()?))
    };
    let entry = |t: u64, i: u32| word(t.checked_add(u64::from(i) * 4)?);
    let mut out = Vec::new();
    let mut previous = table;
    for name in CRC32_SLICES {
        let Some(next) = previous.checked_add(1024) else {
            break;
        };
        let derived = (0..CHECKED).all(|i| {
            let i = u32::try_from(i).unwrap_or(0);
            let (Some(before), Some(here)) = (entry(previous, i), entry(next, i)) else {
                return false;
            };
            entry(table, before & 0xff).is_some_and(|low| (before >> 8) ^ low == here)
        });
        if !derived {
            break;
        }
        out.push((next, name));
        previous = next;
    }
    out
}

/// Makes a signature's name an identifier the decompiler can use.
///
/// Parenthesised asides go, the rest is lowercased and every run of other
/// characters becomes one underscore: `CRC-32 (IEEE 802.3) table` is
/// `crc_32_table`, `SHA-256 K constants` is `sha_256_k_constants`.
///
/// # Arguments
///
/// * `name` - The signature's name from [`SIGNATURES`].
#[must_use]
pub fn identifier(name: &str) -> String {
    let mut out = String::new();
    let mut depth = 0usize;
    for c in name.chars() {
        match c {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            _ if depth > 0 => {}
            _ if c.is_ascii_alphanumeric() => out.extend(c.to_lowercase()),
            _ if !out.ends_with('_') => out.push('_'),
            _ => {}
        }
    }
    out.trim_matches('_').to_owned()
}

/// Parses a signature's hex text into bytes.
///
/// # Arguments
///
/// * `sig` - Whitespace-separated two-digit hex tokens; malformed tokens are skipped.
fn parse(sig: &str) -> Vec<u8> {
    sig.split_whitespace()
        .filter_map(|t| u8::from_str_radix(t, 16).ok())
        .collect()
}

/// What the section column says for a hit in bytes no section maps.
pub const UNMAPPED: &str = "(unmapped)";

/// One hit as [`scan`] meets it, before a caller keeps it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Seen<'p> {
    /// Virtual address of the constant's first byte; `None` in bytes no
    /// section maps.
    pub va: Option<u64>,
    /// File offset of the constant's first byte.
    pub file_off: u64,
    /// Algorithm name from [`SIGNATURES`].
    pub name: &'static str,
    /// How the table was stored, [`Storage::Native`] for the plain form.
    pub storage: Storage,
    /// Name of the section holding the constant, [`UNMAPPED`] for bytes no
    /// section maps.
    pub section: &'p str,
}

impl Seen<'_> {
    /// Returns the hit as a [`CryptoHit`] a caller keeps.
    #[must_use]
    pub fn kept(&self) -> CryptoHit {
        CryptoHit {
            va: self.va,
            file_off: self.file_off,
            name: self.name,
            storage: self.storage,
            section: self.section.to_owned(),
        }
    }
}

/// Scans every mapped section, then the bytes no section maps, for the
/// known constants, handing each hit to `visit` until it says stop.
///
/// Signatures are bucketed by their first byte, so each position compares
/// against the few candidates that can start there: byte-keyed forms
/// under the byte a match starts with, delta forms under the delta. Each
/// table is also
/// matched word-swapped, and through the adjacent-byte deltas a constant
/// xor or add key leaves unchanged, so the other word order and lightly
/// obfuscated forms are named with what was done to them; the plain form
/// reports those once, so a delta hit with key zero is skipped. An
/// overlay, the headers and a file with no sections hold bytes worth
/// scanning, as `search` scans them: a table appended after the last
/// section was found by `search` and missed here.
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
/// * `visit` - Receives every hit in a deterministic order: section, then
///   offset, then table order, then the unmapped runs in file order; it
///   returns [`ControlFlow::Break`] to end the scan.
pub fn scan(program: &Program, mut visit: impl FnMut(&Seen<'_>) -> ControlFlow<()>) {
    /// Which form of a signature [`scan`] matches.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Var {
        /// The signature's own bytes.
        Native,
        /// Each word stored the other way round.
        Swapped,
        /// Adjacent xor deltas, which a constant xor key leaves unchanged.
        Xor,
        /// Adjacent subtract deltas, which a constant add key leaves unchanged.
        Add,
    }

    /// One form of a signature [`scan`] matches at a position.
    struct Form {
        /// The signature's index in [`SIGNATURES`].
        sig: usize,
        /// The bytes this form matches: the constant's own bytes for
        /// [`Var::Native`] and [`Var::Swapped`], the run of adjacent-byte
        /// deltas for [`Var::Xor`] and [`Var::Add`].
        bytes: Vec<u8>,
        /// Which form this is.
        var: Var,
    }
    let sigs: Vec<(&'static str, Vec<u8>)> = SIGNATURES
        .iter()
        .map(|(name, sig)| (*name, parse(sig)))
        .collect();
    let mut forms: Vec<Form> = Vec::new();
    for (sig, (name, bytes)) in sigs.iter().enumerate() {
        forms.push(Form {
            sig,
            bytes: bytes.clone(),
            var: Var::Native,
        });
        let word = word_of(name);
        if word > 0 {
            forms.push(Form {
                sig,
                bytes: bytes
                    .chunks(word)
                    .flat_map(|c| c.iter().rev().copied())
                    .collect(),
                var: Var::Swapped,
            });
        }
        for var in [Var::Xor, Var::Add] {
            forms.push(Form {
                sig,
                bytes: bytes[1..]
                    .iter()
                    .scan(bytes[0], |a, b| {
                        let d = if var == Var::Xor {
                            *a ^ b
                        } else {
                            b.wrapping_sub(*a)
                        };
                        *a = *b;
                        Some(d)
                    })
                    .collect(),
                var,
            });
        }
    }
    let mut by_byte: Vec<Vec<usize>> = vec![Vec::new(); 256];
    let mut by_xor: Vec<Vec<usize>> = vec![Vec::new(); 256];
    let mut by_sub: Vec<Vec<usize>> = vec![Vec::new(); 256];
    for (i, f) in forms.iter().enumerate() {
        let Some(&b) = f.bytes.first() else { continue };
        match f.var {
            Var::Native | Var::Swapped => by_byte[usize::from(b)].push(i),
            Var::Xor => by_xor[usize::from(b)].push(i),
            Var::Add => by_sub[usize::from(b)].push(i),
        }
    }
    let runs = program
        .sections
        .iter()
        .filter_map(|s| {
            Some((
                program.section_bytes(s)?,
                s.file_off.0,
                Some(s.va.0),
                s.name.as_str(),
            ))
        })
        .chain(
            program
                .unmapped()
                .into_iter()
                .map(|(off, data)| (data, off, None, UNMAPPED)),
        );
    for (data, off, va, section) in runs {
        for (i, &b) in (0u64..).zip(data.iter()) {
            let at = crate::num::saturating_usize(i);
            let mut report = |name: &'static str, storage: Storage| {
                visit(&Seen {
                    va: va.map(|v| v.saturating_add(i)),
                    file_off: off.saturating_add(i),
                    name,
                    storage,
                    section,
                })
                .is_break()
            };
            for &fi in &by_byte[usize::from(b)] {
                let f = &forms[fi];
                if data.get(at..at.saturating_add(f.bytes.len())) != Some(f.bytes.as_slice()) {
                    continue;
                }
                let storage = match f.var {
                    Var::Native => Storage::Native,
                    Var::Swapped => Storage::Swapped,
                    Var::Xor | Var::Add => continue,
                };
                if report(sigs[f.sig].0, storage) {
                    return;
                }
            }
            let Some(&next) = data.get(at + 1) else {
                continue;
            };
            for (table, xor) in [(&by_xor, true), (&by_sub, false)] {
                let head = if xor { b ^ next } else { next.wrapping_sub(b) };
                for &fi in &table[usize::from(head)] {
                    let f = &forms[fi];
                    let keyed = (0..f.bytes.len()).all(|j| {
                        data.get(at + j)
                            .copied()
                            .zip(data.get(at + j + 1).copied())
                            .is_some_and(|(l, r)| {
                                let d = if xor { l ^ r } else { r.wrapping_sub(l) };
                                d == f.bytes[j]
                            })
                    });
                    if !keyed {
                        continue;
                    }
                    let key = if xor {
                        b ^ sigs[f.sig].1[0]
                    } else {
                        b.wrapping_sub(sigs[f.sig].1[0])
                    };
                    if key == 0 {
                        continue;
                    }
                    let storage = if xor {
                        Storage::Xored(key)
                    } else {
                        Storage::Added(key)
                    };
                    if report(sigs[f.sig].0, storage) {
                        return;
                    }
                }
            }
        }
    }
}

/// Scans the image for the known constants ([`scan`]), keeping the first
/// [`HITS_MAX`].
///
/// # Arguments
///
/// * `program` - The loaded image whose bytes are scanned.
///
/// # Returns
///
/// Hits in [`scan`]'s order.
pub fn find_crypto_constants(program: &Program) -> Vec<CryptoHit> {
    let mut hits = Vec::new();
    scan(program, |seen| {
        hits.push(seen.kept());
        if hits.len() >= HITS_MAX {
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        }
    });
    hits
}

/// Renders hits as the agent-facing table.
///
/// # Arguments
///
/// * `hits` - The hits from [`find_crypto_constants`].
///
/// # Returns
///
/// A `# N crypto/hash constant hits` header (noting when the cap was
/// reached), a column header, then one `va  section  algorithm` row per hit.
pub fn render(hits: &[CryptoHit]) -> String {
    let mut out = format!(
        "# {} crypto/hash constant hits{}\n",
        hits.len(),
        if hits.len() >= HITS_MAX {
            " (cap reached)"
        } else {
            ""
        }
    );
    out.push_str(&rows(hits));
    out
}

/// Renders the column header and one `va  section  algorithm` row per
/// hit, `off=<n>` in the address column for bytes no section maps.
///
/// # Arguments
///
/// * `hits` - The hits to list.
#[must_use]
pub fn rows(hits: &[CryptoHit]) -> String {
    let mut out = String::from("# va          section   algorithm\n");
    for h in hits {
        let at =
            h.va.map_or_else(|| format!("off={:#x}", h.file_off), |va| format!("{va:#x}"));
        out.push_str(&format!(
            "{at:<12} {:<9} {}{}\n",
            h.section, h.name, h.storage
        ));
    }
    out
}
