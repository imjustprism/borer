//! Standard routines recognized by the constants they use.
//!
//! A function that reads one of the known tables [`crate::crypto`] finds
//! (the SHA-256 K table, the AES S-box, a CRC-32 table), or carries enough
//! of an algorithm's constants as immediates in its own instructions (an
//! unrolled MD5 carries its 64 T values, an init writes the eight SHA-256
//! initial values), is marked with what it uses, and an unnamed one is
//! named after it, so a listing, a summary and every call site say
//! `sha256_block` where they said `sub_14000d830`.
//!
//! The claim never outruns the evidence. Round constants (a K or T table)
//! say compression, initial values say init, and both say the whole hash;
//! a table that does not tell the role apart (an S-box, a CRC table) names
//! the algorithm alone. Initial values more than one algorithm shares
//! (SHA-256 and `BLAKE2s`, SHA-512 and `BLAKE2b`, SHA-1 and RIPEMD-160, MD5 and
//! MD4) name both until round constants in the same function settle it.
//! A single constant is never enough: a table hit is a whole 16-byte run
//! of the table, and inline constants count only when most of a small set
//! (every initial value) or a quarter of a round table is there.
//!
//! One pass over every function's instruction bytes, filtered by a bitmap
//! of the constants' low 16 bits, so the cost is a load and a bit test per
//! code byte.

use std::collections::{BTreeMap, BTreeSet};

use super::{Analysis, NameSource, data_referrers};
use crate::program::Program;

/// An algorithm, or the algorithms one set of constants is shared by.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Family {
    /// SHA-256 (and SHA-224, which shares its round constants).
    Sha256,
    /// SHA-256 or `BLAKE2s`, which share the initial values.
    Sha256OrBlake2s,
    /// SHA-512 (and SHA-384, which shares its round constants).
    Sha512,
    /// SHA-512 or `BLAKE2b`, which share the initial values.
    Sha512OrBlake2b,
    /// SHA-1.
    Sha1,
    /// SHA-1 or RIPEMD-160, which share the initial state.
    Sha1OrRipemd160,
    /// MD5.
    Md5,
    /// MD5 or MD4, which share the initial state.
    Md5OrMd4,
    /// CRC-32 with the IEEE 802.3 polynomial.
    Crc32,
    /// CRC-32C with the Castagnoli polynomial.
    Crc32c,
    /// AES, forward direction.
    Aes,
    /// AES, inverse direction.
    AesInverse,
    /// `ChaCha20` or Salsa20, which share the `expand 32-byte k` constant.
    ChaChaOrSalsa20,
    /// Salsa20 with a 16-byte key (`expand 16-byte k`).
    Salsa20,
    /// Blowfish.
    Blowfish,
}

impl Family {
    /// Returns the algorithm's name as a reader knows it.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Family::Sha256 => "SHA-256",
            Family::Sha256OrBlake2s => "SHA-256 or BLAKE2s",
            Family::Sha512 => "SHA-512",
            Family::Sha512OrBlake2b => "SHA-512 or BLAKE2b",
            Family::Sha1 => "SHA-1",
            Family::Sha1OrRipemd160 => "SHA-1 or RIPEMD-160",
            Family::Md5 => "MD5",
            Family::Md5OrMd4 => "MD5 or MD4",
            Family::Crc32 => "CRC-32",
            Family::Crc32c => "CRC-32C",
            Family::Aes => "AES",
            Family::AesInverse => "AES (inverse)",
            Family::ChaChaOrSalsa20 => "ChaCha20 or Salsa20",
            Family::Salsa20 => "Salsa20",
            Family::Blowfish => "Blowfish",
        }
    }

    /// Returns the identifier a name is built from.
    fn id(self) -> &'static str {
        match self {
            Family::Sha256 => "sha256",
            Family::Sha256OrBlake2s => "sha256_or_blake2s",
            Family::Sha512 => "sha512",
            Family::Sha512OrBlake2b => "sha512_or_blake2b",
            Family::Sha1 => "sha1",
            Family::Sha1OrRipemd160 => "sha1_or_ripemd160",
            Family::Md5 => "md5",
            Family::Md5OrMd4 => "md5_or_md4",
            Family::Crc32 => "crc32",
            Family::Crc32c => "crc32c",
            Family::Aes => "aes",
            Family::AesInverse => "aes_inverse",
            Family::ChaChaOrSalsa20 => "chacha_or_salsa20",
            Family::Salsa20 => "salsa20",
            Family::Blowfish => "blowfish",
        }
    }

    /// Returns the one algorithm a shared set of initial values belongs to
    /// once that algorithm's round constants are in the same function or
    /// in a function it calls.
    fn settled_by(self) -> Option<Family> {
        match self {
            Family::Sha256OrBlake2s => Some(Family::Sha256),
            Family::Sha512OrBlake2b => Some(Family::Sha512),
            Family::Sha1OrRipemd160 => Some(Family::Sha1),
            Family::Md5OrMd4 => Some(Family::Md5),
            Family::Sha256
            | Family::Sha512
            | Family::Sha1
            | Family::Md5
            | Family::Crc32
            | Family::Crc32c
            | Family::Aes
            | Family::AesInverse
            | Family::ChaChaOrSalsa20
            | Family::Salsa20
            | Family::Blowfish => None,
        }
    }
}

/// What a set of constants says the function does with its algorithm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Role {
    /// Initial values: the function starts a hash.
    Init,
    /// Round constants: the function runs the rounds (the compression).
    Rounds,
    /// Constants that do not tell the role apart.
    Uses,
}

/// One piece of evidence: a set of an algorithm's constants a function uses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Evidence {
    /// The algorithm the constants belong to.
    pub family: Family,
    /// What the constants say the function does with it.
    pub role: Role,
    /// The constants and where they are: `SHA-256 K constants at
    /// 0x140020000` for a table, `17 of 64 MD5 T constants inline` for
    /// immediates.
    /// Never a quote, so a decompile header line stays one comment.
    pub what: String,
}

/// Most callees a function may have and still be named after the
/// algorithm; one that calls more inlined the routine into something
/// bigger, so it is only marked.
const CALLEES_MAX: usize = 3;

/// Returns what a table [`crate::crypto`] names says, and how many bytes
/// the table spans, so a reference into its middle counts.
///
/// # Arguments
///
/// * `name` - The table's name from [`crate::crypto`].
///
/// # Returns
///
/// `(family, role, length in bytes)`, or `None` for a constant too short
/// or too common to name a function by (`rcon`, a single magic number, the
/// Base64 alphabet).
fn table(name: &str) -> Option<(Family, Role, u64)> {
    /// `(name prefix, family, role, length in bytes)` per table.
    const TABLES: [(&str, Family, Role, u64); 16] = [
        ("AES forward S-box", Family::Aes, Role::Uses, 256),
        ("AES inverse S-box", Family::AesInverse, Role::Uses, 256),
        ("AES Te0", Family::Aes, Role::Uses, 1024),
        ("AES Td0", Family::AesInverse, Role::Uses, 1024),
        ("SHA-256 K", Family::Sha256, Role::Rounds, 256),
        ("SHA-256 initial", Family::Sha256OrBlake2s, Role::Uses, 32),
        ("SHA-512 K", Family::Sha512, Role::Rounds, 640),
        ("SHA-512 / BLAKE2b", Family::Sha512OrBlake2b, Role::Uses, 64),
        ("MD5 / MD4", Family::Md5OrMd4, Role::Uses, 16),
        ("SHA-1 initial", Family::Sha1OrRipemd160, Role::Uses, 20),
        ("MD5 T", Family::Md5, Role::Rounds, 256),
        ("CRC-32 (IEEE", Family::Crc32, Role::Uses, 1024),
        ("CRC-32 slicing", Family::Crc32, Role::Uses, 1024),
        ("CRC-32C", Family::Crc32c, Role::Uses, 1024),
        (
            "ChaCha20 / Salsa20",
            Family::ChaChaOrSalsa20,
            Role::Uses,
            16,
        ),
        ("Salsa20 tau", Family::Salsa20, Role::Uses, 16),
    ];
    if name.starts_with("Blowfish P-array") {
        return Some((Family::Blowfish, Role::Uses, 72));
    }
    TABLES
        .iter()
        .find(|(prefix, ..)| name.starts_with(prefix))
        .map(|&(_, family, role, len)| (family, role, len))
}

/// A set of constants an implementation carries as immediates.
struct Inline {
    /// The algorithm the set belongs to.
    family: Family,
    /// What the set says the function does.
    role: Role,
    /// The set's name in an evidence line.
    what: &'static str,
    /// The values, each as wide as the instruction carries it.
    values: Values,
    /// Fewest distinct values of the set a function must carry.
    need: usize,
}

/// The values of an [`Inline`] set.
#[derive(Clone, Copy)]
enum Values {
    /// 32-bit immediates.
    W32(&'static [u32]),
    /// 64-bit immediates (`movabs`).
    W64(&'static [u64]),
}

impl Values {
    /// Returns how many values the set has.
    fn len(self) -> usize {
        match self {
            Values::W32(v) => v.len(),
            Values::W64(v) => v.len(),
        }
    }
}

/// SHA-1's four round constants; `0xca62c1d6` sets it apart from MD4 and
/// RIPEMD-160, which share the first ones.
const SHA1_K: [u32; 4] = [0x5a82_7999, 0x6ed9_eba1, 0x8f1b_bcdc, 0xca62_c1d6];
/// SHA-1's (and RIPEMD-160's) five initial state words.
const SHA1_H: [u32; 5] = [
    0x6745_2301,
    0xefcd_ab89,
    0x98ba_dcfe,
    0x1032_5476,
    0xc3d2_e1f0,
];
/// MD5's (and MD4's) four initial state words, SHA-1's first four.
const MD5_H: [u32; 4] = [0x6745_2301, 0xefcd_ab89, 0x98ba_dcfe, 0x1032_5476];
/// The `expand 32-byte k` words `ChaCha20` and Salsa20 put in their state.
const SIGMA: [u32; 4] = [0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574];
/// SHA-256's 64 round constants, the cube roots of the first 64 primes.
const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];
/// SHA-256's (and `BLAKE2s`'s) eight initial hash values, the square roots of the first 8 primes.
const SHA256_H: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];
/// SHA-512's 80 round constants, the cube roots of the first 80 primes.
const SHA512_K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];
/// SHA-512's (and `BLAKE2b`'s) eight initial hash values, the square roots of the first 8 primes.
const SHA512_H: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];
/// MD5's 64 T constants, `floor(abs(sin(i + 1)) * 2^32)`.
const MD5_T: [u32; 64] = [
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
];

/// The sets of constants an implementation carries as immediates.
const INLINES: [Inline; 9] = [
    Inline {
        family: Family::Sha256,
        role: Role::Rounds,
        what: "SHA-256 K constants",
        values: Values::W32(&SHA256_K),
        need: 16,
    },
    Inline {
        family: Family::Sha256OrBlake2s,
        role: Role::Uses,
        what: "SHA-256 initial hash values",
        values: Values::W32(&SHA256_H),
        need: 8,
    },
    Inline {
        family: Family::Sha512,
        role: Role::Rounds,
        what: "SHA-512 K constants",
        values: Values::W64(&SHA512_K),
        need: 16,
    },
    Inline {
        family: Family::Sha512OrBlake2b,
        role: Role::Uses,
        what: "SHA-512 initial hash values",
        values: Values::W64(&SHA512_H),
        need: 8,
    },
    Inline {
        family: Family::Sha1,
        role: Role::Rounds,
        what: "SHA-1 K constants",
        values: Values::W32(&SHA1_K),
        need: 4,
    },
    Inline {
        family: Family::Sha1OrRipemd160,
        role: Role::Uses,
        what: "SHA-1 initial state words",
        values: Values::W32(&SHA1_H),
        need: 5,
    },
    Inline {
        family: Family::Md5,
        role: Role::Rounds,
        what: "MD5 T constants",
        values: Values::W32(&MD5_T),
        need: 16,
    },
    Inline {
        family: Family::Md5OrMd4,
        role: Role::Uses,
        what: "MD5 initial state words",
        values: Values::W32(&MD5_H),
        need: 4,
    },
    Inline {
        family: Family::ChaChaOrSalsa20,
        role: Role::Uses,
        what: "sigma (expand 32-byte k) words",
        values: Values::W32(&SIGMA),
        need: 4,
    },
];

/// `(set, shadowed)` pairs of [`INLINES`] indices.
///
/// A match of the first set voids the second, whose values it contains. A SHA-512 constant's
/// high half is the SHA-256 one, and SHA-1's initial state starts with
/// MD5's.
const SHADOWS: [(usize, usize); 3] = [(2, 0), (3, 1), (5, 7)];

/// The [`INLINES`] values sorted for a binary search, with a bitmap of
/// their low 16 bits that rejects almost every code position at once.
struct Lookup {
    /// Bit `v & 0xffff` is set for every 32-bit value.
    bits32: Vec<u64>,
    /// Bit `v & 0xffff` is set for every 64-bit value.
    bits64: Vec<u64>,
    /// `(value, set, index in the set)`, sorted.
    w32: Vec<(u32, usize, usize)>,
    /// `(value, set, index in the set)`, sorted.
    w64: Vec<(u64, usize, usize)>,
}

/// Words of a bitmap over 16 bits.
const BITMAP_WORDS: usize = 1 << 10;

impl Lookup {
    /// Builds the lookup over [`INLINES`].
    fn new() -> Self {
        let mut l = Lookup {
            bits32: vec![0; BITMAP_WORDS],
            bits64: vec![0; BITMAP_WORDS],
            w32: Vec::new(),
            w64: Vec::new(),
        };
        let set = |bits: &mut [u64], low: u16| bits[usize::from(low >> 6)] |= 1 << (low & 63);
        for (s, inline) in INLINES.iter().enumerate() {
            match inline.values {
                Values::W32(v) => {
                    for (i, &x) in v.iter().enumerate() {
                        set(&mut l.bits32, crate::num::lo16(u64::from(x)));
                        l.w32.push((x, s, i));
                    }
                }
                Values::W64(v) => {
                    for (i, &x) in v.iter().enumerate() {
                        set(&mut l.bits64, crate::num::lo16(x));
                        l.w64.push((x, s, i));
                    }
                }
            }
        }
        l.w32.sort_unstable();
        l.w64.sort_unstable();
        l
    }

    /// Marks, per set, the distinct values the bytes carry at any offset.
    ///
    /// # Arguments
    ///
    /// * `bytes` - Instruction bytes of one block.
    /// * `seen` - One bit per value of each [`INLINES`] set, updated in place.
    fn mark(&self, bytes: &[u8], seen: &mut [u128; INLINES.len()]) {
        let test = |bits: &[u64], low: u16| bits[usize::from(low >> 6)] & (1 << (low & 63)) != 0;
        for (at, win) in bytes.windows(4).enumerate() {
            let low = u16::from_le_bytes([win[0], win[1]]);
            if test(&self.bits32, low) {
                let w = u32::from_le_bytes([win[0], win[1], win[2], win[3]]);
                let from = self.w32.partition_point(|e| e.0 < w);
                for &(_, s, i) in self.w32[from..].iter().take_while(|e| e.0 == w) {
                    seen[s] |= 1 << i;
                }
            }
            if test(&self.bits64, low)
                && let Some(Ok(eight)) = bytes.get(at..at + 8).map(<[u8; 8]>::try_from)
            {
                let w = u64::from_le_bytes(eight);
                let from = self.w64.partition_point(|e| e.0 < w);
                for &(_, s, i) in self.w64[from..].iter().take_while(|e| e.0 == w) {
                    seen[s] |= 1 << i;
                }
            }
        }
    }
}

/// Returns the [`INLINES`] sets a function carries enough of.
///
/// # Arguments
///
/// * `program` - The image the instruction bytes are read from.
/// * `lookup` - The constants to look for.
/// * `f` - The function whose blocks are read.
fn inline_evidence(program: &Program, lookup: &Lookup, f: &super::Function) -> Vec<Evidence> {
    let mut seen = [0u128; INLINES.len()];
    for b in &f.blocks {
        let Ok(len) = usize::try_from(b.end.saturating_sub(b.start)) else {
            continue;
        };
        if let Some(bytes) = program.read_va(b.start, len) {
            lookup.mark(bytes, &mut seen);
        }
    }
    let count = |s: usize| crate::num::saturating_usize(u64::from(seen[s].count_ones()));
    let met = |s: usize| count(s) >= INLINES[s].need;
    (0..INLINES.len())
        .filter(|&s| met(s) && !SHADOWS.iter().any(|&(by, of)| of == s && met(by)))
        .map(|s| Evidence {
            family: INLINES[s].family,
            role: INLINES[s].role,
            what: format!(
                "{} of {} {} inline",
                count(s),
                INLINES[s].values.len(),
                INLINES[s].what
            ),
        })
        .collect()
}

/// Settles shared initial values by round constants and orders the
/// evidence by algorithm.
///
/// Round constants in the same function make the values its initial
/// ones; round constants in a function it calls settle only the
/// algorithm, since a caller of the compression may init, finish or do
/// both.
///
/// # Arguments
///
/// * `evidence` - Everything one function uses, in any order.
/// * `callees` - `(callee, algorithm)` per callee that uses the
///   algorithm's round constants.
fn settle(mut evidence: Vec<Evidence>, callees: &[(u64, Family)]) -> Vec<Evidence> {
    let rounds: BTreeSet<Family> = evidence
        .iter()
        .filter(|e| e.role == Role::Rounds)
        .map(|e| e.family)
        .collect();
    let mut calls = Vec::new();
    for e in &mut evidence {
        let Some(one) = e.family.settled_by() else {
            continue;
        };
        if rounds.contains(&one) {
            e.family = one;
            e.role = Role::Init;
        } else if let Some(&(callee, _)) = callees.iter().find(|(_, g)| *g == one) {
            e.family = one;
            calls.push(Evidence {
                family: one,
                role: Role::Uses,
                what: format!("calls {callee:#x}, which uses its round constants"),
            });
        }
    }
    evidence.extend(calls);
    evidence.sort_by(|a, b| (a.family, &a.what).cmp(&(b.family, &b.what)));
    evidence.dedup();
    evidence
}

/// Returns the name the evidence gives a function: one algorithm only,
/// suffixed by what its constants say the function does.
///
/// # Arguments
///
/// * `evidence` - One function's settled evidence.
///
/// # Returns
///
/// `sha256` (initial values and round constants), `sha256_block` (round
/// constants), `sha256_init` (initial values) or `crc32_fn` (constants that
/// do not tell the role); `None` when the constants name several
/// algorithms.
fn name_for(evidence: &[Evidence]) -> Option<String> {
    let family = super::single(evidence.iter().map(|e| e.family).collect::<BTreeSet<_>>())?;
    let has = |r: Role| evidence.iter().any(|e| e.role == r);
    let suffix = match (has(Role::Init), has(Role::Rounds)) {
        (true, true) => "",
        (false, true) => "_block",
        (true, false) => "_init",
        (false, false) => "_fn",
    };
    Some(format!("{}{suffix}", family.id()))
}

/// Renders a function's evidence as one line: each algorithm, then the
/// constants of it the function uses.
///
/// # Arguments
///
/// * `evidence` - One function's evidence, as [`Analysis::recognized`] keeps it.
///
/// # Returns
///
/// `SHA-256 (SHA-256 K constants at 0x2000; 8 of 8 SHA-256 initial hash
/// values inline)`, algorithms separated by `, `.
#[must_use]
pub fn describe(evidence: &[Evidence]) -> String {
    let mut by: BTreeMap<Family, Vec<&str>> = BTreeMap::new();
    for e in evidence {
        by.entry(e.family).or_default().push(&e.what);
    }
    by.iter()
        .map(|(f, whats)| format!("{} ({})", f.label(), whats.join("; ")))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Marks every function that uses a known algorithm's constants, and
/// names the unnamed ones that use one algorithm's alone.
///
/// Runs after every name the binary or a pack gives, so a name from a
/// symbol or a library signature stays and only gains the mark. A
/// function calling more than [`CALLEES_MAX`] others, a thunk and a
/// funclet are marked but not named. A name two functions would share
/// gets each one's entry appended.
///
/// # Arguments
///
/// * `program` - The image the instruction bytes are read from.
/// * `analysis` - Functions, cross-references and the constant tables
///   ([`Analysis::crypto`]); the marks and names are written in place.
pub(crate) fn infer(program: &Program, analysis: &mut Analysis) {
    let mut found: BTreeMap<u64, Vec<Evidence>> = BTreeMap::new();
    for (&va, &name) in &analysis.crypto {
        let Some((family, role, len)) = table(name) else {
            continue;
        };
        for sites in analysis
            .xrefs
            .range(va..va.saturating_add(len))
            .map(|(_, s)| s)
        {
            for from in data_referrers(sites) {
                found.entry(from).or_default().push(Evidence {
                    family,
                    role,
                    what: format!("{} at {va:#x}", name.replace('"', "")),
                });
            }
        }
    }
    let lookup = Lookup::new();
    let inline = super::striped(&analysis.functions, |f| {
        inline_evidence(program, &lookup, f)
    });
    for (f, ev) in analysis.functions.iter().zip(inline) {
        if let Some(ev) = ev.filter(|e| !e.is_empty()) {
            found.entry(f.entry).or_default().extend(ev);
        }
    }
    let rounds: BTreeMap<u64, BTreeSet<Family>> = found
        .iter()
        .map(|(&entry, ev)| {
            let of = ev.iter().filter(|e| e.role == Role::Rounds);
            (entry, of.map(|e| e.family).collect())
        })
        .collect();
    let found: BTreeMap<u64, Vec<Evidence>> = found
        .into_iter()
        .map(|(entry, ev)| {
            let callees: Vec<(u64, Family)> = analysis
                .function(entry)
                .map_or(&[][..], |f| f.callees.as_slice())
                .iter()
                .filter_map(|c| Some((c, rounds.get(c)?)))
                .flat_map(|(&c, fams)| fams.iter().map(move |&g| (c, g)))
                .collect();
            (entry, settle(ev, &callees))
        })
        .collect();
    let mut names: BTreeMap<u64, String> = BTreeMap::new();
    for (&entry, ev) in &found {
        let Some(f) = analysis.function(entry) else {
            continue;
        };
        if f.name.is_some()
            || f.thunk.is_some()
            || f.funclet.is_some()
            || f.callees.len() > CALLEES_MAX
        {
            continue;
        }
        if let Some(n) = name_for(ev) {
            names.insert(entry, n);
        }
    }
    let taken: BTreeSet<&str> = analysis
        .functions
        .iter()
        .filter_map(|f| f.name.as_deref())
        .collect();
    let mut uses: BTreeMap<&str, usize> = BTreeMap::new();
    for n in names.values() {
        *uses.entry(n).or_default() += 1;
    }
    let names: Vec<(u64, String)> = names
        .iter()
        .map(|(&entry, n)| {
            if uses.get(n.as_str()).is_some_and(|&c| c > 1) || taken.contains(n.as_str()) {
                (entry, format!("{n}_{entry:x}"))
            } else {
                (entry, n.clone())
            }
        })
        .collect();
    for (entry, name) in names {
        if let Some(f) = analysis.function_mut(entry) {
            f.name = Some(name);
            f.name_inferred = true;
            f.name_source = NameSource::Constants;
        }
    }
    analysis.recognized = found;
}
