//! The content hashes analysts correlate on: imphash, authentihash and a
//! TLSH-style locality-sensitive hash.
//!
//! All three are hand-rolled: MD5 and SHA-256 are forty lines each, verified
//! against their RFC 1321 and FIPS 180-4 test vectors below, and the crate
//! carries no hash dependency by policy. Every function here is a pure
//! function of the bytes or the [`Program`] it is handed.
//!
//! The variants, stated precisely:
//!
//! * **imphash** is Mandiant's published construction ("Tracking Malware with
//!   Import Hashing", 2014), the one `pefile` and `VirusTotal` compute: every
//!   *named* import becomes `dll.function`, the dll lowercased with its final
//!   extension stripped (`KERNEL32.dll` and `kernel32.DLL` both become
//!   `kernel32`), the function lowercased, the list sorted and joined with
//!   commas, MD5 over the joined string. Borer hashes `dll.function`, not the
//!   bare function name, because the module is what the convention keeps:
//!   name-only hashes collide across DLLs that share an export. Ordinal-only
//!   imports carry no name and are skipped, as are non-PE imports, which have
//!   no module to strip.
//! * **authentihash** is the PE file hash of Authenticode's `calc-file-hash`
//!   (the `CodeString` spec): SHA-256 over the image with the four-byte
//!   checksum, the eight-byte security directory entry and the certificate
//!   table's bytes excluded, so a re-signed or unsigned copy of the same
//!   image hashes alike. The security directory's address field is a file
//!   offset, not an RVA. A range the file cannot hold is clamped to it
//!   rather than refused: hostile headers are the norm here, and the answer
//!   is `None` only when there is no PE header at all.
//! * **tlsh** follows the published TLSH construction (Oliver et al., "TLSH
//!   — A Locality Sensitive Hash", 2013): a 128-bucket histogram fed by
//!   Pearson-style hashes over byte pairs at distances one to three, quartile
//!   points, a chained checksum byte and a length bucket. The 256-byte
//!   permutation table is borer's own (see [`BUCKETS`]); Trend Micro's
//!   reference constants are not reproduced, so a borer tlsh does **not**
//!   match a `tlsh` tool's string and must not be sent to one. The hash is
//!   for correlating builds within borer — same bytes, same hash; near
//!   bytes, small [`Tlsh::distance`] — which is what diff and carry
//!   workflows need.

use std::fmt::Write as _;

use crate::program::{Program, SymbolKind};

// ---- md5 ----

/// MD5's per-step sine-derived constants, RFC 1321's `T` table.
const MD5_K: [u32; 64] = [
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
];

/// Round 1's rotate amounts, repeating every four steps.
const SHIFT_R1: [u32; 4] = [7, 12, 17, 22];
/// Round 2's rotate amounts, repeating every four steps.
const SHIFT_R2: [u32; 4] = [5, 9, 14, 20];
/// Round 3's rotate amounts, repeating every four steps.
const SHIFT_R3: [u32; 4] = [4, 11, 16, 23];
/// Round 4's rotate amounts, repeating every four steps.
const SHIFT_R4: [u32; 4] = [6, 10, 15, 21];

/// One MD5 mixing step: the new `b` register of RFC 1321's `[abcd k s i]`.
///
/// # Arguments
///
/// * `a` / `b` - The `a` and `b` registers before the step.
/// * `f` - The round function's value over `b`, `c` and `d`.
/// * `x` - The message word the step mixes in.
/// * `k` / `s` - The step's sine constant and rotate amount.
#[must_use]
fn md5_step(a: u32, b: u32, f: u32, x: u32, k: u32, s: u32) -> u32 {
    b.wrapping_add(
        a.wrapping_add(f)
            .wrapping_add(x)
            .wrapping_add(k)
            .rotate_left(s),
    )
}

/// Compresses one 64-byte block into `state`, RFC 1321's `MDUpdate`.
///
/// # Arguments
///
/// * `state` - The chaining state, updated in place.
/// * `block` - Exactly 64 message bytes.
fn md5_compress(state: &mut [u32; 4], block: &[u8; 64]) {
    let mut m = [0u32; 16];
    for (i, w) in m.iter_mut().enumerate() {
        let at = 4 * i;
        *w = u32::from_le_bytes([block[at], block[at + 1], block[at + 2], block[at + 3]]);
    }
    let (mut a, mut b, mut c, mut d) = (state[0], state[1], state[2], state[3]);
    for i in 0..16 {
        let f = (b & c) | (!b & d);
        let nb = md5_step(a, b, f, m[i], MD5_K[i], SHIFT_R1[i & 3]);
        (a, b, c, d) = (d, nb, b, c);
    }
    for i in 0..16 {
        let f = (d & b) | (!d & c);
        let g = (5 * i + 1) % 16;
        let nb = md5_step(a, b, f, m[g], MD5_K[16 + i], SHIFT_R2[i & 3]);
        (a, b, c, d) = (d, nb, b, c);
    }
    for i in 0..16 {
        let f = b ^ c ^ d;
        let g = (3 * i + 5) % 16;
        let nb = md5_step(a, b, f, m[g], MD5_K[32 + i], SHIFT_R3[i & 3]);
        (a, b, c, d) = (d, nb, b, c);
    }
    for i in 0..16 {
        let f = c ^ (b | !d);
        let g = (7 * i) % 16;
        let nb = md5_step(a, b, f, m[g], MD5_K[48 + i], SHIFT_R4[i & 3]);
        (a, b, c, d) = (d, nb, b, c);
    }
    for (s, v) in state.iter_mut().zip([a, b, c, d]) {
        *s = s.wrapping_add(v);
    }
}

/// MD5 over `data`, RFC 1321.
///
/// Not a checksum for anything adversarial: MD5 is broken for collision
/// resistance. It lives here because imphash is defined as MD5 and the
/// threat-intel feeds it is compared against publish MD5.
///
/// # Arguments
///
/// * `data` - The bytes to hash.
///
/// # Returns
///
/// The 16-byte digest.
#[must_use]
pub fn md5(data: &[u8]) -> [u8; 16] {
    let mut state = [0x6745_2301u32, 0xefcd_ab89, 0x98ba_dcfe, 0x1032_5476];
    for block in data.chunks_exact(64) {
        if let Ok(block) = <&[u8; 64]>::try_from(block) {
            md5_compress(&mut state, block);
        }
    }
    let rem = data.len() % 64;
    let mut tail = [0u8; 128];
    tail[..rem].copy_from_slice(&data[data.len() - rem..]);
    tail[rem] = 0x80;
    let at = if rem < 56 { 56 } else { 120 };
    tail[at..at + 8].copy_from_slice(
        &(u64::try_from(data.len())
            .unwrap_or(u64::MAX)
            .wrapping_mul(8))
        .to_le_bytes(),
    );
    md5_compress(&mut state, tail.first_chunk::<64>().unwrap_or(&[0; 64]));
    if rem >= 56 {
        md5_compress(&mut state, tail.last_chunk::<64>().unwrap_or(&[0; 64]));
    }
    let mut out = [0u8; 16];
    for (chunk, word) in out.chunks_exact_mut(4).zip(state) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    out
}

// ---- sha-256 ----

/// SHA-256's round constants, the first 64 primes' cube-root fractions
/// (FIPS 180-4 section 4.2.2).
const SHA_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// SHA-256's initial hash, the square roots of the first eight primes
/// (FIPS 180-4 section 5.3.3).
const SHA_IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Compresses one 64-byte block into `h`, FIPS 180-4 section 6.2.2.
///
/// # Arguments
///
/// * `h` - The chaining state, updated in place.
/// * `block` - Exactly 64 message bytes.
fn sha256_block(h: &mut [u32; 8], block: &[u8; 64]) {
    let mut w = [0u32; 64];
    for (i, word) in w.iter_mut().take(16).enumerate() {
        let at = 4 * i;
        *word = u32::from_be_bytes([block[at], block[at + 1], block[at + 2], block[at + 3]]);
    }
    for i in 16..64 {
        // SPEC: FIPS 180-4 section 4.1.2's sigma0/sigma1 are rotate-right
        // functions; rotate_left by the complement writes them as `u32`
        // rotations with no cast.
        let s0 = w[i - 15].rotate_left(25) ^ w[i - 15].rotate_left(14) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_left(15) ^ w[i - 2].rotate_left(13) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = *h;
    for i in 0..64 {
        // SPEC: big sigma1/big sigma0 of section 4.1.2, rotate-right
        // functions written as their rotate-left complements.
        let big_s1 = e.rotate_left(26) ^ e.rotate_left(21) ^ e.rotate_left(7);
        let ch = (e & f) ^ (!e & g);
        let t1 = hh
            .wrapping_add(big_s1)
            .wrapping_add(ch)
            .wrapping_add(SHA_K[i])
            .wrapping_add(w[i]);
        let big_s0 = a.rotate_left(30) ^ a.rotate_left(19) ^ a.rotate_left(10);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = big_s0.wrapping_add(maj);
        hh = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    for (s, v) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
        *s = s.wrapping_add(v);
    }
}

/// Incremental SHA-256 over byte segments, for hashing an image in pieces
/// the way authentihash skips its excluded ranges.
#[derive(Debug, Clone)]
struct Sha256 {
    /// The chaining state.
    h: [u32; 8],
    /// Bytes of the next block held back.
    pending: [u8; 64],
    /// How many of `pending` are filled.
    held: usize,
    /// Total bytes fed so far.
    total: u64,
}

impl Sha256 {
    /// A fresh hasher at the initial hash.
    fn new() -> Self {
        Sha256 {
            h: SHA_IV,
            pending: [0; 64],
            held: 0,
            total: 0,
        }
    }

    /// Feeds more bytes.
    ///
    /// # Arguments
    ///
    /// * `data` - The bytes to hash.
    fn update(&mut self, data: &[u8]) {
        self.total = self
            .total
            .wrapping_add(u64::try_from(data.len()).unwrap_or(u64::MAX));
        let fill = (64 - self.held).min(data.len());
        self.pending[self.held..self.held + fill].copy_from_slice(&data[..fill]);
        self.held += fill;
        if self.held < 64 {
            return;
        }
        if let Ok(block) = <&[u8; 64]>::try_from(&self.pending[..]) {
            sha256_block(&mut self.h, block);
        }
        self.held = 0;
        let rest = &data[fill..];
        for block in rest.chunks_exact(64) {
            if let Ok(block) = <&[u8; 64]>::try_from(block) {
                sha256_block(&mut self.h, block);
            }
        }
        let rem = rest.len() % 64;
        self.pending[..rem].copy_from_slice(&rest[rest.len() - rem..]);
        self.held = rem;
    }

    /// Pads the message and finishes the digest.
    ///
    /// # Returns
    ///
    /// The 32-byte digest of every byte fed.
    fn finish(mut self) -> [u8; 32] {
        let bits = self.total.wrapping_mul(8);
        let held = self.held;
        self.pending[held] = 0x80;
        if held < 56 {
            self.pending[held + 1..56].fill(0);
            self.pending[56..].copy_from_slice(&bits.to_be_bytes());
            if let Ok(block) = <&[u8; 64]>::try_from(&self.pending[..]) {
                sha256_block(&mut self.h, block);
            }
        } else {
            self.pending[held + 1..].fill(0);
            if let Ok(block) = <&[u8; 64]>::try_from(&self.pending[..]) {
                sha256_block(&mut self.h, block);
            }
            let mut last = [0u8; 64];
            last[56..].copy_from_slice(&bits.to_be_bytes());
            sha256_block(&mut self.h, &last);
        }
        let mut out = [0u8; 32];
        for (chunk, word) in out.chunks_exact_mut(4).zip(self.h) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        out
    }
}

/// SHA-256 over `data`, FIPS 180-4.
///
/// # Arguments
///
/// * `data` - The bytes to hash.
///
/// # Returns
///
/// The 32-byte digest.
#[must_use]
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(data);
    h.finish()
}

// ---- imphash ----

/// The dll name lowercased with its final extension removed.
///
/// `KERNEL32.dll` and `kernel32.DLL` both become `kernel32`; a name whose
/// only dot leads it (`.dll`) keeps its whole text, since an empty stem
/// would merge every such module.
///
/// # Arguments
///
/// * `dll` - The module name as the import table states it.
#[must_use]
fn dll_stem(dll: &str) -> String {
    let lower = dll.to_lowercase();
    match lower.rfind('.') {
        Some(at) if at > 0 => lower[..at].to_owned(),
        _ => lower,
    }
}

/// Mandiant's import hash of the program's import table.
///
/// See the module docs for the exact variant: every named import becomes
/// `dll.function` (dll lowercased, extension stripped; function lowercased),
/// the list is sorted and comma-joined, and the digest is MD5 of that
/// string. Ordinal imports carry no name and are skipped; non-PE imports
/// carry no module and are skipped too.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// The 16-byte imphash, or `None` when no import is named — every such file
/// would share the hash of an empty list.
#[must_use]
pub fn imphash(program: &Program) -> Option<[u8; 16]> {
    let mut names: Vec<String> = program
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .filter_map(|s| s.name.rsplit_once('!'))
        .filter(|&(_, func)| func != "(unnamed)")
        .map(|(dll, func)| format!("{}.{}", dll_stem(dll), func.to_lowercase()))
        .collect();
    if names.is_empty() {
        return None;
    }
    names.sort();
    let joined = names.join(",");
    Some(md5(joined.as_bytes()))
}

// ---- authentihash ----

/// The security directory's slot in the data directory table.
const SECURITY_DIR: usize = 4;

/// The Authenticode file hash of the program's image.
///
/// SHA-256 over the whole file with the checksum field, the security
/// directory entry and the certificate table's bytes excluded, as the module
/// docs state. Ranges the file cannot hold are clamped to it.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// The 32-byte authentihash, or `None` when the file carries no PE header.
#[must_use]
pub fn authentihash(program: &Program) -> Option<[u8; 32]> {
    let bytes = &program.bytes;
    // SPEC: the checksum field sits 64 bytes into either optional header,
    // which begins 24 bytes after the `PE\0\0` signature.
    let checksum = crate::program::pe_signature(bytes)?
        .checked_add(24)?
        .checked_add(64)?;
    let after_checksum = checksum.checked_add(4)?;
    let mut h = Sha256::new();
    h.update(bytes.get(..checksum)?);
    let Some((entry, _)) = crate::program::directory_entry(bytes, SECURITY_DIR) else {
        h.update(bytes.get(after_checksum..)?);
        return Some(h.finish());
    };
    h.update(bytes.get(after_checksum..entry)?);
    let entry_end = entry.checked_add(8)?;
    // An unsigned PE carries a zeroed entry, and a hostile one any value:
    // the table cannot start inside the headers, so the start is clamped to
    // lie between the entry's end and the file's end.
    let start = usize::try_from(u64::from(crate::program::le_u32(bytes, entry)?))
        .ok()?
        .clamp(entry_end, bytes.len());
    let size = usize::try_from(u64::from(crate::program::le_u32(
        bytes,
        entry.checked_add(4)?,
    )?))
    .ok()?;
    let cert_end = start.saturating_add(size).min(bytes.len());
    h.update(bytes.get(entry_end..start)?);
    h.update(bytes.get(cert_end.max(entry_end)..)?);
    Some(h.finish())
}

// ---- tlsh ----

/// Borer's 256-byte permutation for the TLSH bucket hashes and checksum.
///
/// A Fisher-Yates shuffle of `0..=255` driven by an `xorshift64*` generator
/// seeded with `0x9e37_79b9_7f4a_7c15` (the golden ratio constant). Trend
/// Micro's own table is not reproduced, so a borer tlsh only ever matches
/// another borer tlsh.
const BUCKETS: [u8; 256] = [
    0x37, 0x36, 0x1f, 0x14, 0x48, 0x28, 0x3a, 0x09, 0xbd, 0x93, 0xe0, 0x79, 0x22, 0x63, 0x71, 0x1c,
    0xe7, 0x10, 0x55, 0xd6, 0x1a, 0x06, 0x7d, 0x3c, 0xb7, 0x2a, 0x94, 0x3d, 0xae, 0x41, 0xb3, 0x5c,
    0xbe, 0xda, 0x51, 0xfb, 0xdb, 0x9b, 0x69, 0xb9, 0x0a, 0x60, 0xb1, 0xa6, 0xce, 0xf3, 0x39, 0x3b,
    0xfe, 0x08, 0xa0, 0xe5, 0x75, 0x7a, 0xcd, 0x78, 0x9c, 0xa9, 0x0e, 0x8c, 0xe6, 0x1d, 0x24, 0x59,
    0x6e, 0xec, 0xed, 0x00, 0x4a, 0xaa, 0x68, 0x46, 0xac, 0xad, 0x5d, 0xee, 0xb4, 0x42, 0xe2, 0x90,
    0x30, 0x5e, 0x01, 0x74, 0x07, 0xc3, 0xcb, 0x7c, 0x20, 0xc0, 0x8d, 0x12, 0x32, 0xea, 0x4e, 0xf0,
    0x0b, 0xc2, 0x2e, 0xb8, 0x83, 0x35, 0xb0, 0xe9, 0x97, 0x13, 0x4b, 0x6c, 0x86, 0xd0, 0x21, 0xdd,
    0xcc, 0xa2, 0xa7, 0xd4, 0xe4, 0x5b, 0x7f, 0xf2, 0xc9, 0x53, 0x44, 0xc5, 0x88, 0xbc, 0xcf, 0xf1,
    0x29, 0x5f, 0x0d, 0x8e, 0xeb, 0x2d, 0xd1, 0xc1, 0xa8, 0x6f, 0x73, 0x61, 0xfa, 0xc6, 0x56, 0xd5,
    0x49, 0x9e, 0xc4, 0x54, 0x26, 0x45, 0xa4, 0xf9, 0x18, 0x6d, 0xb5, 0xdc, 0xde, 0xd3, 0x03, 0x8f,
    0x6b, 0x5a, 0xaf, 0x76, 0xf8, 0x8a, 0x3f, 0xc7, 0x0f, 0x05, 0xe1, 0x52, 0x19, 0x4d, 0x96, 0xfc,
    0x9a, 0x66, 0x50, 0x87, 0xab, 0x0c, 0x4c, 0xfd, 0x77, 0xa1, 0xd2, 0x89, 0xb2, 0xef, 0x70, 0x47,
    0x80, 0x65, 0xd7, 0xbf, 0xa5, 0x2b, 0x84, 0x16, 0x58, 0x40, 0x6a, 0x3e, 0xd8, 0x31, 0x34, 0x15,
    0xb6, 0x8b, 0x2c, 0x9f, 0x1e, 0x57, 0x04, 0x7e, 0x38, 0x27, 0xa3, 0x72, 0xe3, 0xf5, 0xf6, 0xe8,
    0x02, 0x2f, 0x95, 0x9d, 0xf7, 0x11, 0x7b, 0xd9, 0x92, 0xba, 0x33, 0x81, 0xff, 0x4f, 0x91, 0xf4,
    0x17, 0x23, 0xca, 0x85, 0x98, 0x43, 0xc8, 0x67, 0x1b, 0x25, 0xbb, 0x64, 0x62, 0x82, 0xdf, 0x99,
];

/// One TLSH digest: a checksum byte, a length bucket, the two quartile
/// points it was cut at, and 128 two-bit bucket levels packed four to a byte
/// (bucket 0 in the low bits of byte 0).
///
/// Built by [`tlsh`]; compared with [`Tlsh::distance`] and carried as hex by
/// [`Tlsh::hex`]. The checksum byte takes no part in the distance: it is
/// compared by equality alone, since any difference there means the streams
/// differ even when every bucket agrees.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tlsh {
    /// The chained permutation checksum of the byte stream.
    checksum: u8,
    /// `floor(log2(length))`, capped at 255.
    len_bucket: u8,
    /// The first quartile of the 128 bucket counts, capped at 255.
    q1: u8,
    /// The third quartile of the 128 bucket counts, capped at 255.
    q3: u8,
    /// The 128 two-bit levels, four buckets to a byte.
    levels: [u8; 32],
}

/// The bucket a pair of bytes at distance `salt` falls into.
///
/// The salt shifts each byte's index into [`BUCKETS`] differently, so the
/// three distances see three different mixtures of the same table; the xor
/// of the two lookups and the seven-bit mask keep the bucket in `0..128`.
///
/// # Arguments
///
/// * `salt` - The pair's distance, `1..=3`.
/// * `left` / `right` - The anchor byte and its neighbour.
#[must_use]
fn bucket(salt: u8, left: u8, right: u8) -> usize {
    usize::from(
        BUCKETS[usize::from(salt.wrapping_add(left)) & 0xff]
            ^ BUCKETS[usize::from(salt.wrapping_add(1).wrapping_add(right)) & 0xff],
    ) & 0x7f
}

/// Hashes a byte stream into a TLSH digest.
///
/// The construction is the published TLSH scheme with borer's permutation
/// table (see the module docs): each anchor position hashes its three
/// right-neighbour pairs into 128 buckets, the counts are cut at their
/// quartiles into two-bit levels, and a chained checksum byte and a length
/// bucket ride along in the header.
///
/// # Arguments
///
/// * `data` - The bytes to hash; the whole file is the usual input.
///
/// # Returns
///
/// The digest, or `None` for an empty stream, whose every count is zero and
/// whose digest would say "equal" to any other empty one.
#[must_use]
pub fn tlsh(data: &[u8]) -> Option<Tlsh> {
    if data.is_empty() {
        return None;
    }
    let mut checksum = 0u8;
    for &b in data {
        checksum = BUCKETS[usize::from(checksum ^ b)];
    }
    let mut counts = [0usize; 128];
    let end = data.len().saturating_sub(3);
    for (i, &left) in data.iter().enumerate().take(end) {
        for salt in 1u8..=3 {
            counts[bucket(salt, left, data[i + usize::from(salt)])] += 1;
        }
    }
    let mut sorted = counts;
    sorted.sort_unstable();
    let (q1, q2, q3) = (sorted[32], sorted[64], sorted[96]);
    let mut levels = [0u8; 32];
    for (i, &count) in counts.iter().enumerate() {
        let level: u8 = if count == 0 {
            0
        } else if count <= q1 {
            1
        } else if count <= q2 {
            2
        } else {
            3
        };
        levels[i / 4] |= level << (2 * (i % 4));
    }
    Some(Tlsh {
        checksum,
        len_bucket: u8::try_from(usize::BITS - 1 - data.len().leading_zeros()).unwrap_or(u8::MAX),
        q1: u8::try_from(q1.min(usize::from(u8::MAX))).unwrap_or(u8::MAX),
        q3: u8::try_from(q3.min(usize::from(u8::MAX))).unwrap_or(u8::MAX),
        levels,
    })
}

impl Tlsh {
    /// The digest as 70 lowercase hex characters: checksum, length bucket,
    /// `q1`, `q3`, then the 32 packed level bytes.
    ///
    /// # Returns
    ///
    /// The hex form.
    #[must_use]
    pub fn hex(&self) -> String {
        let head = [self.checksum, self.len_bucket, self.q1, self.q3];
        let mut out = String::with_capacity(70);
        for b in head.iter().chain(self.levels.iter()) {
            let _ = write!(out, "{b:02x}");
        }
        out
    }

    /// How far two streams are, from their digests alone.
    ///
    /// The sum of the 128 absolute level differences plus one capped term
    /// each for the length bucket and the two quartile points, so the
    /// histogram dominates and the header bytes only break ties: `0` for the
    /// same digest, single digits for near streams, three digits for
    /// unrelated ones. The checksum is not in the distance; equal digests
    /// with different checksums never happen, and unequal ones are already
    /// apart.
    ///
    /// # Arguments
    ///
    /// * `other` - The digest to compare with.
    ///
    /// # Returns
    ///
    /// The distance, at most `429` (384 of levels, 45 of header terms).
    #[must_use]
    pub fn distance(&self, other: &Tlsh) -> u32 {
        let mut hist = 0u32;
        for i in 0..128 {
            let shift = 2 * (i % 4);
            let (a, b) = (
                self.levels[i / 4] >> shift & 3,
                other.levels[i / 4] >> shift & 3,
            );
            hist += u32::from(a.abs_diff(b));
        }
        hist + u32::from(self.len_bucket.abs_diff(other.len_bucket)).min(15)
            + u32::from(self.q1.abs_diff(other.q1)).min(15)
            + u32::from(self.q3.abs_diff(other.q3)).min(15)
    }
}

// ---- surface ----

/// Renders the content hashes as the `borer://hashes` answer.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// A header naming the file, one row per hash (`-` when it does not apply),
/// and one note line saying what the tlsh variant does and does not match.
#[must_use]
pub fn hashes_tsv(program: &Program) -> String {
    let hex = |digest: Option<&[u8]>| {
        digest.map_or_else(
            || "-".to_owned(),
            |d| d.iter().map(|b| format!("{b:02x}")).collect::<String>(),
        )
    };
    let mut out = format!(
        "# content hashes of {}\nimphash       {}\nauthentihash  {}\ntlsh          {}\n",
        program.path.display(),
        hex(imphash(program).as_ref().map(|d| d.as_slice())),
        hex(authentihash(program).as_ref().map(|d| d.as_slice())),
        tlsh(&program.bytes).map_or_else(|| "-".to_owned(), |t| t.hex()),
    );
    out.push_str(
        "# tlsh is borer's variant: correlate hashes and distances within borer, not against Trend Micro tlsh strings\n",
    );
    out
}

#[cfg(test)]
mod tests {
    #![expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]

    use super::*;

    /// RFC 1321 appendix A.5's seven test vectors.
    #[test]
    fn md5_matches_rfc_1321() {
        let vectors = [
            ("", "d41d8cd98f00b204e9800998ecf8427e"),
            ("a", "0cc175b9c0f1b6a831c399e269772661"),
            ("abc", "900150983cd24fb0d6963f7d28e17f72"),
            ("message digest", "f96b697d7cb7938d525a2f31aaf161d0"),
            (
                "abcdefghijklmnopqrstuvwxyz",
                "c3fcd3d76192e4007dfb496cca67e13b",
            ),
            (
                "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
                "d174ab98d277d9f5a5611c2c9f419d9f",
            ),
            (
                "12345678901234567890123456789012345678901234567890123456789012345678901234567890",
                "57edf4a22be3c955ac49da2e2107b67a",
            ),
        ];
        for (input, want) in vectors {
            let got = md5(input.as_bytes())
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>();
            assert_eq!(got, want, "md5({input:?})");
        }
    }

    /// FIPS 180-4's SHA-256 vectors, including the million-`a` message.
    #[test]
    fn sha256_matches_fips_180_4() {
        let vectors = [
            (
                "",
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                "abc",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            ),
            (
                "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
                "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
            ),
        ];
        for (input, want) in vectors {
            let got = sha256(input.as_bytes())
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>();
            assert_eq!(got, want, "sha256({input:?})");
        }
        let million = vec![b'a'; 1_000_000];
        assert_eq!(
            sha256(&million)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>(),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
    }

    /// The streaming hasher over segments answers what the one-shot does.
    #[test]
    fn streaming_sha256_matches_one_shot() {
        let mut h = Sha256::new();
        for part in ["ab", "c", "defghijklmnopqrstuvwxyz012345"] {
            h.update(part.as_bytes());
        }
        let stream = h
            .finish()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        let one = sha256(b"abcdefghijklmnopqrstuvwxyz012345")
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        assert_eq!(stream, one);
    }

    /// The dll stem strips one extension, case-insensitively, and keeps a
    /// name whose only dot leads it.
    #[test]
    fn dll_stem_strips_one_extension() {
        assert_eq!(dll_stem("KERNEL32.dll"), "kernel32");
        assert_eq!(dll_stem("kernel32.DLL"), "kernel32");
        assert_eq!(
            dll_stem("api-ms-win-crt-runtime-l1-1-0.dll"),
            "api-ms-win-crt-runtime-l1-1-0"
        );
        assert_eq!(dll_stem("noext"), "noext");
        assert_eq!(dll_stem(".dll"), ".dll");
    }

    /// Pinned against an independent model of the variant: the same input
    /// hashes the same, one flipped byte in a kilobyte stays near, and an
    /// unrelated kilobyte lands far away.
    #[test]
    fn tlsh_is_self_consistent() {
        let base: Vec<u8> = (0..1024usize)
            .map(|i| u8::try_from(i % 256).unwrap_or(0))
            .collect();
        let mut near = base.clone();
        near[600] ^= 0xff;
        let far: Vec<u8> = (0..1024usize)
            .map(|i| u8::try_from((i * 7 + 13) % 256).unwrap_or(0))
            .collect();
        let h = tlsh(&base).expect("a non-empty stream hashes");
        let near_h = tlsh(&near).expect("near hashes");
        let far_h = tlsh(&far).expect("far hashes");
        assert_eq!(
            h.hex(),
            "d50a101cd566bbdfae6df5ddb9feab6fbd9ae5e7b9bb7b6da9dcdf6baa75aeba7a9deddb"
        );
        assert_eq!(
            near_h.hex(),
            "b90a101cd566bbdfae6df5ddb9feab6fbd9ae5e7bdbb7b6da9dcdf6baa75aefa7a9deddb"
        );
        assert_eq!(
            far_h.hex(),
            "bb0a1320dd5e9bfbefbf6bb9dabbffab9befb7699ef5b56f6ea9bdbbfeedaa65fb5b5975"
        );
        assert_eq!(h.distance(&h), 0);
        assert_eq!(h.distance(&near_h), 2);
        assert_eq!(h.distance(&far_h), 122);
        assert!(tlsh(&[]).is_none());
    }
}
