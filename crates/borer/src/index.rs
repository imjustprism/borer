//! The decompilation index: every function's pseudo-C, decompiled once and
//! kept on disk, so a question over the whole program is one scan of a file
//! rather than a hundred decompiles.
//!
//! The engine stays pure; this module owns the file. An index is keyed by
//! the program's bytes and the borer executable that produced it, so a
//! rebuilt borer or a patched program never reads a stale one, and a corrupt
//! file is treated as absent and rebuilt: its header carries a digest of
//! every record, so an edited text is caught as surely as a cut one.
//!
//! The file is named `<program>-<engine>.pcidx`, so every index of one
//! program shares a prefix: saving a new one removes the others, which
//! only an older borer or another set of packs could read, and the
//! directory is held under [`CACHE_MAX`] bytes, oldest first. Without that
//! every rebuild of borer left one more copy of every program's index.

use std::fmt::Write as _;
use std::io::{BufReader, BufWriter, Read, Write as _};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use borer_engine::analysis::decompile::decompile_named_all;
use borer_engine::analysis::{Analysis, Overlay, name_of, render};
use borer_engine::pack::Packs;
use borer_engine::program::Program;
use borer_engine::table::Window;
use rayon::prelude::*;

mod key;
pub use key::index_key;

/// Magic bytes opening an index file.
const MAGIC: &[u8; 8] = b"BORERIDX";
/// Layout version of the file; bump when the record shape changes.
const FORMAT: u32 = 4;
/// Longest name or text one record may carry, a bound on a corrupt length.
const RECORD_MAX: usize = 64 << 20;
/// Fewest bytes one record can hold: its entry and two length words. A
/// count the file cannot hold that many bytes per record of is refused,
/// since no record it could stand for was ever written.
const RECORD_FLOOR: u64 = 16;
/// Environment variable naming the directory indexes live in.
const CACHE_ENV: &str = "BORER_CACHE_DIR";
/// Extension of an index file.
pub const EXTENSION: &str = "pcidx";
/// Most bytes the index directory holds; past it the least recently
/// written indexes are removed first.
const CACHE_MAX: u64 = 1 << 30;

/// What an index file is named by: the program it was decompiled from, and
/// the borer build, file format and packs that decompiled it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IndexKey {
    /// The first 64 bits of the SHA-256 of the program's bytes, shared by
    /// every index of the program. A hash a file can be built to collide
    /// with (FNV-1a was) let an analyzed file store its index under the key
    /// of a known binary, which then read the other's text; a second
    /// preimage of 64 bits of SHA-256 costs 2^64 hashes.
    pub program: u64,
    /// FNV-1a of the file format, the packs, and the borer executable's
    /// size and modification time.
    pub engine: u64,
}

impl IndexKey {
    /// The file name the index is stored under: `<program>-<engine>.pcidx`,
    /// each half sixteen hex digits.
    #[must_use]
    pub fn file_name(self) -> String {
        format!("{:016x}-{:016x}.{EXTENSION}", self.program, self.engine)
    }
}

/// Whether a file stem is `<program>-<engine>`, two sixteen-digit hex
/// halves: the name every index this format writes has.
///
/// # Arguments
///
/// * `stem` - The file name without its extension.
fn is_key_name(stem: &str) -> bool {
    stem.split_once('-').is_some_and(|(program, engine)| {
        [program, engine]
            .iter()
            .all(|half| half.len() == 16 && half.bytes().all(|b| b.is_ascii_hexdigit()))
    })
}

/// One function as the index holds it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexedFunction {
    /// The function's entry address.
    pub entry: u64,
    /// Its name at build time (analysis names; the overlay is not applied).
    pub name: String,
    /// Its pseudo-C as `decompile` renders it.
    pub text: String,
}

/// Every function's pseudo-C for one program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeIndex {
    /// The key the file is named by; see [`index_key`].
    pub key: IndexKey,
    /// The functions in entry order.
    pub functions: Vec<IndexedFunction>,
    /// The trigram index over the functions' texts, the prefilter a
    /// literal grep intersects instead of scanning every line.
    pub postings: Postings,
}

impl CodeIndex {
    /// Sum of the text sizes, in bytes.
    #[must_use]
    pub fn text_bytes(&self) -> usize {
        self.functions.iter().map(|f| f.text.len()).sum()
    }
}

/// The trigram index over every function's text: for each trigram the
/// ascending indices of the functions whose folded text holds it.
///
/// The fold is ASCII case-folding over the identifier alphabet
/// `[a-z0-9_]`; every other byte breaks a run. A line holds a literal
/// only when its function's folded text holds every trigram of the
/// literal's folded runs, so a literal grep intersects a handful of
/// posting lists and line-scans only the survivors - the whole program's
/// pseudo-C is never touched for a word it cannot hold. An expression
/// asks nothing of the index: its matches need not hold any one literal,
/// so it scans as before, in stripes.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Postings {
    /// [`TRIGRAMS`] lists, one per trigram in id order, each holding the
    /// ascending indices of the functions whose text spells it.
    lists: Vec<Vec<u32>>,
}

/// The symbols a trigram is spelled over: the ASCII letters case-folded,
/// the digits and the underscore, the alphabet a C identifier uses.
const SYMBOLS: usize = 37;
/// The count of trigrams the fold can spell, [`SYMBOLS`] cubed.
const TRIGRAMS: usize = SYMBOLS * SYMBOLS * SYMBOLS;

/// One byte's symbol number in the trigram alphabet.
///
/// # Arguments
///
/// * `b` - The byte as it stands in a text or a query.
///
/// # Returns
///
/// The folded symbol below [`SYMBOLS`], or `None` when the byte breaks a
/// run.
fn symbol(b: u8) -> Option<u8> {
    match b {
        b'a'..=b'z' => Some(b - b'a'),
        b'0'..=b'9' => Some(b - b'0' + 26),
        b'_' => Some(36),
        b'A'..=b'Z' => Some(b - b'A'),
        _ => None,
    }
}

/// The trigram three folded symbols spell.
///
/// # Arguments
///
/// * `a`, `b`, `c` - The symbols, as [`symbol`] numbers.
///
/// # Returns
///
/// The trigram's id, below [`TRIGRAMS`].
fn trigram(a: u8, b: u8, c: u8) -> usize {
    (usize::from(a) * SYMBOLS + usize::from(b)) * SYMBOLS + usize::from(c)
}

/// The ids of every trigram the folded runs of `text` spell.
///
/// A run is a stretch of the identifier alphabet; trigrams never span
/// past a byte outside it, and neither does a literal's run, so the ids
/// of a query's runs are exactly the ids its matches' lines must hold.
///
/// # Arguments
///
/// * `text` - A query literal, folded as it is.
///
/// # Returns
///
/// The trigram ids, unsorted and undeduped; empty for text without a
/// three-symbol run.
fn trigram_ids(text: &str) -> Vec<usize> {
    let mut ids = Vec::new();
    let mut run = ([0u8; 2], 0usize);
    for &b in text.as_bytes() {
        let Some(s) = symbol(b) else {
            run.1 = 0;
            continue;
        };
        match run.1 {
            0 => {
                run.0[0] = s;
                run.1 = 1;
            }
            1 => {
                run.0[1] = s;
                run.1 = 2;
            }
            _ => {
                ids.push(trigram(run.0[0], run.0[1], s));
                run.0 = [run.0[1], s];
            }
        }
    }
    ids
}

/// Indexes every function's text into postings, one pass per function.
///
/// # Arguments
///
/// * `functions` - The records the index holds, in order.
///
/// # Returns
///
/// The postings over their texts; an id's list holds each function
/// index once, ascending.
fn trigram_postings(functions: &[IndexedFunction]) -> Postings {
    let mut sieve = vec![false; TRIGRAMS];
    let mut touched: Vec<usize> = Vec::new();
    let mut lists = vec![Vec::<u32>::new(); TRIGRAMS];
    for (i, f) in functions.iter().enumerate() {
        let Some(i) = u32::try_from(i).ok() else {
            continue;
        };
        touched.clear();
        let mut run = ([0u8; 2], 0usize);
        for &b in f.text.as_bytes() {
            let Some(s) = symbol(b) else {
                run.1 = 0;
                continue;
            };
            let id = match run.1 {
                0 => {
                    run.0[0] = s;
                    run.1 = 1;
                    continue;
                }
                1 => {
                    run.0[1] = s;
                    run.1 = 2;
                    continue;
                }
                _ => trigram(run.0[0], run.0[1], s),
            };
            if !sieve[id] {
                sieve[id] = true;
                touched.push(id);
            }
            run.0 = [run.0[1], s];
        }
        for id in touched.drain(..) {
            lists[id].push(i);
            sieve[id] = false;
        }
    }
    Postings { lists }
}

/// One pseudo-C line that matched a query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrepHit {
    /// Entry of the function the line is in.
    pub entry: u64,
    /// The function's name.
    pub name: String,
    /// One-based line number inside the function's text.
    pub line_no: usize,
    /// The line, trimmed.
    pub line: String,
}

/// Prefix that opens a regular expression in a grep pattern.
const REGEX_PREFIX: &str = "re:";

/// What a grep holds each line against.
#[derive(Debug, Clone)]
pub enum Matcher {
    /// Text a line must contain exactly.
    Literal(String),
    /// A regular expression a line must match somewhere.
    Regex(regex::Regex),
}

impl Matcher {
    /// Reads a pattern: `re:` opens a regular expression (the `regex` crate's
    /// syntax, `(?i)` for case-insensitive), anything else is text matched
    /// exactly.
    ///
    /// # Arguments
    ///
    /// * `pattern` - The pattern as the caller wrote it.
    ///
    /// # Errors
    ///
    /// When the expression does not parse, with the parser's message.
    pub fn parse(pattern: &str) -> Result<Matcher, String> {
        match pattern.strip_prefix(REGEX_PREFIX) {
            Some("") => Err("an empty regular expression would match every line".to_owned()),
            Some(expr) => regex::Regex::new(expr)
                .map(Matcher::Regex)
                .map_err(|e| format!("bad regular expression: {e}")),
            None => Ok(Matcher::Literal(pattern.to_owned())),
        }
    }

    /// Whether the line matches; callers hand the line trimmed, so `^` and
    /// `$` anchor to the code and not to its indentation.
    #[must_use]
    pub fn is_match(&self, line: &str) -> bool {
        match self {
            Matcher::Literal(text) => line.contains(text.as_str()),
            Matcher::Regex(re) => re.is_match(line),
        }
    }

    /// Whether nothing can match: an empty text (an empty expression
    /// matches every line, which is a way to list a function).
    #[must_use]
    pub fn matches_nothing(&self) -> bool {
        match self {
            Matcher::Literal(text) => text.is_empty(),
            Matcher::Regex(_) => false,
        }
    }

    /// The verb a header uses: lines `contain` a text, `match` an expression.
    #[must_use]
    pub fn verb(&self) -> &'static str {
        match self {
            Matcher::Literal(_) => "contain",
            Matcher::Regex(_) => "match",
        }
    }

    /// The literal the matcher holds, when it is one.
    ///
    /// # Returns
    ///
    /// The text every matching line contains, or `None` for an
    /// expression, whose matches need not hold any one literal.
    #[must_use]
    pub fn literal(&self) -> Option<&str> {
        match self {
            Matcher::Literal(text) => Some(text),
            Matcher::Regex(_) => None,
        }
    }
}

/// The FNV-1a offset basis: the seed of a fresh hash.
pub const FNV_SEED: u64 = 0xcbf2_9ce4_8422_2325;

/// FNV-1a over a byte string, the hash the key is built from and the
/// hash the answer memory remembers an answer by.
///
/// # Arguments
///
/// * `seed` - The running hash; [`FNV_SEED`] to start.
/// * `bytes` - The bytes to fold in.
#[must_use]
pub fn fnv1a(seed: u64, bytes: &[u8]) -> u64 {
    bytes.iter().fold(seed, |h, b| {
        (h ^ u64::from(*b)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

/// The program half of an index key ([`IndexKey::program`]).
///
/// # Arguments
///
/// * `bytes` - The program's bytes.
///
/// # Returns
///
/// The first eight bytes of their SHA-256, little-endian.
#[must_use]
pub fn program_key(bytes: &[u8]) -> u64 {
    borer_engine::hashing::sha256(bytes)
        .first_chunk::<8>()
        .copied()
        .map_or(0, u64::from_le_bytes)
}

/// Where indexes live: `$BORER_CACHE_DIR`, else the platform cache directory
/// (`%LOCALAPPDATA%\borer\index`, `$XDG_CACHE_HOME/borer/index`,
/// `~/.cache/borer/index`).
///
/// # Returns
///
/// The directory, or `None` when no environment variable names a base.
#[must_use]
pub fn cache_dir() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var(CACHE_ENV)
        && !dir.is_empty()
    {
        return Some(PathBuf::from(dir));
    }
    Some(cache_base()?.join("borer").join("index"))
}

/// The platform cache directory every borer cache hangs from:
/// `%LOCALAPPDATA%`, `$XDG_CACHE_HOME`, else `~/.cache`.
///
/// # Returns
///
/// The directory, or `None` when no environment variable names a base.
#[must_use]
pub fn cache_base() -> Option<PathBuf> {
    std::env::var_os("LOCALAPPDATA")
        .or_else(|| std::env::var_os("XDG_CACHE_HOME"))
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))
}

/// The cache directory, for a call that has to write there.
///
/// # Errors
///
/// When no environment variable names a base ([`cache_dir`]).
fn require_cache_dir() -> Result<PathBuf, String> {
    cache_dir().ok_or_else(|| {
        format!("no cache directory: set {CACHE_ENV}, LOCALAPPDATA, XDG_CACHE_HOME or HOME")
    })
}

/// Decompiles every function of `program` into an index, one stripe per core.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names applied to the text; the default overlay keeps the
///   index valid for every session.
#[must_use]
pub fn build(program: &Program, analysis: &Analysis, overlay: &Overlay) -> CodeIndex {
    let entries: Vec<u64> = analysis.functions.iter().map(|f| f.entry).collect();
    let texts = decompile_named_all(program, analysis, overlay, &entries);
    let functions: Vec<IndexedFunction> = entries
        .iter()
        .zip(texts)
        .map(|(&entry, text)| IndexedFunction {
            entry,
            name: name_of(analysis, overlay, entry),
            text: text.unwrap_or_default(),
        })
        .collect();
    let postings = trigram_postings(&functions);
    CodeIndex {
        key: index_key(program, &analysis.packs),
        functions,
        postings,
    }
}

/// The FNV-1a digest of an index's records, exactly as [`encode`] writes
/// them.
///
/// Per function its entry, then its name and text each behind its
/// length, then the postings, each present trigram by its id, its count
/// and its function indices.
///
/// The header carries it and [`read`] checks it, since a record that still
/// parses after an edit (a changed byte of a text) changed every grep over
/// it, and a cache that answers differently from a fresh build breaks the
/// promise that the same query answers the same. The postings join the
/// digest for the same reason: a listing that skipped a function a
/// tampered posting list dropped would answer less than the build does.
///
/// # Arguments
///
/// * `functions` - The records, in file order.
/// * `postings` - The trigram postings over them.
fn digest(functions: &[IndexedFunction], postings: &Postings) -> u64 {
    let h = functions.iter().fold(FNV_SEED, |h, f| {
        let h = fnv1a(h, &f.entry.to_le_bytes());
        [&f.name, &f.text].iter().fold(h, |h, field| {
            let (len, bytes) = clipped(field);
            fnv1a(fnv1a(h, &len.to_le_bytes()), bytes)
        })
    });
    postings
        .lists
        .iter()
        .enumerate()
        .filter(|(_, list)| !list.is_empty())
        .fold(h, |h, (id, list)| {
            let id = u32::try_from(id).unwrap_or(u32::MAX);
            let len = u32::try_from(list.len()).unwrap_or(u32::MAX);
            let h = fnv1a(h, &id.to_le_bytes());
            let h = fnv1a(h, &len.to_le_bytes());
            list.iter().fold(h, |h, i| fnv1a(h, &i.to_le_bytes()))
        })
}

/// A record field as the file holds it: its length as a `u32` and as many
/// of its bytes as that length counts.
///
/// # Arguments
///
/// * `field` - A function's name or text.
fn clipped(field: &str) -> (u32, &[u8]) {
    let len = u32::try_from(field.len()).unwrap_or(u32::MAX);
    let bytes = field.as_bytes();
    (
        len,
        bytes
            .get(..usize::try_from(len).unwrap_or(usize::MAX))
            .unwrap_or(bytes),
    )
}

/// Serializes an index: the magic, the format, the key's two halves, a
/// count, the records' [`digest`], then the records and the postings.
///
/// Per function its entry and length-prefixed name and text; then the
/// postings: a count of present trigrams, and per trigram its id, a
/// count and the function indices.
///
/// The bytes go straight to `out`: an index is as large as all of a
/// program's pseudo-C, and a copy of it in memory beside the index itself
/// was another hundred megabytes at the peak of a large program's build.
///
/// # Arguments
///
/// * `index` - The index.
/// * `out` - Where the bytes go.
///
/// # Errors
///
/// When `out` refuses a write.
pub fn encode(index: &CodeIndex, out: &mut impl std::io::Write) -> std::io::Result<()> {
    out.write_all(MAGIC)?;
    out.write_all(&FORMAT.to_le_bytes())?;
    out.write_all(&index.key.program.to_le_bytes())?;
    out.write_all(&index.key.engine.to_le_bytes())?;
    out.write_all(
        &u32::try_from(index.functions.len())
            .unwrap_or(u32::MAX)
            .to_le_bytes(),
    )?;
    out.write_all(&digest(&index.functions, &index.postings).to_le_bytes())?;
    for f in &index.functions {
        out.write_all(&f.entry.to_le_bytes())?;
        for field in [&f.name, &f.text] {
            let (len, bytes) = clipped(field);
            out.write_all(&len.to_le_bytes())?;
            out.write_all(bytes)?;
        }
    }
    let present: Vec<usize> = index
        .postings
        .lists
        .iter()
        .enumerate()
        .filter(|(_, list)| !list.is_empty())
        .map(|(id, _)| id)
        .collect();
    out.write_all(
        &u32::try_from(present.len())
            .unwrap_or(u32::MAX)
            .to_le_bytes(),
    )?;
    for id in present {
        let list = &index.postings.lists[id];
        out.write_all(&u32::try_from(id).unwrap_or(u32::MAX).to_le_bytes())?;
        out.write_all(&u32::try_from(list.len()).unwrap_or(u32::MAX).to_le_bytes())?;
        for i in list {
            out.write_all(&i.to_le_bytes())?;
        }
    }
    Ok(())
}

/// A cursor over encoded bytes with bounds-checked reads.
struct Reader<R> {
    /// The bytes.
    input: R,
    /// Bytes not yet read, so no length read from the file asks for more
    /// than the file holds.
    left: u64,
}

impl<R: Read> Reader<R> {
    /// Reads `N` bytes, or `None` past the end.
    fn take<const N: usize>(&mut self) -> Option<[u8; N]> {
        let mut bytes = [0u8; N];
        self.fill(&mut bytes)?;
        Some(bytes)
    }

    /// Fills `buf` from the input, or `None` when it holds fewer bytes.
    ///
    /// # Arguments
    ///
    /// * `buf` - Where the bytes go.
    fn fill(&mut self, buf: &mut [u8]) -> Option<()> {
        self.left = self.left.checked_sub(u64::try_from(buf.len()).ok()?)?;
        self.input.read_exact(buf).ok()
    }

    /// Reads a little-endian `u32`.
    fn u32(&mut self) -> Option<u32> {
        self.take().map(u32::from_le_bytes)
    }

    /// Reads a length-checked sequence of little-endian `u32`s.
    ///
    /// # Arguments
    ///
    /// * `len` - How many values to read.
    fn u32s(&mut self, len: usize) -> Option<Vec<u32>> {
        let mut out = Vec::with_capacity(len.min(1 << 16));
        for _ in 0..len {
            out.push(self.u32()?);
        }
        Some(out)
    }

    /// Reads a little-endian `u64`.
    fn u64(&mut self) -> Option<u64> {
        self.take().map(u64::from_le_bytes)
    }

    /// Reads a length-prefixed UTF-8 string no longer than [`RECORD_MAX`].
    fn string(&mut self) -> Option<String> {
        let len = self.u32()?;
        let size = usize::try_from(len).ok()?;
        if size > RECORD_MAX || u64::from(len) > self.left {
            return None;
        }
        self.left -= u64::from(len);
        let mut bytes = Vec::with_capacity(size);
        (&mut self.input)
            .take(u64::from(len))
            .read_to_end(&mut bytes)
            .ok()?;
        if bytes.len() != size {
            return None;
        }
        String::from_utf8(bytes).ok()
    }
}

/// Parses an index from its encoding as it is read, so the file's bytes are
/// never held whole beside the index they make.
///
/// A record count the file cannot hold [`RECORD_FLOOR`] bytes per record
/// of is refused before anything is allocated for it, and the record
/// vector starts small however large a count claims, so a header alone
/// cannot ask for memory the file never paid for. A posting list that
/// does not name functions in strict ascending order is refused as well:
/// this format never writes one, and the binary search a grep intersects
/// with trusts its order.
///
/// # Arguments
///
/// * `input` - The encoding.
/// * `len` - Its length in bytes.
///
/// # Returns
///
/// The index, or `None` when the bytes are not an index of this format,
/// are cut short or corrupt anywhere, or their records do not hash to the
/// header's [`digest`].
fn read(input: impl Read, len: u64) -> Option<CodeIndex> {
    let mut r = Reader { input, left: len };
    if r.take::<8>()? != *MAGIC || r.u32()? != FORMAT {
        return None;
    }
    let key = IndexKey {
        program: r.u64()?,
        engine: r.u64()?,
    };
    let count = usize::try_from(r.u32()?).ok()?;
    if u64::try_from(count).ok()? > len / RECORD_FLOOR {
        return None;
    }
    let stored = r.u64()?;
    let mut functions = Vec::with_capacity(count.min(1 << 12));
    for _ in 0..count {
        let entry = r.u64()?;
        let name = r.string()?;
        let text = r.string()?;
        functions.push(IndexedFunction { entry, name, text });
    }
    let present = usize::try_from(r.u32()?).ok()?;
    if present > TRIGRAMS {
        return None;
    }
    let mut lists = vec![Vec::<u32>::new(); TRIGRAMS];
    for _ in 0..present {
        let id = usize::try_from(r.u32()?).ok()?;
        let len = usize::try_from(r.u32()?).ok()?;
        if id >= TRIGRAMS || u64::try_from(len).ok()? > r.left {
            return None;
        }
        let list = r.u32s(len)?;
        let lawful = list.windows(2).all(|w| w[0] < w[1])
            && list
                .iter()
                .all(|&i| usize::try_from(i).is_ok_and(|at| at < functions.len()));
        if !lawful {
            return None;
        }
        lists[id] = list;
    }
    let postings = Postings { lists };
    (digest(&functions, &postings) == stored).then_some(CodeIndex {
        key,
        functions,
        postings,
    })
}

/// Parses an index from its encoding.
///
/// # Arguments
///
/// * `bytes` - The file's bytes.
///
/// # Returns
///
/// The index, or `None` when the bytes are not an index of this format or
/// are cut short or corrupt anywhere.
#[must_use]
pub fn decode(bytes: &[u8]) -> Option<CodeIndex> {
    read(bytes, u64::try_from(bytes.len()).ok()?)
}

/// Writes an index to `path`, creating the directory.
///
/// # Arguments
///
/// * `index` - The index.
/// * `path` - The file to write.
///
/// # Errors
///
/// When the directory cannot be created or the file cannot be written.
pub fn save_to(index: &CodeIndex, path: &Path) -> Result<(), String> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).map_err(|e| format!("create {}: {e}", dir.display()))?;
    }
    std::fs::File::create(path)
        .and_then(|file| {
            let mut out = BufWriter::new(file);
            encode(index, &mut out)?;
            out.flush()
        })
        .map_err(|e| format!("write {}: {e}", path.display()))
}

/// Reads an index from `path`.
///
/// # Arguments
///
/// * `path` - The file.
///
/// # Returns
///
/// The index, or `None` when the file is absent, unreadable or not an index.
#[must_use]
pub fn load_from(path: &Path) -> Option<CodeIndex> {
    /// Bytes read from the file at a time.
    const CHUNK: usize = 1 << 20;
    let file = std::fs::File::open(path).ok()?;
    let len = file.metadata().ok()?.len();
    read(BufReader::with_capacity(CHUNK, file), len)
}

/// Reads the index stored under `key` in `dir`, when the file is there and
/// holds that key.
///
/// # Arguments
///
/// * `dir` - The index directory.
/// * `key` - The key wanted.
fn load_in(dir: &Path, key: IndexKey) -> Option<CodeIndex> {
    load_from(&dir.join(key.file_name())).filter(|index| index.key == key)
}

/// Reads the index cached for `program`, without building one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `packs` - The packs its analysis runs with, part of the key.
///
/// # Returns
///
/// The index and its path, or `None` when no cache holds one for this
/// program, engine and packs.
#[must_use]
pub fn load_cached(program: &Program, packs: &Packs) -> Option<(CodeIndex, PathBuf)> {
    let dir = cache_dir()?;
    let key = index_key(program, packs);
    load_in(&dir, key).map(|index| (index, dir.join(key.file_name())))
}

/// Writes an index into `dir` under its key's name, then removes the
/// program's other indexes and holds the directory under `cap` bytes
/// ([`prune`]).
///
/// # Arguments
///
/// * `dir` - The index directory.
/// * `index` - The index.
/// * `cap` - Most bytes the directory keeps.
///
/// # Returns
///
/// The index and the path it was written to.
///
/// # Errors
///
/// When the directory cannot be created or the file cannot be written.
fn save_in(dir: &Path, index: CodeIndex, cap: u64) -> Result<(CodeIndex, PathBuf), String> {
    let name = index.key.file_name();
    let path = dir.join(&name);
    save_to(&index, &path)?;
    prune(dir, &name, index.key.program, cap);
    Ok((index, path))
}

/// Removes what the index directory no longer needs, keeping `kept`.
///
/// Gone first are the other indexes of the same program, which only an
/// older borer or another set of packs could read, and every `.pcidx` file
/// not named `<program>-<engine>`, which an older format wrote and no
/// build reads any more. Then, while the directory holds more than `cap`
/// bytes of indexes, the least recently written goes. A file that cannot
/// be removed (open elsewhere, read-only) stays and is counted: the save
/// that called this has already succeeded and is not undone by a cleanup.
///
/// # Arguments
///
/// * `dir` - The index directory.
/// * `kept` - File name of the index just written, never removed.
/// * `program` - The program half of its key.
/// * `cap` - Most bytes the directory keeps.
fn prune(dir: &Path, kept: &str, program: u64, cap: u64) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let same_program = format!("{program:016x}-");
    let mut total = 0u64;
    let mut others: Vec<(SystemTime, u64, PathBuf)> = Vec::new();
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            continue;
        };
        let Some(stem) = name
            .strip_suffix(EXTENSION)
            .and_then(|n| n.strip_suffix('.'))
        else {
            continue;
        };
        let Some(meta) = entry.metadata().ok().filter(std::fs::Metadata::is_file) else {
            continue;
        };
        let path = entry.path();
        if name == kept {
            total += meta.len();
            continue;
        }
        let stale = stem.starts_with(&same_program) || !is_key_name(stem);
        if stale && std::fs::remove_file(&path).is_ok() {
            continue;
        }
        total += meta.len();
        others.push((meta.modified().unwrap_or(UNIX_EPOCH), meta.len(), path));
    }
    others.sort();
    for (_, len, path) in others {
        if total <= cap {
            break;
        }
        if std::fs::remove_file(&path).is_ok() {
            total -= len;
        }
    }
}

/// Reads the index for `program` from `dir`, or builds and stores it there
/// when none holds this program, borer build and set of packs.
///
/// # Arguments
///
/// * `dir` - The index directory.
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `cap` - Most bytes the directory keeps after a build.
///
/// # Returns
///
/// The index, its path, and whether it was built by this call.
///
/// # Errors
///
/// When the index had to be built and the file cannot be written.
fn load_or_build_in(
    dir: &Path,
    program: &Program,
    analysis: &Analysis,
    cap: u64,
) -> Result<(CodeIndex, PathBuf, bool), String> {
    let key = index_key(program, &analysis.packs);
    if let Some(index) = load_in(dir, key) {
        return Ok((index, dir.join(key.file_name()), false));
    }
    let (index, path) = save_in(dir, build(program, analysis, &Overlay::default()), cap)?;
    Ok((index, path, true))
}

/// Reads the index for `program` from the cache, or builds and stores it
/// when none holds this program, borer build and set of packs.
///
/// Decompiling a large program takes minutes and reading its index a
/// moment, so every reader of the index comes here.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
///
/// # Returns
///
/// The index, the path it is stored at, and whether this call built it
/// (`false` when it was read from the cache).
///
/// # Errors
///
/// When no cache directory can be named, or the index had to be built and
/// the file cannot be written.
pub fn load_or_build(
    program: &Program,
    analysis: &Analysis,
) -> Result<(CodeIndex, PathBuf, bool), String> {
    load_or_build_in(&require_cache_dir()?, program, analysis, CACHE_MAX)
}

/// Finds every pseudo-C line `matcher` accepts, in entry then line order.
///
/// A literal query is prefetched through the postings: the functions whose
/// folded texts hold every trigram of the literal's runs are the only ones
/// whose lines are scanned, and they are scanned in stripes. An
/// expression, or a literal too short to spell a trigram, scans every
/// function the name filter leaves.
///
/// A function whose statements hit loses its declaration-line hits
/// ([`function_hits`]).
///
/// # Arguments
///
/// * `index` - The index to scan.
/// * `matcher` - The text or expression a line must hold.
/// * `function_filter` - Case-insensitive substring of the function name;
///   empty for every function.
///
/// # Returns
///
/// The matching lines, every one of them; callers page.
#[must_use]
pub fn grep(index: &CodeIndex, matcher: &Matcher, function_filter: &str) -> Vec<GrepHit> {
    if matcher.matches_nothing() {
        return Vec::new();
    }
    let q = function_filter.to_lowercase();
    let scope = matcher.literal().and_then(|lit| literal_scope(index, lit));
    index
        .functions
        .par_iter()
        .enumerate()
        .filter(|(i, f)| {
            (q.is_empty() || f.name.to_lowercase().contains(&q))
                && scope.as_ref().is_none_or(|m| m[*i])
        })
        .map(|(_, f)| function_hits(f, matcher))
        .collect::<Vec<Vec<GrepHit>>>()
        .into_iter()
        .flatten()
        .collect()
}

/// The lines of one function `matcher` accepts, less its declaration lines
/// when a statement hits too.
///
/// A function whose statements hit loses its declaration-line hits: the
/// line declaring every local names each of them, and repeated it in every
/// answer for a `local_N`. A hit only the declarations hold stays.
///
/// # Arguments
///
/// * `f` - The function.
/// * `matcher` - The text or expression a line must hold.
///
/// # Returns
///
/// The kept lines, in line order.
fn function_hits(f: &IndexedFunction, matcher: &Matcher) -> Vec<GrepHit> {
    let mut hits: Vec<GrepHit> = f
        .text
        .lines()
        .enumerate()
        .filter(|(_, line)| matcher.is_match(line.trim()))
        .map(|(i, line)| GrepHit {
            entry: f.entry,
            name: f.name.clone(),
            line_no: i + 1,
            line: line.trim().to_owned(),
        })
        .collect();
    if let Some(end) = borer_engine::analysis::decompile::declarations_end(&f.text) {
        let declares = |h: &GrepHit| h.line_no <= end && !h.line.starts_with("//");
        if hits.iter().any(|h| !declares(h)) {
            hits.retain(|h| !declares(h));
        }
    }
    hits
}

/// Which functions a literal can hit, as one membership bit per function.
///
/// The scope is the intersection of the literal's trigrams' posting
/// lists, tested list by list against the marks the shortest list set: a
/// function stays marked only while every list so far holds it. The
/// shortest list first is what keeps the marking pass narrow.
///
/// # Arguments
///
/// * `index` - The index whose postings are intersected.
/// * `literal` - The text every matching line contains.
///
/// # Returns
///
/// The membership bits, or `None` when the literal spells no trigram and
/// nothing can be ruled out.
fn literal_scope(index: &CodeIndex, literal: &str) -> Option<Vec<bool>> {
    let mut needed = trigram_ids(literal);
    needed.sort_unstable();
    needed.dedup();
    if needed.is_empty() {
        return None;
    }
    needed.sort_by_key(|id| index.postings.lists.get(*id).map_or(usize::MAX, Vec::len));
    let mut scope = vec![false; index.functions.len()];
    for &i in index.postings.lists.get(needed[0]).into_iter().flatten() {
        if let Ok(at) = usize::try_from(i)
            && let Some(mark) = scope.get_mut(at)
        {
            *mark = true;
        }
    }
    for id in &needed[1..] {
        let list = index.postings.lists.get(*id)?;
        for (i, mark) in scope.iter_mut().enumerate() {
            let idx = u32::try_from(i).unwrap_or(u32::MAX);
            if *mark && list.binary_search(&idx).is_err() {
                *mark = false;
            }
        }
    }
    Some(scope)
}

/// Renders a grep as a `#`-headed table, paged, with names from the overlay.
///
/// The hits of one function come with the `if`/`else`/loop/`switch`/`case`
/// headers enclosing them, read from the function's whole text in the index
/// ([`render::scope_headers`]): each header once, in line order before the
/// hits it encloses, its line numbered `^N` so it reads as context and not
/// as a match. A function's rows keep their indentation relative to its
/// least indented row, so the nesting shows. Most pseudo-C lines run only
/// under a condition the line does not carry, and a bare hit states it as
/// unconditional.
///
/// # Arguments
///
/// * `index` - The index scanned.
/// * `analysis` - For the names in force.
/// * `overlay` - Names in force; a renamed function shows its new name.
/// * `pattern` - The text matched, or `re:` and an expression.
/// * `function_filter` - The function-name filter applied.
/// * `window` - The hits shown, and the URI naming the next page.
///
/// # Errors
///
/// When the pattern opens an expression that does not parse.
pub fn grep_tsv(
    index: &CodeIndex,
    analysis: &Analysis,
    overlay: &Overlay,
    pattern: &str,
    function_filter: &str,
    window: Window<'_>,
) -> Result<String, String> {
    let Window { skip, limit, .. } = window;
    let matcher = Matcher::parse(pattern)?;
    let hits = grep(index, &matcher, function_filter);
    let functions = {
        let mut entries: Vec<u64> = hits.iter().map(|h| h.entry).collect();
        entries.dedup();
        entries.len()
    };
    let total = hits.len();
    let shown = total.saturating_sub(skip).min(limit);
    let mut body = String::new();
    let mut any_context = false;
    let page: Vec<GrepHit> = hits.into_iter().skip(skip).take(limit).collect();
    for group in page.chunk_by(|x, y| x.entry == y.entry) {
        let Some(entry) = group.first().map(|h| h.entry) else {
            continue;
        };
        let name = name_of(analysis, overlay, entry);
        let Some(f) = index
            .functions
            .binary_search_by_key(&entry, |f| f.entry)
            .ok()
            .and_then(|at| index.functions.get(at))
        else {
            for h in group {
                let _ = writeln!(body, "{entry:#x}\t{name}\t{}\t{}", h.line_no, h.line);
            }
            continue;
        };
        let lines: Vec<&str> = f.text.lines().collect();
        let picked: Vec<usize> = group.iter().map(|h| h.line_no.saturating_sub(1)).collect();
        let context = render::scope_headers(&lines, &picked);
        any_context |= !context.is_empty();
        let mut rows = picked;
        rows.extend(&context);
        rows.sort_unstable();
        let indent = |l: &str| l.len() - l.trim_start_matches(' ').len();
        let least = rows.iter().map(|&i| indent(lines[i])).min().unwrap_or(0);
        for i in rows {
            let mark = if context.contains(&i) { "^" } else { "" };
            let text = lines[i].get(least..).unwrap_or(lines[i]).trim_end();
            let _ = writeln!(body, "{entry:#x}\t{name}\t{mark}{}\t{text}", i + 1);
        }
    }
    let mut out = format!(
        "# {total} lines in {functions} functions {} {}, showing {shown} from {skip}{}\n",
        matcher.verb(),
        borer_engine::text::quoted(pattern),
        if any_context { render::SCOPE_NOTE } else { "" }
    );
    out.push_str("entry\tfunction\tline\ttext\n");
    out.push_str(&body);
    out.push_str(&window.next_page(total, shown));
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The program half of an index key is SHA-256, not a hash a file can
    /// be built to collide with.
    ///
    /// # Panics
    ///
    /// When the key is not the digest's first eight bytes.
    #[test]
    fn the_program_key_is_sha256() {
        assert_eq!(program_key(b"abc"), 0xeacf_018f_bf16_78ba);
        assert_ne!(program_key(b"abc"), fnv1a(FNV_SEED, b"abc"));
    }

    /// A two-function index with a shared line and a distinct one.
    fn sample() -> CodeIndex {
        let functions = vec![
            IndexedFunction {
                entry: 0x1000,
                name: "Game::Send".to_owned(),
                text: "// signature: void Game::Send(void)\nAppendCommand(cmd, 1);\nreturn;\n"
                    .to_owned(),
            },
            IndexedFunction {
                entry: 0x2000,
                name: "sub_2000".to_owned(),
                text: "x = AppendCommand(cmd, 0);\n  return x;\n".to_owned(),
            },
        ];
        CodeIndex {
            key: IndexKey {
                program: 7,
                engine: 9,
            },
            postings: trigram_postings(&functions),
            functions,
        }
    }

    /// The trigram prefilter keeps every hit a full scan finds.
    ///
    /// Across case folds, separator-split runs and texts too short to
    /// spell a trigram, and it rules out functions whose folded text
    /// cannot hold the literal.
    ///
    /// # Panics
    ///
    /// When the prefilled grep disagrees with a scan of every line.
    #[test]
    fn the_trigram_prefilter_answers_what_a_full_scan_answers() {
        let functions = vec![
            IndexedFunction {
                entry: 0x1000,
                name: "a".to_owned(),
                text: "memcpy(dst, src, n);\nreturn 0x20;\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x2000,
                name: "b".to_owned(),
                text: "MEMCPY(dst, src, n);\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x3000,
                name: "c".to_owned(),
                text: "x = 1;\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x4000,
                name: "d".to_owned(),
                text: String::new(),
            },
        ];
        let index = CodeIndex {
            key: IndexKey {
                program: 1,
                engine: 2,
            },
            postings: trigram_postings(&functions),
            functions,
        };
        for lit in ["memcpy", "MEMCPY", "MeMcPy", "dst,", "0x20", "x = 1", "= 1"] {
            let matcher = Matcher::parse(lit).expect("a literal parses");
            let brute: Vec<(u64, usize)> = index
                .functions
                .iter()
                .flat_map(|f| {
                    f.text.lines().enumerate().filter_map(|(i, line)| {
                        matcher.is_match(line.trim()).then_some((f.entry, i + 1))
                    })
                })
                .collect();
            let hits: Vec<(u64, usize)> = grep(&index, &matcher, "")
                .iter()
                .map(|h| (h.entry, h.line_no))
                .collect();
            assert_eq!(hits, brute, "{lit:?}");
        }
        let scope = literal_scope(&index, "memcpy").expect("the literal spells trigrams");
        assert_eq!(scope, vec![true, true, false, false]);
        assert!(
            literal_scope(&index, "= 1").is_none(),
            "a literal without a three-symbol run rules nothing out"
        );
    }

    /// The encoding reads back equal, and a truncated or foreign file is
    /// refused rather than read as an empty index.
    ///
    /// # Panics
    ///
    /// When a decoding disagrees with the index it was encoded from.
    #[test]
    fn encoding_round_trips_and_refuses_garbage() {
        let index = sample();
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        assert_eq!(decode(&bytes), Some(index.clone()));
        assert_eq!(
            decode(&bytes[..bytes.len() - 3]),
            None,
            "a cut file is not an index"
        );
        assert_eq!(decode(b"MZ\x90\x00"), None, "a program is not an index");
        let mut wrong = bytes;
        wrong[8] ^= 1;
        assert_eq!(decode(&wrong), None, "another format version is not read");
        let dir = std::env::temp_dir().join(format!("borer_index_test_{}", std::process::id()));
        let path = dir.join("t.pcidx");
        save_to(&index, &path).expect("writes");
        assert_eq!(load_from(&path), Some(index));
        std::fs::remove_dir_all(&dir).expect("cleans up");
    }

    /// An index whose text was edited still parses, so the header's digest
    /// is what refuses it, and the cache reads it as absent, which rebuilds
    /// it: an edited cache answered a grep the program does not hold.
    ///
    /// # Panics
    ///
    /// When the edited file is read, or the edit does not land in a text.
    #[test]
    fn an_edited_record_is_refused_so_the_index_is_rebuilt() {
        let index = sample();
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        let at = bytes
            .windows(13)
            .position(|w| w == b"AppendCommand")
            .expect("a text is in the file");
        bytes[at] = b'X';
        assert_eq!(decode(&bytes), None, "an edited text is not read");
        let dir = scratch("edited_index");
        std::fs::write(dir.join(index.key.file_name()), &bytes).expect("writes");
        assert_eq!(load_in(&dir, index.key), None, "the cache rebuilds it");
        std::fs::remove_dir_all(&dir).expect("cleans up");
    }

    /// A fresh directory under the system temp directory for one test.
    ///
    /// # Arguments
    ///
    /// * `name` - The test's name, so parallel tests do not share one.
    ///
    /// # Panics
    ///
    /// When the directory cannot be cleared or created.
    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("borer_{name}_{}", std::process::id()));
        if dir.exists() {
            std::fs::remove_dir_all(&dir).expect("clears the last run");
        }
        std::fs::create_dir_all(&dir).expect("creates");
        dir
    }

    /// The first call builds the index, the second reads it.
    ///
    /// The build stores it under `<program>-<engine>.pcidx` and removes the
    /// program's index of another build; an index of another program is
    /// left alone.
    ///
    /// # Panics
    ///
    /// When the second call builds, the stale index survives, or another
    /// program's index is removed.
    #[test]
    fn load_or_build_builds_once_and_replaces_the_programs_stale_index() {
        use borer_engine::program::{Arch, Section};
        let dir = scratch("load_or_build");
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let analysis = Analysis::default();
        let key = index_key(&program, &analysis.packs);
        let stale = dir.join(
            IndexKey {
                engine: key.engine ^ 1,
                ..key
            }
            .file_name(),
        );
        let foreign = dir.join(
            IndexKey {
                program: key.program ^ 1,
                ..key
            }
            .file_name(),
        );
        for path in [&stale, &foreign] {
            std::fs::write(path, b"BORERIDX").expect("writes");
        }

        let (built, path, fresh) =
            load_or_build_in(&dir, &program, &analysis, CACHE_MAX).expect("builds");
        assert!(fresh, "nothing was cached");
        assert_eq!(path, dir.join(key.file_name()));
        assert_eq!(built.key, key);
        assert!(
            !stale.exists(),
            "the program's index of another build is gone"
        );
        assert!(foreign.exists(), "another program's index stays");

        let (read, again, rebuilt) =
            load_or_build_in(&dir, &program, &analysis, CACHE_MAX).expect("reads");
        assert!(!rebuilt, "the second call reads the cache");
        assert_eq!((read, again), (built, path));
        std::fs::remove_dir_all(&dir).expect("cleans up");
    }

    /// Pruning holds the index directory under its cap, oldest first.
    ///
    /// It removes the kept index's siblings and files of the older
    /// single-key name, then the least recently written indexes until the
    /// directory fits; the kept index and files that are not indexes are
    /// never touched.
    ///
    /// # Panics
    ///
    /// When a file survives that should go, or one goes that should stay.
    #[test]
    fn pruning_holds_the_directory_under_the_cap_oldest_first() {
        let dir = scratch("prune");
        let name = |program: u64, engine: u64| IndexKey { program, engine }.file_name();
        let kept = name(1, 2);
        let old = SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000);
        let files = [
            (kept.clone(), 10, 3),
            (name(1, 1), 10, 2),
            ("00000000deadbeef.pcidx".to_owned(), 10, 2),
            (name(3, 1), 40, 0),
            (name(4, 1), 40, 1),
            ("notes.txt".to_owned(), 500, 0),
        ];
        for (file, len, age) in &files {
            let path = dir.join(file);
            std::fs::write(&path, vec![0u8; *len]).expect("writes");
            std::fs::OpenOptions::new()
                .write(true)
                .open(&path)
                .and_then(|f| f.set_modified(old + std::time::Duration::from_secs(*age)))
                .expect("dates");
        }
        prune(&dir, &kept, 1, 60);
        let mut left: Vec<String> = std::fs::read_dir(&dir)
            .expect("lists")
            .map(|e| e.expect("entry").file_name().to_string_lossy().into_owned())
            .collect();
        left.sort();
        assert_eq!(left, vec![kept, name(4, 1), "notes.txt".to_owned()]);
        std::fs::remove_dir_all(&dir).expect("cleans up");
    }

    /// A grep finds every line with the text, in entry then line order,
    /// honours the function filter, and pages.
    ///
    /// # Panics
    ///
    /// When a hit disagrees with the sample.
    #[test]
    fn grep_finds_lines_filters_and_pages() {
        let index = sample();
        let literal = |text: &str| Matcher::parse(text).expect("a text always parses");
        let hits = grep(&index, &literal("AppendCommand(cmd, "), "");
        let shape: Vec<(u64, usize, &str)> = hits
            .iter()
            .map(|h| (h.entry, h.line_no, h.line.as_str()))
            .collect();
        assert_eq!(
            shape,
            vec![
                (0x1000, 2, "AppendCommand(cmd, 1);"),
                (0x2000, 1, "x = AppendCommand(cmd, 0);"),
            ]
        );
        assert_eq!(grep(&index, &literal("return"), "game::").len(), 1);
        assert!(
            grep(&index, &literal(""), "").is_empty(),
            "an empty pattern matches nothing"
        );
        let a = Analysis::default();
        let text = grep_tsv(
            &index,
            &a,
            &Overlay::default(),
            "return",
            "",
            Window {
                skip: 1,
                limit: 5,
                again: None,
            },
        )
        .expect("parses");
        assert!(
            text.starts_with("# 2 lines in 2 functions contain 'return', showing 1 from 1\n"),
            "{text}"
        );
        assert!(text.contains("0x2000\tsub_2000\t2\treturn x;\n"), "{text}");
    }

    /// A grep leaves out a function's declaration line when its statements
    /// also hit, and keeps a hit only the declarations hold.
    ///
    /// # Panics
    ///
    /// When the declaration line comes back beside statement hits, or a
    /// declaration-only hit is lost.
    #[test]
    fn grep_leaves_out_declarations_beside_statement_hits() {
        let functions = vec![IndexedFunction {
            entry: 0x1000,
            name: "f".to_owned(),
            text: "// f @ 0x1000\nuint64_t rax, local_58, local_60;\nchar *p;\n\nlocal_58 = 1;\n"
                .to_owned(),
        }];
        let index = CodeIndex {
            key: IndexKey {
                program: 7,
                engine: 9,
            },
            postings: trigram_postings(&functions),
            functions,
        };
        let literal = |text: &str| Matcher::parse(text).expect("a text always parses");
        assert_eq!(
            grep_shape(&index, &literal("local_58"), ""),
            vec![(0x1000, 5, "local_58 = 1;".to_owned())]
        );
        assert_eq!(
            grep_shape(&index, &literal("local_60"), ""),
            vec![(0x1000, 2, "uint64_t rax, local_58, local_60;".to_owned())]
        );
    }

    /// A hit inside a scope comes with the headers enclosing it.
    ///
    /// They are read from its function's whole text: numbered `^N`, each
    /// once for all the hits of its function, an `else` with its `if`,
    /// indented as in the text; a page holding only a nested hit still gets
    /// them.
    ///
    /// # Panics
    ///
    /// When a header is missing, repeated, numbered as a hit, or the
    /// header line does not say what `^N` means.
    #[test]
    fn a_grep_hit_comes_with_the_headers_enclosing_it() {
        let functions = vec![IndexedFunction {
            entry: 0x1000,
            name: "f".to_owned(),
            text: "// f @ 0x1000\n\nif (a1 != 0) {\n  while (rax) {\n    Send(a1);\n    Send(a2);\n  }\n} else {\n  Send(0);\n}\nSend(9);\n".to_owned(),
        }];
        let index = CodeIndex {
            key: IndexKey {
                program: 7,
                engine: 9,
            },
            postings: trigram_postings(&functions),
            functions,
        };
        let (a, o) = (Analysis::default(), Overlay::default());
        let note = render::SCOPE_NOTE;
        let rows = "entry\tfunction\tline\ttext\n";
        assert_eq!(
            grep_tsv(
                &index,
                &a,
                &o,
                "Send(",
                "",
                Window {
                    skip: 0,
                    limit: 10,
                    again: None
                }
            )
            .expect("parses"),
            format!(
                "# 4 lines in 1 functions contain 'Send(', showing 4 from 0{note}\n{rows}\
                 0x1000\tsub_1000\t^3\tif (a1 != 0) {{\n\
                 0x1000\tsub_1000\t^4\t  while (rax) {{\n\
                 0x1000\tsub_1000\t5\t    Send(a1);\n\
                 0x1000\tsub_1000\t6\t    Send(a2);\n\
                 0x1000\tsub_1000\t^8\t}} else {{\n\
                 0x1000\tsub_1000\t9\t  Send(0);\n\
                 0x1000\tsub_1000\t11\tSend(9);\n"
            )
        );
        assert_eq!(
            grep_tsv(
                &index,
                &a,
                &o,
                "Send(",
                "",
                Window {
                    skip: 2,
                    limit: 1,
                    again: None
                }
            )
            .expect("parses"),
            format!(
                "# 4 lines in 1 functions contain 'Send(', showing 1 from 2{note}\n{rows}\
                 0x1000\tsub_1000\t^3\tif (a1 != 0) {{\n\
                 0x1000\tsub_1000\t^8\t}} else {{\n\
                 0x1000\tsub_1000\t9\t  Send(0);\n"
            )
        );
    }

    /// `re:` opens an expression: it matches by pattern and case flag, an
    /// empty one lists every line, and a broken one is refused with the
    /// parser's message.
    ///
    /// # Panics
    ///
    /// When a hit disagrees with the sample.
    #[test]
    fn grep_takes_regular_expressions() {
        let index = sample();
        let re = Matcher::parse(r"re:AppendCommand\(cmd, [01]\);").expect("parses");
        assert_eq!(grep(&index, &re, "").len(), 2);
        let ci = Matcher::parse("re:(?i)appendcommand").expect("parses");
        assert_eq!(grep(&index, &ci, "").len(), 2);
        let empty = Matcher::parse("re:").expect_err("refused");
        assert!(empty.contains("empty regular expression"), "{empty}");
        let err = Matcher::parse("re:[").expect_err("refused");
        assert!(err.starts_with("bad regular expression: "), "{err}");
        let a = Analysis::default();
        let text = grep_tsv(
            &index,
            &a,
            &Overlay::default(),
            "re:^return",
            "",
            Window {
                skip: 0,
                limit: 5,
                again: None,
            },
        )
        .expect("parses");
        assert!(
            text.starts_with("# 2 lines in 2 functions match 're:^return', showing 2 from 0\n"),
            "{text}"
        );
    }

    /// Every line `matcher` accepts, with no prefilter.
    ///
    /// Entry then line order, the name filter applied and each function's
    /// hits kept as [`function_hits`] keeps them: the answer a scan of
    /// every function owes.
    ///
    /// # Arguments
    ///
    /// * `index` - The index whose texts are scanned.
    /// * `matcher` - What a line must hold.
    /// * `filter` - The function-name filter, as [`grep`] takes it.
    fn brute_hits(index: &CodeIndex, matcher: &Matcher, filter: &str) -> Vec<(u64, usize, String)> {
        let q = filter.to_lowercase();
        index
            .functions
            .iter()
            .filter(|f| q.is_empty() || f.name.to_lowercase().contains(&q))
            .flat_map(|f| function_hits(f, matcher))
            .map(|h| (h.entry, h.line_no, h.line))
            .collect()
    }

    /// What [`grep`] answered, as triples a brute scan can be compared with.
    ///
    /// # Arguments
    ///
    /// * `index` - The index scanned.
    /// * `matcher` - What a line must hold.
    /// * `filter` - The function-name filter.
    fn grep_shape(index: &CodeIndex, matcher: &Matcher, filter: &str) -> Vec<(u64, usize, String)> {
        grep(index, matcher, filter)
            .into_iter()
            .map(|h| (h.entry, h.line_no, h.line))
            .collect()
    }

    /// A deterministic xorshift word generator: the corpus and its queries
    /// come out the same on every run, which is what makes a failure
    /// reproducible.
    #[derive(Debug)]
    struct Rng(u64);

    impl Rng {
        /// Steps the generator and returns the next word.
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        /// A word below `n`.
        ///
        /// # Panics
        ///
        /// When `n` is zero.
        fn below(&mut self, n: usize) -> usize {
            usize::try_from(self.next() % u64::try_from(n).expect("n is not zero"))
                .expect("the word is below n")
        }

        /// One of `items`, evenly enough for a corpus.
        ///
        /// # Panics
        ///
        /// When `items` is empty.
        fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
            &items[self.below(items.len())]
        }
    }

    /// Words the corpus splices into its lines: mixed case, digits and
    /// underscores, so folded trigrams and case-sensitive scans disagree.
    const WORDS: &[&str] = &[
        "Game",
        "GAME",
        "game",
        "Send",
        "sendCmd",
        "MEMCPY",
        "memcpy",
        "dst_buf",
        "SrcPtr",
        "x2",
        "n0",
        "var_1c",
        "qword_140001000",
        "rax",
        "AppendCommand",
        "cmd_queue_2",
        "a1",
        "bB",
        "C_c",
        "d_4e",
        "loop_3x",
        "Ctx",
        "hEvent",
        "dwFlags",
        "lpBuffers",
        "Zz_9",
        "if",
        "return",
        "else",
        "while",
        "NULL",
    ];

    /// What the corpus joins words with, most of it outside the identifier
    /// alphabet so runs break, and some of it spelling trigramless queries.
    const GLUE: &[&str] = &[
        " = ", ", ", "(", ")", " == ", "!=", " + ", " ^ ", "->", ".", "== 0x", "--", " << ", " ? ",
        ":=", "; ",
    ];

    /// Decorations from outside the identifier alphabet, including
    /// multi-byte characters a query may still hold.
    const NOISE: &[&str] = &[
        ";;",
        "}}",
        "===",
        "/* café */",
        "// 参照",
        "\u{1f600}",
        "~~~",
    ];

    /// The seeded corpus the soundness queries run over: forty functions of
    /// two hundred pseudo-C-ish lines each, mixed case, digits, underscores
    /// and punctuation.
    fn corpus() -> CodeIndex {
        let mut rng = Rng(0x5eed_c0de_1234_5678);
        let functions = (0u64..40)
            .map(|i| {
                let mut text = String::new();
                for _ in 0..200 {
                    if rng.below(9) == 0 {
                        text.push('\n');
                        continue;
                    }
                    for w in 0..1 + rng.below(6) {
                        if w > 0 {
                            text.push_str(rng.pick(GLUE));
                        }
                        text.push_str(rng.pick(WORDS));
                    }
                    match rng.below(6) {
                        0 => text.push_str(rng.pick(NOISE)),
                        1 => {
                            text.push_str(rng.pick(GLUE));
                            text.push_str(rng.pick(WORDS));
                        }
                        _ => text.push(';'),
                    }
                    text.push('\n');
                }
                IndexedFunction {
                    entry: 0x1000 + 0x100 * i,
                    name: format!("{}_{i:02x}", rng.pick(WORDS)),
                    text,
                }
            })
            .collect::<Vec<_>>();
        CodeIndex {
            key: IndexKey {
                program: 0x5eed,
                engine: 0xc0de,
            },
            postings: trigram_postings(&functions),
            functions,
        }
    }

    /// `n` random substrings of the corpus's own lines, char-aligned so
    /// they are texts a line can hold.
    ///
    /// # Arguments
    ///
    /// * `rng` - The generator, so the queries are deterministic.
    /// * `index` - The corpus to draw from.
    /// * `n` - How many queries.
    ///
    /// # Panics
    ///
    /// When a picked line holds no characters.
    fn random_queries(rng: &mut Rng, index: &CodeIndex, n: usize) -> Vec<String> {
        (0..n)
            .map(|_| {
                let f = rng.pick(&index.functions);
                let lines: Vec<&str> = f.text.lines().filter(|l| !l.is_empty()).collect();
                let line = rng.pick(&lines);
                let chars: Vec<char> = line.chars().collect();
                let start = rng.below(chars.len());
                let len = 1 + rng.below(12.min(chars.len() - start));
                chars[start..start + len].iter().collect()
            })
            .collect()
    }

    /// The trigram prefilter answers exactly what a full scan answers, on a
    /// seeded corpus, for random substrings of its own texts, their
    /// case-folded variants, and fixed trigramless queries.
    ///
    /// # Panics
    ///
    /// When the prefetched grep disagrees with a scan of every line, or
    /// the corpus does not round-trip through its encoding.
    #[test]
    fn the_prefilter_agrees_with_a_full_scan_on_a_seeded_corpus() {
        let index = corpus();
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        assert_eq!(
            decode(&bytes),
            Some(index.clone()),
            "the corpus round trips"
        );
        let mut rng = Rng(0xfeed_face_2468_ace0);
        let mut queries: Vec<String> = Vec::new();
        for q in random_queries(&mut rng, &index, 60) {
            queries.push(q.to_lowercase());
            queries.push(q.to_uppercase());
            queries.push(q);
        }
        queries.extend(
            [
                "a",
                "ab",
                "z9",
                "--",
                "== 0x",
                "_",
                ";;",
                "}",
                "A",
                "0x",
                "MEMCPY",
                "memcpy",
                "if",
                "IF",
                "café",
                "参照",
                "\u{1f600}",
                "===",
                "dst_buf",
                "DstBuf",
            ]
            .map(str::to_owned),
        );
        for q in &queries {
            let matcher = Matcher::parse(q).expect("a literal parses");
            assert_eq!(
                grep_shape(&index, &matcher, ""),
                brute_hits(&index, &matcher, ""),
                "{q:?}"
            );
        }
    }

    /// `re:` queries ask nothing of the postings and scan every function,
    /// answering exactly what a full scan answers on the same corpus.
    ///
    /// # Panics
    ///
    /// When an expression scan disagrees with a scan of every line.
    #[test]
    fn regular_expression_queries_agree_with_a_full_scan() {
        let index = corpus();
        for pattern in [
            "re:^if",
            "re:return;$",
            "re:(?i)game",
            "re:[0-9a-f]{6}",
            r"re:\w+_\d",
            "re:== 0x[0-9a-f]+",
            "re:(?i)(send|memcpy)",
            r"re:\)",
            "re:x2",
            "re:;",
        ] {
            let matcher = Matcher::parse(pattern).expect("parses");
            assert_eq!(
                grep_shape(&index, &matcher, ""),
                brute_hits(&index, &matcher, ""),
                "{pattern}"
            );
        }
    }

    /// The function filter narrows the prefetched scan to exactly the
    /// functions a brute-force scan of the same names would keep.
    ///
    /// # Panics
    ///
    /// When a filtered grep disagrees with a scan of every line.
    #[test]
    fn the_function_filter_agrees_with_a_full_scan_under_the_prefilter() {
        let index = corpus();
        let mut rng = Rng(0x0d00_dbee_f135_79bd);
        for q in random_queries(&mut rng, &index, 12) {
            let matcher = Matcher::parse(&q).expect("a literal parses");
            for filter in ["", "game", "SEND", "_", "zz", "memcpy", "0f", "a1"] {
                assert_eq!(
                    grep_shape(&index, &matcher, filter),
                    brute_hits(&index, &matcher, filter),
                    "{q:?} over names holding {filter:?}"
                );
            }
        }
    }

    /// Trigramless texts round trip and still answer a grep.
    ///
    /// Empty texts, punctuation-only ones, one or two identifier
    /// characters, multi-byte and duplicated: the queries that cannot
    /// rule anything out still find what a full scan finds.
    ///
    /// # Panics
    ///
    /// When the round trip loses a record or a grep disagrees with a scan
    /// of every line.
    #[test]
    fn trigramless_texts_round_trip_and_still_answer() {
        let functions = vec![
            IndexedFunction {
                entry: 0x1000,
                name: "empty".to_owned(),
                text: String::new(),
            },
            IndexedFunction {
                entry: 0x2000,
                name: "punct".to_owned(),
                text: ";;;}}}===\n--\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x3000,
                name: "one".to_owned(),
                text: "a\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x4000,
                name: "two".to_owned(),
                text: "ab\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x5000,
                name: "under".to_owned(),
                text: "_\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x6000,
                name: "uni".to_owned(),
                text: "café = 参照;\nif (héllo) {\n  return \u{1f600};\n}\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x7000,
                name: "dup1".to_owned(),
                text: "dup(x);\ndup(x);\n".to_owned(),
            },
            IndexedFunction {
                entry: 0x8000,
                name: "dup2".to_owned(),
                text: "dup(x);\ndup(x);\n".to_owned(),
            },
        ];
        let index = CodeIndex {
            key: IndexKey {
                program: 5,
                engine: 6,
            },
            postings: trigram_postings(&functions),
            functions,
        };
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        assert_eq!(
            decode(&bytes),
            Some(index.clone()),
            "every shape round trips"
        );
        for q in [
            "a",
            "ab",
            "_",
            ";;;",
            "===",
            "--",
            "dup(x)",
            "café",
            "参照",
            "\u{1f600}",
            "héllo",
            "}",
            "x",
        ] {
            let matcher = Matcher::parse(q).expect("a literal parses");
            assert_eq!(
                grep_shape(&index, &matcher, ""),
                brute_hits(&index, &matcher, ""),
                "{q:?}"
            );
        }
    }

    /// A megabyte of one word is one line, one trigram and a million
    /// repetitions of it: it round trips, and the prefilter still answers
    /// what a full scan answers for it.
    ///
    /// # Panics
    ///
    /// When the round trip loses the text or a grep disagrees with a scan
    /// of every line.
    #[test]
    fn a_megabyte_run_round_trips() {
        let functions = vec![IndexedFunction {
            entry: 0x1000,
            name: "long".to_owned(),
            text: "a".repeat(1 << 20),
        }];
        let index = CodeIndex {
            key: IndexKey {
                program: 8,
                engine: 9,
            },
            postings: trigram_postings(&functions),
            functions,
        };
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        assert_eq!(decode(&bytes), Some(index.clone()));
        for q in ["a", "aa", "aaaa", "aaaaaaaa", "ab", "b", "aaaab"] {
            let matcher = Matcher::parse(q).expect("a literal parses");
            assert_eq!(
                grep_shape(&index, &matcher, ""),
                brute_hits(&index, &matcher, ""),
                "{q:?}"
            );
        }
    }

    /// An index of no functions encodes, decodes back equal and greps
    /// nothing, with or without a filter.
    ///
    /// # Panics
    ///
    /// When the empty index does not round trip or a grep answers.
    #[test]
    fn an_empty_index_round_trips_and_finds_nothing() {
        let index = CodeIndex {
            key: IndexKey {
                program: 11,
                engine: 12,
            },
            functions: Vec::new(),
            postings: trigram_postings(&[]),
        };
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        assert_eq!(decode(&bytes), Some(index.clone()));
        let lit = Matcher::parse("x").expect("parses");
        assert!(grep(&index, &lit, "").is_empty());
        assert!(grep(&index, &lit, "no_such_name").is_empty());
        let re = Matcher::parse("re:.").expect("parses");
        assert!(grep(&index, &re, "").is_empty());
    }

    /// Every strict prefix of an index file is refused - cut in the
    /// header, mid-record or mid-postings - rather than read as a shorter
    /// index.
    ///
    /// # Panics
    ///
    /// When some prefix of the file decodes.
    #[test]
    fn every_truncation_is_refused() {
        let index = sample();
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        for cut in 0..bytes.len() {
            assert_eq!(decode(&bytes[..cut]), None, "cut at {cut}");
        }
    }

    /// Flipping any byte never panics and never yields a changed index.
    ///
    /// Header, length, text, digest or postings: only the key half of the
    /// header sits outside the digest, and a flipped key still reads back
    /// the same index under another name.
    ///
    /// # Panics
    ///
    /// When a flip crashes the reader or lands a changed index.
    #[test]
    fn every_single_byte_flip_is_refused_or_consistent() {
        let index = sample();
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        for at in 0..bytes.len() {
            for xor in [0x01u8, 0x80, 0xff] {
                let mut flipped = bytes.clone();
                flipped[at] ^= xor;
                let decoded = decode(&flipped);
                assert!(
                    decoded.as_ref().is_none_or(|ix| {
                        ix.functions == index.functions && ix.postings == index.postings
                    }),
                    "byte {at} xor {xor:#x} changed the index"
                );
            }
        }
    }

    /// A flipped byte in each named field - the magic, the format word,
    /// the record count, the digest, a name, a text, and every field of
    /// the postings tail the one-edit test never reaches - is refused.
    ///
    /// # Panics
    ///
    /// When an edited field is read, or a field cannot be located in the
    /// file.
    #[test]
    fn edits_in_every_named_field_are_refused() {
        let index = sample();
        let mut bytes = Vec::new();
        encode(&index, &mut bytes).expect("encodes");
        let find = |needle: &[u8], bytes: &[u8]| {
            bytes
                .windows(needle.len())
                .position(|w| w == needle)
                .expect("the needle is in the file")
        };
        let mut fields = vec![
            (0, "the magic"),
            (8, "the format word"),
            (28, "the record count"),
            (32, "the digest"),
            (find(b"sub_2000", &bytes), "a name"),
            (find(b"AppendCommand", &bytes), "a text"),
        ];
        let mut records_end = 40;
        for f in &index.functions {
            records_end += 16 + f.name.len() + f.text.len();
        }
        let u32_at = |at: usize| u32::from_le_bytes(bytes[at..at + 4].try_into().expect("aligned"));
        let present = u32_at(records_end);
        fields.push((records_end, "the postings count"));
        let mut walk = records_end + 4;
        for _ in 0..present {
            fields.push((walk, "a trigram id"));
            walk += 4;
            fields.push((walk, "a list length"));
            let len = u32_at(walk);
            walk += 4;
            for _ in 0..len {
                fields.push((walk, "a function index"));
                walk += 4;
            }
        }
        assert_eq!(walk, bytes.len(), "the walk reaches the file's end");
        for (at, what) in fields {
            let mut edited = bytes.clone();
            edited[at] ^= 0xff;
            assert_eq!(decode(&edited), None, "{what} is refused");
        }
    }

    /// Postings that claim more than the file holds are refused.
    ///
    /// A present count past the alphabet, a trigram id out of range, a
    /// list longer than the bytes left, a list the file cuts short
    /// mid-entry, a list the digest never covered.
    ///
    /// # Panics
    ///
    /// When a hostile count is read.
    #[test]
    fn hostile_posting_counts_are_refused() {
        let mut plain = sample();
        plain.postings = Postings::default();
        let mut bytes = Vec::new();
        encode(&plain, &mut bytes).expect("encodes an index without postings");
        let words =
            |parts: &[u32]| -> Vec<u8> { parts.iter().flat_map(|p| p.to_le_bytes()).collect() };
        let trigrams = u32::try_from(TRIGRAMS).expect("the alphabet fits a u32");
        let mut cut_short = words(&[1, 0, 1]);
        cut_short.extend_from_slice(&[0xAB, 0xCD]);
        for (tail, why) in [
            (words(&[u32::MAX]), "a present count past the alphabet"),
            (words(&[trigrams]), "more lists than the file holds"),
            (words(&[1, trigrams]), "a trigram id past the alphabet"),
            (
                words(&[1, 0, u32::MAX]),
                "a list longer than the bytes left",
            ),
            (cut_short, "a list the file cuts short mid-entry"),
            (words(&[1, 0, 1, 0]), "a list the digest never covered"),
        ] {
            let mut hostile = bytes[..bytes.len() - 4].to_vec();
            hostile.extend_from_slice(&tail);
            assert_eq!(decode(&hostile), None, "{why} is refused");
        }
    }

    /// A record count the file cannot hold is refused before anything is
    /// allocated for it.
    ///
    /// A 32-byte header claiming four billion records, under a file that
    /// would need sixteen bytes for each: a hostile cache file cannot ask
    /// for memory by its count alone.
    ///
    /// # Panics
    ///
    /// When the count is read or the scratch file cannot be stretched.
    #[test]
    fn a_record_count_past_the_files_bytes_is_refused() {
        let mut header = Vec::new();
        header.extend_from_slice(MAGIC);
        header.extend_from_slice(&FORMAT.to_le_bytes());
        header.extend_from_slice(&1u64.to_le_bytes());
        header.extend_from_slice(&2u64.to_le_bytes());
        header.extend_from_slice(&u32::MAX.to_le_bytes());
        let dir = scratch("huge_count");
        let path = dir.join(
            IndexKey {
                program: 1,
                engine: 2,
            }
            .file_name(),
        );
        std::fs::write(&path, &header).expect("writes the header");
        let file = std::fs::OpenOptions::new()
            .write(true)
            .open(&path)
            .expect("opens");
        file.set_len(u64::from(u32::MAX) + 128)
            .expect("stretches without writing");
        drop(file);
        assert_eq!(
            load_from(&path),
            None,
            "the count is past what the file can hold"
        );
        std::fs::remove_dir_all(&dir).expect("cleans up");
    }

    /// Lawless postings are refused even with a matching digest.
    ///
    /// A list out of order, an entry naming a function that is not there:
    /// this format never writes either, and the binary search a grep
    /// intersects with trusts the order, so over an unsorted list it can
    /// miss every function the shortest list marked, hiding lines the
    /// texts hold.
    ///
    /// # Panics
    ///
    /// When a lawful hand-made index is refused, or a lawless one is read,
    /// or the unsorted list fails to hide the lines it must.
    #[test]
    fn lawless_postings_are_refused_even_with_a_matching_digest() {
        let functions: Vec<IndexedFunction> = (0..3u64)
            .map(|i| IndexedFunction {
                entry: 0x1000 + 0x10 * i,
                name: format!("f{i}"),
                text: if i == 2 {
                    "y = 1;\n".to_owned()
                } else {
                    "x = abcdef;\n".to_owned()
                },
            })
            .collect();
        let (abc, bcd, cde, def) = (
            trigram(0, 1, 2),
            trigram(1, 2, 3),
            trigram(2, 3, 4),
            trigram(3, 4, 5),
        );
        let made = |lists: Vec<(usize, Vec<u32>)>| {
            let mut postings = Postings {
                lists: vec![Vec::new(); TRIGRAMS],
            };
            for (id, list) in lists {
                postings.lists[id] = list;
            }
            CodeIndex {
                key: IndexKey {
                    program: 13,
                    engine: 14,
                },
                functions: functions.clone(),
                postings,
            }
        };
        let round_trip = |index: &CodeIndex| {
            let mut bytes = Vec::new();
            encode(index, &mut bytes).expect("encodes");
            decode(&bytes)
        };
        let lawful = made(vec![
            (abc, vec![0, 1]),
            (bcd, vec![0, 1]),
            (cde, vec![0, 1]),
            (def, vec![0, 1]),
        ]);
        assert_eq!(
            round_trip(&lawful),
            Some(lawful),
            "a hand-made but lawful shape reads back"
        );
        let unsorted = made(vec![
            (abc, vec![0, 1]),
            (bcd, vec![2, 1, 0]),
            (cde, vec![0, 1]),
            (def, vec![0, 1]),
        ]);
        let matcher = Matcher::parse("abcdef").expect("parses");
        assert_eq!(
            grep_shape(&unsorted, &matcher, ""),
            Vec::new(),
            "the binary search over the unsorted list misses every function it marked"
        );
        assert_eq!(
            brute_hits(&unsorted, &matcher, "").len(),
            2,
            "both texts hold the literal"
        );
        assert_eq!(
            round_trip(&unsorted),
            None,
            "an out-of-order list is corrupt, digest or no digest"
        );
        let foreign = made(vec![
            (abc, vec![0, 1]),
            (bcd, vec![0, 1]),
            (cde, vec![0, 1]),
            (def, vec![0, 99]),
        ]);
        assert_eq!(
            round_trip(&foreign),
            None,
            "an entry past the functions is corrupt"
        );
    }
}
