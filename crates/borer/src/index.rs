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

/// Magic bytes opening an index file.
const MAGIC: &[u8; 8] = b"BORERIDX";
/// Layout version of the file; bump when the record shape changes.
const FORMAT: u32 = 3;
/// Longest name or text one record may carry, a bound on a corrupt length.
const RECORD_MAX: usize = 64 << 20;
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
    /// FNV-1a of the program's bytes, shared by every index of the program.
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
}

impl CodeIndex {
    /// Sum of the text sizes, in bytes.
    #[must_use]
    pub fn text_bytes(&self) -> usize {
        self.functions.iter().map(|f| f.text.len()).sum()
    }
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

/// The key an index for `program` is stored under: the program's bytes,
/// then the borer executable's size and modification time, the file format,
/// and the packs the analysis ran with.
///
/// The executable goes in because the text is what the decompiler of that
/// build renders; a newer borer must not read an older one's index. The
/// packs go in because they change the names the text uses. Both are kept
/// apart from the program's half, so a new index finds and replaces the
/// stale ones of its program by name.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `packs` - The packs the analysis ran with.
#[must_use]
pub fn index_key(program: &Program, packs: &Packs) -> IndexKey {
    let mut h = fnv1a(FNV_SEED, &FORMAT.to_le_bytes());
    for pack in &packs.packs {
        for e in &pack.entries {
            for part in [&e.section, &e.key, &e.value] {
                h = fnv1a(h, part.as_bytes());
                h = fnv1a(h, &[0]);
            }
        }
        for (_, code) in &pack.scripts {
            h = fnv1a(h, code.as_bytes());
            h = fnv1a(h, &[0]);
        }
    }
    if let Ok(exe) = std::env::current_exe()
        && let Ok(meta) = std::fs::metadata(exe)
    {
        h = fnv1a(h, &meta.len().to_le_bytes());
        let modified = meta
            .modified()
            .ok()
            .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
            .map_or(0, |d| d.as_secs());
        h = fnv1a(h, &modified.to_le_bytes());
    }
    IndexKey {
        program: fnv1a(FNV_SEED, &program.bytes),
        engine: h,
    }
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
    let functions = entries
        .iter()
        .zip(texts)
        .map(|(&entry, text)| IndexedFunction {
            entry,
            name: name_of(analysis, overlay, entry),
            text: text.unwrap_or_default(),
        })
        .collect();
    CodeIndex {
        key: index_key(program, &analysis.packs),
        functions,
    }
}

/// The FNV-1a digest of an index's records, exactly as [`encode`] writes
/// them: per function its entry, then its name and text each behind its
/// length.
///
/// The header carries it and [`read`] checks it, since a record that still
/// parses after an edit (a changed byte of a text) changed every grep over
/// it, and a cache that answers differently from a fresh build breaks the
/// promise that the same query answers the same.
///
/// # Arguments
///
/// * `functions` - The records, in file order.
fn digest(functions: &[IndexedFunction]) -> u64 {
    functions.iter().fold(FNV_SEED, |h, f| {
        let h = fnv1a(h, &f.entry.to_le_bytes());
        [&f.name, &f.text].iter().fold(h, |h, field| {
            let (len, bytes) = clipped(field);
            fnv1a(fnv1a(h, &len.to_le_bytes()), bytes)
        })
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
/// count, the records' [`digest`], then per function its entry and
/// length-prefixed name and text.
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
    out.write_all(&digest(&index.functions).to_le_bytes())?;
    for f in &index.functions {
        out.write_all(&f.entry.to_le_bytes())?;
        for field in [&f.name, &f.text] {
            let (len, bytes) = clipped(field);
            out.write_all(&len.to_le_bytes())?;
            out.write_all(bytes)?;
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
    if u64::try_from(count).ok()? > len {
        return None;
    }
    let stored = r.u64()?;
    let mut functions = Vec::with_capacity(count);
    for _ in 0..count {
        let entry = r.u64()?;
        let name = r.string()?;
        let text = r.string()?;
        functions.push(IndexedFunction { entry, name, text });
    }
    (digest(&functions) == stored).then_some(CodeIndex { key, functions })
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
    index
        .functions
        .iter()
        .filter(|f| q.is_empty() || f.name.to_lowercase().contains(&q))
        .flat_map(|f| {
            f.text
                .lines()
                .enumerate()
                .filter(|(_, line)| matcher.is_match(line.trim()))
                .map(|(i, line)| GrepHit {
                    entry: f.entry,
                    name: f.name.clone(),
                    line_no: i + 1,
                    line: line.trim().to_owned(),
                })
        })
        .collect()
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
/// * `skip` - Hits to skip.
/// * `limit` - Hits shown at most.
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
    skip: usize,
    limit: usize,
) -> Result<String, String> {
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
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A two-function index with a shared line and a distinct one.
    fn sample() -> CodeIndex {
        CodeIndex {
            key: IndexKey {
                program: 7,
                engine: 9,
            },
            functions: vec![
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
            ],
        }
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
        let text = grep_tsv(&index, &a, &Overlay::default(), "return", "", 1, 5).expect("parses");
        assert!(
            text.starts_with("# 2 lines in 2 functions contain 'return', showing 1 from 1\n"),
            "{text}"
        );
        assert!(text.contains("0x2000\tsub_2000\t2\treturn x;\n"), "{text}");
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
        let index = CodeIndex {
            key: IndexKey {
                program: 7,
                engine: 9,
            },
            functions: vec![IndexedFunction {
                entry: 0x1000,
                name: "f".to_owned(),
                text: "// f @ 0x1000\n\nif (a1 != 0) {\n  while (rax) {\n    Send(a1);\n    Send(a2);\n  }\n} else {\n  Send(0);\n}\nSend(9);\n".to_owned(),
            }],
        };
        let (a, o) = (Analysis::default(), Overlay::default());
        let note = render::SCOPE_NOTE;
        let rows = "entry\tfunction\tline\ttext\n";
        assert_eq!(
            grep_tsv(&index, &a, &o, "Send(", "", 0, 10).expect("parses"),
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
            grep_tsv(&index, &a, &o, "Send(", "", 2, 1).expect("parses"),
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
        let text =
            grep_tsv(&index, &a, &Overlay::default(), "re:^return", "", 0, 5).expect("parses");
        assert!(
            text.starts_with("# 2 lines in 2 functions match 're:^return', showing 2 from 0\n"),
            "{text}"
        );
    }
}
