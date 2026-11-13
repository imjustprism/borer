//! Reading a program's file: paths that cannot be read, archives and the
//! members nested in them, and the parse of each object found.

use std::path::{Component, Path, PathBuf};

use anyhow::{Context, anyhow};

use super::caught;
use crate::num::{from_usize, saturating_usize};

/// Where an embedded program's bytes came from.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Parent {
    /// The file holding it, as named; itself `<file>@<offset>` for a
    /// program carved from a carved one.
    pub path: PathBuf,
    /// File offset of the program's first byte in that file.
    pub off: u64,
    /// Bytes of that file the program spans.
    pub len: u64,
}

/// The container a file's first bytes name, for a parse that fails.
///
/// # Arguments
///
/// * `bytes` - The file.
///
/// # Returns
///
/// `a PE`, `an ELF image`, `a Mach-O image`, `a fat Mach-O (or a Java
/// class file)` or `an archive`, or `None` when the magic is none of them.
pub(crate) fn magic_name(bytes: &[u8]) -> Option<&'static str> {
    let word = bytes.first_chunk::<4>().map(|b| u32::from_be_bytes(*b));
    match word {
        _ if bytes.first_chunk::<2>() == Some(b"MZ") => Some("a PE"),
        Some(0x7f45_4c46) => Some("an ELF image"),
        Some(0xfeed_face | 0xfeed_facf | 0xcefa_edfe | 0xcffa_edfe) => Some("a Mach-O image"),
        Some(0xcafe_babe) => Some("a fat Mach-O (or a Java class file)"),
        _ if bytes.starts_with(b"!<arch>\n") => Some("an archive"),
        _ => None,
    }
}

/// Parses a byte image into a goblin object, retrying a damaged one leniently.
///
/// A protector rewrites the section table and data directories so a strict
/// parse of the exception, import or relocation directory can fail on a file
/// that still loads and runs, and one bad byte in a header the loader never
/// reads (a section name that is not UTF-8, a symbol table offset past the
/// end) failed the whole file. When the strict parse fails, an `MZ` file
/// is parsed again in permissive mode, an ELF image in permissive mode and
/// a Mach-O image lossily: each keeps what it can read and drops what it
/// cannot, so the code is available to analyze even when the headers lie,
/// and what the strict parse said is kept for the summary to show.
///
/// # Arguments
///
/// * `bytes` - The file image.
/// * `parse_imports` - Whether a PE's import directory is read; `false`
///   when [`implausible_imports`](super::pe::implausible_imports) refused it.
///
/// # Returns
///
/// The object, with what the strict parse said when only the lenient one
/// read the file. A file whose magic names no format is
/// [`goblin::Object::Unknown`], however short.
///
/// # Errors
///
/// When a file whose magic names a format fails both parses, with what
/// each said.
pub(super) fn parse_object(
    bytes: &[u8],
    parse_imports: bool,
) -> anyhow::Result<(goblin::Object<'_>, Option<String>)> {
    use goblin::pe::options::{ParseMode, ParseOptions};
    if bytes.first_chunk::<2>() == Some(b"MZ") {
        let strict = ParseOptions::default().with_parse_imports(parse_imports);
        return match caught(|| goblin::pe::PE::parse_with_opts(bytes, &strict))? {
            Ok(pe) => Ok((goblin::Object::PE(pe), None)),
            Err(strict_err) => {
                let permissive = strict.with_parse_mode(ParseMode::Permissive);
                let pe = caught(|| goblin::pe::PE::parse_with_opts(bytes, &permissive))?
                    .map_err(|permissive| anyhow!("{strict_err}; permissive: {permissive}"))?;
                Ok((goblin::Object::PE(pe), Some(strict_err.to_string())))
            }
        };
    }
    let strict_err = match caught(|| goblin::Object::parse(bytes))? {
        Ok(obj) => return Ok((obj, None)),
        Err(e) => e,
    };
    let lenient = match bytes.first_chunk::<4>().map(|b| u32::from_be_bytes(*b)) {
        Some(0x7f45_4c46) if !permissive_elf_affordable(bytes)? => {
            return Err(anyhow!("{strict_err}"));
        }
        Some(0x7f45_4c46) => caught(|| {
            goblin::elf::Elf::parse_with_opts(bytes, &goblin::options::ParseOptions::permissive())
        })?
        .map(goblin::Object::Elf),
        Some(0xfeed_face | 0xfeed_facf | 0xcefa_edfe | 0xcffa_edfe | 0xcafe_babe) => {
            caught(|| goblin::mach::Mach::parse_lossy(bytes))?.map(goblin::Object::Mach)
        }
        _ if magic_name(bytes).is_none() => return Ok((goblin::Object::Unknown(0), None)),
        _ => return Err(anyhow!("{strict_err}")),
    };
    lenient
        .map(|obj| (obj, Some(strict_err.to_string())))
        .map_err(|lenient| anyhow!("{strict_err}; lenient: {lenient}"))
}

/// Most scan steps goblin's permissive ELF string-table preparse may take.
const PERMISSIVE_STRTAB_STEPS_MAX: u128 = 64 << 20;
/// Most `(offset, &str)` entries goblin's permissive ELF preparses may hold.
const PERMISSIVE_STRTAB_ENTRIES_MAX: u128 = 2 << 20;

/// Exact byte-scan steps and entry count goblin's permissive `Strtab` loop
/// takes on `bytes[offset..offset + len]`, bounded by the permissive caps.
///
/// On invalid UTF-8 goblin records `""` and advances by one byte, rescanning
/// to the same NUL on every invalid prefix of a chunk. The first starting
/// offset whose remainder to the NUL is valid UTF-8 jumps past the NUL, so
/// one linear UTF-8 chunk pass gives the exact quadratic step sum.
///
/// # Arguments
///
/// * `bytes` - Whole ELF file image.
/// * `offset` - String table file offset.
/// * `len` - Stated string table byte length.
fn strtab_cost(bytes: &[u8], offset: usize, len: usize) -> (u128, u128) {
    let Some(avail) = bytes.get(offset..) else {
        return (0, 0);
    };
    let slice = &avail[..avail.len().min(len)];
    let mut pos = 0usize;
    let mut steps: u128 = 0;
    let mut entries: u128 = 0;
    while pos < slice.len() {
        let rest = &slice[pos..];
        let nul = rest.iter().position(|&b| b == 0);
        let chunk_len = nul.unwrap_or(rest.len());
        let has_nul = nul.is_some();
        let chunk = &rest[..chunk_len];
        let valid_tail = chunk.utf8_chunks().last().map_or(0, |c| c.valid().len());
        let bad = chunk_len - valid_tail;
        let runs = bad + usize::from(valid_tail > 0 || has_nul);
        let top = u128::try_from(chunk_len + usize::from(has_nul)).unwrap_or(0);
        let r = u128::try_from(runs).unwrap_or(0);
        steps += r * top - r * r.saturating_sub(1) / 2;
        entries += r;
        if steps > PERMISSIVE_STRTAB_STEPS_MAX || entries > PERMISSIVE_STRTAB_ENTRIES_MAX {
            return (steps, entries);
        }
        pos = pos.saturating_add(chunk_len).saturating_add(1);
    }
    (steps, entries)
}

/// Checks whether goblin's permissive ELF retry stays within the string-table
/// scan and entry budgets across `e_shstrndx`, `.symtab`'s linked table, and
/// `DT_STRTAB`.
///
/// # Arguments
///
/// * `bytes` - Whole ELF file image.
///
/// # Errors
///
/// When inspecting the ELF headers panics inside the underlying parser.
fn permissive_elf_affordable(bytes: &[u8]) -> anyhow::Result<bool> {
    use goblin::container::{Container, Ctx, Endian};
    use goblin::elf::section_header::{SHN_XINDEX, SHT_SYMTAB, SectionHeader};
    use goblin::elf::{Dynamic, Elf, ProgramHeader};
    caught(|| {
        let Ok(header) = Elf::parse_header(bytes) else {
            return true;
        };
        let Ok(lazy) = Elf::lazy_parse(header) else {
            return true;
        };
        let container = if lazy.is_64 {
            Container::Big
        } else {
            Container::Little
        };
        let ctx = Ctx::new(container, Endian::from(lazy.little_endian));
        let Ok(phdrs) = ProgramHeader::parse(
            bytes,
            saturating_usize(header.e_phoff),
            usize::from(header.e_phnum),
            ctx,
        ) else {
            return true;
        };
        let shdrs = SectionHeader::parse(
            bytes,
            saturating_usize(header.e_shoff),
            usize::from(header.e_shnum),
            ctx,
        )
        .unwrap_or_default();
        let sec_range = |mut idx: usize| -> Option<(usize, usize)> {
            if idx == usize::try_from(SHN_XINDEX).unwrap_or(usize::MAX) {
                idx = usize::try_from(shdrs.first()?.sh_link).ok()?;
            }
            let sh = shdrs.get(idx)?;
            Some((saturating_usize(sh.sh_offset), saturating_usize(sh.sh_size)))
        };
        let sym_str = shdrs
            .iter()
            .rfind(|s| s.sh_type == SHT_SYMTAB)
            .and_then(|s| usize::try_from(s.sh_link).ok())
            .and_then(sec_range);
        let dyn_str = Dynamic::parse(bytes, &phdrs, ctx)
            .ok()
            .flatten()
            .map(|d| (d.info.strtab, d.info.strsz));
        let mut steps: u128 = 0;
        let mut entries: u128 = 0;
        for (off, len) in [sec_range(usize::from(header.e_shstrndx)), sym_str, dyn_str]
            .into_iter()
            .flatten()
        {
            let (s, e) = strtab_cost(bytes, off, len);
            steps = steps.saturating_add(s);
            entries = entries.saturating_add(e);
            if steps > PERMISSIVE_STRTAB_STEPS_MAX || entries > PERMISSIVE_STRTAB_ENTRIES_MAX {
                return false;
            }
        }
        true
    })
}

/// Why a path cannot be a file, when it cannot.
///
/// Public because a path from a caller is opened in more than one place: the
/// loader here, the fingerprint sidecar a diff reads, and a saved project.
/// Each of those refused a bad path in
/// its own words, or in the operating system's, which for an empty path was
/// "The system cannot find the path specified" with a blank where the path
/// should be.
///
/// Windows resolves a handful of names to character devices in every
/// directory and under any extension, so `con`, `C:/tmp/con` and `con.exe`
/// are all the console, and `CONIN$`/`CONOUT$` its two halves. A name is
/// read as Windows reads it: cut at its first `.` or `:`, trailing spaces
/// and dots dropped, in any case, and a superscript one, two or three is a
/// port number too, so `con `, `con:` and `COM` with a superscript one are
/// devices as well. Reading one
/// is not reading a file: `con` blocks on console input, and inside the MCP
/// server - whose stdin carries the protocol - that took the session's own
/// stream and ended it silently, with no reply to the call that asked. A
/// path in the device namespace (`\\.\pipe\x`, `\\.\PhysicalDrive0`, the
/// same with `/`) is refused whole unless it spells a drive path, and so is
/// an unparsed `\\?\` path that is not a drive path. Windows leaves a path
/// unparsed only when it starts with exactly `\\?\`, and folds `..` in every
/// other device path (`\\.\`, `//?/`, `\\?/`) with the prefix as the root,
/// so `\\.\C:\..\UNC\host\share` and `//?/C:/../UNC/host/share` are the
/// share: one with a `..` component is refused too.
///
/// A network share (`\\host\share\x`, `//host/share/x`,
/// `\\?\UNC\host\share\x`) is refused too: opening one, or only asking
/// whether it exists, makes Windows connect to the host and authenticate as
/// the user, so a path out of an analyzed file or an agent's argument would
/// hand the user's credentials to whoever named the host. borer reads local
/// files only.
///
/// A path in the NT object namespace (`\??\C:\x`, `\??\UNC\host\share\x`)
/// is refused whatever it names: Windows hands it to the kernel unparsed,
/// where `\??\UNC` is the network redirector and any device can be named,
/// and no file borer reads needs that spelling.
///
/// # Arguments
///
/// * `path` - The path as given.
///
/// # Returns
///
/// The reason, ready to put in a message, or `None` when the path is an
/// ordinary one. Only emptiness is checked off Windows, where these names
/// are names like any other and a share is a mounted directory.
#[must_use]
pub fn unusable_path(path: &Path) -> Option<String> {
    if path.as_os_str().is_empty() {
        return Some("the path is empty".to_owned());
    }
    if !cfg!(windows) {
        return None;
    }
    let raw = path.as_os_str().to_string_lossy();
    let spelled = raw.replace('/', "\\");
    if spelled.starts_with("\\??\\") {
        return Some(format!(
            "{spelled} names the NT object namespace, not a file"
        ));
    }
    let drive = |rest: &str| {
        let b = rest.as_bytes();
        b.len() >= 3 && b[0].is_ascii_alphabetic() && b[1] == b':' && b[2] == b'\\'
    };
    let long = spelled.strip_prefix("\\\\?\\");
    let share = long.is_some_and(|rest| rest.to_ascii_uppercase().starts_with("UNC\\"))
        || (spelled.starts_with("\\\\") && long.is_none() && !spelled.starts_with("\\\\.\\"));
    if share {
        return Some(format!(
            "{spelled} names a network share; borer reads local files only"
        ));
    }
    let folded = spelled.starts_with("\\\\.\\") || (long.is_some() && !raw.starts_with("\\\\?\\"));
    if folded && path.components().any(|c| c == Component::ParentDir) {
        return Some(format!(
            "{raw} holds `..` in a device path, which Windows folds past the drive to any device or share"
        ));
    }
    let device = spelled
        .strip_prefix("\\\\.\\")
        .is_some_and(|rest| !drive(rest))
        || long.is_some_and(|rest| !drive(rest));
    if device {
        return Some(format!("{spelled} names a device, not a file"));
    }
    const DEVICES: [&str; 9] = [
        "con", "prn", "aux", "nul", "com", "lpt", "conin$", "conout$", "clock$",
    ];
    let port = |digit: &str| {
        let mut chars = digit.chars();
        matches!(
            (chars.next(), chars.next()),
            (Some('1'..='9' | '\u{b9}' | '\u{b2}' | '\u{b3}'), None)
        )
    };
    let named_device = |part: &str| {
        let base = part
            .split(['.', ':'])
            .next()
            .unwrap_or_default()
            .trim_end_matches([' ', '.'])
            .to_ascii_lowercase();
        DEVICES.iter().any(|d| {
            base == *d || (matches!(*d, "com" | "lpt") && base.strip_prefix(d).is_some_and(port))
        })
    };
    let mut chars = raw.chars();
    if !matches!(path.components().next(), Some(Component::Prefix(_)))
        && matches!((chars.next(), chars.next()), (Some(_), Some(':')))
        && named_device(chars.as_str())
    {
        return Some(format!("{raw} names a device, not a file"));
    }
    let name = path.file_name()?.to_str()?;
    named_device(name).then(|| format!("{name} names a device, not a file"))
}

/// How a capped read failed.
enum ReadFail {
    /// The file's metadata stated a size past the cap.
    Over(String, u64),
    /// The file grew past the cap while it was read.
    Grew(String),
    /// Any other refusal or I/O failure.
    Other(anyhow::Error),
}

/// Reads a program file whole within `max` bytes, refusing what is not a
/// regular file.
///
/// # Arguments
///
/// * `path` - The file to read.
/// * `max` - Most bytes the file may hold.
///
/// # Returns
///
/// The file's bytes.
///
/// # Errors
///
/// Returns the I/O error of reading the file, the refusal of a file past
/// `max` bytes (naming `BORER_MAX_FILE`), or the refusal of a name that is
/// a device, a directory or anything else that is not a regular file.
fn read_program_file(path: &Path, max: u64) -> anyhow::Result<Vec<u8>> {
    match read_regular_raw(path, max) {
        Ok(bytes) => Ok(bytes),
        Err(ReadFail::Over(shown, len)) => Err(anyhow!(
            "{shown} is {len} bytes, past the {max}-byte limit: borer reads a file into memory whole and its analysis takes several times that. Set BORER_MAX_FILE (bytes, or 4G; 0 for no limit) to load it anyway, or load raw ranges with arch and regions"
        )),
        Err(ReadFail::Grew(shown)) => Err(anyhow!(
            "{shown} grew past the {max}-byte limit: set BORER_MAX_FILE (bytes, or 4G; 0 for no limit) to load it anyway"
        )),
        Err(ReadFail::Other(e)) => Err(anyhow!("{e:#}; give a path to a program to analyze")),
    }
}

/// Reads a file whole when it is a regular one no larger than a cap.
///
/// The file is opened by [`open_regular`]; the read itself stops one byte
/// past the cap. A path borer is given (in an argument, a file, a pack or
/// the environment) is read here, opened by [`open_regular`] or stated by
/// [`checked_metadata`]: clippy bars the standard readers elsewhere, and a
/// path borer builds itself says why where it reads one.
///
/// # Arguments
///
/// * `path` - The file.
/// * `max` - Most bytes it may hold.
///
/// # Returns
///
/// The file's bytes.
///
/// # Errors
///
/// As [`open_regular`], and when the read fails or the file grew past
/// `max` meanwhile.
pub fn read_regular(path: &Path, max: u64) -> anyhow::Result<Vec<u8>> {
    match read_regular_raw(path, max) {
        Ok(bytes) => Ok(bytes),
        Err(ReadFail::Over(shown, len)) => Err(anyhow!(
            "{shown} is {len} bytes, past the {max} it may hold"
        )),
        Err(ReadFail::Grew(shown)) => Err(anyhow!("{shown} grew past the {max} bytes it may hold")),
        Err(ReadFail::Other(e)) => Err(e),
    }
}

/// Reads a regular file within `max` bytes, distinguishing size-cap refusals.
///
/// # Arguments
///
/// * `path` - The file.
/// * `max` - Most bytes it may hold.
///
/// # Errors
///
/// Returns [`ReadFail::Over`] when the stated size exceeds `max`,
/// [`ReadFail::Grew`] when the read passes `max`, and [`ReadFail::Other`]
/// otherwise.
fn read_regular_raw(path: &Path, max: u64) -> Result<Vec<u8>, ReadFail> {
    let (file, len) = open_regular_sized(path, max)?;
    let shown = crate::text::short_path(&path.display().to_string());
    let cap = saturating_usize(len.min(max.saturating_add(1)));
    let mut bytes = Vec::with_capacity(cap);
    std::io::Read::read_to_end(
        &mut std::io::Read::take(file, max.saturating_add(1)),
        &mut bytes,
    )
    .with_context(|| format!("reading {shown}"))
    .map_err(ReadFail::Other)?;
    if from_usize(bytes.len()) > max {
        return Err(ReadFail::Grew(shown));
    }
    Ok(bytes)
}

/// Opens a file when it is a regular one no larger than a cap.
///
/// The path is judged before it is opened: on Linux and macOS opening a
/// pipe blocks until a writer comes and a device such as `/dev/zero`
/// reads forever, so what is not a regular file is refused by its
/// metadata, and the open file is judged again in case the name changed
/// in between.
///
/// # Arguments
///
/// * `path` - The file.
/// * `max` - Most bytes it may hold.
///
/// # Returns
///
/// The open file.
///
/// # Errors
///
/// When the path is unusable ([`unusable_path`]), is a directory, a
/// device, a pipe or anything else that is not a regular file, holds more
/// than `max` bytes, or does not open.
pub fn open_regular(path: &Path, max: u64) -> anyhow::Result<std::fs::File> {
    match open_regular_sized(path, max) {
        Ok((file, _)) => Ok(file),
        Err(ReadFail::Over(shown, len)) => Err(anyhow!(
            "{shown} is {len} bytes, past the {max} it may hold"
        )),
        Err(ReadFail::Grew(shown)) => Err(anyhow!("{shown} grew past the {max} bytes it may hold")),
        Err(ReadFail::Other(e)) => Err(e),
    }
}

/// Opens a regular file no larger than `max` and returns its stated length.
///
/// # Arguments
///
/// * `path` - The file.
/// * `max` - Most bytes it may hold.
///
/// # Returns
///
/// The open file and the length reported by its open handle's metadata.
///
/// # Errors
///
/// Returns [`ReadFail::Over`] when the file is larger than `max` and
/// [`ReadFail::Other`] for any other refusal or open error.
fn open_regular_sized(path: &Path, max: u64) -> Result<(std::fs::File, u64), ReadFail> {
    if let Some(why) = unusable_path(path) {
        return Err(ReadFail::Other(anyhow!("{why}")));
    }
    let shown = crate::text::short_path(&path.display().to_string());
    let judge = |meta: &std::fs::Metadata| {
        if meta.is_dir() {
            Err(ReadFail::Other(anyhow!(
                "{shown} is a directory; give the path of a file inside it"
            )))
        } else if !meta.is_file() {
            Err(ReadFail::Other(anyhow!(
                "{shown} is not a regular file (a device or a pipe)"
            )))
        } else if meta.len() > max {
            Err(ReadFail::Over(shown.clone(), meta.len()))
        } else {
            Ok(())
        }
    };
    #[expect(
        clippy::disallowed_methods,
        reason = "the checked reader, past unusable_path"
    )]
    let meta = std::fs::metadata(path)
        .with_context(|| format!("reading {shown}"))
        .map_err(ReadFail::Other)?;
    judge(&meta)?;
    #[expect(
        clippy::disallowed_methods,
        reason = "the checked reader, on a regular file"
    )]
    let file = std::fs::File::open(path)
        .with_context(|| format!("reading {shown}"))
        .map_err(ReadFail::Other)?;
    let open_meta = file
        .metadata()
        .with_context(|| format!("reading {shown}"))
        .map_err(ReadFail::Other)?;
    judge(&open_meta)?;
    Ok((file, open_meta.len()))
}

/// Returns a path's metadata, once [`unusable_path`] lets the path through:
/// the one stat of a path borer is given that is not a read.
///
/// # Arguments
///
/// * `path` - The path.
///
/// # Returns
///
/// The metadata, or `None` when it does not read: nothing is there, or it
/// cannot be reached.
///
/// # Errors
///
/// When the path is unusable, with the reason.
pub fn checked_metadata(path: &Path) -> Result<Option<std::fs::Metadata>, String> {
    if let Some(why) = unusable_path(path) {
        return Err(why);
    }
    #[expect(
        clippy::disallowed_methods,
        reason = "the checked stat, past unusable_path"
    )]
    let meta = std::fs::metadata(path).ok();
    Ok(meta)
}

/// How much of a file a `<file>@<offset>` load takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Take {
    /// The program that starts at the offset, as far as its headers state
    /// ([`crate::carve::at`]).
    Program,
    /// Every byte from the offset to the end, for a stated layout to map.
    Rest,
}

/// Most `@<offset>` suffixes one path may chain.
const NESTING_MAX: usize = 4;

/// Splits a path that names no file into the file and the offset its
/// `@<offset>` suffix names.
///
/// # Arguments
///
/// * `path` - The path as given.
///
/// # Returns
///
/// The file part and the offset (`0x` hex or decimal), or `None` when the
/// path names a file of its own or has no such suffix.
fn child_path(path: &Path) -> Option<(PathBuf, u64)> {
    if checked_metadata(path).ok().flatten().is_some() {
        return None;
    }
    let (file, off) = path.to_str()?.rsplit_once('@')?;
    let off = match off.strip_prefix("0x").or_else(|| off.strip_prefix("0X")) {
        Some(hex) => u64::from_str_radix(hex, 16).ok()?,
        None => off.parse().ok()?,
    };
    Some((PathBuf::from(file), off))
}

/// Reads a program file, or the bytes of a program embedded in one.
///
/// A path naming no file but ending in `@<offset>` after one that does
/// names the bytes at that file offset ([`child_path`]): the program its
/// headers say starts there, as far as they state ([`crate::carve::at`]),
/// or for a stated layout every byte from there on. The file part may
/// itself be `<file>@<offset>`, up to [`NESTING_MAX`] deep.
///
/// # Arguments
///
/// * `path` - The path as given.
/// * `take` - How much a `@<offset>` path takes.
/// * `max` - Most bytes the underlying file on disk may hold.
/// * `depth` - How many `@<offset>` suffixes were read off already.
///
/// # Returns
///
/// The bytes, and where they came from when they are a carved program's.
///
/// # Errors
///
/// As [`read_program_file`]; for a `@<offset>` path, when the offset is
/// past the end, or no PE, ELF or Mach-O image starts there (naming the
/// container that does, if one does).
pub(super) fn read_program_bytes(
    path: &Path,
    take: Take,
    max: u64,
    depth: usize,
) -> anyhow::Result<(Vec<u8>, Option<Parent>)> {
    if let Some(why) = unusable_path(path) {
        return Err(anyhow!("{why}; give a path to a program to analyze"));
    }
    let Some((file, off)) = child_path(path).filter(|_| depth < NESTING_MAX) else {
        return Ok((read_program_file(path, max)?, None));
    };
    let (outer, _) = read_program_bytes(&file, Take::Program, max, depth + 1)?;
    let shown = crate::text::short_path(&file.display().to_string());
    let rest = usize::try_from(off)
        .ok()
        .and_then(|start| outer.get(start..))
        .filter(|rest| !rest.is_empty())
        .ok_or_else(|| {
            anyhow!(
                "offset {off:#x} is past the end of {shown} ({:#x} bytes)",
                outer.len()
            )
        })?;
    let len = match take {
        Take::Rest => rest.len(),
        Take::Program => match crate::carve::at(&outer, off) {
            Some(child) if child.kind.is_program() => match child.size {
                crate::carve::Size::Stated(n) => saturating_usize(n),
                crate::carve::Size::Run(_) | crate::carve::Size::Unknown => rest.len(),
            },
            Some(child) => {
                return Err(anyhow!(
                    "{shown} holds a {} at {off:#x} ({}): containers are listed, not extracted, and a load opens a PE, ELF or Mach-O image; with arch the bytes from there map raw",
                    child.kind.name(),
                    child.identity
                ));
            }
            None => {
                return Err(anyhow!(
                    "no PE, ELF or Mach-O image starts at {off:#x} in {shown}: borer://children lists the programs it holds; with arch the bytes from there map raw"
                ));
            }
        },
    };
    let bytes = rest.get(..len).unwrap_or(rest).to_vec();
    Ok((
        bytes,
        Some(Parent {
            path: file,
            off,
            len: from_usize(len),
        }),
    ))
}
