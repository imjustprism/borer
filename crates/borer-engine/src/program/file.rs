//! Reading a program's file: paths that cannot be read, archives and the
//! members nested in them, and the parse of each object found.

use std::path::{Path, PathBuf};

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
/// are all the console, and `CONIN$`/`CONOUT$` its two halves. Reading one
/// is not reading a file: `con` blocks on console input, and inside the MCP
/// server - whose stdin carries the protocol - that took the session's own
/// stream and ended it silently, with no reply to the call that asked. A
/// path in the device namespace (`\\.\pipe\x`, `\\.\PhysicalDrive0`, the
/// same with `/`) is refused whole unless it spells a drive path, and so is
/// an unparsed `\\?\` path that is neither a drive nor a `UNC` path.
///
/// # Arguments
///
/// * `path` - The path as given.
///
/// # Returns
///
/// The reason, ready to put in a message, or `None` when the path is an
/// ordinary one. Only emptiness is checked off Windows, where these names
/// are names like any other.
#[must_use]
pub fn unusable_path(path: &Path) -> Option<String> {
    if path.as_os_str().is_empty() {
        return Some("the path is empty".to_owned());
    }
    if !cfg!(windows) {
        return None;
    }
    let spelled = path.as_os_str().to_string_lossy().replace('/', "\\");
    let drive = |rest: &str| {
        let b = rest.as_bytes();
        b.len() >= 3 && b[0].is_ascii_alphabetic() && b[1] == b':' && b[2] == b'\\'
    };
    let device = spelled
        .strip_prefix("\\\\.\\")
        .is_some_and(|rest| !drive(rest))
        || spelled
            .strip_prefix("\\\\?\\")
            .is_some_and(|rest| !drive(rest) && !rest.to_ascii_uppercase().starts_with("UNC\\"));
    if device {
        return Some(format!("{spelled} names a device, not a file"));
    }
    const DEVICES: [&str; 9] = [
        "con", "prn", "aux", "nul", "com", "lpt", "conin$", "conout$", "clock$",
    ];
    let stem = path.file_stem()?.to_str()?;
    let lower = stem.to_lowercase();
    let named = DEVICES.iter().any(|d| {
        lower == *d
            || (matches!(*d, "com" | "lpt")
                && lower.len() == 4
                && lower.starts_with(d)
                && lower.ends_with(|c: char| c.is_ascii_digit() && c != '0'))
    });
    named.then(|| format!("{stem} is a device, not a file"))
}

/// Reads a program file whole, refusing what is not a regular file.
///
/// # Arguments
///
/// * `path` - The file to read.
///
/// # Returns
///
/// The file's bytes.
///
/// # Errors
///
/// Returns the I/O error of reading the file, or the refusal of a name
/// that is a device, a directory or anything else that is not a regular
/// file.
fn read_program_file(path: &Path) -> anyhow::Result<Vec<u8>> {
    if let Some(why) = unusable_path(path) {
        return Err(anyhow!("{why}; give a path to a program to analyze"));
    }
    let shown = crate::text::short_path(&path.display().to_string());
    if path.is_dir() {
        return Err(anyhow!(
            "{shown} is a directory; give the path of a program file inside it"
        ));
    }
    let mut file = std::fs::File::open(path).with_context(|| format!("reading {shown}"))?;
    let meta = file
        .metadata()
        .with_context(|| format!("reading {shown}"))?;
    if !meta.is_file() {
        return Err(anyhow!(
            "{shown} is not a regular file (a device or a pipe); give a path to a program to analyze"
        ));
    }
    let mut bytes = Vec::new();
    std::io::Read::read_to_end(&mut file, &mut bytes)
        .with_context(|| format!("reading {shown}"))?;
    Ok(bytes)
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
    if path.exists() {
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
    depth: usize,
) -> anyhow::Result<(Vec<u8>, Option<Parent>)> {
    let Some((file, off)) = child_path(path).filter(|_| depth < NESTING_MAX) else {
        return Ok((read_program_file(path)?, None));
    };
    let (outer, _) = read_program_bytes(&file, Take::Program, depth + 1)?;
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
