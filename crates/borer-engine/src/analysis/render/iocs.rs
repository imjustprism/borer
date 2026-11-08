//! Indicators with provenance: each URL, host, address, key, path and
//! object name the program holds, with where it was found and how.
//!
//! A row names the pass that read it and the region its bytes sit in; an
//! indicator no code references is listed low and counted apart from the
//! ones the program uses.

use super::calls::{Reach, gather, listed_args};
use super::triage::call_sites;
use super::*;
use crate::analysis::decompile::CallArg;
use crate::cancel::Cancel;
use crate::fileinfo::Region;
use crate::ioc::{Confidence, Indicator, Kind, classify, named};

/// Most rows one read lists; the rest page with `offset=`.
pub const IOCS_PAGE: usize = 200;

/// Most indicators collected, so one huge image cannot grow the list
/// without bound.
const IOCS_MAX: usize = 5000;

/// Most functions decompiled for the arguments of the naming APIs.
const IOC_CALLERS_MAX: usize = 100;

/// Shortest string read for indicators.
const STRING_MIN: usize = 6;

/// Shortest base64 text decoded to look for indicators inside.
const BASE64_MIN: usize = 16;

/// Longest argument text read for an indicator, in characters.
const ARG_TEXT_MAX: usize = 512;

/// Most bytes walked back from a string's run to the start of the literal
/// holding it.
const LITERAL_BACK_MAX: usize = 4096;

/// Returns the file offset of the NUL-ended text an ASCII or UTF-16 run at
/// `off` is part of: a literal holding line breaks walks as one run per
/// line, and code references its first.
///
/// The walk stays inside the run's section, so code or another section's
/// bytes never pass for the literal's start; a run no section maps is its
/// own start.
///
/// # Arguments
///
/// * `p` - The loaded file.
/// * `off` - Where the run starts.
/// * `unit` - Bytes per character: one for ASCII, two for UTF-16.
fn literal_start(p: &Program, off: u64, unit: usize) -> u64 {
    let run = crate::num::saturating_usize(off);
    let floor = p
        .offset_to_va(off)
        .and_then(|va| p.section_at(va))
        .map_or(run, |s| {
            run.saturating_sub(LITERAL_BACK_MAX)
                .max(crate::num::saturating_usize(s.file_off.0))
        });
    let back = p
        .bytes
        .get(floor..run)
        .unwrap_or_default()
        .rchunks_exact(unit)
        .take_while(|c| {
            c.split_first().is_some_and(|(&b, high)| {
                (crate::strings::printable(b) || matches!(b, b'\t' | b'\n' | b'\r'))
                    && high.iter().all(|&h| h == 0)
            })
        })
        .count();
    off - from_usize(back.saturating_mul(unit))
}

/// Openings of the compiler and linker identifications a toolchain leaves
/// in the file outside the image (an ELF's `.comment`): each names the
/// toolchain's own repository, which the program never contacts.
const TOOLCHAIN_IDENTS: [&str; 4] = ["clang version ", "Linker: ", "GCC: (", "rustc version "];

/// APIs whose argument names an indicator: the API, the argument's
/// position counting from one, and what it names; `None` reads the text
/// for whatever it is (a URL, a host, a command line).
const NAMING_APIS: &[(&str, usize, Option<Kind>)] = &[
    ("CreateMutexA", 3, Some(Kind::Mutex)),
    ("CreateMutexW", 3, Some(Kind::Mutex)),
    ("CreateMutexExA", 2, Some(Kind::Mutex)),
    ("CreateMutexExW", 2, Some(Kind::Mutex)),
    ("OpenMutexA", 3, Some(Kind::Mutex)),
    ("OpenMutexW", 3, Some(Kind::Mutex)),
    ("CreateEventA", 4, Some(Kind::Object)),
    ("CreateEventW", 4, Some(Kind::Object)),
    ("OpenEventA", 3, Some(Kind::Object)),
    ("OpenEventW", 3, Some(Kind::Object)),
    ("CreateSemaphoreA", 4, Some(Kind::Object)),
    ("CreateSemaphoreW", 4, Some(Kind::Object)),
    ("CreateFileMappingA", 6, Some(Kind::Object)),
    ("CreateFileMappingW", 6, Some(Kind::Object)),
    ("OpenFileMappingA", 3, Some(Kind::Object)),
    ("OpenFileMappingW", 3, Some(Kind::Object)),
    ("CreateNamedPipeA", 1, Some(Kind::Pipe)),
    ("CreateNamedPipeW", 1, Some(Kind::Pipe)),
    ("WaitNamedPipeA", 1, Some(Kind::Pipe)),
    ("WaitNamedPipeW", 1, Some(Kind::Pipe)),
    ("CallNamedPipeA", 1, Some(Kind::Pipe)),
    ("CallNamedPipeW", 1, Some(Kind::Pipe)),
    ("RegOpenKeyA", 2, Some(Kind::Registry)),
    ("RegOpenKeyW", 2, Some(Kind::Registry)),
    ("RegOpenKeyExA", 2, Some(Kind::Registry)),
    ("RegOpenKeyExW", 2, Some(Kind::Registry)),
    ("RegCreateKeyA", 2, Some(Kind::Registry)),
    ("RegCreateKeyW", 2, Some(Kind::Registry)),
    ("RegCreateKeyExA", 2, Some(Kind::Registry)),
    ("RegCreateKeyExW", 2, Some(Kind::Registry)),
    ("RegDeleteKeyA", 2, Some(Kind::Registry)),
    ("RegDeleteKeyW", 2, Some(Kind::Registry)),
    ("RegSetKeyValueA", 2, Some(Kind::Registry)),
    ("RegSetKeyValueW", 2, Some(Kind::Registry)),
    ("RegGetValueA", 2, Some(Kind::Registry)),
    ("RegGetValueW", 2, Some(Kind::Registry)),
    ("CreateFileA", 1, Some(Kind::Path)),
    ("CreateFileW", 1, Some(Kind::Path)),
    ("DeleteFileA", 1, Some(Kind::Path)),
    ("DeleteFileW", 1, Some(Kind::Path)),
    ("CopyFileA", 2, Some(Kind::Path)),
    ("CopyFileW", 2, Some(Kind::Path)),
    ("MoveFileA", 2, Some(Kind::Path)),
    ("MoveFileW", 2, Some(Kind::Path)),
    ("MoveFileExA", 2, Some(Kind::Path)),
    ("MoveFileExW", 2, Some(Kind::Path)),
    ("CreateDirectoryA", 1, Some(Kind::Path)),
    ("CreateDirectoryW", 1, Some(Kind::Path)),
    ("fopen", 1, Some(Kind::Path)),
    ("_wfopen", 1, Some(Kind::Path)),
    ("URLDownloadToFileA", 2, None),
    ("URLDownloadToFileW", 2, None),
    ("InternetOpenUrlA", 2, None),
    ("InternetOpenUrlW", 2, None),
    ("InternetConnectA", 2, None),
    ("InternetConnectW", 2, None),
    ("WinHttpConnect", 2, None),
    ("gethostbyname", 1, None),
    ("getaddrinfo", 1, None),
    ("inet_addr", 1, None),
    ("WinExec", 1, None),
    ("CreateProcessA", 2, None),
    ("CreateProcessW", 2, None),
    ("ShellExecuteA", 3, None),
    ("ShellExecuteW", 3, None),
];

/// The predefined registry handles a key is opened under, by value.
const HIVE_HANDLES: [(u64, &str); 6] = [
    (0x8000_0000, "HKCR"),
    (0x8000_0001, "HKCU"),
    (0x8000_0002, "HKLM"),
    (0x8000_0003, "HKU"),
    (0x8000_0004, "HKPD"),
    (0x8000_0005, "HKCC"),
];

/// Which pass found an indicator.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Source {
    /// A string stored in the file, ASCII or UTF-16.
    Static,
    /// A .NET user string, a literal IL code loads, read from `#US`.
    DotnetUs,
    /// A base64 string stored in the file, decoded.
    DecodedB64,
    /// A string a function builds on its stack.
    Stack,
    /// A string a generator builds at run time, recovered by running it.
    Generated,
    /// A string a decoder produced, recovered by running it at a call site.
    Decoded,
    /// A string argument a generator run passed to an imported API or
    /// syscall, decoded when the emulator serviced the call: the function's
    /// name.
    Emulated(String),
    /// A string argument of a call to an API that names what it takes:
    /// the API and the argument's position counting from one.
    Call(String, usize),
}

impl Source {
    /// The word a row prints.
    fn word(&self) -> String {
        match self {
            Source::Static => "static".to_owned(),
            Source::DotnetUs => "dotnet-us".to_owned(),
            Source::DecodedB64 => "decoded-b64".to_owned(),
            Source::Stack => "stack".to_owned(),
            Source::Generated => "generated".to_owned(),
            Source::Decoded => "decoded".to_owned(),
            Source::Emulated(api) => format!("emulated:{api}"),
            Source::Call(api, pos) => format!("call:{api},a{pos}"),
        }
    }
}

/// One indicator with where it came from.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    /// The indicator.
    found: Indicator,
    /// The pass that found it.
    source: Source,
    /// Where: the string's address (or file offset when no section maps
    /// it), the store that starts a stack string, the generator, the call.
    site: Site,
    /// The function using it: referencing the string, building it, or
    /// making the call.
    function: Option<u64>,
    /// Where its bytes sit ([`crate::fileinfo::region`]): a stored string's
    /// region, [`Region::Code`] for one code builds or passes.
    region: Region,
}

/// Where an indicator sits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Site {
    /// A virtual address.
    Va(u64),
    /// A file offset no section maps.
    Off(u64),
}

/// Every indicator of a program, as one read collects them.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Collected {
    /// The rows, in listing order.
    rows: Vec<Row>,
    /// The collection stopped at [`IOCS_MAX`].
    full: bool,
    /// Functions calling a naming API.
    callers: usize,
    /// Of those, the ones decompiled.
    read: usize,
}

/// Collects every indicator of a program, once per set of names.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, holding the memo.
/// * `o` - Names in force, which the decompiled callers are read under.
fn collected(p: &Program, a: &Analysis, o: &Overlay) -> Arc<Collected> {
    a.derived
        .get_or_build_named("iocs", o.fingerprint(), (), || collect(p, a, o))
}

/// Adds the indicators the strings stored in the file hold: its ASCII and
/// UTF-16 strings outside code and a .NET assembly's user strings, with
/// the base64 among them decoded.
///
/// A stored string's indicators are as sure as where its bytes sit
/// ([`crate::fileinfo::region`]): one in data nothing references, in bytes
/// the loader leaves unmapped, or in data appended past the image reads
/// low and names its region, since nothing shows the program uses it. A
/// .NET user string is one IL code loads. The literal a string's run is a
/// line of ([`literal_start`]) is what code references: its region, and
/// the first function whose reference lands in it, are the run's.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: the references, and the functions using a string.
/// * `rows` - Where the indicators go, until [`IOCS_MAX`] are.
fn stored_rows(p: &Program, a: &Analysis, rows: &mut Vec<Row>) {
    let user = |off: u64, len: u64| {
        let va = p.offset_to_va(off)?;
        a.xrefs
            .range(va..va.saturating_add(len.max(1)))
            .flat_map(|(_, sites)| sites)
            .find_map(|s| s.from_entry)
    };
    let mut strings = crate::strings::find_strings(&p.bytes, STRING_MIN);
    strings.extend(crate::strings::find_wide_strings(&p.bytes, STRING_MIN));
    strings.sort_by_key(|h| h.off);
    let clr = p.clr();
    let user_strings = clr.map_or(&[][..], |c| c.user_strings.as_slice());
    let stored = user_strings
        .iter()
        .map(|u| {
            (
                u.off,
                (u.off, 1),
                std::borrow::Cow::Borrowed(u.text.as_str()),
                Source::DotnetUs,
                Region::Referenced,
            )
        })
        .chain(
            strings
                .iter()
                .filter(|hit| !clr.is_some_and(|c| c.in_user_strings(hit.off)))
                .map(|hit| {
                    let unit = if hit.encoding == crate::strings::Encoding::Ascii {
                        1
                    } else {
                        2
                    };
                    let start = literal_start(p, hit.off, unit);
                    let len =
                        from_usize(hit.len.saturating_mul(unit)).saturating_add(hit.off - start);
                    let place = crate::fileinfo::region(p, Some(a), start, len);
                    (
                        hit.off,
                        (start, len),
                        hit.full_text(&p.bytes),
                        Source::Static,
                        place,
                    )
                }),
        );
    for (off, (start, len), text, source, place) in stored {
        let skipped = match place {
            Region::Code => true,
            Region::Unmapped | Region::Appended => {
                TOOLCHAIN_IDENTS.iter().any(|t| text.starts_with(t))
            }
            Region::Referenced | Region::Loaded => false,
        };
        if source == Source::Static && skipped {
            continue;
        }
        let site = p.offset_to_va(off).map_or(Site::Off(off), Site::Va);
        let function = user(start, len);
        let decoded = base64_text(&text);
        let found = classify(&text)
            .into_iter()
            .map(|f| (f, source.clone()))
            .chain(
                decoded
                    .iter()
                    .flat_map(|d| classify(d))
                    .map(|f| (f, Source::DecodedB64)),
            );
        for (mut found, source) in found {
            if place > Region::Referenced {
                found.confidence = Confidence::Low;
            }
            rows.push(Row {
                found,
                source,
                site,
                function,
                region: place,
            });
        }
        if rows.len() >= IOCS_MAX {
            break;
        }
    }
}

/// Collects every indicator of a program with its provenance.
///
/// Six passes: the strings stored in the file outside code and a .NET
/// assembly's user strings (and the base64 among them, decoded), the
/// strings functions build on their stacks, the
/// strings generators build at run time ([`recovered_strings`]), the string
/// arguments those generator runs pass to imported APIs and syscalls
/// (decoded when the emulator services the call), the strings a decoder
/// produces when run at each of its call sites
/// ([`decoded_strings`]), and the string
/// arguments of the APIs that name a mutex, a pipe, a key, a file or
/// a host ([`NAMING_APIS`]), read from the decompiled callers' recorded
/// calls. An API's word for its argument decides its kind where the text
/// alone would not (a mutex name has no shape of its own), and a key opened
/// under a predefined hive handle is written under the hive.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
fn collect(p: &Program, a: &Analysis, o: &Overlay) -> Collected {
    let mut rows: Vec<Row> = Vec::new();
    stored_rows(p, a, &mut rows);
    for s in stack_strings(p, a, "") {
        for found in classify(&s.text) {
            rows.push(Row {
                found,
                source: Source::Stack,
                site: Site::Va(s.at),
                function: Some(s.entry),
                region: Region::Code,
            });
        }
    }
    let recovered = recovered_strings(p, a);
    for g in &recovered.found {
        for found in classify(&g.text) {
            rows.push(Row {
                found,
                source: Source::Generated,
                site: Site::Va(g.built_by),
                function: Some(g.built_by),
                region: Region::Code,
            });
        }
    }
    for arg in &recovered.emulated {
        for found in classify(&arg.text) {
            rows.push(Row {
                found,
                source: Source::Emulated(arg.api.clone()),
                site: Site::Va(arg.at),
                function: Some(arg.built_by),
                region: Region::Code,
            });
        }
    }
    for r in &decoded_strings(p, a, o).rows {
        for found in classify(&r.text) {
            rows.push(Row {
                found,
                source: Source::Decoded,
                site: Site::Va(r.at),
                function: Some(r.caller),
                region: Region::Code,
            });
        }
    }
    let (callers, read) = if p.refuses(Feature::Decompile).is_none() {
        call_arguments(p, a, o, &mut rows)
    } else {
        (0, 0)
    };
    let full = rows.len() >= IOCS_MAX;
    rows.truncate(IOCS_MAX);
    rows.sort_by(|l, r| {
        (
            l.found.benign,
            l.found.kind,
            &l.found.value,
            &l.source,
            l.site,
        )
            .cmp(&(
                r.found.benign,
                r.found.kind,
                &r.found.value,
                &r.source,
                r.site,
            ))
    });
    rows.dedup();
    Collected {
        rows,
        full,
        callers,
        read,
    }
}

/// Reads the indicators the naming APIs are handed, from the recorded
/// calls of the functions calling them.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
/// * `rows` - Where the indicators go.
///
/// # Returns
///
/// The functions calling a naming API, and how many of them were
/// decompiled ([`IOC_CALLERS_MAX`] in all); a raised cancel flag
/// ([`Cancel`]) reads no further API.
fn call_arguments(p: &Program, a: &Analysis, o: &Overlay, rows: &mut Vec<Row>) -> (usize, usize) {
    let mut callers = 0usize;
    let mut read = 0usize;
    for &(api, pos, kind) in NAMING_APIS.iter().take_while(|_| !Cancel::raised()) {
        let Some(sym) = p
            .symbols
            .iter()
            .find(|s| s.kind == SymbolKind::Import && s.addr != 0 && bare_name(&s.name) == api)
        else {
            continue;
        };
        let reach = Reach::import(a, sym.addr, &sym.name);
        let gathered = gather(p, a, o, &reach, IOC_CALLERS_MAX.saturating_sub(read));
        callers += gathered.callers;
        read += gathered.read;
        for f in &gathered.found {
            let Some(site) = &f.site else {
                continue;
            };
            let args = listed_args(site, None);
            let Some(text) = args.get(pos - 1).and_then(|arg| argument_text(p, api, arg)) else {
                continue;
            };
            let hive = args
                .first()
                .and_then(|h| h.value)
                .and_then(|v| HIVE_HANDLES.iter().find(|(h, _)| *h == v))
                .map(|(_, name)| *name);
            let text = match (kind, hive) {
                (Some(Kind::Registry), Some(hive)) => format!("{hive}\\{text}"),
                _ => text,
            };
            let mut found = classify(&text);
            if let Some(kind) = kind
                && !found.iter().any(|i| i.kind == kind)
            {
                found = named(kind, &text).into_iter().collect();
            }
            for found in found {
                rows.push(Row {
                    found,
                    source: Source::Call(api.to_owned(), pos),
                    site: Site::Va(f.at),
                    function: Some(f.caller),
                    region: Region::Code,
                });
            }
        }
    }
    (callers, read)
}

/// The text a naming API's argument names, read the way the API reads it.
///
/// A `W` API reads UTF-16 and any other reads bytes, so a constant argument
/// is read again from the image in the API's width: the decompiler may have
/// spelled a wide string by its first byte, and `RegCreateKeyW(hkey, "S")`
/// made a registry indicator `S`. An argument the text spells as a literal
/// with no address left is that literal, its C escapes undone, except a
/// narrow literal handed to a `W` API: that is a wide string read by its
/// first byte, and no indicator beats a wrong one.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `api` - The API's bare name.
/// * `arg` - The recorded argument.
///
/// # Returns
///
/// The text, or `None` when the argument names no string.
fn argument_text(p: &Program, api: &str, arg: &CallArg) -> Option<String> {
    let Some(v) = arg.value else {
        if api.ends_with('W') && !arg.text.starts_with("L\"") {
            return None;
        }
        return arg.string.as_deref().map(unescaped);
    };
    arg.string.as_ref()?;
    let read = if api.ends_with('W') {
        wstr_text_at(p, v, 1, ARG_TEXT_MAX)
    } else {
        cstr_text_at(p, v, 1, ARG_TEXT_MAX)
    };
    read.map(|(_, text)| text)
}

/// Undoes the C escapes of a literal's text: a backslash before `n`, `r`,
/// `t` or `0` stands for that control character, before `xNN` for that
/// byte, and before anything else for the character itself.
///
/// # Arguments
///
/// * `text` - The text between the quotes.
fn unescaped(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('0') => out.push('\0'),
            Some('x') => {
                let hex: String = chars.by_ref().take(2).collect();
                if let Ok(b) = u8::from_str_radix(&hex, 16) {
                    out.push(char::from(b));
                }
            }
            Some(other) => out.push(other),
            None => out.push('\\'),
        }
    }
    out
}

/// The text a base64 string decodes to, when it decodes to text.
///
/// # Arguments
///
/// * `s` - The string.
///
/// # Returns
///
/// The decoded text, or `None` when the string is short, not base64 or
/// decodes to bytes that are not printable text.
fn base64_text(s: &str) -> Option<String> {
    let body = s.trim_end_matches('=');
    let shaped = s.len() >= BASE64_MIN
        && s.len().is_multiple_of(4)
        && s.len() - body.len() <= 2
        && body
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'+' || b == b'/');
    if !shaped {
        return None;
    }
    let mut bytes = Vec::with_capacity(body.len() * 3 / 4);
    crate::entropy::decode(body.as_bytes(), crate::entropy::Encoding::Base64, |b| {
        bytes.push(b);
    });
    let text = bytes.iter().all(|b| literal_byte(*b)) && bytes.len() >= STRING_MIN;
    text.then(|| String::from_utf8_lossy(&bytes).into_owned())
}

/// A filter of an `iocs` read.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Filter {
    /// The kinds kept; empty keeps every kind.
    kinds: BTreeSet<Kind>,
    /// Lowercase text the value must contain; empty keeps every value.
    text: String,
    /// Rows to skip first.
    offset: usize,
    /// Most rows shown, when `limit=` asked for fewer than a page.
    limit: Option<usize>,
}

impl Filter {
    /// Reads a filter: comma-separated kind words (`ip` for both address
    /// kinds), `offset=<n>`, `limit=<n>`, and any other text the value must
    /// contain.
    ///
    /// # Arguments
    ///
    /// * `spec` - The filter as the URI carries it.
    ///
    /// # Errors
    ///
    /// When the offset or the limit is not a number.
    fn parse(spec: &str) -> Result<Filter, String> {
        let mut filter = Filter::default();
        let mut text: Vec<&str> = Vec::new();
        for token in spec.split(',').map(str::trim).filter(|t| !t.is_empty()) {
            if let Some(n) = token.strip_prefix("offset=") {
                filter.offset = n
                    .parse()
                    .map_err(|_| format!("bad offset {n:?}: a row count"))?;
            } else if let Some(n) = token.strip_prefix("limit=") {
                filter.limit = Some(crate::table::row_limit(n)?);
            } else if token.eq_ignore_ascii_case("ip") {
                filter.kinds.extend([Kind::Ipv4, Kind::Ipv6]);
            } else if let Some(kind) = Kind::ALL
                .into_iter()
                .find(|k| k.word().eq_ignore_ascii_case(token))
            {
                filter.kinds.insert(kind);
            } else {
                text.push(token);
            }
        }
        filter.text = text.join(",").to_lowercase();
        Ok(filter)
    }

    /// Tells whether a row passes.
    ///
    /// # Arguments
    ///
    /// * `row` - The row.
    fn keeps(&self, row: &Row) -> bool {
        (self.kinds.is_empty() || self.kinds.contains(&row.found.kind))
            && (self.text.is_empty() || row.found.value.to_lowercase().contains(&self.text))
    }
}

/// The count by kind of a set of rows, `2 url, 1 registry`, the benign
/// ones apart and so those no code references.
///
/// # Arguments
///
/// * `rows` - The rows.
fn by_kind(rows: &[&Row]) -> String {
    let mut counts: BTreeMap<Kind, usize> = BTreeMap::new();
    let (mut benign, mut unreached) = (0usize, 0usize);
    for r in rows {
        if r.found.benign {
            benign += 1;
        } else if r.region > Region::Referenced {
            unreached += 1;
        } else {
            *counts.entry(r.found.kind).or_default() += 1;
        }
    }
    let mut parts: Vec<String> = counts
        .iter()
        .map(|(k, n)| format!("{n} {}", k.word()))
        .collect();
    if parts.is_empty() {
        parts.push("none to act on".to_owned());
    }
    let mut tail = String::new();
    if benign > 0 {
        tail.push_str(&format!(" (+{benign} benign-common)"));
    }
    if unreached > 0 {
        tail.push_str(&format!(" (+{unreached} no code references)"));
    }
    format!("{}{tail}", parts.join(", "))
}

/// The triage's line on the program's indicators: their count by kind.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
pub(super) fn iocs_line(p: &Program, a: &Analysis, o: &Overlay) -> String {
    let all = collected(p, a, o);
    let rows: Vec<&Row> = all.rows.iter().collect();
    if rows.is_empty() {
        return "none in the strings, stack strings, generated strings or API arguments".to_owned();
    }
    format!(
        "{}; borer://iocs lists each with where it came from",
        by_kind(&rows)
    )
}

/// Lists the indicators a program holds, each with where it came from.
///
/// URLs, domains, IPv4 and IPv6 addresses, e-mail addresses, registry keys,
/// file paths, pipes, mutexes, other kernel object names and user agents
/// ([`crate::ioc::classify`]), from the strings stored outside code (and
/// base64 among them, decoded), the strings functions build on their
/// stacks, the strings generators build at run time, the string arguments
/// those runs pass to imported APIs and syscalls, the strings a decoder
/// produces at each of its call sites, and the string
/// arguments of the APIs that name what they take, read from the callers'
/// decompiled calls. A row says the kind, the confidence (or
/// `benign-common` for what every program carries: schema hosts, the
/// loopback address, a toolchain's build paths), the pass (`static`,
/// `decoded-b64`, `stack`, `generated`, `decoded`, `emulated:<api>`,
/// `call:<api>,a<N>`), the site (the
/// string's address or file offset, the store starting a stack string, the
/// generator, the call), the region its bytes sit in (`referenced`,
/// `unreferenced`, `unmapped` or `appended` for a stored string, `code` for
/// one code builds or passes: one no code references reads low and the
/// header counts it apart), the function using it, and the value. Rows are
/// sorted by kind and value, the benign ones last, [`IOCS_PAGE`] a page.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - The filter: kind words (`url`, `domain`, `ip`, `ipv4`,
///   `ipv6`, `email`, `registry`, `path`, `pipe`, `mutex`, `object`,
///   `useragent`), `offset=<n>`, `limit=<n>` (fewer rows than a page), and
///   any other text the value contains, comma-separated; empty for every
///   row.
///
/// # Returns
///
/// The header with the count by kind, then a row per indicator of the
/// page.
///
/// # Errors
///
/// When the offset or the limit is not a number.
pub fn iocs_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    let filter = Filter::parse(spec)?;
    let all = collected(p, a, o);
    let rows: Vec<&Row> = all.rows.iter().filter(|r| filter.keeps(r)).collect();
    let total = rows.len();
    let narrowed: Vec<&str> = spec
        .split(',')
        .map(str::trim)
        .filter(|t| !t.is_empty() && !t.starts_with("offset=") && !t.starts_with("limit="))
        .collect();
    let mut out = if narrowed.is_empty() {
        format!("# {total} indicator{}: {}\n", plural(total), by_kind(&rows))
    } else {
        format!(
            "# {total} of {} indicators where {}: {}\n",
            all.rows.len(),
            narrowed.join(","),
            by_kind(&rows)
        )
    };
    if all.full {
        let _ = writeln!(
            out,
            "# the collection stopped at {IOCS_MAX} indicators; a filter narrows what is read"
        );
    }
    if all.read < all.callers {
        let _ = writeln!(
            out,
            "# API arguments read in {} of the {} functions calling a naming API",
            all.read, all.callers
        );
    }
    let start = filter.offset.min(total);
    let size = filter.limit.map_or(IOCS_PAGE, |n| n.min(IOCS_PAGE));
    let page = &rows[start..total.min(start.saturating_add(size))];
    let _ = writeln!(
        out,
        "# {} from {}",
        showing(page.len(), total),
        filter.offset
    );
    if page.is_empty() {
        return Ok(out);
    }
    out.push_str(
        "# type      confidence     source                    site            region       function                  value\n",
    );
    for r in page {
        let confidence = if r.found.benign {
            "benign-common"
        } else {
            r.found.confidence.word()
        };
        let site = match r.site {
            Site::Va(va) => format!("{va:#x}"),
            Site::Off(off) => format!("off={off:#x}"),
        };
        let function = r
            .function
            .map_or_else(|| "-".to_owned(), |f| short_name(a, o, f));
        let _ = writeln!(
            out,
            "{:<9} {confidence:<14} {:<25} {site:<15} {:<12} {function:<25} {}",
            r.found.kind.word(),
            r.source.word(),
            r.region.word(),
            r.found.value
        );
    }
    let next = start + page.len();
    if next < total {
        let mut again: Vec<String> = spec
            .split(',')
            .map(str::trim)
            .filter(|t| !t.is_empty() && !t.starts_with("offset="))
            .map(str::to_owned)
            .collect();
        again.push(format!("offset={next}"));
        let _ = writeln!(
            out,
            "# {} more; borer://iocs/{} for the next page",
            total - next,
            again.join(",")
        );
    }
    Ok(out)
}

/// Whether the registry APIs write the program's own settings.
///
/// A Run key, a startup folder or a service stays persistence. Settings
/// are a registry write only when every function that calls one of the
/// APIs references a `Software\` key, and no key string names one of
/// those. A caller with no such key, or no code analysis to find the
/// callers, stays persistence: the key may be built at runtime.
///
/// Winlogon, Image File Execution Options, `AppInit_DLLs`, Shell Folders
/// and the `exefile` open command are persistence keys too.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its functions, for the callers and the keys they reference.
/// * `apis` - The persistence imports and syscalls, as the map shows them.
pub(super) fn settings_keys(p: &Program, a: Option<&Analysis>, apis: &[String]) -> bool {
    let Some(a) = a else {
        return false;
    };
    if apis.iter().any(|n| n.to_lowercase().contains("service")) {
        return false;
    }
    let run = |s: &str| {
        let s = s.to_lowercase();
        s.contains("\\run")
            || s.contains("runonce")
            || s.contains("\\startup")
            || s.contains("\\services\\")
            || s.contains("winlogon")
            || s.contains("image file execution options")
            || s.contains("appinit_dlls")
            || s.contains("shell folders")
            || s.contains("exefile\\shell\\open\\command")
    };
    if program_strings(p).iter().any(|s| run(s)) {
        return false;
    }
    let keyed: BTreeSet<u64> = referenced_strings(p, a)
        .iter()
        .filter(|r| r.folded.contains("software\\"))
        .flat_map(|r| a.xrefs_to(r.target).iter().filter_map(|s| s.from_entry))
        .collect();
    apis.iter().all(|api| {
        let stem = api.to_lowercase();
        let mut callers = a
            .functions
            .iter()
            .filter(|f| !call_sites(p, a, f.entry, &stem).is_empty())
            .peekable();
        callers.peek().is_some() && callers.all(|f| keyed.contains(&f.entry))
    })
}

/// The ASCII and wide strings in the image.
fn program_strings(p: &Program) -> Vec<String> {
    let mut out: Vec<String> = crate::strings::find_strings(&p.bytes, 4)
        .into_iter()
        .map(|hit| hit.text)
        .collect();
    out.extend(
        crate::strings::find_wide_strings(&p.bytes, 4)
            .into_iter()
            .map(|hit| hit.text),
    );
    out
}

#[cfg(test)]
mod tests {
    use super::{argument_text, unescaped};
    use crate::analysis::decompile::CallArg;
    use crate::program::{Arch, Program, Section};

    /// A wide string handed to a `W` API reads whole, though the text
    /// spelled it by its first byte, and an escaped literal reads as the
    /// characters it stands for.
    ///
    /// # Panics
    ///
    /// When the registry key reads as `S`, or the escapes stay.
    #[test]
    fn a_w_api_argument_reads_as_utf16() {
        let mut bytes = vec![0u8; 0x100];
        let key: Vec<u8> = r"Software\Notepad"
            .encode_utf16()
            .flat_map(u16::to_le_bytes)
            .collect();
        bytes[0x10..0x10 + key.len()].copy_from_slice(&key);
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0x1000,
            None,
            vec![Section::mapped(".rdata", 0x1000, 0, 0x100, false, false)],
        );
        let arg = CallArg {
            text: "\"S\"".to_owned(),
            value: Some(0x1010),
            string: Some("S".to_owned()),
        };
        assert_eq!(
            argument_text(&p, "RegCreateKeyW", &arg).as_deref(),
            Some(r"Software\Notepad")
        );
        assert_eq!(
            argument_text(&p, "RegCreateKeyA", &arg).as_deref(),
            Some("S")
        );
        let folded = CallArg { value: None, ..arg };
        assert_eq!(argument_text(&p, "RegCreateKeyW", &folded), None);
        assert_eq!(
            unescaped(r#"Software\\Microsoft\x41\"q\""#),
            r#"Software\MicrosoftA"q""#
        );
    }
}
