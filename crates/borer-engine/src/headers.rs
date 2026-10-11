//! Header-level facts a triage reads before any code.
//!
//! What kind of image the file is, when and how it was linked, which exploit
//! mitigations it enables, where its debug information lives, what runs
//! before the entry point, what is appended after the mapped image, and what
//! it links against.
//!
//! The loader fills a [`Headers`] while it holds the parsed file headers and
//! [`Program::summary`](crate::program::Program::summary) renders it as a few
//! lines, so one `binary_info` call answers the first triage questions.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use goblin::elf::Elf;
use goblin::pe::PE;
use goblin::pe::data_directories::DataDirectoryType;

use crate::program::Section;

/// A handler the x64 unwind tables register for one function.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ExceptionHandler {
    /// Entry of the function the handler is registered for.
    pub function: u64,
    /// The handler's address: a thunk into the runtime, or the runtime
    /// itself when it is linked in.
    pub handler: u64,
    /// Where the handler's language-specific data begins.
    pub data: u64,
}

/// Facts read from the file headers; every field is empty for a raw file.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Headers {
    /// The exception handlers the unwind tables register, one per x64
    /// function that has one: the function, the handler's address, and
    /// where the handler's own data begins. What that data names -
    /// funclets - [`crate::unwind`] reads.
    pub exception_handlers: Vec<ExceptionHandler>,
    /// Extents of the x64 exception table's chained entries, sorted: the
    /// separated chunks of a function (PGO's cold code), which share the
    /// unwind state of the function they belong to.
    pub chained_chunks: Vec<(u64, u64)>,
    /// Image kind: `exe`, `dll`, `driver` (PE) or `ET_EXEC`, `ET_DYN (pie)`,
    /// `ET_DYN (shared object)`, `ET_REL`, `ET_CORE` (ELF).
    pub kind: Option<&'static str>,
    /// The instruction set the header names, for an architecture the
    /// disassembler does not decode: the goblin machine string with the
    /// raw code (`ARM (e_machine 40)`, `RISCV (e_machine 243)`). `None` for
    /// x86 and x86-64, whose architecture the summary already names, and for
    /// a raw file with no header to read.
    pub machine: Option<String>,
    /// PE link timestamp in seconds since the Unix epoch; `None` when zero.
    pub timestamp: Option<u32>,
    /// Linker `major.minor` from the PE optional header (`14.44`).
    pub linker: Option<String>,
    /// PE subsystem: `console`, `gui`, `native`, `posix`, `efi`, `boot`, `other`.
    pub subsystem: Option<&'static str>,
    /// Mitigations the headers enable (`aslr`, `dep`, `cfg`, `nx`, `relro`, ...).
    pub mitigations: Vec<&'static str>,
    /// Mitigations the format offers and the headers leave off (`no-aslr`, `exec-stack`, ...).
    pub missing: Vec<&'static str>,
    /// `CodeView` PDB path with its symbol-server id (PE), or `build-id <hex>` (ELF).
    pub debug_id: Option<String>,
    /// TLS callback addresses: code that runs before the entry point.
    pub tls_callbacks: Vec<u64>,
    /// Address of the module's TLS index (`_tls_index`), the slot of the
    /// thread's TLS array that holds this module's block.
    pub tls_index: Option<u64>,
    /// Whether an Authenticode certificate table is present (its signature
    /// is not verified); `None` for a format that has no such table.
    pub signed: Option<bool>,
    /// Mach-O `FairPlay` encryption: `Some(true)` when an
    /// `LC_ENCRYPTION_INFO` or `LC_ENCRYPTION_INFO_64` command is present
    /// and its `cryptid` is nonzero, so the image ships encrypted;
    /// `None` when the file has no such command.
    pub fairplay: Option<bool>,
    /// The PE header checksum as `(declared, computed over the file)`; a
    /// declared zero is a checksum never set, a mismatch is a file edited
    /// after linking.
    pub checksum: Option<(u32, u32)>,
    /// The PE data directories that are present, by name, in table order.
    pub directories: Vec<&'static str>,
    /// The MSVC Rich header as `(product id, build, object count)` entries,
    /// most objects first: the compilers and tools that produced the link,
    /// a build fingerprint that survives stripping.
    pub rich: Vec<(u16, u16, u32)>,
    /// The PE resource types present, by name, in directory order.
    pub resources: Vec<&'static str>,
    /// The `VS_VERSIONINFO` string fields present, as `(field, value)`:
    /// `CompanyName`, `ProductName`, `FileVersion` and the rest.
    pub version: Vec<(&'static str, String)>,
    /// What the assembly manifest declares, as `(fact, value)`: the
    /// requested execution level (does it ask for admin), UI access, DPI
    /// awareness.
    pub manifest: Vec<(&'static str, String)>,
    /// `(file offset, length)` of each run of bytes after the last mapped
    /// section that the certificate table does not hold, in file order:
    /// appended payloads and installers, before the table and after it.
    /// Bytes appended after the table sit outside what the signature covers,
    /// so a signed file still verifies with them there.
    pub overlay: Vec<(u64, u64)>,
    /// `(file offset, length)` of the Authenticode certificate table that
    /// follows the sections, cut at the end of the file.
    pub certificates: Option<(u64, u64)>,
    /// Function extents the x64 exception table declares (chained chunks excluded).
    pub unwind_functions: usize,
    /// PE sections whose name is still a `/NN` COFF string-table index because
    /// that table is absent or out of range, so the name shown is an offset
    /// rather than a name. Common in rebuilt or stripped images carrying
    /// DWARF sections.
    pub unresolved_section_names: usize,
    /// A COFF symbol table the header declares but the file does not hold,
    /// as `(offset, entry count)`.
    ///
    /// The header of a rebuilt or hand-edited image often still points at a
    /// symbol table that was dropped, and an offset past the end of the file
    /// is proof the image is not what its own header says. It is also why the
    /// long section names cannot be resolved.
    pub symbols_out_of_range: Option<(u64, u32)>,
    /// Linked libraries: PE import DLLs or ELF `DT_NEEDED` entries, in file order.
    pub libraries: Vec<String>,
    /// The PE import directory was not read because it names at least this
    /// many entries, more than fit in the file or than any module imports:
    /// a rewritten or shifted directory, whose every word read as an import.
    pub implausible_imports: Option<u64>,
    /// The PE export directory was not read because it claims this many
    /// entries, more than a sixteen-bit ordinal reaches: a damaged header.
    pub implausible_exports: Option<u32>,
    /// ELF program interpreter (the dynamic loader path).
    pub interpreter: Option<String>,
    /// ELF: the static symbol table is absent (`Some(true)` means stripped).
    pub stripped: Option<bool>,
    /// Section table rows the loader dropped because the file cannot hold
    /// what they state: bytes past its end, a size past 1 GiB, an end past
    /// the top of the address space.
    pub dropped_sections: usize,
    /// The furthest file offset a kept section's bytes reach when that is
    /// past the end of the file: the file is truncated, and each such
    /// section keeps only the bytes the file holds.
    pub truncated: Option<u64>,
}

/// Names a section from the shape of its bytes.
///
/// A PE stores a section name longer than eight bytes as `/NN`, an offset
/// into the COFF string table. When that table is stripped or, as on a
/// rebuilt image, points past the end of the file, the name is gone and the
/// loader shows the offset. The bytes still say what the section is: every
/// DWARF section carries a header or a signature, so the name can be
/// recovered from content rather than left as `/19`.
///
/// The answer is a guess from evidence and says so where two shapes are
/// identical: DWARF 5 gives range lists and location lists the same header,
/// so nothing in the bytes separates them.
///
/// # Arguments
///
/// * `bytes` - The section's file bytes, from its start.
///
/// # Returns
///
/// The name the content indicates, or `None` when nothing matches.
#[must_use]
pub fn sniff_section(bytes: &[u8]) -> Option<&'static str> {
    /// Reads a little-endian `u32` at `at`.
    fn u32_at(b: &[u8], at: usize) -> Option<u32> {
        b.get(at..at + 4)?.try_into().ok().map(u32::from_le_bytes)
    }
    /// Reads a little-endian `u16` at `at`.
    fn u16_at(b: &[u8], at: usize) -> Option<u16> {
        b.get(at..at + 2)?.try_into().ok().map(u16::from_le_bytes)
    }
    if bytes.len() < 8 {
        return None;
    }
    let version = u16_at(bytes, 4);
    let address_size_at = |at: usize| matches!(bytes.get(at), Some(4 | 8));
    // A call-frame section opens with a CIE whose id says which one it is:
    // zero for the runtime unwinder's copy, all ones for the debug copy.
    if let Some(id) = u32_at(bytes, 4)
        && bytes.get(8) == Some(&1)
    {
        if id == 0 {
            return Some(".eh_frame");
        }
        if id == u32::MAX {
            return Some(".debug_frame");
        }
    }
    // The line-number program header ends with the standard opcode lengths,
    // a fixed run that no other section carries.
    if bytes
        .windows(6)
        .take(64)
        .any(|w| w == [0x01, 0x01, 0x01, 0xfb, 0x0e, 0x0d])
    {
        return Some(".debug_line");
    }
    // An address-range table is version 2 to this day, with the address size
    // and segment selector after the offset into .debug_info.
    if version == Some(2) && address_size_at(10) && bytes.get(11) == Some(&0) {
        return Some(".debug_aranges");
    }
    // A DWARF 5 unit header: version, then the unit's kind and address size.
    if version == Some(5) {
        if matches!(bytes.get(6), Some(0x01..=0x06)) && address_size_at(7) {
            return Some(".debug_info");
        }
        // Range lists and location lists share this header exactly.
        if address_size_at(6) && bytes.get(7) == Some(&0) {
            return Some(".debug_rnglists or .debug_loclists");
        }
    }
    if matches!(version, Some(2..=4)) && address_size_at(10) {
        return Some(".debug_info");
    }
    // An abbreviation table opens with declaration code 1, a small tag, and
    // the byte saying whether that tag has children.
    if bytes[0] == 0x01 && matches!(bytes[1], 0x01..=0x4b) && matches!(bytes[2], 0 | 1) {
        return Some(".debug_abbrev");
    }
    // A string table is printable text in NUL-terminated runs. Paths tell the
    // line-program's file table from the one holding names.
    let text = bytes.iter().take(4096);
    let printable = text
        .clone()
        .filter(|b| (0x20..0x7f).contains(*b) || **b == 0)
        .count();
    if printable * 10 >= bytes.len().min(4096) * 9 {
        let looked = bytes.len().min(4096);
        let separators = bytes
            .iter()
            .take(4096)
            .filter(|b| **b == b'/' || **b == 0x5c)
            .count();
        // A file table is made of paths, so separators are a percent of it or
        // more; a name table has almost none.
        let looks_like_paths = separators * 100 > looked;
        return Some(if looks_like_paths {
            ".debug_line_str or .debug_str"
        } else {
            ".debug_str"
        });
    }
    None
}

/// Names the container a file is from the magic at its start.
///
/// For a file the loader does not read as a program: a compressed archive,
/// a database, a document, an image, or an encrypted wallet. The list holds
/// the common containers only; a file that matches none of them is told
/// apart by its entropy instead.
///
/// # Arguments
///
/// * `bytes` - The file, from its first byte.
///
/// # Returns
///
/// What the magic says the file is, or `None` when no magic matches.
#[must_use]
pub fn sniff_file(bytes: &[u8]) -> Option<&'static str> {
    /// Leading bytes and the container they open.
    const MAGIC: [(&[u8], &str); 21] = [
        (b"PK\x03\x04", "zip archive"),
        (b"PK\x05\x06", "zip archive (empty)"),
        (b"\x1f\x8b", "gzip stream"),
        (b"7z\xbc\xaf\x27\x1c", "7z archive"),
        (b"\xfd7zXZ\x00", "xz stream"),
        (b"\x28\xb5\x2f\xfd", "zstd frame"),
        (b"BZh", "bzip2 stream"),
        (b"\x04\x22\x4d\x18", "lz4 frame"),
        (b"Rar!\x1a\x07\x00", "RAR archive (v1.5)"),
        (b"Rar!\x1a\x07\x01\x00", "RAR archive (v5)"),
        (b"MSCF", "Microsoft Cabinet"),
        (
            b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1",
            "OLE2 compound file (MSI/DOC/XLS)",
        ),
        (b"!<arch>\n", "ar archive or static library"),
        (b"SQLite format 3\x00", "SQLite database"),
        (b"%PDF-", "PDF document"),
        (b"\x89PNG\r\n\x1a\n", "PNG image"),
        (b"\xff\xd8\xff", "JPEG image"),
        (b"GIF8", "GIF image"),
        (b"-----BEGIN ", "PEM-encoded key or certificate"),
        (b"\xca\xfe\xba\xbe", "Java class or Mach-O fat binary"),
        (
            b"QklFMQ",
            "Electrum encrypted wallet (base64 of BIE1 ECIES ciphertext)",
        ),
    ];
    // tar's `ustar` magic sits at offset 257, not the start, so it is
    // checked there rather than as a leading signature.
    if bytes.len() > 262 && bytes[257..262] == *b"ustar" {
        return Some("tar archive (ustar)");
    }
    MAGIC
        .iter()
        .find(|(magic, _)| bytes.starts_with(magic))
        .map(|&(_, name)| name)
}

impl Headers {
    /// Renders the facts as summary lines; empty for a raw file.
    ///
    /// Lines: `image:` (kind, link time, linker, subsystem, interpreter,
    /// symbol table), `mitigations:` (enabled and missing), `debug:`,
    /// `tls:` (callbacks), `notes:` (signature, fairplay, overlay, unwind
    /// count, a refused import or export table) and
    /// `libraries (N):` capped at twelve names. Each appears only when it has
    /// something to say.
    pub fn render(&self) -> String {
        /// Most library names listed before `, ...`.
        const LIBS_SHOWN: usize = 12;
        /// Most Rich header entries listed before `, ... N more`.
        const RICH_SHOWN: usize = 6;
        let mut out = String::new();
        let mut image: Vec<String> = Vec::new();
        if let Some(k) = self.kind {
            image.push(format!("kind {k}"));
        }
        if let Some(t) = self.timestamp {
            image.push(format!("linked {}", stamp(t)));
        }
        if let Some(l) = &self.linker {
            image.push(format!("linker {l}"));
        }
        if let Some(s) = self.subsystem {
            image.push(format!("subsystem {s}"));
        }
        if let Some(i) = &self.interpreter {
            image.push(format!("interp {i}"));
        }
        if let Some(stripped) = self.stripped {
            image.push(if stripped { "stripped" } else { "symtab" }.to_owned());
        }
        if !image.is_empty() {
            let _ = writeln!(out, "image:   {}", image.join("   "));
        }
        if !self.mitigations.is_empty() || !self.missing.is_empty() {
            let _ = writeln!(
                out,
                "mitigations: {}   missing: {}",
                join_or_dash(&self.mitigations),
                join_or_dash(&self.missing)
            );
        }
        if let Some(d) = &self.debug_id {
            let _ = writeln!(out, "debug:   {d}");
        }
        if !self.tls_callbacks.is_empty() {
            let list: Vec<String> = self
                .tls_callbacks
                .iter()
                .map(|c| format!("{c:#x}"))
                .collect();
            let _ = writeln!(
                out,
                "tls:     {} callbacks [{}]",
                self.tls_callbacks.len(),
                list.join(", ")
            );
        }
        let mut notes: Vec<String> = Vec::new();
        match self.signed {
            Some(true) => notes.push("signed".to_owned()),
            Some(false) => notes.push("unsigned".to_owned()),
            None => {}
        }
        if self.fairplay == Some(true) {
            notes.push("fairplay-encrypted".to_owned());
        }
        if let Some((declared, computed)) = self.checksum {
            notes.push(if declared == 0 {
                "checksum unset".to_owned()
            } else if declared == computed {
                format!("checksum {declared:#x} verified")
            } else {
                format!(
                    "checksum {declared:#x} declared, {computed:#x} computed: edited after linking"
                )
            });
        }
        for &(off, len) in &self.overlay {
            let after = self.certificates.is_some_and(|(at, size)| off == at + size);
            notes.push(format!(
                "overlay {len} bytes @ {off:#x}{}",
                if after {
                    " after the certificate table"
                } else {
                    ""
                }
            ));
        }
        if self.unwind_functions > 0 {
            notes.push(format!("unwind {} functions", self.unwind_functions));
        }
        if self.unresolved_section_names > 0 {
            notes.push(format!(
                "{} section names unresolved (/NN is a COFF string-table offset, that table is gone)",
                self.unresolved_section_names
            ));
        }
        if let Some((at, count)) = self.symbols_out_of_range {
            notes.push(format!(
                "the header declares {count} COFF symbols at {at:#x}, past the end of the file: the image is not what its header says"
            ));
        }
        if let Some(n) = self.implausible_imports {
            notes.push(format!(
                "import table implausible ({n}+ entries, more than fit): not read"
            ));
        }
        if let Some(n) = self.implausible_exports {
            notes.push(format!(
                "export table implausible ({n} entries, more than an ordinal reaches): not read"
            ));
        }
        if !notes.is_empty() {
            let _ = writeln!(out, "notes:   {}", notes.join("   "));
        }
        if !self.directories.is_empty() {
            let _ = writeln!(out, "dirs:    {}", self.directories.join(" "));
        }
        if !self.rich.is_empty() {
            let shown: Vec<String> = self
                .rich
                .iter()
                .take(RICH_SHOWN)
                .map(|(id, build, count)| format!("{id:#x}.{build} x{count}"))
                .collect();
            let more = if self.rich.len() > RICH_SHOWN {
                format!(", ... {} more", self.rich.len() - RICH_SHOWN)
            } else {
                String::new()
            };
            let _ = writeln!(
                out,
                "rich:    {} tools (product.build x objects): {}{more}",
                self.rich.len(),
                shown.join(", ")
            );
        }
        if !self.resources.is_empty() {
            let _ = writeln!(out, "rsrc:    {}", self.resources.join(" "));
        }
        if !self.version.is_empty() {
            let fields: Vec<String> = self
                .version
                .iter()
                .map(|(k, v)| format!("{k} \"{v}\""))
                .collect();
            let _ = writeln!(out, "version: {}", fields.join("  "));
        }
        if !self.manifest.is_empty() {
            let facts: Vec<String> = self
                .manifest
                .iter()
                .map(|(k, v)| format!("{k}={v}"))
                .collect();
            let _ = writeln!(out, "manifest: {}", facts.join("  "));
        }
        if !self.libraries.is_empty() {
            let shown: Vec<&str> = self
                .libraries
                .iter()
                .take(LIBS_SHOWN)
                .map(String::as_str)
                .collect();
            let _ = writeln!(
                out,
                "libraries ({}): {}{}",
                self.libraries.len(),
                shown.join(", "),
                if self.libraries.len() > LIBS_SHOWN {
                    ", ..."
                } else {
                    ""
                }
            );
        }
        out
    }
}

/// Joins names with spaces, or `-` for none.
///
/// # Arguments
///
/// * `names` - The names.
fn join_or_dash(names: &[&str]) -> String {
    if names.is_empty() {
        "-".to_owned()
    } else {
        names.join(" ")
    }
}

/// Formats a PE link timestamp.
///
/// Reproducible builds store a hash in the field, so values outside
/// 1990..=2100 render as the raw number.
///
/// # Arguments
///
/// * `secs` - Seconds since the Unix epoch.
///
/// # Returns
///
/// `YYYY-MM-DD HH:MM:SS` (UTC), or `stamp 0x...` for an implausible date.
///
/// # Examples
///
/// ```
/// use borer_engine::headers::stamp;
///
/// assert_eq!(stamp(1_757_030_400), "2025-09-05 00:00:00");
/// assert_eq!(stamp(0), "stamp 0x0");
/// ```
pub fn stamp(secs: u32) -> String {
    let secs = i64::from(secs);
    let (y, m, d) = civil_from_days(secs.div_euclid(86_400));
    if !(1990..=2100).contains(&y) {
        return format!("stamp {secs:#x}");
    }
    let rem = secs.rem_euclid(86_400);
    format!(
        "{y:04}-{m:02}-{d:02} {:02}:{:02}:{:02}",
        rem / 3600,
        rem % 3600 / 60,
        rem % 60
    )
}

/// Converts days since 1970-01-01 to a proleptic Gregorian date.
///
/// Howard Hinnant's `civil_from_days`, exact for the whole `i64` range.
///
/// # Arguments
///
/// * `days` - Days since the Unix epoch (negative before it).
///
/// # Returns
///
/// `(year, month 1..=12, day 1..=31)`.
fn civil_from_days(days: i64) -> (i64, i64, i64) {
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    (y, m, d)
}

/// Reads the PE header facts.
///
/// Mitigations come from the optional header's DLL characteristics and the
/// load configuration (`cfg` from the guard flags, `safeseh` from the x86
/// handler table). The overlay is what follows the last section's file
/// extent less the certificate table when one is appended: the bytes
/// before the table, and those after it.
///
/// # Arguments
///
/// * `pe` - The parsed file.
/// * `file_len` - Length of the whole file.
/// * `sections` - The loader's sanity-checked sections.
/// * `unwind_functions` - Number of function extents in the exception table.
pub(crate) fn from_pe(
    pe: &PE<'_>,
    bytes: &[u8],
    file_len: u64,
    sections: &[Section],
    unwind_functions: usize,
) -> Headers {
    use goblin::pe::dll_characteristic as dc;
    use goblin::pe::load_config::IMAGE_GUARD_CF_INSTRUMENTED;
    use goblin::pe::subsystem as ss;

    let mut h = Headers {
        unwind_functions,
        ..Headers::default()
    };
    let machine = pe.header.coff_header.machine;
    if !matches!(machine, 0x8664 | 0x014c | 0xaa64) {
        h.machine = Some(format!(
            "{} (machine {machine:#06x})",
            goblin::pe::header::machine_to_str(machine)
        ));
    }
    h.unresolved_section_names = sections
        .iter()
        .filter(|s| {
            s.name
                .strip_prefix('/')
                .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
        })
        .count();
    // A declared symbol table that does not fit in the file is a tamper
    // mark, and the reason a `/NN` section name cannot be resolved: the
    // string table sits just past the symbols it does not have.
    let symbols_at = u64::from(pe.header.coff_header.pointer_to_symbol_table);
    let symbol_count = pe.header.coff_header.number_of_symbol_table;
    let declared_end = symbols_at.saturating_add(u64::from(symbol_count).saturating_mul(18));
    if symbols_at != 0 && declared_end > file_len {
        h.symbols_out_of_range = Some((symbols_at, symbol_count));
    }
    let stamp = pe.header.coff_header.time_date_stamp;
    h.timestamp = (stamp != 0).then_some(stamp);
    h.signed = Some(!pe.certificates.is_empty());
    let pe_pointer = usize::try_from(pe.header.dos_header.pe_pointer).unwrap_or(usize::MAX);
    h.rich = rich_header(bytes, pe_pointer);
    if let Some(res) = &pe.resource_data {
        let mut seen: BTreeSet<&'static str> = BTreeSet::new();
        for entry in res.entries().flatten() {
            let name = entry.id().map_or("named", resource_type_name);
            if seen.insert(name) {
                h.resources.push(name);
            }
        }
        if let Some(v) = &res.version_info {
            let s = &v.string_info;
            let fields = [
                ("CompanyName", s.company_name()),
                ("ProductName", s.product_name()),
                ("FileDescription", s.file_description()),
                ("FileVersion", s.file_version()),
                ("ProductVersion", s.product_version()),
                ("InternalName", s.internal_name()),
                ("OriginalFilename", s.original_filename()),
                ("LegalCopyright", s.legal_copyright()),
            ];
            for (field, value) in fields {
                if let Some(value) =
                    value.map(|v| crate::text::one_line(v.trim_end_matches('\0').trim()))
                    && !value.is_empty()
                {
                    h.version.push((field, value));
                }
            }
        }
        if let Some(m) = &res.manifest_data {
            h.manifest = manifest_facts(m.data);
        }
    }
    h.libraries = pe.libraries.iter().map(|l| (*l).to_owned()).collect();
    h.tls_callbacks = pe
        .tls_data
        .as_ref()
        .map(|t| t.callbacks.clone())
        .unwrap_or_default();
    h.tls_index = pe
        .tls_data
        .as_ref()
        .map(|t| t.image_tls_directory.address_of_index)
        .filter(|va| *va != 0);
    if let Some(cv) = pe
        .debug_data
        .as_ref()
        .and_then(|d| d.codeview_pdb70_debug_info.as_ref())
    {
        // The debug path is bytes out of the file like any other name.
        let path =
            crate::text::one_line(String::from_utf8_lossy(cv.filename).trim_end_matches('\0'));
        let g = cv.signature;
        let tail: String = g[8..].iter().map(|b| format!("{b:02X}")).collect();
        let guid = format!(
            "{:08X}{:04X}{:04X}{tail}",
            u32::from_le_bytes([g[0], g[1], g[2], g[3]]),
            u16::from_le_bytes([g[4], g[5]]),
            u16::from_le_bytes([g[6], g[7]])
        );
        h.debug_id = Some(format!("{path} (pdb {guid}{:X})", cv.age));
    }
    let load_config = pe.load_config_data.as_ref().map(|l| &l.directory);
    let mapped_end = sections
        .iter()
        .map(|s| s.file_off + s.file_size)
        .max()
        .unwrap_or(0);
    let mut overlay_end = file_len;
    if let Some(opt) = &pe.header.optional_header {
        let std_fields = &opt.standard_fields;
        h.linker = Some(format!(
            "{}.{}",
            std_fields.major_linker_version, std_fields.minor_linker_version
        ));
        let win = &opt.windows_fields;
        h.subsystem = Some(match win.subsystem {
            ss::IMAGE_SUBSYSTEM_NATIVE => "native",
            ss::IMAGE_SUBSYSTEM_WINDOWS_GUI => "gui",
            ss::IMAGE_SUBSYSTEM_WINDOWS_CUI => "console",
            ss::IMAGE_SUBSYSTEM_POSIX_CUI => "posix",
            ss::IMAGE_SUBSYSTEM_EFI_APPLICATION
            | ss::IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER
            | ss::IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER
            | ss::IMAGE_SUBSYSTEM_EFI_ROM => "efi",
            ss::IMAGE_SUBSYSTEM_WINDOWS_BOOT_APPLICATION => "boot",
            _ => "other",
        });
        h.kind = Some(if pe.is_lib {
            "dll"
        } else if win.subsystem == ss::IMAGE_SUBSYSTEM_NATIVE {
            "driver"
        } else {
            "exe"
        });
        let has = |flag: u16| win.dll_characteristics & flag != 0;
        let mut on: Vec<&'static str> = Vec::new();
        let mut off: Vec<&'static str> = Vec::new();
        if has(dc::IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE) {
            on.push("aslr");
            if pe.is_64 {
                if has(dc::IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA) {
                    on.push("high-entropy-va");
                } else {
                    off.push("no-high-entropy-va");
                }
            }
        } else {
            off.push("no-aslr");
        }
        if has(dc::IMAGE_DLLCHARACTERISTICS_NX_COMPAT) {
            on.push("dep");
        } else {
            off.push("no-dep");
        }
        let guard = load_config
            .and_then(|l| l.guard_flags)
            .is_some_and(|g| g & IMAGE_GUARD_CF_INSTRUMENTED != 0);
        if has(dc::IMAGE_DLLCHARACTERISTICS_GUARD_CF) || guard {
            on.push("cfg");
        } else {
            off.push("no-cfg");
        }
        if !has(dc::IMAGE_DLLCHARACTERISTICS_NO_SEH) {
            on.push("seh");
            if !pe.is_64 {
                let safeseh = load_config
                    .and_then(|l| l.se_handler_table)
                    .is_some_and(|t| t != 0);
                if safeseh {
                    on.push("safeseh");
                } else {
                    off.push("no-safeseh");
                }
            }
        }
        if has(dc::IMAGE_DLLCHARACTERISTICS_FORCE_INTEGRITY) {
            on.push("force-integrity");
        }
        if has(dc::IMAGE_DLLCHARACTERISTICS_APPCONTAINER) {
            on.push("appcontainer");
        }
        h.mitigations = on;
        h.missing = off;
        h.directories = opt
            .data_directories
            .dirs()
            .filter(|(_, d)| d.virtual_address != 0 && d.size != 0)
            .map(|(kind, _)| directory_name(kind))
            .collect();
        // INVARIANT: the checksum field sits 64 bytes into the optional
        // header on PE32 and PE32+ alike, after the signature and the COFF
        // header.
        let field = pe_pointer.saturating_add(4 + 20 + 64);
        h.checksum = Some((win.check_sum, pe_checksum(bytes, field)));
        if let Some((cert, size)) = opt
            .data_directories
            .dirs()
            .find(|(kind, _)| *kind == DataDirectoryType::CertificateTable)
            .map(|(_, d)| (u64::from(d.virtual_address), u64::from(d.size)))
            .filter(|(off, _)| *off >= mapped_end && *off <= file_len)
        {
            overlay_end = cert;
            if size > 0 && cert < file_len {
                h.certificates = Some((cert, size.min(file_len - cert)));
            }
        }
    }
    if overlay_end > mapped_end {
        h.overlay.push((mapped_end, overlay_end - mapped_end));
    }
    if let Some((cert, size)) = h.certificates
        && cert + size < file_len
    {
        h.overlay.push((cert + size, file_len - cert - size));
    }
    h
}

/// Names a resource type by its `RT_*` id.
///
/// # Arguments
///
/// * `id` - The type id at the top of the resource directory.
fn resource_type_name(id: u16) -> &'static str {
    use goblin::pe::resource as rt;
    match id {
        rt::RT_CURSOR => "cursor",
        rt::RT_BITMAP => "bitmap",
        rt::RT_ICON => "icon",
        rt::RT_MENU => "menu",
        rt::RT_DIALOG => "dialog",
        rt::RT_STRING => "string",
        rt::RT_FONTDIR => "fontdir",
        rt::RT_FONT => "font",
        rt::RT_ACCELERATOR => "accelerator",
        rt::RT_RCDATA => "rcdata",
        rt::RT_MESSAGETABLE => "messagetable",
        rt::RT_GROUP_CURSOR => "group_cursor",
        rt::RT_GROUP_ICON => "group_icon",
        rt::RT_VERSION => "version",
        rt::RT_DLGINCLUDE => "dlginclude",
        rt::RT_PLUGPLAY => "plugplay",
        rt::RT_VXD => "vxd",
        rt::RT_ANICURSOR => "anicursor",
        rt::RT_ANIICON => "aniicon",
        rt::RT_HTML => "html",
        rt::RT_MANIFEST => "manifest",
        _ => "other",
    }
}

/// Reads what an assembly manifest declares about privilege and display.
///
/// The manifest is XML the program cannot lie about to the loader: the
/// requested execution level is whether it asks for administrator rights,
/// and the DPI elements are how it wants to be drawn. Element and attribute
/// names are matched without their namespace prefixes.
///
/// # Arguments
///
/// * `xml` - The `RT_MANIFEST` bytes.
///
/// # Returns
///
/// `(fact, value)` pairs for the declarations present.
fn manifest_facts(xml: &[u8]) -> Vec<(&'static str, String)> {
    let text = String::from_utf8_lossy(xml);
    let mut out = Vec::new();
    if let Some(v) = xml_attribute(&text, "requestedExecutionLevel", "level") {
        out.push(("requestedExecutionLevel", v));
    }
    if let Some(v) = xml_attribute(&text, "requestedExecutionLevel", "uiAccess") {
        out.push(("uiAccess", v));
    }
    for tag in [
        "dpiAware",
        "dpiAwareness",
        "longPathAware",
        "activeCodePage",
    ] {
        if let Some(v) = xml_element(&text, tag) {
            out.push((tag, v));
        }
    }
    out
}

/// Reads one attribute of the first element with a tag name.
///
/// # Arguments
///
/// * `text` - The document.
/// * `tag` - The element's local name.
/// * `attr` - The attribute's name.
fn xml_attribute(text: &str, tag: &str, attr: &str) -> Option<String> {
    let at = text.find(tag)?;
    let rest = text.get(at..)?;
    let element = rest.get(..rest.find('>')?)?;
    let key = format!("{attr}=\"");
    let value = element.get(element.find(&key)? + key.len()..)?;
    Some(value.get(..value.find('"')?)?.trim().to_owned())
}

/// Reads the text of the first element with a tag name.
///
/// # Arguments
///
/// * `text` - The document.
/// * `tag` - The element's local name.
fn xml_element(text: &str, tag: &str) -> Option<String> {
    let key = format!("{tag}>");
    let at = text.find(&key)? + key.len();
    let value = text.get(at..)?;
    Some(value.get(..value.find('<')?)?.trim().to_owned())
}

/// Names a data directory the way the listing names sections.
///
/// # Arguments
///
/// * `kind` - The directory's slot in the optional header.
fn directory_name(kind: DataDirectoryType) -> &'static str {
    match kind {
        DataDirectoryType::ExportTable => "export",
        DataDirectoryType::ImportTable => "import",
        DataDirectoryType::ResourceTable => "resource",
        DataDirectoryType::ExceptionTable => "exception",
        DataDirectoryType::CertificateTable => "certificate",
        DataDirectoryType::BaseRelocationTable => "reloc",
        DataDirectoryType::DebugTable => "debug",
        DataDirectoryType::Architecture => "architecture",
        DataDirectoryType::GlobalPtr => "globalptr",
        DataDirectoryType::TlsTable => "tls",
        DataDirectoryType::LoadConfigTable => "load-config",
        DataDirectoryType::BoundImportTable => "bound-import",
        DataDirectoryType::ImportAddressTable => "iat",
        DataDirectoryType::DelayImportDescriptor => "delay-import",
        DataDirectoryType::ClrRuntimeHeader => "clr",
    }
}

/// Computes the PE checksum of a file.
///
/// The ones'-complement sum of every 16-bit word but the checksum field
/// itself, folded to 16 bits, plus the file length: what the loader
/// verifies for a driver and what any edit after linking breaks.
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `field` - File offset of the four-byte checksum field.
fn pe_checksum(bytes: &[u8], field: usize) -> u32 {
    let mut sum: u32 = 0;
    for (i, pair) in bytes.chunks(2).enumerate() {
        let at = i * 2;
        if at >= field && at < field.saturating_add(4) {
            continue;
        }
        let low = u32::from(pair.first().copied().unwrap_or(0));
        let high = u32::from(pair.get(1).copied().unwrap_or(0));
        sum += low | (high << 8);
        sum = (sum & 0xffff) + (sum >> 16);
    }
    sum = (sum & 0xffff) + (sum >> 16);
    (sum & 0xffff).wrapping_add(u32::try_from(bytes.len()).unwrap_or(u32::MAX))
}

/// Reads the MSVC Rich header between the DOS stub and the PE header.
///
/// The record ends with `Rich` and the key that masks it; walked back in
/// four-byte steps under the key it starts at `DanS`, and between the two,
/// after three padding words, come `(product id << 16 | build, count)`
/// pairs, one per compiler or tool that produced an object in the link.
///
/// # Arguments
///
/// * `bytes` - The whole file.
/// * `pe_pointer` - File offset of the PE signature, where the search ends.
///
/// # Returns
///
/// `(product id, build, count)` entries, most objects first; empty when
/// there is no record.
fn rich_header(bytes: &[u8], pe_pointer: usize) -> Vec<(u16, u16, u32)> {
    /// The masked `DanS` word that opens the record.
    const DANS: u32 = 0x536e_6144;
    let Some(head) = bytes.get(..pe_pointer.min(bytes.len())) else {
        return Vec::new();
    };
    let Some(rich) = head.windows(4).rposition(|w| w == b"Rich") else {
        return Vec::new();
    };
    let Some(key) = le_u32(head, rich + 4) else {
        return Vec::new();
    };
    let mut at = rich;
    loop {
        if at < 4 {
            return Vec::new();
        }
        at -= 4;
        match le_u32(head, at) {
            Some(v) if v ^ key == DANS => break,
            Some(_) => {}
            None => return Vec::new(),
        }
    }
    let mut entries = Vec::new();
    let mut p = at + 16;
    while p + 8 <= rich {
        let (Some(id), Some(count)) = (le_u32(head, p), le_u32(head, p + 4)) else {
            break;
        };
        let id = id ^ key;
        entries.push((
            u16::try_from(id >> 16).unwrap_or(0),
            u16::try_from(id & 0xffff).unwrap_or(0),
            count ^ key,
        ));
        p += 8;
    }
    entries.sort_by(|l, r| r.2.cmp(&l.2).then(l.cmp(r)));
    entries
}

/// Reads a little-endian `u32` at a file offset.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `at` - The offset.
fn le_u32(bytes: &[u8], at: usize) -> Option<u32> {
    let b = bytes.get(at..at.checked_add(4)?)?;
    Some(u32::from_le_bytes(b.try_into().ok()?))
}

/// Reads the ELF header facts.
///
/// Mitigations: `nx` from a non-executable `PT_GNU_STACK`, `relro` from
/// `PT_GNU_RELRO` (with `bind-now` when the dynamic flags request eager
/// binding), `pie` for a position-independent executable, `canary` and
/// `fortify` from the imports the compiler's hardening emits.
///
/// # Arguments
///
/// * `elf` - The parsed file.
/// * `bytes` - The whole file, for the note segments.
pub(crate) fn from_elf(elf: &Elf<'_>, bytes: &[u8]) -> Headers {
    use goblin::elf::dynamic::{DF_1_NOW, DF_1_PIE, DF_BIND_NOW};
    use goblin::elf::header::{ET_CORE, ET_DYN, ET_EXEC, ET_REL};
    use goblin::elf::note::NT_GNU_BUILD_ID;
    use goblin::elf::program_header::{PF_X, PT_GNU_RELRO, PT_GNU_STACK};

    let mut h = Headers::default();
    let (flags, flags_1) = elf
        .dynamic
        .as_ref()
        .map_or((0, 0), |d| (d.info.flags, d.info.flags_1));
    let pie = elf.header.e_type == ET_DYN && (elf.interpreter.is_some() || flags_1 & DF_1_PIE != 0);
    h.kind = Some(match elf.header.e_type {
        ET_EXEC => "ET_EXEC",
        ET_DYN if pie => "ET_DYN (pie)",
        ET_DYN => "ET_DYN (shared object)",
        ET_REL => "ET_REL",
        ET_CORE => "ET_CORE",
        _ => "other",
    });
    h.interpreter = elf.interpreter.map(str::to_owned);
    h.libraries = elf.libraries.iter().map(|l| (*l).to_owned()).collect();
    h.stripped = Some(elf.syms.is_empty());
    // Only an architecture the summary does not already name: x86 (3),
    // x86-64 (62) and AArch64 (183) are named there, so naming them here
    // would just repeat the line.
    let machine = elf.header.e_machine;
    if !matches!(machine, 3 | 62 | 183) {
        h.machine = Some(format!(
            "{} (e_machine {machine})",
            goblin::elf::header::machine_to_str(machine)
        ));
    }

    let mut on: Vec<&'static str> = Vec::new();
    let mut off: Vec<&'static str> = Vec::new();
    let stack = elf
        .program_headers
        .iter()
        .find(|p| p.p_type == PT_GNU_STACK);
    match stack {
        Some(p) if p.p_flags & PF_X == 0 => on.push("nx"),
        _ => off.push("exec-stack"),
    }
    if elf.program_headers.iter().any(|p| p.p_type == PT_GNU_RELRO) {
        on.push("relro");
        if flags & DF_BIND_NOW != 0 || flags_1 & DF_1_NOW != 0 {
            on.push("bind-now");
        }
    } else {
        off.push("no-relro");
    }
    if pie {
        on.push("pie");
    } else if elf.header.e_type == ET_EXEC {
        off.push("no-pie");
    }
    let imports: BTreeSet<&str> = elf
        .dynsyms
        .iter()
        .filter(|s| s.is_import())
        .filter_map(|s| elf.dynstrtab.get_at(s.st_name))
        .collect();
    if imports.contains("__stack_chk_fail") {
        on.push("canary");
    } else if !imports.is_empty() {
        off.push("no-canary");
    }
    if imports
        .iter()
        .any(|n| n.ends_with("_chk") && *n != "__stack_chk_fail")
    {
        on.push("fortify");
    }
    h.mitigations = on;
    h.missing = off;

    let is_build_id = |n: &goblin::elf::note::Note<'_>| {
        n.n_type == NT_GNU_BUILD_ID && n.name.trim_end_matches('\0') == "GNU"
    };
    let build_id = elf
        .iter_note_headers(bytes)
        .into_iter()
        .flatten()
        .flatten()
        .find(is_build_id)
        .or_else(|| {
            elf.iter_note_sections(bytes, Some(".note.gnu.build-id"))
                .into_iter()
                .flatten()
                .flatten()
                .find(is_build_id)
        });
    if let Some(n) = build_id {
        let hex: String = n.desc.iter().map(|b| format!("{b:02x}")).collect();
        h.debug_id = Some(format!("build-id {hex}"));
    }
    h
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{
        manifest_facts, pe_checksum, resource_type_name, rich_header, sniff_file, sniff_section,
    };
    use crate::num::lo8;

    /// A container's magic names it; the base64 an encrypted Electrum
    /// wallet opens with is `BIE1` encoded, and a file of text names nothing.
    #[test]
    fn a_container_is_named_by_its_magic() {
        assert_eq!(sniff_file(b"PK\x03\x04\x14\x00"), Some("zip archive"));
        assert_eq!(sniff_file(b"\x1f\x8b\x08\x00"), Some("gzip stream"));
        assert_eq!(sniff_file(b"\x89PNG\r\n\x1a\n\0\0"), Some("PNG image"));
        assert_eq!(
            sniff_file(b"SQLite format 3\0\x10\0"),
            Some("SQLite database")
        );
        assert!(sniff_file(b"QklFMQAAAAAA").is_some_and(|n| n.contains("BIE1")));
        assert_eq!(sniff_file(b"BZh91AY"), Some("bzip2 stream"));
        assert_eq!(
            sniff_file(b"Rar!\x1a\x07\x01\x00rest"),
            Some("RAR archive (v5)")
        );
        assert_eq!(sniff_file(b"MSCF\0\0\0\0"), Some("Microsoft Cabinet"));
        assert_eq!(
            sniff_file(b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1rest"),
            Some("OLE2 compound file (MSI/DOC/XLS)")
        );
        assert!(sniff_file(b"-----BEGIN CERTIFICATE-----").is_some_and(|n| n.contains("PEM")));
        // `ustar` at offset 257 names a tar even though the file opens with
        // a name field, not a signature.
        let mut tar = vec![0u8; 263];
        tar[257..262].copy_from_slice(b"ustar");
        assert_eq!(sniff_file(&tar), Some("tar archive (ustar)"));
        assert_eq!(sniff_file(b"hello, world"), None);
        assert_eq!(sniff_file(b""), None);
    }

    /// A manifest's privilege and display declarations are read through
    /// their namespace prefixes, and a manifest without them says nothing.
    #[test]
    fn a_manifest_declares_its_privilege_and_display() {
        let xml = br#"<?xml version="1.0"?><assembly xmlns="urn:schemas-microsoft-com:asm.v1">
  <trustInfo xmlns="urn:schemas-microsoft-com:asm.v3"><security><requestedPrivileges>
    <requestedExecutionLevel level="requireAdministrator" uiAccess="false"/>
  </requestedPrivileges></security></trustInfo>
  <asmv3:application xmlns:asmv3="urn:schemas-microsoft-com:asm.v3">
    <asmv3:windowsSettings><asmv3:dpiAware>true/pm</asmv3:dpiAware></asmv3:windowsSettings>
  </asmv3:application></assembly>"#;
        assert_eq!(
            manifest_facts(xml),
            vec![
                ("requestedExecutionLevel", "requireAdministrator".to_owned()),
                ("uiAccess", "false".to_owned()),
                ("dpiAware", "true/pm".to_owned()),
            ]
        );
        assert!(manifest_facts(b"<assembly/>").is_empty());
        assert_eq!(resource_type_name(16), "version");
        assert_eq!(resource_type_name(24), "manifest");
        assert_eq!(resource_type_name(99), "other");
    }

    /// The checksum folds the words, skips its own field, and adds the
    /// length: words 1, 2, (the field), 3 over ten bytes give 6 + 10.
    #[test]
    fn the_checksum_skips_its_own_field_and_adds_the_length() {
        let file = [1, 0, 2, 0, 0xff, 0xff, 0xff, 0xff, 3, 0];
        assert_eq!(pe_checksum(&file, 4), 16);
    }

    /// A Rich record masked under a key reads back to its product, build
    /// and count; a stub without one reads as nothing.
    #[test]
    fn a_rich_header_is_unmasked_and_read() {
        let key = 0x1111_1111u32;
        let mut stub = vec![0u8; 0x80];
        for word in [
            0x536e_6144 ^ key,
            key,
            key,
            key,
            0x0105_7809 ^ key,
            12 ^ key,
            0x0083_7809 ^ key,
            3 ^ key,
        ] {
            stub.extend_from_slice(&word.to_le_bytes());
        }
        stub.extend_from_slice(b"Rich");
        stub.extend_from_slice(&key.to_le_bytes());
        let end = stub.len();
        assert_eq!(
            rich_header(&stub, end),
            vec![(0x105, 30729, 12), (0x83, 30729, 3)]
        );
        assert!(rich_header(&[0u8; 0x80], 0x80).is_empty());
    }

    /// Each DWARF section is named from its own header shape.
    ///
    /// The names of these sections are gone on a rebuilt image, so the bytes
    /// are the only evidence left. Two of the DWARF 5 sections share a header
    /// exactly, and the answer names both rather than picking one.
    #[test]
    fn a_debug_section_is_named_from_its_header() {
        // unit_length, version 2, .debug_info offset, address size, segment
        let aranges = [0x2c, 0, 0, 0, 2, 0, 0, 0, 0, 0, 8, 0];
        assert_eq!(sniff_section(&aranges), Some(".debug_aranges"));
        // unit_length, version 5, unit type, address size, abbrev offset
        let info = [0x40, 0, 0, 0, 5, 0, 1, 8, 0, 0, 0, 0];
        assert_eq!(sniff_section(&info), Some(".debug_info"));
        // the standard opcode lengths a line program header ends with
        let line = [
            0x0c, 4, 0, 0, 5, 0, 8, 0x20, 0, 0, 0, 1, 1, 1, 0xfb, 0x0e, 0x0d,
        ];
        assert_eq!(sniff_section(&line), Some(".debug_line"));
        // a CIE: length, then the id that says which frame section this is
        let eh = [0x14, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0x78];
        assert_eq!(sniff_section(&eh), Some(".eh_frame"));
        let dbg = [0x14, 0, 0, 0, 0xff, 0xff, 0xff, 0xff, 1, 0, 1, 0x78];
        assert_eq!(sniff_section(&dbg), Some(".debug_frame"));
        // declaration code 1, a tag, and whether it has children
        let abbrev = [1, 0x11, 1, 0x25, 0x0e, 0x13, 0x05, 3, 0x0e, 0, 0];
        assert_eq!(sniff_section(&abbrev), Some(".debug_abbrev"));
        // version 5, address size, segment selector, offset entry count
        let rnglists = [0x20, 0, 0, 0, 5, 0, 8, 0, 0, 0, 0, 0];
        assert_eq!(
            sniff_section(&rnglists),
            Some(".debug_rnglists or .debug_loclists")
        );
    }

    /// A table of names reads apart from a table of paths.
    ///
    /// Both are printable text in NUL-terminated runs, and the separators are
    /// what tell the line program's file table from the one holding names.
    #[test]
    fn a_string_table_is_told_from_a_path_table() {
        let names = b"Subsystem\0CheckSum\0SizeOfImage\0BaseOfCode\0";
        assert_eq!(sniff_section(names), Some(".debug_str"));
        let paths = b"/usr/src/mingw-w64/crt/crtexe.c\0/usr/include/stdio.h\0";
        assert_eq!(sniff_section(paths), Some(".debug_line_str or .debug_str"));
    }

    /// Bytes that match nothing are not named.
    #[test]
    fn random_bytes_are_not_named() {
        assert_eq!(sniff_section(&[]), None);
        assert_eq!(sniff_section(&[0xde, 0xad]), None);
        // The sum runs past 255 for some `k`; the wrapped low byte is the noise.
        let noise: Vec<u8> = (0..256u32)
            .map(|k| lo8(u64::from(k * 37 % 251 + 128)))
            .collect();
        assert_eq!(sniff_section(&noise), None);
    }
}
