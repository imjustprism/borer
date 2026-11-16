//! The one-call triage: what the file is, how it is protected, what it
//! can do, what the report could not see and the functions to read first.

use super::calls::{Reach, gather};
use super::*;

/// Most addresses a [`Summary`] keeps.
pub const SUMMARY_AT_MAX: usize = 16;

/// What one report says in its first line, held as the value it is spelled
/// from, so a reader of the summary never reads the report's text back.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Summary {
    /// The report's first line, without its `# `.
    pub headline: String,
    /// How many things the report found: techniques, hits, functions or
    /// marks, as the producer's own docs say.
    pub count: usize,
    /// The addresses the headline is about, ascending and distinct, at most
    /// [`SUMMARY_AT_MAX`]; empty for a report about the file rather than
    /// places in it.
    pub at: Vec<u64>,
    /// How many distinct addresses the headline is about, `at` holding the
    /// lowest of them.
    pub at_total: usize,
}

impl Summary {
    /// Returns a summary of `headline` keeping the lowest
    /// [`SUMMARY_AT_MAX`] distinct addresses of `at`.
    ///
    /// # Arguments
    ///
    /// * `headline` - The first line, without its `# `.
    /// * `count` - How many things the report found.
    /// * `at` - The addresses the headline is about, in any order.
    pub(super) fn new(headline: String, count: usize, at: impl IntoIterator<Item = u64>) -> Self {
        let at: BTreeSet<u64> = at.into_iter().collect();
        Self {
            headline,
            count,
            at_total: at.len(),
            at: at.into_iter().take(SUMMARY_AT_MAX).collect(),
        }
    }
}

/// Functions the reading list names.
const READ_MAX: usize = 10;

/// Capability lines the triage repeats under its capabilities line.
const CAPABILITY_ROWS: usize = 6;

/// A section of the triage: the report whose first line it repeats, with
/// that report's typed verdict where it has one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SectionKind {
    /// The packer and protector marks ([`protection_tsv`]) and their verdict.
    Protection(Packing),
    /// The anti-debug and anti-VM techniques ([`anti_analysis_tsv`]) and
    /// their verdict.
    AntiAnalysis(Resistance),
    /// The crypto and hash constants ([`crypto_tsv`]).
    Crypto,
    /// The imports resolved by name at run time ([`dynamic_imports_tsv`]).
    DynamicImports,
    /// The functions that judge a key or serial ([`license_checks_tsv`]).
    Checks,
    /// The strings generators build when run, which [`hidden_strings_tsv`]
    /// lists; the line counts them and the generators
    /// ([`generated_summary`]), not that report's first line.
    GeneratedStrings,
    /// What the imports and syscalls let the program do
    /// ([`capability_map_tsv`]), with the map's note and rows.
    Capabilities(CapabilityMap),
    /// The indicators the program holds ([`iocs_tsv`]).
    Iocs,
}

impl SectionKind {
    /// Returns the label the triage puts in front of the section's line.
    #[must_use]
    pub const fn label(&self) -> &'static str {
        match self {
            Self::Protection(_) => "protection",
            Self::AntiAnalysis(_) => "anti-analysis",
            Self::Crypto => "crypto",
            Self::DynamicImports => "dynamic imports",
            Self::Checks => "checks",
            Self::GeneratedStrings => "generated strings",
            Self::Capabilities(_) => "capabilities",
            Self::Iocs => "iocs",
        }
    }

    /// Returns the resource that answers more than the section's line.
    ///
    /// # Returns
    ///
    /// The URI, or `None` for the crypto constants, which the
    /// `find_crypto_constants` tool lists and no resource does.
    #[must_use]
    pub const fn uri(&self) -> Option<&'static str> {
        match self {
            Self::Protection(_) => Some("borer://protection"),
            Self::AntiAnalysis(_) => Some("borer://antianalysis"),
            Self::Crypto => None,
            Self::DynamicImports => Some("borer://dynimports"),
            Self::Checks => Some("borer://checks"),
            Self::GeneratedStrings => Some("borer://hidden"),
            Self::Capabilities(_) => Some("borer://capabilities"),
            Self::Iocs => Some("borer://iocs"),
        }
    }
}

/// One section of the triage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TriageSection {
    /// The report it repeats.
    pub kind: SectionKind,
    /// That report's first line, as a value.
    pub summary: Summary,
}

impl TriageSection {
    /// Writes the section's line and, for the capabilities, the first lines
    /// of the map under it.
    ///
    /// A headline that repeats the label in front of it is trimmed, so the
    /// line does not read `anti-analysis: anti-analysis: ...`.
    ///
    /// # Arguments
    ///
    /// * `out` - The report.
    fn spell(&self, out: &mut String) {
        let label = self.kind.label();
        let line = self.summary.headline.as_str();
        let said = line
            .strip_prefix(label)
            .map_or(line, |rest| rest.trim_start_matches([':', ' ']))
            .trim();
        let _ = writeln!(out, "# {label}: {said}");
        if let SectionKind::Capabilities(map) = &self.kind {
            for row in map.body().take(CAPABILITY_ROWS) {
                let _ = writeln!(out, "#   {}", row.trim());
            }
        }
    }
}

/// A function the triage says to read first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadFirst {
    /// The function's entry.
    pub entry: u64,
    /// Its name as the list prints it, without a module prefix.
    pub name: String,
    /// What its evidence weighs; zero for a function listed only for the
    /// strings and imports it references.
    pub score: usize,
    /// Why it is on the list, at most four.
    pub reasons: Vec<Reason>,
}

/// Why a function is on the reading list, with where the engine saw it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reason {
    /// It builds a string a run of the generator recovered.
    Builds {
        /// Where the run wrote the text.
        written_at: u64,
        /// The recovered text.
        text: String,
    },
    /// It calls a function of the network, crypto or injection surface.
    Calls {
        /// The callee: an import's slot, or a function the symbol tables
        /// name.
        callee: u64,
        /// The callee's name, without its module.
        name: String,
    },
    /// It holds a cipher's or keystream's constant.
    Holds {
        /// Where the constant sits.
        at: u64,
        /// The constant's signature name.
        name: &'static str,
        /// How the constant is stored.
        storage: crate::crypto::Storage,
    },
    /// It references many strings and imports, on a list no other evidence
    /// filled.
    References {
        /// Distinct string literals it references.
        strings: usize,
        /// Distinct imports it references or calls through a thunk.
        imports: usize,
    },
}

/// How the engine knows a [`Reason`]: a reading of what it did, not a
/// confidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Basis {
    /// The emulator ran the code and saw the result: a permissive run,
    /// where a read of unmapped memory answers zero, that may have begun
    /// at a block inside the function rather than its entry, so what it
    /// saw is what that run did, not every run the program makes.
    Observed,
    /// The code's calls and references say it, without running it.
    Static,
    /// Bytes matched a known constant's signature.
    Pattern,
}

impl Reason {
    /// Returns how the engine knows this reason.
    #[must_use]
    pub const fn basis(&self) -> Basis {
        match self {
            Self::Builds { .. } => Basis::Observed,
            Self::Calls { .. } | Self::References { .. } => Basis::Static,
            Self::Holds { .. } => Basis::Pattern,
        }
    }
}

impl std::fmt::Display for Reason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Builds { text, .. } => write!(f, "builds {text:?}"),
            Self::Calls { name, .. } => write!(f, "calls {name}"),
            Self::Holds { name, storage, .. } => write!(f, "holds {name}{storage}"),
            Self::References { strings, imports } => {
                write!(f, "references {strings} strings and {imports} imports")
            }
        }
    }
}

/// The triage of a program with code, as the values its text is spelled
/// from ([`Triage::spell`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Triage {
    /// The file's name.
    pub name: String,
    /// The format, architecture and counts line, without its `# `.
    pub shape: String,
    /// Whether discovery ran out of budget, so lists may be short.
    pub incomplete: bool,
    /// The lines about the file before its code
    /// ([`crate::fileinfo::triage_lines`]), each with its `# `.
    pub file: Vec<String>,
    /// The sections, in the order the text prints them.
    pub sections: Vec<TriageSection>,
    /// What the report could not see, each without its `# blind spot: `.
    pub blind_spots: Vec<String>,
    /// The functions to read first, at most [`READ_MAX`], the first first.
    pub read_first: Vec<ReadFirst>,
    /// How many functions the list ranked, listed or not: every one with
    /// evidence, then of the rest only enough to fill [`READ_MAX`].
    pub candidates: usize,
}

impl Triage {
    /// Returns the text [`triage_tsv`] answers.
    #[must_use]
    pub fn spell(&self) -> String {
        let mut out = format!("# triage: {}\n# {}\n", self.name, self.shape);
        if self.incomplete {
            out.push_str(INCOMPLETE_NOTE);
            out.push('\n');
        }
        for line in &self.file {
            let _ = writeln!(out, "{line}");
        }
        for section in &self.sections {
            section.spell(&mut out);
        }
        for spot in &self.blind_spots {
            let _ = writeln!(out, "# blind spot: {spot}");
        }
        match self.read_first.first() {
            None => out.push_str("# read first: nothing stood out; start at the entry point\n"),
            Some(first) if first.score == 0 => out.push_str(
                "# read first: no protection signal fired, so the ranking is by the strings and imports each function references\n",
            ),
            Some(_) => out.push_str("# read first\n"),
        }
        for r in &self.read_first {
            let why: Vec<String> = r.reasons.iter().map(Reason::to_string).collect();
            let _ = writeln!(out, "{:<#12x} {:<28} {}", r.entry, r.name, why.join("; "));
        }
        if !self.read_first.is_empty() {
            more_line(&mut out, self.candidates, READ_MAX, "candidates not listed");
        }
        out.push_str(
            "# next: function_summary(addr), then decompile(addr); emulate/<addr> runs one\n",
        );
        out
    }
}

/// Answers the first question about a binary in one call.
///
/// The procedure this replaces is ten calls in a fixed order: what format is
/// it, is it packed, what can it do, what does it hide, what crypto is in it,
/// what strings does it build, and which function should be read first. Every
/// one of those answers already exists behind its own tool, and an agent
/// spent ten round trips assembling them before it could start reading code.
///
/// Each section is the summary of the report that owns it, the value that
/// report spells its own first line from, so this composes rather than
/// reimplements. The reading list is computed from evidence and says why
/// each entry is on it ([`reading_list`]).
///
/// An `iocs` line counts the indicators by kind ([`iocs_tsv`] lists them),
/// and a `blind spot` line says each thing the report could not see
/// ([`blind_spots`]): a confident "nothing found" on a packed or thin
/// sample is the most dangerous answer a triage gives.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
///
/// # Returns
///
/// The triage. Every section reads the whole program, so it is built once
/// per set of names ([`Analysis::derived`]).
pub fn triage(p: &Program, a: &Analysis, o: &Overlay) -> Arc<Triage> {
    a.derived
        .get_or_build_named("triage", o.fingerprint(), (), || triage_of(p, a, o))
}

/// Answers the first question about a binary in one call, as text.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
///
/// # Returns
///
/// A report of a dozen lines, then the functions to read first: the
/// spelling of [`triage()`].
pub fn triage_tsv(p: &Program, a: &Analysis, o: &Overlay) -> String {
    triage(p, a, o).spell()
}

/// Builds the triage [`triage()`] memoizes.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
fn triage_of(p: &Program, a: &Analysis, o: &Overlay) -> Triage {
    let section = |kind, summary| TriageSection { kind, summary };
    let mut phases = crate::timing::Phases::new();
    let protection = protection_of(p, a);
    let mut sections = vec![section(
        SectionKind::Protection(protection.packing.clone()),
        protection.summary(),
    )];
    phases.mark("triage protection");
    let (resistance, anti) = anti_analysis(p, a);
    sections.push(section(SectionKind::AntiAnalysis(resistance), anti));
    phases.mark("triage anti-analysis");
    sections.push(section(SectionKind::Crypto, crypto_summary(p, a)));
    phases.mark("triage crypto");
    sections.push(section(
        SectionKind::DynamicImports,
        dynamic_imports_summary(p, a, o),
    ));
    phases.mark("triage dynamic imports");
    sections.push(section(
        SectionKind::Checks,
        license_checks_summary(p, a, o),
    ));
    phases.mark("triage checks");
    sections.push(section(
        SectionKind::GeneratedStrings,
        generated_summary(p, a),
    ));
    phases.mark("triage generated strings");
    let (capabilities, map) = capability_map(p, Some(a));
    sections.push(section(SectionKind::Capabilities(map), capabilities));
    phases.mark("triage capabilities");
    sections.push(section(SectionKind::Iocs, iocs_summary(p, a, o)));
    phases.mark("triage iocs");
    let blind_spots = blind_spots(p, a, o, &protection.packing);
    phases.mark("triage blind spots");
    let (read_first, candidates) = reading_list(p, a, o, &recovered_strings(p, a));
    Triage {
        name: p.path.file_name().map_or_else(
            || String::from("<unnamed>"),
            |n| n.to_string_lossy().into_owned(),
        ),
        shape: shape(p, a),
        incomplete: a.incomplete,
        file: crate::fileinfo::triage_lines(p)
            .split_terminator('\n')
            .map(str::to_owned)
            .collect(),
        sections,
        blind_spots,
        read_first,
        candidates,
    }
}

/// The triage's line on the file's format, architecture and counts.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for its function count.
fn shape(p: &Program, a: &Analysis) -> String {
    format!(
        "{} {}, {} bytes, entry {}, {} sections, {} imports, {} exports, {} functions",
        p.format.name(),
        p.arch.name(),
        p.bytes.len(),
        hex_or_dash(p.entry),
        p.sections.len(),
        p.symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import)
            .count(),
        p.symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::Export | SymbolKind::Forwarder))
            .count(),
        a.functions.len()
    )
}

/// Ranks the functions to read first by the evidence each one carries.
///
/// A function that builds a hidden string, holds a keystream's constants,
/// or calls the network and crypto surface is where the program's own
/// logic is. The evidence is weighted, because its kinds are not equally
/// telling: a string a function builds says what it does, a call to the
/// network or crypto surface says what it touches, and a keystream
/// constant only says it obfuscates something, which most of these
/// functions do. An ordinary program has none of that evidence, so the
/// list is filled from what every binary can answer, the strings and
/// imports each function references ([`everyday_reading_list`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `recovered` - The strings the generators build ([`recovered_strings`]).
///
/// # Returns
///
/// The first [`READ_MAX`] functions, ranked, and how many were ranked
/// ([`Triage::candidates`]).
fn reading_list(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    recovered: &Recovery,
) -> (Vec<ReadFirst>, usize) {
    /// Imports whose use marks a function as the program's own logic rather
    /// than its runtime: what it talks to, what it encrypts, what it injects.
    const TELLING: [&str; 24] = [
        "InternetOpen",
        "InternetConnect",
        "HttpSendRequest",
        "HttpOpenRequest",
        "InternetReadFile",
        "WinHttpOpen",
        "WinHttpSendRequest",
        "socket",
        "connect",
        "send",
        "recv",
        "BCryptEncrypt",
        "BCryptDecrypt",
        "BCryptCreateHash",
        "BCryptGenerateSymmetricKey",
        "CryptEncrypt",
        "CryptDecrypt",
        "WriteProcessMemory",
        "ReadProcessMemory",
        "VirtualAllocEx",
        "CreateRemoteThread",
        "NtCreateThreadEx",
        "OpenProcess",
        "CreateProcess",
    ];
    /// Score for a recovered string the function builds.
    const WEIGHT_BUILDS: usize = 4;
    /// Score for a call into the telling import surface.
    const WEIGHT_CALLS: usize = 3;
    /// Score for holding a cipher or keystream constant.
    const WEIGHT_HOLDS: usize = 1;
    let mut reasons: BTreeMap<u64, Vec<Reason>> = BTreeMap::new();
    let mut score: BTreeMap<u64, usize> = BTreeMap::new();
    for g in &recovered.found {
        *score.entry(g.built_by).or_default() += WEIGHT_BUILDS;
        let entry = reasons.entry(g.built_by).or_default();
        if entry.len() < 3 {
            entry.push(Reason::Builds {
                written_at: g.written_at,
                text: g.text.clone(),
            });
        }
    }
    for hit in crypto_hits(p, a).hits.iter().take(crate::crypto::HITS_MAX) {
        if let Some((at, f)) = hit.va.and_then(|va| a.function_at(va).map(|f| (va, f))) {
            let entry = reasons.entry(f.entry).or_default();
            let held = |r: &Reason| matches!(r, Reason::Holds { name, storage, .. } if *name == hit.name && *storage == hit.storage);
            if !entry.iter().any(held) {
                *score.entry(f.entry).or_default() += WEIGHT_HOLDS;
                if entry.len() < 4 {
                    entry.push(Reason::Holds {
                        at,
                        name: hit.name,
                        storage: hit.storage,
                    });
                }
            }
        }
    }
    for f in &a.functions {
        for callee in &f.callees {
            let Some(name) = called_import(p, a, *callee) else {
                continue;
            };
            if TELLING.iter().any(|t| name.starts_with(t)) {
                let entry = reasons.entry(f.entry).or_default();
                let called = |r: &Reason| matches!(r, Reason::Calls { name: n, .. } if n == name);
                if !entry.iter().any(called) {
                    *score.entry(f.entry).or_default() += WEIGHT_CALLS;
                    if entry.len() < 4 {
                        entry.push(Reason::Calls {
                            callee: *callee,
                            name: name.to_owned(),
                        });
                    }
                }
            }
        }
    }
    let mut ranked: Vec<(u64, Vec<Reason>)> = reasons.into_iter().collect();
    rank_reading(a, &score, &mut ranked);
    let telling = ranked.len();
    if telling < READ_MAX {
        let have: BTreeSet<u64> = ranked.iter().map(|r| r.0).collect();
        ranked.extend(everyday_reading_list(p, a, &have, READ_MAX - telling));
    }
    let candidates = ranked.len();
    let listed = ranked
        .into_iter()
        .take(READ_MAX)
        .map(|(entry, reasons)| ReadFirst {
            entry,
            name: short_name(a, o, entry),
            score: score.get(&entry).copied().unwrap_or(0),
            reasons,
        })
        .collect();
    (listed, candidates)
}

/// Returns the name a call to `callee` reaches: its symbol, or the import
/// it jumps to when it is an import thunk.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `callee` - A call target's address.
///
/// # Returns
///
/// The bare name, `None` when no symbol names the target.
fn called_import<'p>(p: &'p Program, a: &Analysis, callee: u64) -> Option<&'p str> {
    a.symbol_at(p, callee)
        .or_else(|| a.symbol_at(p, a.function(callee)?.thunk?))
        .map(|s| bare_name(&s.name))
}

/// Orders the reading list so a function left mostly unchecked is not first.
///
/// The checker stops at [`ANSWER_BLOCKS`](crate::analysis::decompile::replay::ANSWER_BLOCKS).
/// More than twice that many blocks means most of the function was not
/// checked. Those sort after every function the checker can cover. Score,
/// then address, still orders each group.
///
/// # Arguments
///
/// * `a` - The analysis, for each function's blocks.
/// * `score` - The rank each entry earned.
/// * `ranked` - The candidates, sorted in place.
fn rank_reading(a: &Analysis, score: &BTreeMap<u64, usize>, ranked: &mut [(u64, Vec<Reason>)]) {
    let limit = 2 * crate::analysis::decompile::replay::ANSWER_BLOCKS;
    let open = |e: u64| a.function(e).is_some_and(|f| f.blocks.len() > limit);
    ranked.sort_by(|l, r| {
        open(l.0).cmp(&open(r.0)).then_with(|| {
            let ls = score.get(&l.0).copied().unwrap_or(0);
            let rs = score.get(&r.0).copied().unwrap_or(0);
            rs.cmp(&ls).then(l.0.cmp(&r.0))
        })
    });
}

/// Least file bytes a section needs before its entropy or its lack of code
/// is worth a line: below it, a section is a stub's padding or a handful
/// of constants.
const SPOT_SECTION_MIN: u64 = 0x200;

/// Says what the triage could not see, one line each, so a quiet report on
/// a packed or thin sample is not read as a clean one.
///
/// Each line fires on a signal already computed and names what it hides:
/// a packed verdict (what the report describes is the stub, or for an
/// image already unpacked the stub's few imports: [`stub_spot`]), sections at
/// packed entropy (read as neither code nor text), executable sections with
/// no function found in them, an import table too thin to run a program (or
/// none, for a static image), `GetProcAddress` calls whose name argument
/// the decompiler cannot read (the imports they resolve stay unseen), TLS
/// callbacks (they run before the entry point, which emulation starts
/// from) and .NET metadata (managed code is not machine code).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force, which the decompiled callers are read under.
/// * `packing` - The protection report's verdict.
///
/// # Returns
///
/// The lines, without their `# blind spot: ` prefix; none for a plain image.
fn blind_spots(p: &Program, a: &Analysis, o: &Overlay, packing: &Packing) -> Vec<String> {
    let mut spots: Vec<String> = stub_spot(p, packing).into_iter().collect();
    let sized = || {
        p.sections
            .iter()
            .filter(|s| s.file_size >= SPOT_SECTION_MIN)
    };
    let dense: Vec<&str> = sized()
        .filter(|s| {
            let len = usize::try_from(s.file_size).unwrap_or(0);
            p.read_va(s.va.0, len)
                .is_some_and(|b| crate::entropy::shannon(b) >= PACKED_ENTROPY)
        })
        .map(|s| s.name.as_str())
        .collect();
    if !dense.is_empty() {
        spots.push(format!(
            "{} section{} at entropy {PACKED_ENTROPY:.1} or above ({}): compressed or encrypted bytes, read as neither code nor text until unpacked",
            dense.len(),
            plural(dense.len()),
            dense.join(", ")
        ));
    }
    let bare: Vec<&str> = sized()
        .filter(|s| s.executable)
        .filter(|s| {
            let end = s.va.0.saturating_add(s.vsize.max(s.file_size));
            !a.functions
                .iter()
                .any(|f| f.entry >= s.va.0 && f.entry < end)
        })
        .map(|s| s.name.as_str())
        .collect();
    if !bare.is_empty() {
        spots.push(format!(
            "{} executable section{} with no function found ({}): code reached only by a computed jump, or bytes that are not code, were not read",
            bare.len(),
            plural(bare.len()),
            bare.join(", ")
        ));
    }
    let imports = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .count();
    let sites = crate::analysis::syscalls::syscall_sites(p, a);
    let unresolved = sites.iter().filter(|s| s.nr.is_none()).count();
    match p.format {
        BinaryFormat::Raw | BinaryFormat::Archive => {}
        BinaryFormat::Elf | BinaryFormat::MachO if imports == 0 && !sites.is_empty() => {
            spots.push(format!(
                "no imports (statically linked): capabilities come from {} syscall site{} alone, and the {unresolved} whose number is set outside its block name nothing",
                sites.len(),
                plural(sites.len()),
            ));
        }
        BinaryFormat::Elf | BinaryFormat::MachO if imports == 0 => spots.push(
            "no imports (statically linked): capabilities, read from import names, say nothing about this file".to_owned(),
        ),
        BinaryFormat::Pe | BinaryFormat::Elf | BinaryFormat::MachO if imports < THIN_IMPORTS => {
            spots.push(format!(
                "{imports} import{} only: capabilities are likely understated; what the program resolves at runtime is seen only as far as borer://dynimports recovers its names",
                plural(imports)
            ));
        }
        BinaryFormat::Pe | BinaryFormat::Elf | BinaryFormat::MachO => {}
    }
    if let Some((unread, total)) = unread_lookups(p, a, o)
        && unread > 0
    {
        spots.push(format!(
            "{unread} of {total} GetProcAddress call{} {} a name the decompiler cannot read (computed, hashed or decrypted): the imports resolved there stay unseen",
            plural(total),
            if unread == 1 { "passes" } else { "pass" }
        ));
    }
    let tls = p.headers.tls_callbacks.len();
    if tls > 0 {
        spots.push(format!(
            "{tls} TLS callback{} run before the entry point: emulation from the entry (unpack, emulate/<entry>) skips {}",
            plural(tls),
            if tls == 1 { "it" } else { "them" }
        ));
    }
    if p.headers.directories.contains(&"clr") {
        spots.push(
            ".NET metadata: managed methods are CIL, which borer does not disassemble; only the native code is read".to_owned(),
        );
    }
    spots
}

/// Counts the `GetProcAddress` calls whose name argument the decompiler
/// cannot read: not a string literal, not the address of a string (one in
/// a code section prints as its address), and not an ordinal.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
///
/// # Returns
///
/// `(unread, total)` call sites, or `None` when the program does not
/// import `GetProcAddress` or does not decompile.
fn unread_lookups(p: &Program, a: &Analysis, o: &Overlay) -> Option<(usize, usize)> {
    /// Most callers decompiled for the count.
    const CALLERS: usize = 100;
    /// Values below this passed as the name are ordinals.
    const ORDINAL_END: u64 = 0x1_0000;
    if p.refuses(Feature::Decompile).is_some() {
        return None;
    }
    let sym = p.symbols.iter().find(|s| {
        s.kind == SymbolKind::Import && s.addr != 0 && bare_name(&s.name) == "GetProcAddress"
    })?;
    let reach = Reach::import(a, sym.addr, &sym.name);
    let found = gather(p, a, o, &reach, CALLERS).found;
    let unread = found
        .iter()
        .filter(|f| {
            f.site.as_ref().is_none_or(|s| {
                s.args.get(1).is_none_or(|n| {
                    n.string.is_none()
                        && n.value
                            .is_none_or(|v| v >= ORDINAL_END && cstr_at(p, v, 2, 256).is_none())
                })
            })
        })
        .count();
    Some((unread, found.len()))
}
