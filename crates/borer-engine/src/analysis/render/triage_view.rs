//! The one-call triage: what the file is, how it is protected, what it
//! can do, what the report could not see and the functions to read first.

use super::calls::{Reach, gather};
use super::iocs::iocs_line;
use super::*;

/// Answers the first question about a binary in one call.
///
/// The procedure this replaces is ten calls in a fixed order: what format is
/// it, is it packed, what can it do, what does it hide, what crypto is in it,
/// what strings does it build, and which function should be read first. Every
/// one of those answers already exists behind its own tool, and an agent
/// spent ten round trips assembling them before it could start reading code.
///
/// Each section is the headline of the tool that owns it, which is a stable
/// line by convention here, so this composes rather than reimplements. The
/// reading list is computed from evidence and says why each entry is on it:
/// a function that builds a hidden string, holds a keystream's constants, or
/// calls the network and crypto surface is where the program's own logic is.
/// The evidence is weighted, because its kinds are not equally telling: a
/// string a function builds says what it does, a call to the network or
/// crypto surface says what it touches, and a keystream constant only says
/// it obfuscates something, which most of these functions do. An ordinary
/// program has none of that evidence, so the list is filled from what every
/// binary can answer, the strings and imports each function references
/// ([`everyday_reading_list`]), and the header says so.
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
/// A report of a dozen lines, then the functions to read first. Every
/// section reads the whole program, so the report is built once per set
/// of names ([`Analysis::derived`]).
pub fn triage_tsv(p: &Program, a: &Analysis, o: &Overlay) -> String {
    a.derived
        .get_or_build_named("triage", o.fingerprint(), (), || triage_of(p, a, o))
        .as_ref()
        .clone()
}

/// Builds the report [`triage_tsv`] memoizes.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
///
/// # Returns
///
/// As [`triage_tsv`].
fn triage_of(p: &Program, a: &Analysis, o: &Overlay) -> String {
    /// Functions listed to read first.
    const READ_MAX: usize = 10;
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
    /// The first line of a tool's output, which is its summary by convention.
    ///
    /// A headline that repeats the label this report puts in front of it is
    /// trimmed, so the line does not read `anti-analysis: anti-analysis: ...`.
    fn headline<'t>(text: &'t str, label: &str) -> &'t str {
        let line = text.lines().next().unwrap_or("").trim_start_matches("# ");
        line.strip_prefix(label)
            .map_or(line, |rest| rest.trim_start_matches([':', ' ']))
            .trim()
    }
    let mut out = format!(
        "# triage: {}\n",
        p.path.file_name().map_or_else(
            || String::from("<unnamed>"),
            |n| n.to_string_lossy().into_owned()
        )
    );
    let _ = writeln!(
        out,
        "# {} {}, {} bytes, entry {}, {} sections, {} imports, {} exports, {} functions",
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
    );
    if a.incomplete {
        out.push_str(INCOMPLETE_NOTE);
        out.push('\n');
    }
    out.push_str(&crate::fileinfo::triage_lines(p));
    let mut phases = crate::timing::Phases::new();
    let protection = protection_tsv(p, a);
    let _ = writeln!(out, "# protection: {}", headline(&protection, "protection"));
    phases.mark("triage protection");
    let anti = anti_analysis_tsv(p, a, o);
    let _ = writeln!(out, "# anti-analysis: {}", headline(&anti, "anti-analysis"));
    phases.mark("triage anti-analysis");
    let crypto = crypto_tsv(p, a, o, 0, 1);
    let _ = writeln!(out, "# crypto: {}", headline(&crypto, "crypto"));
    phases.mark("triage crypto");
    let dynamic = dynamic_imports_tsv(p, a, o);
    let _ = writeln!(
        out,
        "# dynamic imports: {}",
        headline(&dynamic, "dynamic imports")
    );
    phases.mark("triage dynamic imports");
    let checks = license_checks_tsv(p, a, o);
    let _ = writeln!(out, "# checks: {}", headline(&checks, "checks"));
    phases.mark("triage checks");
    let recovered = recovered_strings(p, a);
    let _ = writeln!(
        out,
        "# generated strings: {} recovered from {} generator(s)",
        recovered.found.len(),
        recovered.generators
    );
    phases.mark("triage generated strings");
    let capabilities = capability_map_tsv(p, Some(a));
    let _ = writeln!(
        out,
        "# capabilities: {}",
        headline(&capabilities, "capabilities")
    );
    for line in capabilities.lines().skip(1).take(6) {
        let _ = writeln!(out, "#   {}", line.trim());
    }
    phases.mark("triage capabilities");
    let _ = writeln!(out, "# iocs: {}", iocs_line(p, a, o));
    phases.mark("triage iocs");
    for spot in blind_spots(p, a, o, headline(&protection, "protection")) {
        let _ = writeln!(out, "# blind spot: {spot}");
    }
    phases.mark("triage blind spots");
    let mut reasons: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    let mut score: BTreeMap<u64, usize> = BTreeMap::new();
    for g in &recovered.found {
        *score.entry(g.built_by).or_default() += WEIGHT_BUILDS;
        let entry = reasons.entry(g.built_by).or_default();
        if entry.len() < 3 {
            entry.push(format!("builds {:?}", g.text));
        }
    }
    for hit in crypto_hits(p, a).hits.iter().take(crate::crypto::HITS_MAX) {
        if let Some(f) = hit.va.and_then(|va| a.function_at(va)) {
            let entry = reasons.entry(f.entry).or_default();
            let note = format!("holds {}{}", hit.name, hit.storage);
            if !entry.contains(&note) {
                *score.entry(f.entry).or_default() += WEIGHT_HOLDS;
                if entry.len() < 4 {
                    entry.push(note);
                }
            }
        }
    }
    for f in &a.functions {
        for callee in &f.callees {
            let Some(name) = a.symbol_at(p, *callee).map(|s| bare_name(&s.name)) else {
                continue;
            };
            if TELLING.iter().any(|t| name.starts_with(t)) {
                let entry = reasons.entry(f.entry).or_default();
                let note = format!("calls {name}");
                if !entry.contains(&note) {
                    *score.entry(f.entry).or_default() += WEIGHT_CALLS;
                    if entry.len() < 4 {
                        entry.push(note);
                    }
                }
            }
        }
    }
    let mut ranked: Vec<(u64, Vec<String>)> = reasons.into_iter().collect();
    rank_reading(a, &score, &mut ranked);
    let telling = ranked.len();
    if telling < READ_MAX {
        let have: BTreeSet<u64> = ranked.iter().map(|r| r.0).collect();
        ranked.extend(everyday_reading_list(p, a, &have, READ_MAX - telling));
    }
    if ranked.is_empty() {
        out.push_str("# read first: nothing stood out; start at the entry point\n");
    } else {
        if telling == 0 {
            out.push_str(
                "# read first: no protection signal fired, so the ranking is by the strings and imports each function references\n",
            );
        } else {
            out.push_str("# read first\n");
        }
        for (entry, why) in ranked.iter().take(READ_MAX) {
            let _ = writeln!(
                out,
                "{entry:<#12x} {:<28} {}",
                short_name(a, o, *entry),
                why.join("; ")
            );
        }
        more_line(&mut out, ranked.len(), READ_MAX, "candidates not listed");
    }
    out.push_str("# next: function_summary(addr), then decompile(addr); emulate/<addr> runs one\n");
    out
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
fn rank_reading(a: &Analysis, score: &BTreeMap<u64, usize>, ranked: &mut [(u64, Vec<String>)]) {
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
/// * `verdict` - The protection report's headline.
///
/// # Returns
///
/// The lines, without their `# blind spot: ` prefix; none for a plain image.
fn blind_spots(p: &Program, a: &Analysis, o: &Overlay, verdict: &str) -> Vec<String> {
    let mut spots: Vec<String> = stub_spot(p, verdict).into_iter().collect();
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
