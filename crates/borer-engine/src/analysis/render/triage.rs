//! Program triage: capabilities from imports, emulation runs, crypto constants
//! and the one-call overview.

use super::calls::{Reach, gather};
use super::iocs::iocs_line;
use super::*;

/// A capability and the API-name fragments that give it away.
///
/// This is defensive triage: borer reads the import table of the file under
/// analysis and tags each behavior an analyst would want to notice — the same
/// capability-labeling an antivirus, a YARA ruleset, or a sandbox report does.
/// The category names (`process injection`, `anti-debug`, …) describe what the
/// *inspected sample* is built to do, from the Win32 APIs it imports; borer
/// itself never calls any of them. Recognizing that a binary imports
/// `WriteProcessMemory`/`CreateRemoteThread` is how a triage tool says "this
/// looks like a code injector" — it is a read over static bytes, not an action.
///
/// Each fragment is matched case-insensitively against the imported API
/// name, so `WriteProcessMemory` lands under process injection whichever DLL
/// exports it. A fragment written `=name` must equal the whole API name,
/// which the short socket verbs need so `send` does not catch `SendMessage`.
/// The list leans on the fragments a Windows program cannot avoid for a
/// behavior, and stays deliberately short of guessing. A framework's
/// network classes count as well: a Qt or OpenSSL client never touches a
/// socket API of its own.
pub(super) const CAPABILITIES: [(&str, &[&str]); 16] = [
    (
        "networking",
        &[
            "=socket",
            "=connect",
            "=recv",
            "=send",
            "=recvfrom",
            "=sendto",
            "=bind",
            "=listen",
            "=accept",
            "=closesocket",
            "wsastartup",
            "wsasocket",
            "wsaconnect",
            "internetopen",
            "internetconnect",
            "httpsend",
            "httpopen",
            "urldownload",
            "winhttp",
            "getaddrinfo",
            "gethostby",
            "inet_",
            "qnetworkaccessmanager",
            "qnetworkrequest",
            "qtcpsocket",
            "qudpsocket",
            "qsslsocket",
            "qhostinfo",
            "curl_easy",
            "curl_multi",
            "ssl_connect",
            "ssl_read",
            "ssl_write",
        ],
    ),
    (
        "code integrity",
        &[
            "winverifytrust",
            "wintrust",
            "cryptcatadmin",
            "certverifycertificatechainpolicy",
            "certgetcertificatechain",
            "imagegetcertificatedata",
        ],
    ),
    (
        "process injection",
        &[
            "writeprocessmemory",
            "virtualallocex",
            "createremotethread",
            "openprocess",
            "ntunmapviewofsection",
            "queueuserapc",
            "setthreadcontext",
            "getthreadcontext",
            "ntmapviewofsection",
            "rtlcreateuserthread",
        ],
    ),
    (
        "process control",
        &[
            "createprocess",
            "shellexecute",
            "winexec",
            "terminateprocess",
            "openprocesstoken",
        ],
    ),
    (
        "memory protection",
        &[
            "virtualalloc",
            "virtualprotect",
            "virtualfree",
            "ntprotectvirtualmemory",
            "heapcreate",
        ],
    ),
    (
        "dynamic api resolution",
        &[
            "loadlibrary",
            "getprocaddress",
            "ldrgetprocedureaddress",
            "ldrloaddll",
        ],
    ),
    (
        "cryptography",
        &[
            "crypt",
            "bcrypt",
            "ncrypt",
            "cryptacquire",
            "cryptencrypt",
            "cryptdecrypt",
            "cngget",
        ],
    ),
    (
        "persistence",
        &[
            "regsetvalue",
            "regcreatekey",
            "createservice",
            "startservice",
            "regsetkeyvalue",
        ],
    ),
    (
        "privilege escalation",
        &[
            "adjusttokenprivileges",
            "lookupprivilege",
            "impersonate",
            "duplicatetoken",
        ],
    ),
    (
        "anti-analysis",
        &[
            "isdebuggerpresent",
            "checkremotedebugger",
            "ntqueryinformationprocess",
            "outputdebugstring",
            "queryperformancecounter",
            "ntsetinformationthread",
            "getthreadcontext",
            "blockinput",
        ],
    ),
    (
        "keylogging",
        &[
            "getasynckeystate",
            "setwindowshookex",
            "getkeystate",
            "registerrawinput",
            "getkeyboardstate",
        ],
    ),
    (
        "screen capture",
        &[
            "bitblt",
            "getdc",
            "createcompatiblebitmap",
            "getdibits",
            "printwindow",
        ],
    ),
    (
        "clipboard",
        &["openclipboard", "getclipboarddata", "setclipboarddata"],
    ),
    (
        "filesystem",
        &[
            "createfile",
            "writefile",
            "readfile",
            "deletefile",
            "movefile",
            "copyfile",
            "findfirstfile",
        ],
    ),
    (
        "host reconnaissance",
        &[
            "getcomputername",
            "getusername",
            "getsysteminfo",
            "getvolumeinformation",
            "gethostname",
        ],
    ),
    (
        "service and driver",
        &[
            "openscmanager",
            "ntloaddriver",
            "createservice",
            "devicecontrol",
            "deviceiocontrol",
        ],
    ),
];

/// Groups the imports into the capabilities they grant.
///
/// The one question asked of an unknown binary before any other is what it
/// can do, and the imports answer most of it: a program that resolves
/// sockets talks on the network, one that writes another process's memory
/// injects into it. This lists every capability at least one import gives,
/// with the imports that give it, so a reader sees the program's reach in one
/// screen. It does not judge intent: memory protection is an unpacker and a
/// JIT alike.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// The capabilities, each with its imports, the fullest first.
pub fn capability_map_tsv(p: &Program) -> String {
    let imports: Vec<&str> = p
        .symbols
        .iter()
        .filter(|s| matches!(s.kind, SymbolKind::Import))
        .map(|s| s.name.as_str())
        .collect();
    let mut hits: Vec<(&str, Vec<&str>)> = Vec::new();
    for (capability, fragments) in CAPABILITIES {
        let mut named: BTreeSet<&str> = BTreeSet::new();
        for import in &imports {
            let api = bare_name(import).to_lowercase();
            if fragments.iter().any(|frag| match frag.strip_prefix('=') {
                Some(exact) => api == exact,
                None => api.contains(frag),
            }) {
                named.insert(import);
            }
        }
        if !named.is_empty() {
            hits.push((capability, named.into_iter().collect()));
        }
    }
    hits.sort_by_key(|(cap, named)| (std::cmp::Reverse(named.len()), *cap));
    let mut out = format!(
        "# {} of {} capabilities present across {} imports\n",
        hits.len(),
        CAPABILITIES.len(),
        imports.len()
    );
    if imports.len() < 12 {
        out.push_str("# few imports: the rest are likely resolved at runtime, so this understates the reach\n");
    }
    for (capability, named) in &hits {
        let shown: Vec<&str> = named.iter().take(6).map(|n| bare_name(n)).collect();
        let more = if named.len() > shown.len() {
            format!(", +{}", named.len() - shown.len())
        } else {
            String::new()
        };
        let _ = writeln!(out, "{capability:<24}  {}{more}", shown.join(", "));
    }
    out
}

/// Resolves a function name or address string to an entry address.
///
/// `0x`-hex is an address; any other text is a function's name before it
/// is a number, as [`crate::analysis::resolve`] reads it.
///
/// # Arguments
///
/// * `a` - The analysis, for its functions.
/// * `o` - User names.
/// * `target` - A `0x`-hex address, decimal, or a function name.
///
/// # Returns
///
/// The entry address, or `None` when nothing matches.
pub(super) fn resolve(a: &Analysis, o: &Overlay, target: &str) -> Option<u64> {
    let number =
        parse_addr(target).filter(|&va| a.function(va).is_some() || a.function_at(va).is_some());
    if crate::analysis::hex_prefixed(target) && number.is_some() {
        return number;
    }
    a.functions
        .iter()
        .find(|f| name_of(a, o, f.entry) == target)
        .map(|f| f.entry)
        .or(number)
}

/// Instructions the emulator runs before giving up on a routine.
pub(super) const EMULATE_BUDGET: usize = 200_000;

/// Shortest decoded run reported from an emulation.
pub(super) const EMULATE_STRING_LEN: usize = 5;

/// Runs the emulator from `target` and reports the outcome and any text it
/// wrote.
///
/// A self-contained decoder, the kind a crypter puts in front of its strings,
/// reads an embedded buffer and writes the plaintext; running it is the exact
/// way to read that plaintext, with no key to guess. With nothing set it runs
/// from the given address with zeroed registers, which suits a decoder that
/// carries its own pointers. `target` can instead carry a whole experiment
/// (see [`ExperimentSpec`]): set registers and arguments, write bytes to set
/// up data or patch an instruction out, halt at an address and read the state
/// there. A routine that needs state nothing set stops and says so rather
/// than inventing an answer.
///
/// A register name that sets nothing stops the run instead of being echoed
/// in the header as a setting that was applied, since the run would answer
/// a different question than the one asked. A start that neither the image
/// nor a `w` directive backs is refused before the run, which would only
/// fault on its first fetch. An address inside a function is reported as
/// that function at an offset, not as a function of its own.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, to resolve a name to an address.
/// * `o` - User names.
/// * `target` - The experiment spec: an address or name, then directives.
///
/// # Returns
///
/// The stop reason, the step count, and the printable runs among the bytes
/// written.
///
/// # Errors
///
/// When the spec does not read, the start is unmapped, a register cannot
/// be set, or the architecture is not emulated.
pub fn emulate_tsv(p: &Program, a: &Analysis, o: &Overlay, target: &str) -> Result<String, String> {
    /// API calls named in the header before the rest are counted.
    const CALLS_MAX: usize = 24;
    let spec = ExperimentSpec::parse(a, o, target)?;
    let mut emu =
        Emulator::new(p, spec.budget).ok_or_else(|| String::from("unknown architecture"))?;
    emu.install_imports();
    emu.stop_at(spec.stop);
    emu.set_trace(spec.trace);
    emu.set_profile(spec.profile > 0);
    for &(ref reg, v) in &spec.regs {
        if !emu.set_register(reg, v) {
            return Err(format!(
                "{} is not a register this can set; use rax..r15, rsp, or aN for the argument the decompiler names aN (a1 is the first)",
                crate::text::one_line(reg)
            ));
        }
    }
    for &(i, v) in &spec.args {
        emu.set_arg(i, v);
    }
    for &(addr, ref bytes) in &spec.writes {
        poke_all(&mut emu, addr, bytes);
    }
    if emu.code_at(spec.entry, 1).is_empty() {
        return Err(format!(
            "nothing is mapped at {:#x}; start in the image, or write code there first with w<addr>=<hex>",
            spec.entry
        ));
    }
    let run = emu.run(spec.entry);
    let ran = match a.function_at(spec.entry) {
        Some(f) if f.entry != spec.entry => {
            format!("{}+{:#x}", name_of(a, o, f.entry), spec.entry - f.entry)
        }
        _ => name_of(a, o, spec.entry),
    };
    let mut out = format!(
        "# ran {} from {:#x}{}: {} after {} steps, {} bytes written\n",
        ran,
        spec.entry,
        spec.setup_note(),
        run.stop,
        run.steps,
        run.written
    );
    out.push_str("# registers: ");
    out.push_str(
        &emu.registers()
            .iter()
            .map(|(n, v)| format!("{n}={v:#x}"))
            .collect::<Vec<_>>()
            .join(" "),
    );
    out.push('\n');
    if matches!(run.stop, Stop::Budget) {
        let at = emu.last_ip();
        let _ = writeln!(out, "# at: {at:#x}{}", where_in(a, o, at));
    }
    if spec.profile > 0 {
        let (hot, pages) = emu.profile(spec.profile);
        out.push_str("# hot: where control landed, times\n");
        for (at, n) in hot {
            let _ = writeln!(out, "{at:#x}  {n}{}", where_in(a, o, at));
        }
        out.push_str("# read off the stack: pages, loads each, first loader\n");
        for run in pages {
            let section = p
                .section_at(run.first)
                .map_or_else(String::new, |s| format!("  {}", s.name));
            let _ = writeln!(
                out,
                "{:#x}..{:#x}  {}  by {:#x}{}{section}",
                run.first,
                run.end(),
                run.each,
                run.by,
                where_in(a, o, run.by)
            );
        }
    }
    if let Some(value) = spec.origin {
        match emu.origin() {
            Some((at, instr)) => {
                let _ = writeln!(out, "# origin of {value:#x}: {at:#x}  {instr}");
            }
            None => {
                let _ = writeln!(
                    out,
                    "# origin of {value:#x}: the value never appeared in a register or memory"
                );
            }
        }
    }
    let calls = emu.api_calls();
    if !calls.is_empty() {
        let shown: Vec<&str> = calls.iter().take(CALLS_MAX).map(String::as_str).collect();
        let _ = writeln!(
            out,
            "# calls: {}{}",
            shown.join(" -> "),
            plus_more(calls.len(), CALLS_MAX)
        );
    }
    let neutralized = emu.neutralized();
    if !neutralized.is_empty() {
        let _ = writeln!(
            out,
            "# answered as an unwatched process: {}",
            neutralized.join(", ")
        );
    }
    let traced = emu.trace();
    if !traced.is_empty() {
        out.push_str("# trace: address, instruction, registers it changed\n");
        for line in traced {
            let _ = writeln!(out, "{line}");
        }
    }
    let runs = written_text(&run.history, EMULATE_STRING_LEN);
    if !runs.is_empty() {
        out.push_str("# decoded text\n");
        for (addr, text) in &runs {
            let _ = writeln!(out, "{addr:<#15x} {text:?}");
        }
    }
    for &(addr, len, asked) in &spec.dumps {
        let bytes: Vec<Option<u8>> = (0..len)
            .map(|k| emu.byte_at(addr.wrapping_add(from_usize(k))))
            .collect();
        let _ = write!(
            out,
            "# dump {addr:#x}..{:#x}",
            addr.saturating_add(from_usize(len))
        );
        if len < asked {
            let _ = write!(
                out,
                ", {len} of the {asked} bytes asked: a dump reads at most {DUMP_MAX} and stops at the end of memory"
            );
        }
        if bytes.contains(&None) {
            out.push_str(", ?? where nothing is mapped");
        }
        out.push('\n');
        out.push_str(&crate::hexdump::hexdump_sparse(&bytes, addr));
    }
    Ok(out)
}

/// Names the function an address falls in, as `  (name+0xoff)`, or nothing
/// when no discovered function holds it: a profile row or a stop address
/// read against the function list without a second lookup.
fn where_in(a: &Analysis, o: &Overlay, at: u64) -> String {
    a.function_at(at).map_or_else(String::new, |f| {
        if f.entry == at {
            format!("  ({})", name_of(a, o, f.entry))
        } else {
            format!("  ({}+{:#x})", name_of(a, o, f.entry), at - f.entry)
        }
    })
}

/// One algorithm's constant hits, with where they were found.
pub(super) struct Group {
    /// The algorithm's leading name word, the group's key.
    pub(super) family: &'static str,
    /// How many constants of this algorithm were found.
    pub(super) sites: usize,
    /// Entry addresses of the functions holding them.
    pub(super) owners: Vec<u64>,
    /// Sections holding the hits that no function covers: a cipher's tables.
    pub(super) sections: Vec<String>,
}

/// Renders the crypto constant hits grouped by algorithm and by function.
///
/// A protected binary repeats one generator's constants at every site it
/// obfuscates a string, so the flat table is mostly one algorithm listed
/// three rows at a time: 132 of the target's 141 hits are the same three
/// splitmix64 constants across 36 functions. The group answers the question
/// the table buries, how many distinct generators there are and where they
/// live, and the rows stay underneath for anyone who needs an address.
///
/// The leading word of a signature's name is its algorithm, so the three
/// splitmix64 constants, the four AES tables and the SHA-256 round constants
/// each collapse to one row. A constant inlined in code belongs to the
/// function around it; a table in data belongs to the functions that index
/// it, which the reference index knows and the address alone does not, and
/// its section is where it lives whether or not something indexes it.
///
/// The groups count every hit in the image; the per-site rows page by
/// `offset` and `limit`, where they stopped at the first 200 hits with no
/// way past them.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the function containing a hit.
/// * `o` - User names.
/// * `offset` - Per-site rows to skip first (paging).
/// * `limit` - Most per-site rows listed.
///
/// # Returns
///
/// A group per algorithm with its site and function counts and the
/// functions it appears in, then a `# showing N of M hits from O` header
/// over one page of the per-site table.
pub fn crypto_tsv(p: &Program, a: &Analysis, o: &Overlay, offset: usize, limit: usize) -> String {
    /// Functions named in a group's `where` column before the rest are counted.
    const NAMED_MAX: usize = 8;
    let mut groups: Vec<Group> = Vec::new();
    let mut owned: BTreeSet<(&str, u64)> = BTreeSet::new();
    let mut page: Vec<crate::crypto::CryptoHit> = Vec::new();
    let mut total = 0usize;
    crate::crypto::scan(p, |h| {
        if total >= offset && page.len() < limit {
            page.push(h.kept());
        }
        total += 1;
        let family = h.name.split_whitespace().next().unwrap_or(h.name);
        let inside = h.va.and_then(|va| a.function_at(va));
        let owners: Vec<u64> = match (inside, h.va) {
            (Some(f), _) => vec![f.entry],
            (None, Some(va)) => a.xrefs_to(va).iter().filter_map(|s| s.from_entry).collect(),
            (None, None) => Vec::new(),
        };
        let at = match groups.iter().position(|g| g.family == family) {
            Some(k) => k,
            None => {
                groups.push(Group {
                    family,
                    sites: 0,
                    owners: Vec::new(),
                    sections: Vec::new(),
                });
                groups.len() - 1
            }
        };
        let slot = &mut groups[at];
        slot.sites += 1;
        for entry in owners {
            if owned.insert((family, entry)) {
                slot.owners.push(entry);
            }
        }
        if inside.is_none() && !slot.sections.iter().any(|s| s == h.section) {
            slot.sections.push(h.section.to_owned());
        }
        std::ops::ControlFlow::Continue(())
    });
    if total == 0 {
        return crate::crypto::render(&[]);
    }
    groups.sort_by(|l, r| r.sites.cmp(&l.sites).then(l.family.cmp(r.family)));
    let functions: usize = {
        let mut all: Vec<u64> = groups
            .iter()
            .flat_map(|g| g.owners.iter().copied())
            .collect();
        all.sort_unstable();
        all.dedup();
        all.len()
    };
    let mut out = format!(
        "# {total} crypto/hash constant hits: {} algorithm(s) across {functions} function(s)\n",
        groups.len()
    );
    out.push_str("# algorithm        sites  functions  where\n");
    for g in &groups {
        let named: Vec<String> = g
            .owners
            .iter()
            .take(NAMED_MAX)
            .map(|e| name_of(a, o, *e))
            .collect();
        let tail = plus_more(g.owners.len(), NAMED_MAX);
        let where_ = match (named.is_empty(), g.sections.is_empty()) {
            (true, _) => format!("data in {}", g.sections.join(", ")),
            (false, true) => format!("{}{tail}", named.join(", ")),
            (false, false) => format!(
                "data in {}, read by {}{tail}",
                g.sections.join(", "),
                named.join(", ")
            ),
        };
        let _ = writeln!(
            out,
            "{:<17} {:<6} {:<10} {where_}",
            g.family,
            g.sites,
            g.owners.len()
        );
    }
    let _ = writeln!(
        out,
        "\n# showing {} of {total} hits from {offset}",
        page.len()
    );
    out.push_str(&crate::crypto::rows(&page));
    let next = offset.saturating_add(page.len());
    if next < total {
        let _ = writeln!(
            out,
            "# {} more hits; offset={next} for the next page",
            total - next
        );
    }
    out
}
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
/// A report of a dozen lines, then the functions to read first.
pub fn triage_tsv(p: &Program, a: &Analysis, o: &Overlay) -> String {
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
    if !p.debug_functions.is_empty() {
        let _ = writeln!(
            out,
            "# debug info: {} functions named by the compiler",
            p.debug_functions.len()
        );
    }
    if let Some(outcome) = &p.pdb {
        let _ = writeln!(out, "# pdb: {}", outcome.render());
    }
    let protection = protection_tsv(p, a);
    let _ = writeln!(out, "# protection: {}", headline(&protection, "protection"));
    let anti = anti_analysis_tsv(p, a, o);
    let _ = writeln!(out, "# anti-analysis: {}", headline(&anti, "anti-analysis"));
    let crypto = crypto_tsv(p, a, o, 0, 1);
    let _ = writeln!(out, "# crypto: {}", headline(&crypto, "crypto"));
    let dynamic = dynamic_imports_tsv(p, a, o);
    let _ = writeln!(
        out,
        "# dynamic imports: {}",
        headline(&dynamic, "dynamic imports")
    );
    let checks = license_checks_tsv(p, a, o);
    let _ = writeln!(out, "# checks: {}", headline(&checks, "checks"));
    let recovered = recovered_strings(p, a);
    let _ = writeln!(
        out,
        "# generated strings: {} recovered from {} generator(s)",
        recovered.found.len(),
        recovered.generators
    );
    let capabilities = capability_map_tsv(p);
    let _ = writeln!(
        out,
        "# capabilities: {}",
        headline(&capabilities, "capabilities")
    );
    for line in capabilities.lines().skip(1).take(6) {
        let _ = writeln!(out, "#   {}", line.trim());
    }
    let _ = writeln!(out, "# iocs: {}", iocs_line(p, a, o));
    for spot in blind_spots(p, a, o, headline(&protection, "protection")) {
        let _ = writeln!(out, "# blind spot: {spot}");
    }
    let mut reasons: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    let mut score: BTreeMap<u64, usize> = BTreeMap::new();
    for g in &recovered.found {
        *score.entry(g.built_by).or_default() += WEIGHT_BUILDS;
        let entry = reasons.entry(g.built_by).or_default();
        if entry.len() < 3 {
            entry.push(format!("builds {:?}", g.text));
        }
    }
    for hit in crate::crypto::find_crypto_constants(p) {
        if let Some(f) = hit.va.and_then(|va| a.function_at(va)) {
            let entry = reasons.entry(f.entry).or_default();
            let note = format!("holds {}", hit.name);
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
    ranked.sort_by(|l, r| {
        let (ls, rs) = (
            score.get(&l.0).copied().unwrap_or(0),
            score.get(&r.0).copied().unwrap_or(0),
        );
        rs.cmp(&ls).then(l.0.cmp(&r.0))
    });
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

/// Least file bytes a section needs before its entropy or its lack of code
/// is worth a line: below it, a section is a stub's padding or a handful
/// of constants.
const SPOT_SECTION_MIN: u64 = 0x200;

/// Says what the triage could not see, one line each, so a quiet report on
/// a packed or thin sample is not read as a clean one.
///
/// Each line fires on a signal already computed and names what it hides:
/// a packed verdict (what the report describes is the stub), sections at
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
    let mut spots = Vec::new();
    if verdict.starts_with("packed") || verdict.starts_with("protected") {
        spots.push(format!(
            "{}: the strings, imports and capabilities above describe the stub, not the payload; borer://unpack/{} runs the stub",
            verdict.split(':').next().unwrap_or(verdict),
            hex_or_dash(p.entry)
        ));
    }
    let sized = || {
        p.sections
            .iter()
            .filter(|s| s.file_size >= SPOT_SECTION_MIN)
    };
    let dense: Vec<&str> = sized()
        .filter(|s| {
            let len = usize::try_from(s.file_size).unwrap_or(0);
            p.read_va(s.va, len)
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
            let end = s.va.saturating_add(s.vsize.max(s.file_size));
            !a.functions.iter().any(|f| f.entry >= s.va && f.entry < end)
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
    match p.format {
        BinaryFormat::Raw | BinaryFormat::Archive => {}
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
/// cannot read: not a string literal, and not an ordinal.
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
                s.args
                    .get(1)
                    .is_none_or(|n| n.string.is_none() && n.value.is_none_or(|v| v >= ORDINAL_END))
            })
        })
        .count();
    Some((unread, found.len()))
}

/// Renders the triage of a file with no code to analyze.
///
/// An unrecognized file (an encrypted wallet, an archive, a payload pulled
/// out of a dropper) or a program for an instruction set borer does not
/// decompile still answers the first questions: what it is, how large,
/// how random, where the random or encoded bytes sit, and what text it
/// holds. The code questions are said not to apply rather than answered
/// with an empty list.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// A report of a few lines: the format and why no code analysis applies,
/// the magic, the entropy of the whole file, its high-entropy and encoded
/// regions ([`crate::entropy::high_entropy_regions`] at the defaults of the
/// `entropy` tool), and its string count with the first few strings
/// outside those regions.
pub fn file_triage_tsv(p: &Program) -> String {
    /// Bytes per window of the region scan, the `entropy` tool's default.
    const WINDOW: usize = 1024;
    /// Bits per byte a window needs, the `entropy` tool's default.
    const THRESHOLD: f64 = 7.2;
    /// Regions listed before the rest are counted.
    const REGIONS_SHOWN: usize = 10;
    /// Strings listed before the rest are counted.
    const STRINGS_SHOWN: usize = 5;
    /// Shortest string counted, the `strings` tool's default.
    const STRING_MIN: usize = 5;
    let mut out = format!(
        "# triage: {}\n",
        p.path.file_name().map_or_else(
            || String::from("<unnamed>"),
            |n| n.to_string_lossy().into_owned()
        )
    );
    let _ = writeln!(
        out,
        "# {} {}, {} bytes, {} sections, {} symbols",
        p.format.name(),
        p.arch.name(),
        p.bytes.len(),
        p.sections.len(),
        p.symbols.len()
    );
    if let Some(why) = p.refuses(Feature::Decompile) {
        let _ = writeln!(out, "# code: {why}");
    }
    let _ = writeln!(
        out,
        "# magic: {}",
        crate::headers::sniff_file(&p.bytes).unwrap_or("none of the common containers")
    );
    let _ = writeln!(
        out,
        "# entropy: {:.2} bits per byte over the whole file",
        crate::entropy::shannon(&p.bytes)
    );
    let regions = crate::entropy::high_entropy_regions(p, WINDOW, THRESHOLD);
    let _ = writeln!(
        out,
        "# {} high-entropy or encoded regions (window={WINDOW}, threshold={THRESHOLD:.2})",
        regions.len()
    );
    if !regions.is_empty() {
        let shown = &regions[..regions.len().min(REGIONS_SHOWN)];
        out.push_str(&crate::entropy::regions_tsv(p, shown));
        more_line(
            &mut out,
            regions.len(),
            REGIONS_SHOWN,
            "not listed; entropy lists them",
        );
    }
    let mut strings = crate::strings::find_strings(&p.bytes, STRING_MIN);
    strings.extend(crate::strings::find_wide_strings(&p.bytes, STRING_MIN));
    strings.sort_by_key(|h| h.off);
    let total = strings.len();
    let outside: Vec<_> = strings
        .into_iter()
        .filter(|h| {
            !regions
                .iter()
                .any(|r| (r.off..r.off + r.len).contains(&h.off))
        })
        .collect();
    let _ = writeln!(
        out,
        "# {total} strings (ascii and utf16, {STRING_MIN}+ characters), {} outside those regions",
        outside.len()
    );
    for h in outside.iter().take(STRINGS_SHOWN) {
        let _ = writeln!(out, "off={:#x} {} \"{}\"", h.off, h.encoding.name(), h.text);
    }
    more_line(
        &mut out,
        outside.len(),
        STRINGS_SHOWN,
        "not listed; strings pages them",
    );
    let _ = writeln!(
        out,
        "# next: entropy(threshold, window) to scan wider, strings(filter) for the text{}",
        if p.symbols.is_empty() {
            ""
        } else {
            ", symbols for the imports and exports"
        }
    );
    out
}

#[cfg(test)]
mod tests {
    use super::emulate_tsv;
    use crate::analysis::{Analysis, Overlay};
    use crate::program::Program;

    /// An emulation is refused before it runs when nothing backs its start,
    /// runs when a write puts code there, and refuses a malformed count.
    ///
    /// # Panics
    ///
    /// When an unmapped start runs, a written one does not, or `steps=abc`
    /// is read as hex.
    #[test]
    fn emulate_refuses_an_unmapped_start_and_a_bad_count() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let err = emulate_tsv(&p, &a, &o, "0x1").unwrap_err();
        assert!(err.starts_with("nothing is mapped at 0x1;"), "{err}");
        let out = emulate_tsv(&p, &a, &o, "0x9000,w0x9000=c3").unwrap();
        assert!(out.contains(": returned after "), "{out}");
        let err = emulate_tsv(&p, &a, &o, "0x1000,steps=abc").unwrap_err();
        assert_eq!(err, "bad step count in steps=abc");
    }

    /// `aN` sets the argument the decompiler names `aN`, counting from one.
    ///
    /// `a1` is the first (`rcx` on x64) and `a2` the second, so a name
    /// copied out of the pseudo-C sets the argument it names. `a0`, which
    /// names no argument, is refused pointing at `a1` rather than read as
    /// the first.
    ///
    /// # Panics
    ///
    /// When `a1` sets another argument than the first, or `a0` runs.
    #[test]
    fn emulate_numbers_arguments_as_the_decompiler_does() {
        let p = Program::raw_x64(&[0x48, 0x89, 0xc8, 0xc3]); // ASM: mov rax,rcx; ret
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let first = emulate_tsv(&p, &a, &o, "0x1000,a1=0x30").unwrap();
        assert!(first.contains(" with a1=0x30: returned"), "{first}");
        assert!(first.contains("# registers: rax=0x30 rcx=0x30 "), "{first}");
        let second = emulate_tsv(&p, &a, &o, "0x1000,a2=0x30").unwrap();
        assert!(second.contains(" with a2=0x30: returned"), "{second}");
        assert!(
            second.contains("# registers: rax=0x0 rcx=0x0 rdx=0x30 "),
            "{second}"
        );
        let err = emulate_tsv(&p, &a, &o, "0x1000,a0=0x30").unwrap_err();
        assert_eq!(
            err,
            "a0=0x30: arguments count from one as the decompiler names them; a1 is the first"
        );
    }

    /// A file with no code is triaged from its bytes: it says why no code
    /// analysis applies, names the magic, lists the encoded region, and
    /// shows the text outside it rather than the encoded text itself.
    ///
    /// # Panics
    ///
    /// When a line of that report is missing or the base64 is printed.
    #[test]
    fn a_file_with_no_code_is_triaged_from_its_bytes() {
        const ALPHABET: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let mut bytes = b"QklFMQ".to_vec();
        let mut x = 0x2545_f491_4f6c_dd1du64;
        for _ in 0..4000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            bytes.push(ALPHABET[usize::try_from(x >> 58).unwrap()]);
        }
        bytes.extend_from_slice(b"\0\0a note in plain text\0");
        let mut p = Program::raw(bytes, crate::program::Arch::Unknown, 0, None, Vec::new());
        p.path = std::path::PathBuf::from("default_wallet");
        let out = super::file_triage_tsv(&p);
        assert!(out.starts_with("# triage: default_wallet\n"), "{out}");
        assert!(out.contains("# code: raw file, arch 'unknown': "), "{out}");
        assert!(out.contains("no code analysis applies"), "{out}");
        assert!(out.contains("# magic: Electrum encrypted wallet"), "{out}");
        assert!(
            out.lines()
                .any(|l| l.starts_with("0x0 ") && l.ends_with(" base64")),
            "{out}"
        );
        assert!(out.contains("\"a note in plain text\""), "{out}");
        assert!(
            !out.contains("QklFMQ"),
            "the encoded text is printed: {out}"
        );
    }
}
