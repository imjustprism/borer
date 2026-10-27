//! Protection signals: anti-analysis sites, license checks, dynamically
//! resolved imports and packer evidence.

use super::*;

/// Most sites listed per anti-analysis technique.
pub(super) const ANTI_SITES_MAX: usize = 12;

/// The import names that signal an anti-analysis technique.
///
/// The ones [`CRT_IMPORTS`] names come with every C runtime as well, so
/// they are listed but never decide the verdict.
pub(super) const ANTI_IMPORTS: [(&str, &str); 8] = [
    ("isdebuggerpresent", "IsDebuggerPresent"),
    ("checkremotedebugger", "CheckRemoteDebuggerPresent"),
    (
        "ntqueryinformationprocess",
        "NtQueryInformationProcess (debug port)",
    ),
    (
        "ntsetinformationthread",
        "NtSetInformationThread (hide from debugger)",
    ),
    ("outputdebugstring", "OutputDebugString (exception probe)"),
    (
        "queryperformancecounter",
        "QueryPerformanceCounter (timing)",
    ),
    ("gettickcount", "GetTickCount (timing)"),
    ("ntclose", "NtClose (invalid-handle probe)"),
];

/// Labels of [`ANTI_IMPORTS`] the C runtime imports by itself (its failure
/// and timing paths): an ordinary program carries them, so they tip no
/// verdict.
const CRT_IMPORTS: [&str; 5] = [
    "IsDebuggerPresent",
    "OutputDebugString (exception probe)",
    "QueryPerformanceCounter (timing)",
    "GetTickCount (timing)",
    "NtClose (invalid-handle probe)",
];

/// Reports the anti-debug and anti-VM techniques the binary carries.
///
/// The loud ones are imports (`IsDebuggerPresent`); the stealthy ones are
/// bare instructions a compiler never emits in ordinary code, so finding them
/// at all is the signal. `rdtsc` times a region to catch a single-stepping
/// debugger; `cpuid` and the descriptor-table reads (`sidt`, `sgdt`, `sldt`,
/// `str`) fingerprint a hypervisor; `in` reads a hypervisor backdoor port; an
/// inline `int3` or `icebp` traps a debugger; a read of the PEB
/// (`gs:[0x60]`, `fs:[0x30]`) reaches the `BeingDebugged` byte. A little
/// `cpuid` is ordinary feature detection; a pile of these together is a
/// program that does not want to be watched.
///
/// Two of these a compiler does emit, and they are not counted: an `int3`
/// after a call, a branch, a return or another `int3` (nops aside) is the
/// trap MSVC and clang put after a call that does not return, or padding;
/// and the imports of [`CRT_IMPORTS`] come with every C runtime, so they
/// are listed without tipping the verdict. The verdict counts techniques,
/// not sites: msvcrt's `_inp` is three `in` instructions because reading a
/// port is its job, and three sites of one instruction are one technique.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: functions and their blocks.
/// * `o` - User names.
///
/// # Returns
///
/// The techniques present, each with where they are, the instruction ones
/// first.
pub fn anti_analysis_tsv(p: &Program, a: &Analysis, o: &Overlay) -> String {
    let sites = anti_sites(p, a);
    let mut out = String::new();
    let weak = |tag: &str| tag.starts_with("cpuid") || tag.starts_with("rdtsc");
    let strong = sites.keys().filter(|tag| !weak(tag)).count();
    let instr_count: usize = sites.values().map(Vec::len).sum();
    for (tag, at) in sites.iter() {
        let shown: Vec<String> = at
            .iter()
            .take(ANTI_SITES_MAX)
            .map(|a| format!("{a:#x}"))
            .collect();
        let more = if at.len() > shown.len() {
            format!(" +{} more", at.len() - shown.len())
        } else {
            String::new()
        };
        let named = a.function_at(at[0]).map_or_else(|| at[0], |f| f.entry);
        let _ = writeln!(
            out,
            "{:<32} {:>4}  {} (in {}){more}",
            tag,
            at.len(),
            shown.join(", "),
            name_of(a, o, named)
        );
    }
    let mut imports: Vec<&str> = Vec::new();
    for sym in &p.symbols {
        if !matches!(sym.kind, SymbolKind::Import) {
            continue;
        }
        let api = sym
            .name
            .rsplit('!')
            .next()
            .unwrap_or(&sym.name)
            .to_lowercase();
        for (frag, label) in ANTI_IMPORTS {
            if api.contains(frag) && !imports.contains(&label) {
                imports.push(label);
            }
        }
    }
    for label in &imports {
        let _ = writeln!(out, "{label:<32}  import");
    }
    let telling = imports.iter().any(|label| !CRT_IMPORTS.contains(label));
    let verdict = if strong >= 3 || (strong >= 1 && telling) {
        "anti-analysis: a program that resists being watched"
    } else if instr_count + imports.len() == 0 {
        "no anti-analysis tells"
    } else {
        "a few anti-analysis tells, within what ordinary code uses"
    };
    format!("# {verdict}\n# technique                       sites  where\n{out}")
}

/// Returns the sites of each anti-analysis instruction in the program's
/// functions, found once per analysis.
///
/// Every instruction of every function is decoded for them, and they are
/// facts of the code alone, so they are kept in [`Analysis::derived`]
/// rather than decoded again on every `antianalysis` and `triage` read.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: functions and their blocks.
///
/// # Returns
///
/// Each technique's label and its instruction addresses, in function
/// then address order; empty for an architecture with no x86 decoder.
fn anti_sites(p: &Program, a: &Analysis) -> Arc<BTreeMap<&'static str, Vec<u64>>> {
    a.derived.get_or_build("anti_sites", (), || {
        let mut sites: BTreeMap<&'static str, Vec<u64>> = BTreeMap::new();
        let Some(bits) = p.arch.bitness() else {
            return sites;
        };
        for f in &a.functions {
            let mut after = FlowControl::Next;
            each_instruction(p, f, bits, |i| {
                let trap = i.mnemonic() == Mnemonic::Int3 && after != FlowControl::Next;
                if let Some(tag) = anti_instruction(i).filter(|_| !trap) {
                    sites.entry(tag).or_default().push(i.ip());
                }
                if i.mnemonic() != Mnemonic::Nop {
                    after = i.flow_control();
                }
            });
        }
        sites
    })
}

/// The anti-analysis technique an instruction is, if any.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// A short label, or `None` when the instruction is not a tell.
pub(super) fn anti_instruction(i: &Instruction) -> Option<&'static str> {
    match i.mnemonic() {
        Mnemonic::Rdtsc | Mnemonic::Rdtscp => Some("rdtsc (timing)"),
        Mnemonic::Cpuid => Some("cpuid (hypervisor probe)"),
        Mnemonic::Int3 => Some("int3 (debugger trap)"),
        Mnemonic::Int1 => Some("icebp (debugger trap)"),
        Mnemonic::Sidt | Mnemonic::Sgdt | Mnemonic::Sldt | Mnemonic::Str => {
            Some("descriptor-table read (VM red pill)")
        }
        Mnemonic::In | Mnemonic::Insb | Mnemonic::Insw | Mnemonic::Insd => {
            Some("in (VMware backdoor port)")
        }
        _ => None,
    }
}

/// Phrases that mark a function as judging a key, serial or license.
///
/// Each is distinctive enough not to fire on ordinary text; the generic
/// `invalid` is left out because it is in every argument check.
pub(super) const CHECK_PHRASES: [&str; 18] = [
    "serial",
    "license",
    "activation",
    "registration",
    "registered",
    "incorrect",
    "wrong password",
    "access denied",
    "product key",
    "unlock",
    "trial",
    "expired",
    "authenticate",
    "authentication",
    "congratulation",
    "not valid",
    "invalid key",
    "invalid serial",
];

/// Most check functions listed in one read.
pub(super) const CHECKS_MAX: usize = 200;

/// Constants shown per check function.
pub(super) const CHECK_CONSTS_MAX: usize = 6;

/// One function that mentions a check phrase, and what it compares against.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Check {
    /// The function's entry.
    pub(super) entry: u64,
    /// The phrases it references, sorted.
    pub(super) phrases: Vec<String>,
    /// The telling constants it compares against, in first-seen order.
    pub(super) constants: Vec<u64>,
}

/// Finds the functions that decide whether a secret is valid.
///
/// A crackme or a license check reads an input and decides accept or reject;
/// the decision usually names itself, with a string like `incorrect serial`
/// or `activation`, and turns on a comparison against the expected value.
/// This lists each function that references such a phrase, the phrase, and
/// the distinctive constants it compares against, so the value the check
/// wants and the branch that enforces it are both in front of the reader.
/// A row claims a check, and the claim rests on a constant the function
/// compares against; a function that only mentions a phrase (an HTTP
/// authentication dialog, a signal named `authenticationRequired`) is
/// reported apart, as a mention and nothing more.
///
/// A crackme need not name its decision at all, so a second pass reads the
/// functions that take input (a call to argv, `scanf`, `recv`) and test a
/// value computed from it: a compare of what was read against a constant
/// or a call's result. Those are listed apart from the phrase-named rows,
/// since their claim rests on the flow, not on a string.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: cross-references, functions, blocks.
/// * `o` - User names.
///
/// # Returns
///
/// The listing as text, the functions with the most telling constants first.
/// It reads every referenced string and decompiles the input readers, so
/// it is built once per set of names ([`Analysis::derived`]).
pub fn license_checks_tsv(p: &Program, a: &Analysis, o: &Overlay) -> String {
    a.derived
        .get_or_build_named("license_checks", o.fingerprint(), (), || checks_of(p, a, o))
        .as_ref()
        .clone()
}

/// Builds the listing [`license_checks_tsv`] memoizes.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: cross-references, functions, blocks.
/// * `o` - User names.
///
/// # Returns
///
/// As [`license_checks_tsv`].
fn checks_of(p: &Program, a: &Analysis, o: &Overlay) -> String {
    let mut found: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for (target, lit) in literal_targets(p, a).iter() {
        let sites = a.xrefs_to(*target);
        let low = lit.to_lowercase();
        let matched: Vec<&str> = CHECK_PHRASES
            .iter()
            .copied()
            .filter(|ph| low.contains(ph))
            .collect();
        if matched.is_empty() {
            continue;
        }
        for site in sites {
            if let Some(entry) = site.from_entry {
                let e = found.entry(entry).or_default();
                for ph in &matched {
                    e.insert((*ph).to_owned());
                }
            }
        }
    }
    let bits = p.arch.bitness();
    let mut rows: Vec<Check> = found
        .iter()
        .map(|(entry, phrases)| Check {
            entry: *entry,
            phrases: phrases.iter().cloned().collect(),
            constants: bits.map_or_else(Vec::new, |b| check_constants(p, a, *entry, b)),
        })
        .collect();
    rows.sort_by_key(|c| (std::cmp::Reverse(c.constants.len()), c.entry));
    let (checks, mentions): (Vec<_>, Vec<_>) =
        rows.into_iter().partition(|c| !c.constants.is_empty());
    let readers = input_readers(p, a, o, &found, bits);
    let mut out = format!(
        "# {} function{} judge a key, serial or license{}\n",
        checks.len().min(CHECKS_MAX),
        plural(checks.len()),
        if readers.is_empty() {
            String::new()
        } else {
            format!("; {} more test what they read", readers.len())
        }
    );
    if !mentions.is_empty() {
        let named: Vec<String> = mentions
            .iter()
            .take(CHECK_CONSTS_MAX)
            .map(|c| format!("{} ({})", name_of(a, o, c.entry), c.phrases.join(",")))
            .collect();
        let _ = writeln!(
            out,
            "# {} more mention a phrase and compare nothing constant: {}{}",
            mentions.len(),
            named.join(", "),
            plus_more(mentions.len(), CHECK_CONSTS_MAX)
        );
    }
    out.push_str("# function                       mentions          tests against\n");
    for c in checks.iter().take(CHECKS_MAX) {
        let cs: Vec<String> = c
            .constants
            .iter()
            .take(CHECK_CONSTS_MAX)
            .map(|c| format!("{c:#x}"))
            .collect();
        let _ = writeln!(
            out,
            "{:<32} {:<17} {}",
            name_of(a, o, c.entry),
            c.phrases.join(","),
            cs.join(", ")
        );
    }
    if !readers.is_empty() {
        let named: Vec<String> = readers
            .iter()
            .take(CHECK_CONSTS_MAX)
            .map(|c| {
                format!(
                    "{} ({})",
                    name_of(a, o, c.entry),
                    if c.constants.is_empty() {
                        "a value it parsed".to_owned()
                    } else {
                        c.constants
                            .iter()
                            .take(CHECK_CONSTS_MAX)
                            .map(|v| format!("{v:#x}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    }
                )
            })
            .collect();
        let _ = writeln!(
            out,
            "# {} read input and test what they compute against it: {}{}",
            readers.len(),
            named.join(", "),
            plus_more(readers.len(), CHECK_CONSTS_MAX)
        );
    }
    out
}

/// The APIs whose buffer or return carries input the program did not
/// compute: argv and its getters, console and stream reads, an environment
/// lookup.
///
/// Matched against an import's last name segment only, spelled exactly: a
/// whole-name substring would fire on every type named `RecvTimeoutError`
/// and every method ending in `_args`. Debug-named callees are matched
/// only as `env::args`, because the short names collide with ordinary
/// internals (`core::ptr::read` reads memory, not input).
pub(super) const INPUT_APIS: [&str; 16] = [
    "args",
    "argv",
    "__getmainargs",
    "getmainargs",
    "commandlinetoargvw",
    "commandlinetoargva",
    "getcommandlinea",
    "getcommandlinew",
    "scanf",
    "sscanf",
    "fgets",
    "gets",
    "getenv",
    "readline",
    "read",
    "recv",
];

/// Whether a callee symbol is one of the [`INPUT_APIS`] an input reader
/// calls.
///
/// # Arguments
///
/// * `s` - The callee's symbol.
pub(super) fn input_api(s: &Symbol) -> bool {
    if matches!(s.kind, SymbolKind::Import) {
        let bare = s.name.rsplit('!').next().unwrap_or(&s.name).to_lowercase();
        INPUT_APIS.contains(&bare.as_str())
    } else {
        s.name
            .split('<')
            .next()
            .is_some_and(|bare| bare == "std::env::args" || bare.ends_with("::env::args"))
    }
}

/// The functions that take input and test a value computed from it, found
/// without a phrase to name them.
///
/// Each reads input through one of the [`INPUT_APIS`] and then compares a
/// value its own code computed from memory it read against a call's result
/// or a telling constant ([`computed_vs_external`]): the shape of
/// `check(key(name), serial)`, keygen math on one side and the parsed
/// input on the other. The compare itself is required, not just a telling
/// constant somewhere in the function, because a reader that compares
/// sizes and limits against round numbers is ordinary code. Phrase-named
/// functions are left to the main table; this pass only adds what no
/// string names.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: functions and their callees.
/// * `o` - User names.
/// * `phrased` - Entries the phrase pass already found, skipped.
/// * `bits` - The architecture bitness, if known.
///
/// # Returns
///
/// The reader checks, the most telling constants first, then by entry.
pub(super) fn input_readers(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    phrased: &BTreeMap<u64, BTreeSet<String>>,
    bits: Option<u32>,
) -> Vec<Check> {
    let mut imports: BTreeSet<u64> = BTreeSet::new();
    for sym in &p.symbols {
        if matches!(sym.kind, SymbolKind::Import) && input_api(sym) {
            for site in a.xrefs_to(sym.addr) {
                if let Some(entry) = site.from_entry {
                    imports.insert(entry);
                }
            }
        }
    }
    let mut rows: Vec<Check> = Vec::new();
    for f in &a.functions {
        if phrased.contains_key(&f.entry) {
            continue;
        }
        if a.symbol_at(p, f.entry)
            .is_some_and(|s| s.name.contains("env::args"))
        {
            continue;
        }
        let reads = imports.contains(&f.entry)
            || f.callees
                .iter()
                .any(|c| a.symbol_at(p, *c).is_some_and(input_api));
        if !reads {
            continue;
        }
        if !crate::analysis::decompile::decompile(p, a, o, f.entry)
            .is_some_and(|t| computed_vs_external(&t))
        {
            continue;
        }
        rows.push(Check {
            entry: f.entry,
            phrases: Vec::new(),
            constants: bits.map_or_else(Vec::new, |b| check_constants(p, a, f.entry, b)),
        });
    }
    rows.sort_by_key(|c| (std::cmp::Reverse(c.constants.len()), c.entry));
    rows
}

/// Assignment operators as the decompiler writes them, plain and
/// compound (a keygen mixes its reads into its accumulator with an
/// xor-assign).
pub(super) const ASSIGNS: [&str; 9] = [
    " = ", " += ", " -= ", " *= ", " ^= ", " |= ", " &= ", " <<= ", " >>= ",
];

/// Whether decompiled text compares a value computed from memory it read
/// against a value a call returned or a telling constant.
///
/// The text carries the flow borer needs: a variable assigned a read
/// through a pointer (`x = *(uint8_t*)p`), or the read itself inlined
/// into the compare, is the computed side; a variable assigned a call's
/// result (`y = parse(...)`) is the parsed side; and a `==`/`!=` between
/// the two is the check. A read inlined into the compare must face a
/// call's result directly: paired with a literal it would be any loop
/// testing a byte against a delimiter, and a literal only counts when it
/// is telling ([`telling_constant`]), the same standard the phrase-named
/// rows hold. Anything weaker (a compare of two calls, of two reads) is
/// ordinary code and stays out.
///
/// # Arguments
///
/// * `text` - The function's decompiled text.
pub(super) fn computed_vs_external(text: &str) -> bool {
    let mut from_reads: Vec<&str> = Vec::new();
    let mut from_calls: Vec<&str> = Vec::new();
    for line in text.lines() {
        let Some((lhs, rhs)) = ASSIGNS.iter().find_map(|op| line.split_once(op)) else {
            continue;
        };
        let var = lhs.trim();
        if var.is_empty() || !var.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            continue;
        }
        if (rhs.contains("*(uint") || rhs.contains("*(int")) && !from_reads.contains(&var) {
            from_reads.push(var);
        } else if rhs.contains('(') && !from_calls.contains(&var) {
            from_calls.push(var);
        }
    }
    if from_reads.is_empty() && !text.contains("*(uint") && !text.contains("*(int") {
        return false;
    }
    text.lines().any(|line| {
        [" != ", " == "].iter().any(|op| {
            let Some(at) = line.find(op) else {
                return false;
            };
            let (l, r) = (&line[..at], &line[at + op.len()..]);
            (side(l, &from_reads) && (side(r, &from_calls) || telling(r)))
                || (side(r, &from_reads) && (side(l, &from_calls) || telling(l)))
                || (reads(l) && side(r, &from_calls))
                || (reads(r) && side(l, &from_calls))
        })
    })
}

/// Whether one side of a compare reads through a pointer, inlined.
///
/// # Arguments
///
/// * `s` - One side of a compare.
fn reads(s: &str) -> bool {
    s.contains("*(uint") || s.contains("*(int")
}

/// Whether one side of a compare names a variable from a set, as a whole
/// word: `r9` matches `(uint32_t)r9` and never `r90`.
///
/// # Arguments
///
/// * `s` - One side of a compare.
/// * `vars` - The variables looked for.
fn side(s: &str, vars: &[&str]) -> bool {
    vars.iter().any(|v| says_word(s, v))
}

/// Whether `s` mentions `word` delimited by anything but identifier
/// characters.
///
/// # Arguments
///
/// * `s` - The text searched.
/// * `word` - The identifier looked for.
fn says_word(s: &str, word: &str) -> bool {
    let is_id = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let mut rest = s;
    while let Some(at) = rest.find(word) {
        let before = rest[..at].chars().next_back().is_none_or(|c| !is_id(c));
        let after = rest[at + word.len()..]
            .chars()
            .next()
            .is_none_or(|c| !is_id(c));
        if before && after {
            return true;
        }
        rest = &rest[at + word.len()..];
    }
    false
}

/// Whether one side of a compare is a telling constant.
///
/// # Arguments
///
/// * `s` - One side of a compare.
fn telling(s: &str) -> bool {
    s.split(|c: char| !(c.is_ascii_alphanumeric() || c == 'x' || c == 'X'))
        .filter(|t| t.starts_with(|c: char| c.is_ascii_digit()))
        .find_map(
            |t| match t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
                Some(hex) => u64::from_str_radix(hex, 16).ok(),
                None => t.parse::<u64>().ok(),
            },
        )
        .is_some_and(telling_constant)
}

/// The distinctive constants a function compares against.
///
/// A check tests the input against the value it wants, `cmp eax, 0x4a2b`;
/// small values (0, 1, sizes), the all-ones sentinels and page-sized round
/// numbers are not secrets, so they are left out.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the function's blocks.
/// * `entry` - The function's entry.
/// * `bits` - The architecture bitness.
///
/// # Returns
///
/// The telling constants, in first-seen order, without duplicates.
pub(super) fn check_constants(p: &Program, a: &Analysis, entry: u64, bits: u32) -> Vec<u64> {
    let Some(f) = a.function(entry) else {
        return Vec::new();
    };
    let mut out: Vec<u64> = Vec::new();
    let mut seen: BTreeSet<u64> = BTreeSet::new();
    each_instruction(p, f, bits, |i| {
        if !matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Sub) {
            return;
        }
        if !matches!(
            i.op1_kind(),
            OpKind::Immediate16
                | OpKind::Immediate32
                | OpKind::Immediate32to64
                | OpKind::Immediate64
        ) {
            return;
        }
        let v = i.immediate(1);
        if telling_constant(v) && seen.insert(v) {
            out.push(v);
        }
    });
    out
}

/// Whether a constant is distinctive enough to be a secret a check tests.
///
/// A small aligned number is a struct field offset, not a secret; a
/// printable four-byte code (`0x6e696157`) is a deliberate magic value;
/// and otherwise a secret is large or has low bits set, unlike a round
/// limit. Four more shapes are limits, not secrets: the other all-ones
/// sentinels (`0xffff`, `0x7fffffff`, every read bound), a power of two
/// (`0x1000`, `0x10000`, every buffer size and page), a mask of nothing
/// but the two top bits (`0x40000000`, `0xc0000000`, the futex rwlock
/// reader and writer bits a synchronization wrapper compares state
/// against), and a power of ten (`1000000000`, a timeout or a size a
/// human wrote).
///
/// # Arguments
///
/// * `v` - The immediate.
pub(super) fn telling_constant(v: u64) -> bool {
    if v <= 0xff
        || v == u64::from(u32::MAX)
        || v == u64::MAX
        || v == u64::from(u16::MAX)
        || v == 0x7fff_ffff
    {
        return false;
    }
    if v < 0x1000 && v.is_multiple_of(4) {
        return false;
    }
    let bytes = crate::num::lo32(v).to_le_bytes();
    if u32::try_from(v).is_ok() && bytes.iter().all(|c| (0x20..0x7f).contains(c)) {
        return true;
    }
    if v >= 0x4000_0000 && v & 0x3fff_ffff == 0 {
        return false;
    }
    let mut power_of_ten = 10u64;
    while power_of_ten < v && power_of_ten <= u64::MAX / 10 {
        power_of_ten *= 10;
    }
    power_of_ten != v && v.count_ones() != 1 && (v >= 0x1000 || v & 0xf != 0)
}

/// The resolver APIs whose string argument names a runtime import or DLL.
///
/// `(bare API name, is it a library load rather than a function lookup)`.
pub(super) const RESOLVERS: [(&str, bool); 8] = [
    ("GetProcAddress", false),
    ("LdrGetProcedureAddress", false),
    ("LoadLibraryA", true),
    ("LoadLibraryW", true),
    ("LoadLibraryExA", true),
    ("LoadLibraryExW", true),
    ("GetModuleHandleA", true),
    ("LdrLoadDll", true),
];

/// Fewest resolver callers worth decompiling across the cores.
const RESOLVER_PAR_MIN: usize = 8;

/// Most runtime imports listed in one read.
pub(super) const DYNIMPORTS_MAX: usize = 400;

/// Recovers the APIs and DLLs a program resolves at runtime.
///
/// A program that calls `GetProcAddress(h, "WriteProcessMemory")` imports
/// that function without it appearing in the import table, which is how
/// malware keeps its real capability off the list a quick look reads. The
/// callers of the resolver APIs are decompiled and the string each passes is
/// collected, so the hidden imports are named. Only the functions that call
/// a resolver are decompiled, across the cores, so this stays cheap.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: symbols and cross-references.
/// * `o` - User names.
///
/// # Returns
///
/// The DLLs loaded and the functions resolved, as text.
pub fn dynamic_imports_tsv(p: &Program, a: &Analysis, o: &Overlay) -> String {
    let mut callers: BTreeSet<u64> = BTreeSet::new();
    for sym in &p.symbols {
        if !matches!(sym.kind, SymbolKind::Import) || sym.addr == 0 {
            continue;
        }
        let bare = sym.name.rsplit('!').next().unwrap_or(&sym.name);
        if RESOLVERS.iter().any(|(r, _)| *r == bare) {
            for site in a.xrefs_to(sym.addr) {
                if let Some(e) = site.from_entry {
                    callers.insert(e);
                }
            }
        }
    }
    let mut apis: BTreeSet<String> = BTreeSet::new();
    let mut dlls: BTreeSet<String> = BTreeSet::new();
    let callers: Vec<u64> = callers.into_iter().collect();
    let texts = crate::analysis::striped_with(
        &callers,
        RESOLVER_PAR_MIN,
        || (),
        |(), &entry| crate::analysis::decompile::decompile(p, a, o, entry),
    );
    for text in texts.into_iter().flatten().flatten() {
        for line in text.lines() {
            for (api, is_lib) in RESOLVERS {
                collect_resolved(p, line, api, is_lib, &mut apis, &mut dlls);
            }
        }
    }
    let mut out = format!(
        "# {} function{} resolved at runtime, {} librar{} loaded, from {} call site group{}\n",
        apis.len(),
        plural(apis.len()),
        dlls.len(),
        if dlls.len() == 1 { "y" } else { "ies" },
        callers.len(),
        plural(callers.len())
    );
    if !dlls.is_empty() {
        out.push_str("# loaded libraries:\n");
        for d in dlls.iter().take(DYNIMPORTS_MAX) {
            let _ = writeln!(out, "  {d}");
        }
        elided_line(&mut out, dlls.len(), DYNIMPORTS_MAX, " libraries");
    }
    if !apis.is_empty() {
        out.push_str("# resolved functions:\n");
        for f in apis.iter().take(DYNIMPORTS_MAX) {
            let _ = writeln!(out, "  {f}");
        }
        elided_line(&mut out, apis.len(), DYNIMPORTS_MAX, " functions");
    }
    out
}

/// Pulls the string argument out of a resolver call on one line.
///
/// The string is the last quoted literal before the matching `)`.
///
/// # Arguments
///
/// * `p` - The loaded image, read where a name is spelled as its address.
/// * `line` - A decompiled line.
/// * `api` - The resolver's name.
/// * `is_lib` - Whether it loads a library (vs. resolving a function).
/// * `apis` - Receives resolved function names.
/// * `dlls` - Receives loaded library names.
pub(super) fn collect_resolved(
    p: &Program,
    line: &str,
    api: &str,
    is_lib: bool,
    apis: &mut BTreeSet<String>,
    dlls: &mut BTreeSet<String>,
) {
    let call = format!("{api}(");
    let mut rest = line;
    while let Some(pos) = rest.find(&call) {
        let after = &rest[pos + call.len()..];
        rest = after;
        let end = matching_call_end(after);
        let args = &after[..end.min(after.len())];
        if let Some(name) = last_quoted(args).or_else(|| addressed_name(p, api, args)) {
            if is_lib {
                if library_name(&name) {
                    dlls.insert(name);
                }
            } else if function_name(&name) {
                apis.insert(name);
            }
        }
    }
}

/// Reads the name a resolver call's last argument points at, when the text
/// spells it as an address.
///
/// A string kept in a code section (a DLL that merges its read-only data
/// into `.text`) is printed as its address, not as a literal.
///
/// msvcrt's `rename` calls `GetProcAddress(hModule, 0x10003ecc)` for
/// `"MoveFileA"`, and triage called all 19 of its lookups unreadable.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `api` - The resolver; a `W` one reads UTF-16.
/// * `args` - The call's argument text.
///
/// # Returns
///
/// The text at that address, or `None` when the last argument is no
/// address or no string is there.
pub(super) fn addressed_name(p: &Program, api: &str, args: &str) -> Option<String> {
    /// Longest name read.
    const NAME_MAX: usize = 256;
    let last = args.rsplit(',').next()?.trim();
    let va = u64::from_str_radix(last.strip_prefix("0x")?, 16).ok()?;
    let read = if api.ends_with('W') {
        wstr_at(p, va, 2, NAME_MAX)
    } else {
        cstr_at(p, va, 2, NAME_MAX)
    };
    read.map(|(_, text)| text)
}

/// The offset of the `)` that closes the call opened at the start of `s`.
///
/// # Arguments
///
/// * `s` - Text just after a call's `(`.
pub(super) fn matching_call_end(s: &str) -> usize {
    let mut depth = 1i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return i;
                }
            }
            _ => {}
        }
    }
    s.len()
}

/// The content of the last double-quoted literal in `s`, if any.
///
/// # Arguments
///
/// * `s` - The call's argument text.
pub(super) fn last_quoted(s: &str) -> Option<String> {
    let mut last = None;
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            if let Some(rel) = s[i + 1..].find('"') {
                last = Some(s[i + 1..i + 1 + rel].to_owned());
                i += rel + 2;
                continue;
            }
            break;
        }
        i += 1;
    }
    last.filter(|t| !t.is_empty())
}

/// Whether a string looks like a library name, not a stray literal.
///
/// # Arguments
///
/// * `name` - The quoted argument.
pub(super) fn library_name(name: &str) -> bool {
    name.to_lowercase().ends_with(".dll")
        || (name.len() >= 3
            && name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-'))
}

/// Whether a string looks like an exported function's name, not the bytes
/// of a structure the decompiler printed as a literal.
///
/// `LdrGetProcedureAddress` takes the name as an `ANSI_STRING`, whose
/// first four bytes are two lengths: `0x25, 0x26` printed as `L"%&"` and
/// was listed as a function resolved at run time. An export name is an
/// identifier, a C++ decorated one included (`?`, `@`, `$`).
///
/// # Arguments
///
/// * `name` - The literal's text.
pub(super) fn function_name(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_alphabetic() || matches!(c, '_' | '?' | '@'))
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '?' | '@' | '$' | '.'))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::collect_resolved;
    use crate::program::Program;

    /// A structure the decompiler printed as a wide literal is not taken
    /// for the name of a function resolved at run time, and a decorated
    /// name is.
    ///
    /// # Panics
    ///
    /// When the structure's bytes are listed, or the name is not.
    #[test]
    fn a_structure_printed_as_a_literal_names_no_function() {
        let p = Program::raw_x64(&[0xc3]);
        let (mut apis, mut dlls) = (BTreeSet::new(), BTreeSet::new());
        for (line, api) in [
            (
                "s = LdrGetProcedureAddress(h, L\"%&\", 0, &p);",
                "LdrGetProcedureAddress",
            ),
            ("p = GetProcAddress(h, \"?Run@@YAXXZ\");", "GetProcAddress"),
        ] {
            collect_resolved(&p, line, api, false, &mut apis, &mut dlls);
        }
        assert_eq!(apis.into_iter().collect::<Vec<_>>(), ["?Run@@YAXXZ"]);
        assert!(dlls.is_empty());
    }

    /// A name the text spells as the address of a string in a code section
    /// is read there, as the literal it is.
    ///
    /// # Panics
    ///
    /// When the name at the address is not listed.
    #[test]
    fn a_name_spelled_as_its_address_is_read() {
        let mut code = vec![0xc3u8; 0x20];
        code[0x10..0x1a].copy_from_slice(b"MoveFileA\0");
        let p = Program::raw_x64(&code);
        let (mut apis, mut dlls) = (BTreeSet::new(), BTreeSet::new());
        collect_resolved(
            &p,
            "var10 = GetProcAddress(hModule, 0x1010);",
            "GetProcAddress",
            false,
            &mut apis,
            &mut dlls,
        );
        assert_eq!(apis.into_iter().collect::<Vec<_>>(), ["MoveFileA"]);
    }
}

/// Section names a packer or protector writes, and what it is called.
pub(super) const PACKER_SECTIONS: [(&str, &str); 40] = [
    ("UPX0", "UPX"),
    ("UPX1", "UPX"),
    ("UPX2", "UPX"),
    (".UPX0", "UPX"),
    (".UPX1", "UPX"),
    (".UPX2", "UPX"),
    (".aspack", "ASPack"),
    (".adata", "ASPack"),
    (".themida", "Themida/WinLicense"),
    (".winlice", "Themida/WinLicense"),
    (".vsec", "Themida/WinLicense"),
    (".vmp0", "VMProtect"),
    (".vmp1", "VMProtect"),
    (".vmp2", "VMProtect"),
    (".enigma1", "Enigma"),
    (".enigma2", "Enigma"),
    ("MPRESS1", "MPRESS"),
    ("MPRESS2", "MPRESS"),
    (".MPRESS1", "MPRESS"),
    (".MPRESS2", "MPRESS"),
    (".petite", "Petite"),
    ("PEC2", "PECompact"),
    ("pec1", "PECompact"),
    (".pec1", "PECompact"),
    (".pec2", "PECompact"),
    (".pec3", "PECompact"),
    (".nsp0", "NsPack"),
    (".nsp1", "NsPack"),
    (".nsp2", "NsPack"),
    ("FSG", "FSG"),
    (".fsg", "FSG"),
    (".MEW", "MEW"),
    ("MEW", "MEW"),
    (".packed", "unnamed packer"),
    (".boom", "The Boomerang"),
    (".taz", "PESpin"),
    (".sforce3", "StarForce"),
    (".boot", "Themida/WinLicense"),
    (".vm_sec", "a virtualizing protector"),
    (".vmp", "VMProtect"),
];

/// One packer's entry-stub signature.
#[derive(Debug)]
pub(super) struct EntrySig {
    /// The packer family a match names.
    pub(super) packer: &'static str,
    /// The stub's first bytes at the entry point, `??` where versions vary.
    pub(super) pattern: &'static str,
    /// The stub each entry documents itself with: what the bytes do, shown
    /// as the match's evidence.
    pub(super) stub: &'static str,
}

/// Entry stubs a packer writes, as `??`-wildcard patterns read at the entry
/// point. Each entry's [`EntrySig::stub`] line is its documentation.
pub(super) const PACKER_ENTRY_SIGS: [EntrySig; 5] = [
    EntrySig {
        packer: "SteamStub",
        pattern: "60 81 EC 00 10 00 00 BE ?? ?? ?? ?? B9 ?? ?? ?? ?? 8D BD ?? ?? ?? ?? F3 A5",
        stub: "pushad; sub esp, 0x1000; mov esi, imm32; mov ecx, imm32; lea \
               edi, [ebp+disp32]; rep movsd: an x86 SteamStub before 3.x",
    },
    EntrySig {
        packer: "SteamStub",
        pattern: "E8 00 00 00 00 50 53 51 52 56 57 55 41 50 41 51",
        stub: "call $+5; push rax..rbp; push r8; push r9: an x64 SteamStub 3.x",
    },
    EntrySig {
        packer: "UPX",
        pattern: "60 BE ?? ?? ?? ?? 8D BE ?? ?? ?? ?? 57 83 CD FF EB",
        stub: "pushad; mov esi, imm32; lea edi, [esi+disp32]; push edi; or \
               ecx, -1",
    },
    EntrySig {
        packer: "FSG",
        pattern: "87 25 ?? ?? ?? ?? 61 94 F3 A5 5F C3",
        stub: "xchg esp, [imm32]; popad; xchg eax, ebp; rep movsd; pop edi; \
               ret",
    },
    EntrySig {
        packer: "ASPack",
        pattern: "60 E8 03 00 00 00 E9 EB 04 5D 45 55 C3",
        stub: "pushad; call $+8; jmp; pop ebp; inc ebp; push ebp; ret",
    },
];

/// Bytes read at the entry point when matching [`PACKER_ENTRY_SIGS`], enough
/// for the longest stub and no more.
pub(super) const ENTRY_STUB_MAX: usize = 25;

/// Sections whose holding the entry point is itself a protector's mark, and
/// the family that places one there.
pub(super) const ENTRY_SECTION_MARKS: [(&str, &str); 3] = [
    (".boot", "Themida/WinLicense"),
    (".init", "Themida/WinLicense"),
    (".bind", "SteamStub"),
];

/// The signatures a `SteamStub` 3.x header decodes to, and the variant each
/// names.
const STEAMSTUB_SIGNATURES: [(u32, &str); 2] = [(0xc0de_c0de, "3.0"), (0xc0de_c0df, "3.1")];
/// The lengths a `SteamStub` 3.x header has, by variant and width; it ends
/// where the stub's entry point begins.
const STEAMSTUB_HEADERS: [usize; 3] = [0xf0, 0xd0, 0xb0];
/// The x64 `SteamStub` 3.1 header's length, the one layout whose fields are
/// read.
const STEAMSTUB_X64_31: usize = 0xf0;
/// The `SteamStub` flag that leaves the code section unencrypted.
const STEAMSTUB_NO_ENCRYPTION: u32 = 0x4;

/// The `SteamStub` 3.x header that ends at the entry point, decoded.
///
/// Each word decodes by XOR with the encoded word before it, the first being
/// the key. For the x64 3.1 layout the header also gives the Steam app id, the
/// original entry point and whether the code section is encrypted.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// What the header says, or `None` when no length before the entry point
/// decodes to a `SteamStub` signature.
pub(super) fn steamstub_header(p: &Program) -> Option<String> {
    let entry = p.entry?;
    STEAMSTUB_HEADERS.iter().find_map(|&len| {
        let start = entry.checked_sub(from_usize(len))?;
        let words: Vec<u32> = p
            .read_va(start, len)?
            .chunks_exact(4)
            .filter_map(|w| crate::num::u32_le(w, 0))
            .collect();
        let mut key = *words.first()?;
        let decoded: Vec<u32> = words
            .iter()
            .skip(1)
            .map(|&w| {
                let d = w ^ key;
                key = w;
                d
            })
            .collect();
        let (_, variant) = STEAMSTUB_SIGNATURES
            .iter()
            .find(|s| decoded.first() == Some(&s.0))?;
        let field = |off: usize| decoded.get(off / 4 - 1).copied();
        let mut text = format!("SteamStub {variant} header at {start:#x}, decoded");
        if p.is_64
            && *variant == "3.1"
            && len == STEAMSTUB_X64_31
            && let (Some(oep), Some(app), Some(flags)) = (field(0x20), field(0x38), field(0x3c))
        {
            let _ = write!(
                text,
                ": Steam app id {app}, original entry point {:#x}, {}",
                p.image_base.saturating_add(u64::from(oep)),
                if flags & STEAMSTUB_NO_ENCRYPTION == 0 {
                    "the code section is encrypted"
                } else {
                    "the code section is not encrypted"
                }
            );
        }
        Some(text)
    })
}

/// ASCII markers a protector rebuilds into the DOS header, and their family.
pub(super) const HEADER_MARKS: [(&str, &str); 1] = [("tELock", "tELock")];

/// The entry stubs the image's entry point starts with.
///
/// A stub is written once by the packer, not by a compiler, so a match at the
/// entry point names the family whatever the sections are called; UPX keeps
/// its names, but a renamed or hand-built section table hides every other
/// packer's.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// Each signature whose pattern the first [`ENTRY_STUB_MAX`] entry bytes
/// match, with the entry point it matched at, in table order; empty when
/// there is no entry point or its bytes cannot be read.
pub(super) fn entry_stubs(p: &Program) -> Vec<(&'static EntrySig, u64)> {
    let Some(entry) = p.entry else {
        return Vec::new();
    };
    let Some(bytes) = p.read_va_upto(entry, ENTRY_STUB_MAX) else {
        return Vec::new();
    };
    PACKER_ENTRY_SIGS
        .iter()
        .filter(|sig| {
            crate::search::parse_pattern(sig.pattern).is_some_and(|pat| {
                pat.len() <= bytes.len()
                    && pat
                        .iter()
                        .zip(bytes)
                        .all(|(p, b)| p.is_none_or(|p| p == *b))
            })
        })
        .map(|sig| (sig, entry))
        .collect()
}

/// Entropy at or above which a section reads as compressed or encrypted.
pub(super) const PACKED_ENTROPY: f64 = 7.2;

/// Imports below which the table is a stub that resolves the rest at runtime.
pub(super) const THIN_IMPORTS: usize = 12;

/// Executable bytes per function above which the code found cannot be the
/// whole program: ordinary compiled code runs a few hundred bytes a
/// function, and a packer leaves one stub in front of megabytes.
pub(super) const SPARSE_CODE: u64 = 2048;

/// The `UPX!` mark UPX writes into the headers of what it packs, back to
/// front ([`crate::fileinfo::reversed`]) so borer's own binary does not
/// carry it.
const UPX_MARK: [u8; 4] = crate::fileinfo::reversed(b"UPX!");

/// Where UPX's `UPX!` mark sits in the PE headers and the UPX version
/// written just before it (`4.22`), when it is printable.
///
/// # Arguments
///
/// * `header` - The bytes before the first section.
pub(super) fn upx_header(header: &[u8]) -> Option<(usize, Option<String>)> {
    let at = crate::fileinfo::find(header, &crate::fileinfo::forward(&UPX_MARK))?;
    let before = header.get(at.saturating_sub(6)..at.saturating_sub(1))?;
    let digits = before
        .iter()
        .rev()
        .take_while(|b| b.is_ascii_digit() || **b == b'.')
        .count();
    let version = String::from_utf8_lossy(before.get(before.len() - digits..)?).into_owned();
    Some((at, version.contains('.').then_some(version)))
}

/// The packers and protectors the image names by a mark only they leave:
/// a section they write, their entry stub, where the entry point sits, or a
/// marker in the headers.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// Each family found with its marks, by family name.
pub fn packer_marks(p: &Program) -> BTreeMap<&'static str, Vec<String>> {
    let mut names: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    for s in &p.sections {
        for (mark, name) in PACKER_SECTIONS {
            if s.name.eq_ignore_ascii_case(mark) {
                names
                    .entry(name)
                    .or_default()
                    .push(format!("{mark} section"));
            }
        }
    }
    for (sig, entry) in entry_stubs(p) {
        names
            .entry(sig.packer)
            .or_default()
            .push(format!("entry stub at {entry:#x} ({})", sig.stub));
    }
    if let Some(sec) = p.entry.and_then(|e| p.section_at(e)) {
        for (mark, family) in ENTRY_SECTION_MARKS {
            if sec.name.eq_ignore_ascii_case(mark) {
                names
                    .entry(family)
                    .or_default()
                    .push(format!("entry point in {}", sec.name));
            }
        }
    }
    if let Some(header) = steamstub_header(p) {
        names.entry("SteamStub").or_default().push(header);
    }
    if let Some(first) = p
        .sections
        .iter()
        .filter(|s| s.file_size > 0)
        .map(|s| s.file_off.0)
        .min()
    {
        let header_end = usize::try_from(first).unwrap_or(0).min(p.bytes.len());
        if let Some(header) = p.bytes.get(..header_end) {
            for (needle, family) in HEADER_MARKS {
                let bytes = needle.as_bytes();
                if header.windows(bytes.len()).any(|w| w == bytes) {
                    names
                        .entry(family)
                        .or_default()
                        .push(format!("{needle} marker in the DOS header"));
                }
            }
            if let Some((at, version)) = upx_header(header) {
                names.entry("UPX").or_default().push(format!(
                    "UPX! mark at {at:#x} in the headers{}",
                    version.map_or_else(String::new, |v| format!(", written by UPX {v}"))
                ));
            }
        }
    }
    names
}

/// Reports the marks a packer or protector leaves.
///
/// Nothing here decrypts anything: it says what the image looks like before
/// it unpacks itself, which is what decides whether reading the static text
/// is worth anything. The name comes from [`packer_marks`]; the rest is
/// evidence any packer leaves whatever its name: a high-entropy body, an
/// import table too thin to run the program, a section that is both
/// writable and executable, an entry point outside the code, an entry point
/// in writable memory, and executable bytes with almost no code found in
/// them.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for how much code was found.
///
/// # Returns
///
/// The verdict, the evidence and the section table.
pub fn protection_tsv(p: &Program, a: &Analysis) -> String {
    let names = packer_marks(p);
    let mut evidence: Vec<String> = Vec::new();
    let mut rows = String::new();
    let mut packed_bytes = 0u64;
    let mut total_bytes = 0u64;
    let mut wx: Vec<&str> = Vec::new();
    for s in &p.sections {
        let len = usize::try_from(s.file_size).unwrap_or(0);
        let e = p.read_va(s.va.0, len).map_or(0.0, crate::entropy::shannon);
        total_bytes += s.file_size;
        if e >= PACKED_ENTROPY {
            packed_bytes += s.file_size;
        }
        if s.writable && s.executable {
            wx.push(&s.name);
        }
        let grows = s.vsize > s.file_size * 2 && s.file_size > 0;
        let _ = writeln!(
            rows,
            "{:<12} {:#012x}  {:>10}  {:>10}  {}  {e:>5.2}{}",
            s.name,
            s.va.0,
            s.file_size,
            s.vsize,
            s.perms(),
            if grows { "  expands in memory" } else { "" }
        );
    }
    let imports = p
        .symbols
        .iter()
        .filter(|s| matches!(s.kind, SymbolKind::Import))
        .count();
    let entry_section = p
        .entry
        .and_then(|e| p.section_at(e))
        .map(|s| s.name.clone());
    if total_bytes > 0 && packed_bytes * 2 >= total_bytes {
        evidence.push(format!(
            "{}% of the file is at entropy {PACKED_ENTROPY} or above",
            packed_bytes * 100 / total_bytes
        ));
    }
    if imports < THIN_IMPORTS {
        evidence.push(format!("{imports} imports, too few to run a program"));
    }
    if !wx.is_empty() {
        evidence.push(format!("writable and executable: {}", wx.join(", ")));
    }
    let first_code = p.sections.iter().find(|s| s.executable).map(|s| &s.name);
    if let Some(name) = &entry_section
        && first_code.is_some_and(|f| f != name)
    {
        evidence.push(format!("entry point in {name}, not the first code section"));
    }
    if !p.headers.tls_callbacks.is_empty() {
        evidence.push(format!(
            "{} TLS callback(s), which run before the entry point",
            p.headers.tls_callbacks.len()
        ));
    }
    if p.entry
        .and_then(|e| p.section_at(e))
        .is_some_and(|s| s.writable)
    {
        evidence.push("the entry point sits in writable memory".to_owned());
    }
    let code_bytes: u64 = p
        .sections
        .iter()
        .filter(|s| s.executable)
        .map(|s| s.file_size)
        .sum();
    let covered = from_usize(a.functions.len());
    if code_bytes > 0x10000 && covered * SPARSE_CODE < code_bytes {
        evidence.push(format!(
            "{covered} functions in {} KB of executable bytes, one per {} bytes",
            code_bytes / 1024,
            code_bytes / covered.max(1)
        ));
    }
    let verdict = if !names.is_empty() {
        format!(
            "protected: {}",
            names.keys().copied().collect::<Vec<_>>().join(", ")
        )
    } else if evidence.len() >= 2 {
        "packed: no name, but the marks are there".to_owned()
    } else if evidence.is_empty() {
        "plain: no packer marks".to_owned()
    } else {
        "plain: one mark only, not enough to call it packed".to_owned()
    };
    let mut out = format!("# {verdict}\n");
    for (name, marks) in &names {
        let _ = writeln!(out, "# - {name}: {}", marks.join("; "));
    }
    for e in &evidence {
        let _ = writeln!(out, "# - {e}");
    }
    out.push_str("# section      va             raw         virtual  rwx  entropy\n");
    out.push_str(&rows);
    out
}
