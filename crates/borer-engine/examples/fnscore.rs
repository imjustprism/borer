//! Function discovery scored against a PDB's ground truth.
//!
//! ```text
//! cargo run --release --example fnscore -- <binary> [pdb] [options]
//!
//!   --samples <n>    addresses listed under each class (default 12)
//!   --bounds         list the functions found short, with what was missed
//!   --probe <a,b..>  say what the PDB and borer each have at these addresses
//!   --pack <file>    run with a pack, and score the library names it gives
//! ```
//!
//! Without a pdb, the public one is fetched from the Microsoft symbol server
//! into `target/symcache` (`BORER_SYMCACHE` names another directory). The
//! Windows system DLLs score that way; a program built with `/Zi` scores
//! against its own full PDB, which names the statics too.
//!
//! Recall is the share of the PDB's functions borer found, precision the
//! share of borer's functions the PDB names, and the boundaries the share of
//! the functions whose size the PDB states that borer covers exactly: no
//! byte of theirs left out (padding aside) and none of another function's
//! taken. An `__except` body inside its function is the function's own
//! code to both, and is left out of the count.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use borer_engine::analysis::{Analysis, BlockTerm, FuncletRole, Function, NameSource};
use borer_engine::num::{saturating_usize, usize_f64};
use borer_engine::pack::{Pack, Packs};
use borer_engine::program::Program;
use pdb::FallibleIterator;

/// A function the PDB names: its size when the PDB states it, and its name.
struct Truth {
    /// The size, from a module's procedure record; a public has none.
    size: Option<u32>,
    /// The name, decorated as the PDB has it.
    name: String,
}

/// What the command line asked for.
struct Options {
    /// The binary.
    binary: PathBuf,
    /// Its PDB, when given.
    pdb: Option<PathBuf>,
    /// Addresses listed under each class.
    samples: usize,
    /// Whether to list the short functions.
    bounds: bool,
    /// Addresses to explain.
    probe: Vec<u64>,
    /// A pack to run with.
    pack: Option<PathBuf>,
}

/// Reads the command line.
///
/// # Arguments
///
/// * `args` - The arguments after the program's name.
///
/// # Errors
///
/// When the binary is missing or an option is not understood.
fn options(args: &[String]) -> Result<Options, Box<dyn Error>> {
    let mut out = Options {
        binary: PathBuf::new(),
        pdb: None,
        samples: 12,
        bounds: false,
        probe: Vec::new(),
        pack: None,
    };
    let mut positional = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let value = |i: usize| -> Result<&String, Box<dyn Error>> {
            args.get(i + 1)
                .ok_or_else(|| format!("{a} needs a value").into())
        };
        match a {
            "--samples" => {
                out.samples = value(i)?.parse()?;
                i += 1;
            }
            "--bounds" => out.bounds = true,
            "--probe" => {
                for p in value(i)?.split(',') {
                    let p = p.trim().trim_start_matches("0x");
                    out.probe.push(u64::from_str_radix(p, 16)?);
                }
                i += 1;
            }
            "--pack" => {
                out.pack = Some(PathBuf::from(value(i)?));
                i += 1;
            }
            _ => positional.push(PathBuf::from(a)),
        }
        i += 1;
    }
    let mut positional = positional.into_iter();
    out.binary = positional.next().ok_or("usage: fnscore <binary> [pdb]")?;
    out.pdb = positional.next();
    Ok(out)
}

/// Fetches the program's PDB from the Microsoft symbol server, unless it is
/// in the cache already.
///
/// # Arguments
///
/// * `program` - The loaded image, whose debug directory names the PDB.
///
/// # Returns
///
/// The cached file, or `None` when the image names no PDB or the fetch
/// fails.
fn fetch_pdb(program: &Program) -> Option<PathBuf> {
    // `<path> (pdb <guid><age>)`, as the headers spell it.
    let id = program.headers.debug_id.as_deref()?;
    let (path, rest) = id.rsplit_once(" (pdb ")?;
    let guid_age = rest.strip_suffix(')')?;
    let name = path.rsplit(['\\', '/']).next()?.to_owned();
    let cache = std::env::var_os("BORER_SYMCACHE")
        .map_or_else(|| PathBuf::from("target/symcache"), PathBuf::from);
    let dir = cache.join(&name).join(guid_age);
    let out = dir.join(&name);
    if out.exists() {
        return Some(out);
    }
    std::fs::create_dir_all(&dir).ok()?;
    let url = format!("https://msdl.microsoft.com/download/symbols/{name}/{guid_age}/{name}");
    let ok = std::process::Command::new("curl")
        .args(["-sfL", "-A", "Microsoft-Symbol-Server/10.0.0.0", "-o"])
        .arg(&out)
        .arg(&url)
        .status()
        .ok()?
        .success();
    if !ok {
        eprintln!("fetch failed: {url}");
        return None;
    }
    Some(out)
}

/// Reads the PDB's functions by RVA: every public marked function or code,
/// and every module procedure and thunk, which carry a size.
///
/// # Arguments
///
/// * `path` - The PDB.
///
/// # Errors
///
/// When the PDB cannot be read.
fn truth(path: &Path) -> Result<BTreeMap<u32, Truth>, pdb::Error> {
    let mut pdb = pdb::PDB::open(std::fs::File::open(path)?)?;
    let map = pdb.address_map()?;
    let mut out: BTreeMap<u32, Truth> = BTreeMap::new();
    let globals = pdb.global_symbols()?;
    let mut it = globals.iter();
    while let Some(s) = it.next()? {
        if let Ok(pdb::SymbolData::Public(p)) = s.parse()
            && (p.function || p.code)
            && let Some(rva) = p.offset.to_rva(&map)
        {
            out.entry(rva.0).or_insert(Truth {
                size: None,
                name: p.name.to_string().into_owned(),
            });
        }
    }
    let dbi = pdb.debug_information()?;
    let mut modules = dbi.modules()?;
    while let Some(m) = modules.next()? {
        let Some(info) = pdb.module_info(&m)? else {
            continue;
        };
        let mut syms = info.symbols()?;
        while let Some(s) = syms.next()? {
            let (rva, len, name) = match s.parse() {
                Ok(pdb::SymbolData::Procedure(p)) => (
                    p.offset.to_rva(&map),
                    p.len,
                    p.name.to_string().into_owned(),
                ),
                Ok(pdb::SymbolData::Thunk(t)) => (
                    t.offset.to_rva(&map),
                    u32::from(t.len),
                    t.name.to_string().into_owned(),
                ),
                _ => continue,
            };
            let Some(rva) = rva else { continue };
            let e = out.entry(rva.0).or_insert(Truth {
                size: None,
                name: name.clone(),
            });
            e.size = Some(len);
            if e.name.is_empty() {
                e.name = name;
            }
        }
    }
    Ok(out)
}

/// A name as both a PDB and a library spell it: demangled and bare, the
/// 32-bit C decorations and the spellings the two demanglers differ on
/// evened out.
///
/// # Arguments
///
/// * `name` - A name from either side.
fn plain_name(name: &str) -> String {
    let d = borer_engine::search::demangled_name(name);
    let d = if name.starts_with('?') {
        d
    } else {
        let t = d
            .strip_prefix('_')
            .or_else(|| d.strip_prefix('@'))
            .unwrap_or(&d);
        match t.rsplit_once('@') {
            Some((h, n)) if !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()) => h.to_owned(),
            _ => t.to_owned(),
        }
    };
    d.replace("class ", "")
        .replace("struct ", "")
        .replace("__cdecl *", "__cdecl*")
        .replace("__stdcall *", "__stdcall*")
        .replace("unsigned __int64", "uint64_t")
        .replace("__int64", "int64_t")
        .trim_start_matches('_')
        .to_owned()
}

/// Cuts a name for a listing.
///
/// # Arguments
///
/// * `name` - The name.
/// * `n` - Most characters kept.
fn short(name: &str, n: usize) -> String {
    name.chars().take(n).collect()
}

/// Scores one binary and prints the report.
///
/// # Errors
///
/// When the binary, the PDB or the pack cannot be read.
fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let opts = options(&args)?;
    let program = Program::load(&opts.binary)?;
    let pdb_path = match &opts.pdb {
        Some(p) => p.clone(),
        None => fetch_pdb(&program).ok_or("no PDB given and none fetched")?,
    };
    #[expect(
        clippy::disallowed_methods,
        reason = "the scorer reports how long discovery took"
    )]
    let started = std::time::Instant::now();
    let a = match &opts.pack {
        Some(file) => {
            let text = std::fs::read_to_string(file)?;
            let (pack, _) = Pack::parse(&text, &file.display().to_string())?;
            Analysis::compute_with(&program, Arc::new(Packs { packs: vec![pack] }))
        }
        None => Analysis::compute(&program),
    };
    let secs = started.elapsed().as_secs_f64();
    let base = program.image_base;
    let exec = |va: u64| {
        program
            .sections
            .iter()
            .any(|s| s.executable && va >= s.va && va < s.va + s.vsize.max(s.file_size))
    };
    let truth: BTreeMap<u64, Truth> = truth(&pdb_path)?
        .into_iter()
        .map(|(rva, t)| (base + u64::from(rva), t))
        .filter(|(va, _)| exec(*va))
        .collect();
    let starts: Vec<u64> = truth.keys().copied().collect();
    // Where each truth function ends: its size, else the next start.
    let extent = |va: u64| -> u64 {
        match truth.get(&va).and_then(|t| t.size) {
            Some(n) if n > 0 => va + u64::from(n),
            _ => starts
                .get(starts.partition_point(|&s| s <= va))
                .copied()
                .unwrap_or(va + 1),
        }
    };
    let truth_owner = |va: u64| -> Option<u64> {
        let i = starts.partition_point(|&s| s <= va).checked_sub(1)?;
        let s = starts[i];
        (va < extent(s)).then_some(s)
    };
    // An `__except` body is the function's own code to a PDB as to borer.
    let found: BTreeMap<u64, &Function> = a
        .functions
        .iter()
        .filter(|f| !matches!(f.funclet.map(|x| x.role), Some(FuncletRole::Except(_))))
        .map(|f| (f.entry, f))
        .collect();
    let mut covered: BTreeMap<u64, (u64, u64)> = BTreeMap::new();
    for f in &a.functions {
        for b in &f.blocks {
            covered.insert(b.start, (b.end, f.entry));
        }
    }
    let owner = |va: u64| -> Option<u64> {
        covered
            .range(..=va)
            .next_back()
            .filter(|(_, (end, _))| va < *end)
            .map(|(_, (_, e))| *e)
    };
    let declared: BTreeSet<u64> = program.function_ranges.iter().map(|r| r.0).collect();

    let hit = truth.keys().filter(|va| found.contains_key(va)).count();
    let recall = 100.0 * usize_f64(hit) / usize_f64(truth.len().max(1));
    let precision = 100.0 * usize_f64(hit) / usize_f64(found.len().max(1));
    println!("{}  ({secs:.1}s)", opts.binary.display());
    println!(
        "  truth {} ({} sized), borer {}, matched {hit}",
        truth.len(),
        truth.values().filter(|t| t.size.is_some()).count(),
        found.len()
    );
    println!("  recall {recall:.2}%  precision {precision:.2}%");
    if a.incomplete {
        println!("  INCOMPLETE: the walk's budget ran out");
    }

    let mut misses: BTreeMap<&str, Vec<u64>> = BTreeMap::new();
    for &va in truth.keys() {
        if found.contains_key(&va) {
            continue;
        }
        let size = extent(va) - va;
        let class = match owner(va) {
            Some(_) => "absorbed into another function",
            None if size <= 2 => "undecoded, tiny (<=2 bytes)",
            None if declared.contains(&va) => "undecoded, with an exception-table entry",
            None => "undecoded",
        };
        misses.entry(class).or_default().push(va);
    }
    let mut extras: BTreeMap<&str, Vec<u64>> = BTreeMap::new();
    for &va in found.keys() {
        if truth.contains_key(&va) {
            continue;
        }
        let class = match truth_owner(va) {
            Some(s) if truth[&s].size.is_some() => "inside a sized truth function",
            Some(_) => "inside a public's span (may be a static the PDB leaves out)",
            None => "outside every truth function",
        };
        extras.entry(class).or_default().push(va);
    }

    // Boundaries over the functions whose size the PDB states.
    let is_pad = |va: u64| program.read_va(va, 1) == Some(&[0xcc][..]);
    let bitness = if program.is_64 { 64 } else { 32 };
    let nop_run = |lo: u64, hi: u64| -> bool {
        let Some(bytes) = program.read_va(lo, saturating_usize(hi - lo)) else {
            return false;
        };
        let mut d = borer_engine::isa::Decoder::with_ip(
            bitness,
            bytes,
            lo,
            borer_engine::isa::DecoderOptions::NONE,
        );
        d.iter().all(|i| {
            matches!(
                i.mnemonic(),
                borer_engine::isa::Mnemonic::Nop | borer_engine::isa::Mnemonic::Int3
            )
        })
    };
    let (mut exact, mut chunked) = (0usize, 0usize);
    let mut shorts: Vec<(u64, u64, u64, u64)> = Vec::new();
    let mut longs: Vec<(u64, u64, u64)> = Vec::new();
    for (&va, t) in &truth {
        let (Some(f), Some(n)) = (found.get(&va), t.size) else {
            continue;
        };
        let end = va + u64::from(n);
        let mut inside: Vec<(u64, u64)> = Vec::new();
        let mut other: Option<u64> = None;
        let mut far = false;
        for b in &f.blocks {
            if b.start >= va && b.start < end {
                inside.push((b.start, b.end.min(end)));
            } else {
                // Only a sized function owns its span; an unsized public's
                // runs on over cold code to the next one.
                match truth_owner(b.start) {
                    Some(o) if o != va && truth[&o].size.is_some() => other = other.or(Some(o)),
                    _ => far = true,
                }
            }
        }
        inside.sort_unstable();
        let mut cur = va;
        let mut missing = 0u64;
        let mut first_gap: Option<u64> = None;
        for (lo, hi) in inside {
            if lo > cur && !nop_run(cur, lo) {
                let m = (cur..lo).filter(|&x| !is_pad(x)).count() as u64;
                if m > 0 {
                    first_gap = first_gap.or(Some(cur));
                }
                missing += m;
            }
            cur = cur.max(hi);
        }
        // A switch's tables sit after its function, inside the PDB's size.
        let has_switch = f
            .blocks
            .iter()
            .any(|b| b.term == BlockTerm::Indirect && !b.successors.is_empty());
        if !has_switch {
            let m = (cur..end).filter(|&x| !is_pad(x)).count() as u64;
            if m > 0 {
                first_gap = first_gap.or(Some(cur));
            }
            missing += m;
        }
        if let Some(o) = other {
            longs.push((va, o, end));
        } else if missing > 0 {
            shorts.push((va, missing, first_gap.unwrap_or(cur), end));
        } else {
            exact += 1;
        }
        chunked += usize::from(far);
    }
    let sized = exact + shorts.len() + longs.len();
    if sized > 0 {
        println!(
            "  boundaries over {sized} sized: exact {:.2}%, short {}, enters another {} (with far chunks {chunked})",
            100.0 * usize_f64(exact) / usize_f64(sized),
            shorts.len(),
            longs.len()
        );
    }
    for (class, v) in &misses {
        println!("  MISS {class}: {}", v.len());
        for va in v.iter().take(opts.samples) {
            let into = owner(*va)
                .map(|e| format!(" in {e:#x}"))
                .unwrap_or_default();
            println!(
                "      {va:#x} +{} {}{into}",
                extent(*va) - va,
                short(&truth[va].name, 60)
            );
        }
    }
    if !found.is_empty() {
        let (mut begins, mut inside, mut undeclared) = (0, 0, 0);
        for &va in found.keys().filter(|va| !truth.contains_key(va)) {
            if declared.contains(&va) {
                begins += 1;
            } else if program
                .function_ranges
                .iter()
                .any(|&(s, e)| s < va && va < e)
            {
                inside += 1;
            } else {
                undeclared += 1;
            }
        }
        println!(
            "  extras by the exception table: {begins} begin a declared function, {inside} inside one, {undeclared} undeclared (leaf or chunk)"
        );
    }
    for (class, v) in &extras {
        println!("  EXTRA {class}: {}", v.len());
        for va in v.iter().take(opts.samples) {
            let inside = truth_owner(*va)
                .map(|s| format!(" in {s:#x} {}", short(&truth[&s].name, 50)))
                .unwrap_or_default();
            println!("      {va:#x}{inside}");
        }
    }
    if opts.bounds {
        for (va, missing, from, end) in shorts.iter().take(opts.samples) {
            println!(
                "  SHORT {va:#x} missing {missing} bytes from {from:#x} of ..{end:#x} {}",
                short(&truth[va].name, 60)
            );
        }
        for (va, o, end) in longs.iter().take(opts.samples) {
            println!(
                "  ENTERS {va:#x} (..{end:#x}) enters {o:#x} {} / {}",
                short(&truth[va].name, 40),
                short(&truth[o].name, 40)
            );
        }
    }
    for &va in &opts.probe {
        let t = truth_owner(va).map_or_else(
            || "none".to_owned(),
            |s| format!("{s:#x}+{} {}", extent(s) - s, short(&truth[&s].name, 60)),
        );
        let b = owner(va).map_or_else(|| "none".to_owned(), |e| format!("{e:#x}"));
        println!("  PROBE {va:#x}: truth {t}; borer {b}");
    }
    if opts.pack.is_some() {
        let (mut right, mut wrong) = (0, 0);
        for f in a
            .functions
            .iter()
            .filter(|f| f.name_source == NameSource::Library)
        {
            let got = plain_name(f.name.as_deref().unwrap_or(""));
            let want = truth
                .get(&f.entry)
                .map(|t| plain_name(&t.name))
                .unwrap_or_default();
            if got == want {
                right += 1;
            } else {
                wrong += 1;
                if wrong <= opts.samples {
                    println!("  LIBRARY NAME {:#x}: {got}, the PDB says {want}", f.entry);
                }
            }
        }
        println!(
            "  library names: {right} as the PDB has them, {wrong} differ; {}",
            borer_engine::analysis::libnames::library_names_tsv(&a.library_names).trim()
        );
    }
    Ok(())
}
