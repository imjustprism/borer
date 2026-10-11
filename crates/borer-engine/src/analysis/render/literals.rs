//! Strings in both directions: the functions a string leads to, and the strings
//! a program generates.

use super::*;

/// Most strings one function's row lists.
const STRINGS_PER_FUNCTION: usize = 20;

/// Lists the functions that reference a string, one row per function with
/// the matching strings it references, the functions that run the same
/// code over the same strings folded into one.
///
/// A row per string listed a function under every string it referenced,
/// and a fifth of the lines of a typical answer repeated a function already
/// printed; a row per function prints each once, with everything it
/// references that matched, which is what the reader decompiles next. The
/// strings are numbered in a `# strings:` legend, each text printed once in
/// the order it first appears, and a row carries the numbers: a string a
/// dozen functions share costs its text once, not a dozen times, which is
/// what kept the row-per-function form from paying for itself on a
/// stripped binary. A registration table gives hundreds of one-shape
/// thunks that all name the same string, so listing every one is a wall a
/// reader cannot use: the functions whose code and matched strings are the
/// same are one row, the lowest entry standing for them, with how many more
/// there are. An answer lists at most `limit` rows from `offset` and
/// numbers at most `limit` strings, the rows cut where the legend would
/// overflow: a first row with more strings than the legend holds shows the
/// first that many and counts the rest.
///
/// The filter matches a string's text, not the quoted form it is printed
/// in: `L"` matched every wide string and `"` every string.
///
/// A protected binary does not store the strings that matter, it computes
/// them, so when nothing in the table matches the generators are asked
/// before reporting that the string is not in the program. Only on a miss:
/// running them costs more than a table lookup, and a hit there means the
/// answer could not have come from the table.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading the strings.
/// * `a` - Cross-references, functions and their shapes.
/// * `o` - User names.
/// * `filter` - Case-insensitive substring of the string.
/// * `offset` - Rows to skip first (paging).
/// * `limit` - Most rows listed, and most strings numbered.
///
/// # Returns
///
/// A `# showing N of R rows: P function/string pairs match 'f' across S
/// strings in F functions` header, the `# strings: 1="..." 2="..."` legend
/// of the page, a column header, then one `entry name: 1 2 5` row per
/// function in entry order with its strings' numbers in address order, and
/// a `# N more rows; offset=K for the next page` line when rows remain.
pub fn functions_by_string_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    filter: &str,
    offset: usize,
    limit: usize,
) -> String {
    let q = filter.to_lowercase();
    let shown_filter = crate::text::quoted(filter);
    let mut texts: BTreeMap<u64, String> = BTreeMap::new();
    let mut by_function: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
    for (target, sites) in &a.xrefs {
        let Some((start, lit)) = referenced_literal(p, a, *target, STRING_MATCH_CAP) else {
            continue;
        };
        if !unquoted(&lit).to_lowercase().contains(&q) {
            continue;
        }
        for e in sites.iter().filter_map(|s| s.from_entry) {
            by_function.entry(e).or_default().insert(start);
            texts.entry(start).or_insert_with(|| shown_text(&lit));
        }
    }
    let pairs: usize = by_function.values().map(BTreeSet::len).sum();
    if pairs == 0 && !q.is_empty() {
        let found = recovered_matching(p, a, filter).found;
        if !found.is_empty() {
            let shown = found.len().saturating_sub(offset).min(limit);
            let mut out = format!(
                "# showing {shown} of {}: no function references {shown_filter} directly; {} generate it at run time\n",
                found.len(),
                found.len()
            );
            out.push_str("# built_by                     written_at      text\n");
            for g in found.iter().skip(offset).take(limit) {
                let _ = writeln!(
                    out,
                    "{:<28} {:<#15x} {:?}",
                    short_name(a, o, g.built_by),
                    g.written_at,
                    g.text
                );
            }
            next_page_line(&mut out, found.len(), offset, shown, "texts");
            return out;
        }
    }
    let mut families: BTreeMap<(u64, &BTreeSet<u64>), (u64, usize)> = BTreeMap::new();
    for (&e, strings) in &by_function {
        let shape = a.function(e).map_or(0, |f| f.shape_hash);
        let family = families.entry((shape, strings)).or_insert((e, 0));
        if family.0 != e {
            family.1 += 1;
        }
    }
    let mut rows: Vec<(u64, usize, &BTreeSet<u64>)> = families
        .iter()
        .map(|(&(_, strings), &(e, more))| (e, more, strings))
        .collect();
    rows.sort_unstable_by_key(|r| r.0);
    let mut numbers: BTreeMap<u64, usize> = BTreeMap::new();
    let mut legend: Vec<u64> = Vec::new();
    let mut body = String::new();
    let mut listed = 0usize;
    for &(e, more, strings) in rows.iter().skip(offset).take(limit) {
        let fresh = strings
            .iter()
            .take(STRINGS_PER_FUNCTION)
            .filter(|start| !numbers.contains_key(start))
            .count();
        if listed > 0 && legend.len() + fresh > limit {
            break;
        }
        listed += 1;
        let _ = write!(body, "{e:#x} {}:", name_of(a, o, e));
        let mut unnumbered = 0usize;
        for start in strings.iter().take(STRINGS_PER_FUNCTION) {
            let number = match numbers.get(start) {
                Some(&n) => n,
                None if legend.len() < limit => {
                    legend.push(*start);
                    numbers.insert(*start, legend.len());
                    legend.len()
                }
                None => {
                    unnumbered += 1;
                    continue;
                }
            };
            let _ = write!(body, " {number}");
        }
        let rest = unnumbered + strings.len().saturating_sub(STRINGS_PER_FUNCTION);
        if rest > 0 {
            let _ = write!(body, " (+{rest} more strings)");
        }
        if more > 0 {
            let _ = write!(
                body,
                " (+{more} function{} running the same code)",
                plural(more)
            );
        }
        body.push('\n');
    }
    let mut out = format!(
        "# showing {listed} of {} row{}: {pairs} function/string pairs match {shown_filter} across {} string{} in {} function{}\n# strings:",
        rows.len(),
        plural(rows.len()),
        texts.len(),
        plural(texts.len()),
        by_function.len(),
        plural(by_function.len())
    );
    for (i, start) in legend.iter().enumerate() {
        let _ = write!(
            out,
            " {}={}",
            i + 1,
            texts.get(start).map_or("", String::as_str)
        );
    }
    out.push_str("\n# entry name: string numbers\n");
    out.push_str(&body);
    next_page_line(&mut out, rows.len(), offset, listed, "rows");
    out
}

/// The text of a quoted literal, without the quotes and the `L` of a wide
/// one, which a filter matches.
///
/// # Arguments
///
/// * `lit` - A literal as `string_literal` quotes it: `"..."` or `L"..."`.
fn unquoted(lit: &str) -> &str {
    lit.strip_prefix("L\"")
        .or_else(|| lit.strip_prefix('"'))
        .and_then(|body| body.strip_suffix('"'))
        .unwrap_or(lit)
}

/// Writes `# N more <what>; offset=K for the next page` when a page did not
/// reach the end.
///
/// # Arguments
///
/// * `out` - The answer.
/// * `total` - How many there are.
/// * `offset` - Where the page started.
/// * `shown` - How many the page listed.
/// * `what` - The noun, plural.
fn next_page_line(out: &mut String, total: usize, offset: usize, shown: usize, what: &str) {
    let next = offset.saturating_add(shown);
    if next < total {
        let _ = writeln!(
            out,
            "# {} more {what}; offset={next} for the next page",
            total - next
        );
    }
}

/// Returns the import an instruction's memory operand names, if it names one.
///
/// `call qword [rel 14029dd20h]` is how a PE reaches an import without a
/// thunk, and the slot address is the only thing that says which import it
/// is. Left as a number, every such call and tail jump reads as a branch
/// into data.
///
/// # Arguments
///
/// * `p` - The loaded image, for its symbol table.
/// * `text` - The rendered instruction.
///
/// # Returns
///
/// The import's full `dll!name`, or `None` when the operand is not a bare
/// absolute or rip-relative address with an import slot at it.
pub(super) fn memory_import<'a>(p: &'a Program, text: &str) -> Option<&'a str> {
    let inside = text.split_once('[')?.1.split_once(']')?.0;
    let hex = inside.strip_prefix("rel ").unwrap_or(inside).trim();
    let addr = u64::from_str_radix(hex.strip_suffix('h')?, 16).ok()?;
    p.symbols
        .iter()
        .find(|s| matches!(s.kind, SymbolKind::Import) && s.addr == addr && s.addr != 0)
        .map(|s| s.name.as_str())
}

/// Gathers the runs of printable text among bytes placed in order.
///
/// A run is bytes at consecutive positions that are all printable ASCII; a
/// gap, a position going backwards or a byte outside that range ends it.
/// The position is whatever addresses the bytes: a virtual address for the
/// bytes a run wrote, a frame offset for the bytes a function stores.
///
/// # Arguments
///
/// * `placed` - `(position, byte)` pairs in the order they are read.
///
/// # Returns
///
/// `(position of the first byte, text)` for every run.
pub(super) fn printable_runs(placed: impl Iterator<Item = (u64, u8)>) -> Vec<(u64, String)> {
    let mut runs: Vec<(u64, String)> = Vec::new();
    let mut cur = String::new();
    let mut start = 0u64;
    let mut last: Option<u64> = None;
    for (at, b) in placed {
        let contiguous = last.is_some_and(|l| at == l.wrapping_add(1));
        let printable = (0x20..0x7f).contains(&b);
        if (!contiguous || !printable) && !cur.is_empty() {
            runs.push((start, std::mem::take(&mut cur)));
        }
        if printable {
            if cur.is_empty() {
                start = at;
            }
            cur.push(char::from(b));
            last = Some(at);
        } else {
            last = None;
        }
    }
    if !cur.is_empty() {
        runs.push((start, cur));
    }
    runs
}

/// Gathers the runs of printable text a run wrote, in address order.
///
/// A routine that builds a string writes it byte by byte, so the writes
/// themselves carry the plaintext whether or not the program keeps it.
///
/// # Arguments
///
/// * `writes` - The bytes the run wrote, in address order.
/// * `min` - Shortest run reported, in characters.
///
/// # Returns
///
/// `(address of the first byte, text)` for every contiguous printable run of
/// at least `min` characters.
pub(super) fn written_text(writes: &[Written], min: usize) -> Vec<(u64, String)> {
    let mut runs = printable_runs(writes.iter().map(|w| (w.addr, w.value)));
    runs.retain(|(_, t)| t.chars().count() >= min);
    runs
}

/// One string a program builds at run time instead of storing.
#[derive(Debug, Clone)]
pub struct Generated {
    /// Where the run wrote the text.
    pub written_at: u64,
    /// Entry of the function that built it.
    pub built_by: u64,
    /// The recovered text.
    pub text: String,
}

/// What running a program's string generators recovered, and how the runs
/// went.
#[derive(Debug, Clone, Default)]
pub struct Recovery {
    /// The strings recovered, in the order the runs found them.
    pub found: Vec<Generated>,
    /// How many runs ended each way, by stop reason.
    pub stops: BTreeMap<String, usize>,
    /// Start points run.
    pub runs: usize,
    /// Functions holding a keystream's constants.
    pub generators: usize,
}

/// Recovers the strings a program generates instead of storing.
///
/// A protector keeps its endpoint, its key material and its messages as
/// ciphertext and a seed, and rebuilds each one where it is used. Nothing in
/// the strings table shows them, and the code that makes them reads as sixty
/// lines of shifts and multiplies. Running that code is what reads them: the
/// generator takes its ciphertext from the image and its keystream from
/// constants, so the bytes it writes are the plaintext.
///
/// Unmapped reads answer zero, because the generator sits inside a larger
/// function whose arguments are unknown. The loop does not depend on them,
/// and stopping at the first unknown read recovers nothing. Each generator is
/// run from its entry and from the blocks around the mixer: starting at the
/// entry runs argument-dependent code that can branch past the generator
/// entirely, starting at the generator's own block skips that, and the
/// machine's stack pointer is valid either way.
///
/// One string reached from two start points is one string, and a fragment of
/// a longer recovery is the same string seen from a start that joined the
/// loop late. The address reported is where this run put it, which is not
/// always where the program would: a destination read through an
/// uninitialised pointer answers zero under a permissive read, and the
/// plaintext then lands near null. The text is still the text.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the functions holding a keystream's constants.
/// * `filter` - Case-insensitive substring; empty keeps everything.
///
/// # Returns
///
/// The recovered strings, and how each run ended, by stop reason.
#[must_use]
pub fn generated_strings(p: &Program, a: &Analysis, filter: &str) -> Recovery {
    /// Shortest recovered text kept.
    const MIN_LEN: usize = 6;
    /// Instructions each candidate is given.
    const BUDGET: usize = 300_000;
    /// Candidates run, so one binary cannot run for ever.
    const CANDIDATES_MAX: usize = 400;
    /// Blocks before the mixer that a run may start at, to pick up the
    /// ciphertext load and the buffer the loop fills.
    const BLOCKS_BACK: usize = 3;
    let want = filter.to_lowercase();
    let mut seeds: BTreeSet<u64> = BTreeSet::new();
    let mut funcs: BTreeSet<u64> = BTreeSet::new();
    for hit in crate::crypto::find_crypto_constants(p) {
        if !hit.name.contains("obfuscation") && !hit.name.contains("gamma") {
            continue;
        }
        let Some((va, f)) = hit.va.and_then(|va| Some((va, a.function_at(va)?))) else {
            continue;
        };
        funcs.insert(f.entry);
        seeds.insert(f.entry);
        if let Some(i) = f.blocks.iter().position(|b| b.start <= va && va < b.end) {
            for back in 0..=BLOCKS_BACK {
                if let Some(b) = i.checked_sub(back).and_then(|j| f.blocks.get(j)) {
                    seeds.insert(b.start);
                }
            }
        }
    }
    let mut found: Vec<Generated> = Vec::new();
    let mut stops: BTreeMap<String, usize> = BTreeMap::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut runs = 0usize;
    for entry in seeds.iter().copied().take(CANDIDATES_MAX) {
        let Some(mut emu) = Emulator::new(p, BUDGET) else {
            return Recovery {
                found: Vec::new(),
                stops,
                runs,
                generators: funcs.len(),
            };
        };
        emu.install_imports();
        emu.set_permissive(true);
        let run = emu.run(entry);
        runs += 1;
        *stops.entry(run.stop.to_string()).or_default() += 1;
        for (written_at, text) in written_text(&run.history, MIN_LEN) {
            if !want.is_empty() && !text.to_lowercase().contains(&want) {
                continue;
            }
            if !seen.insert(text.clone()) {
                continue;
            }
            found.push(Generated {
                written_at,
                built_by: entry,
                text,
            });
        }
    }
    let texts: Vec<String> = found.iter().map(|g| g.text.clone()).collect();
    found.retain(|g| {
        !texts
            .iter()
            .any(|other| other.len() > g.text.len() && other.contains(g.text.as_str()))
    });
    Recovery {
        found,
        stops,
        runs,
        generators: funcs.len(),
    }
}

/// The strings the program generates that contain `filter`, from the one
/// recovery an analysis keeps ([`recovered_strings`]).
///
/// Filtering the whole recovery is what [`generated_strings`] answers for
/// the filter: a text is dropped there when a longer recovered text holds
/// it, and that longer text holds the filter too, so it is kept by both;
/// the de-duplication keeps the first run's copy either way, and the runs
/// and their stops do not depend on the filter.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, holding the recovery.
/// * `filter` - Case-insensitive substring; empty keeps everything.
///
/// # Returns
///
/// The recovery with only the matching strings.
fn recovered_matching(p: &Program, a: &Analysis, filter: &str) -> Recovery {
    let all = recovered_strings(p, a);
    let want = filter.to_lowercase();
    Recovery {
        found: all
            .found
            .iter()
            .filter(|g| want.is_empty() || g.text.to_lowercase().contains(&want))
            .cloned()
            .collect(),
        stops: all.stops.clone(),
        runs: all.runs,
        generators: all.generators,
    }
}

/// Recovers the strings a program generates, by running its generators.
///
/// [`generated_strings`] as a tuple: the recovered strings, how the runs
/// ended by stop reason, the start points run, and the functions holding a
/// keystream's constants.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the functions holding a keystream's constants.
/// * `filter` - Case-insensitive substring; empty keeps everything.
///
/// # Returns
///
/// The recovered strings, and how each run ended, by stop reason.
#[must_use]
pub fn hidden_strings(
    p: &Program,
    a: &Analysis,
    filter: &str,
) -> (Vec<Generated>, BTreeMap<String, usize>, usize, usize) {
    let Recovery {
        found,
        stops,
        runs,
        generators,
    } = recovered_matching(p, a, filter);
    (found, stops, runs, generators)
}

/// Reports the strings a program generates instead of storing.
///
/// The rendering of [`generated_strings`]: a row per recovered string saying
/// which function built it and where the run wrote it, then a count of how
/// the runs ended, because a stop reason names the instruction or the state
/// that bounded the recovery.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the functions holding a keystream's constants.
/// * `o` - User names.
/// * `filter` - Case-insensitive substring; empty keeps everything.
///
/// # Returns
///
/// The table, and one line per distinct stop reason.
pub fn hidden_strings_tsv(p: &Program, a: &Analysis, o: &Overlay, filter: &str) -> String {
    /// Rows reported.
    const ROWS_MAX: usize = 300;
    let Recovery {
        found,
        stops,
        runs,
        generators,
    } = recovered_matching(p, a, filter);
    let total = found.len();
    let mut out = format!(
        "# {total} generated string{} from {runs} start point{} in {generators} function{} that mix a keystream\n",
        plural(total),
        plural(runs),
        plural(generators)
    );
    if total > 0 {
        out.push_str("# written_at     built_by                     text\n");
        for g in found.iter().take(ROWS_MAX) {
            let _ = writeln!(
                out,
                "{:<#15x} {:<28} {:?}",
                g.written_at,
                short_name(a, o, g.built_by),
                g.text
            );
        }
        more_line(&mut out, total, ROWS_MAX, "not shown");
    }
    for (stop, n) in &stops {
        let _ = writeln!(out, "# {n} run{} ended {stop}", plural(*n));
    }
    out
}
