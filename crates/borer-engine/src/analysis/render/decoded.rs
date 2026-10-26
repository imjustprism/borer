//! Strings recovered by running a decoder at each of its call sites.
//!
//! Most samples hide their configuration behind one decoder function called
//! from many sites, each passing a pointer to a different ciphertext and
//! often its length. A keystream-constant generator ([`generated_strings`])
//! does not cover it, because the ciphertext and the length live at the call
//! site, not in the decoder. This finds the decoder candidates the way
//! [`borer://calls`](calls) does (a callee with many sites passing data
//! pointers), runs the decoder in the sandboxed emulator with each site's own
//! arguments, and reads the plaintext out of what the run wrote, dropping a
//! run whose output only repeats a string already stored in the image (a
//! `memcpy`, not a decoder).

use super::calls::{gather, listed_args, reach_of};
use super::literals::written_text;
use super::*;
use crate::analysis::decompile::CallArg;
use crate::cancel::Cancel;

/// Most rows one read lists; the rest page with `offset=`.
pub const DECODED_PAGE: usize = 200;

/// Shortest string a decoder call site has to be reached from to be a
/// candidate: a decoder is a function reused across the strings it hides.
const MIN_SITES: usize = 3;

/// Decoder candidates examined, the most-called first; the rest are left.
const CANDIDATES_MAX: usize = 24;

/// Call sites emulated for one decoder; the rest are counted.
const SITES_MAX: usize = 32;

/// Call sites emulated across every candidate, so one binary cannot spend
/// the triage that reads this on thousands of decoder runs.
const SITE_RUNS_MAX: usize = 160;

/// Callers decompiled to find one decoder's sites.
const CALLERS_MAX: usize = 200;

/// Steps each call-site run is given, so a decoder fed a runaway length
/// stops at the budget rather than looping without end.
const BUDGET: usize = 120_000;

/// Shortest recovered text kept.
const MIN_LEN: usize = 5;

/// Longest recovered text kept: a decoder fed a runaway length writes a
/// buffer far longer than any string, which is dropped rather than listed.
const TEXT_MAX: usize = 512;

/// One string a decoder produced at one call site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct DecodedRow {
    /// The decoder function's entry.
    pub(super) decoder: u64,
    /// The function the call was made from.
    pub(super) caller: u64,
    /// The call instruction.
    pub(super) at: u64,
    /// The recovered text.
    pub(super) text: String,
}

/// What running a program's decoders at their call sites recovered.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) struct Decoded {
    /// The recovered strings, in listing order.
    pub(super) rows: Vec<DecodedRow>,
    /// Decoder candidates examined.
    pub(super) candidates: usize,
    /// Call sites run across all candidates.
    pub(super) sites: usize,
}

/// Collects the decoded strings of a program, once per set of names.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, holding the memo.
/// * `o` - Names in force, which the decompiled callers are read under.
///
/// # Returns
///
/// The recovered decoded strings, built once and memoized.
fn collected(p: &Program, a: &Analysis, o: &Overlay) -> Arc<Decoded> {
    a.derived
        .get_or_build_named("decoded", o.fingerprint(), (), || collect(p, a, o))
}

/// Tells whether an address points into a section the program does not
/// execute: the ciphertext a decoder reads lives in such a section.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `va` - The address.
///
/// # Returns
///
/// `true` when a mapped, non-executable section holds the address.
fn in_data(p: &Program, va: u64) -> bool {
    p.section_at(va).is_some_and(|s| !s.executable)
}

/// Tells whether the image already stores `text` verbatim.
///
/// A function that copies a plaintext string (a `memcpy`) leaves the same
/// bytes it read, which are already in the file; a decoder leaves bytes the
/// file does not hold. Dropping a recovery the image already contains keeps
/// the copiers out.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `text` - The recovered text.
///
/// # Returns
///
/// `true` when the image's bytes contain the text verbatim.
fn already_stored(p: &Program, text: &str) -> bool {
    let needle = text.as_bytes();
    needle.len() >= 2 && crate::search::holds(&p.bytes, needle)
}

/// The call sites of one decoder, emulated, with the plaintext each wrote.
///
/// Each site's recorded arguments ([`listed_args`]) are placed where the
/// convention puts them, and the decoder is run from its entry in the
/// sandboxed emulator, bounded by [`BUDGET`]; a read of memory nothing
/// backs faults and ends that run, so a wrong pointer stops rather than
/// invents. The printable runs the decoder wrote ([`written_text`]) are its
/// output, less any the image already stores and any longer than
/// [`TEXT_MAX`] (a runaway length). A raised cancel flag
/// ([`Cancel`]) runs no further site.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `decoder` - The candidate's entry.
/// * `sites` - Its call sites, with the arguments each passes.
/// * `rows` - Where the recovered strings go.
///
/// # Returns
///
/// How many sites were run.
fn run_sites(
    p: &Program,
    decoder: u64,
    sites: &[(u64, u64, Vec<CallArg>)],
    budget: usize,
    rows: &mut Vec<DecodedRow>,
) -> usize {
    let mut run = 0usize;
    let mut seen: BTreeSet<(u64, String)> = BTreeSet::new();
    let sites = sites.iter().take(SITES_MAX.min(budget));
    for (at, caller, args) in sites.take_while(|_| !Cancel::raised()) {
        let Some(mut emu) = Emulator::new(p, BUDGET) else {
            break;
        };
        emu.install_imports();
        for (i, arg) in args.iter().enumerate() {
            if let Some(v) = arg.value {
                emu.set_arg(i, v);
            }
        }
        let outcome = emu.run(decoder);
        run += 1;
        for (_, text) in written_text(&outcome.history, MIN_LEN) {
            if text.chars().count() > TEXT_MAX || already_stored(p, &text) {
                continue;
            }
            if seen.insert((*at, text.clone())) {
                rows.push(DecodedRow {
                    decoder,
                    caller: *caller,
                    at: *at,
                    text,
                });
            }
        }
    }
    run
}

/// Collects every decoder's recovered strings.
///
/// The candidates are the functions reached from at least [`MIN_SITES`]
/// call sites, the most-called first ([`CANDIDATES_MAX`] examined). Each is
/// read through [`gather`] for its sites and their arguments; a candidate
/// no site passes a data pointer to is not a decoder and is skipped. The
/// rest are run at each site ([`run_sites`]) and the recovered strings
/// sorted by text so the listing is deterministic. A raised cancel flag
/// ([`Cancel`]) examines no further candidate; the request's answer then
/// says it stopped, and the memo does not keep what was found.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
///
/// # Returns
///
/// Every decoder's recovered strings, the candidates examined and the call
/// sites run.
fn collect(p: &Program, a: &Analysis, o: &Overlay) -> Decoded {
    if p.refuses(Feature::Decompile).is_some() || x86_only(p, "decoded").is_err() {
        return Decoded::default();
    }
    let mut candidates: Vec<(usize, u64)> = a
        .functions
        .iter()
        .map(|f| f.entry)
        .filter_map(|entry| {
            let sites = a
                .xrefs_to(entry)
                .iter()
                .filter(|s| {
                    matches!(s.kind, RefKind::Call | RefKind::Jmp) && s.from_entry.is_some()
                })
                .count();
            (sites >= MIN_SITES).then_some((sites, entry))
        })
        .collect();
    candidates.sort_by(|l, r| r.0.cmp(&l.0).then(l.1.cmp(&r.1)));
    candidates.truncate(CANDIDATES_MAX);
    let mut rows: Vec<DecodedRow> = Vec::new();
    let mut examined = 0usize;
    let mut sites_run = 0usize;
    for (_, decoder) in candidates.into_iter().take_while(|_| !Cancel::raised()) {
        let Ok(reach) = reach_of(p, a, o, decoder) else {
            continue;
        };
        let gathered = gather(p, a, o, &reach, CALLERS_MAX);
        let sites: Vec<(u64, u64, Vec<CallArg>)> = gathered
            .found
            .iter()
            .filter_map(|f| {
                let args = listed_args(f.site.as_ref()?, None);
                Some((f.at, f.caller, args))
            })
            .collect();
        let passes_pointer = sites
            .iter()
            .flat_map(|(_, _, args)| args.iter())
            .any(|arg| arg.value.is_some_and(|v| in_data(p, v)));
        if sites.len() < MIN_SITES || !passes_pointer {
            continue;
        }
        let left = SITE_RUNS_MAX.saturating_sub(sites_run);
        if left == 0 {
            break;
        }
        examined += 1;
        sites_run += run_sites(p, decoder, &sites, left, &mut rows);
    }
    rows.sort_by(|l, r| (&l.text, l.decoder, l.at).cmp(&(&r.text, r.decoder, r.at)));
    rows.dedup();
    Decoded {
        rows,
        candidates: examined,
        sites: sites_run,
    }
}

/// The decoded strings a program holds, for the IOC collector to tag
/// `decoded`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
///
/// # Returns
///
/// Each recovered string with its decoder and call site.
pub(super) fn decoded_strings(p: &Program, a: &Analysis, o: &Overlay) -> Arc<Decoded> {
    collected(p, a, o)
}

/// What a `decoded` read asks for: the text a string must contain and the
/// page.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Filter {
    /// Lowercase text the string must contain; empty keeps every string.
    text: String,
    /// Rows to skip first.
    offset: usize,
    /// Most rows shown, when `limit=` asked for fewer than a page.
    limit: Option<usize>,
}

impl Filter {
    /// Reads a filter: `offset=<n>`, `limit=<n>`, and any other text the
    /// string must contain, comma-separated.
    ///
    /// # Arguments
    ///
    /// * `spec` - The filter as the URI carries it.
    ///
    /// # Returns
    ///
    /// The filter.
    ///
    /// # Errors
    ///
    /// When the offset or the limit is not a row count.
    fn parse(spec: &str) -> Result<Filter, String> {
        let mut filter = Filter::default();
        let mut text: Vec<&str> = Vec::new();
        for token in spec.split(',').map(str::trim).filter(|t| !t.is_empty()) {
            if let Some(n) = token.strip_prefix("offset=") {
                filter.offset = crate::table::row_offset(n)?;
            } else if let Some(n) = token.strip_prefix("limit=") {
                filter.limit = Some(crate::table::row_limit(n)?);
            } else {
                text.push(token);
            }
        }
        filter.text = text.join(",").to_lowercase();
        Ok(filter)
    }
}

/// Lists the strings a program's decoders produce, each with the decoder
/// and the call site it was recovered from.
///
/// Candidate decoders are the functions reached from many call sites that
/// pass a data pointer (per [`borer://calls`](calls)); each is run in the
/// sandboxed emulator with the arguments of each of its sites, and the
/// plaintext read from what the run writes. A run whose output only repeats
/// a string the image already stores is dropped, so a `memcpy` yields no
/// rows. Rows are sorted by text, [`DECODED_PAGE`] a page.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - Case-insensitive text the string contains, `offset=<n>` and
///   `limit=<n>` (fewer rows than a page), comma-separated; empty for all.
///
/// # Returns
///
/// The header with the counts, then a row per recovered string of the page.
///
/// # Errors
///
/// When the offset or the limit is not a row count.
pub fn decoded_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    if let Err(why) = x86_only(p, "decoded") {
        return Ok(format!("# {why}\n"));
    }
    let filter = Filter::parse(spec)?;
    let all = collected(p, a, o);
    let rows: Vec<&DecodedRow> = all
        .rows
        .iter()
        .filter(|r| filter.text.is_empty() || r.text.to_lowercase().contains(&filter.text))
        .collect();
    let total = rows.len();
    let mut out = format!(
        "# {total} decoded string{} from {} decoder{} run at {} call site{}\n",
        plural(total),
        all.candidates,
        plural(all.candidates),
        all.sites,
        plural(all.sites)
    );
    let start = filter.offset.min(total);
    let size = filter.limit.map_or(DECODED_PAGE, |n| n.min(DECODED_PAGE));
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
        "# text                                     decoder                       call site\n",
    );
    for r in page {
        let _ = writeln!(
            out,
            "{:<40} {:<29} {:#x} in {}",
            format!("{:?}", r.text),
            short_name(a, o, r.decoder),
            r.at,
            short_name(a, o, r.caller)
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
            "# {} more; borer://decoded/{} for the next page",
            total - next,
            again.join(",")
        );
    }
    Ok(out)
}
