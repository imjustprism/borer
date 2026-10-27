//! Pointer chains from a fixed place to an address in a process.
//!
//! A value a game keeps on its heap moves every run, but some global of a
//! module, or a thread's singleton slot, reaches it through a fixed walk:
//! read the pointer at the base, add an offset, read again, and so on
//! until the address. This finds such walks backwards from the address,
//! one level per sweep of the process's writable memory and its modules'
//! read-only data (a table protected once filled), not its code nor the
//! read-only files it maps (a game's asset archives): the words that
//! point at most `max_offset` bytes below an address of the level are the
//! next level's addresses, and one inside a base ends a chain. A level
//! keeps at most [`FRONTIER_MAX`] addresses, smallest offset first, and
//! says how many it set aside, so the answer may miss chains but never
//! claims one it did not read; every chain is walked again before it is
//! shown ([`follow`]).

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::ops::ControlFlow;

use super::scan::{Stop, Swept, sweep};
use super::{Memory, Rebase};
use crate::analysis::{Analysis, Overlay};
use crate::memory::le_word;
use crate::num::from_usize;
use crate::program::Program;
use crate::search::demangled_name;

/// Most addresses one level of the search goes on from.
pub const FRONTIER_MAX: usize = 4096;

/// Most chains a search collects.
pub const CHAINS_MAX: usize = 4096;

/// Most pointers one level collects before it stops looking.
pub const CANDIDATES_MAX: usize = 1 << 20;

/// A fixed place a chain may start at: a module, or a singleton's slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Base {
    /// What a chain names it by (`game.exe`, `Player::instance`).
    pub name: String,
    /// First address.
    pub start: u64,
    /// Length in bytes.
    pub len: u64,
}

/// One chain: read the word at `at`, add the first offset, read again, and
/// so on; after the last offset the address is the target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Chain {
    /// Index of the base the chain starts in.
    pub base: usize,
    /// The address of the first pointer, inside the base.
    pub at: u64,
    /// The offsets added after each read, first read first; empty when the
    /// target is itself inside a base.
    pub offsets: Vec<u64>,
}

/// What a search for chains found.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Paths {
    /// The chains, shortest first, then by smaller offsets.
    pub chains: Vec<Chain>,
    /// What the sweeps read, over every level.
    pub swept: Swept,
    /// Levels searched.
    pub levels: usize,
    /// Per level, the addresses it found and set aside past
    /// [`FRONTIER_MAX`]: `(level, found, set aside)`.
    pub set_aside: Vec<(usize, usize, usize)>,
    /// Chains [`verify`] dropped because walking them again no longer
    /// reached the target.
    pub dropped: usize,
}

/// One address the search reached.
#[derive(Debug, Clone, Copy)]
struct Node {
    /// The address: the target, or where a pointer on the way to it is.
    at: u64,
    /// The node this one's pointer leads to, `None` for the target.
    next: Option<usize>,
    /// What is added to this node's pointer to reach `next`'s address.
    offset: u64,
}

/// Finds pointer chains from the bases to a target.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `target` - The address chains end at.
/// * `bases` - Where a chain may start.
/// * `depth` - Most pointers a chain reads.
/// * `max_offset` - Largest offset added after a read.
/// * `word` - The pointer width in bytes, 4 or 8.
#[must_use]
pub fn paths(
    mem: &dyn Memory,
    target: u64,
    bases: &[Base],
    depth: usize,
    max_offset: u64,
    word: usize,
) -> Paths {
    let mut out = Paths::default();
    let mut starts: Vec<(u64, usize)> = bases
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    starts.sort_unstable();
    let base_of = |at: u64| {
        let below = starts.partition_point(|(s, _)| *s <= at);
        starts[..below]
            .iter()
            .rev()
            .map(|(_, i)| *i)
            .find(|&i| at - bases[i].start < bases[i].len)
    };
    if let Some(b) = base_of(target) {
        out.chains.push(Chain {
            base: b,
            at: target,
            offsets: Vec::new(),
        });
    }
    let ranges: Vec<(u64, u64)> = mem
        .regions()
        .iter()
        .filter(|r| r.writable || (r.image && !r.executable))
        .map(|r| (r.base, r.base.saturating_add(r.size)))
        .collect();
    let mask = if word == 8 { u64::MAX } else { 0xffff_ffff };
    let mut nodes = vec![Node {
        at: target,
        next: None,
        offset: 0,
    }];
    let mut frontier = vec![0usize];
    let mut seen: BTreeSet<u64> = BTreeSet::from([target]);
    for level in 1..=depth {
        if frontier.is_empty() || out.swept.stop.is_some() {
            break;
        }
        out.levels = level;
        let mut sorted: Vec<(u64, usize)> = frontier.iter().map(|&n| (nodes[n].at, n)).collect();
        sorted.sort_unstable();
        let (lo, hi) = (
            sorted[0].0.saturating_sub(max_offset),
            sorted[sorted.len() - 1].0,
        );
        let mut found: Vec<(u64, u64, usize)> = Vec::new();
        let mut swept = sweep(mem, &ranges, 0, |at, bytes, own| {
            for (i, w) in bytes[..own].chunks_exact(word).enumerate() {
                let v = le_word(w) & mask;
                if v < lo || v > hi {
                    continue;
                }
                let loc = at.saturating_add(from_usize(i * word));
                let first = sorted.partition_point(|(a, _)| *a < v);
                for &(a, n) in sorted[first..]
                    .iter()
                    .take_while(|(a, _)| a - v <= max_offset)
                {
                    found.push((a - v, loc, n));
                    if found.len() >= CANDIDATES_MAX {
                        return ControlFlow::Break(());
                    }
                }
            }
            ControlFlow::Continue(())
        });
        if swept.stop == Some(Stop::Full) {
            swept.stop = Some(Stop::Crowded);
        }
        out.swept.add(swept);
        found.sort_unstable();
        let mut next = Vec::new();
        let mut aside = 0usize;
        for (offset, loc, n) in found {
            if let Some(b) = base_of(loc) {
                if out.chains.len() < CHAINS_MAX {
                    out.chains.push(chain_from(&nodes, b, loc, offset, n));
                }
                continue;
            }
            if level == depth || !seen.insert(loc) {
                continue;
            }
            if next.len() >= FRONTIER_MAX {
                aside += 1;
                continue;
            }
            nodes.push(Node {
                at: loc,
                next: Some(n),
                offset,
            });
            next.push(nodes.len() - 1);
        }
        if aside > 0 {
            out.set_aside.push((level, next.len() + aside, aside));
        }
        if out.chains.len() >= CHAINS_MAX {
            out.swept.stop = out.swept.stop.or(Some(Stop::Full));
        }
        frontier = next;
    }
    out.chains.sort_by(|a, b| {
        let key = |c: &Chain| (c.offsets.len(), c.offsets.iter().sum::<u64>(), c.base, c.at);
        key(a).cmp(&key(b)).then_with(|| a.offsets.cmp(&b.offsets))
    });
    out
}

/// Builds the chain that starts at a pointer in a base and goes on through
/// the nodes to the target.
///
/// # Arguments
///
/// * `nodes` - The nodes reached.
/// * `base` - Index of the base.
/// * `at` - The pointer's address.
/// * `offset` - What is added to it to reach node `n`.
/// * `n` - The node it leads to.
fn chain_from(nodes: &[Node], base: usize, at: u64, offset: u64, n: usize) -> Chain {
    let mut offsets = vec![offset];
    let mut here = n;
    while let Some(next) = nodes[here].next {
        offsets.push(nodes[here].offset);
        here = next;
    }
    Chain { base, at, offsets }
}

/// Walks a chain in the process as it is now.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `chain` - The chain.
/// * `word` - The pointer width in bytes.
///
/// # Returns
///
/// The address the chain reaches, or `None` when a pointer on the way does
/// not read.
#[must_use]
pub fn follow(mem: &dyn Memory, chain: &Chain, word: usize) -> Option<u64> {
    let mut at = chain.at;
    for off in &chain.offsets {
        let bytes = mem.read(at, word).filter(|b| b.len() == word)?;
        at = le_word(&bytes).checked_add(*off)?;
    }
    Some(at)
}

/// Walks every chain again and drops those that no longer reach the
/// target, counting them in [`Paths::dropped`].
///
/// # Arguments
///
/// * `mem` - The process.
/// * `paths` - The search.
/// * `target` - The address the chains must reach.
/// * `word` - The pointer width in bytes.
pub fn verify(mem: &dyn Memory, paths: &mut Paths, target: u64, word: usize) {
    let before = paths.chains.len();
    paths
        .chains
        .retain(|c| follow(mem, c, word) == Some(target));
    paths.dropped += before - paths.chains.len();
}

/// Spells a chain the way Cheat Engine's pointer notation does:
/// `[[game.exe+0x1f0]+0x10]+0x28`.
///
/// # Arguments
///
/// * `chain` - The chain.
/// * `bases` - The bases its index names.
#[must_use]
pub fn spell(chain: &Chain, bases: &[Base]) -> String {
    let (name, start) = bases
        .get(chain.base)
        .map_or(("?", 0), |b| (b.name.as_str(), b.start));
    let mut out = if chain.at == start {
        name.to_owned()
    } else {
        format!("{name}+{:#x}", chain.at.saturating_sub(start))
    };
    for off in &chain.offsets {
        out = format!("[{out}]+{off:#x}");
    }
    out
}

/// Labels a chain's first pointer when it is in the analysed image.
///
/// The label is its static address, and the singleton class whose
/// constructor stores its instance there, the user's name, or the symbol
/// the file has there.
///
/// # Arguments
///
/// * `rebase` - Where the image sits.
/// * `program` - The analysed image.
/// * `analysis` - Its analysis.
/// * `overlay` - User names.
/// * `live` - The pointer's process address.
///
/// # Returns
///
/// `static 0x.. Name`, `static 0x..` when the file names nothing there, or
/// `None` outside the image.
#[must_use]
pub fn base_label(
    rebase: &Rebase,
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    live: u64,
) -> Option<String> {
    let va = rebase.to_static(live)?;
    let name = analysis
        .classes
        .global_hints
        .get(&va)
        .map(|class| format!("{class} singleton"))
        .or_else(|| overlay.names.get(&va).cloned())
        .or_else(|| {
            analysis
                .symbol_at(program, va)
                .map(|s| demangled_name(&s.name))
        });
    Some(name.map_or_else(
        || format!("static {va:#x}"),
        |n| format!("static {va:#x} {n}"),
    ))
}

/// Renders a page of verified chains.
///
/// # Arguments
///
/// * `paths` - The search, its chains walked again ([`verify`]).
/// * `bases` - The bases.
/// * `label` - What the analysis calls a chain's first pointer's address,
///   when it knows.
/// * `notes` - Lines put after the header (what was read).
/// * `offset` - Chains to skip first.
/// * `limit` - Most rows.
/// * `count_only` - The header alone.
#[must_use]
pub fn paths_page(
    paths: &Paths,
    bases: &[Base],
    label: &dyn Fn(u64) -> Option<String>,
    notes: &str,
    offset: usize,
    limit: usize,
    count_only: bool,
) -> String {
    let total = match paths.swept.stop {
        Some(_) => format!("at least {}", paths.chains.len()),
        None => paths.chains.len().to_string(),
    };
    let mut out = if count_only {
        format!("# {total} chains\n")
    } else {
        let shown = paths.chains.len().saturating_sub(offset).min(limit);
        format!("# showing {shown} of {total} chains, shortest first, each walked again\n")
    };
    out.push_str(notes);
    if paths.dropped > 0 {
        let _ = writeln!(
            out,
            "# {} more no longer reached the target when walked again (memory changed between the reads)",
            paths.dropped
        );
    }
    for (level, found, aside) in &paths.set_aside {
        let _ = writeln!(
            out,
            "# rough: level {level} found {found} addresses and went on from {}; chains through the rest are not looked for",
            found - aside
        );
    }
    if count_only {
        return out;
    }
    out.push_str("# depth chain base-label\n");
    for c in paths.chains.iter().skip(offset).take(limit) {
        let note = label(c.at).map_or_else(String::new, |l| format!(" {l}"));
        let _ = writeln!(out, "{} {}{note}", c.offsets.len(), spell(c, bases));
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::*;
    use crate::live::scan::tests::process;

    /// The one base the tests' process has: its image `game.exe`.
    fn game() -> Vec<Base> {
        vec![Base {
            name: "game.exe".to_owned(),
            start: 0x40_0000,
            len: 0x1000,
        }]
    }

    /// A chain from a module's global through a heap object to a field is
    /// found, spelled and walked again.
    ///
    /// Only within the depth asked; a pointer cycle on the way does not
    /// loop, and a target inside the base is its own chain.
    #[test]
    fn a_chain_from_a_global_reaches_the_target() {
        let mem = process(0x3000);
        mem.put(0x40_0100, &0x11000u64.to_le_bytes());
        mem.put(0x11020, &0x12000u64.to_le_bytes());
        mem.put(0x12000, &0x11000u64.to_le_bytes());
        let bases = game();
        let target = 0x12018;
        let found = paths(&mem, target, &bases, 3, 0x100, 8);
        let spelled: Vec<String> = found.chains.iter().map(|c| spell(c, &bases)).collect();
        assert_eq!(spelled[0], "[[game.exe+0x100]+0x20]+0x18", "{spelled:?}");
        let mut found = found;
        let all = found.chains.len();
        mem.put(0x11020, &0x13000u64.to_le_bytes());
        verify(&mem, &mut found, target, 8);
        assert_eq!(found.dropped, all, "every chain went through 0x11020");
        mem.put(0x11020, &0x12000u64.to_le_bytes());
        let mut found = paths(&mem, target, &bases, 3, 0x100, 8);
        verify(&mem, &mut found, target, 8);
        assert_eq!(found.dropped, 0);
        assert!(paths(&mem, target, &bases, 1, 0x100, 8).chains.is_empty());
        let label = |at: u64| (at == 0x40_0100).then(|| "g_world".to_owned());
        let page = paths_page(&found, &bases, &label, "", 0, 1, false);
        assert!(
            page.ends_with("# depth chain base-label\n2 [[game.exe+0x100]+0x20]+0x18 g_world\n"),
            "{page}"
        );
        let at_base = paths(&mem, 0x40_0010, &bases, 2, 0x100, 8);
        assert_eq!(spell(&at_base.chains[0], &bases), "game.exe+0x10");
    }

    /// A base in the image is labelled with its static address and what
    /// the analysis knows there: a global singleton, a user name, a symbol.
    #[test]
    fn a_base_in_the_image_is_labelled_by_the_analysis() {
        use crate::program::{Arch, Section, Symbol, SymbolKind};
        let data = Section::mapped(".data", 0x2000, 0, 0x100, true, false);
        let mut program = Program::raw(vec![0; 0x100], Arch::X86_64, 0, None, vec![data]);
        program.symbols.push(Symbol {
            name: "g_state".to_owned(),
            addr: 0x2040,
            kind: SymbolKind::Data,
        });
        let mut analysis = Analysis::compute(&program);
        analysis
            .classes
            .global_hints
            .insert(0x2080, "World".to_owned());
        let mut overlay = Overlay::default();
        overlay.names.insert(0x2010, "g_hero".to_owned());
        let r = Rebase {
            static_base: 0,
            static_end: 0x2100,
            live_base: 0x7000_0000,
        };
        let label = |live| base_label(&r, &program, &analysis, &overlay, live);
        assert_eq!(
            label(0x7000_2080).as_deref(),
            Some("static 0x2080 World singleton")
        );
        assert_eq!(label(0x7000_2010).as_deref(), Some("static 0x2010 g_hero"));
        assert_eq!(label(0x7000_2040).as_deref(), Some("static 0x2040 g_state"));
        assert_eq!(label(0x7000_2050).as_deref(), Some("static 0x2050"));
        assert_eq!(label(0x10), None);
    }

    /// A pointer in a module's read-only data starts a chain too, as a
    /// table the module protected once filled does.
    #[test]
    fn a_read_only_module_pointer_starts_a_chain() {
        let mut mem = process(0x2000);
        if let Some(image) = mem.regions.get_mut(1) {
            image.2 = false;
        }
        mem.put(0x40_0300, &0x11000u64.to_le_bytes());
        let found = paths(&mem, 0x11010, &game(), 1, 0x100, 8);
        assert_eq!(spell(&found.chains[0], &game()), "[game.exe+0x300]+0x10");
    }

    /// A 32-bit process's pointers are four bytes wide.
    #[test]
    fn four_byte_pointers_chain_too() {
        let mem = process(0x2000);
        mem.put(0x40_0200, &0x11000u32.to_le_bytes());
        let bases = game();
        let found = paths(&mem, 0x11040, &bases, 2, 0x100, 4);
        assert_eq!(spell(&found.chains[0], &bases), "[game.exe+0x200]+0x40");
    }
}
