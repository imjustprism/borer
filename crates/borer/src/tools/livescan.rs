//! The live search tools: finding the addresses in the attached process
//! that hold a value, and the pointer chains that reach an address.

use std::fmt::Write as _;

use borer_engine::live::Memory as _;
use borer_engine::live::path::{self, Base};
use borer_engine::live::scan::{self, Compare, Found, Needle, Scope};
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::params::{
    Annotation, LivePathParams, LiveScanParams, Page, ScanCompare, ScanScope, count_param,
    must_fit_a_row,
};
use crate::safety::{Effect, effects};
use crate::tools::live::LiveSession;

/// Most result sets a session holds.
pub(crate) const SETS_MAX: usize = 8;

/// The largest `max_offset` a pointer search takes, in bytes.
const MAX_OFFSET_CAP: u32 = 0x1_0000;

/// A value scan's result set, as the session keeps it under its name.
#[derive(Debug, Clone)]
pub(crate) struct ScanSet {
    /// The hits and their values as last read.
    pub(crate) found: Found,
    /// How the set came to be: the first scan's needle and scope, then each
    /// next scan's comparison and what it kept.
    pub(crate) history: String,
}

/// Reads a needle of a kind from the text an agent gave.
///
/// # Arguments
///
/// * `kind` - The engine kind, `None` for bytes.
/// * `value` - The text.
/// * `tolerance` - A float's tolerance, if given.
///
/// # Errors
///
/// When the text does not read as the kind, or a tolerance comes with
/// bytes.
fn needle_of(
    kind: Option<borer_engine::memory::Kind>,
    value: &str,
    tolerance: Option<f64>,
) -> Result<Needle, String> {
    match kind {
        Some(k) => Needle::parse(k, value, tolerance),
        None if tolerance.is_some() => Err("tolerance applies to f32 and f64 only".to_owned()),
        None => Needle::aob(value),
    }
}

/// The scope a first scan reads, and how its header names it.
///
/// # Arguments
///
/// * `session` - The attached process, whose name is its main module's.
/// * `scope` - The scope asked for; absent is `module` when a module is
///   named, else `all`.
/// * `module` - The module name, for `scope=module`.
///
/// # Errors
///
/// When `scope=module` comes without a module, or a module with another
/// scope.
fn scope_of(
    session: &LiveSession,
    scope: Option<ScanScope>,
    module: Option<String>,
) -> Result<(Scope, String), String> {
    let default = if module.is_some() {
        ScanScope::Module
    } else {
        ScanScope::All
    };
    match (scope.unwrap_or(default), module) {
        (ScanScope::Module, Some(m)) => Ok((Scope::Module(m.clone()), m)),
        (ScanScope::Module, None) => Err("scope=module needs module=<name>".to_owned()),
        (ScanScope::All | ScanScope::Main | ScanScope::Heap, Some(m)) => {
            Err(format!("module={m} goes with scope=module"))
        }
        (ScanScope::All, None) => Ok((Scope::All, "every readable region".to_owned())),
        (ScanScope::Heap, None) => Ok((Scope::Heap, "the heaps".to_owned())),
        (ScanScope::Main, None) => {
            let name = session.process.name().to_owned();
            Ok((Scope::Module(name.clone()), name))
        }
    }
}

/// The comparison a next scan makes.
///
/// # Arguments
///
/// * `compare` - The comparison asked for.
/// * `set` - The set it narrows, whose kind reads `value`.
/// * `value` - The value, for `equal` only.
/// * `tolerance` - A float's tolerance, for `equal`.
///
/// # Errors
///
/// When `equal` comes without a value, a value with another comparison,
/// or the value does not read as the set's kind.
fn compare_of(
    compare: ScanCompare,
    set: &Found,
    value: Option<&str>,
    tolerance: Option<f64>,
) -> Result<Compare, String> {
    if compare != ScanCompare::Equal && (value.is_some() || tolerance.is_some()) {
        return Err(
            "value and tolerance go with compare=equal, or with a first scan (no compare)"
                .to_owned(),
        );
    }
    Ok(match compare {
        ScanCompare::Changed => Compare::Changed,
        ScanCompare::Unchanged => Compare::Unchanged,
        ScanCompare::Increased => Compare::Increased,
        ScanCompare::Decreased => Compare::Decreased,
        ScanCompare::Equal => {
            let v = value.ok_or("compare=equal needs value=...")?;
            Compare::Equal(needle_of(set.needle.kind(), v, tolerance)?)
        }
    })
}

/// The word a comparison goes by in a set's history.
///
/// # Arguments
///
/// * `compare` - The comparison.
fn compare_word(compare: ScanCompare) -> &'static str {
    match compare {
        ScanCompare::Changed => "changed",
        ScanCompare::Unchanged => "unchanged",
        ScanCompare::Increased => "increased",
        ScanCompare::Decreased => "decreased",
        ScanCompare::Equal => "equal",
    }
}

/// The hint every scan answer ends with.
///
/// # Arguments
///
/// * `name` - The set's name.
/// * `hits` - How many hits it holds.
fn next_hint(name: &str, hits: usize) -> String {
    match hits {
        0 => format!("next: no hit is left; live_scan(name=\"{name}\", value=...) starts over\n"),
        1..=8 => "next: live_read(address) or live_watch(name, address) on a hit; live_path(address) for a pointer chain that finds it after a restart\n".to_owned(),
        _ => format!(
            "next: change the value in the program, then live_scan(name=\"{name}\", compare=changed|unchanged|increased|decreased|equal)\n"
        ),
    }
}

/// Renders a page of a result set, its hint after it.
///
/// # Arguments
///
/// * `set` - The set.
/// * `name` - Its name.
/// * `notes` - Lines after the header: what was read or kept.
/// * `modules` - The process's modules, to place each hit.
/// * `page` - Which rows.
fn set_page(
    set: &ScanSet,
    name: &str,
    notes: &str,
    modules: &[borer_engine::live::Module],
    page: Page,
) -> String {
    let title = format!("in \"{name}\": {}", set.history);
    let mut out = scan::found_page(
        &set.found,
        &title,
        notes,
        modules,
        page.offset,
        page.limit.n,
        page.count_only,
    );
    out.push_str(&next_hint(name, set.found.hits.len()));
    out
}

#[tool_router(router = live_scan_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Scans the attached process for a value, or narrows a result set.
    ///
    /// # Arguments
    ///
    /// * `LiveScanParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no process is attached, a value or comparison
    /// does not read, the set named does not exist, or the session holds
    /// [`SETS_MAX`] sets and the name is new.
    #[tool(
        description = "Find addresses in the attached process holding a value (CE-style first and next scan; read-only). First scan: value with kind u8..u64, i8..i64, f32/f64 (tolerance default: half the last digit), string, wstring or bytes (hex, ?? wildcard); scope all (default), main, module (+module) or heap. The hits are kept as result set `name` (8 sets, 2M hits each). Next scan: same name with compare=changed|unchanged|increased|decreased|equal(+value) re-reads only the set's hits; name alone pages the set without reading. Rows: address, value, module+offset, by address; the header says MiB read and regions skipped. Paged (default 50, max 500).",
        meta = effects(&[Effect::ReadsProcessMemory]),
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    pub(crate) fn live_scan(
        &self,
        Parameters(LiveScanParams {
            name,
            value,
            kind,
            tolerance,
            compare,
            scope,
            module,
            offset,
            limit,
            count_only,
        }): Parameters<LiveScanParams>,
    ) -> Result<String, ErrorData> {
        must_fit_a_row(&name, Annotation::Name)?;
        let page = Page::new(offset, limit, count_only, 50, 500)?;
        self.with_live(|s| {
            if compare.is_none() && value.is_none() {
                let set = s.scans.get(&name).ok_or_else(|| {
                    format!("no result set is named {name}; a first scan passes value=...")
                })?;
                let notes = "# the set as last read; nothing was read now\n";
                return Ok(set_page(set, &name, notes, &s.process.modules(), page));
            }
            let left_out = s.process.unreadable_regions();
            let (set, notes) = match compare {
                None => {
                    let value = value.ok_or("a first scan needs value=...")?;
                    if !s.scans.contains_key(&name) && s.scans.len() >= SETS_MAX {
                        let names: Vec<&str> = s.scans.keys().map(String::as_str).collect();
                        return Err(format!(
                            "the session holds {SETS_MAX} result sets ({}); reuse one of the names to replace it",
                            names.join(", ")
                        ));
                    }
                    let needle = needle_of(kind.unwrap_or_default().kind(), &value, tolerance)?;
                    let (scope, place) = scope_of(s, scope, module)?;
                    let ranges = scan::ranges(&s.process, &scope)?;
                    let found = scan::scan(&s.process, needle, &ranges);
                    let history = format!("{} in {place}", found.needle.describe());
                    let mut notes = found.swept.line(left_out);
                    let full = format!("{} hits", found.hits.len());
                    notes.push_str(&scan::stop_line(found.swept.stop, &full));
                    (ScanSet { found, history }, notes)
                }
                Some(c) => {
                    let set = s.scans.get(&name).ok_or_else(|| {
                        format!("no result set is named {name}; a first scan (value=..., no compare) makes one")
                    })?;
                    if scope.is_some() || module.is_some() {
                        return Err("a next scan reads only the set's hits; scope and module go with a first scan".to_owned());
                    }
                    if let Some(k) = kind
                        && k.kind() != set.found.needle.kind()
                    {
                        return Err(format!(
                            "set {name} holds {}; a next scan keeps the set's kind, so leave kind out",
                            set.found.needle.describe()
                        ));
                    }
                    let how = compare_of(c, &set.found, value.as_deref(), tolerance)?;
                    let was = set.found.hits.len();
                    let narrowed = scan::narrow(&s.process, &set.found, &how)?;
                    let kept = narrowed.found.hits.len();
                    let mut notes = format!("# {} kept {kept} of {was}", compare_word(c));
                    if narrowed.unreadable > 0 {
                        let _ = write!(notes, "; {} no longer readable", narrowed.unreadable);
                    }
                    notes.push('\n');
                    let history = format!("{}, then {} ({kept})", set.history, compare_word(c));
                    (
                        ScanSet {
                            found: narrowed.found,
                            history,
                        },
                        notes,
                    )
                }
            };
            let out = set_page(&set, &name, &notes, &s.process.modules(), page);
            s.scans.insert(name.clone(), set);
            Ok(out)
        })
        .map(|text| page.limit.noted(text))
    }

    /// Finds pointer chains from fixed places to an address of the process.
    ///
    /// # Arguments
    ///
    /// * `LivePathParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no process is attached, the address does not
    /// resolve, the module is unknown, or a count is zero.
    #[tool(
        description = "Find pointer chains to an address in the attached process, the CE pointer scan (read-only): [[base+off]+o1]+o2 = address, where base is a module (any, or `module`) or a thread-local singleton slot of the mapped binary. depth reads per chain (default 4, max 6), each offset 0..max_offset (default 4096, max 65536). Shortest first; every chain is walked again before it is shown; a base in the binary is labelled with its static address and singleton or name. Rough past 4096 addresses per level, and says so. Paged (default 20, max 200).",
        meta = effects(&[Effect::ReadsProcessMemory]),
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    pub(crate) fn live_path(
        &self,
        Parameters(LivePathParams {
            address,
            depth,
            max_offset,
            module,
            offset,
            limit,
            count_only,
        }): Parameters<LivePathParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, count_only, 20, 200)?;
        let depth = count_param(depth, 4, 6, "depth")?;
        let asked = max_offset.unwrap_or(0x1000);
        let max_off = u64::from(asked.min(MAX_OFFSET_CAP));
        let program = self.loaded();
        let overlay = self.overlay();
        self.with_live(|s| {
            let target = self.live_addr(s, &address)?;
            let modules = s.process.modules();
            let to_base = |m: &borer_engine::live::Module| Base {
                name: m.name.clone(),
                start: m.base,
                len: m.size,
            };
            let mut bases: Vec<Base> = match &module {
                Some(m) => vec![to_base(scan::module_named(&modules, m)?)],
                None => modules.iter().map(to_base).collect(),
            };
            let analysis = match (&program, s.rebase.is_ok()) {
                (Some(_), true) => self.ensure_analysis().ok(),
                _ => None,
            };
            if let (None, Some(block), Some(a)) = (&module, s.tls_block, &analysis) {
                for (off, class) in &a.classes.tls_slots {
                    bases.push(Base {
                        name: format!("{class}::instance"),
                        start: block.saturating_add(*off),
                        len: borer_engine::num::from_usize(s.word),
                    });
                }
            }
            let mut found = path::paths(&s.process, target, &bases, depth.n, max_off, s.word);
            path::verify(&s.process, &mut found, target, s.word);
            let label = |at: u64| match (&program, &analysis, &s.rebase) {
                (Some(p), Some(a), Ok(r)) => path::base_label(r, p, a, &overlay, at),
                _ => None,
            };
            let mut notes = format!(
                "# target {target:#x}; {} levels searched, offsets 0..={max_off:#x}, {} bases\n",
                found.levels,
                bases.len()
            );
            notes.push_str(&found.swept.line(s.process.unreadable_regions()));
            notes.push_str(&scan::stop_line(found.swept.stop, &format!("{} chains", path::CHAINS_MAX)));
            let mut out = path::paths_page(
                &found,
                &bases,
                &label,
                &notes,
                page.offset,
                page.limit.n,
                page.count_only,
            );
            if found.chains.is_empty() && !page.count_only {
                out.push_str("next: no chain within these limits; raise depth or max_offset, or the value may sit on a thread's stack, which no base covers\n");
            }
            Ok(out)
        })
        .map(|text| {
            let text = page.limit.noted(text);
            let text = depth.noted(text);
            if asked > MAX_OFFSET_CAP {
                format!("# max_offset {asked} capped at {MAX_OFFSET_CAP}\n{text}")
            } else {
                text
            }
        })
    }
}

#[cfg(all(test, windows))]
mod tests {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

    use rmcp::handler::server::wrapper::Parameters;

    use crate::params::{
        LiveAttachParams, LivePathParams, LiveScanParams, ScanCompare, ScanKind, ScanScope,
    };

    /// A scan's parameters with only the name set.
    fn scan(name: &str) -> LiveScanParams {
        LiveScanParams {
            name: name.to_owned(),
            value: None,
            kind: None,
            tolerance: None,
            compare: None,
            scope: None,
            module: None,
            offset: None,
            limit: None,
            count_only: None,
        }
    }

    /// A value planted on this process's heap is found by a first scan,
    /// kept by the next scans as it rises and when it equals a value, and
    /// reached by a pointer chain from a global of this executable.
    ///
    /// # Panics
    ///
    /// When the planted value or the chain is not found, or a wrong call is
    /// taken.
    #[test]
    fn a_planted_value_is_scanned_narrowed_and_reached() {
        /// The global the chain starts at.
        static ROOT: AtomicUsize = AtomicUsize::new(0);
        const PLANTED: u64 = 0x6b6b_2121_8484_0001;
        let inner: Box<[AtomicU64; 8]> = Box::new(std::array::from_fn(|_| AtomicU64::new(0)));
        inner[5].store(PLANTED, Ordering::SeqCst);
        let outer: Box<[AtomicUsize; 4]> = Box::new(std::array::from_fn(|_| AtomicUsize::new(0)));
        outer[2].store(inner.as_ptr() as usize, Ordering::SeqCst);
        ROOT.store(outer.as_ptr() as usize, Ordering::SeqCst);
        let target = format!("{:#x}", inner.as_ptr() as usize + 0x28);
        let server = crate::BorerServer {
            live_any: true,
            ..crate::BorerServer::default()
        };
        server
            .live_attach(Parameters(LiveAttachParams {
                process: std::process::id().to_string(),
            }))
            .expect("attach to self");
        let first = server
            .live_scan(Parameters(LiveScanParams {
                value: Some(format!("{PLANTED:#x}")),
                kind: Some(ScanKind::U64),
                scope: Some(ScanScope::Heap),
                ..scan("v")
            }))
            .expect("a first scan");
        assert!(first.contains(&format!("\n{target} ")), "{first}");
        assert!(first.contains("MiB in "), "{first}");
        inner[5].store(PLANTED + 5, Ordering::SeqCst);
        let rose = server
            .live_scan(Parameters(LiveScanParams {
                compare: Some(ScanCompare::Increased),
                ..scan("v")
            }))
            .expect("a next scan");
        assert!(rose.contains("# increased kept "), "{rose}");
        assert!(rose.contains(&format!("\n{target} ")), "{rose}");
        let equal = server
            .live_scan(Parameters(LiveScanParams {
                compare: Some(ScanCompare::Equal),
                value: Some((PLANTED + 5).to_string()),
                ..scan("v")
            }))
            .expect("an equal scan");
        assert!(equal.contains(&format!("\n{target} ")), "{equal}");
        inner[5].store(PLANTED, Ordering::SeqCst);
        let paged = server
            .live_scan(Parameters(scan("v")))
            .expect("the set, paged");
        assert!(paged.contains("nothing was read now"), "{paged}");
        assert!(paged.contains(&format!("\n{target} ")), "{paged}");
        for wrong in [
            LiveScanParams {
                compare: Some(ScanCompare::Changed),
                ..scan("nope")
            },
            LiveScanParams {
                compare: Some(ScanCompare::Increased),
                value: Some("1".to_owned()),
                ..scan("v")
            },
            LiveScanParams {
                value: Some("1".to_owned()),
                scope: Some(ScanScope::Module),
                ..scan("w")
            },
        ] {
            server.live_scan(Parameters(wrong)).expect_err("refused");
        }
        let chains = server
            .live_path(Parameters(LivePathParams {
                address: target,
                depth: Some(2),
                max_offset: Some(0x100),
                module: None,
                offset: None,
                limit: Some(200),
                count_only: None,
            }))
            .expect("the chains");
        let root = format!("{:#x}", core::ptr::from_ref(&ROOT) as usize);
        let held = server
            .live_scan(Parameters(LiveScanParams {
                value: Some(format!("{:#x}", outer.as_ptr() as usize)),
                kind: Some(ScanKind::U64),
                ..scan("root")
            }))
            .expect("a scan for the pointer to outer");
        assert!(
            chains.contains("]+0x10]+0x28"),
            "{chains}\nROOT {root} outer {:p}\n{held}",
            outer.as_ptr()
        );
        assert!(chains.starts_with("# showing "), "{chains}");
        server.live_detach().expect("detach");
        drop((inner, outer));
    }
}
