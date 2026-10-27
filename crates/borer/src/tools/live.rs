//! The live tools: attaching to a running process and reading its memory
//! typed and named by the loaded binary.

use std::fmt::Write as _;

use borer_engine::analysis::parse_addr;
use borer_engine::live::{self as live, Memory as _, Rebase, Snapshot};
use borer_engine::program::{Feature, Program};
use borer_engine::{memory, num};
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::errors::err_params;
use crate::params::{
    Annotation, Filter, LiveAttachParams, LiveInstancesParams, LiveModulesParams, LiveObjectParams,
    LiveReadParams, LiveWatchParams, Page, count_param, must_fit_a_row,
};
use crate::safety::{Effect, effects};
use crate::state::{NO_BINARY, lock};

/// The environment variable that, set to `1`, lets `live_attach` take any
/// process the user can read rather than only one running the loaded
/// binary.
pub(crate) const LIVE_ANY_ENV: &str = "BORER_LIVE_ANY";

/// Whether a process's main image is the loaded binary, the one process
/// `live_attach` reads unless the user opened it to any.
///
/// A process name or id is a tool argument, and a tool argument can come
/// from text inside the analyzed binary, so without this an agent could be
/// talked into reading a browser's or a password manager's memory. The
/// image is the loaded binary when both paths name one file, or when the
/// image's file holds the loaded bytes exactly (a copy run from elsewhere).
///
/// # Arguments
///
/// * `program` - The loaded binary, `None` before `load_binary`.
/// * `image` - The process's main module, `None` when it lists none.
/// * `who` - The process as a message names it.
///
/// # Errors
///
/// When nothing is loaded, the process lists no main module, or its image
/// is another file; the message says how to attach anyway.
pub(crate) fn runs_loaded(
    program: Option<&Program>,
    image: Option<&live::Module>,
    who: &str,
) -> Result<(), String> {
    let anyway =
        format!("set {LIVE_ANY_ENV}=1 in the server's environment to attach to any process");
    let program = program.ok_or_else(|| {
        format!("load the binary {who} runs first: live_attach reads only a process whose main image is the loaded binary; or {anyway}")
    })?;
    let image = image.ok_or_else(|| format!("{who} lists no main module; {anyway}"))?;
    let path = std::path::Path::new(&image.path);
    if borer_engine::program::unusable_path(path).is_none() {
        let same_file = matches!(
            (std::fs::canonicalize(path), std::fs::canonicalize(&program.path)),
            (Ok(a), Ok(b)) if a == b
        );
        let same_bytes = || {
            std::fs::metadata(path)
                .is_ok_and(|m| m.is_file() && num::from_usize(program.bytes.len()) == m.len())
                && std::fs::read(path).is_ok_and(|b| b == program.bytes)
        };
        if same_file || same_bytes() {
            return Ok(());
        }
    }
    Err(format!(
        "{who} runs {}, not the loaded binary {}: live_attach reads only a process running the loaded binary; load_binary its image first, or {anyway}",
        borer_engine::text::short_path(&image.path),
        borer_engine::text::short_path(&program.path.display().to_string())
    ))
}

/// A process attached for reading, with where the loaded binary sits in it
/// and the snapshots taken of its memory.
#[derive(Debug)]
pub(crate) struct LiveSession {
    /// The process, open with read rights only.
    pub(crate) process: borer_live::Process,
    /// Where the loaded binary's image sits in the process, or why it is
    /// not mapped there; unmapped, addresses are taken as live.
    pub(crate) rebase: Result<Rebase, String>,
    /// Watches by name, so a diff names the fields that changed.
    pub(crate) snapshots: std::collections::BTreeMap<String, Watch>,
    /// Value scans' result sets by name, which a next scan narrows
    /// ([`crate::tools::livescan`]).
    pub(crate) scans: std::collections::BTreeMap<String, crate::tools::livescan::ScanSet>,
    /// The main thread's block of the image's thread-local storage, where
    /// the singletons the analysis placed at TLS offsets live; `None` when
    /// the image has no TLS or the block could not be read.
    pub(crate) tls_block: Option<u64>,
    /// The pointer width live reads use, in bytes: the mapped image's, else
    /// the process's own.
    pub(crate) word: usize,
}

impl LiveSession {
    /// Opens a session on a process with nothing mapped onto it yet.
    ///
    /// # Arguments
    ///
    /// * `process` - The process, open for reading.
    pub(crate) fn new(process: borer_live::Process) -> LiveSession {
        LiveSession {
            word: process.pointer_width(),
            process,
            rebase: Err(NO_BINARY.to_owned()),
            snapshots: std::collections::BTreeMap::new(),
            scans: std::collections::BTreeMap::new(),
            tls_block: None,
        }
    }

    /// Maps a binary onto the process.
    ///
    /// It finds the image among the modules by its headers
    /// ([`Rebase::of`]), the main thread's block of its thread-local
    /// storage, and the pointer width reads use. Called on attach and again
    /// on every `load_binary`, so the mapping is always the loaded binary's.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded binary, `None` when nothing is loaded.
    ///
    /// # Returns
    ///
    /// The lines saying where the image sits, or why it is not mapped.
    pub(crate) fn map(&mut self, program: Option<&Program>) -> String {
        self.tls_block = None;
        self.word = self.process.pointer_width();
        let Some(p) = program else {
            self.rebase = Err(NO_BINARY.to_owned());
            return "no binary loaded: load_binary the process's executable so live memory is named and typed\n".to_owned();
        };
        let file = p
            .path
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        self.rebase = Rebase::of(p, &self.process);
        let r = match &self.rebase {
            Ok(r) => *r,
            Err(why) => {
                return format!(
                    "the loaded binary {file} is not mapped onto this process: {why}; static addresses and names do not apply, numbers are taken as live addresses, and reads use the process's {}-byte pointers\n",
                    self.word
                );
            }
        };
        self.word = word_size(Some(p));
        let mut out = format!(
            "image {file} at live {:#x} = static {:#x} ({:#x} bytes), its headers match the file: static addresses and names rebase automatically\n",
            r.live_base,
            r.static_base,
            r.static_end - r.static_base
        );
        self.tls_block = p.headers.tls_index.and_then(|index| {
            let tid = self.process.threads().ok()?.into_iter().next()?;
            let teb = self.process.teb_of(tid).ok()?;
            live::tls_block(&self.process, &r, index, teb)
        });
        if let Some(b) = self.tls_block {
            let _ = writeln!(
                out,
                "thread-local storage: the main thread's block is at {b:#x}; a class's singleton there reads as Class::instance"
            );
        }
        out
    }

    /// The mapping, for a tool that types memory by the loaded binary.
    ///
    /// # Errors
    ///
    /// When the loaded binary is not mapped onto the process, saying why.
    pub(crate) fn mapped(&self) -> Result<Rebase, String> {
        self.rebase
            .as_ref()
            .copied()
            .map_err(|why| format!("{NOT_A_MODULE}: {why}"))
    }
}

/// Bytes of the process kept under a watch name.
#[derive(Debug, Clone)]
pub(crate) struct Watch {
    /// The bytes as they were when the watch was set or last reported.
    pub(crate) snapshot: Snapshot,
    /// The object's fields by offset, empty when its class is unknown; a
    /// diff names a change by them. Taken when the watch is set.
    pub(crate) fields: std::collections::BTreeMap<u64, live::Field>,
}

/// Bytes a watch covers when neither a length nor a class's fields say.
pub(crate) const WATCH_DEFAULT: usize = 256;

/// The prefix that makes a live tool take a number as a process address
/// as it is, never rebased from the loaded binary's static range.
pub(crate) const LIVE_PREFIX: &str = "live:";

/// Modules `live_attach` lists before pointing at `live_modules`.
pub(crate) const ATTACH_MODULES: usize = 16;

/// Watch names a re-attach lists when it drops them.
pub(crate) const DROPPED_NAMES: usize = 8;

/// The refusal of a live tool that types memory by the loaded binary's
/// classes when the binary is not loaded in the process.
pub(crate) const NOT_A_MODULE: &str =
    "the loaded binary is not a module of the process, so its classes do not apply";

/// Says that the attached process has exited, for every live tool asked
/// after it did.
///
/// # Arguments
///
/// * `process` - The attached process.
/// * `code` - Its exit code.
pub(crate) fn exited(process: &borer_live::Process, code: u32) -> String {
    format!(
        "{} (pid {}) has exited (exit code {code:#x}), so nothing of it is left to read; live_attach a running process",
        process.name(),
        process.pid()
    )
}

/// The pointer width in bytes of a program, or of the host when none is
/// loaded.
///
/// # Arguments
///
/// * `program` - The loaded program, if any.
pub(crate) fn word_size(program: Option<&Program>) -> usize {
    program.map_or(8, |p| if p.is_64 { 8 } else { 4 })
}

#[tool_router(router = live_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Runs `f` with the attached process.
    ///
    /// A process that has exited is said to have, before `f` runs: its
    /// memory is gone, and a read, a scan or a diff would otherwise answer
    /// "not readable" or "0 instances" as if the address were the problem.
    ///
    /// Every refusal is invalid params, as [`Self::with_program`]'s are: a
    /// body refuses what it was asked (an address not readable, a name or
    /// class that is not there, a process that is gone), and the agent's
    /// next move is to change the call, so one code says so for every live
    /// tool and for the static ones alike.
    ///
    /// # Arguments
    ///
    /// * `f` - The tool body over the session.
    ///
    /// # Errors
    ///
    /// Invalid params when no process is attached, it has exited, or `f`
    /// refuses the request.
    pub(crate) fn with_live(
        &self,
        f: impl FnOnce(&mut LiveSession) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        let mut guard = lock(&self.live);
        let session = guard
            .as_mut()
            .ok_or_else(|| err_params("no process attached: live_attach first"))?;
        if let Some(code) = session.process.exit_code() {
            return Err(err_params(exited(&session.process, code)));
        }
        f(session).map_err(err_params)
    }

    /// Resolves an address an agent gave for the process: a name or a
    /// static address of the loaded binary moves into the process, any
    /// other number is taken as live, and a number after `live:` is live
    /// even inside the image's static range (a heap the process placed
    /// there).
    ///
    /// A singleton the analysis placed in thread-local storage has no
    /// static address: its slot is at the offset in the thread's block.
    ///
    /// # Arguments
    ///
    /// * `session` - The attached process.
    /// * `text` - The argument as the agent passed it.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name.
    pub(crate) fn live_addr(&self, session: &LiveSession, text: &str) -> Result<u64, String> {
        let program = self.loaded();
        if let (Some(_), Some(block)) = (&program, session.tls_block)
            && let Some(class) = text.trim().to_lowercase().strip_suffix("::instance")
            && let Ok(a) = self.ensure_analysis()
            && let Some((off, _)) = a
                .classes
                .tls_slots
                .iter()
                .find(|(_, c)| c.to_lowercase() == class)
        {
            return block
                .checked_add(*off)
                .ok_or_else(|| format!("{text}: the TLS offset overflows"));
        }
        if let Some(live) = text.trim().strip_prefix(LIVE_PREFIX) {
            return parse_addr(live).ok_or_else(|| {
                format!("{text}: after {LIVE_PREFIX} comes a number (0x-hex or decimal)")
            });
        }
        if let Some(va) = parse_addr(text) {
            return Ok(session.rebase.as_ref().map_or(va, |r| r.live_of(va)));
        }
        let Some(p) = program else {
            return Err(format!(
                "{text} is not an address, and no binary is loaded to look the name up in"
            ));
        };
        let va = self.addr(&p, text)?;
        let r = session.rebase.as_ref().map_err(|why| {
            format!("{text} is {va:#x} in the loaded binary, which is not mapped onto the process ({why}), so it has no live address")
        })?;
        Ok(r.live_of(va))
    }

    /// Follows a singleton's slot to its object: `Class::instance` names
    /// the slot that holds the pointer, and the object is what it points at.
    ///
    /// # Arguments
    ///
    /// * `session` - The attached process.
    /// * `text` - The address argument as given.
    /// * `va` - What it resolved to.
    /// * `word` - The pointer width in bytes.
    ///
    /// # Errors
    ///
    /// When the slot is not readable or holds no object.
    pub(crate) fn through_singleton(
        session: &LiveSession,
        text: &str,
        va: u64,
        word: usize,
    ) -> Result<(u64, String), String> {
        if !text.trim().to_lowercase().ends_with("::instance") {
            return Ok((va, String::new()));
        }
        let values = live::read_values(&session.process, va, memory::Kind::Ptr, 1, word)?;
        let target = values.first().and_then(|v| v.target).unwrap_or(0);
        if target == 0 {
            return Err(format!(
                "{text}: the slot at {va:#x} holds no object (null)"
            ));
        }
        Ok((
            target,
            format!("{text}: slot {va:#x} -> object {target:#x}\n"),
        ))
    }

    /// Attaches to a running process for reading.
    ///
    /// # Arguments
    ///
    /// * `LiveAttachParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no process matches, several do, the system refuses a read
    /// handle, or the process does not run the loaded binary
    /// ([`runs_loaded`]) and the server was not started with
    /// `BORER_LIVE_ANY=1`.
    #[tool(
        description = "Attach read-only to a running process (name or pid) of the loaded binary, so live tools take static addresses. Windows only; another binary needs BORER_LIVE_ANY=1. Replaces an attach; live_detach ends it.",
        meta = effects(&[Effect::ReadsProcessMemory, Effect::ChangesSession]),
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    pub(crate) fn live_attach(
        &self,
        Parameters(LiveAttachParams { process }): Parameters<LiveAttachParams>,
    ) -> Result<String, ErrorData> {
        let proc = borer_live::Process::attach(&process).map_err(err_params)?;
        let modules = proc.modules();
        if !self.live_any {
            let image = modules
                .iter()
                .find(|m| m.name.eq_ignore_ascii_case(proc.name()))
                .or_else(|| modules.first());
            let who = format!("process {} ({})", proc.pid(), proc.name());
            runs_loaded(self.loaded().as_deref(), image, &who).map_err(err_params)?;
        }
        let mut out = format!(
            "attached to {} (pid {}), {} modules, read-only\n",
            proc.name(),
            proc.pid(),
            modules.len()
        );
        let mut session = LiveSession::new(proc);
        out.push_str(&session.map(self.loaded().as_deref()));
        out.push_str("modules:\n");
        for m in modules.iter().take(ATTACH_MODULES) {
            let _ = writeln!(out, "  {:#x} {:>10} {}", m.base, m.size, m.name);
        }
        if modules.len() > ATTACH_MODULES {
            let _ = writeln!(
                out,
                "  ... {} more: live_modules(offset={ATTACH_MODULES}) lists them, live_modules(filter=...) finds one",
                modules.len() - ATTACH_MODULES
            );
        }
        out.push_str("next: live_object(address or singleton name), live_instances(class), live_read(address, kind), live_watch(name, address), live_scan(name, value), borer://livepath/<address>\n");
        if let Some(was) = lock(&self.live).replace(session) {
            let _ = write!(
                out,
                "note: detached from {} (pid {}) first",
                was.process.name(),
                was.process.pid()
            );
            if was.snapshots.is_empty() {
                out.push('\n');
            } else {
                let names: Vec<&str> = was
                    .snapshots
                    .keys()
                    .take(DROPPED_NAMES)
                    .map(String::as_str)
                    .collect();
                let more = was.snapshots.len() - names.len();
                let _ = writeln!(
                    out,
                    "; its {} watch(es) are dropped: {}{}",
                    was.snapshots.len(),
                    names.join(", "),
                    if more > 0 {
                        format!(", +{more} more")
                    } else {
                        String::new()
                    }
                );
            }
            if !was.scans.is_empty() {
                let names: Vec<&str> = was.scans.keys().map(String::as_str).collect();
                let _ = writeln!(
                    out,
                    "note: its {} result set(s) are dropped: {}",
                    names.len(),
                    names.join(", ")
                );
            }
        }
        Ok(out)
    }

    /// Detaches from the process.
    ///
    /// # Errors
    ///
    /// Never; detaching with nothing attached is a no-op.
    #[tool(
        description = "Detach from the attached process and drop its watches; the process is untouched, and nothing attached is a no-op. Not needed before attaching elsewhere: live_attach replaces it.",
        meta = effects(&[Effect::ChangesSession]),
        annotations(
            read_only_hint = false,
            destructive_hint = true,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn live_detach(&self) -> Result<String, ErrorData> {
        let was = lock(&self.live).take();
        Ok(match was {
            Some(s) => format!(
                "detached from {} (pid {}){}",
                s.process.name(),
                s.process.pid(),
                s.process
                    .exit_code()
                    .map_or_else(String::new, |code| format!(
                        ", which had exited (exit code {code:#x})"
                    ))
            ),
            None => "no process was attached".to_owned(),
        })
    }

    /// Lists the attached process's modules, a page at a time.
    ///
    /// # Arguments
    ///
    /// * `LiveModulesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params for a zero limit, or when no process is attached or
    /// it has exited.
    #[tool(
        description = "List the attached process's modules (base, size, name), paged. Not for the binary's imports (use symbols). Fails if nothing is attached.",
        meta = effects(&[Effect::ReadsProcessMemory]),
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = true
        )
    )]
    pub(crate) fn live_modules(
        &self,
        Parameters(LiveModulesParams {
            filter,
            offset,
            limit,
            count_only,
        }): Parameters<LiveModulesParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, count_only, 50, 500)?;
        let filter = Filter::new(filter.as_deref());
        self.with_live(|s| {
            let image = s.rebase.as_ref().ok().map(|r| r.live_base);
            let (total, table) = live::modules_page(
                &s.process.modules(),
                filter.needle(),
                page.offset,
                page.limit.n,
                image,
            );
            Ok(if page.count_only {
                format!("# {total} modules\n")
            } else {
                table
            })
        })
        .map(|text| page.limit.noted(text))
    }

    /// Reads typed values from the process.
    ///
    /// # Arguments
    ///
    /// * `LiveReadParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params for an unknown kind, or when no process is attached,
    /// the address does not resolve, or its first value does not read.
    #[tool(
        description = "Read typed values from the attached process; static addresses rebase onto it and pointers say what they point at. Not for the file on disk (use read) or an object (use live_object).",
        meta = effects(&[Effect::ReadsProcessMemory]),
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    pub(crate) fn live_read(
        &self,
        Parameters(LiveReadParams {
            address,
            kind,
            count,
        }): Parameters<LiveReadParams>,
    ) -> Result<String, ErrorData> {
        let kind_text = kind.unwrap_or_default();
        let kind: memory::Kind = kind_text.into();
        let count = count_param(count, 1, 256, "count")?;
        let n = count.n;
        let program = self.loaded();
        let overlay = self.overlay();
        self.with_live(|s| {
            let va = self.live_addr(s, &address)?;
            let word = s.word;
            let values = live::read_values(&s.process, va, kind, n, word)?;
            let rebase = s.rebase.as_ref().ok().copied();
            let analysis = match (rebase, values.iter().any(|v| v.target.is_some())) {
                (Some(_), true) => self.ensure_analysis().ok(),
                _ => None,
            };
            let origin = rebase
                .and_then(|r| r.to_static(va))
                .map_or_else(String::new, |st| format!(" (= static {st:#x})"));
            let mut out = format!(
                "# {} {kind_text} value(s) at live {va:#x}{origin}",
                values.len()
            );
            if values.len() < n {
                let next = values
                    .last()
                    .map_or(va, |v| v.at.wrapping_add(num::from_usize(v.size)));
                let _ = write!(
                    out,
                    "; asked for {n}, nothing readable as {kind_text} at {next:#x}"
                );
            }
            out.push('\n');
            for v in &values {
                let note = match (v.target, &program, &analysis, rebase) {
                    (Some(t), Some(p), Some(a), Some(r)) => r
                        .describe(p, a, &overlay, t)
                        .map(|d| format!("  -> {d}"))
                        .or_else(|| {
                            live::class_at(&s.process, &r, a, t, word)
                                .map(|c| format!("  -> {c} object"))
                        })
                        .unwrap_or_default(),
                    _ => String::new(),
                };
                let _ = writeln!(out, "{:#x}  {}{note}", v.at, v.text);
            }
            Ok(out)
        })
        .map(|text| count.noted(text))
    }

    /// Reads an object of the process with its class's fields.
    ///
    /// # Arguments
    ///
    /// * `LiveObjectParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no process is attached or no binary is loaded, the address does
    /// not resolve, the class is unknown, or the object is not readable.
    #[tool(
        description = "Read one object in the attached process as its class: each field's name, type and value, pointers resolved. Not for raw values (use live_read) or finding objects (use live_instances).",
        meta = effects(&[Effect::ReadsProcessMemory]),
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    pub(crate) fn live_object(
        &self,
        Parameters(LiveObjectParams { address, class }): Parameters<LiveObjectParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, o| {
            self.with_live(|s| {
                let r = s.mapped()?;
                let va = self.live_addr(s, &address)?;
                let (va, via) = Self::through_singleton(s, &address, va, s.word)?;
                let text = live::object(&s.process, p, a, o, &r, va, class.as_deref())?;
                Ok(format!("{via}{text}"))
            })
            .map_err(|e| e.message.to_string())
        })
    }

    /// Finds the instances of a class in the process.
    ///
    /// # Arguments
    ///
    /// * `LiveInstancesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no process is attached or no binary is loaded, or the analysis
    /// knows no vtable for the class.
    #[tool(
        description = "Find a class's live objects by scanning the attached process for its vtable, paged. Then read one with live_object. Fails if nothing is attached or no vtable is known.",
        meta = effects(&[Effect::ReadsProcessMemory]),
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    pub(crate) fn live_instances(
        &self,
        Parameters(LiveInstancesParams {
            class,
            offset,
            limit,
            count_only,
        }): Parameters<LiveInstancesParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, count_only, 64, 512)?;
        let collect = if page.count_only {
            live::COUNT_MAX
        } else {
            page.offset.saturating_add(page.limit.n)
        };
        self.with_analysis(Feature::Decompile, |_, a, _| {
            self.with_live(|s| {
                let r = s.mapped()?;
                let scan = live::instances(&s.process, &r, a, &class, s.word, collect)?;
                let mut out = live::instances_page(
                    &scan,
                    &class,
                    page.offset,
                    page.limit.n,
                    page.count_only,
                );
                if !scan.hits.is_empty() && !page.count_only {
                    out.push_str("next: live_object(address) for the fields; live_watch(name, address), then live_watch(name) for what changes\n");
                }
                Ok(out)
            })
            .map_err(|e| e.message.to_string())
        })
        .map(|text| page.limit.noted(text))
    }

    /// Watches memory of the process: starts a watch, or lists what changed.
    ///
    /// # Arguments
    ///
    /// * `LiveWatchParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no process is attached, the address does not resolve or is not
    /// readable, the class given is unknown, or no watch has the name.
    #[tool(
        description = "Watch attached-process memory: with address, snapshot it under name; without, show what changed since the last look, fields named. For one snapshot use live_read.",
        meta = effects(&[Effect::ReadsProcessMemory]),
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = true
        )
    )]
    pub(crate) fn live_watch(
        &self,
        Parameters(LiveWatchParams {
            name,
            address,
            length,
            class,
        }): Parameters<LiveWatchParams>,
    ) -> Result<String, ErrorData> {
        must_fit_a_row(&name, Annotation::Name)?;
        let length = length
            .map(|n| count_param(Some(n), 1, live::READ_MAX, "length"))
            .transpose()?;
        let program = self.loaded();
        let overlay = self.overlay();
        self.with_live(|s| {
            let Some(address) = address else {
                let watch = s
                    .snapshots
                    .get(&name)
                    .cloned()
                    .ok_or_else(|| format!("no watch is named {name}; pass an address to start one"))?;
                let diff = watch.snapshot.diff(&s.process, &watch.fields, s.word)?;
                let mut out = live::render_changes(&watch.snapshot, &diff, &watch.fields);
                if diff.now != watch.snapshot {
                    out.push_str("(the watch now holds these bytes)\n");
                    s.snapshots.insert(
                        name.clone(),
                        Watch {
                            snapshot: diff.now,
                            fields: watch.fields,
                        },
                    );
                }
                return Ok(out);
            };
            let va = self.live_addr(s, &address)?;
            let analysis = match (&program, &class) {
                (Some(_), Some(_)) => Some(self.ensure_analysis()?),
                (Some(_), None) if s.rebase.is_ok() => self.ensure_analysis().ok(),
                _ => None,
            };
            let (class, fields) = match (class, &program, &analysis) {
                (Some(c), None, _) => {
                    return Err(format!(
                        "class {c} names fields of a loaded binary, and none is loaded"
                    ));
                }
                (Some(c), Some(p), Some(a)) => {
                    let fields = live::fields_of(p, a, &overlay, &c)
                        .ok_or_else(|| format!("no function belongs to class {c}"))?;
                    (Some(c), fields)
                }
                (Some(c), Some(_), None) => {
                    return Err(format!("no function belongs to class {c}"));
                }
                (None, Some(p), Some(a)) => {
                    let found = s
                        .rebase
                        .as_ref()
                        .ok()
                        .and_then(|r| live::class_at(&s.process, r, a, va, s.word));
                    let fields = found
                        .as_deref()
                        .and_then(|c| live::fields_of(p, a, &overlay, c))
                        .unwrap_or_default();
                    (found, fields)
                }
                (None, None, _) | (None, Some(_), None) => (None, std::collections::BTreeMap::new()),
            };
            let size = fields
                .iter()
                .map(|(off, f)| {
                    usize::try_from(*off)
                        .unwrap_or(live::READ_MAX)
                        .saturating_add(f.len)
                })
                .max()
                .unwrap_or(WATCH_DEFAULT);
            let len = length.map_or(size.clamp(8, live::READ_MAX), |asked| asked.n);
            let snapshot = Snapshot::take(&s.process, va, len)?;
            let readable = if snapshot.bytes.len() < snapshot.len {
                format!("{} of {} bytes readable", snapshot.bytes.len(), snapshot.len)
            } else {
                format!("{} bytes", snapshot.len)
            };
            let out = format!(
                "watch {name}: {readable} at {va:#x}{}; live_watch(\"{name}\") after the change you want to see",
                class
                    .as_ref()
                    .map_or_else(String::new, |c| format!(" ({c}, {} fields)", fields.len()))
            );
            s.snapshots
                .insert(name.clone(), Watch { snapshot, fields });
            Ok(out)
        })
        .map(|text| match length {
            Some(asked) => asked.noted(text),
            None => text,
        })
    }
}

#[cfg(test)]
mod tests {
    #[cfg(windows)]
    use crate::testing::raw_server;

    /// Loads a file into a server, without its PDB, and returns the summary.
    ///
    /// # Panics
    ///
    /// When the file does not load.
    #[cfg(windows)]
    fn load_into(server: &crate::BorerServer, path: &std::path::Path) -> String {
        use crate::params::LoadBinaryParams;
        use rmcp::handler::server::wrapper::Parameters;
        server
            .load_binary(Parameters(LoadBinaryParams {
                path: path.display().to_string(),
                entry_file_offset: None,
                pdb: Some(false),
                arch: None,
                base: None,
                entry: None,
                regions: None,
            }))
            .expect("the file loads")
    }

    /// A process attached before `load_binary` is mapped onto the binary
    /// the load brings.
    ///
    /// A static address then reads at its live place; a file that only
    /// shares the module's name is another build, refused with what
    /// differs and never mapped.
    ///
    /// # Panics
    ///
    /// When the load leaves the process unmapped, the read is not rebased,
    /// or the impostor is mapped.
    #[cfg(windows)]
    #[test]
    fn the_live_mapping_follows_load_binary_and_checks_headers() {
        use crate::params::LiveAttachParams;
        use crate::params::LiveReadParams;
        use rmcp::handler::server::wrapper::Parameters;
        let exe = std::env::current_exe().expect("the test binary has a path");
        let server = crate::BorerServer {
            live_any: true,
            ..crate::BorerServer::default()
        };
        let attached = server
            .live_attach(Parameters(LiveAttachParams {
                process: std::process::id().to_string(),
            }))
            .expect("attach to self");
        assert!(attached.contains("no binary loaded"), "{attached}");
        let loaded = load_into(&server, &exe);
        assert!(loaded.contains("its headers match the file"), "{loaded}");
        let entry = server
            .loaded()
            .and_then(|p| p.entry)
            .expect("the test binary has an entry");
        let read = server
            .live_read(Parameters(LiveReadParams {
                address: format!("{entry:#x}"),
                kind: Some(crate::params::ReadKind::U8),
                count: None,
            }))
            .expect("the entry is readable");
        assert!(read.contains(&format!("(= static {entry:#x})")), "{read}");
        let unrebased = server.live_read(Parameters(LiveReadParams {
            address: format!("live:{entry:#x}"),
            kind: Some(crate::params::ReadKind::U8),
            count: None,
        }));
        assert!(
            unrebased.as_ref().map_or_else(
                |e| e
                    .message
                    .starts_with(&format!("{entry:#x} is not readable")),
                |text| text.starts_with(&format!("# 1 u8 value(s) at live {entry:#x}\n"))
            ),
            "live: is taken as it is: {unrebased:?}"
        );

        let dir = std::env::temp_dir().join(format!("borer-live-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp directory");
        let impostor = dir.join(exe.file_name().expect("a file name"));
        let mut bytes = std::fs::read(&exe).expect("read the test binary");
        let pe = usize::try_from(u32::from_le_bytes(
            bytes[0x3c..0x40].try_into().expect("four bytes"),
        ))
        .expect("fits");
        bytes[pe + 8] ^= 0xff;
        std::fs::write(&impostor, &bytes).expect("write the impostor");
        let loaded = load_into(&server, &impostor);
        std::fs::remove_dir_all(&dir).expect("remove the temp directory");
        assert!(loaded.contains("is another build (timestamp"), "{loaded}");
        assert!(
            crate::state::lock(&server.live)
                .as_ref()
                .is_some_and(|s| s.rebase.is_err()),
            "the impostor is not mapped"
        );
        server.live_detach().expect("detach");
    }

    /// Only a process running the loaded binary is attached.
    ///
    /// With nothing loaded, or another binary loaded, attaching to this
    /// test process is refused, and with the test binary itself loaded it
    /// is taken. A copy of the loaded file at another path is the same
    /// image by its bytes.
    ///
    /// # Panics
    ///
    /// When another program's process is attached or the binary's own is
    /// refused.
    #[cfg(windows)]
    #[test]
    fn live_attach_takes_only_a_process_running_the_loaded_binary() {
        use crate::params::LiveAttachParams;
        use rmcp::handler::server::wrapper::Parameters;
        let me = std::process::id().to_string();
        let attach = |server: &crate::BorerServer| {
            server.live_attach(Parameters(LiveAttachParams {
                process: me.clone(),
            }))
        };
        let empty = crate::BorerServer::default();
        let none = attach(&empty).expect_err("nothing loaded");
        assert!(none.message.contains("load the binary"), "{}", none.message);
        assert!(
            none.message.contains("BORER_LIVE_ANY=1"),
            "{}",
            none.message
        );
        let other = attach(&raw_server()).expect_err("another binary loaded");
        assert!(
            other.message.contains("not the loaded binary"),
            "{}",
            other.message
        );
        assert!(crate::state::lock(&empty.live).is_none());
        let server = crate::BorerServer::default();
        let exe = std::env::current_exe().expect("the test binary has a path");
        load_into(&server, &exe);
        attach(&server).expect("the loaded binary's own process");
        server.live_detach().expect("detach");
        let exe_module = |path: &std::path::Path| borer_engine::live::Module {
            name: "x.exe".to_owned(),
            path: path.display().to_string(),
            base: 0,
            size: 0,
        };
        let program = server.loaded().expect("loaded");
        let dir = std::env::temp_dir().join(format!("borer-live-copy-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp directory");
        let copy = dir.join("copy.exe");
        std::fs::copy(&exe, &copy).expect("copy the test binary");
        let changed = dir.join("changed.exe");
        let mut bytes = std::fs::read(&exe).expect("read");
        if let Some(last) = bytes.last_mut() {
            *last ^= 0xff;
        }
        std::fs::write(&changed, &bytes).expect("write");
        let by_copy = super::runs_loaded(Some(&program), Some(&exe_module(&copy)), "p");
        let by_change = super::runs_loaded(Some(&program), Some(&exe_module(&changed)), "p");
        let by_share = super::runs_loaded(
            Some(&program),
            Some(&exe_module(std::path::Path::new(r"\\host\share\x.exe"))),
            "p",
        );
        std::fs::remove_dir_all(&dir).expect("clean up");
        assert!(by_copy.is_ok(), "{by_copy:?}");
        assert!(by_change.is_err(), "another file's bytes");
        assert!(by_share.is_err(), "a share is never opened");
    }

    /// Every live refusal is invalid params, as a static one is, so one code
    /// tells the agent to change the call: nothing attached, an address not
    /// readable, a process name that is empty.
    ///
    /// # Panics
    ///
    /// When a refusal comes back as an internal error or says the wrong thing.
    #[test]
    fn a_live_refusal_is_invalid_params() {
        use crate::params::LiveAttachParams;
        use crate::params::LiveReadParams;
        use rmcp::handler::server::wrapper::Parameters;
        use rmcp::model::ErrorCode;
        let server = crate::BorerServer {
            live_any: true,
            ..crate::BorerServer::default()
        };
        let read = |address: &str| {
            server
                .live_read(Parameters(LiveReadParams {
                    address: address.to_owned(),
                    kind: None,
                    count: None,
                }))
                .expect_err("refused")
        };
        let none = read("0x10");
        assert_eq!(none.code, ErrorCode::INVALID_PARAMS);
        assert_eq!(none.message, "no process attached: live_attach first");
        let attach = |process: &str| {
            server.live_attach(Parameters(LiveAttachParams {
                process: process.to_owned(),
            }))
        };
        let blank = attach("").expect_err("no process named");
        assert_eq!(blank.code, ErrorCode::INVALID_PARAMS);
        if cfg!(windows) {
            assert!(
                blank.message.starts_with("no process given: "),
                "{}",
                blank.message
            );
            attach(&std::process::id().to_string()).expect("attach to self");
            let unreadable = read("0x10");
            assert_eq!(unreadable.code, ErrorCode::INVALID_PARAMS);
            assert_eq!(unreadable.message, "0x10 is not readable in the process");
            server.live_detach().expect("detach");
        }
    }

    /// A second attach says it drops the first one's watches, `reload` says
    /// the live session ends with the server, and the module list pages.
    ///
    /// # Panics
    ///
    /// When a drop goes unsaid or the module list does not page.
    #[cfg(windows)]
    #[test]
    fn the_live_session_says_what_it_drops_and_pages_modules() {
        use crate::params::LiveAttachParams;
        use crate::params::LiveModulesParams;
        use crate::params::LiveWatchParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = crate::BorerServer {
            live_any: true,
            ..raw_server()
        };
        let attach = || {
            server
                .live_attach(Parameters(LiveAttachParams {
                    process: std::process::id().to_string(),
                }))
                .expect("attach to self")
        };
        attach();
        server
            .live_watch(Parameters(LiveWatchParams {
                name: "w".to_owned(),
                address: Some("0x7ffe0000".to_owned()),
                length: Some(8),
                class: None,
            }))
            .expect("the shared user page is readable");
        let again = attach();
        assert!(
            again.contains("its 1 watch(es) are dropped: w\n"),
            "{again}"
        );
        let reload = server.reload().expect("reload answers");
        assert!(
            reload.contains("and its 0 watch(es) end with this server: live_attach again"),
            "{reload}"
        );
        let modules = |filter: Option<&str>, count_only| {
            server
                .live_modules(Parameters(LiveModulesParams {
                    filter: filter.map(str::to_owned),
                    offset: None,
                    limit: Some(1),
                    count_only,
                }))
                .expect("the module list")
        };
        let page = modules(Some(".dll"), None);
        assert!(page.starts_with("# showing 1 of "), "{page}");
        assert_eq!(page.lines().count(), 3, "{page}");
        let count = modules(None, Some(true));
        assert!(
            count.ends_with(" modules\n") && count.lines().count() == 1,
            "{count}"
        );
        server.live_detach().expect("detach");
    }

    /// Once the attached process exits, every live tool says it has exited
    /// instead of blaming the address, and so does the detach.
    ///
    /// # Panics
    ///
    /// When a tool answers after the exit, or blames the address.
    #[cfg(windows)]
    #[test]
    fn every_live_tool_says_the_process_exited() {
        use crate::params::LiveAttachParams;
        use crate::params::LiveReadParams;
        use crate::params::LiveWatchParams;
        use rmcp::handler::server::wrapper::Parameters;
        let mut child = std::process::Command::new("ping")
            .args(["-n", "60", "127.0.0.1"])
            .stdout(std::process::Stdio::null())
            .spawn()
            .expect("ping starts");
        let server = crate::BorerServer {
            live_any: true,
            ..crate::BorerServer::default()
        };
        let mut tries = 0;
        while let Err(e) = server.live_attach(Parameters(LiveAttachParams {
            process: child.id().to_string(),
        })) {
            tries += 1;
            assert!(tries < 500, "{}", e.message);
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
        let watch = |address: Option<&str>| {
            server.live_watch(Parameters(LiveWatchParams {
                name: "w".to_owned(),
                address: address.map(str::to_owned),
                length: Some(8),
                class: None,
            }))
        };
        watch(Some("0x7ffe0000")).expect("the shared user page is readable");
        child.kill().expect("end ping");
        child.wait().expect("ping ended");
        let read = server
            .live_read(Parameters(LiveReadParams {
                address: "0x7ffe0000".to_owned(),
                kind: None,
                count: None,
            }))
            .expect_err("the process is gone");
        assert!(
            read.message.contains("has exited (exit code 0x1)"),
            "{}",
            read.message
        );
        let diff = watch(None).expect_err("the process is gone");
        assert!(diff.message.contains("has exited"), "{}", diff.message);
        let detached = server.live_detach().expect("detach");
        assert!(
            detached.ends_with(", which had exited (exit code 0x1)"),
            "{detached}"
        );
    }

    /// A watch refuses a class the analysis does not know, as `live_object`
    /// does.
    ///
    /// A watch without a class reports a change as the whole aligned word.
    ///
    /// # Panics
    ///
    /// When the unknown class is accepted or the change is not reported
    /// as the word's value.
    #[cfg(windows)]
    #[test]
    fn a_watch_refuses_an_unknown_class_and_reports_whole_words() {
        use crate::params::LiveAttachParams;
        use crate::params::LiveWatchParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = crate::BorerServer {
            live_any: true,
            ..raw_server()
        };
        server
            .live_attach(Parameters(LiveAttachParams {
                process: std::process::id().to_string(),
            }))
            .expect("attach to self");
        let cell = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0xff));
        let at = format!("{:#x}", cell.as_ptr() as usize);
        let watch = |class: Option<&str>, address: Option<&str>| {
            server.live_watch(Parameters(LiveWatchParams {
                name: "w".to_owned(),
                address: address.map(str::to_owned),
                length: Some(8),
                class: class.map(str::to_owned),
            }))
        };
        let refused = watch(Some("Nope"), Some(&at)).expect_err("no such class");
        assert_eq!(refused.message, "no function belongs to class Nope");
        let started = watch(None, Some(&at)).expect("a watch of a heap word");
        assert!(started.starts_with("watch w: 8 bytes at "), "{started}");
        cell.store(0x100, std::sync::atomic::Ordering::SeqCst);
        let diff = watch(None, None).expect("the diff");
        assert!(diff.contains("(255 -> 256)"), "{diff}");
        server.live_detach().expect("detach");
    }
}
