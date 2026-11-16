//! The handlers behind the `borer://` resource templates, and the help
//! that says how to read each one.
//!
//! The engine answers most resources on its own ([`borer_engine::answer`]);
//! this holds the ones that read what the server holds (another build or a
//! file the URI names, the packs, the decompilation index on disk, the
//! session), each answering in the same table conventions as the tools, and
//! the call that prepares what an engine answer reads
//! ([`BorerServer::engine_answer`]). `read_resource` in `main.rs` parses the
//! URI and dispatches here.

use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;

use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::answer::Need;
use borer_engine::program::{Feature, Program};
use borer_engine::strings::walk::{Needle, StringRow, row_matches};
use rmcp::ErrorData;

use crate::BorerServer;
use crate::catalog::{RESOURCE_TEMPLATES, RESOURCES, resource_name};
use crate::errors::{err_internal, err_not_found, err_params};
use crate::paging::Asked;
use crate::session;
use crate::state::{lock, read_lock};

/// The refusal of a request whose cancel flag was raised while it analyzed
/// another build ([`Analysis::try_compute_with`]).
const OTHER_BUILD_CUT: &str =
    "the request stopped before the other build's analysis was whole, so it was not compared";

/// Another build of the loaded program, analysed for a comparison surface.
#[derive(Debug)]
struct OtherBuild {
    /// The build.
    program: Program,
    /// Its analysis, run with the packs that fit it.
    analysis: Analysis,
    /// Its file name, for the headers.
    label: String,
}

/// A surface that renders one function of the loaded build against the
/// same function in another: `difffn` and `migrate`. Its `Err` refuses a
/// function the loaded build lacks.
type AcrossBuilds = fn(
    &Program,
    &Analysis,
    &Overlay,
    &Program,
    &Analysis,
    &Overlay,
    &str,
    &str,
    &str,
) -> Result<String, String>;

/// The file name of a path, for a readable label; the whole path if it has no
/// final component.
///
/// # Arguments
///
/// * `path` - A file path.
fn file_label(path: &Path) -> String {
    path.file_name().map_or_else(
        || path.display().to_string(),
        |n| n.to_string_lossy().into_owned(),
    )
}

/// Largest text file a resource reads, in bytes: a script, a manifest or
/// a fingerprint sidecar is text an agent wrote or borer did, and a large
/// binary's sidecar runs to tens of megabytes.
pub(crate) const SPEC_FILE_MAX: u64 = 1 << 26;

/// Reads a file a resource names, refusing a device and naming the file in
/// any failure.
///
/// # Arguments
///
/// * `path` - The file, as the URI carried it.
/// * `kind` - What the file is meant to be, for the message.
///
/// # Errors
///
/// When the path is a device, a share or not a regular file, the file is
/// past [`SPEC_FILE_MAX`] bytes, does not read, or is not text.
fn read_spec_file(path: &str, kind: &str) -> Result<String, ErrorData> {
    read_spec_file_max(path, kind, SPEC_FILE_MAX)
}

/// Reads a text file a resource names within `max` bytes.
///
/// # Arguments
///
/// * `path` - The file, as the URI carried it.
/// * `kind` - What the file is meant to be, for the message.
/// * `max` - Largest byte count accepted.
///
/// # Errors
///
/// When `path` is refused or not a regular file, exceeds `max` bytes, fails
/// to read, or is not UTF-8 text.
fn read_spec_file_max(path: &str, kind: &str, max: u64) -> Result<String, ErrorData> {
    let bytes = borer_engine::program::read_regular(Path::new(path), max)
        .map_err(|e| err_params(format!("{e:#}; give a path to {kind}")))?;
    String::from_utf8(bytes).map_err(|_| {
        err_params(format!(
            "{} is not a text file; give a path to {kind}",
            borer_engine::text::short_path(path)
        ))
    })
}

/// Reads a `# borer fingerprint` sidecar within [`SPEC_FILE_MAX`] bytes, or
/// returns `Ok(None)` when `path` names no file or has another header.
///
/// # Arguments
///
/// * `path` - Candidate sidecar or comparison binary path.
///
/// # Errors
///
/// When `path` is unusable, names an existing non-regular file, or opens with
/// `# borer fingerprint` and exceeds [`SPEC_FILE_MAX`] or is not UTF-8.
pub(crate) fn fingerprint_sidecar(path: &Path) -> Result<Option<String>, String> {
    use std::io::Read as _;
    /// Magic prefix opening every fingerprint sidecar.
    const HEAD: &[u8] = b"# borer fingerprint";
    if borer_engine::program::checked_metadata(path)?.is_none() {
        return Ok(None);
    }
    let f = borer_engine::program::open_regular(path, u64::MAX).map_err(|e| format!("{e:#}"))?;
    let shown = borer_engine::text::short_path(&path.to_string_lossy());
    let mut head = Vec::with_capacity(HEAD.len());
    f.take(borer_engine::num::from_usize(HEAD.len()))
        .read_to_end(&mut head)
        .map_err(|e| format!("reading {shown}: {e}"))?;
    if head != HEAD {
        return Ok(None);
    }
    let bytes =
        borer_engine::program::read_regular(path, SPEC_FILE_MAX).map_err(|e| format!("{e:#}"))?;
    String::from_utf8(bytes)
        .map(Some)
        .map_err(|_| format!("{shown} is not a text file"))
}

impl BorerServer {
    /// Loads and analyses another build for a comparison surface.
    ///
    /// # Arguments
    ///
    /// * `path` - Path of the other build.
    ///
    /// No binary loaded is refused first: the other build was loaded and
    /// analysed, which takes minutes on a large one, only to be told then
    /// that there was nothing to compare it with.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the other build does not load, has no
    /// code analysis, or is not the loaded program's architecture, or the
    /// request's cancel flag was raised while the other build was analyzed.
    fn other_build(&self, path: &str) -> Result<OtherBuild, ErrorData> {
        self.require_loaded()?;
        let program = self.load_other(path)?;
        let analysis = Analysis::try_compute_with(&program, self.packs_for(&program).0)
            .ok_or_else(|| err_internal(OTHER_BUILD_CUT))?;
        let label = file_label(&program.path);
        Ok(OtherBuild {
            program,
            analysis,
            label,
        })
    }

    /// Renders one function of the loaded binary against another build.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<function>/<other-path>`: the baseline function by address
    ///   or name, then the other version's file path.
    /// * `template` - The resource's name, for the message when the spec
    ///   lacks a path.
    /// * `render` - The surface.
    ///
    /// # Errors
    ///
    /// When the spec lacks a path, no binary is loaded, the other build
    /// cannot be loaded or analyzed, or the loaded build has no such
    /// function.
    fn across_builds(
        &self,
        spec: &str,
        template: &str,
        render: AcrossBuilds,
    ) -> Result<String, ErrorData> {
        let Some((function, other)) = spec.split_once('/') else {
            return Err(err_params(format!(
                "expected borer://{template}/<function>/<other-path>"
            )));
        };
        let other = self.other_build(other)?;
        self.refusing(Feature::Decompile, |p, a, o| {
            render(
                p,
                a,
                o,
                &other.program,
                &other.analysis,
                &Overlay::default(),
                function,
                &file_label(&p.path),
                &other.label,
            )
        })
    }

    /// Runs a renderer that refuses an argument it cannot answer, inside the
    /// analysis's fault boundary.
    ///
    /// A refusal is the caller's mistake, an address that names nothing or
    /// a directive that does not read, so it reaches the client as an
    /// invalid-params error; returned through [`Self::with_analysis`] it
    /// would read as the server failing, and answered as a `#` line it read
    /// as a success.
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the renderer reads ([`Self::with_analysis`]).
    /// * `render` - The renderer; its `Err` is the refusal's message.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or the renderer refuses;
    /// internal error when the engine does not do `feature` with the
    /// architecture, or the analysis cannot run or faults.
    fn refusing(
        &self,
        feature: Feature,
        render: impl FnOnce(&Program, &Analysis, &Overlay) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        let mut refused = None;
        let out = self.with_analysis(feature, |p, a, o| {
            Ok(render(p, a, o).unwrap_or_else(|why| {
                refused = Some(why);
                String::new()
            }))
        })?;
        refused.map_or(Ok(out), |why| Err(err_params(why)))
    }

    /// One chart series as a table ([`borer_engine::analysis::stats::stats_tsv`]),
    /// a page at a time.
    ///
    /// # Arguments
    ///
    /// The series of the file's bytes answer on any architecture, from an
    /// empty analysis where the code is not discovered; `sizes` refuses
    /// there.
    ///
    /// # Arguments
    ///
    /// * `spec` - The kind and its settings.
    /// * `asked` - The URI with its paging, which the table is paged by.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the spec is refused.
    pub(crate) fn stats_text(&self, spec: &str, asked: &Asked) -> Result<String, ErrorData> {
        /// Most rows one read returns.
        const PAGE: usize = 200;
        let again = asked.again();
        self.with_managed(|p, a| {
            borer_engine::analysis::stats::stats_tsv(p, a, spec, asked.page(&again).window(PAGE))
        })
    }

    /// Compares the loaded binary against another version and reports the diff.
    ///
    /// When `other` is a fingerprint manifest (from `borer://fingerprint`), it
    /// is the prior version and the loaded binary is the new one, so a build
    /// diffs against a saved sidecar without the old binary. Otherwise `other`
    /// is a binary and the loaded binary is the baseline.
    ///
    /// A device name is refused before [`Program::load`] sees it, so the
    /// loader's own refusal is not reached: reading the console here blocked
    /// the server on input that was never coming.
    ///
    /// # Arguments
    ///
    /// * `other` - File path of the other version, binary or manifest.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the other file cannot be loaded or has no
    /// code analysis.
    pub(crate) fn diff_text(&self, other: &str) -> Result<String, ErrorData> {
        self.require_loaded()?;
        if let Some(text) = fingerprint_sidecar(Path::new(other)).map_err(|e| {
            err_params(format!(
                "{e}; give a path to a program or a fingerprint sidecar"
            ))
        })? {
            let old_prints = render::parse_prints(&text);
            let base = file_label(Path::new(other));
            return self.with_analysis(Feature::Discover, |p, a, _| {
                Ok(render::diff_prints_tsv(
                    &old_prints,
                    &render::prints_of(a),
                    &base,
                    &file_label(&p.path),
                ))
            });
        }
        let other = self.other_build(other)?;
        self.with_analysis(Feature::Discover, |p, a, _| {
            Ok(render::diff_tsv(
                a,
                &other.analysis,
                &file_label(&p.path),
                &other.label,
            ))
        })
    }

    /// Shows how one function changed between the loaded binary and another
    /// version, as a diff of the two decompilations.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<function>/<other-path>`: the baseline function by address
    ///   or name, then the other version's file path.
    ///
    /// # Errors
    ///
    /// When the spec lacks a path, no binary is loaded, or the other file
    /// cannot be loaded or analyzed.
    pub(crate) fn diff_function_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.across_builds(spec, "difffn", render::diff_function_tsv)
    }

    /// Carries this project's names to another build.
    ///
    /// # Arguments
    ///
    /// * `other` - Path to the other build.
    ///
    /// # Errors
    ///
    /// When the other build does not load or has no code analysis.
    pub(crate) fn carry_text(&self, other: &str) -> Result<String, ErrorData> {
        let other = self.other_build(other)?;
        self.with_analysis(Feature::Discover, |_, a, o| {
            Ok(render::carry_names_tsv(
                a,
                o,
                &other.analysis,
                &Overlay::default(),
            ))
        })
    }

    /// Migrates one function's field offsets to another build.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<function>/<other-path>`.
    ///
    /// # Errors
    ///
    /// When the spec is malformed or the other build does not load.
    pub(crate) fn migrate_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.across_builds(spec, "migrate", render::migrate_function_tsv)
    }

    /// Lists the packs this session knows and how each fits the loaded
    /// program, the CLI's `packs`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn packs_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Discover, |p, a, _| {
            let mut out = borer::packs::listing(p, &self.packs, borer::packs::auto_enabled());
            out.push_str(&borer_engine::analysis::sigs::pack_names_tsv(&a.pack_names));
            out.push_str(&borer_engine::analysis::libnames::library_names_tsv(
                &a.library_names,
            ));
            out.push_str(&borer_engine::script::pack_scripts_tsv(&a.pack_scripts));
            Ok(out)
        })
    }

    /// Runs a script file against the loaded program in borer's sandbox,
    /// the CLI's `script`: what it printed and the names and comments it
    /// proposes, which are not applied.
    ///
    /// A script that fails answers as the `script` tool answers one: what it
    /// printed and proposed before the error, then a `# script failed:`
    /// line, since the lines before the error say how far it got.
    ///
    /// # Arguments
    ///
    /// * `path` - The script file.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, borer does not disassemble its
    /// architecture, or the path is a device or does not read.
    pub(crate) fn script_text(&self, path: &str) -> Result<String, ErrorData> {
        let code = read_spec_file(path, "a Rhai script")?;
        let (program, a, o) = self.script_snapshot()?;
        let run = borer_engine::script::run_with(program, a, Arc::new(o), &code, &[], None);
        Ok(borer_engine::script::run_tsv(&run))
    }

    /// Lists pseudo-C lines program-wide containing `text`, or matching it
    /// when written `re:<expression>`, from the decompilation index, building
    /// the index on first use.
    ///
    /// # Arguments
    ///
    /// * `text` - The text a line must contain, as the URI carried it
    ///   (decoded once at [`super::BorerServer::read_uri`]).
    /// * `asked` - The URI as asked, for the page it asks for.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the text is empty, the expression does not
    /// parse, or the index cannot be written.
    pub(crate) fn grep_text(&self, text: &str, asked: &Asked) -> Result<String, ErrorData> {
        /// Most matching lines one read returns; the headers enclosing them
        /// come beside them.
        const PAGE: usize = 200;
        if borer::index::Matcher::parse(text)
            .map_err(err_params)?
            .matches_nothing()
        {
            return Err(err_params(
                "grep needs a non-empty text; an empty one would match nothing",
            ));
        }
        let again = asked.again();
        self.with_analysis(Feature::Decompile, |p, a, o| {
            let (index, _, _) = borer::index::load_or_build(p, a)?;
            borer::index::grep_tsv(&index, a, o, text, "", asked.page(&again).window(PAGE))
        })
    }

    /// Reports the decompilation index of the loaded binary, building it
    /// only when the cache holds none for this program and this engine.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the index had to be built and cannot be
    /// written.
    pub(crate) fn index_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, _| {
            let (index, path, built) = borer::index::load_or_build(p, a)?;
            Ok(format!(
                "# {} {} functions, {} bytes of pseudo-C -> {}\n",
                if built { "indexed" } else { "already indexed" },
                index.functions.len(),
                index.text_bytes(),
                path.display()
            ))
        })
    }

    /// Measures the speed of the hot queries on the loaded binary: an
    /// anchored AOB scan, the string walks, and an indexed grep when the
    /// cache holds the index.
    ///
    /// Each row names the op, what it answered, how long the fastest of
    /// its runs took, and the throughput where bytes name one: the numbers
    /// an agent compares against the machine it sits on. Timings are
    /// wall-clock and differ run to run; the rows and counts never do.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn bench_text(&self) -> Result<String, ErrorData> {
        self.with_program(|p| {
            /// Runs `op` `runs` times, returning the fastest elapsed.
            #[expect(
                clippy::disallowed_methods,
                reason = "the bench resource is a benchmark: wall time is its answer, never another's"
            )]
            fn fastest(runs: usize, op: impl Fn()) -> std::time::Duration {
                (0..runs)
                    .map(|_| {
                        let t = std::time::Instant::now();
                        op();
                        t.elapsed()
                    })
                    .min()
                    .unwrap_or_default()
            }
            let mut out = String::from("# bench: op rows elapsed throughput\n");
            let va = p.entry.unwrap_or(p.image_base);
            let head: Option<[u8; 4]> = p
                .read_va_upto(va, 4)
                .and_then(|b| b.first_chunk::<4>().copied())
                .or_else(|| p.bytes.as_slice().first_chunk::<4>().copied());
            if let Some([a, b, _, _]) = head {
                let pattern = [Some(a), Some(b), None, None];
                let scan = fastest(3, || {
                    let _ = borer_engine::search::find_bytes(p, &pattern, 0);
                });
                let total = borer_engine::search::find_bytes(p, &pattern, 0).total;
                let gb =
                    borer_engine::num::as_f64(u64::try_from(p.bytes.len()).unwrap_or(u64::MAX))
                        / scan.as_secs_f64()
                        / 1e9;
                let _ = writeln!(
                    out,
                    "aob {a:02x} {b:02x} ?? ??\t{total}\t{scan:.2?}\t{gb:.1} GB/s"
                );
            }
            let walk = fastest(3, || {
                let _ = borer_engine::strings::find_ascii_spans(&p.bytes, 5);
            });
            let spans = borer_engine::strings::find_ascii_spans(&p.bytes, 5);
            let gb = borer_engine::num::as_f64(u64::try_from(p.bytes.len()).unwrap_or(u64::MAX))
                / walk.as_secs_f64()
                / 1e9;
            let _ = writeln!(out, "strings\t{}\t{walk:.2?}\t{gb:.1} GB/s", spans.len());
            let e = Needle::new("e");
            let needle = Some(&e);
            let filtered = spans
                .iter()
                .filter(|&s| row_matches(p, &StringRow::Span(*s), needle));
            let scan = fastest(3, || {
                let n = spans
                    .iter()
                    .filter(|&s| row_matches(p, &StringRow::Span(*s), needle))
                    .count();
                let _ = n;
            });
            let rows = filtered.count();
            let _ = writeln!(out, "strings filter=e\t{rows}\t{scan:.2?}\t0 allocs");
            let analysis = read_lock(&self.analysis).as_ref().map(Arc::clone);
            let cached = analysis
                .as_ref()
                .and_then(|a| borer::index::load_cached(p, &a.packs));
            if let Some((index, _)) = cached {
                let matcher = borer::index::Matcher::parse("return")?;
                let scan = fastest(3, || {
                    let _ = borer::index::grep(&index, &matcher, "");
                });
                let lines = borer::index::grep(&index, &matcher, "").len();
                let mb = borer_engine::num::as_f64(
                    u64::try_from(index.text_bytes()).unwrap_or(u64::MAX),
                ) / scan.as_secs_f64()
                    / 1e6;
                let _ = writeln!(
                    out,
                    "grep return\t{lines}\t{scan:.2?}\t{mb:.0} MB/s over {} functions",
                    index.functions.len()
                );
            } else {
                let _ = writeln!(
                    out,
                    "grep -\t-\t-\tquery borer://index once to build the index first"
                );
            }
            Ok(out)
        })
    }

    /// Compares a snapshot file of an earlier build with the loaded binary.
    ///
    /// # Arguments
    ///
    /// * `path` - The snapshot, as the URI carried it (decoded once at
    ///   [`super::BorerServer::read_uri`]).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the file cannot be read or is not a
    /// snapshot.
    pub(crate) fn changes_text(&self, path: &str) -> Result<String, ErrorData> {
        let text = read_spec_file(
            path,
            "a snapshot file (`borer snapshot <binary> <out>` writes one)",
        )?;
        let before = borer_engine::analysis::snapshot::read(&text).map_err(err_params)?;
        self.with_analysis(Feature::Decompile, |p, a, o| {
            let after = borer_engine::analysis::snapshot::facts(p, a, o);
            Ok(borer_engine::analysis::snapshot::changes_tsv(
                &before, &after,
            ))
        })
    }

    /// Judges every anchor in a manifest file against the loaded binary.
    ///
    /// A manifest pins hundreds of facts, and each is derived again by a
    /// walk of the analysis, so one read takes a manifest of at most
    /// `MANIFEST_MAX` bytes and `ANCHORS_MAX` anchors and lists at most
    /// `PAGE` rows; the CLI's `anchors` judges a bigger one.
    ///
    /// # Arguments
    ///
    /// * `path` - The manifest, as the URI carried it (decoded once at
    ///   [`super::BorerServer::read_uri`]).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the file cannot be read or is too big, a
    /// line is not an anchor, or there are too many anchors.
    pub(crate) fn anchors_text(&self, path: &str) -> Result<String, ErrorData> {
        /// Largest manifest one read takes, in bytes.
        const MANIFEST_MAX: u64 = 1 << 20;
        /// Most anchors one read judges.
        const ANCHORS_MAX: usize = 5000;
        /// Most rows one read lists.
        const PAGE: usize = 500;
        let short = borer_engine::text::short_path(path);
        let text = read_spec_file_max(
            path,
            "an anchors manifest (field, vconst, function, encode and decode lines); split a larger manifest or judge it with the CLI's anchors",
            MANIFEST_MAX,
        )?;
        let anchors = borer_engine::analysis::anchors::parse_manifest(&text).map_err(err_params)?;
        if anchors.len() > ANCHORS_MAX {
            return Err(err_params(format!(
                "{short} has {} anchors, past the {ANCHORS_MAX} one read judges; split the manifest or judge it with the CLI's anchors",
                anchors.len()
            )));
        }
        self.with_analysis(Feature::Decompile, |p, a, o| {
            let (table, _) = borer_engine::analysis::anchors::verify_tsv(p, a, o, &anchors, PAGE);
            Ok(table)
        })
    }

    /// Renders the session ledger ([`crate::session::Ledger`]): what is
    /// loaded, the overlay and whether it is saved, the changes the
    /// session applied and the requests it answered.
    ///
    /// It answers with nothing loaded too, since where a session stands is
    /// worth knowing before its first load.
    pub(crate) fn session_text(&self) -> String {
        let loaded = self.loaded().map(|p| {
            let file = p.path.file_name().map_or_else(
                || p.path.display().to_string(),
                |n| n.to_string_lossy().into_owned(),
            );
            let functions = read_lock(&self.analysis).as_ref().map_or_else(
                || "not analyzed yet".to_owned(),
                |a| format!("{} functions", a.functions.len()),
            );
            let packs: Vec<String> = read_lock(&self.program_packs)
                .packs
                .iter()
                .map(|pack| pack.name.clone())
                .collect();
            format!(
                "{file} ({} {}), {functions}; packs: {}",
                p.format.name(),
                p.arch.name(),
                if packs.is_empty() {
                    "none".to_owned()
                } else {
                    packs.join(", ")
                }
            )
        });
        let (counts, fingerprint) = {
            let o = read_lock(&self.overlay);
            let open = o
                .comments
                .values()
                .filter(|c| borer_engine::analysis::edit::open_question(c).is_some())
                .count();
            let fields: usize = o.fields.values().map(std::collections::BTreeMap::len).sum();
            let empty = o.names.is_empty()
                && o.comments.is_empty()
                && o.types.is_empty()
                && o.applied.is_empty()
                && o.prototypes.is_empty()
                && o.vars.is_empty()
                && fields == 0;
            let stated = match fields {
                0 => String::new(),
                n => format!(", {n} stated fields"),
            };
            (
                format!(
                    "{} names, {} comments ({open} open questions), {} types, {} typed globals, {} prototypes{stated}",
                    o.names.len(),
                    o.comments.len(),
                    o.types.len(),
                    o.applied.len(),
                    o.prototypes.len()
                ),
                (!empty).then(|| o.fingerprint()),
            )
        };
        let recall = lock(&self.recall);
        lock(&self.ledger).render(loaded.as_deref(), (&counts, fingerprint), |key| {
            recall.holds(key)
        })
    }

    /// Answers `borer://session/evidence/<id>`, or how to read it when the
    /// URI stops at `evidence`.
    ///
    /// The kept answer comes back as it was sent, its own evidence line
    /// included; an id past the cap is answered with the notice that says
    /// so, since the text is gone but the session still lists the request
    /// that minted it.
    ///
    /// # Arguments
    ///
    /// * `spec` - The URI's argument after `borer://session/`:
    ///   `evidence/<id>`, or `evidence` alone for the grammar.
    ///
    /// # Errors
    ///
    /// When the id is not one a `# evidence:` line carried, or the spec
    /// names nothing under `borer://session`.
    pub(crate) fn session_evidence(&self, spec: &str) -> Result<String, ErrorData> {
        let Some(id) = spec.strip_prefix("evidence/").filter(|id| !id.is_empty()) else {
            return if spec == "evidence" {
                self.help_text("session")
            } else {
                Err(unknown_resource(&format!("borer://session/{spec}")))
            };
        };
        match lock(&self.ledger).evidence(id) {
            Ok(session::Answer::Kept(text)) => Ok(text),
            Ok(session::Answer::LetGo) => Ok(format!(
                "# evidence {id} was let go past the {} the session keeps; borer://session lists the requests it answered\n",
                session::EVIDENCE_KEPT
            )),
            Err(why) => Err(err_params(why)),
        }
    }

    /// Answers a resource the engine answers on its own
    /// ([`borer_engine::answer::read`]), with what it reads prepared.
    ///
    /// Everything is decided under the program's lock, so no load in
    /// between pairs one program with another's analysis. A [`Need::Code`]
    /// resource reads the analysis, and the engine refuses an architecture
    /// without the stage; a [`Need::Best`] one reads it where the program
    /// does the stage, else the empty analysis held for the program, which
    /// keeps a `.NET` listing's index from one read to the next; a
    /// [`Need::File`] one reads the file alone, its facts kept in the
    /// analysis's memo once one is held.
    ///
    /// # Arguments
    ///
    /// * `need` - What the resource reads ([`borer_engine::answer::need`]).
    /// * `asked` - The URI with its suffixes read off, for the page.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or the engine refuses the
    /// argument or the architecture; internal error when the analysis
    /// faults.
    pub(crate) fn engine_answer(&self, need: Need, asked: &Asked) -> Result<String, ErrorData> {
        let again = asked.again();
        let page = asked.page(&again);
        self.with_program(|p| {
            let analysis = match need {
                Need::Code(stage) | Need::Best(stage) if p.refuses(stage).is_none() => {
                    Some(self.ensure_analysis()?)
                }
                Need::Code(_) => None,
                Need::Best(_) => Some(self.empty_analysis()),
                Need::File => read_lock(&self.analysis).clone(),
            };
            let o = self.overlay();
            borer_engine::answer::read(p, analysis.as_deref(), &o, &asked.core, page)
                .unwrap_or_else(|| {
                    Err(format!(
                        "the engine does not answer {}",
                        borer_engine::text::one_line(&asked.core)
                    ))
                })
        })
    }
}

/// Most resources the refusal of an unknown URI names.
const NEAREST_RESOURCES: usize = 3;

/// Longest description `borer://help` gives a resource, in characters.
const SUMMARY_MAX: usize = 72;

/// Where the refusal of an unknown URI sends the reader for the rest.
const EVERY_RESOURCE: &str = "borer://help lists every resource";

impl BorerServer {
    /// Answers how to read one resource.
    ///
    /// The answer is its URI and what it answers, and for a template an
    /// example built from the loaded binary ([`example`]). A template read
    /// without its argument answers this, so the grammar a description
    /// holds reaches an agent whose host only has the `query` tool.
    ///
    /// # Arguments
    ///
    /// * `name` - The resource's name (`emulate`).
    ///
    /// # Errors
    ///
    /// Resource-not-found for a name no resource has, naming the nearest.
    pub(crate) fn help_text(&self, name: &str) -> Result<String, ErrorData> {
        let program = self.loaded();
        let mut out = String::new();
        for &(uri, what) in RESOURCES.iter().filter(|r| resource_name(r.0) == name) {
            let _ = writeln!(out, "# {uri}\n{what}");
        }
        for &(uri, what, shown) in RESOURCE_TEMPLATES
            .iter()
            .filter(|t| resource_name(t.0) == name)
        {
            let _ = writeln!(
                out,
                "# {uri}\n{what}\n# example: {}",
                example(shown, program.as_deref())
            );
        }
        if out.is_empty() {
            return Err(unknown_name(&format!("borer://help/{name}"), name));
        }
        Ok(out)
    }
}

/// Answers a prompt's text as a resource, for an agent whose host offers
/// prompts only to its user ([`crate::playbooks`]).
///
/// # Arguments
///
/// * `spec` - `<prompt>[/<argument>]`: the argument fills what the text
///   leaves open (`find_check/serial`).
///
/// # Errors
///
/// Resource-not-found for a name no prompt has, naming the playbooks.
pub(crate) fn playbook_text(spec: &str) -> Result<String, ErrorData> {
    let (name, argument) = spec
        .split_once('/')
        .map_or((spec, None), |(n, a)| (n, Some(a)));
    crate::playbooks::playbook(name, argument)
        .map(|text| text + "\n")
        .ok_or_else(|| {
            let names: Vec<&str> = crate::playbooks::PLAYBOOKS.iter().map(|p| p.0).collect();
            err_not_found(format!(
                "no playbook {}; the playbooks are {}",
                borer_engine::text::quoted(name),
                names.join(", ")
            ))
        })
}

/// Fills a template's example from the loaded binary.
///
/// `{entry}` becomes its entry point (else its first section's address)
/// and `{path}` its file, which a comparison against itself reads.
///
/// # Arguments
///
/// * `shown` - The example as [`RESOURCE_TEMPLATES`] writes it.
/// * `program` - The loaded binary; `None` leaves `<entry>` and `<path>`
///   for the reader to fill.
fn example(shown: &str, program: Option<&Program>) -> String {
    let entry = program
        .and_then(|p| p.entry.or_else(|| p.sections.first().map(|s| s.va.0)))
        .map_or_else(|| "<entry>".to_owned(), |va| format!("{va:#x}"));
    let path = program
        .map(|p| p.path.display().to_string().replace('\\', "/"))
        .filter(|path| !path.is_empty())
        .unwrap_or_else(|| "<path>".to_owned());
    shown.replace("{entry}", &entry).replace("{path}", &path)
}

/// Lists every resource with what it answers, one line each, a template's
/// with an example URI built from the loaded binary ([`example`]).
///
/// This is the `borer://help` answer, the whole list for an agent whose
/// host lists no resources, and what a script's `help("query")` returns.
/// Each description is cut to its first sentence and [`SUMMARY_MAX`]
/// characters; `borer://help/<name>` gives the whole of one.
///
/// # Arguments
///
/// * `program` - The loaded binary, for the examples; `None` leaves their
///   `<entry>` and `<path>` for the reader.
pub(crate) fn help_index(program: Option<&Program>) -> String {
    let mut out = format!(
        "# {} resources ({} fixed, {} templates); a template read without its argument, or borer://help/<name>, gives its grammar and an example\n",
        RESOURCES.len() + RESOURCE_TEMPLATES.len(),
        RESOURCES.len(),
        RESOURCE_TEMPLATES.len()
    );
    for &(uri, what) in RESOURCES {
        let _ = writeln!(out, "{uri}\t{}", summary(what));
    }
    for &(uri, what, shown) in RESOURCE_TEMPLATES {
        let _ = writeln!(
            out,
            "{uri}\t{}\te.g. {}",
            summary(what),
            example(shown, program)
        );
    }
    out
}

/// The first sentence of a description, cut at a word to at most
/// [`SUMMARY_MAX`] characters with `...` where it was cut.
///
/// # Arguments
///
/// * `description` - A description from the resource tables.
fn summary(description: &str) -> String {
    let end = [". ", "; "]
        .iter()
        .filter_map(|sep| description.find(sep))
        .min()
        .unwrap_or(description.len());
    let sentence = description.get(..end).unwrap_or(description);
    if sentence.chars().count() <= SUMMARY_MAX {
        return sentence.to_owned();
    }
    let mut cut = String::new();
    for word in sentence.split(' ') {
        if cut.chars().count() + word.chars().count() + 1 > SUMMARY_MAX {
            break;
        }
        if !cut.is_empty() {
            cut.push(' ');
        }
        cut.push_str(word);
    }
    cut.push_str("...");
    cut
}

/// Refuses a URI no resource answers, with the few resources nearest it.
///
/// The refusal says where the rest are listed; a fixed resource given an
/// argument is told it takes none. It listed every resource, about 2 KB a
/// miss, and taught names without saying which was meant.
///
/// # Arguments
///
/// * `uri` - The URI as asked, its suffixes taken off.
///
/// # Returns
///
/// A resource-not-found error.
pub(crate) fn unknown_resource(uri: &str) -> ErrorData {
    let Some(path) = uri.strip_prefix("borer://") else {
        return err_not_found(format!(
            "unknown resource {}; a resource's URI starts with borer://; {EVERY_RESOURCE}",
            borer_engine::text::one_line(uri)
        ));
    };
    let (name, argument) = path
        .split_once('/')
        .map_or((path, false), |(n, _)| (n, true));
    let template = RESOURCE_TEMPLATES
        .iter()
        .any(|t| resource_name(t.0) == name);
    if argument
        && !template
        && let Some(&(fixed, _)) = RESOURCES.iter().find(|r| resource_name(r.0) == name)
    {
        return err_not_found(format!("{fixed} takes no argument; read {fixed}"));
    }
    unknown_name(uri, name)
}

/// Refuses a resource name nothing lists, with the nearest names' URIs.
///
/// # Arguments
///
/// * `uri` - The URI as asked, for the message.
/// * `name` - The name in it that nothing lists.
///
/// # Returns
///
/// A resource-not-found error.
fn unknown_name(uri: &str, name: &str) -> ErrorData {
    let names = RESOURCES
        .iter()
        .map(|r| resource_name(r.0))
        .chain(RESOURCE_TEMPLATES.iter().map(|t| resource_name(t.0)));
    let near: Vec<&str> = borer_engine::text::nearest(name, names, NEAREST_RESOURCES)
        .into_iter()
        .filter_map(|n| {
            RESOURCES
                .iter()
                .map(|r| r.0)
                .chain(RESOURCE_TEMPLATES.iter().map(|t| t.0))
                .find(|uri| resource_name(uri) == n)
        })
        .collect();
    let near = if near.is_empty() {
        "no resource is near it".to_owned()
    } else {
        format!("nearest: {}", near.join(", "))
    };
    err_not_found(format!(
        "unknown resource {}; {near}; {EVERY_RESOURCE}",
        borer_engine::text::one_line(uri)
    ))
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, RwLock};

    use borer_engine::program::{Arch, Program, Section};
    use rmcp::ErrorData;
    use rmcp::model::ErrorCode;

    use borer_engine::answer::ABOUT_NEEDS_A_NAME;

    use super::BorerServer;

    /// A layout's plan read while another request edits the overlay is no
    /// change of the session: only a read told to apply can be one.
    ///
    /// A read tells whether it applied by the overlay's fingerprint before
    /// and after, which an edit landing beside a plan moves as well. A
    /// thread rewrites a comment for as long as the plans are read, so
    /// with nothing keeping a plan apart from an apply, one of them meets
    /// an edit and is listed.
    ///
    /// # Panics
    ///
    /// When a plan does not read, or is listed among the session's changes.
    #[test]
    fn a_layout_plan_read_beside_an_edit_is_no_change() {
        use std::sync::atomic::{AtomicBool, Ordering};
        let server = crate::testing::code_server(
            Arch::X86_64,
            &[
                0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
                0xc3, // ASM: ret
            ],
        );
        let done = AtomicBool::new(false);
        let plans: Vec<Result<String, ErrorData>> = std::thread::scope(|s| {
            s.spawn(|| {
                let mut n = 0u64;
                while !done.load(Ordering::Relaxed) {
                    crate::state::write_lock(&server.overlay)
                        .comments
                        .insert(0x1000, n.to_string());
                    n = n.wrapping_add(1);
                    std::thread::yield_now();
                }
            });
            let plans = (0..400)
                .map(|_| server.resource_text("borer://layout/0x1000,apply=Rec"))
                .collect();
            done.store(true, Ordering::Relaxed);
            plans
        });
        assert!(plans.iter().all(Result::is_ok), "{plans:?}");
        let session = server.session_text();
        assert!(session.contains("\n# 0 changes this session"), "{session}");
    }

    /// A field offset most code touches lists one page of 200 sites and
    /// says where the next starts.
    ///
    /// # Panics
    ///
    /// When the page holds more than 200 rows or no next page is named.
    #[test]
    fn fieldrefs_pages_at_200_sites() {
        let mut bytes: Vec<u8> = std::iter::repeat_n([0x48u8, 0x8b, 0x41, 0x10], 250)
            .flatten()
            .collect();
        bytes.push(0xc3);
        bytes.resize(0x1000, 0xcc);
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let program = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = BorerServer {
            program: Arc::new(RwLock::new(Some(Arc::new(program)))),
            ..BorerServer::default()
        };
        let out = server
            .resource_text("borer://fieldrefs/0x10")
            .expect("lists the sites");
        assert!(
            out.starts_with("# 250 sites touch [reg+0x10], showing 200 from 0\n"),
            "{out}"
        );
        assert!(out.contains("offset=200"), "{out}");
    }

    /// Reading a resource leaves the names, comments and types the session
    /// holds as they were, and the program it has loaded.
    ///
    /// Every fixed resource, every template's example and a layout's plan
    /// are read twice, as `resources/read` and `query` read them; a second
    /// read answers or refuses as the first did. The tools' hints were
    /// held against the effects they state, never against what a read does.
    ///
    /// # Panics
    ///
    /// When a read changes the overlay, the loaded program or the ledger's
    /// changes, or a second read does not go the first one's way.
    #[test]
    fn reading_a_resource_leaves_the_session_as_it_was() {
        let server = crate::testing::code_server(
            Arch::X86_64,
            &[
                0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
                0xc3, // ASM: ret
            ],
        );
        crate::state::write_lock(&server.overlay)
            .names
            .insert(0x1000, "probe".to_owned());
        let program = server.loaded().expect("a program is loaded");
        let before = server.overlay_plain().fingerprint();
        let uris = super::RESOURCES
            .iter()
            .map(|r| r.0.to_owned())
            .chain(
                super::RESOURCE_TEMPLATES
                    .iter()
                    .map(|t| super::example(t.2, Some(&program))),
            )
            .chain(
                ["", ",dry_run=false"].map(|told| format!("borer://layout/0x1000,apply=Rec{told}")),
            );
        for uri in uris {
            let (first, second) = (server.read_uri(&uri), server.read_uri(&uri));
            assert_eq!(first.is_ok(), second.is_ok(), "{uri}");
            assert_eq!(server.overlay_plain().fingerprint(), before, "{uri}");
            assert!(
                server
                    .loaded()
                    .is_some_and(|now| Arc::ptr_eq(&now, &program)),
                "{uri}"
            );
        }
        let session = server.session_text();
        assert!(session.contains("\n# 0 changes this session"), "{session}");
    }

    /// A binary given where a snapshot or a manifest goes is refused as not
    /// text, with what the file should be, where the error was the reader's
    /// `stream did not contain valid UTF-8`.
    ///
    /// # Panics
    ///
    /// When the binary reads, or the refusal does not say what to give.
    #[test]
    fn a_binary_given_for_a_text_file_says_what_to_give() {
        let binary =
            std::env::temp_dir().join(format!("borer-not-text-{}.bin", std::process::id()));
        std::fs::write(&binary, [0x4d, 0x5a, 0x90, 0x00, 0xff, 0xfe, 0x00, 0xc3]).expect("write");
        let path = binary.to_string_lossy();
        let refused = super::read_spec_file(&path, "an anchors manifest").unwrap_err();
        std::fs::remove_file(&binary).ok();
        assert!(
            refused
                .message
                .ends_with("is not a text file; give a path to an anchors manifest"),
            "{}",
            refused.message
        );
    }

    /// A resource whose argument names nothing, or is empty where one is
    /// needed, answers an invalid-params error carrying the renderer's
    /// message, where it answered a `#` line a client read as a success.
    ///
    /// # Panics
    ///
    /// When a refusal answers, is another kind of error, or says something
    /// else.
    #[test]
    fn an_argument_naming_nothing_is_an_invalid_params_error() {
        /// Bytes in the one section.
        const PAGE: usize = 0x1000;
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let program = Program::raw(vec![0xc3; PAGE], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = BorerServer {
            program: Arc::new(RwLock::new(Some(Arc::new(program)))),
            ..BorerServer::default()
        };
        let cases: [(&str, &str, &str); 16] = [
            ("why", "nowhere", "cannot resolve nowhere"),
            ("taint", "nowhere", "cannot resolve nowhere"),
            ("layout", "nowhere", "cannot resolve nowhere"),
            ("solve", "nowhere", "cannot resolve nowhere"),
            ("emulate", "nowhere", "cannot resolve nowhere"),
            ("emulate", "0x1", "nothing is mapped at 0x1;"),
            ("emulate", "0x1000,steps=abc", "bad step count in steps=abc"),
            ("run", "nowhere/1", "cannot resolve nowhere"),
            (
                "run",
                "0x1000,steps=abc/1",
                "cannot read steps=abc; use steps=N",
            ),
            ("devirt", "nowhere", "no function nowhere"),
            ("unpack", "0x1000,budget=abc", "bad budget in budget=abc"),
            ("oracle", "nowhere", "no discovered function at 'nowhere'"),
            ("flat", "nowhere", "cannot resolve nowhere"),
            ("vm", "nowhere", "cannot resolve nowhere"),
            ("grep", "", "grep needs a non-empty text"),
            ("about", "", ABOUT_NEEDS_A_NAME),
        ];
        for (resource, arg, message) in cases {
            let err = server
                .resource_text(&format!("borer://{resource}/{arg}"))
                .expect_err(resource);
            assert_eq!(
                err.code,
                ErrorCode::INVALID_PARAMS,
                "{resource}/{arg}: {err:?}"
            );
            assert!(
                err.message.starts_with(message),
                "{resource}/{arg}: {}",
                err.message
            );
        }
    }

    /// `diff` refuses a session with no binary before it probes `other`
    /// for a fingerprint sidecar, and a path that names nothing goes on to
    /// the binary load rather than failing as a sidecar.
    ///
    /// The probe ran first, so with nothing loaded a share was refused as a
    /// sidecar path instead of answering that no binary was loaded.
    ///
    /// # Panics
    ///
    /// When either refusal differs.
    #[test]
    fn diff_refuses_no_binary_before_its_sidecar_probe() {
        let share = r"\\host.invalid\s\x";
        let e = BorerServer::default()
            .diff_text(share)
            .expect_err("nothing is loaded");
        assert_eq!(e.message, crate::state::NO_BINARY);
        let server = crate::testing::code_server(Arch::X86_64, &[0xc3]);
        let e = server
            .diff_text("C:/borer-no-such-dir/other.exe")
            .expect_err("no such file");
        assert!(e.message.starts_with("load failed: "), "{}", e.message);
        assert!(!e.message.contains("fingerprint sidecar"), "{}", e.message);
    }

    /// The comparison resources refuse a session with no binary before
    /// they load the other build, and `exportpack` refuses a part after the
    /// name that is not `all`.
    ///
    /// # Panics
    ///
    /// When a refusal differs.
    #[test]
    fn resources_refuse_what_they_would_drop_or_waste() {
        let server = BorerServer::default();
        let nowhere = "C:/borer-no-such-dir/other.exe";
        for refused in [
            server.diff_text(nowhere),
            server.carry_text(nowhere),
            server.diff_function_text(&format!("f/{nowhere}")),
            server.migrate_text(&format!("f/{nowhere}")),
        ] {
            let e = refused.expect_err("nothing is loaded");
            assert_eq!(e.message, crate::state::NO_BINARY);
        }
        let e = server
            .resource_text("borer://exportpack/x,y")
            .expect_err("not all");
        assert_eq!(e.code, ErrorCode::INVALID_PARAMS);
        assert_eq!(
            e.message,
            "after the pack name comes ,all or nothing, not 'y'"
        );
    }

    /// A resource argument is decoded once, at the URI boundary.
    ///
    /// The handlers decoded it a second time, so a `%25` in a name, the
    /// escape of a literal `%`, reached the lookup as the character behind
    /// it: the agent asked about `x%2541` and was answered about `xA`.
    ///
    /// # Panics
    ///
    /// When the name reaches the lookup decoded a second time.
    #[test]
    fn a_resource_argument_is_decoded_once() {
        /// Bytes in the one section.
        const PAGE: usize = 0x1000;
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let program = Program::raw(vec![0xc3; PAGE], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = BorerServer {
            program: Arc::new(RwLock::new(Some(Arc::new(program)))),
            ..BorerServer::default()
        };
        let out = server
            .resource_text("borer://about/x%252541")
            .expect("about answers");
        assert!(out.contains("'x%2541'"), "{out}");
    }

    /// Every resource the engine answers reads the same through the server
    /// as from the engine, refusals included, and a script with no front
    /// end reads what the server answers.
    ///
    /// Only the `# since` and `# evidence` lines the server adds differ: the
    /// server holds no answer of its own for them, so a script or the app
    /// reading the engine shows what an agent reads. Each URI is a fixed
    /// resource or a template's example, read on a small function and on
    /// a program whose architecture borer does not disassemble, and every
    /// resource the engine answers is among them.
    ///
    /// # Panics
    ///
    /// When an answer or a refusal differs, or a resource the engine
    /// answers is reached by no URI.
    #[test]
    fn the_server_answers_what_the_engine_answers() {
        let code = [
            0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
            0xc3, // ASM: ret
        ];
        let mut reached = std::collections::BTreeSet::new();
        for arch in [Arch::X86_64, Arch::Unknown] {
            reached.extend(engine_answers_agree(&crate::testing::code_server(
                arch, &code,
            )));
        }
        for name in borer_engine::answer::names() {
            assert!(reached.contains(name), "no URI reaches borer://{name}");
        }
    }

    /// Reads every fixed resource and template example the engine answers
    /// through the server, the engine and a script with no front end, and
    /// holds them to one text.
    ///
    /// # Arguments
    ///
    /// * `server` - A server with a program loaded.
    ///
    /// # Returns
    ///
    /// The names of the resources read.
    ///
    /// # Panics
    ///
    /// When two of them differ.
    fn engine_answers_agree(server: &BorerServer) -> Vec<String> {
        let program = server.loaded().expect("a program is loaded");
        let analysis = server.ensure_analysis().ok();
        let overlay = server.overlay();
        let mark = |text: &str| {
            text.lines()
                .filter(|l| {
                    !["# since=", "%% since=", "# evidence:", "%% evidence:"]
                        .iter()
                        .any(|m| l.starts_with(m))
                })
                .collect::<Vec<_>>()
                .join("\n")
        };
        let uris = super::RESOURCES.iter().map(|r| r.0.to_owned()).chain(
            super::RESOURCE_TEMPLATES
                .iter()
                .map(|t| super::example(t.2, Some(&program))),
        );
        let mut reached = Vec::new();
        for uri in uris {
            let Some((name, arg)) = borer_engine::answer::split(&uri) else {
                continue;
            };
            if borer_engine::answer::need(name, arg.as_deref()).is_none() {
                continue;
            }
            reached.push(name.to_owned());
            let page = borer_engine::answer::Page::whole(&uri);
            let engine =
                borer_engine::answer::read(&program, analysis.as_deref(), &overlay, &uri, page)
                    .expect("the engine answers it")
                    .map(|text| mark(&text));
            let served = server
                .read_uri(&uri)
                .map(|(_, text)| mark(&text))
                .map_err(|e| e.message.into_owned());
            assert_eq!(served, engine, "{uri}");
            if let Some(a) = &analysis {
                let ran = borer_engine::script::run_with(
                    Arc::clone(&program),
                    Arc::clone(a),
                    Arc::new(overlay.clone()),
                    &format!(r#"print(query("{uri}"));"#),
                    &[],
                    None,
                );
                match &served {
                    Ok(text) => assert_eq!(ran.output.join("\n"), *text, "{uri}"),
                    Err(_) => assert!(ran.error.is_some(), "{uri}"),
                }
            }
        }
        reached
    }

    /// A program whose architecture borer does not disassemble answers its
    /// triage from the file alone and refuses its fingerprint, and every
    /// `.NET` listing of it reads the one empty analysis held for it.
    ///
    /// # Panics
    ///
    /// When the triage differs from the file's, the fingerprint answers, or
    /// a second listing reads another analysis.
    #[test]
    fn a_program_without_code_analysis_reads_the_file_alone() {
        let server = crate::testing::code_server(Arch::Unknown, &[0xc3; 0x10]);
        let program = server.loaded().expect("a program is loaded");
        let triage = server
            .resource_text("borer://triage")
            .expect("triage answers");
        assert_eq!(
            triage,
            borer_engine::analysis::render::file_triage_tsv(&program)
        );
        assert!(server.resource_text("borer://fingerprint").is_err());
        let held = || {
            crate::state::read_lock(&server.no_code)
                .as_ref()
                .map(|(_, a)| Arc::clone(a))
                .expect("an empty analysis is held")
        };
        let first = server.resource_text("borer://clr/methods");
        let before = held();
        let second = server.resource_text("borer://clr/methods");
        assert_eq!(first.is_ok(), second.is_ok());
        assert!(Arc::ptr_eq(&before, &held()));
    }
}
