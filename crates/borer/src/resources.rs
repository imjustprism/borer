//! The handlers behind the `borer://` resource templates.
//!
//! One method per template, each answering in the same table conventions as
//! the tools; `read_resource` in `main.rs` parses the URI and dispatches here.

use std::path::Path;
use std::sync::Arc;

use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::program::Program;
use rmcp::ErrorData;

use super::{BorerServer, err_params, parse_field_offset};

/// Most rows one listing keyed by a vtable slot returns.
const SLOT_PAGE: usize = 2000;

/// The refusal of an `about` given no name, the resource's and the CLI's.
pub(crate) const ABOUT_NEEDS_A_NAME: &str =
    "about needs a name: an attribute, a class, or a function";

/// A listing keyed by a vtable slot: `<slot>[,<class-filter>]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SlotSpec<'a> {
    /// The zero-based vtable index.
    slot: usize,
    /// A case-insensitive substring of the class name, empty for every class.
    filter: &'a str,
}

impl<'a> SlotSpec<'a> {
    /// Reads a spec as the URI carries it.
    ///
    /// # Arguments
    ///
    /// * `spec` - The URI argument.
    ///
    /// # Errors
    ///
    /// When the slot is not a number.
    fn parse(spec: &'a str) -> Result<SlotSpec<'a>, ErrorData> {
        let (slot_text, filter) = spec.split_once(',').unwrap_or((spec, ""));
        let slot = slot_text.trim().parse().map_err(|_| {
            err_params(format!(
                "bad slot {}: a zero-based index",
                borer_engine::text::quoted(slot_text)
            ))
        })?;
        Ok(SlotSpec {
            slot,
            filter: filter.trim(),
        })
    }
}

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
/// When the path is a device or the file does not read.
fn read_spec_file(path: &str, kind: &str) -> Result<String, ErrorData> {
    if let Some(why) = borer_engine::program::unusable_path(Path::new(path)) {
        return Err(err_params(format!("{why}; give a path to {kind}")));
    }
    std::fs::read_to_string(path).map_err(|e| {
        err_params(format!(
            "reading {}: {e}",
            borer_engine::text::short_path(path)
        ))
    })
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
    /// code analysis, or is not the loaded program's architecture.
    fn other_build(&self, path: &str) -> Result<OtherBuild, ErrorData> {
        self.require_loaded()?;
        let program = self.load_other(path)?;
        let analysis = Analysis::compute_with(&program, self.packs_for(&program).0);
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
        self.refusing(|p, a, o| {
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
    /// * `render` - The renderer; its `Err` is the refusal's message.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or the renderer refuses;
    /// internal error when the analysis cannot run or faults.
    fn refusing(
        &self,
        render: impl FnOnce(&Program, &Analysis, &Overlay) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        let mut refused = None;
        let out = self.with_analysis(|p, a, o| {
            Ok(render(p, a, o).unwrap_or_else(|why| {
                refused = Some(why);
                String::new()
            }))
        })?;
        refused.map_or(Ok(out), |why| Err(err_params(why)))
    }

    /// Runs the emulator from a routine and reports what it decoded.
    ///
    /// # Arguments
    ///
    /// * `target` - The routine's address or name, then directives.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the spec is refused.
    pub(crate) fn emulate_text(&self, target: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::emulate_tsv(p, a, o, target))
    }

    /// Runs a function over a probe string in every argument shape and
    /// reports what it does with it, the CLI's `oracle`.
    ///
    /// # Arguments
    ///
    /// * `target` - The function's address or name.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the target is not a function.
    pub(crate) fn oracle_text(&self, target: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::oracle_tsv(p, a, o, target))
    }

    /// Calls a function on typed inputs and checks its decompiled text on
    /// them, the CLI's `run`.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<function>[,steps=N]/<input>[;<input>...]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the spec is refused.
    pub(crate) fn run_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::run_tsv(p, a, o, spec))
    }

    /// Recovers the strings the program generates at run time, the CLI's
    /// `hidden`.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive text the string or its generator must
    ///   contain; empty for all.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn hidden_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| Ok(render::hidden_strings_tsv(p, a, o, filter)))
    }

    /// Groups the imports into the capabilities they grant.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn capabilities_text(&self) -> Result<String, ErrorData> {
        self.with_program(|p| Ok(render::capability_map_tsv(p)))
    }

    /// Lists the `QObject` subclasses `moc` described and their methods.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn qt_text(&self) -> Result<String, ErrorData> {
        let a = self.analysis()?;
        Ok(render::qt_tsv(&a))
    }

    /// Recovers the strings functions build on their stacks.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive substring of the recovered text.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn stack_strings_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| Ok(render::stack_strings_tsv(p, a, o, filter)))
    }

    /// Recovers the virtual program a virtualized function runs.
    ///
    /// # Arguments
    ///
    /// * `target` - The function's address, with optional registers.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the spec is refused.
    pub(crate) fn devirtualize_text(&self, target: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::devirtualize_tsv(p, a, o, target))
    }

    /// Runs a packer's bootstrap and reports the code it decrypts into memory.
    ///
    /// # Arguments
    ///
    /// * `target` - Where to start, with optional registers; entry by default.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the spec is refused.
    pub(crate) fn unpack_text(&self, target: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::unpack_tsv(p, a, o, target))
    }

    /// The loaded binary's function fingerprint manifest.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn fingerprint_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(|_, a, _| Ok(render::fingerprint_digest(a)))
    }

    /// The content hashes the loaded file is correlated by: imphash,
    /// authentihash and tlsh, from the image alone.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn hashes_text(&self) -> Result<String, ErrorData> {
        self.with_program(|p| Ok(borer_engine::hashing::hashes_tsv(p)))
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
        if let Some(why) = borer_engine::program::unusable_path(Path::new(other)) {
            return Err(err_params(format!(
                "{why}; give a path to a program or a fingerprint sidecar"
            )));
        }
        if let Ok(text) = std::fs::read_to_string(other)
            && text.starts_with("# borer fingerprint")
        {
            let old_prints = render::parse_prints(&text);
            let base = file_label(Path::new(other));
            return self.with_analysis(|p, a, _| {
                Ok(render::diff_prints_tsv(
                    &old_prints,
                    &render::prints_of(a),
                    &base,
                    &file_label(&p.path),
                ))
            });
        }
        let other = self.other_build(other)?;
        self.with_analysis(|p, a, _| {
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
        self.with_analysis(|_, a, o| {
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

    /// Finds the dispatch loops, or describes the handlers of one.
    ///
    /// # Arguments
    ///
    /// * `filter` - Empty for the list, or a dispatch or function address.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the filter names no dispatch loop.
    pub(crate) fn vm_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::vm_dispatch_tsv(p, a, o, filter))
    }

    /// Recovers the APIs and DLLs the program resolves at runtime.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn dynamic_imports_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| Ok(render::dynamic_imports_tsv(p, a, o)))
    }

    /// Finds the functions that judge a key, serial or license.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn checks_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| Ok(render::license_checks_tsv(p, a, o)))
    }

    /// Reports the anti-debug and anti-VM techniques the binary carries.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn anti_analysis_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| Ok(render::anti_analysis_tsv(p, a, o)))
    }

    /// Reports flattened control flow.
    ///
    /// # Arguments
    ///
    /// * `filter` - Empty for every dispatcher, or one address or name.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it has no code analysis, or the filter
    /// names no dispatcher.
    pub(crate) fn flattening_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::flattening_tsv(p, a, o, filter))
    }

    /// Searches for an argument value that changes a function's answer.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<address>[,aN]`, `aN` the argument the decompiler names
    ///   so, counting from one; `a1` when absent.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it has no code analysis, or the spec is
    /// refused.
    pub(crate) fn solve_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::solve_tsv(p, a, o, spec))
    }

    /// Says what is at an address and where each fact came from.
    ///
    /// # Arguments
    ///
    /// * `target` - An address or a name.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it has no code analysis, or the target
    /// names nothing.
    pub(crate) fn why_text(&self, target: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::why_tsv(p, a, o, target))
    }

    /// Proposes a structure from a pointer's accesses.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<address>[,<register>]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it has no code analysis, or the spec is
    /// refused.
    pub(crate) fn layout_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::layout_tsv(p, a, o, spec))
    }

    /// Follows a value forward from an address.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<address>[,<register>]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it has no code analysis, or the spec is
    /// refused.
    pub(crate) fn taint_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.refusing(|p, a, o| render::taint_tsv(p, a, o, spec))
    }

    /// Renders the one-call triage report.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn triage_text(&self) -> Result<String, ErrorData> {
        if self.require_loaded()?.no_code().is_some() {
            return self.with_program(|p| Ok(render::file_triage_tsv(p)));
        }
        self.with_analysis(|p, a, o| Ok(render::triage_tsv(p, a, o)))
    }

    /// Reports the marks a packer or protector leaves on the image.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn protection_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, _| Ok(render::protection_tsv(p, a)))
    }

    /// Lists the fields the binary's assertions name.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive substring of the field or class.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn asserts_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| Ok(render::asserted_fields_tsv(p, a, o, filter)))
    }

    /// Groups the functions by the source file their assertions name.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive substring of the path, or empty for the
    ///   directory summary.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn sources_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, _| Ok(render::source_tree_tsv(p, a, filter)))
    }

    /// Lists the classes that registered a four-character code.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive substring of the class name or the code.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn classes_text(&self, filter: &str) -> Result<String, ErrorData> {
        let a = self.analysis()?;
        Ok(render::class_ids_tsv(&a, filter))
    }

    /// Lists the packs this session knows and how each fits the loaded
    /// program, the CLI's `packs`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn packs_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, _| {
            let mut out = borer::packs::listing(p, &self.packs, borer::packs::auto_enabled());
            out.push_str(&borer_engine::analysis::sigs::pack_names_tsv(&a.pack_names));
            out.push_str(&borer_engine::analysis::libnames::library_names_tsv(
                &a.library_names,
            ));
            out.push_str(&borer_engine::script::pack_scripts_tsv(&a.pack_scripts));
            Ok(out)
        })
    }

    /// Decompiles a function under a scenario, the CLI's `scenario`.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<function>/<a2=5,...>`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the spec does not read, or the function
    /// does not decompile.
    pub(crate) fn scenario_text(&self, spec: &str) -> Result<String, ErrorData> {
        let (target, assume) = spec
            .rsplit_once('/')
            .ok_or_else(|| err_params("borer://scenario/<function>/<a2=5,...>"))?;
        let assume =
            borer_engine::analysis::decompile::parse_scenario(assume).map_err(err_params)?;
        self.with_analysis(|p, a, o| {
            let entry = self.function_entry(p, a, target)?;
            borer_engine::analysis::decompile::decompile_scenario(p, a, o, entry, &assume)
                .ok_or_else(|| "the function does not decompile".to_owned())
        })
    }

    /// Runs a scenario for each value of one parameter and groups the ones
    /// that behave alike, the CLI's `scenarios`.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<function>/<a2=0..32>`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the spec does not read.
    pub(crate) fn scenarios_text(&self, spec: &str) -> Result<String, ErrorData> {
        let (target, values) = spec
            .rsplit_once('/')
            .ok_or_else(|| err_params("borer://scenarios/<function>/<a2=0..32>"))?;
        let (slot, values) =
            borer_engine::analysis::decompile::parse_explosion(values).map_err(err_params)?;
        self.with_analysis(|p, a, o| {
            let entry = self.function_entry(p, a, target)?;
            let cases = borer_engine::analysis::decompile::explode(p, a, o, entry, slot, &values);
            Ok(borer_engine::analysis::decompile::explode_tsv(
                &cases,
                slot,
                values.len(),
            ))
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
    /// When no binary is loaded, or the path is a device or does not read.
    pub(crate) fn script_text(&self, path: &str) -> Result<String, ErrorData> {
        let code = read_spec_file(path, "a Rhai script")?;
        let program = self.require_loaded()?;
        let a = self.ensure_analysis().map_err(err_params)?;
        let run =
            borer_engine::script::run_with(program, a, Arc::new(self.overlay()), &code, &[], None);
        Ok(borer_engine::script::run_tsv(&run))
    }

    /// Writes the session's names as a pack that finds the same functions
    /// in another build by their first bytes, the CLI's `export-pack`.
    ///
    /// # Arguments
    ///
    /// * `spec` - The pack's name, then `,all` to add the names the
    ///   analysis recovered to the user's.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the name is empty or has a space, or what
    /// follows a comma is not `all`: `x,y` named a pack `x,y`.
    pub(crate) fn export_pack_text(&self, spec: &str) -> Result<String, ErrorData> {
        let (name, all) = match spec.split_once(',') {
            None => (spec, false),
            Some((name, "all")) => (name, true),
            Some((_, other)) => {
                return Err(err_params(format!(
                    "after the pack name comes ,all or nothing, not {}",
                    borer_engine::text::quoted(other)
                )));
            }
        };
        if name.is_empty() || name.contains(char::is_whitespace) {
            return Err(err_params(format!(
                "a pack name is one word, not {}",
                borer_engine::text::quoted(name)
            )));
        }
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::sigs::export_pack(
                p, a, o, name, all,
            ))
        })
    }

    /// Lists the program's recovered singletons (thread-local and global),
    /// each with its slot, `::Instance` accessor and class.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive substring of the class name; empty for all.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn singletons_text(&self, filter: &str) -> Result<String, ErrorData> {
        let a = self.analysis()?;
        Ok(render::singletons_tsv(&a, &self.overlay(), filter))
    }

    /// Lists the pointer-relative field accesses one function makes, keyed by
    /// `(base, offset)`, from its decompilation.
    ///
    /// The offset an SDK anchors to an engine function is confirmed against a
    /// real typed dereference here, not a byte search, and a field a build
    /// moved shows its new offset.
    ///
    /// # Arguments
    ///
    /// * `address` - A function entry, an interior address, or a name.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address is not in a function, or it does
    /// not decompile.
    pub(crate) fn fields_text(&self, address: &str) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| {
            let entry = self.function_entry(p, a, address)?;
            borer_engine::analysis::classes::fields_tsv(p, a, o, entry)
                .ok_or_else(|| format!("{address} did not decompile"))
        })
    }

    /// Lists every instruction in the program that touches `[reg + offset]`,
    /// each with the function it belongs to.
    ///
    /// The inverse of [`Self::fields_text`]: that asks what one function
    /// dereferences, this asks who dereferences one field. A byte search for
    /// the encoding finds the same sites among strangers that share the
    /// displacement and names none of them.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<offset>[,<name-filter>]`: the field offset as hex or
    ///   decimal with an optional minus sign, then a case-insensitive
    ///   substring of the function name.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the offset does not parse.
    pub(crate) fn fieldrefs_text(&self, spec: &str) -> Result<String, ErrorData> {
        /// Most rows one read returns.
        const PAGE: usize = 500;
        let (offset_text, filter) = spec.split_once(',').unwrap_or((spec, ""));
        let offset = parse_field_offset(offset_text.trim()).map_err(err_params)?;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::fieldrefs::field_refs_tsv(
                p,
                a,
                o,
                offset,
                filter.trim(),
                0,
                PAGE,
            ))
        })
    }

    /// Lists every recovered class whose virtual at a vtable slot returns a
    /// constant, with the constant: a registry's id table read off the
    /// classes instead of the registry.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<slot>[,<class-filter>]`: the zero-based vtable index,
    ///   then a case-insensitive substring of the class name.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the slot does not parse.
    pub(crate) fn vslot_text(&self, spec: &str) -> Result<String, ErrorData> {
        let SlotSpec { slot, filter } = SlotSpec::parse(spec)?;
        self.with_analysis(|p, a, _| {
            Ok(borer_engine::analysis::vtables::slot_constants_tsv(
                p, a, slot, filter, SLOT_PAGE,
            ))
        })
    }

    /// Lists pseudo-C lines program-wide containing `text`, or matching it
    /// when written `re:<expression>`, from the decompilation index, building
    /// the index on first use.
    ///
    /// # Arguments
    ///
    /// * `text` - The text a line must contain, as the URI carried it
    ///   (decoded once at [`super::BorerServer::read_uri`]).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the text is empty, the expression does not
    /// parse, or the index cannot be written.
    pub(crate) fn grep_text(&self, text: &str) -> Result<String, ErrorData> {
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
        self.with_analysis(|p, a, o| {
            let (index, _, _) = borer::index::load_or_build(p, a)?;
            borer::index::grep_tsv(&index, a, o, text, "", 0, PAGE)
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
        self.with_analysis(|p, a, _| {
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

    /// Renders the record a deserializer reads off its stream.
    ///
    /// A function that reads no stream is an answer, not a fault: the line
    /// says so, where an error code read as the server failing.
    ///
    /// # Arguments
    ///
    /// * `what` - A function by address or name, or a class name whose
    ///   reading virtual is picked.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the name is neither a function nor a
    /// class whose virtuals read a stream.
    pub(crate) fn schema_text(&self, what: &str) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| match self.function_entry(p, a, what) {
            Ok(entry) => Ok(borer_engine::analysis::schema::schema_tsv(p, a, o, entry)
                .unwrap_or_else(|| {
                    format!(
                        "# {} hands no stream to its calls: not a deserializer\n",
                        borer_engine::analysis::name_of(a, o, entry)
                    )
                })),
            Err(_) => {
                borer_engine::analysis::schema::class_schema_tsv(p, a, o, what).ok_or_else(|| {
                    format!(
                        "{} is neither a function nor a class whose virtuals read a stream",
                        borer_engine::text::quoted(what)
                    )
                })
            }
        })
    }

    /// Lists every class with a constant at a vtable slot and the record its
    /// reading virtual decodes.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<slot>[,<class-filter>]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the slot does not parse.
    pub(crate) fn schemas_text(&self, spec: &str) -> Result<String, ErrorData> {
        let SlotSpec { slot, filter } = SlotSpec::parse(spec)?;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::schema::schemas_tsv(
                p, a, o, slot, filter, SLOT_PAGE,
            ))
        })
    }

    /// Renders what a serializer writes onto its stream.
    ///
    /// A function that writes no stream is an answer, not a fault, as for
    /// [`Self::schema_text`].
    ///
    /// # Arguments
    ///
    /// * `what` - A function by address or name, or a class name whose
    ///   writing virtual is picked.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the name is neither a function nor a
    /// class whose virtuals write a stream.
    pub(crate) fn encode_text(&self, what: &str) -> Result<String, ErrorData> {
        self.with_analysis(|p, a, o| match self.function_entry(p, a, what) {
            Ok(entry) => Ok(borer_engine::analysis::encode::encoding_tsv(p, a, o, entry)
                .unwrap_or_else(|| {
                    format!(
                        "# {} hands its stream nothing: not a serializer\n",
                        borer_engine::analysis::name_of(a, o, entry)
                    )
                })),
            Err(_) => {
                borer_engine::analysis::encode::class_encoding_tsv(p, a, o, what).ok_or_else(|| {
                    format!(
                        "{} is neither a function nor a class whose virtuals write a stream",
                        borer_engine::text::quoted(what)
                    )
                })
            }
        })
    }

    /// Lists every class with a constant at a vtable slot and what its
    /// writing virtual puts on the wire.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<slot>[,<class-filter>]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the slot does not parse.
    pub(crate) fn encodes_text(&self, spec: &str) -> Result<String, ErrorData> {
        let SlotSpec { slot, filter } = SlotSpec::parse(spec)?;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::encode::encodings_tsv(
                p, a, o, slot, filter, SLOT_PAGE,
            ))
        })
    }

    /// Lists every class with a constant at a vtable slot with the addresses
    /// a binding hooks.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<slot>[,<class-filter>]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the slot does not parse.
    pub(crate) fn hooks_text(&self, spec: &str) -> Result<String, ErrorData> {
        let SlotSpec { slot, filter } = SlotSpec::parse(spec)?;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::protocol::hooks_tsv(
                p, a, o, slot, filter, SLOT_PAGE,
            ))
        })
    }

    /// Lists every class with a constant at a vtable slot with its senders,
    /// its encoding and its decoding on one row.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<slot>[,<class-filter>]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the slot does not parse.
    pub(crate) fn protocol_text(&self, spec: &str) -> Result<String, ErrorData> {
        let SlotSpec { slot, filter } = SlotSpec::parse(spec)?;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::protocol::protocol_tsv(
                p, a, o, slot, filter, SLOT_PAGE,
            ))
        })
    }

    /// Lists every class with a constant at a vtable slot and the functions
    /// constructing it.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<slot>[,<class-filter>]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the slot does not parse.
    pub(crate) fn senders_text(&self, spec: &str) -> Result<String, ErrorData> {
        let SlotSpec { slot, filter } = SlotSpec::parse(spec)?;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::senders::senders_tsv(
                p, a, o, slot, filter, SLOT_PAGE,
            ))
        })
    }

    /// Lists every function sharing the shape of one, with what differs.
    ///
    /// # Arguments
    ///
    /// * `address` - A function entry, an interior address, or a name.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not in a function.
    pub(crate) fn shape_text(&self, address: &str) -> Result<String, ErrorData> {
        /// Most rows one read returns.
        const PAGE: usize = 2000;
        self.with_analysis(|p, a, o| {
            let entry = self.function_entry(p, a, address)?;
            render::shape_siblings_tsv(p, a, o, entry, PAGE)
                .ok_or_else(|| format!("no function at {address}"))
        })
    }

    /// Lists every message every component accepts, with its handler.
    ///
    /// # Arguments
    ///
    /// * `filter` - Substring of the component's or the message's class;
    ///   empty for all.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn ports_text(&self, filter: &str) -> Result<String, ErrorData> {
        /// Most rows one read returns.
        const PAGE: usize = 5000;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::ports::routes_tsv(
                p,
                a,
                o,
                filter.trim(),
                PAGE,
            ))
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
        let text = read_spec_file(path, "a snapshot file")?;
        let before = borer_engine::analysis::snapshot::read(&text).map_err(err_params)?;
        self.with_analysis(|p, a, o| {
            let after = borer_engine::analysis::snapshot::facts(p, a, o);
            Ok(borer_engine::analysis::snapshot::changes_tsv(
                &before, &after,
            ))
        })
    }

    /// Answers everything the analysis knows about one name.
    ///
    /// # Arguments
    ///
    /// * `name` - The name, as the URI carried it (decoded once at
    ///   [`super::BorerServer::read_uri`]).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the name is empty.
    pub(crate) fn about_text(&self, name: &str) -> Result<String, ErrorData> {
        if name.trim().is_empty() {
            return Err(err_params(ABOUT_NEEDS_A_NAME));
        }
        self.with_analysis(|p, a, o| Ok(borer_engine::analysis::about::about_tsv(p, a, o, name)))
    }

    /// Lays out the program's namespaces, or one namespace's classes, by role.
    ///
    /// # Arguments
    ///
    /// * `namespace` - A namespace; empty for the overview.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn map_text(&self, namespace: &str) -> Result<String, ErrorData> {
        /// Most rows one read returns.
        const PAGE: usize = 5000;
        let a = self.analysis()?;
        Ok(borer_engine::analysis::map::map_tsv(
            &a,
            &self.overlay(),
            namespace.trim(),
            PAGE,
        ))
    }

    /// Lists every attribute the loaded client registers.
    ///
    /// # Arguments
    ///
    /// * `filter` - Substring of the name or the code; empty for all.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn attrs_text(&self, filter: &str) -> Result<String, ErrorData> {
        /// Most rows one read returns, where the renderer pages too.
        const PAGE: usize = 200;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::attributes::catalog_tsv(
                p,
                a,
                o,
                filter.trim(),
                PAGE,
            ))
        })
    }

    /// Lists every class that registered a wire id, with its named fields
    /// and the functions that test for the id.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive substring of the class name; empty for all.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn messages_text(&self, filter: &str) -> Result<String, ErrorData> {
        /// Most rows one read returns, where the renderer pages too.
        const PAGE: usize = 200;
        self.with_analysis(|p, a, o| {
            Ok(borer_engine::analysis::messages::catalog_tsv(
                p,
                a,
                o,
                filter.trim(),
                PAGE,
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
        if let Ok(meta) = std::fs::metadata(path)
            && meta.is_file()
            && meta.len() > MANIFEST_MAX
        {
            return Err(err_params(format!(
                "{short} is {} bytes, past the {MANIFEST_MAX} one read takes; split the manifest or judge it with the CLI's anchors",
                meta.len()
            )));
        }
        let text = read_spec_file(path, "a manifest file")?;
        let anchors = borer_engine::analysis::anchors::parse_manifest(&text).map_err(err_params)?;
        if anchors.len() > ANCHORS_MAX {
            return Err(err_params(format!(
                "{short} has {} anchors, past the {ANCHORS_MAX} one read judges; split the manifest or judge it with the CLI's anchors",
                anchors.len()
            )));
        }
        self.with_analysis(|p, a, o| {
            let (table, _) = borer_engine::analysis::anchors::verify_tsv(p, a, o, &anchors, PAGE);
            Ok(table)
        })
    }

    /// Lists every name table the binary encodes, one line per function.
    ///
    /// The listing reads every table-shaped function of the binary, the
    /// one answer that waits for them all; every other tool reads only the
    /// tables of the functions it decompiles. A table named by an enum
    /// type is written `enum <type>` once, where the type's own `enum`
    /// made it `enum enum <type>`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn enums_text(&self) -> Result<String, ErrorData> {
        let a = self.analysis()?;
        let p = self.require_loaded()?;
        let o = self.overlay_plain();
        let tables = borer_engine::analysis::decompile::enum_tables(&p, &a, &o);
        let mut out = format!("# {} name tables\n", tables.len());
        for (entry, table) in &tables {
            out.push_str(&enum_row(
                &borer_engine::analysis::name_of(&a, &o, *entry),
                *entry,
                table,
            ));
        }
        Ok(out)
    }
}

/// One `borer://enums` row: the function, its entry, `enum` and the
/// table's name, then its members.
///
/// # Arguments
///
/// * `function` - The function's name.
/// * `entry` - Its entry.
/// * `table` - The name table it encodes.
fn enum_row(
    function: &str,
    entry: u64,
    table: &borer_engine::analysis::decompile::EnumTable,
) -> String {
    let members: Vec<String> = table
        .members
        .iter()
        .map(|(k, lit)| format!("{lit} = {k}"))
        .collect();
    let name = match table.name.strip_prefix("enum ").unwrap_or(&table.name) {
        "" => String::new(),
        bare => format!(" {bare}"),
    };
    format!(
        "{function} @ {entry:#x}: enum{name}: {}\n",
        members.join(", ")
    )
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, RwLock};

    use borer_engine::program::{Arch, Program, Section};
    use rmcp::ErrorData;
    use rmcp::model::ErrorCode;

    use super::{ABOUT_NEEDS_A_NAME, BorerServer};

    /// A resource handler, as `read_resource` calls it with the URI's argument.
    type Handler = fn(&BorerServer, &str) -> Result<String, ErrorData>;

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
        let cases: [(&str, Handler, &str, &str); 16] = [
            (
                "why",
                BorerServer::why_text,
                "nowhere",
                "cannot resolve nowhere",
            ),
            (
                "taint",
                BorerServer::taint_text,
                "nowhere",
                "cannot resolve nowhere",
            ),
            (
                "layout",
                BorerServer::layout_text,
                "nowhere",
                "cannot resolve nowhere",
            ),
            (
                "solve",
                BorerServer::solve_text,
                "nowhere",
                "cannot resolve nowhere",
            ),
            (
                "emulate",
                BorerServer::emulate_text,
                "nowhere",
                "cannot resolve nowhere",
            ),
            (
                "emulate",
                BorerServer::emulate_text,
                "0x1",
                "nothing is mapped at 0x1;",
            ),
            (
                "emulate",
                BorerServer::emulate_text,
                "0x1000,steps=abc",
                "bad step count in steps=abc",
            ),
            (
                "run",
                BorerServer::run_text,
                "nowhere/1",
                "cannot resolve nowhere",
            ),
            (
                "run",
                BorerServer::run_text,
                "0x1000,steps=abc/1",
                "cannot read steps=abc; use steps=N",
            ),
            (
                "devirt",
                BorerServer::devirtualize_text,
                "nowhere",
                "no function nowhere",
            ),
            (
                "unpack",
                BorerServer::unpack_text,
                "0x1000,budget=abc",
                "bad budget in budget=abc",
            ),
            (
                "oracle",
                BorerServer::oracle_text,
                "nowhere",
                "no discovered function at 'nowhere'",
            ),
            (
                "flat",
                BorerServer::flattening_text,
                "nowhere",
                "cannot resolve nowhere",
            ),
            (
                "vm",
                BorerServer::vm_text,
                "nowhere",
                "cannot resolve nowhere",
            ),
            (
                "grep",
                BorerServer::grep_text,
                "",
                "grep needs a non-empty text",
            ),
            ("about", BorerServer::about_text, "", ABOUT_NEEDS_A_NAME),
        ];
        for (resource, handler, arg, message) in cases {
            let err = handler(&server, arg).expect_err(resource);
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

    /// The comparison resources refuse a session with no binary before
    /// they load the other build, `exportpack` refuses a part after the
    /// name that is not `all`, and an enum table's row says `enum` once.
    ///
    /// # Panics
    ///
    /// When a refusal differs or a row repeats `enum`.
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
            assert_eq!(e.message, crate::NO_BINARY);
        }
        let e = server.export_pack_text("x,y").expect_err("not all");
        assert_eq!(e.code, ErrorCode::INVALID_PARAMS);
        assert_eq!(
            e.message,
            "after the pack name comes ,all or nothing, not 'y'"
        );
        let table = |name: &str| borer_engine::analysis::decompile::EnumTable {
            name: name.to_owned(),
            members: vec![(0, "S".to_owned()), (1, "X".to_owned())],
            param: Some(0),
        };
        assert_eq!(
            super::enum_row("f", 0x10, &table("enum mi_chunkbin_e")),
            "f @ 0x10: enum mi_chunkbin_e: S = 0, X = 1\n"
        );
        assert_eq!(
            super::enum_row("f", 0x10, &table("")),
            "f @ 0x10: enum: S = 0, X = 1\n"
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
        let out = server.about_text("x%2541").expect("about answers");
        assert!(out.contains("'x%2541'"), "{out}");
    }
}
