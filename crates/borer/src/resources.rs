//! The handlers behind the `borer://` resource templates, and the help
//! that says how to read each one.
//!
//! One method per template, each answering in the same table conventions as
//! the tools; `read_resource` in `main.rs` parses the URI and dispatches here.

use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;

use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::program::{Feature, Program};
use rmcp::ErrorData;

use crate::BorerServer;
use crate::catalog::{RESOURCE_TEMPLATES, RESOURCES, resource_name};
use crate::errors::{err_not_found, err_params};
use crate::paging::Asked;
use crate::params::parse_field_offset;
use crate::session;
use crate::state::{lock, read_lock};

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

/// Largest text file a resource reads, in bytes: a script, a manifest or
/// a fingerprint sidecar is text an agent wrote or borer did, and a large
/// binary's sidecar runs to tens of megabytes.
const SPEC_FILE_MAX: u64 = 1 << 26;

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
    let bytes = borer_engine::program::read_regular(Path::new(path), SPEC_FILE_MAX)
        .map_err(|e| err_params(format!("{e:#}; give a path to {kind}")))?;
    String::from_utf8(bytes).map_err(|_| {
        err_params(format!(
            "{} is not a text file; give a path to {kind}",
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
        self.refusing(Feature::Emulate, |p, a, o| {
            render::emulate_tsv(p, a, o, target)
        })
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
        self.refusing(Feature::Emulate, |p, a, o| {
            render::oracle_tsv(p, a, o, target)
        })
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
        self.refusing(Feature::Emulate, |p, a, o| render::run_tsv(p, a, o, spec))
    }

    /// Answers where two runs of one function part ways.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<function>[,steps=N]/<input>;<input>`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the spec is refused.
    pub(crate) fn diverge_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.refusing(Feature::Emulate, |p, a, o| {
            render::run_diff_tsv(p, a, o, spec)
        })
    }

    /// Records test vectors for reimplementing a function: typed inputs
    /// run in the emulator and a C harness asserting what came back.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<function>[,count=N][,steps=N]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it is not emulated, or the spec or the
    /// function's signature is refused.
    pub(crate) fn vectors_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.refusing(Feature::Emulate, |p, a, o| {
            render::vectors_tsv(p, a, o, spec)
        })
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
        self.with_analysis(Feature::Emulate, |p, a, o| {
            Ok(render::hidden_strings_tsv(p, a, o, filter))
        })
    }

    /// Recovers the strings a decoder produces when run at each of its call
    /// sites, the resource `borer://decoded`.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive text the string must contain, with
    ///   `offset=<n>` and `limit=<n>` for paging; empty for all.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the offset or the limit does not read.
    pub(crate) fn decoded_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.refusing(Feature::Emulate, |p, a, o| {
            render::decoded_tsv(p, a, o, filter)
        })
    }

    /// Groups the imports, and the syscall sites of a program with code
    /// analysis, into the capabilities they grant.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or its analysis fails.
    pub(crate) fn capabilities_text(&self) -> Result<String, ErrorData> {
        self.with_program(|p| {
            let a = match p.refuses(Feature::Discover) {
                None => Some(self.ensure_analysis()?),
                Some(_) => None,
            };
            Ok(render::capability_map_tsv(p, a.as_deref()))
        })
    }

    /// Lists the `QObject` subclasses `moc` described and their methods.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn qt_text(&self) -> Result<String, ErrorData> {
        let a = self.analysis(Feature::Decompile)?;
        Ok(render::qt_tsv(&a))
    }

    /// Lists the Objective-C classes and categories a Mach-O's metadata
    /// describes, a row per method with its implementation.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive substring of the class or selector;
    ///   empty for all.
    /// * `asked` - The read, for its page.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or its functions are not discovered.
    pub(crate) fn objc_text(&self, filter: &str, asked: &Asked) -> Result<String, ErrorData> {
        /// Most rows one read returns, where the renderer pages too.
        const PAGE: usize = 200;
        let again = asked.again();
        self.with_analysis(Feature::Discover, |_, a, _| {
            Ok(borer_engine::analysis::objc::objc_tsv(
                a,
                filter.trim(),
                asked.window(PAGE, &again),
            ))
        })
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(render::stack_strings_tsv(p, a, o, filter))
        })
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
        self.refusing(Feature::Emulate, |p, a, o| {
            render::devirtualize_tsv(p, a, o, target)
        })
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
        self.refusing(Feature::Emulate, |p, a, o| {
            render::unpack_tsv(p, a, o, target)
        })
    }

    /// The loaded binary's function fingerprint manifest.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn fingerprint_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Discover, |_, a, _| {
            Ok(render::fingerprint_digest(a))
        })
    }

    /// The content hashes the loaded file is correlated by: imphash,
    /// authentihash, TLSH and borer-lsh, from the image alone.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn hashes_text(&self) -> Result<String, ErrorData> {
        self.with_program(|p| Ok(borer_engine::hashing::hashes_tsv(p)))
    }

    /// The shortest byte signature that matches code once
    /// ([`render::signature_tsv`]).
    ///
    /// # Arguments
    ///
    /// * `target` - A function's name or entry, or any code address.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the target names nothing, or the image is
    /// not x86 or x86-64 code.
    pub(crate) fn sig_text(&self, target: &str) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Discover, |p, a, o| {
            let va = borer_engine::analysis::resolve_suggesting(p, a, o, target)?;
            render::signature_tsv(p, a, o, va)
        })
    }

    /// A YARA rule from functions' signatures and the strings they
    /// reference ([`render::yara_rule`]).
    ///
    /// # Arguments
    ///
    /// * `list` - Functions by name or entry, comma-separated.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, a function names nothing, or nothing is
    /// left to match on.
    pub(crate) fn yara_text(&self, list: &str) -> Result<String, ErrorData> {
        let (list, out) = export_target(list);
        let text = self.with_analysis(Feature::Discover, |p, a, o| {
            let entries = list
                .split(',')
                .map(str::trim)
                .filter(|f| !f.is_empty())
                .map(|f| borer_engine::analysis::resolve_suggesting(p, a, o, f))
                .collect::<Result<Vec<u64>, String>>()?;
            render::yara_rule(p, a, o, &entries)
        })?;
        export(text, out)
    }

    /// borer's names and comments as a script or database another tool
    /// applies ([`render::names_export`]).
    ///
    /// # Arguments
    ///
    /// * `tool` - `ida`, `ghidra`, `binja` or `x64dbg`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the tool is not one of those.
    pub(crate) fn names_text(&self, tool: &str) -> Result<String, ErrorData> {
        let (tool, out) = export_target(tool);
        let Some(tool) = render::Tool::parse(tool) else {
            return Err(err_params(format!(
                "unknown tool {}; use one of: {}",
                borer_engine::text::quoted(tool),
                render::Tool::NAMES
            )));
        };
        let text = self.with_analysis(Feature::Discover, |p, a, o| {
            Ok(render::names_export(p, a, o, tool))
        })?;
        export(text, out)
    }

    /// One place as virtual address, relative address, file offset,
    /// section and function ([`borer_engine::fileinfo::locate`]).
    ///
    /// # Arguments
    ///
    /// * `place` - A virtual address, `rva:<n>` or `off:<n>`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the place is not a number or maps to
    /// nothing.
    pub(crate) fn addr_text(&self, place: &str) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Discover, |p, a, o| {
            borer_engine::fileinfo::locate(p, Some(a), o, place)
        })
    }

    /// Base64 and hex strings that decode to text or a known file
    /// ([`render::encoded_strings_tsv`]).
    ///
    /// # Arguments
    ///
    /// * `filter` - Text the decoded value must contain; empty for all.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn encoded_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.with_program(|p| Ok(render::encoded_strings_tsv(p, filter)))
    }

    /// Answers the resources that take a function, a tool or a place for
    /// another tool: `sig`, `yara`, `names` and `addr`.
    ///
    /// # Arguments
    ///
    /// * `kind` - The resource's name.
    /// * `arg` - Its argument.
    ///
    /// # Errors
    ///
    /// As the resource does.
    pub(crate) fn handoff_text(&self, kind: &str, arg: &str) -> Result<String, ErrorData> {
        match kind {
            "sig" => self.sig_text(arg),
            "yara" => self.yara_text(arg),
            "names" => self.names_text(arg),
            _ => self.addr_text(arg),
        }
    }

    /// Lists a .NET assembly's metadata: types, methods, P/Invokes,
    /// external members, references and user strings.
    ///
    /// # Arguments
    ///
    /// * `spec` - Kinds and texts to keep, and the page, comma-separated.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, its metadata was refused, or the page
    /// does not read.
    pub(crate) fn clr_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.with_program(|p| borer_engine::clr::clr_tsv(p, spec).map_err(|e| e.to_string()))
    }

    /// Lists the programs and containers embedded in the loaded file, and
    /// the high-entropy runs no header explains.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn children_text(&self) -> Result<String, ErrorData> {
        self.with_program(|p| Ok(borer_engine::carve::children_tsv(p)))
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
        if let Ok(bytes) = borer_engine::program::read_regular(Path::new(other), SPEC_FILE_MAX)
            && let Ok(text) = String::from_utf8(bytes)
            && text.starts_with("# borer fingerprint")
        {
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
        self.refusing(Feature::Decompile, |p, a, o| {
            render::vm_dispatch_tsv(p, a, o, filter)
        })
    }

    /// Recovers the APIs and DLLs the program resolves at runtime.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn dynamic_imports_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(render::dynamic_imports_tsv(p, a, o))
        })
    }

    /// Finds the functions that judge a key, serial or license.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn checks_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(render::license_checks_tsv(p, a, o))
        })
    }

    /// Reports the anti-debug and anti-VM techniques the binary carries.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn anti_analysis_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(render::anti_analysis_tsv(p, a, o))
        })
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
        self.refusing(Feature::Decompile, |p, a, o| {
            render::flattening_tsv(p, a, o, filter)
        })
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
        self.refusing(Feature::Emulate, |p, a, o| render::solve_tsv(p, a, o, spec))
    }

    /// Reports a counted loop that compares a few bits of a product.
    ///
    /// A loop with no such check is a refusal, not a `#` line: an empty
    /// success would read as a check the function does not have.
    ///
    /// # Arguments
    ///
    /// * `address` - The function's address or name.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it has no code analysis, or the function
    /// has no partial product check.
    pub(crate) fn partial_text(&self, address: &str) -> Result<String, ErrorData> {
        self.refusing(Feature::Decompile, |p, a, o| {
            render::partial_tsv(p, a, o, address)
        })
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
        self.refusing(Feature::Decompile, |p, a, o| {
            render::why_tsv(p, a, o, target)
        })
    }

    /// Proposes a structure from a pointer's accesses, or with `apply=Name`
    /// defines it as a user struct and types the parameter the pointer
    /// arrives in ([`borer_engine::analysis::apply::from_pointer`]): a dry
    /// run unless the spec also says `dry_run=false`.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<address>[,<register>][,apply=<Name>][,dry_run=false]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it has no code analysis, or the spec or
    /// the struct to apply is refused.
    pub(crate) fn layout_text(&self, spec: &str) -> Result<String, ErrorData> {
        let mut apply: Option<&str> = None;
        let mut dry = true;
        let mut kept: Vec<&str> = Vec::new();
        for part in spec.split(',') {
            match part.trim() {
                "dry_run=false" => dry = false,
                "dry_run=true" => dry = true,
                t => match t.strip_prefix("apply=") {
                    Some(name) => apply = Some(name),
                    None => kept.push(part),
                },
            }
        }
        let spec = kept.join(",");
        self.refusing(Feature::Decompile, |p, a, o| match apply {
            None => render::layout_tsv(p, a, o, &spec),
            Some(name) => {
                let plan = borer_engine::analysis::apply::from_pointer(p, a, o, &spec, name)?;
                Ok(self.answer_plan(plan, a, o, dry))
            }
        })
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
        self.refusing(Feature::Decompile, |p, a, o| {
            render::taint_tsv(p, a, o, spec)
        })
    }

    /// Renders the one-call triage report: the code triage where the
    /// engine decompiles the program, else the triage of its bytes.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn triage_text(&self) -> Result<String, ErrorData> {
        if self.require_loaded()?.refuses(Feature::Decompile).is_some() {
            return self.with_program(|p| Ok(render::file_triage_tsv(p)));
        }
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(render::triage_tsv(p, a, o))
        })
    }

    /// Reports the marks a packer or protector leaves on the image.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn protection_text(&self) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Discover, |p, a, _| {
            Ok(render::protection_tsv(p, a))
        })
    }

    /// Lists the indicators the program holds, each with where it came from.
    ///
    /// # Arguments
    ///
    /// * `filter` - Kind words, text the value contains and `offset=<n>`,
    ///   comma-separated; empty for every indicator.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or the offset does not read.
    pub(crate) fn iocs_text(&self, filter: &str) -> Result<String, ErrorData> {
        self.refusing(Feature::Decompile, |p, a, o| {
            render::iocs_tsv(p, a, o, filter)
        })
    }

    /// Lists every call site of a function or import with its arguments.
    ///
    /// # Arguments
    ///
    /// * `spec` - `<callee>[,aN<op><value>]...[,offset=<n>]`.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, it does not decompile, or the spec is
    /// refused.
    pub(crate) fn calls_text(&self, spec: &str) -> Result<String, ErrorData> {
        self.refusing(Feature::Decompile, |p, a, o| {
            render::calls_tsv(p, a, o, spec)
        })
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(render::asserted_fields_tsv(p, a, o, filter))
        })
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
        self.with_analysis(Feature::Decompile, |p, a, _| {
            Ok(render::source_tree_tsv(p, a, filter))
        })
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
        let a = self.analysis(Feature::Decompile)?;
        Ok(render::class_ids_tsv(&a, filter))
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
    /// When no binary is loaded, borer does not disassemble its
    /// architecture, or the path is a device or does not read.
    pub(crate) fn script_text(&self, path: &str) -> Result<String, ErrorData> {
        let code = read_spec_file(path, "a Rhai script")?;
        let program = self.require_loaded()?;
        if let Some(why) = program.refuses(Feature::Disasm) {
            return Err(err_params(why));
        }
        let a = self.analysis_or_empty();
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
        let a = self.analysis(Feature::Decompile)?;
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
    /// * `asked` - The URI as asked, for the page it asks for.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the offset does not parse.
    pub(crate) fn fieldrefs_text(&self, spec: &str, asked: &Asked) -> Result<String, ErrorData> {
        /// Most rows one read returns: 500 rows of a common offset like
        /// `0x10` ran past 20 KB, a page more than one question needs.
        const PAGE: usize = 200;
        let (offset_text, filter) = spec.split_once(',').unwrap_or((spec, ""));
        let offset = parse_field_offset(offset_text.trim()).map_err(err_params)?;
        let again = asked.again();
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(borer_engine::analysis::fieldrefs::field_refs_tsv(
                p,
                a,
                o,
                offset,
                filter.trim(),
                asked.window(PAGE, &again),
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
        self.with_analysis(Feature::Decompile, |p, a, _| {
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
            borer::index::grep_tsv(&index, a, o, text, "", asked.window(PAGE, &again))
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
            let filter = crate::params::Filter::new(Some("e"));
            let filtered = spans
                .iter()
                .filter(|&s| crate::strwalk::row_matches(p, &crate::strwalk::StringRow::Span(*s), &filter));
            let scan = fastest(3, || {
                let n = spans
                    .iter()
                    .filter(|&s| {
                        crate::strwalk::row_matches(p, &crate::strwalk::StringRow::Span(*s), &filter)
                    })
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
            match self.function_entry(p, a, what) {
                Ok(entry) => Ok(borer_engine::analysis::schema::schema_tsv(p, a, o, entry)
                    .unwrap_or_else(|| {
                        format!(
                            "# {} hands no stream to its calls: not a deserializer\n",
                            borer_engine::analysis::name_of(a, o, entry)
                        )
                    })),
                Err(_) => borer_engine::analysis::schema::class_schema_tsv(p, a, o, what)
                    .ok_or_else(|| {
                        format!(
                            "{} is neither a function nor a class whose virtuals read a stream",
                            borer_engine::text::quoted(what)
                        )
                    }),
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
            match self.function_entry(p, a, what) {
                Ok(entry) => Ok(borer_engine::analysis::encode::encoding_tsv(p, a, o, entry)
                    .unwrap_or_else(|| {
                        format!(
                            "# {} hands its stream nothing: not a serializer\n",
                            borer_engine::analysis::name_of(a, o, entry)
                        )
                    })),
                Err(_) => borer_engine::analysis::encode::class_encoding_tsv(p, a, o, what)
                    .ok_or_else(|| {
                        format!(
                            "{} is neither a function nor a class whose virtuals write a stream",
                            borer_engine::text::quoted(what)
                        )
                    }),
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
        self.with_analysis(Feature::Discover, |p, a, o| {
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
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
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(borer_engine::analysis::about::about_tsv(p, a, o, name))
        })
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
        let a = self.analysis(Feature::Decompile)?;
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
    /// * `asked` - The URI as asked, for the page it asks for.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn attrs_text(&self, filter: &str, asked: &Asked) -> Result<String, ErrorData> {
        /// Most rows one read returns, where the renderer pages too.
        const PAGE: usize = 200;
        let again = asked.again();
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(borer_engine::analysis::attributes::catalog_tsv(
                p,
                a,
                o,
                filter.trim(),
                asked.window(PAGE, &again),
            ))
        })
    }

    /// Lists every class that registered a wire id, with its named fields
    /// and the functions that test for the id.
    ///
    /// # Arguments
    ///
    /// * `filter` - Case-insensitive substring of the class name; empty for all.
    /// * `asked` - The URI as asked, for the page it asks for.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn messages_text(&self, filter: &str, asked: &Asked) -> Result<String, ErrorData> {
        /// Most rows one read returns, where the renderer pages too.
        const PAGE: usize = 200;
        let again = asked.again();
        self.with_analysis(Feature::Decompile, |p, a, o| {
            Ok(borer_engine::analysis::messages::catalog_tsv(
                p,
                a,
                o,
                filter.trim(),
                asked.window(PAGE, &again),
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
        if let Some(why) = borer_engine::program::unusable_path(Path::new(path)) {
            return Err(err_params(format!(
                "{why}; give a path to an anchors manifest"
            )));
        }
        if let Ok(meta) = std::fs::metadata(path)
            && meta.is_file()
            && meta.len() > MANIFEST_MAX
        {
            return Err(err_params(format!(
                "{short} is {} bytes, past the {MANIFEST_MAX} one read takes; split the manifest or judge it with the CLI's anchors",
                meta.len()
            )));
        }
        let text = read_spec_file(
            path,
            "an anchors manifest (field, vconst, function, encode and decode lines)",
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
                .filter(|c| c.trim_start().starts_with('?'))
                .count();
            let empty = o.names.is_empty()
                && o.comments.is_empty()
                && o.types.is_empty()
                && o.applied.is_empty()
                && o.prototypes.is_empty()
                && o.vars.is_empty();
            (
                format!(
                    "{} names, {} comments ({open} open questions), {} types, {} typed globals, {} prototypes",
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
        let a = self.analysis(Feature::Decompile)?;
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

/// Splits a trailing `,out=<path>` off an export's spec.
///
/// # Arguments
///
/// * `spec` - The spec as the URI carries it.
///
/// # Returns
///
/// The spec without it, and the path when one was given.
fn export_target(spec: &str) -> (&str, Option<&str>) {
    match spec.rsplit_once(",out=") {
        Some((rest, path)) if !path.trim().is_empty() => (rest, Some(path.trim())),
        _ => (spec, None),
    }
}

/// Writes an export whole to the path asked for, or answers it as text.
///
/// A file a reader loads as it is (a YARA rule, an x64dbg database) has to
/// reach it whole, without the paging and evidence lines a text answer
/// carries, so `out=<path>` writes it and answers where.
///
/// # Arguments
///
/// * `text` - The export.
/// * `out` - Where to write it, `None` to answer it.
///
/// # Errors
///
/// When the file cannot be written.
fn export(text: String, out: Option<&str>) -> Result<String, ErrorData> {
    let Some(path) = out else {
        return Ok(text);
    };
    std::fs::write(path, text.as_bytes())
        .map_err(|e| err_params(format!("cannot write {path}: {e}")))?;
    Ok(format!("wrote {} bytes to {path}\n", text.len()))
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

    use super::{ABOUT_NEEDS_A_NAME, Asked, BorerServer};

    /// A resource handler, as `read_resource` calls it with the URI's argument.
    type Handler = fn(&BorerServer, &str) -> Result<String, ErrorData>;

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
            .fieldrefs_text("0x10", &Asked::whole("borer://fieldrefs/0x10"))
            .expect("lists the sites");
        assert!(
            out.starts_with("# 250 sites touch [reg+0x10], showing 200 from 0\n"),
            "{out}"
        );
        assert!(out.contains("offset=200"), "{out}");
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
                |server, text| server.grep_text(text, &Asked::whole("borer://grep/")),
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
            assert_eq!(e.message, crate::state::NO_BINARY);
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
