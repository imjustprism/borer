//! The tools that load a binary, its PDB or a saved project, and the one
//! that restarts the server in place.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use borer::project::Identity;
use borer_engine::layout::Layout;
use borer_engine::num;
use borer_engine::program::{Feature, Program};
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::catalog::template_names;
use crate::errors::{err_internal, err_params};
use crate::params::{FetchPdbParams, LoadBinaryParams, LoadProjectParams, SaveProjectParams};
use crate::state::{RawLoad, fault_text, lock, read_lock, write_lock};
use crate::symsrv;

/// The line `load_binary` ends with: the one call that answers what the
/// first ten of a triage would, where `binary_info` would only repeat the
/// summary.
pub(crate) const LOAD_NEXT: &str = "# next: query borer://triage (a whole triage in one call)\n";

/// Environment variable naming the largest file borer loads, in bytes
/// or with a `K`, `M` or `G` suffix (binary units); `0` lifts the limit.
pub(crate) const MAX_FILE_ENV: &str = "BORER_MAX_FILE";

/// The largest file loaded when `BORER_MAX_FILE` sets none: 1 GiB.
///
/// A file is read into memory whole and analysis takes many times its
/// size, so past this a load would end in an allocator abort, not a
/// message.
const MAX_FILE_DEFAULT: u64 = 1 << 30;

/// Reads a `BORER_MAX_FILE` value.
///
/// # Arguments
///
/// * `value` - The variable's value, `None` when it is unset.
///
/// # Returns
///
/// The limit in bytes: [`MAX_FILE_DEFAULT`] when unset or unreadable,
/// `u64::MAX` at `0`.
pub(crate) fn max_file_size(value: Option<&str>) -> u64 {
    let Some(text) = value.map(str::trim) else {
        return MAX_FILE_DEFAULT;
    };
    let (digits, shift) = match text.chars().last().map(|c| c.to_ascii_uppercase()) {
        Some('K') => (&text[..text.len() - 1], 10),
        Some('M') => (&text[..text.len() - 1], 20),
        Some('G') => (&text[..text.len() - 1], 30),
        Some(_) | None => (text, 0),
    };
    match digits.trim().parse::<u64>() {
        Ok(0) => u64::MAX,
        Ok(n) => n
            .checked_shl(shift)
            .filter(|v| v >> shift == n)
            .unwrap_or(u64::MAX),
        Err(_) => MAX_FILE_DEFAULT,
    }
}

/// Refuses a file larger than borer loads, before it is read.
///
/// A path that names no file (or a `<file>@<offset>` slice) passes, so
/// the load says what is wrong with it.
///
/// # Arguments
///
/// * `path` - The file asked for.
/// * `max` - The largest size loaded, in bytes ([`max_file_size`]).
///
/// # Errors
///
/// When the file is larger than `max`, naming both sizes, the variable
/// that raises the limit and the ways to load a part.
pub(crate) fn file_fits(path: &Path, max: u64) -> Result<(), String> {
    match std::fs::metadata(path) {
        Ok(meta) if meta.is_file() && meta.len() > max => Err(format!(
            "{} is {} bytes, past the {max}-byte limit: borer reads a file into memory whole and its analysis takes several times that. Set {MAX_FILE_ENV} (bytes, or 4G; 0 for no limit) to load it anyway, or load a part: <file>@<offset> for an embedded program, or arch with regions for raw ranges",
            borer_engine::text::short_path(&path.display().to_string()),
            meta.len()
        )),
        Ok(_) | Err(_) => Ok(()),
    }
}

/// Says where a relative path was looked for, when it was relative.
///
/// The server's working directory is the client's choice (often the
/// system directory or `/`), not one an agent can know.
///
/// # Arguments
///
/// * `path` - The path asked for.
/// * `cwd` - The server's working directory, `None` when unknown.
///
/// # Returns
///
/// A `; ...` clause for a relative path, empty for an absolute one.
pub(crate) fn relative_note(path: &Path, cwd: Option<&Path>) -> String {
    if path.is_absolute() {
        return String::new();
    }
    cwd.map_or_else(
        || "; the path is relative and the server's working directory is unknown: pass an absolute path".to_owned(),
        |dir| {
            format!(
                "; the path is relative to the server's working directory {}: pass an absolute path",
                dir.display()
            )
        },
    )
}

#[tool_router(router = load_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Loads a file as the current program and resets analysis and overlay.
    ///
    /// A session's names must not leak into another image, so the overlay
    /// is cleared; a session that has not saved them is told what it lost.
    /// An attached process is mapped onto the new binary
    /// ([`LiveSession::map`]), so live addresses never rebase by a binary
    /// no longer loaded.
    ///
    /// # Arguments
    ///
    /// * `LoadBinaryParams` - Destructured tool parameters (see its field docs).
    ///
    /// A refused load changes nothing: the program, its names and the
    /// load options of the session stay what they were.
    ///
    /// With `arch`, the file is not parsed: its bytes map where `base` or
    /// `regions` say ([`Layout`]), so raw code and memory dumps analyze
    /// with every other tool; without it the load is what it always was.
    ///
    /// # Errors
    ///
    /// Invalid params when the file does not load, the entry offset is
    /// past its end or in no section's file bytes, the stated layout does
    /// not parse or the file cannot hold it, or `entry` and
    /// `entry_file_offset` are both given.
    #[tool(
        description = "Load a PE, ELF or Mach-O file (a fat Mach-O: its x86-64 slice), or any other file as raw bytes, as the current program; returns its summary. pdb=false skips the companion PDB; entry_file_offset overrides the entry; arch maps raw code or a dump.",
        annotations(
            read_only_hint = false,
            destructive_hint = true,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn load_binary(
        &self,
        Parameters(LoadBinaryParams {
            path,
            entry_file_offset,
            pdb,
            arch,
            base,
            entry,
            regions,
        }): Parameters<LoadBinaryParams>,
    ) -> Result<String, ErrorData> {
        let apply_pdb = pdb.unwrap_or(true);
        if entry.is_some() && entry_file_offset.is_some() {
            return Err(err_params(
                "entry and entry_file_offset both name the entry; give one",
            ));
        }
        let raw = RawLoad {
            arch,
            base,
            entry,
            regions,
        };
        let layout = Layout::parse(
            raw.arch.map(Into::into),
            raw.base.as_deref(),
            raw.entry.as_deref(),
            raw.regions.as_deref(),
        )
        .map_err(|e| err_params(format!("load failed: {e:#}")))?;
        file_fits(
            Path::new(&path),
            max_file_size(std::env::var(MAX_FILE_ENV).ok().as_deref()),
        )
        .map_err(err_params)?;
        let loaded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let path = PathBuf::from(&path);
            match &layout {
                Some(layout) => Program::load_layout(&path, layout),
                None => {
                    Program::load_with_symsrv(&path, apply_pdb, symsrv::cache_dir().as_deref())
                }
            }
        }))
        .map_err(|e| {
            err_internal(format!(
                "loading faulted on this file: {}. The session is still up and keeps the program it had.",
                fault_text(e.as_ref())
            ))
        })?;
        let mut program = loaded.map_err(|e| {
            err_params(format!(
                "load failed: {e:#}{}",
                relative_note(Path::new(&path), std::env::current_dir().ok().as_deref())
            ))
        })?;
        if let Some(off) = entry_file_offset {
            if off >= num::from_usize(program.bytes.len()) {
                return Err(err_params(format!(
                    "entry_file_offset {off:#x} beyond file size {:#x}",
                    program.bytes.len()
                )));
            }
            let va = program.offset_to_va(off).ok_or_else(|| {
                err_params(format!(
                    "entry_file_offset {off:#x} is in no section's file bytes, so it maps to no address; sections: {}",
                    program.section_list()
                ))
            })?;
            program.entry = Some(va);
        }
        let mut summary = program.summary();
        let dropped = std::mem::take(&mut *write_lock(&self.overlay));
        if !dropped.names.is_empty() || !dropped.comments.is_empty() {
            let previous = self.loaded().map_or_else(
                || "the previous binary".to_owned(),
                |p| p.path.display().to_string(),
            );
            summary.push_str(&format!(
                "note: discarded {} name(s) and {} comment(s) set on {previous}; save_project before load_binary keeps them\n",
                dropped.names.len(),
                dropped.comments.len()
            ));
        }
        let (packs, notes) = self.packs_for(&program);
        for note in notes {
            let _ = writeln!(summary, "{note}");
        }
        *write_lock(&self.pdb_applied) = apply_pdb;
        *write_lock(&self.entry_file_offset) = entry_file_offset;
        *write_lock(&self.raw_load) = raw;
        if let Some(s) = lock(&self.live).as_mut() {
            let mapped = s.map(Some(&program));
            let _ = write!(
                summary,
                "live {} (pid {}): {mapped}",
                s.process.name(),
                s.process.pid()
            );
        }
        if !summary.ends_with('\n') {
            summary.push('\n');
        }
        summary.push_str(LOAD_NEXT);
        *write_lock(&self.program_packs) = packs;
        *write_lock(&self.program) = Some(Arc::new(program));
        *write_lock(&self.analysis) = None;
        *write_lock(&self.strings) = None;
        Ok(summary)
    }

    /// Fetches the loaded PE's missing companion PDB from a symbol server.
    ///
    /// Off by default like every side effect: a dry run says the URL and
    /// the cache destination and touches nothing. A PDB of this build
    /// already on disk (beside the binary, at its recorded path, or in the
    /// cache) is named instead of fetched: a load with `pdb=false` leaves
    /// it unapplied. A confirmed fetch checks
    /// the cache first (a hit answers without the network), downloads with
    /// `curl`, and keeps the file only when its GUID and age name this
    /// binary, so a wrong or hostile download is discarded, never cached.
    /// The landed PDB applies on the next `load_binary`.
    ///
    /// # Arguments
    ///
    /// * `FetchPdbParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded, the image names no PDB, no
    /// cache directory resolves, the name or server is refused, or the
    /// fetch or its validation fails.
    #[tool(
        description = "Fetch the loaded PE's missing companion PDB over https from the configured symbol server (Microsoft's, or BORER_SYMBOL_SERVER; public hosts only) into the cache; guid+age must match; dry-run unless dry_run=false; the next load_binary applies it.",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = true
        )
    )]
    pub(crate) fn fetch_pdb(
        &self,
        Parameters(FetchPdbParams { dry_run }): Parameters<FetchPdbParams>,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| {
            if let Some(outcome) = &p.pdb
                && matches!(outcome, borer_engine::pdb::Outcome::Applied { .. })
            {
                return Ok(format!(
                    "the companion pdb already applied ({}); nothing to fetch",
                    outcome.render()
                ));
            }
            let Some(record) = p.pdb_record.as_ref() else {
                return Err("the loaded binary names no companion pdb (no codeview record: not a PE, or a build without debug info)".to_owned());
            };
            let Some(root) = symsrv::cache_dir() else {
                return Err(format!(
                    "no cache directory: set {}, LOCALAPPDATA, XDG_CACHE_HOME or HOME",
                    symsrv::CACHE_ENV
                ));
            };
            if let Some(found) = borer_engine::pdb::resolved(&p.path, record, Some(&root)) {
                return Ok(format!(
                    "{} is this build's pdb and did not apply to this load (load_binary passed pdb=false, or it landed since): load_binary with pdb=true applies it; nothing to fetch",
                    found.display()
                ));
            }
            symsrv::obtain(
                record,
                &root,
                &symsrv::server(),
                dry_run.unwrap_or(true),
                symsrv::curl,
            )
        })
    }

    /// Returns the program summary.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    #[tool(
        description = "Summary of the current program: format, arch, entry, sections with entropy, imports/exports.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn binary_info(&self) -> Result<String, ErrorData> {
        self.with_program(|p| {
            let more = if p.refuses(Feature::Decompile).is_some() {
                "borer://triage reads the whole file in one call".to_owned()
            } else {
                template_names()
            };
            Ok(format!("{}# more: {more}\n", p.summary()))
        })
    }

    /// Restarts the server on the binary at its own path, keeping the session.
    ///
    /// The answer is written first; the hand-over itself follows it
    /// ([`Self::call_tool`], [`HandOver`]): the relay gives this worker no
    /// request after this one, the worker ends once this reply and those of
    /// the requests before it are written, and the relay starts the binary
    /// again, which resumes the session ([`relay`]). A request the client
    /// sends as soon as the reply arrives waits in the relay for it.
    ///
    /// An attached process is not carried over: its handle and watches end
    /// with this worker, and the reply says so, so the agent attaches again
    /// rather than meeting "no process attached" on its next live call.
    ///
    /// # Errors
    ///
    /// Never.
    #[tool(
        description = "Restart the server on the binary at its path, keeping the session, the loaded file and its names and comments: use after rebuilding borer, instead of restarting the client.",
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = false,
            open_world_hint = false
        )
    )]
    pub(crate) fn reload(&self) -> Result<String, ErrorData> {
        let exe = std::env::args().next().unwrap_or_default();
        let loaded = self.loaded().map(|p| p.path.display().to_string());
        let live = lock(&self.live).as_ref().map_or_else(String::new, |s| {
            format!(
                "; the live session with {} (pid {}) and its {} watch(es) end with this server: live_attach again once it is up",
                s.process.name(),
                s.process.pid(),
                s.snapshots.len()
            )
        });
        Ok(format!(
            "reloading borer from {exe}{}{live}; the tool list is announced again once the new server is up",
            loaded.map_or_else(String::new, |p| format!(", reloading {p}"))
        ))
    }

    /// Saves the overlay to a JSON project file.
    ///
    /// # Arguments
    ///
    /// * `SaveProjectParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or the path is refused (outside
    /// the output root, not `.json`, or an existing file without
    /// `overwrite`); internal error when the file cannot be written.
    #[tool(
        description = "Save the annotation overlay (names, comments, types) to a .json project file, keyed to the binary by its SHA-256, under the output root (BORER_OUTPUT_DIR, else the binary's project directory); an existing file is refused unless overwrite=true; answers the absolute path written.",
        annotations(
            read_only_hint = false,
            destructive_hint = true,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn save_project(
        &self,
        Parameters(SaveProjectParams { path, overwrite }): Parameters<SaveProjectParams>,
    ) -> Result<String, ErrorData> {
        let program = self.require_loaded()?;
        let existing = borer::output::Existing::from_flag(overwrite);
        let path = borer::output::for_program(&program, &path, &["json"], existing)
            .map_err(err_params)?
            .display()
            .to_string();
        let pf = borer::project::ProjectFile::from_overlay(
            &program.path.display().to_string(),
            Some(borer::project::identity(&program.bytes)),
            &read_lock(&self.overlay),
        );
        pf.save(&path, existing).map_err(err_internal)?;
        let vars: usize = pf.vars.values().map(std::collections::BTreeMap::len).sum();
        let stated = if pf.prototypes.is_empty() && vars == 0 {
            String::new()
        } else {
            format!(" + {} prototypes + {vars} variables", pf.prototypes.len())
        };
        Ok(format!(
            "saved {} names + {} comments + {} types{stated} to {path}",
            pf.names.len(),
            pf.comments.len(),
            pf.types.len()
        ))
    }

    /// Loads a JSON project file into the overlay, replacing it.
    ///
    /// A project's addresses belong to the binary it was saved for, and
    /// loading replaces every annotation the session holds, so a project
    /// saved for another binary ([`borer::project::ProjectFile::identify`]:
    /// by its SHA-256, or by its path in a project older than the hash) is
    /// refused, leaving the overlay as it was, unless `force` says to load
    /// it anyway; a rebuild is pointed at `borer://carry`, which moves the
    /// names to it, and a project judged by path says so. Either way the
    /// annotations `set_name`, `set_comment` and
    /// `set_type` would refuse of the loaded binary, at an address no
    /// section holds or with blank text, are skipped and listed
    /// ([`borer::project::keep_placeable`]), and the counts said are of what
    /// the overlay then holds.
    ///
    /// # Arguments
    ///
    /// * `LoadProjectParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded, the file does not parse or
    /// states something the overlay cannot hold, or it was saved for
    /// another binary and `force` is not set.
    #[tool(
        description = "Load a JSON project file into the annotation overlay, replacing it. A project saved for another binary (by SHA-256) is refused unless force=true; names, comments and types at addresses no section holds, or blank, are skipped and listed.",
        annotations(
            read_only_hint = false,
            destructive_hint = true,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn load_project(
        &self,
        Parameters(LoadProjectParams { path, force }): Parameters<LoadProjectParams>,
    ) -> Result<String, ErrorData> {
        /// Most left-out annotations the answer names before counting the rest.
        const LEFT_OUT_SHOWN: usize = 8;
        /// Hex digits of a SHA-256 a message shows.
        const HASH_SHOWN: usize = 12;
        let program = self.require_loaded()?;
        let pf = borer::project::ProjectFile::load(&path).map_err(err_params)?;
        let identity = pf.identify(&program);
        let foreign = matches!(identity, Identity::Other | Identity::OtherPath);
        let saved_for = borer_engine::text::short_path(&pf.program);
        let loaded_path = program.path.display().to_string();
        if foreign && !force.unwrap_or(false) {
            let short = |hash: &str| hash.chars().take(HASH_SHOWN).collect::<String>();
            return Err(err_params(match &pf.sha256 {
                Some(saved) => format!(
                    "the project was saved for another build (sha-256 {}... at {saved_for}), but {} is sha-256 {}...; nothing was loaded. Its addresses belong to that build: load it with this project, then borer://carry/{} carries the names to this one; or pass force=true to load the project anyway",
                    short(&borer_engine::text::one_line(saved)),
                    borer_engine::text::short_path(&loaded_path),
                    short(&borer::project::identity(&program.bytes)),
                    borer_engine::text::short_path(&loaded_path.replace('\\', "/"))
                ),
                None => format!(
                    "the project was saved for {saved_for}, but {} is loaded; nothing was loaded. Its addresses belong to that binary: load it first, or pass force=true to load the project anyway",
                    borer_engine::text::short_path(&loaded_path)
                ),
            }));
        }
        let mut loaded = pf.to_overlay().map_err(err_params)?;
        let left_out = borer::project::keep_placeable(&mut loaded, &program);
        let vars: usize = loaded
            .vars
            .values()
            .map(std::collections::BTreeMap::len)
            .sum();
        let stated = if loaded.prototypes.is_empty() && vars == 0 {
            String::new()
        } else {
            format!(
                " + {} prototypes + {vars} variables",
                loaded.prototypes.len()
            )
        };
        let mut said = format!(
            "loaded {} names + {} comments + {} types + {} applied{stated}\n",
            loaded.names.len(),
            loaded.comments.len(),
            loaded.types.len(),
            loaded.applied.len()
        );
        if !left_out.is_empty() {
            let shown = left_out.len().min(LEFT_OUT_SHOWN);
            let _ = writeln!(
                said,
                "# skipped {total} (showing {shown} of {total}): {}",
                left_out[..shown].join(", "),
                total = left_out.len()
            );
        }
        if foreign {
            let _ = writeln!(
                said,
                "# forced: the project was saved for {saved_for}, so its names may sit on other code here"
            );
        }
        if matches!(identity, Identity::PathOnly | Identity::OtherPath) {
            said.push_str("# the project names its binary by path alone (saved before projects recorded its sha-256), so a rebuild at that path loads it too; save_project records the hash\n");
        }
        let before = self.overlay_plain();
        *write_lock(&self.overlay) = loaded;
        self.names_changed(&before);
        Ok(said)
    }
}

#[cfg(test)]
mod tests {
    /// `BORER_MAX_FILE` reads bytes or a binary suffix, `0` lifts the
    /// limit and junk keeps the default; a file past the limit is refused
    /// naming the variable, and one within it, or no file, passes.
    ///
    /// # Panics
    ///
    /// When a value reads otherwise or the refusal is missing.
    #[test]
    fn a_file_past_the_size_limit_is_refused_by_name() {
        use super::{MAX_FILE_DEFAULT, MAX_FILE_ENV, file_fits, max_file_size};
        assert_eq!(max_file_size(None), MAX_FILE_DEFAULT);
        assert_eq!(max_file_size(Some("4096")), 4096);
        assert_eq!(max_file_size(Some("2k")), 2048);
        assert_eq!(max_file_size(Some("3G")), 3 << 30);
        assert_eq!(max_file_size(Some("0")), u64::MAX);
        assert_eq!(max_file_size(Some("lots")), MAX_FILE_DEFAULT);
        assert_eq!(max_file_size(Some("99999999999999G")), u64::MAX);
        let exe = std::env::current_exe().expect("the test binary");
        let refused = file_fits(&exe, 16).expect_err("past the limit");
        assert!(refused.contains(MAX_FILE_ENV), "{refused}");
        assert!(refused.contains("16-byte limit"), "{refused}");
        assert!(file_fits(&exe, u64::MAX).is_ok());
        assert!(file_fits(std::path::Path::new("no/such/file"), 16).is_ok());
    }

    /// A relative path that does not load says the directory it was
    /// looked for in and asks for an absolute one; an absolute one adds
    /// nothing.
    ///
    /// # Panics
    ///
    /// When the note is missing or added to an absolute path.
    #[test]
    fn a_relative_path_names_the_directory_it_was_read_from() {
        let dir = std::env::temp_dir();
        let note = super::relative_note(std::path::Path::new("notepad.exe"), Some(&dir));
        assert!(
            note.contains(&dir.display().to_string()) && note.ends_with("pass an absolute path"),
            "{note}"
        );
        let absolute = dir.join("notepad.exe");
        assert_eq!(super::relative_note(&absolute, Some(&dir)), "");
    }

    /// A refused `load_binary` changes nothing.
    ///
    /// The session keeps the program it had and the load options it was loaded
    /// with. The `pdb` setting was written before the load was tried, so a
    /// failed load with `pdb=false` made the next comparison build skip its
    /// PDB.
    ///
    /// # Panics
    ///
    /// When a refused load changes the session.
    #[test]
    fn a_refused_load_changes_nothing() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let exe = exe.display().to_string();
        let load = |path: &str, pdb: Option<bool>, entry_file_offset: Option<u64>| {
            crate::params::LoadBinaryParams {
                path: path.to_owned(),
                entry_file_offset,
                pdb,
                arch: None,
                base: None,
                entry: None,
                regions: None,
            }
        };
        let server = crate::BorerServer::default();
        server
            .load_binary(rmcp::handler::server::wrapper::Parameters(load(
                &exe,
                Some(true),
                None,
            )))
            .expect("the test binary loads");
        let missing = server.load_binary(rmcp::handler::server::wrapper::Parameters(load(
            "no/such/file.exe",
            Some(false),
            Some(0),
        )));
        assert!(missing.is_err());
        let past = server.load_binary(rmcp::handler::server::wrapper::Parameters(load(
            &exe,
            Some(false),
            Some(u64::MAX),
        )));
        assert!(past.is_err());
        assert!(
            *crate::state::read_lock(&server.pdb_applied),
            "the pdb setting moved"
        );
        assert_eq!(*crate::state::read_lock(&server.entry_file_offset), None);
        assert!(server.loaded().is_some(), "the program was dropped");
    }

    /// `fetch_pdb` names this build's PDB when one is on disk instead of
    /// offering to fetch it.
    ///
    /// A load with `pdb=false` leaves the PDB beside the binary unapplied, and
    /// the dry run offered a download of the file already there. A build
    /// without its PDB on disk has nothing to ask about, and nothing is
    /// asserted.
    ///
    /// # Panics
    ///
    /// When the dry run offers a fetch of a PDB on disk.
    #[test]
    fn fetch_pdb_names_a_pdb_already_on_disk() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let server = crate::BorerServer::default();
        server
            .load_binary(rmcp::handler::server::wrapper::Parameters(
                crate::params::LoadBinaryParams {
                    path: exe.display().to_string(),
                    entry_file_offset: None,
                    pdb: Some(false),
                    arch: None,
                    base: None,
                    entry: None,
                    regions: None,
                },
            ))
            .expect("the test binary loads");
        let on_disk = server.loaded().and_then(|p| {
            let record = p.pdb_record.as_ref()?;
            borer_engine::pdb::resolved(&p.path, record, None)
        });
        if on_disk.is_none() {
            return;
        }
        let said = server
            .fetch_pdb(rmcp::handler::server::wrapper::Parameters(
                crate::params::FetchPdbParams { dry_run: None },
            ))
            .expect("the dry run answers");
        assert!(said.contains("nothing to fetch"), "{said}");
        assert!(!said.contains("would fetch"), "{said}");
    }

    /// `load_project` holds a project to what the annotating tools accept
    /// and refuses one saved for another binary unless forced.
    ///
    /// A name or comment at an address no section holds, a blank one and a
    /// type applied outside every section are skipped and listed, and the
    /// counts said are of what the overlay then holds; a project saved for
    /// another path is refused and leaves the overlay as it was, and with
    /// `force` it loads and says so.
    ///
    /// # Panics
    ///
    /// When an entry no section holds is loaded, the counts miss, or a
    /// foreign project loads unforced.
    #[test]
    fn load_project_skips_what_set_name_refuses_and_guards_another_binary() {
        use crate::params::LoadProjectParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(
            vec![0xcc; 0x200],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text, data],
        );
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let dir = std::env::temp_dir().join(format!("borer-load-project-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let write = |name: &str, program: &str| {
            let path = dir.join(name);
            let json = format!(
                r#"{{"program":"{program}","names":{{"0x1010":"f","0x0":"zero","0x5000":"far"}},"comments":{{"0x2000":"c","0x2004":"   "}},"applied":{{"0x9000":"u32"}}}}"#
            );
            std::fs::write(&path, json).expect("the project is written");
            path.display().to_string()
        };
        let load = |path: String, force: Option<bool>| {
            server.load_project(Parameters(LoadProjectParams { path, force }))
        };
        let out = load(write("same.json", ""), None).expect("loads");
        assert!(
            out.starts_with("loaded 1 names + 1 comments + 0 types + 0 applied\n"),
            "{out}"
        );
        assert!(
            out.contains(
                "# skipped 4 (showing 4 of 4): name at 0x0 (in no section), name at 0x5000 (in no section), comment at 0x2004 (blank), type at 0x9000 (in no section)"
            ),
            "{out}"
        );
        let held = || {
            let o = crate::state::read_lock(&server.overlay);
            (
                o.names.keys().copied().collect::<Vec<_>>(),
                o.comments.keys().copied().collect::<Vec<_>>(),
                o.applied.len(),
            )
        };
        assert_eq!(held(), (vec![0x1010], vec![0x2000], 0));
        crate::state::write_lock(&server.overlay).names.clear();
        let foreign = write("foreign.json", "C:/elsewhere/other.exe");
        let refused = load(foreign.clone(), None).expect_err("a foreign project loaded");
        assert!(
            refused
                .message
                .contains("the project was saved for C:/elsewhere/other.exe"),
            "{}",
            refused.message
        );
        assert!(
            refused.message.contains("force=true"),
            "{}",
            refused.message
        );
        assert_eq!(held(), (vec![], vec![0x2000], 0));
        let forced = load(foreign, Some(true)).expect("a forced load loads");
        assert!(forced.starts_with("loaded 1 names"), "{forced}");
        assert!(
            forced.contains("# forced: the project was saved for C:/elsewhere/other.exe"),
            "{forced}"
        );
        assert_eq!(held(), (vec![0x1010], vec![0x2000], 0));
    }

    /// `load_binary` ends by naming the call that answers a whole triage,
    /// where `binary_info`, which the instructions sent an agent to next,
    /// only repeats the summary.
    ///
    /// # Panics
    ///
    /// When the file does not load or the answer ends otherwise.
    #[test]
    fn load_binary_points_at_the_triage() {
        use crate::params::LoadBinaryParams;
        use rmcp::handler::server::wrapper::Parameters;
        let path = std::env::temp_dir().join(format!("borer-load-next-{}.bin", std::process::id()));
        std::fs::write(&path, [0xc3u8; 64]).expect("the file is written");
        let said = crate::BorerServer::default().load_binary(Parameters(LoadBinaryParams {
            path: path.display().to_string(),
            entry_file_offset: None,
            pdb: Some(false),
            arch: None,
            base: None,
            entry: None,
            regions: None,
        }));
        std::fs::remove_file(&path).expect("the file is removed");
        let said = said.expect("any file loads");
        assert!(said.ends_with(super::LOAD_NEXT), "{said}");
    }

    /// `load_binary` with `arch` maps a headerless file where `base` says.
    ///
    /// The code tools then read it; without `arch` the same file loads as
    /// it always did, with no code; a layout that does not parse or fit,
    /// or an entry given twice, is refused and changes nothing.
    ///
    /// # Panics
    ///
    /// When a load answers otherwise or a refused one moves the session.
    #[test]
    fn load_binary_maps_raw_code_at_a_stated_layout() {
        use crate::params::FunctionsParams;
        use crate::params::LoadBinaryParams;
        use crate::params::RawArch;
        use crate::state::RawLoad;
        use rmcp::handler::server::wrapper::Parameters;
        // ASM: call 0x1000b; add rax, 1; ret; int3; mov eax, 42; ret
        const CODE: [u8; 17] = [
            0xe8, 0x06, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc0, 0x01, 0xc3, 0xcc, 0xb8, 0x2a, 0x00,
            0x00, 0x00, 0xc3,
        ];
        let path =
            std::env::temp_dir().join(format!("borer-raw-layout-{}.bin", std::process::id()));
        std::fs::write(&path, CODE).expect("the file is written");
        let shown = path.display().to_string();
        let load = |raw: RawLoad, entry_file_offset: Option<u64>| {
            crate::BorerServer::default().load_binary(Parameters(LoadBinaryParams {
                path: shown.clone(),
                entry_file_offset,
                pdb: None,
                arch: raw.arch,
                base: raw.base,
                entry: raw.entry,
                regions: raw.regions,
            }))
        };
        let plain = load(RawLoad::default(), None);
        let server = crate::BorerServer::default();
        let stated = RawLoad {
            arch: Some(RawArch::X64),
            base: Some("0x10000".to_owned()),
            entry: None,
            regions: None,
        };
        let mapped = server.load_binary(Parameters(LoadBinaryParams {
            path: shown.clone(),
            entry_file_offset: None,
            pdb: None,
            arch: stated.arch,
            base: stated.base.clone(),
            entry: None,
            regions: None,
        }));
        let functions = server.functions(Parameters(FunctionsParams {
            filter: None,
            sort: None,
            offset: None,
            limit: None,
            count_only: None,
        }));
        let past = server.load_binary(Parameters(LoadBinaryParams {
            path: shown.clone(),
            entry_file_offset: None,
            pdb: Some(false),
            arch: Some(RawArch::X64),
            base: None,
            entry: None,
            regions: Some("0x10000@0:0x40".to_owned()),
        }));
        let twice = load(
            RawLoad {
                entry: Some("0x10000".to_owned()),
                ..stated.clone()
            },
            Some(0),
        );
        let no_arch = load(
            RawLoad {
                base: Some("0x10000".to_owned()),
                ..RawLoad::default()
            },
            None,
        );
        std::fs::remove_file(&path).expect("the file is removed");

        let plain = plain.expect("any file loads");
        assert!(plain.contains("arch: unknown\n"), "{plain}");
        let mapped = mapped.expect("the layout maps");
        assert!(
            mapped.contains("format:  raw   arch: x86-64 (64-bit)\n"),
            "{mapped}"
        );
        assert!(mapped.contains("entry: 0x10000\n"), "{mapped}");
        assert!(mapped.contains("kind stated layout"), "{mapped}");
        let functions = functions.expect("it lists");
        assert!(
            functions.contains("0x10000 ") && functions.contains("0x1000b "),
            "{functions}"
        );
        let past = past.expect_err("refused").message;
        assert!(
            past.contains("runs past the end of the file at 0x11"),
            "{past}"
        );
        assert!(
            twice.expect_err("refused").message.contains("give one"),
            "both entries"
        );
        assert!(
            no_arch.expect_err("refused").message.contains("need arch"),
            "base alone"
        );
        assert_eq!(
            *crate::state::read_lock(&server.raw_load),
            stated,
            "the refusal moved it"
        );
        assert!(server.loaded().is_some_and(|p| p.entry == Some(0x10000)));
    }
}
