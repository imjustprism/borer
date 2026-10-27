//! Writing the whole-binary exports, for `export` and `decompile_batch(out=)`.
//!
//! [`borer_engine::analysis::decompile::export`] goes to a C file, the mod
//! SDK ([`borer_engine::analysis::modsdk`]) to a C++ header, a Cheat
//! Engine table and a ReClass.NET project. The function definitions stream to a sibling `.part` file while they
//! are rendered, and the file is then written as the hoisted declarations
//! followed by that part, so memory never holds the file.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::Path;

use anyhow::Context as _;
use borer_engine::analysis::decompile::export::{BUDGET_BLOCKS, Hoisted, Library, export};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Program;
use borer_engine::text::short_path;

use crate::output::{Existing, create};

/// What an export wrote.
#[derive(Debug)]
pub struct Written {
    /// The hoisted declarations and the function counts.
    pub hoisted: Hoisted,
    /// Bytes in the file.
    pub bytes: u64,
    /// Requested entries no function starts at, even after gap recovery.
    pub unmatched: Vec<u64>,
}

impl Written {
    /// Says what was written, on one line.
    ///
    /// # Arguments
    ///
    /// * `out` - The file's path.
    #[must_use]
    pub fn line(&self, out: &str) -> String {
        let h = &self.hoisted;
        let cut = if h.cut == 0 {
            String::new()
        } else {
            format!(
                ", {} cut over the budget of {BUDGET_BLOCKS} blocks a function",
                h.cut
            )
        };
        let missed = if self.unmatched.is_empty() {
            String::new()
        } else {
            let list: Vec<String> = self.unmatched.iter().map(|va| format!("{va:#x}")).collect();
            format!("; no function starts at {}", list.join(", "))
        };
        format!(
            "wrote {} functions to {} ({} bytes); {} did not decompile{cut}, {} library functions and stubs left out, {} declarations stated two ways kept the first",
            h.written,
            short_path(out),
            self.bytes,
            h.failed,
            h.left_out,
            h.conflicts
        ) + missed.as_str()
    }
}

/// Exports every function of a binary as one C file at `out`.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names, types and comments to apply.
/// * `library` - Whether library code is written.
/// * `out` - The C file to write.
/// * `existing` - Whether a regular file already at `out` is replaced;
///   a link there is never written through.
///
/// # Returns
///
/// What was written.
///
/// # Errors
///
/// When the file or its `.part` beside it cannot be written, a file is
/// at `out` and `existing` keeps it, or the request's deadline passed while
/// the functions were decompiled ([`borer_engine::cancel::Cancel`]): then
/// the `.part` is removed and whatever is at `out` stays untouched.
pub fn write_c(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    library: Library,
    out: &str,
    existing: Existing,
) -> anyhow::Result<Written> {
    write_with_set(program, analysis, overlay, library, None, out, existing)
}

/// Exports the entries in `only`, or every function when `only` is `None`.
///
/// The file is the same shape as [`write_c`]: declarations those functions
/// hoist, then their bodies. An entry that is not a written function is
/// skipped.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names, types and comments to apply.
/// * `library` - Whether library code is written.
/// * `only` - Entries to write, or every function when `None`.
/// * `out` - The C file to write.
/// * `existing` - Whether a regular file already at `out` is replaced;
///   a link there is never written through.
///
/// # Returns
///
/// What was written.
///
/// # Errors
///
/// When the file or its `.part` beside it cannot be written, or a file
/// is at `out` and `existing` keeps it.
pub fn write_entries(
    program: &Program,
    analysis: &mut Analysis,
    overlay: &Overlay,
    library: Library,
    only: Option<&[u64]>,
    out: &str,
    existing: Existing,
) -> anyhow::Result<Written> {
    let mut unmatched = Vec::new();
    if let Some(entries) = only {
        let sorted: BTreeSet<u64> = entries.iter().copied().collect();
        for va in sorted {
            let thumb = (program.arch == borer_engine::program::Arch::Arm)
                .then(|| analysis.function(va & !1))
                .flatten();
            let known = analysis.function(va).or(thumb);
            if known.is_none() && analysis.start_gap_function(program, va).is_none() {
                unmatched.push(va);
            }
        }
    }
    let set = only.map(|entries| entries.iter().copied().collect::<BTreeSet<_>>());
    let mut written = write_with_set(
        program,
        analysis,
        overlay,
        library,
        set.as_ref(),
        out,
        existing,
    )?;
    written.unmatched = unmatched;
    Ok(written)
}

/// Writes the exported C file for `set` (or every function when `None`).
///
/// # Errors
///
/// Fails when `out` cannot be created or written, or already exists under [`Existing::Keep`].
fn write_with_set(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    library: Library,
    set: Option<&BTreeSet<u64>>,
    out: &str,
    existing: Existing,
) -> anyhow::Result<Written> {
    let path = Path::new(out);
    if let Some(why) = borer_engine::program::unusable_path(path) {
        anyhow::bail!("{why}; nothing was written");
    }
    let part_name = format!("{out}.part");
    let part = Path::new(&part_name);
    let shown = short_path(out);
    if existing == Existing::Keep && std::fs::symlink_metadata(path).is_ok() {
        anyhow::bail!("{shown} exists; nothing was written");
    }
    let mut bodies = std::io::BufWriter::new(
        create(part, Existing::Replace).with_context(|| format!("creating {shown}.part"))?,
    );
    let hoisted = export(program, analysis, overlay, library, set, &mut |text| {
        bodies
            .write_all(text.as_bytes())
            .with_context(|| format!("writing {shown}.part"))
    })?;
    bodies
        .flush()
        .with_context(|| format!("writing {shown}.part"))?;
    drop(bodies);
    if borer_engine::cancel::Cancel::raised() {
        std::fs::remove_file(part).with_context(|| format!("removing {shown}.part"))?;
        anyhow::bail!(
            "the request's deadline passed before every function was decompiled, so {shown} was left as it was; export fewer functions (a filter or a list) or raise BORER_DEADLINE_SECS"
        );
    }
    let binary = short_path(&program.path.display().to_string());
    let mut file = std::io::BufWriter::new(
        create(path, existing).with_context(|| format!("creating {shown}"))?,
    );
    file.write_all(hoisted.head(&binary).as_bytes())
        .with_context(|| format!("writing {shown}"))?;
    let mut from = std::fs::File::open(part).with_context(|| format!("reading {shown}.part"))?;
    std::io::copy(&mut from, &mut file).with_context(|| format!("writing {shown}"))?;
    file.flush().with_context(|| format!("writing {shown}"))?;
    drop(from);
    std::fs::remove_file(part).with_context(|| format!("removing {shown}.part"))?;
    let bytes = std::fs::metadata(path)
        .with_context(|| format!("reading {shown}"))?
        .len();
    Ok(Written {
        hoisted,
        bytes,
        unmatched: Vec::new(),
    })
}

/// A file a mod author loads, written from the program's mod SDK
/// ([`borer_engine::analysis::modsdk`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModFile {
    /// A C++ header: classes, offsets, vtables and addresses (`.h`).
    Header,
    /// A Cheat Engine table of the globals and their fields (`.ct`).
    CheatTable,
    /// A ReClass.NET project of the class layouts (`.rcnet`).
    ReClass,
}

impl ModFile {
    /// Every mod file, with the extension that names it.
    pub const ALL: [(ModFile, &'static str); 3] = [
        (ModFile::Header, "h"),
        (ModFile::CheatTable, "ct"),
        (ModFile::ReClass, "rcnet"),
    ];

    /// Returns the mod file a path's extension names.
    ///
    /// # Arguments
    ///
    /// * `path` - The file to write; its extension in any case.
    ///
    /// # Returns
    ///
    /// The kind, or `None` for another extension (a `.c` export).
    #[must_use]
    pub fn of_path(path: &str) -> Option<Self> {
        let ext = Path::new(path).extension()?.to_str()?.to_ascii_lowercase();
        Self::ALL
            .iter()
            .find(|(_, e)| *e == ext)
            .map(|(kind, _)| *kind)
    }

    /// Returns what the file holds, for the line saying it was written.
    fn what(self) -> &'static str {
        match self {
            ModFile::Header => "mod SDK header",
            ModFile::CheatTable => "Cheat Engine table",
            ModFile::ReClass => "ReClass.NET project",
        }
    }
}

/// Writes the program's mod SDK as each file asked for.
///
/// The SDK is gathered once and every file rendered before any is
/// written, so a request whose deadline passes writes nothing.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and types, which win over what is recovered.
/// * `files` - Each file to write and its kind.
/// * `existing` - Whether a regular file already at a path is replaced;
///   a link there is never written through.
///
/// # Returns
///
/// One line per file written, and one saying what the SDK holds.
///
/// # Errors
///
/// When a path is unusable, a file is there and `existing` keeps it, a
/// write fails, or the request's deadline passed while the classes were
/// read ([`borer_engine::cancel::Cancel`]); the files written before a
/// failed write stay.
pub fn write_mod_files(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    files: &[(ModFile, &str)],
    existing: Existing,
) -> anyhow::Result<String> {
    use borer_engine::analysis::modsdk::{self, Evidence};
    for (_, out) in files {
        if let Some(why) = borer_engine::program::unusable_path(Path::new(out)) {
            anyhow::bail!("{why}; nothing was written");
        }
        if existing == Existing::Keep && std::fs::symlink_metadata(out).is_ok() {
            anyhow::bail!("{} exists; nothing was written", short_path(out));
        }
    }
    let cut = || {
        borer_engine::cancel::Cancel::raised().then(|| {
            anyhow::anyhow!(
                "the request's deadline passed before the mod files were ready, so nothing was written; raise BORER_DEADLINE_SECS"
            )
        })
    };
    let sdk = modsdk::build(program, analysis, overlay);
    if let Some(why) = cut() {
        return Err(why);
    }
    let mut rendered = Vec::with_capacity(files.len());
    for &(kind, out) in files {
        let bytes = match kind {
            ModFile::Header => modsdk::header::header(&sdk).into_bytes(),
            ModFile::CheatTable => modsdk::cheat::cheat_table(&sdk).into_bytes(),
            ModFile::ReClass => modsdk::reclass::reclass(&sdk)?,
        };
        rendered.push((kind, out, bytes));
    }
    if let Some(why) = cut() {
        return Err(why);
    }
    let mut lines = String::new();
    for (kind, out, bytes) in rendered {
        let shown = short_path(out);
        let mut file =
            create(Path::new(out), existing).with_context(|| format!("creating {shown}"))?;
        file.write_all(&bytes)
            .with_context(|| format!("writing {shown}"))?;
        let _ = writeln!(
            lines,
            "wrote the {} to {shown} ({} bytes)",
            kind.what(),
            bytes.len()
        );
    }
    let fields = sdk.classes.iter().flat_map(|c| &c.fields);
    let unsure = fields
        .clone()
        .filter(|f| matches!(f.evidence, Evidence::Unsure(_)))
        .count();
    let _ = write!(
        lines,
        "{} classes, {} fields ({unsure} unsure), {} globals, {} thread-local singletons, {} named functions",
        sdk.classes.len(),
        fields.count(),
        sdk.globals.len(),
        sdk.tls.len(),
        sdk.functions.len()
    );
    Ok(lines)
}

#[cfg(test)]
mod tests {
    use super::{Existing, Library, write_c, write_entries};
    use borer_engine::analysis::{Analysis, Overlay};
    use borer_engine::program::{Arch, Program, Section};

    /// A caller and its leaf export as one file, the leaf first.
    ///
    /// The file has the prelude, the leaf's prototype once above both
    /// definitions, the name the overlay gives in force, and no `.part`
    /// file is left behind.
    ///
    /// # Panics
    ///
    /// When the file is not that.
    #[test]
    fn a_caller_and_its_leaf_export_leaves_first() {
        let mut code = vec![0xccu8; 0x20];
        code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 1; ret
        code[0x10..0x1e].copy_from_slice(&[
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, 0xe7, 0xff, 0xff, 0xff, // ASM: call 0x1000
            0x48, 0x83, 0xc4, 0x28, 0xc3, // ASM: add rsp, 0x28; ret
        ]);
        let text = Section::mapped(".text", 0x1000, 0, 0x20, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1010), vec![text]);
        let a = Analysis::compute(&p);
        let mut o = Overlay::default();
        o.names.insert(0x1000, "leaf_one".to_owned());
        let dir = std::env::temp_dir().join(format!("borer-export-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("t.c").display().to_string();
        let written = write_c(&p, &a, &o, Library::Skip, &out, Existing::Keep).expect("writes");
        assert!(
            write_c(&p, &a, &o, Library::Skip, &out, Existing::Keep).is_err(),
            "a second write keeps the first file"
        );
        let c = std::fs::read_to_string(&out).expect("reads");
        let part_left = std::path::Path::new(&format!("{out}.part")).exists();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert!(!part_left);
        assert_eq!(written.hoisted.written, 2, "{c}");
        assert!(c.contains("#include <stdint.h>"), "{c}");
        let leaf = c
            .find("\nuint32_t leaf_one();")
            .unwrap_or_else(|| panic!("{c}"));
        let leaf_def = c
            .find(" leaf_one()\n{\n  return 1;\n}")
            .unwrap_or_else(|| panic!("{c}"));
        let caller = c.find(" sub_1010()\n{").unwrap_or_else(|| panic!("{c}"));
        assert!(leaf < leaf_def && leaf_def < caller, "{c}");
        assert_eq!(c.matches("\nuint32_t leaf_one();").count(), 1, "{c}");
    }

    /// An `--only` entry no function starts at, even after gap recovery, is
    /// named in the summary rather than dropped without a word.
    ///
    /// # Panics
    ///
    /// When the summary does not name it.
    #[test]
    fn an_only_entry_no_function_starts_at_is_named() {
        let mut code = vec![0xccu8; 0x10];
        code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 1; ret
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-only-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("o.c").display().to_string();
        let only = [0x1000, 0x1008];
        let w = write_entries(
            &p,
            &mut a,
            &Overlay::default(),
            Library::Skip,
            Some(&only),
            &out,
            Existing::Replace,
        )
        .expect("writes");
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert_eq!(w.unmatched, vec![0x1008]);
        assert!(
            w.line(&out).contains("no function starts at 0x1008"),
            "{}",
            w.line(&out)
        );
    }

    /// An export whose request's deadline has passed refuses to write.
    ///
    /// The file already at `out` stays as it was even when `existing` would
    /// replace it, no `.part` is left, and the error says how to narrow it.
    ///
    /// The flag is raised before the export runs, so every decompile in it
    /// answers that it stopped, whatever the machine's speed.
    ///
    /// # Panics
    ///
    /// When the export succeeds, touches the file or leaves the `.part`.
    #[test]
    fn an_export_past_the_deadline_leaves_the_file_as_it_was() {
        let mut code = vec![0xccu8; 0x10];
        code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 1; ret
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-cut-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("c.c").display().to_string();
        std::fs::write(&out, "complete export").expect("writes");
        let flag = borer_engine::cancel::Cancel::new();
        flag.raise();
        let cut = flag.within(|| {
            write_c(
                &p,
                &a,
                &Overlay::default(),
                Library::Skip,
                &out,
                Existing::Replace,
            )
        });
        let kept = std::fs::read_to_string(&out).expect("reads");
        let part_left = std::path::Path::new(&format!("{out}.part")).exists();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        let why = format!("{:#}", cut.expect_err("a cut export is refused"));
        assert!(why.contains("BORER_DEADLINE_SECS"), "{why}");
        assert_eq!(kept, "complete export");
        assert!(!part_left);
    }

    /// Mod files whose request's deadline has passed are refused, and none
    /// is written.
    ///
    /// # Panics
    ///
    /// When the files are written or the error does not say why.
    #[test]
    fn mod_files_past_the_deadline_are_not_written() {
        use super::{ModFile, write_mod_files};
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-mod-cut-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let h = dir.join("cut.h").display().to_string();
        let flag = borer_engine::cancel::Cancel::new();
        flag.raise();
        let files = [(ModFile::Header, h.as_str())];
        let cut =
            flag.within(|| write_mod_files(&p, &a, &Overlay::default(), &files, Existing::Replace));
        let written = std::path::Path::new(&h).exists();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        let why = format!("{:#}", cut.expect_err("a cut export is refused"));
        assert!(why.contains("BORER_DEADLINE_SECS"), "{why}");
        assert!(!written);
    }

    /// Checks a C++17 file with a compiler, warnings as errors.
    ///
    /// # Arguments
    ///
    /// * `cxx` - The compiler.
    /// * `file` - The file.
    ///
    /// # Returns
    ///
    /// What the compiler said, or `None` when it does not run.
    fn syntax_check(cxx: &std::path::Path, file: &std::path::Path) -> Option<std::process::Output> {
        std::process::Command::new(cxx)
            .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Werror"])
            .arg(file)
            .output()
            .ok()
    }

    /// The C++ compiler this machine has with its standard library.
    ///
    /// The first of `$CXX`, `c++`, `clang++` or `g++` on the path, and
    /// LLVM's clang++ where Windows installs it, that compiles the two
    /// headers the mod SDK includes.
    ///
    /// # Arguments
    ///
    /// * `dir` - A scratch directory for the probe.
    ///
    /// # Returns
    ///
    /// The compiler, or `None` when none does.
    fn cxx(dir: &std::path::Path) -> Option<std::path::PathBuf> {
        let probe = dir.join("probe.cpp");
        std::fs::write(&probe, "#include <cstddef>\n#include <cstdint>\n").ok()?;
        let named = std::env::var_os("CXX").map(std::path::PathBuf::from);
        let llvm = std::path::PathBuf::from(r"C:\Program Files\LLVM\bin\clang++.exe");
        named
            .into_iter()
            .chain(["c++", "clang++", "g++"].map(std::path::PathBuf::from))
            .chain([llvm])
            .find(|c| syntax_check(c, &probe).is_some_and(|o| o.status.success()))
    }

    /// The mod files of a class with a vtable, a stated struct and a
    /// global singleton are written, and the header compiles as C++17:
    /// its `static_assert`s on every offset and size hold.
    ///
    /// A member of the struct is spelled like the class a later member
    /// points at, which the header's qualified pointer types keep apart;
    /// two are spelled like the macros `<cstddef>` and `<cstdint>` define.
    ///
    /// Where no C++ compiler runs, the header is only checked for its
    /// asserts and the test says so on stderr.
    ///
    /// # Panics
    ///
    /// When a file is not written, the header lacks its asserts, or the
    /// compiler rejects it.
    #[test]
    fn the_mod_files_are_written_and_the_header_compiles() {
        use super::{ModFile, write_mod_files};
        use borer_engine::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
        use borer_engine::analysis::vtables::ClassInfo;
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut a = Analysis::compute(&p);
        a.classes.by_name.insert(
            "Game::Player".to_owned(),
            ClassInfo {
                name: "Game::Player".to_owned(),
                vtable: Some(0x5000),
                slots: vec![0x1000, 0],
                parent: None,
                ctors: Vec::new(),
                creators: Vec::new(),
            },
        );
        a.classes
            .global_hints
            .insert(0x6000, "Game::Player".to_owned());
        let mut o = Overlay::default();
        let field = |name: &str, ty| UserField {
            name: name.to_owned(),
            ty,
        };
        let fields = [
            (0, field("hp", TypeExpr::I32)),
            (4, field("pos", TypeExpr::Array(Box::new(TypeExpr::F32), 3))),
            (0x10, field("Game_Player", TypeExpr::U8)),
            (0x11, field("NULL", TypeExpr::U8)),
            (0x12, field("INT16_MAX", TypeExpr::U16)),
            (
                0x18,
                field(
                    "owner",
                    TypeExpr::Ptr(Box::new(TypeExpr::Named("Game::Player".to_owned()))),
                ),
            ),
        ];
        o.types.insert(
            "Stats".to_owned(),
            UserType::Struct(UserStruct {
                size: 0x28,
                fields: fields.into_iter().collect(),
            }),
        );
        let dir = std::env::temp_dir().join(format!("borer-mod-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let path = |name: &str| dir.join(name).display().to_string();
        let (h, ct, rc) = (path("sdk.h"), path("t.CT"), path("t.rcnet"));
        let files = [
            (ModFile::of_path(&h).expect("h"), h.as_str()),
            (ModFile::of_path(&ct).expect("ct"), ct.as_str()),
            (ModFile::of_path(&rc).expect("rcnet"), rc.as_str()),
        ];
        let said = write_mod_files(&p, &a, &o, &files, Existing::Keep).expect("writes");
        assert!(
            said.contains("2 classes, 7 fields (0 unsure), 1 globals"),
            "{said}"
        );
        assert!(
            write_mod_files(&p, &a, &o, &files, Existing::Keep).is_err(),
            "a second write keeps the files"
        );
        let header = std::fs::read_to_string(&h).expect("reads");
        let table = std::fs::read_to_string(&ct).expect("reads");
        let zip = std::fs::read(&rc).expect("reads");
        assert!(
            header.contains("static_assert(offsetof(Stats, owner) == 0x18"),
            "{header}"
        );
        assert!(
            table.contains("<Address>\"module\"+6000</Address>"),
            "{table}"
        );
        assert!(zip.starts_with(b"PK\x03\x04"));
        let cpp = dir.join("use.cpp");
        std::fs::write(&cpp, "#include \"sdk.h\"\nint main() { return 0; }\n").expect("writes");
        let compiled = cxx(&dir).map(|c| syntax_check(&c, &cpp).expect("runs"));
        std::fs::remove_dir_all(&dir).expect("cleans up");
        match compiled {
            Some(out) => assert!(
                out.status.success(),
                "{}\n{header}",
                String::from_utf8_lossy(&out.stderr)
            ),
            None => {
                eprintln!("no C++ compiler runs here; the header was checked for its asserts only");
            }
        }
    }
}
