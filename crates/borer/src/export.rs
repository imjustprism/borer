//! Writing a whole-binary export ([`borer_engine::analysis::decompile::export`])
//! to a C file, for the `export` command and the `export_c` tool.
//!
//! The function definitions stream to a sibling `.part` file while they
//! are rendered, and the file is then written as the hoisted declarations
//! followed by that part, so memory never holds the file.

use std::io::Write as _;
use std::path::Path;

use anyhow::Context as _;
use borer_engine::analysis::decompile::export::{Hoisted, Library, export};
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
        format!(
            "wrote {} functions to {} ({} bytes); {} did not decompile, {} library functions and stubs left out, {} declarations stated two ways kept the first",
            h.written,
            short_path(out),
            self.bytes,
            h.failed,
            h.left_out,
            h.conflicts
        )
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
/// When the file or its `.part` beside it cannot be written, or a file
/// is at `out` and `existing` keeps it.
pub fn write_c(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    library: Library,
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
    let hoisted = export(program, analysis, overlay, library, &mut |text| {
        bodies
            .write_all(text.as_bytes())
            .with_context(|| format!("writing {shown}.part"))
    })?;
    bodies
        .flush()
        .with_context(|| format!("writing {shown}.part"))?;
    drop(bodies);
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
    Ok(Written { hoisted, bytes })
}

#[cfg(test)]
mod tests {
    use super::{Existing, Library, write_c};
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
}
