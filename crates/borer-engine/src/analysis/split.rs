//! The export split per source file and per class: the file each part of
//! the export goes to, and the map that says why.
//!
//! A build that keeps its assertions names, in every assert, the source
//! file the asserting code is in ([`super::decompile::unit_of`]), so the
//! decompiled functions can be filed by the source file they came from,
//! and the mod SDK's classes each get a header
//! ([`super::modsdk::header::class_headers`]). The paths come from the
//! binary, so each is rebuilt from safe components before any writer sees
//! it: no `..`, no root or drive, no device name, no character a file
//! system refuses, at most [`DEPTH_MAX`] directories deep, and unique
//! however the file system folds case.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::modsdk::{Sdk, Taken, unique};
use super::{Analysis, Overlay};
use crate::program::Program;

/// The file every split C file includes: the export's hoisted declarations.
pub const DECLS: &str = "_decls.h";
/// The C file of the functions whose asserts cite no source file.
pub const REMAINDER: &str = "_unattributed.c";
/// The header every class header includes: the SDK's forward declarations
/// and addresses.
pub const SDK_HEADER: &str = "_sdk.h";
/// Most source files a split writes; the functions of the rest go to
/// [`REMAINDER`].
pub const UNITS_MAX: usize = 4096;
/// Most directories a split file is nested in; the outermost are dropped.
const DEPTH_MAX: usize = 8;
/// Most characters of one path component.
const COMPONENT_MAX: usize = 64;
/// Names Windows keeps for devices, whatever the extension.
const DEVICES: [&str; 22] = [
    "CON", "PRN", "AUX", "NUL", "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8",
    "COM9", "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9",
];

/// Returns one path component made safe to create on any file system.
///
/// # Arguments
///
/// * `part` - The component as the binary spells it.
///
/// # Returns
///
/// ASCII letters, digits, `.`, `_`, `-` and `+` kept and every other
/// character `_`, at most [`COMPONENT_MAX`] characters, no trailing dot or
/// space, a device name prefixed with `_`, and `_` for nothing.
fn safe_component(part: &str) -> String {
    let mut out: String = part
        .trim_end_matches(['.', ' '])
        .chars()
        .take(COMPONENT_MAX)
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-' | '+') {
                c
            } else {
                '_'
            }
        })
        .collect();
    while out.ends_with('.') {
        out.pop();
    }
    let stem = out.split('.').next().unwrap_or("").to_ascii_uppercase();
    if out.is_empty() || DEVICES.contains(&stem.as_str()) {
        out.insert(0, '_');
    }
    out
}

/// Returns `stem` and `ext`, or `stem` with `_2`, `_3` ... before `ext`,
/// the first no other file took however the file system folds case, and
/// takes it.
///
/// A stem wanted again resumes at the suffix it reached ([`unique`]), so
/// many names folding to one stay linear.
///
/// # Arguments
///
/// * `taken` - The stems taken so far, lower-cased.
/// * `stem` - The file wanted without its extension: safe components.
/// * `ext` - The extension, with its dot.
fn unique_file(taken: &mut Taken, stem: &str, ext: &str) -> String {
    let key = unique(taken, &stem.to_ascii_lowercase());
    let suffix = key.get(stem.len()..).unwrap_or_default();
    format!("{stem}{suffix}{ext}")
}

/// Where the split files one function, or why it goes to [`REMAINDER`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Filed<'a> {
    /// The source path it came from, as the binary cites it with `/`
    /// separators: a key of [`Sources::files`].
    Source(&'a str),
    /// It references no source path and its text cites none.
    Nothing,
    /// It references several and its text settles on none.
    Tie,
    /// The file its text names, cut to its last components, fits several
    /// of the paths it references.
    Ambiguous,
    /// The file its text names is none of the paths it references.
    Unmatched,
    /// Its source path is past the [`UNITS_MAX`] files a split writes.
    PastCap,
}

/// The cited source paths, the file each goes to, and the paths each
/// function references.
#[derive(Debug, Default)]
pub struct Sources {
    /// The C file of each cited path, relative to the split's `src`
    /// directory, for the first [`UNITS_MAX`] paths in byte order.
    pub files: BTreeMap<String, String>,
    /// The paths each function references, in byte order.
    of: BTreeMap<u64, Vec<String>>,
}

/// Returns the cited source paths with the C file each goes to and the
/// paths each function references.
///
/// The build root most paths share is dropped ([`super::render::common_root`]),
/// each component is made safe, a path deeper than [`DEPTH_MAX`] keeps its
/// innermost directories, and `.c` is added (`net/socket.cpp` goes to
/// `net/socket.cpp.c`).
///
/// # Arguments
///
/// * `p` - The loaded image, for the cited paths.
/// * `a` - The analysis, for the references to them.
#[must_use]
pub fn sources(p: &Program, a: &Analysis) -> Sources {
    let cited = super::render::cited_sources(p, a);
    let root = super::render::common_root(cited.keys());
    let mut taken: Taken = [REMAINDER.trim_end_matches(".c").to_owned()]
        .into_iter()
        .collect();
    let mut out = Sources::default();
    for (path, entries) in &cited {
        for &e in entries {
            out.of.entry(e).or_default().push(path.clone());
        }
    }
    for path in cited.keys().take(UNITS_MAX) {
        let short = path.strip_prefix(root.as_str()).unwrap_or(path);
        out.files.insert(
            path.clone(),
            unique_file(&mut taken, &rel_stem(short), ".c"),
        );
    }
    out
}

/// Returns the stem of a cited path's split file.
///
/// Its components are made safe, at most [`DEPTH_MAX`] directories are
/// kept, the innermost, and a directory named like a split file (`a.c/`,
/// `b.h/`) takes a `_`, so no file is named as a directory.
///
/// # Arguments
///
/// * `short` - The path, the build root dropped, `/`-separated.
fn rel_stem(short: &str) -> String {
    let mut parts: Vec<String> = short
        .split('/')
        .filter(|c| !c.is_empty() && *c != "." && *c != "..")
        .map(safe_component)
        .collect();
    let dirs = parts.len().saturating_sub(1);
    for dir in parts.iter_mut().take(dirs) {
        if [".c", ".h"]
            .iter()
            .any(|e| dir.to_ascii_lowercase().ends_with(e))
        {
            dir.push('_');
        }
    }
    let kept = parts
        .get(parts.len().saturating_sub(DEPTH_MAX + 1)..)
        .unwrap_or_default();
    if kept.is_empty() {
        "_".to_owned()
    } else {
        kept.join("/")
    }
}

impl Filed<'_> {
    /// Returns why a function went to [`REMAINDER`], `None` when it was
    /// filed under its source.
    #[must_use]
    pub fn why(self) -> Option<&'static str> {
        match self {
            Filed::Source(_) => None,
            Filed::Nothing => Some("cite no source file"),
            Filed::Tie => Some("cite several and settle on none"),
            Filed::Ambiguous => Some("name a cut path that fits several"),
            Filed::Unmatched => Some("name a file they do not reference"),
            Filed::PastCap => Some("cite a file past the 4096 a split writes"),
        }
    }
}

impl Sources {
    /// Returns where the split files a function.
    ///
    /// A function referencing one source path came from it. One
    /// referencing several came from the one its text names
    /// ([`super::decompile::unit_of`]), which the decompiler cuts to its
    /// last components, so that spelling is matched back to the paths the
    /// function references ([`super::render::spelled_as`]).
    ///
    /// # Arguments
    ///
    /// * `entry` - The function's entry.
    /// * `text` - Its decompiled text.
    #[must_use]
    pub fn filed(&self, entry: u64, text: &str) -> Filed<'_> {
        let paths = self.of.get(&entry).map_or(&[][..], Vec::as_slice);
        let path = match paths {
            [one] => one.as_str(),
            _ => match super::decompile::unit_of(text) {
                None if paths.is_empty() => return Filed::Nothing,
                None => return Filed::Tie,
                Some(spelled) => match super::render::spelled_as(paths, &spelled) {
                    Ok(path) => path,
                    Err(0) => return Filed::Unmatched,
                    Err(_) => return Filed::Ambiguous,
                },
            },
        };
        if self.files.contains_key(path) {
            Filed::Source(path)
        } else {
            Filed::PastCap
        }
    }
}

/// Returns the names a split's class headers start from: [`SDK_HEADER`]'s
/// is taken.
#[must_use]
pub(crate) fn header_names() -> Taken {
    [SDK_HEADER.trim_end_matches(".h").to_owned()]
        .into_iter()
        .collect()
}

/// Returns a class header's file name, unique among the split's headers.
///
/// # Arguments
///
/// * `taken` - The headers taken so far ([`header_names`]).
/// * `ident` - The class's C++ identifier.
#[must_use]
pub(crate) fn header_file(taken: &mut Taken, ident: &str) -> String {
    unique_file(taken, &safe_component(ident), ".h")
}

/// Returns the opening of one split C file: what it holds, how rough it
/// is, and the include of [`DECLS`] from its directory.
///
/// # Arguments
///
/// * `file` - The file, relative to the split's `src` directory.
#[must_use]
pub fn unit_prologue(file: &str) -> String {
    let what = if file == REMAINDER {
        "the functions the split filed under no source file (the export's answer counts why: no cited file, a tie, a cut path fitting several, a file past the cap; the ones that did not decompile or were cut for size are here too)".to_owned()
    } else {
        format!("{file}: the functions whose asserts cite this source file")
    };
    format!(
        "/* {what}, as borer decompiled them.\n   Rough pseudo-C: it says what the binary does, and is not the source it was built from. */\n#include \"{}{DECLS}\"\n\n",
        "../".repeat(file.matches('/').count())
    )
}

/// Returns the split's map: each class with its header, the source file
/// most of its methods' asserts cite, the evidence and the counts.
///
/// # Arguments
///
/// * `a` - The analysis, for each class's methods.
/// * `o` - Names in force.
/// * `sdk` - The classes.
/// * `headers` - Each class written with its header file.
/// * `exported` - Each exported function's source path by entry, `None`
///   for one filed under none.
///
/// # Returns
///
/// A `#` header line with the counts, a column header and one
/// tab-separated row per class of the SDK: class, header (`-` when none
/// was written), source file (`-` when none of its exported methods is
/// filed under one), evidence, methods, fields, slots.
#[must_use]
pub fn split_map(
    a: &Analysis,
    o: &Overlay,
    sdk: &Sdk,
    headers: &[(&str, &str)],
    exported: &BTreeMap<u64, Option<String>>,
) -> String {
    let files: BTreeMap<&str, &str> = headers.iter().copied().collect();
    let mut out = format!(
        "# {} classes, {} with a header; a class's source file is the one most of its exported methods are filed under\n# class\theader\tsource\tevidence\tmethods\tfields\tslots\n",
        sdk.classes.len(),
        headers.len()
    );
    for c in &sdk.classes {
        let methods = super::classes::methods_of(a, o, &c.name);
        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        let mut out_of = 0usize;
        for e in &methods {
            if let Some(unit) = exported.get(e) {
                out_of += 1;
                if let Some(u) = unit {
                    *counts.entry(u.as_str()).or_default() += 1;
                }
            }
        }
        let best = counts
            .iter()
            .max_by(|x, y| x.1.cmp(y.1).then_with(|| y.0.cmp(x.0)));
        let (source, evidence) = match best {
            Some((unit, n)) => {
                let others = counts.len().saturating_sub(1);
                let also = if others > 0 {
                    format!("; {others} other files cited too")
                } else {
                    String::new()
                };
                (
                    (*unit).to_owned(),
                    format!("{n} of {out_of} exported methods filed under it{also}"),
                )
            }
            None if out_of == 0 => (
                "-".to_owned(),
                format!("none of its {} methods was exported", methods.len()),
            ),
            None => (
                "-".to_owned(),
                format!("none of its {out_of} exported methods is filed under a source file"),
            ),
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{source}\t{evidence}\t{}\t{}\t{}",
            c.name.replace(['\t', '\n', '\r'], " "),
            files.get(c.name.as_str()).copied().unwrap_or("-"),
            methods.len(),
            c.fields.len(),
            c.slots.len()
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A path from the binary becomes a file under the split's directory and
    /// nowhere else: no parent, root, drive or device, no refused
    /// character, and two that fold to one name stay two.
    ///
    /// # Panics
    ///
    /// When a path keeps a part that could leave the directory.
    #[test]
    fn a_hostile_path_stays_inside_the_split() {
        assert_eq!(safe_component(".."), "_");
        assert_eq!(safe_component("con.cpp"), "_con.cpp");
        assert_eq!(safe_component("a:b*c?.h. "), "a_b_c_.h");
        assert_eq!(safe_component(""), "_");
        assert_eq!(safe_component(&"x".repeat(200)).len(), COMPONENT_MAX);
        let mut taken = Taken::default();
        assert_eq!(
            unique_file(&mut taken, "net/Socket.cpp", ".c"),
            "net/Socket.cpp.c"
        );
        assert_eq!(
            unique_file(&mut taken, "net/socket.cpp", ".c"),
            "net/socket.cpp_2.c"
        );
        assert_eq!(
            unique_file(&mut taken, "net/socket.cpp", ".c"),
            "net/socket.cpp_3.c"
        );
        let mut headers = header_names();
        assert_eq!(header_file(&mut headers, "_sdk"), "_sdk_2.h");
        assert_eq!(header_file(&mut headers, "Foo"), "Foo.h");
        assert_eq!(header_file(&mut headers, "foo"), "foo_2.h");
    }

    /// A cited path's file stays under the split however the binary spells
    /// it, and a directory named like a split file takes a `_`.
    ///
    /// # Panics
    ///
    /// When a stem leaves the directory or names a file as a directory.
    #[test]
    fn a_cited_path_becomes_a_safe_stem() {
        assert_eq!(rel_stem("a.c/x.cpp"), "a.c_/x.cpp");
        assert_eq!(rel_stem("B.H/y.h"), "B.H_/y.h");
        assert_eq!(rel_stem("../../x/./con.cpp"), "x/_con.cpp");
        assert_eq!(rel_stem("/"), "_");
        assert_eq!(rel_stem("a/b/c/d/e/f/g/h/i/j/k.cc"), "c/d/e/f/g/h/i/j/k.cc");
    }

    /// A class whose methods were not exported is not said to cite no
    /// source file: the map says they were not exported.
    ///
    /// # Panics
    ///
    /// When the map's row blames the asserts.
    #[test]
    fn a_class_with_no_exported_method_is_not_blamed_on_its_asserts() {
        use crate::analysis::modsdk::{Class, Size};
        use crate::program::{Arch, Section};
        let mut bytes = vec![0u8; 0x2000];
        bytes[0x1000] = 0xc3;
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![Section::mapped(
                ".text", 0x1000, 0x1000, 0x1000, false, true,
            )],
        );
        let a = Analysis::compute(&p);
        let mut o = Overlay::default();
        o.names.insert(0x1000, "Foo::Bar".to_owned());
        let sdk = Sdk {
            module: "t".to_owned(),
            image_base: 0,
            word: 8,
            classes: vec![Class {
                name: "Foo".to_owned(),
                size: Size::AtLeast(0),
                parent: None,
                vtable: None,
                slots: Vec::new(),
                fields: Vec::new(),
                notes: Vec::new(),
            }],
            globals: Vec::new(),
            tls: Vec::new(),
            functions: Vec::new(),
        };
        let none = split_map(&a, &o, &sdk, &[], &BTreeMap::new());
        assert!(
            none.contains("none of its 1 methods was exported"),
            "{none}"
        );
        assert!(!none.contains("asserts cite"), "{none}");
        let unfiled = split_map(&a, &o, &sdk, &[], &[(0x1000, None)].into_iter().collect());
        assert!(
            unfiled.contains("none of its 1 exported methods is filed under a source file"),
            "{unfiled}"
        );
    }

    /// A function's source file is the one its `// source:` line would
    /// name: the only file cited, or the one its class names, or the most
    /// cited; a tie names none, so the function is not filed.
    ///
    /// # Panics
    ///
    /// When a function is filed under another file, or a tie is filed.
    #[test]
    fn a_function_is_filed_as_its_source_line_names_it_and_a_tie_is_not() {
        use crate::analysis::decompile::unit_of;
        let class = "// Vec::Push @ 0x1000: 9 instructions\n  f(\"n > 0\", \"inc/vec.h\", 1);\n  g(\"p\", \"net/a.cpp\", 2);\n  g(\"q\", \"net/a.cpp\", 3);\n";
        assert_eq!(unit_of(class).as_deref(), Some("inc/vec.h"));
        let most = "// f @ 0x1000: 9 instructions\n  f(\"a\", \"x/b.h\", 1);\n  f(\"b\", \"x/a.h\", 2);\n  f(\"c\", \"x/a.h\", 3);\n";
        assert_eq!(unit_of(most).as_deref(), Some("x/a.h"));
        let tie = "// f @ 0x1000: 9 instructions\n  f(\"a\", \"x/b.h\", 1);\n  f(\"b\", \"x/a.cpp\", 2);\n";
        assert_eq!(unit_of(tie), None);
        assert_eq!(
            unit_of("// f @ 0x1000\n  f(\"a\", \"no path\", 1);\n"),
            None
        );
    }
}
