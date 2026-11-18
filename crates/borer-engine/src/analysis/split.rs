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

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::modsdk::Sdk;
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

/// Returns `want`, or `want` with `_2`, `_3` ... before its extension, the
/// first no other file took in any case, and takes it.
///
/// # Arguments
///
/// * `taken` - The files taken so far, lower-cased.
/// * `want` - The file wanted, a relative path of safe components.
fn unique_file(taken: &mut BTreeSet<String>, want: &str) -> String {
    let (stem, ext) = match want.rsplit_once('.') {
        Some((stem, ext)) if !stem.is_empty() && !stem.ends_with('/') => (stem, format!(".{ext}")),
        _ => (want, String::new()),
    };
    let mut file = want.to_owned();
    let mut n = 1usize;
    while !taken.insert(file.to_ascii_lowercase()) {
        n += 1;
        file = format!("{stem}_{n}{ext}");
    }
    file
}

/// Returns the C file each cited source file's functions go to.
///
/// The build root most paths share is dropped ([`super::render::common_root`]),
/// each component is made safe, a path deeper than [`DEPTH_MAX`] keeps its
/// innermost directories, and `.c` is added (`net/socket.cpp` goes to
/// `net/socket.cpp.c`). The first [`UNITS_MAX`] paths in byte order get a
/// file.
///
/// # Arguments
///
/// * `p` - The loaded image, for the cited paths.
/// * `a` - The analysis, for the references to them.
///
/// # Returns
///
/// The file, relative to the split's `src` directory, by the path as
/// [`super::decompile::unit_of`] spells it.
#[must_use]
pub fn unit_files(p: &Program, a: &Analysis) -> BTreeMap<String, String> {
    let cited = super::render::cited_sources(p, a);
    let root = super::render::common_root(cited.keys());
    let mut taken: BTreeSet<String> = [DECLS, REMAINDER].into_iter().map(str::to_owned).collect();
    let mut out = BTreeMap::new();
    for path in cited.keys().take(UNITS_MAX) {
        let short = path.strip_prefix(root.as_str()).unwrap_or(path);
        let parts: Vec<String> = short
            .split('/')
            .filter(|c| !c.is_empty() && *c != "." && *c != "..")
            .map(safe_component)
            .collect();
        let kept = parts
            .get(parts.len().saturating_sub(DEPTH_MAX + 1)..)
            .unwrap_or_default();
        let rel = if kept.is_empty() {
            "_".to_owned()
        } else {
            kept.join("/")
        };
        out.insert(path.clone(), unique_file(&mut taken, &format!("{rel}.c")));
    }
    out
}

/// Returns a class header's file name, unique among the split's headers.
///
/// # Arguments
///
/// * `taken` - The headers taken so far, lower-cased; [`SDK_HEADER`] is
///   taken first.
/// * `ident` - The class's C++ identifier.
#[must_use]
pub fn header_file(taken: &mut BTreeSet<String>, ident: &str) -> String {
    if taken.is_empty() {
        taken.insert(SDK_HEADER.to_owned());
    }
    unique_file(taken, &format!("{}.h", safe_component(ident)))
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
        "the functions whose asserts cite no source file".to_owned()
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
/// * `units` - Each written function's source file, by entry.
///
/// # Returns
///
/// A `#` header line with the counts, a column header and one
/// tab-separated row per class of the SDK: class, header (`-` when none
/// was written), source file (`-` when no method's asserts cite one),
/// evidence, methods, fields, slots.
#[must_use]
pub fn split_map(
    a: &Analysis,
    o: &Overlay,
    sdk: &Sdk,
    headers: &[(&str, &str)],
    units: &BTreeMap<u64, String>,
) -> String {
    let files: BTreeMap<&str, &str> = headers.iter().copied().collect();
    let mut out = format!(
        "# {} classes, {} with a header; a class's source file is the one most of its methods' asserts cite\n# class\theader\tsource\tevidence\tmethods\tfields\tslots\n",
        sdk.classes.len(),
        headers.len()
    );
    for c in &sdk.classes {
        let methods = super::classes::methods_of(a, o, &c.name);
        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for e in &methods {
            if let Some(u) = units.get(e) {
                *counts.entry(u.as_str()).or_default() += 1;
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
                    format!("{n} of {} methods' asserts cite it{also}", methods.len()),
                )
            }
            None => (
                "-".to_owned(),
                "no method's asserts cite a source file".to_owned(),
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
        let mut taken = BTreeSet::new();
        assert_eq!(
            unique_file(&mut taken, "net/Socket.cpp.c"),
            "net/Socket.cpp.c"
        );
        assert_eq!(
            unique_file(&mut taken, "net/socket.cpp.c"),
            "net/socket.cpp_2.c"
        );
        assert_eq!(
            unique_file(&mut taken, "net/socket.cpp.c"),
            "net/socket.cpp_3.c"
        );
        let mut headers = BTreeSet::new();
        assert_eq!(header_file(&mut headers, "_sdk"), "_sdk_2.h");
        assert_eq!(header_file(&mut headers, "Foo"), "Foo.h");
        assert_eq!(header_file(&mut headers, "foo"), "foo_2.h");
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
