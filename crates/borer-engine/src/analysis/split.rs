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
    if out.is_empty() || crate::program::file::named_device(&out) {
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
    /// It references no source path, but it is a method of a class whose
    /// methods that reference any all reference this one, no header: a key
    /// of [`Sources::files`] ([`Sources::file_by_class`]).
    Class(&'a str),
    /// It references no source path, its text cites none, and its class
    /// settles on none.
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
    /// Every cited path, in byte order.
    paths: Vec<String>,
    /// The paths each function references, as indexes into `paths`, in
    /// byte order.
    of: BTreeMap<u64, Vec<usize>>,
    /// The path each function referencing none is filed under by its class,
    /// as an index into `paths` ([`Sources::file_by_class`]).
    class: BTreeMap<u64, usize>,
}

/// What the methods of one class that reference a source path reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cites {
    /// Each references this one path alone, an index into [`Sources::paths`].
    One(usize),
    /// Two reference different paths, or one references several.
    Several,
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
    for (at, (path, entries)) in cited.into_iter().enumerate() {
        for e in entries {
            out.of.entry(e).or_default().push(at);
        }
        if at < UNITS_MAX {
            let short = path.strip_prefix(root.as_str()).unwrap_or(&path);
            let file = unique_file(&mut taken, &rel_stem(short), ".c");
            out.files.insert(path.clone(), file);
        }
        out.paths.push(path);
    }
    out
}

/// Returns the stem of a cited path's split file.
///
/// A `..` drops the directory before it (`ui/../core/a.h` is
/// `core/a.h`) and none past the start, its components are made safe, at
/// most [`DEPTH_MAX`] directories are kept, the innermost, and a directory named like a split file (`a.c/`,
/// `b.h/`) takes a `_`, so no file is named as a directory.
///
/// # Arguments
///
/// * `short` - The path, the build root dropped, `/`-separated.
fn rel_stem(short: &str) -> String {
    let mut resolved: Vec<&str> = Vec::new();
    for c in short.split('/') {
        match c {
            "" | "." => {}
            ".." => {
                resolved.pop();
            }
            _ => resolved.push(c),
        }
    }
    let mut parts: Vec<String> = resolved.into_iter().map(safe_component).collect();
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
    pub fn why(self) -> Option<String> {
        let why = match self {
            Filed::Source(_) | Filed::Class(_) => return None,
            Filed::Nothing => "cite no source file",
            Filed::Tie => "cite several and settle on none",
            Filed::Ambiguous => "name a cut path that fits several",
            Filed::Unmatched => "name a file they do not reference",
            Filed::PastCap => {
                return Some(format!("cite a file past the {UNITS_MAX} a split writes"));
            }
        };
        Some(why.to_owned())
    }
}

impl Sources {
    /// Returns where the split files a function.
    ///
    /// A function referencing one source path came from it. One
    /// referencing several came from the one its text names
    /// ([`super::decompile::unit_of`]), which the decompiler cuts to its
    /// last components, so that spelling is matched back to the paths the
    /// function references ([`super::render::spelled_as`]). One
    /// referencing none, whose text cites none, goes where its class files
    /// it ([`Sources::file_by_class`]).
    ///
    /// # Arguments
    ///
    /// * `entry` - The function's entry.
    /// * `text` - Its decompiled text.
    #[must_use]
    pub fn filed(&self, entry: u64, text: &str) -> Filed<'_> {
        let paths: Vec<&str> = self
            .of
            .get(&entry)
            .into_iter()
            .flatten()
            .filter_map(|&at| self.paths.get(at).map(String::as_str))
            .collect();
        let path = match paths.as_slice() {
            [one] => *one,
            _ => match super::decompile::unit_of(text) {
                None if paths.is_empty() => {
                    return self
                        .class
                        .get(&entry)
                        .and_then(|&at| self.paths.get(at))
                        .and_then(|p| self.files.get_key_value(p))
                        .map_or(Filed::Nothing, |(key, _)| Filed::Class(key));
                }
                None => return Filed::Tie,
                Some(spelled) => match super::render::spelled_as(&paths, &spelled) {
                    Ok(path) => path,
                    Err(0) => return Filed::Unmatched,
                    Err(_) => return Filed::Ambiguous,
                },
            },
        };
        self.files
            .get_key_value(path)
            .map_or(Filed::PastCap, |(key, _)| Filed::Source(key))
    }

    /// Files each method referencing no source path under the one its
    /// class settles on, which [`Sources::filed`] then answers as
    /// [`Filed::Class`].
    ///
    /// A class settles on a path when every method of it referencing any
    /// references that one alone, a source file within [`UNITS_MAX`], not
    /// a header.
    ///
    /// A method is a function whose name's qualifier
    /// ([`super::classes::class_of`]) is one of the SDK's classes, so a
    /// free function in a namespace, or a template method whose class was
    /// never recovered, has none.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis, for the functions.
    /// * `o` - Names in force, for each function's class.
    /// * `sdk` - The classes.
    pub fn file_by_class(&mut self, a: &Analysis, o: &Overlay, sdk: &Sdk) {
        let known: BTreeSet<&str> = sdk.classes.iter().map(|c| c.name.as_str()).collect();
        let methods = a.functions.iter().filter_map(|f| {
            let class = super::classes::declared_name(o, f).and_then(super::classes::class_of)?;
            known.contains(class).then_some((f.entry, class))
        });
        self.class = self.by_class(methods);
    }

    /// Returns the path each method referencing no source path is filed
    /// under by its class.
    ///
    /// A class settles on a path when it has a method referencing one and
    /// every method of it referencing any references that one alone; a
    /// method referencing several, or two referencing different paths,
    /// settle it on none. A header settles nothing, its code being inlined
    /// wherever it is used, nor does a path past [`UNITS_MAX`]; a method
    /// two classes claim is filed only when both settle on one path.
    ///
    /// # Arguments
    ///
    /// * `methods` - Each method's entry with its class, in any order.
    ///
    /// # Returns
    ///
    /// The path by entry, an index into `paths`, for the methods
    /// referencing none whose class settles on one.
    fn by_class<'n>(
        &self,
        methods: impl Iterator<Item = (u64, &'n str)> + Clone,
    ) -> BTreeMap<u64, usize> {
        let mut cites: BTreeMap<&str, Cites> = BTreeMap::new();
        for (entry, class) in methods.clone() {
            let seen = match self.of.get(&entry).map(Vec::as_slice) {
                None | Some([]) => continue,
                Some(&[one]) => Cites::One(one),
                Some(_) => Cites::Several,
            };
            cites
                .entry(class)
                .and_modify(|c| {
                    if *c != seen {
                        *c = Cites::Several;
                    }
                })
                .or_insert(seen);
        }
        let mut out: BTreeMap<u64, Option<usize>> = BTreeMap::new();
        for (entry, class) in methods.filter(|(e, _)| !self.of.contains_key(e)) {
            let at = match cites.get(class) {
                Some(&Cites::One(at)) => self
                    .paths
                    .get(at)
                    .filter(|p| !super::decompile::is_header(p) && self.files.contains_key(*p))
                    .map(|_| at),
                Some(Cites::Several) | None => None,
            };
            out.entry(entry)
                .and_modify(|was| {
                    if *was != at {
                        *was = None;
                    }
                })
                .or_insert(at);
        }
        out.into_iter()
            .filter_map(|(entry, at)| Some((entry, at?)))
            .collect()
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
        "the functions the split filed under no source file (the export's answer counts why: no cited file, a tie, a cut path fitting several, a file past the cap, or no text to read: it did not decompile or was cut for size; one of those referencing a single source path is filed under it)".to_owned()
    } else {
        format!(
            "{file}: the functions filed under this source file, the one source path their literals name or the one their text settles on among several, or, naming none, the one their class's methods all name"
        )
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
/// * `exported` - Where the split filed each exported function, by entry
///   ([`Sources::filed`]).
///
/// # Returns
///
/// A `#` header line with the counts, a column header and one
/// tab-separated row per class of the SDK: class, header (`-` when none
/// was written), source file (`-` when none of its exported methods is
/// filed under one), evidence (how many were filed there by the paths
/// they reference and how many by their class), methods, fields, slots.
#[must_use]
pub fn split_map(
    a: &Analysis,
    o: &Overlay,
    sdk: &Sdk,
    headers: &[(&str, &str)],
    exported: &BTreeMap<u64, Filed<'_>>,
) -> String {
    let files: BTreeMap<&str, &str> = headers.iter().copied().collect();
    let mut out = format!(
        "# {} classes, {} with a header; a class's source file is the one most of its exported methods are filed under\n# class\theader\tsource\tevidence\tmethods\tfields\tslots\n",
        sdk.classes.len(),
        headers.len()
    );
    let by_class = super::classes::methods_by_class(a, o);
    for c in &sdk.classes {
        let methods = by_class.get(&c.name).map_or(&[][..], Vec::as_slice);
        let mut counts: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
        let mut out_of = 0usize;
        for e in methods {
            let Some(filed) = exported.get(e) else {
                continue;
            };
            out_of += 1;
            match *filed {
                Filed::Source(u) => counts.entry(u).or_default().0 += 1,
                Filed::Class(u) => counts.entry(u).or_default().1 += 1,
                Filed::Nothing
                | Filed::Tie
                | Filed::Ambiguous
                | Filed::Unmatched
                | Filed::PastCap => {}
            }
        }
        let best = counts
            .iter()
            .max_by(|x, y| x.1.cmp(y.1).then_with(|| y.0.cmp(x.0)));
        let (source, evidence) = match best {
            Some((unit, &(n, k))) => {
                let mut said = Vec::new();
                if n > 0 {
                    said.push(format!("{n} of {out_of} exported methods filed under it"));
                }
                if k > 0 {
                    said.push(format!(
                        "{k} of {out_of} filed under it by their class, citing no source file themselves"
                    ));
                }
                let others = counts.len().saturating_sub(1);
                if others > 0 {
                    said.push(format!("{others} other files cited too"));
                }
                ((*unit).to_owned(), said.join("; "))
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
        assert_eq!(rel_stem("ui/../core/assert.h"), "core/assert.h");
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
        let unfiled = split_map(
            &a,
            &o,
            &sdk,
            &[],
            &[(0x1000, Filed::Nothing)].into_iter().collect(),
        );
        assert!(
            unfiled.contains("none of its 1 exported methods is filed under a source file"),
            "{unfiled}"
        );
    }

    /// A function's source file is the one its `// source:` line names.
    ///
    /// The only file cited wins, then the one its class names among two or
    /// more, then a source file over every header, then the most cited; a
    /// tie names none, so the function is not filed.
    ///
    /// # Panics
    ///
    /// When a function is filed under another file, or a tie is filed.
    #[test]
    fn a_function_is_filed_as_its_source_line_names_it_and_a_tie_is_not() {
        use crate::analysis::decompile::unit_of;
        let head = |name: &str, cites: &[&str]| {
            let mut text = format!("// {name} @ 0x1000: 9 instructions\n");
            for (line, path) in cites.iter().enumerate() {
                text.push_str(&format!("  f(\"x\", \"{path}\", {line});\n"));
            }
            text
        };
        let class = head("Vec::Push", &["inc/vec.h", "net/a.cpp", "net/a.cpp"]);
        assert_eq!(unit_of(&class).as_deref(), Some("inc/vec.h"));
        let skill = head(
            "Skills::GameSkill::Use",
            &[
                "src/other.cpp",
                "src/other.cpp",
                "src/gameskill.cc",
                "inc/util.h",
            ],
        );
        assert_eq!(unit_of(&skill).as_deref(), Some("src/gameskill.cc"));
        let level = head("f", &["game/level.cpp", "core/array.h", "core/array.h"]);
        assert_eq!(unit_of(&level).as_deref(), Some("game/level.cpp"));
        let cxx = head(
            "Foo::Run",
            &[
                r"C:\ws\src\foo.cxx",
                r"C:\ws\inc\vec.hh",
                r"C:\ws\inc\vec.hh",
            ],
        );
        assert_eq!(unit_of(&cxx).as_deref(), Some("C:/ws/src/foo.cxx"));
        let most = head("f", &["x/b.h", "x/a.h", "x/a.h"]);
        assert_eq!(unit_of(&most).as_deref(), Some("x/a.h"));
        let tie = head("f", &["x/b.cc", "x/a.cpp", "x/a.h", "x/a.h"]);
        assert_eq!(unit_of(&tie), None);
        assert_eq!(unit_of(&head("f", &["no path"])), None);
        let shader = "// f @ 0x1000: 9 instructions\n  load(\"shaders/lit.inc\");\n";
        assert_eq!(unit_of(shader), None);
    }

    /// A function referencing several paths is filed only on the one its
    /// text settles on.
    ///
    /// A tie, a cut spelling that fits two paths, a file it does not
    /// reference and a file past the cap each leave it unfiled.
    ///
    /// # Panics
    ///
    /// When one of them is filed under a path.
    #[test]
    fn a_function_referencing_several_paths_is_filed_only_on_its_text() {
        let paths = ["a/x.cpp", "a/y.cpp", "b/x.cpp", "z/past.cpp"];
        let s = Sources {
            files: paths[..3]
                .iter()
                .map(|p| ((*p).to_owned(), format!("{p}.c")))
                .collect(),
            paths: paths.iter().map(|p| (*p).to_owned()).collect(),
            of: [
                (1, vec![0, 1]),
                (2, vec![0, 2]),
                (3, vec![0, 1]),
                (4, vec![0, 3]),
                (5, vec![0, 1]),
            ]
            .into_iter()
            .collect(),
            class: BTreeMap::new(),
        };
        let text = |cites: &[&str]| {
            let mut t = "// f @ 0x1000: 9 instructions\n".to_owned();
            for (line, p) in cites.iter().enumerate() {
                t.push_str(&format!("  f(\"x\", \"{p}\", {line});\n"));
            }
            t
        };
        assert_eq!(s.filed(1, &text(&["a/x.cpp", "a/y.cpp"])), Filed::Tie);
        assert_eq!(s.filed(2, &text(&["x.cpp"])), Filed::Ambiguous);
        assert_eq!(s.filed(3, &text(&["q/other.cpp"])), Filed::Unmatched);
        assert_eq!(
            s.filed(4, &text(&["z/past.cpp", "z/past.cpp", "a/x.cpp"])),
            Filed::PastCap
        );
        assert_eq!(
            s.filed(5, &text(&["a/y.cpp", "a/y.cpp", "a/x.cpp"])),
            Filed::Source("a/y.cpp")
        );
        assert_eq!(s.filed(6, &text(&[])), Filed::Nothing);
        assert_eq!(
            Filed::PastCap.why().as_deref(),
            Some("cite a file past the 4096 a split writes")
        );
    }

    /// A method referencing no source path is filed by its class only when
    /// every method of the class referencing one references the same
    /// single path, a source file within the cap.
    ///
    /// `C` cites `c.cpp` alone; `D` cites `d1.cpp` and `d2.cpp`; `E` has a
    /// method citing `c.cpp` and `e.h` at once; `H` cites only `h.h`; `P`
    /// cites a path past the cap; `Big` has 100,000 methods, one citing
    /// `c.cpp`; entry 30 is claimed by `C` and `D`, entry 31 by `C` and
    /// `Big`, which settle on one path.
    ///
    /// # Panics
    ///
    /// When a method is filed where its class does not settle.
    #[test]
    fn a_method_citing_nothing_is_filed_only_by_a_class_that_settles() {
        let paths = ["c.cpp", "d1.cpp", "d2.cpp", "e.h", "h.h", "past.cpp"];
        let mut s = Sources {
            files: [0, 1, 2, 3, 4]
                .map(|i: usize| (paths[i].to_owned(), format!("{}.c", paths[i])))
                .into_iter()
                .collect(),
            paths: paths.iter().map(|p| (*p).to_owned()).collect(),
            of: [
                (1, vec![0]),
                (3, vec![1]),
                (4, vec![2]),
                (6, vec![0, 3]),
                (8, vec![4]),
                (10, vec![5]),
                (100, vec![0]),
            ]
            .into_iter()
            .collect(),
            class: BTreeMap::new(),
        };
        let big = (100..100_100).map(|e| (e, "Big"));
        let methods = [
            (1, "C"),
            (2, "C"),
            (3, "D"),
            (4, "D"),
            (5, "D"),
            (6, "E"),
            (7, "E"),
            (8, "H"),
            (9, "H"),
            (10, "P"),
            (11, "P"),
            (30, "C"),
            (30, "D"),
            (31, "C"),
            (31, "Big"),
        ];
        s.class = s.by_class(methods.into_iter().chain(big));
        let none = "// f @ 0x1000: 9 instructions\n";
        assert_eq!(s.filed(2, none), Filed::Class("c.cpp"));
        assert_eq!(s.filed(31, none), Filed::Class("c.cpp"));
        assert_eq!(s.filed(100_099, none), Filed::Class("c.cpp"));
        assert_eq!(s.filed(1, none), Filed::Source("c.cpp"));
        for unsettled in [5, 7, 9, 11, 30, 12] {
            assert_eq!(s.filed(unsettled, none), Filed::Nothing, "{unsettled}");
        }
        assert_eq!(s.class.len(), 100_001);
        assert_eq!(Filed::Class("c.cpp").why(), None);
    }

    /// A split file's opening says how its functions were filed, not that
    /// asserts cite it: a function is filed on any source path its literals
    /// name.
    ///
    /// # Panics
    ///
    /// When the opening claims asserts.
    #[test]
    fn a_split_file_says_how_its_functions_were_filed() {
        let head = unit_prologue("net/a.cpp.c");
        assert!(!head.contains("asserts cite"), "{head}");
        assert!(
            head.contains("the one source path their literals name"),
            "{head}"
        );
        assert!(head.contains("#include \"../_decls.h\""), "{head}");
    }
}
