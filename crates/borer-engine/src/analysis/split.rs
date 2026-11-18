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
    /// methods' own asserts settle on one source file
    /// ([`Sources::file_by_class`]).
    Class(ByClass<'a>),
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
    /// The classes that settled on a source file ([`Sources::file_by_class`]).
    settled: Vec<Settled>,
    /// Each function referencing no path that its class files, as an index
    /// into `settled`.
    class: BTreeMap<u64, usize>,
}

/// Fewest methods whose own asserts must cite a class's file before the
/// class files its methods citing none there.
///
/// None may cite another. One method can be defined apart from its class
/// (a specialization, a second source file of the class), so one is a
/// guess.
pub const WITNESSES_MIN: usize = 2;

/// Where a class filed one of its methods and on what evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ByClass<'a> {
    /// The source path: a key of [`Sources::files`].
    pub path: &'a str,
    /// The class, as its methods' names qualify them.
    pub class: &'a str,
    /// Methods of the class whose own asserts cite `path` alone; none
    /// cites another.
    pub cite: usize,
    /// Methods of the class.
    pub methods: usize,
}

/// A class that settled on a source file.
#[derive(Debug)]
struct Settled {
    /// The class.
    class: String,
    /// The path, an index into [`Sources::paths`].
    path: usize,
    /// Methods whose own asserts cite it alone.
    cite: usize,
    /// Methods of the class.
    methods: usize,
}

/// A class's methods by class, each with its name: the functions whose
/// declared name a class of the SDK qualifies ([`class_methods`]).
pub(crate) type ClassMethods<'a> = BTreeMap<&'a str, Vec<(u64, &'a str)>>;

/// Returns each class's methods: what both the split's filing by class and
/// its map count as a class's methods.
///
/// A method is a function whose name's qualifier
/// ([`super::classes::class_of`]) is one of the SDK's classes and whose
/// name a symbol, a signature it carries or the user declared, never one
/// borer guessed; a class in an anonymous namespace has none, since two
/// such classes in two files read as one.
///
/// # Arguments
///
/// * `a` - The analysis, for the functions.
/// * `o` - Names in force.
/// * `sdk` - The classes.
#[must_use]
pub(crate) fn class_methods<'a>(a: &'a Analysis, o: &'a Overlay, sdk: &Sdk) -> ClassMethods<'a> {
    use super::NameSource;
    let known: BTreeSet<&str> = sdk.classes.iter().map(|c| c.name.as_str()).collect();
    let mut out = ClassMethods::new();
    for f in &a.functions {
        let declared = o.names.contains_key(&f.entry)
            || matches!(f.name_source, NameSource::Symbol | NameSource::Signature);
        let Some(name) = super::classes::declared_name(o, f).filter(|_| declared) else {
            continue;
        };
        let Some(class) = super::classes::class_of(name) else {
            continue;
        };
        if known.contains(class) && !class.contains("anonymous namespace") {
            out.entry(class).or_default().push((f.entry, name));
        }
    }
    out
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
                    return self.by_class_of(entry).map_or(Filed::Nothing, Filed::Class);
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

    /// Returns where a function's class files it, `None` when it does not.
    ///
    /// # Arguments
    ///
    /// * `entry` - The function's entry.
    fn by_class_of(&self, entry: u64) -> Option<ByClass<'_>> {
        let settled = self.settled.get(*self.class.get(&entry)?)?;
        let (path, _) = self
            .files
            .get_key_value(self.paths.get(settled.path)?.as_str())?;
        Some(ByClass {
            path,
            class: &settled.class,
            cite: settled.cite,
            methods: settled.methods,
        })
    }

    /// Files each method referencing no source path under the source file
    /// its class settles on, which [`Sources::filed`] then answers as
    /// [`Filed::Class`].
    ///
    /// A class's methods are [`class_methods`]'s. A class settles on a path
    /// when at least [`WITNESSES_MIN`] of them cite it alone in their own
    /// asserts ([`super::members::own_assert_paths`]) and none cites another
    /// there, the path being no header (its code is inlined wherever it is
    /// used) and within [`UNITS_MAX`]. A path a method references beside no
    /// signature of its own, a literal or an assert inlined from elsewhere,
    /// witnesses nothing.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded image, for the asserts' literals.
    /// * `a` - The analysis, for the functions.
    /// * `o` - Names in force, for each function's class.
    /// * `sdk` - The classes.
    pub fn file_by_class(&mut self, p: &Program, a: &Analysis, o: &Overlay, sdk: &Sdk) {
        let methods = class_methods(a, o, sdk);
        let own: BTreeMap<&str, Vec<(u64, BTreeSet<usize>)>> = methods
            .iter()
            .map(|(class, list)| {
                let cites = list.iter().map(|&(entry, name)| {
                    let paths = if self.of.contains_key(&entry) {
                        super::members::own_assert_paths(p, a, entry, name)
                            .iter()
                            .filter_map(|path| self.paths.binary_search(path).ok())
                            .collect()
                    } else {
                        BTreeSet::new()
                    };
                    (entry, paths)
                });
                (*class, cites.collect())
            })
            .collect();
        self.by_class(&own);
    }

    /// Settles each class whose methods' own asserts agree on one path and
    /// files its methods referencing none there ([`Sources::file_by_class`]).
    ///
    /// # Arguments
    ///
    /// * `own` - Each class's methods, each with the paths its own asserts
    ///   cite as indexes into `paths`.
    fn by_class(&mut self, own: &BTreeMap<&str, Vec<(u64, BTreeSet<usize>)>>) {
        for (class, methods) in own {
            let mut cited = methods.iter().map(|(_, p)| p).filter(|p| !p.is_empty());
            let Some(first) = cited.next() else {
                continue;
            };
            let (Some(&path), 1) = (first.first(), first.len()) else {
                continue;
            };
            if !cited
                .clone()
                .all(|p| p.len() == 1 && p.first() == Some(&path))
            {
                continue;
            }
            let cite = 1 + cited.count();
            let fits = self
                .paths
                .get(path)
                .is_some_and(|p| !super::decompile::is_header(p) && self.files.contains_key(p));
            if cite < WITNESSES_MIN || !fits {
                continue;
            }
            let at = self.settled.len();
            self.settled.push(Settled {
                class: (*class).to_owned(),
                path,
                cite,
                methods: methods.len(),
            });
            for (entry, _) in methods.iter().filter(|(e, _)| !self.of.contains_key(e)) {
                self.class.insert(*entry, at);
            }
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
/// most of its exported methods are filed under, the evidence and the
/// counts.
///
/// # Arguments
///
/// * `a` - The analysis, for each class's methods ([`class_methods`]).
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
/// they reference and how many by their class, with how many of the
/// class's methods cite it in their own asserts), methods
/// ([`class_methods`]), fields, slots.
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
    let by_class = class_methods(a, o, sdk);
    for c in &sdk.classes {
        let methods = by_class.get(c.name.as_str()).map_or(&[][..], Vec::as_slice);
        let mut counts: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
        let mut witnessed = None;
        let mut out_of = 0usize;
        for (e, _) in methods {
            let Some(filed) = exported.get(e) else {
                continue;
            };
            out_of += 1;
            match *filed {
                Filed::Source(u) => counts.entry(u).or_default().0 += 1,
                Filed::Class(b) => {
                    counts.entry(b.path).or_default().1 += 1;
                    witnessed = Some((b.cite, b.methods));
                }
                Filed::Nothing
                | Filed::Tie
                | Filed::Ambiguous
                | Filed::Unmatched
                | Filed::PastCap => {}
            }
        }
        let best = counts.iter().max_by(|x, y| {
            (x.1.0 + x.1.1)
                .cmp(&(y.1.0 + y.1.1))
                .then_with(|| y.0.cmp(x.0))
        });
        let (source, evidence) = match best {
            Some((unit, &(n, k))) => {
                let mut said = Vec::new();
                if n > 0 {
                    said.push(format!("{n} of {out_of} exported methods filed under it"));
                }
                if let (true, Some((cite, of))) = (k > 0, witnessed) {
                    said.push(format!(
                        "{k} of {out_of} filed under it by their class, citing none themselves: {cite} methods of {of} cite it in their own asserts"
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
            ..Sources::default()
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
    /// at least [`WITNESSES_MIN`] of the class's methods cite one source
    /// file alone in their own asserts and none cites another.
    ///
    /// `C` has two witnesses of `c.cpp`; `One` one; `D` two of two files;
    /// `E` two of `c.cpp` and a third citing `c.cpp` and `d1.cpp`; `H` two
    /// of the header `h.h`; `P` two of a path past the cap; `Foo` a method
    /// referencing `c.cpp` in no own assert; `Big` 100,000 methods, two
    /// witnesses of `c.cpp`.
    ///
    /// # Panics
    ///
    /// When a method is filed where its class does not settle.
    #[test]
    fn a_method_citing_nothing_is_filed_only_by_a_class_that_settles() {
        let paths = ["c.cpp", "d1.cpp", "d2.cpp", "e.h", "h.h", "past.cpp"];
        let referencing = [1, 2, 10, 20, 21, 30, 31, 32, 40, 41, 50, 51, 60, 100, 101];
        let mut s = Sources {
            files: [0, 1, 2, 3, 4]
                .map(|i: usize| (paths[i].to_owned(), format!("{}.c", paths[i])))
                .into_iter()
                .collect(),
            paths: paths.iter().map(|p| (*p).to_owned()).collect(),
            of: referencing.into_iter().map(|e| (e, vec![0])).collect(),
            ..Sources::default()
        };
        let own = |cited: &[usize]| cited.iter().copied().collect::<BTreeSet<usize>>();
        let class = |methods: &[(u64, &[usize])]| -> Vec<(u64, BTreeSet<usize>)> {
            methods.iter().map(|(e, c)| (*e, own(c))).collect()
        };
        let mut big: Vec<(u64, BTreeSet<usize>)> = (102..100_100).map(|e| (e, own(&[]))).collect();
        big.extend([(100, own(&[0])), (101, own(&[0]))]);
        let classes: BTreeMap<&str, Vec<(u64, BTreeSet<usize>)>> = [
            ("C", class(&[(1, &[0]), (2, &[0]), (3, &[])])),
            ("One", class(&[(10, &[0]), (11, &[])])),
            ("D", class(&[(20, &[1]), (21, &[2]), (22, &[])])),
            (
                "E",
                class(&[(30, &[0]), (31, &[0]), (32, &[0, 1]), (33, &[])]),
            ),
            ("H", class(&[(40, &[4]), (41, &[4]), (42, &[])])),
            ("P", class(&[(50, &[5]), (51, &[5]), (52, &[])])),
            ("Foo", class(&[(60, &[]), (61, &[])])),
            ("Big", big),
        ]
        .into_iter()
        .collect();
        s.by_class(&classes);
        let none = "// f @ 0x1000: 9 instructions\n";
        let by = |class, cite, methods| {
            Filed::Class(ByClass {
                path: "c.cpp",
                class,
                cite,
                methods,
            })
        };
        assert_eq!(s.filed(3, none), by("C", 2, 3));
        assert_eq!(s.filed(100_099, none), by("Big", 2, 100_000));
        assert_eq!(s.filed(1, none), Filed::Source("c.cpp"));
        for unsettled in [11, 22, 33, 42, 52, 61, 7] {
            assert_eq!(s.filed(unsettled, none), Filed::Nothing, "{unsettled}");
        }
        assert_eq!(s.class.len(), 1 + 99_998);
        assert_eq!(by("C", 2, 3).why(), None);
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
