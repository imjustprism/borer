//! Program-wide catalogs read from asserts: asserted fields, the source tree,
//! class ids and singletons, and the legend that keeps a repeated name out
//! of every row of a catalog.

use super::*;
use crate::fxmap::FxHashMap;

/// A legend numbering the names that repeat on one page of a catalog, so a
/// row says `3` where the page's `# <column>: 3=...` line spells the name.
///
/// A name used once costs less inline than numbered, so only a name two or
/// more cells share is numbered, by first appearance; a function or class
/// name never starts with a digit, so a bare number in a cell is always a
/// legend entry.
#[derive(Debug, Default)]
pub(crate) struct Legend {
    /// The repeated names, in numbering order; entry `i` is number `i + 1`.
    names: Vec<String>,
    /// Each repeated name's number.
    numbers: FxHashMap<String, usize>,
}

impl Legend {
    /// Numbers the names that occur more than once in `names`, by first
    /// appearance.
    ///
    /// # Arguments
    ///
    /// * `names` - Every name every cell of the page spells, in row order.
    pub(crate) fn of<'a>(names: impl Iterator<Item = &'a str> + Clone) -> Self {
        let mut counts: FxHashMap<&str, usize> = FxHashMap::default();
        for name in names.clone() {
            *counts.entry(name).or_default() += 1;
        }
        let mut legend = Legend::default();
        for name in names {
            if counts.get(name).is_some_and(|&n| n > 1) && !legend.numbers.contains_key(name) {
                legend.names.push(name.to_owned());
                legend.numbers.insert(name.to_owned(), legend.names.len());
            }
        }
        legend
    }

    /// A name as a cell spells it: its number when the legend has it, else
    /// the name itself.
    ///
    /// # Arguments
    ///
    /// * `name` - The name.
    pub(crate) fn cell(&self, name: &str) -> String {
        self.numbers
            .get(name)
            .map_or_else(|| name.to_owned(), usize::to_string)
    }

    /// The `# <column>: 1=... 2=...` line, with its newline; empty when no
    /// name repeats.
    ///
    /// # Arguments
    ///
    /// * `column` - What the legend numbers, as the header names it.
    pub(crate) fn line(&self, column: &str) -> String {
        if self.names.is_empty() {
            return String::new();
        }
        let entries: Vec<String> = self
            .names
            .iter()
            .enumerate()
            .map(|(i, name)| format!("{}={name}", i + 1))
            .collect();
        format!("# {column}: {}\n", entries.join(" "))
    }
}

/// Most fields listed in one read of the assertion index.
pub(super) const FIELDS_MAX: usize = 200;

/// Conditions shown under a field when the list was filtered.
pub(super) const CONDITIONS_PER_FIELD: usize = 8;

/// Longest assertion text kept as a condition.
pub(super) const CONDITION_MAX: usize = 100;

/// What one asserted field name gathers.
#[derive(Debug, Default)]
pub(super) struct Asserted {
    /// Entries of the functions that assert it.
    pub(super) functions: BTreeSet<u64>,
    /// The classes those functions belong to.
    pub(super) classes: BTreeSet<String>,
    /// The conditions they check, as the assertions spell them.
    pub(super) conditions: BTreeSet<String>,
}

/// Lists the fields the binary's assertions name.
///
/// A build that keeps its assertions says `this->state` in the text of the
/// ones that check a member, which names a field no symbol does. This is the
/// index of those names: one row per field, with how many functions assert
/// it and which classes they belong to, so a reader can ask which class owns
/// a name instead of reading layouts one at a time.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading the strings.
/// * `a` - Cross-references and functions.
/// * `o` - User names.
/// * `filter` - Case-insensitive substring of the field or the class.
///
/// # Returns
///
/// The listing as text, the most asserted first, tab-separated: how many
/// functions assert the field, the field, and up to three of the classes
/// they belong to (the ones the filter matched first) with `+N` for the
/// rest. A filtered listing also shows what the assertions check, one
/// tab-indented line each, which is where the values a field is compared
/// against are written down.
pub fn asserted_fields_tsv(p: &Program, a: &Analysis, o: &Overlay, filter: &str) -> String {
    let want = filter.to_lowercase();
    let mut fields: BTreeMap<String, Asserted> = BTreeMap::new();
    for (target, sites) in &a.xrefs {
        let Some((_, lit)) = string_literal(p, *target, STRING_MATCH_CAP) else {
            continue;
        };
        let mut rest = lit.as_str();
        while let Some(at) = rest.find("this->") {
            let tail = rest.get(at + 6..).unwrap_or("");
            let end = tail
                .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .unwrap_or(tail.len());
            let name = tail.get(..end).unwrap_or("");
            rest = tail.get(end..).unwrap_or("");
            if name.is_empty() {
                continue;
            }
            let e = fields.entry(name.to_owned()).or_default();
            if let Some(text) = lit.strip_prefix('"').and_then(|t| t.strip_suffix('"'))
                && text.len() <= CONDITION_MAX
            {
                e.conditions.insert(text.to_owned());
            }
            for site in sites {
                let Some(entry) = site.from_entry else {
                    continue;
                };
                e.functions.insert(entry);
                if let Some(class) = crate::analysis::classes::class_of(&name_of(a, o, entry)) {
                    e.classes.insert(class.to_owned());
                }
            }
        }
    }
    let total = fields.len();
    let mut rows: Vec<(&String, &Asserted)> = fields
        .iter()
        .filter(|(name, field)| {
            want.is_empty()
                || name.to_lowercase().contains(&want)
                || field
                    .classes
                    .iter()
                    .any(|c| c.to_lowercase().contains(&want))
        })
        .collect();
    rows.sort_by_key(|(name, field)| (std::cmp::Reverse(field.functions.len()), (*name).clone()));
    let mut out = format!(
        "# {} of {total} asserted field names{}\n",
        rows.len().min(FIELDS_MAX),
        narrows(rows.len(), FIELDS_MAX, "asserts")
    );
    out.push_str("# functions\tfield\tclasses\n");
    for (name, field) in rows.iter().take(FIELDS_MAX) {
        let mut named: Vec<&String> = field.classes.iter().collect();
        named.sort_by_key(|c| (!c.to_lowercase().contains(&want), c.len()));
        let shown: Vec<&str> = named.iter().take(3).map(|c| c.as_str()).collect();
        let more = if field.classes.len() > shown.len() {
            format!(", +{}", field.classes.len() - shown.len())
        } else {
            String::new()
        };
        let _ = writeln!(
            out,
            "{}\t{name}\t{}{more}",
            field.functions.len(),
            shown.join(", ")
        );
        if want.is_empty() {
            continue;
        }
        for text in field.conditions.iter().take(CONDITIONS_PER_FIELD) {
            let _ = writeln!(out, "\t{text}");
        }
        if field.conditions.len() > CONDITIONS_PER_FIELD {
            let _ = writeln!(
                out,
                "\t+{} more conditions",
                field.conditions.len() - CONDITIONS_PER_FIELD
            );
        }
    }
    out
}

/// Most rows in one read of the source tree.
pub(super) const SOURCES_MAX: usize = 200;

/// One source file an assertion cites, and the functions that cite it.
#[derive(Debug)]
pub(super) struct SourceFile {
    /// The path, with the build root stripped.
    pub(super) path: String,
    /// How many functions cite it.
    pub(super) functions: usize,
    /// The lowest entry among them.
    pub(super) first: u64,
}

/// Groups the functions by the source file their assertions name.
///
/// A C++ build that keeps its assertions ships the path of every file that
/// asserts, and the functions referencing one path came from that file. The
/// paths share a build root nobody needs to read, so the prefix most of
/// them agree on is dropped from every row ([`common_root`]) and written
/// once, as a `# base: <root>` line, when there is one. Without a filter
/// this is one row per directory, which is the subsystem list; with one it
/// is the files that match, each with the functions that came from it.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading the strings.
/// * `a` - Cross-references and functions.
/// * `filter` - Case-insensitive substring of the path, or empty.
///
/// # Returns
///
/// The listing as text, the busiest first, tab-separated: without a filter
/// the functions, files and directory of each row; with one the functions,
/// the lowest entry among them and the file.
pub fn source_tree_tsv(p: &Program, a: &Analysis, filter: &str) -> String {
    /// File extensions a cited source path ends with.
    const EXTENSIONS: [&str; 10] = [
        ".h", ".hpp", ".hh", ".hxx", ".inl", ".c", ".cc", ".cpp", ".cxx", ".inc",
    ];
    let want = filter.to_lowercase();
    let mut files: BTreeMap<String, BTreeSet<u64>> = BTreeMap::new();
    for (target, sites) in &a.xrefs {
        let Some((_, lit)) = string_literal(p, *target, STRING_MATCH_CAP) else {
            continue;
        };
        let Some(path) = lit.strip_prefix('"').and_then(|t| t.strip_suffix('"')) else {
            continue;
        };
        if path.contains(' ') || !EXTENSIONS.iter().any(|e| path.ends_with(e)) {
            continue;
        }
        let entries: BTreeSet<u64> = sites.iter().filter_map(|s| s.from_entry).collect();
        if entries.is_empty() {
            continue;
        }
        files
            .entry(path.replace('\\', "/"))
            .or_default()
            .extend(entries);
    }
    let root = common_root(files.keys());
    let mut by_dir: BTreeMap<String, (usize, BTreeSet<u64>)> = BTreeMap::new();
    let mut rows: Vec<SourceFile> = Vec::new();
    let mut total = 0usize;
    for (path, entries) in &files {
        let short = path.strip_prefix(&root).unwrap_or(path);
        total += entries.len();
        let dir = short.rsplit_once('/').map_or("(root)", |(d, _)| d);
        let e = by_dir.entry(dir.to_owned()).or_default();
        e.0 += 1;
        e.1.extend(entries.iter().copied());
        if !want.is_empty() && short.to_lowercase().contains(&want) {
            rows.push(SourceFile {
                path: short.to_owned(),
                functions: entries.len(),
                first: entries.iter().copied().min().unwrap_or_default(),
            });
        }
    }
    let base = if root.is_empty() {
        String::new()
    } else {
        format!("# base: {root}\n")
    };
    if want.is_empty() {
        let mut dirs: Vec<(&String, &(usize, BTreeSet<u64>))> = by_dir.iter().collect();
        dirs.sort_by_key(|(d, (_, e))| (std::cmp::Reverse(e.len()), (*d).clone()));
        let mut out = format!(
            "# {} files in {} directories, cited by {total} function references\n{base}",
            files.len(),
            by_dir.len()
        );
        out.push_str("# functions\tfiles\tdirectory (borer://sources/<filter> for the files)\n");
        for (dir, (n, entries)) in dirs.iter().take(SOURCES_MAX) {
            let _ = writeln!(out, "{}\t{n}\t{dir}", entries.len());
        }
        return out;
    }
    rows.sort_by_key(|r| (std::cmp::Reverse(r.functions), r.path.clone()));
    let mut out = format!("# {} files match '{filter}'\n{base}", rows.len());
    out.push_str("# functions\tfirst\tfile\n");
    for r in rows.iter().take(SOURCES_MAX) {
        let _ = writeln!(out, "{}\t{:#x}\t{}", r.functions, r.first, r.path);
    }
    more_line(&mut out, rows.len(), SOURCES_MAX, "not listed");
    out
}

/// The build root most of the paths share.
///
/// Paths from one build agree on a long prefix nobody needs to read, but a
/// few assertions cite a short relative path, and one of those would empty a
/// strict common prefix. The root is grown one component at a time while at
/// least half the paths still agree on it.
///
/// # Arguments
///
/// * `paths` - The paths, separators already normalized to `/`.
///
/// # Returns
///
/// The root with a trailing separator, or an empty string.
pub(super) fn common_root<'a>(paths: impl Iterator<Item = &'a String>) -> String {
    let dirs: Vec<Vec<&str>> = paths
        .filter_map(|p| p.rsplit_once('/'))
        .map(|(d, _)| d.split('/').collect())
        .collect();
    if dirs.is_empty() {
        return String::new();
    }
    let mut root: Vec<&str> = Vec::new();
    loop {
        let depth = root.len();
        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for d in &dirs {
            if d.len() > depth && d.iter().take(depth).eq(root.iter()) {
                *counts.entry(d[depth]).or_default() += 1;
            }
        }
        let Some((component, count)) = counts.into_iter().max_by_key(|(_, c)| *c) else {
            break;
        };
        if count * 2 < dirs.len() {
            break;
        }
        root.push(component);
    }
    if root.is_empty() {
        String::new()
    } else {
        format!("{}/", root.join("/"))
    }
}

/// Most classes listed in one read of the registry.
pub(super) const CLASSES_MAX: usize = 300;

/// Lists the classes that registered a four-character code.
///
/// A class registers its name, its code and its factory with the engine at
/// startup, and that code is what identifies it on the wire. This is the
/// index of the registry: one row per class, with how many of its methods
/// were recovered and where to start reading them.
///
/// # Arguments
///
/// * `a` - The analysis holding the registry and the functions.
/// * `filter` - Case-insensitive substring of the class name or the code.
///
/// # Returns
///
/// The listing as text, in registry order, tab-separated: the code as
/// [`crate::analysis::classes::fourcc`] renders it (its four characters
/// quoted, or its value when a byte is unprintable), the method count, the
/// first method's address or `-`, and the class. A registered name that is
/// the tail of a fuller class name is shown with that name in brackets,
/// since the engine registers `ShopWidget` for what the code calls
/// `UI::ShopWidget`, and `class_layout` resolves either spelling to it.
pub fn class_ids_tsv(a: &Analysis, filter: &str) -> String {
    let want = filter.to_lowercase();
    let mut methods: BTreeMap<&str, (usize, u64)> = BTreeMap::new();
    for f in &a.functions {
        let name = f.name.as_deref().unwrap_or_default();
        let Some(class) = crate::analysis::classes::class_of(name) else {
            continue;
        };
        let e = methods.entry(class).or_insert((0, f.entry));
        e.0 += 1;
        e.1 = e.1.min(f.entry);
    }
    let mut by_tail: BTreeMap<&str, &str> = BTreeMap::new();
    for class in methods.keys() {
        if let Some((_, tail)) = class.rsplit_once("::") {
            by_tail.entry(tail).or_insert(class);
        }
    }
    let rows: Vec<(&String, String)> = a
        .classes
        .ids
        .iter()
        .map(|(class, code)| (class, crate::analysis::classes::fourcc(*code)))
        .filter(|(class, code)| {
            want.is_empty()
                || class.to_lowercase().contains(&want)
                || code.to_lowercase().contains(&want)
        })
        .collect();
    let shown = rows.len().min(CLASSES_MAX);
    let mut out = format!(
        "# {shown} of {} classes carry a four-character code{}\n",
        a.classes.ids.len(),
        narrows(rows.len(), CLASSES_MAX, "classes")
    );
    out.push_str("# code\tmethods\tfirst\tclass\n");
    for (class, code) in rows.iter().take(CLASSES_MAX) {
        let full = methods
            .contains_key(class.as_str())
            .then_some(class.as_str())
            .or_else(|| by_tail.get(class.as_str()).copied())
            .unwrap_or(class.as_str());
        let (n, first) = methods
            .get(full)
            .map_or((0, None), |(n, at)| (*n, Some(*at)));
        let shown_name = if full == class.as_str() {
            (*class).clone()
        } else {
            format!("{class} ({full})")
        };
        let _ = writeln!(out, "{code}\t{n}\t{}\t{shown_name}", hex_or_dash(first));
    }
    out
}

/// Most global singletons listed in one read.
pub(super) const SINGLETONS_MAX: usize = 400;

/// Lists the program's recovered singletons: the classes whose one instance
/// lives at a fixed thread-local or global slot.
///
/// A singleton's constructor stores `this` into a fixed place — a thread-local
/// slot the loader hands the module (a manager kept per game thread), or a
/// plain global — and every accessor reads it back from there. borer votes a
/// class onto each slot from the constructors it saw ([`crate::analysis::vtables`]); this lists
/// them, thread-local first, with the `::Instance` accessor's address when the
/// program names one. It is the global object model in one read: which managers
/// exist and where the one instance of each is kept, the shape a game engine or
/// any singleton-heavy program is built around. A filter narrows by class name.
///
/// # Arguments
///
/// * `a` - The analysis holding the singleton maps and functions.
/// * `o` - Names in force, for the `::Instance` accessor lookup.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
///
/// # Returns
///
/// One row per singleton: `kind` (`tls`/`global`), the slot, the accessor
/// address (or `-`), and the class.
pub fn singletons_tsv(a: &Analysis, o: &Overlay, filter: &str) -> String {
    let want = filter.to_lowercase();
    let keep = |class: &str| want.is_empty() || class.to_lowercase().contains(&want);
    let mut instance: BTreeMap<String, u64> = BTreeMap::new();
    for f in &a.functions {
        let name = name_of(a, o, f.entry);
        if let Some(class) = name.strip_suffix("::Instance") {
            let e = instance.entry(class.to_owned()).or_insert(f.entry);
            *e = (*e).min(f.entry);
        }
    }
    let accessor = |class: &str| hex_or_dash(instance.get(class).copied());
    let tls: Vec<(&u64, &String)> = a
        .classes
        .tls_slots
        .iter()
        .filter(|(_, c)| keep(c))
        .collect();
    let globals: Vec<(&u64, &String)> = a
        .classes
        .global_hints
        .iter()
        .filter(|(_, c)| keep(c))
        .collect();
    let mut out = format!(
        "# {} thread-local + {} global singletons{}\n",
        tls.len(),
        globals.len(),
        narrows(globals.len(), SINGLETONS_MAX, "singletons")
    );
    out.push_str("kind\tslot\tinstance\tclass\n");
    for (off, class) in tls {
        let _ = writeln!(out, "tls\t{off:#x}\t{}\t{class}", accessor(class));
    }
    for (addr, class) in globals.into_iter().take(SINGLETONS_MAX) {
        let _ = writeln!(out, "global\t{addr:#x}\t{}\t{class}", accessor(class));
    }
    out
}
