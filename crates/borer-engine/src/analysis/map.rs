//! The map: a program's namespaces and, in each, its classes by role, the
//! way a reader new to a large C++ program wants to meet it.
//!
//! A large program is a few hundred subsystems, each a namespace of
//! managers (the one instance that runs a system), components, widgets,
//! messages, commands and handlers. The role of a class follows from its
//! lineage and name: a pack's `[roles]` lines first (a family's base
//! classes and name prefixes), else the nearest ancestor whose name ends
//! with a role word (`...Widget`, `...Manager`, `...Component`), else its
//! own name.
//! Its one instance, if it has one, comes from the singleton slots, and its
//! size from how many functions carry its name. Laid out per namespace this
//! is a table of contents for the whole program, read from what the
//! analysis already holds.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::classes::class_of;
use super::{Analysis, Overlay, name_of};

/// Ancestors walked for a class's role.
const LINEAGE_MAX: usize = 16;
/// Roles the overview gives a column, the most common first.
const ROLE_COLUMNS: usize = 6;
/// The role of a class no rule places.
const PLAIN: &str = "class";
/// The namespace a class without one is listed under.
const GLOBAL: &str = "(global)";

/// One namespace's tally.
#[derive(Debug, Default)]
struct NsTally<'a> {
    /// Classes in the namespace.
    classes: usize,
    /// Classes by role.
    by_role: BTreeMap<&'a str, usize>,
    /// Functions named as members of its classes.
    methods: usize,
    /// Classes with one instance.
    singletons: usize,
}

/// The role rules in force, read once from the packs.
struct Roles<'a> {
    /// `[roles] prefix` lines: a name prefix and its role.
    prefix: Vec<(&'a str, &'a str)>,
    /// `[roles] class` lines: a base class and its role.
    base: Vec<(&'a str, &'a str)>,
    /// `[roles] word` lines, the word in lower case, and the role.
    word: Vec<(String, &'a str)>,
}

impl<'a> Roles<'a> {
    /// Reads the rules from the packs an analysis runs with.
    ///
    /// # Arguments
    ///
    /// * `analysis` - The analysis.
    fn of(analysis: &'a Analysis) -> Self {
        let packs = &analysis.packs;
        Roles {
            prefix: packs.pairs("roles", "prefix"),
            base: packs.pairs("roles", "class"),
            word: packs
                .pairs("roles", "word")
                .into_iter()
                .map(|(w, r)| (w.to_ascii_lowercase(), r))
                .collect(),
        }
    }

    /// Where a role sorts: the order its rule was given in, a plain class
    /// last.
    ///
    /// # Arguments
    ///
    /// * `role` - The role.
    fn rank(&self, role: &str) -> usize {
        self.prefix
            .iter()
            .chain(&self.base)
            .map(|(_, r)| *r)
            .chain(self.word.iter().map(|(_, r)| *r))
            .position(|r| r == role)
            .unwrap_or(usize::MAX)
    }
}

/// One class as the map shows it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MapClass {
    /// The qualified name.
    pub name: String,
    /// Its role: what a pack's `[roles]` line or a role word gives
    /// (`property`, `manager`, `widget`, `command`), else `class`.
    pub role: String,
    /// Its parent, when known.
    pub parent: Option<String>,
    /// Functions named as its members.
    pub methods: usize,
    /// Where its one instance lives: `tls+0x58` or a global's address.
    pub instance: Option<String>,
}

/// The role a class plays, by the packs' rules and its lineage.
///
/// A `[roles] prefix` its name starts with comes first, then a `[roles]
/// class` it derives from, then the nearest ancestor whose last name
/// component ends with a `[roles] word` (see [`ends_with_word`]), then its
/// own name. The lineage outranks the name: `Msg::ShowWidget`
/// derives from `Msg::Message` and is a message. A class no rule
/// places is a `class`.
///
/// # Arguments
///
/// * `analysis` - The recovered classes.
/// * `roles` - The rules in force.
/// * `class` - The class.
fn role_of(analysis: &Analysis, roles: &Roles<'_>, class: &str) -> String {
    if let Some((_, role)) = roles.prefix.iter().find(|(p, _)| class.starts_with(p)) {
        return (*role).to_owned();
    }
    let mut at = Some(class.to_owned());
    let mut lineage: Vec<String> = Vec::new();
    for _ in 0..LINEAGE_MAX {
        let Some(c) = at.take() else {
            break;
        };
        at = analysis
            .classes
            .by_name
            .get(&c)
            .and_then(|i| i.parent.clone());
        lineage.push(c);
    }
    if let Some((_, role)) = roles
        .base
        .iter()
        .find(|(base, _)| lineage.iter().skip(1).any(|s| s == base))
    {
        return (*role).to_owned();
    }
    lineage
        .iter()
        .skip(1)
        .chain(lineage.first())
        .find_map(|c| {
            let head = c.split('<').next().unwrap_or(c);
            let last = head.rsplit("::").next().unwrap_or(head);
            roles
                .word
                .iter()
                .find(|(w, _)| ends_with_word(last, w))
                .map(|(_, role)| (*role).to_owned())
        })
        .unwrap_or_else(|| PLAIN.to_owned())
}

/// Tells whether a name component ends with a role word, in any case, where
/// a word starts: at the start, at a capital, or after an underscore.
///
/// `ShowWidget`, `QWidget` and `io_service` end with `widget`, `widget` and
/// `service`; `Teleport` does not end with `port`.
///
/// # Arguments
///
/// * `component` - The last component of a class name.
/// * `word` - The word, in lower case.
fn ends_with_word(component: &str, word: &str) -> bool {
    let Some(at) = component.len().checked_sub(word.len()) else {
        return false;
    };
    let (Some(head), Some(tail)) = (component.get(..at), component.get(at..)) else {
        return false;
    };
    !word.is_empty()
        && tail.eq_ignore_ascii_case(word)
        && (head.is_empty()
            || head.ends_with('_')
            || tail.starts_with(|c: char| c.is_ascii_uppercase()))
}

/// A role's plural for a column header: `property` gives `properties`,
/// `class` gives `classes`, `widget` gives `widgets`.
///
/// # Arguments
///
/// * `role` - The role.
fn plural(role: &str) -> String {
    if let Some(stem) = role.strip_suffix('y')
        && !stem.ends_with(['a', 'e', 'o', 'u'])
    {
        return format!("{stem}ies");
    }
    if role.ends_with(['s', 'x']) || role.ends_with("ch") || role.ends_with("sh") {
        return format!("{role}es");
    }
    format!("{role}s")
}

/// The top namespace of a qualified name.
///
/// # Arguments
///
/// * `class` - The class.
fn namespace_of(class: &str) -> &str {
    class.split_once("::").map_or(GLOBAL, |(ns, _)| ns)
}

/// Every recovered class with its role, parent, method count and instance.
///
/// # Arguments
///
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
#[must_use]
pub fn classes(analysis: &Analysis, overlay: &Overlay) -> Vec<MapClass> {
    let mut methods: BTreeMap<String, usize> = BTreeMap::new();
    for f in &analysis.functions {
        let name = name_of(analysis, overlay, f.entry);
        if let Some(class) = class_of(&name) {
            *methods.entry(class.to_owned()).or_default() += 1;
        }
    }
    let mut instance: BTreeMap<&str, String> = BTreeMap::new();
    for (off, class) in &analysis.classes.tls_slots {
        instance
            .entry(class.as_str())
            .or_insert_with(|| format!("tls+{off:#x}"));
    }
    for (addr, class) in &analysis.classes.global_hints {
        instance
            .entry(class.as_str())
            .or_insert_with(|| format!("{addr:#x}"));
    }
    let names: BTreeSet<&String> = analysis.classes.by_name.keys().collect();
    let roles = Roles::of(analysis);
    names
        .into_iter()
        .filter(|n| !n.starts_with("class_"))
        .map(|name| MapClass {
            name: name.clone(),
            role: role_of(analysis, &roles, name),
            parent: analysis
                .classes
                .by_name
                .get(name)
                .and_then(|c| c.parent.clone()),
            methods: methods.get(name).copied().unwrap_or(0),
            instance: instance.get(name.as_str()).cloned(),
        })
        .collect()
}

/// Renders the map: with no namespace, one row per namespace counting its
/// classes by role; with one, a row per class in it.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `namespace` - A namespace (or any prefix of class names); empty for
///   the overview.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn map_tsv(analysis: &Analysis, overlay: &Overlay, namespace: &str, limit: usize) -> String {
    let all = classes(analysis, overlay);
    let rules = Roles::of(analysis);
    let mut out = String::new();
    if namespace.is_empty() {
        let mut by_ns: BTreeMap<&str, NsTally<'_>> = BTreeMap::new();
        let mut totals: BTreeMap<&str, usize> = BTreeMap::new();
        for c in &all {
            let e = by_ns.entry(namespace_of(&c.name)).or_default();
            e.classes += 1;
            *e.by_role.entry(c.role.as_str()).or_default() += 1;
            e.methods += c.methods;
            e.singletons += usize::from(c.instance.is_some());
            if c.role != PLAIN {
                *totals.entry(c.role.as_str()).or_default() += 1;
            }
        }
        let mut columns: Vec<(&str, usize)> = totals.into_iter().collect();
        columns.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        columns.truncate(ROLE_COLUMNS);
        let mut rows: Vec<_> = by_ns.into_iter().collect();
        rows.sort_by(|a, b| b.1.methods.cmp(&a.1.methods).then(a.0.cmp(b.0)));
        let _ = writeln!(
            out,
            "# {} classes in {} namespaces, showing {}; map/<namespace> lists one",
            all.len(),
            rows.len(),
            rows.len().min(limit)
        );
        out.push_str("namespace\tclasses");
        for (role, _) in &columns {
            let _ = write!(out, "\t{}", plural(role));
        }
        out.push_str("\tsingletons\tmethods\n");
        for (ns, tally) in rows.into_iter().take(limit) {
            let _ = write!(out, "{ns}\t{}", tally.classes);
            for (role, _) in &columns {
                let _ = write!(out, "\t{}", tally.by_role.get(role).copied().unwrap_or(0));
            }
            let _ = writeln!(out, "\t{}\t{}", tally.singletons, tally.methods);
        }
        return out;
    }
    let prefix = if namespace.ends_with("::") || namespace == GLOBAL {
        namespace.to_owned()
    } else {
        format!("{namespace}::")
    };
    let picked: Vec<&MapClass> = all
        .iter()
        .filter(|c| {
            if prefix == GLOBAL {
                !c.name.contains("::")
            } else {
                c.name.starts_with(&prefix)
            }
        })
        .collect();
    let mut roles: BTreeMap<&str, usize> = BTreeMap::new();
    for c in &picked {
        *roles.entry(c.role.as_str()).or_default() += 1;
    }
    let summary: Vec<String> = roles.iter().map(|(r, n)| format!("{n} {r}")).collect();
    let _ = writeln!(
        out,
        "# {} classes under {}: {}, showing {}",
        picked.len(),
        crate::text::one_line(prefix.trim_end_matches("::")),
        if summary.is_empty() {
            "none".to_owned()
        } else {
            summary.join(", ")
        },
        picked.len().min(limit)
    );
    out.push_str("class\trole\tparent\tmethods\tinstance\n");
    let mut sorted = picked;
    sorted.sort_by(|a, b| {
        rules
            .rank(&a.role)
            .cmp(&rules.rank(&b.role))
            .then(b.methods.cmp(&a.methods))
            .then(a.name.cmp(&b.name))
    });
    for c in sorted.into_iter().take(limit) {
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}\t{}",
            c.name,
            c.role,
            c.parent.as_deref().unwrap_or("-"),
            c.methods,
            c.instance.as_deref().unwrap_or("-")
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::vtables::ClassInfo;

    /// An ancestor's role word outranks the class's own name, and a word
    /// matches only where a word starts.
    ///
    /// # Panics
    ///
    /// When a role differs.
    #[test]
    fn the_lineage_outranks_the_name() {
        let mut a = Analysis::default();
        let class = |name: &str, parent: Option<&str>| ClassInfo {
            name: name.to_owned(),
            parent: parent.map(str::to_owned),
            ..ClassInfo::default()
        };
        a.classes
            .by_name
            .insert("Msg::Message".into(), class("Msg::Message", None));
        a.classes.by_name.insert(
            "Msg::ShowWidget".into(),
            class("Msg::ShowWidget", Some("Msg::Message")),
        );
        let rules = Roles::of(&a);
        assert_eq!(role_of(&a, &rules, "Msg::ShowWidget"), "message");
        assert_eq!(role_of(&a, &rules, "App::Hop"), "class");
        assert_eq!(role_of(&a, &rules, "asio::io_service"), "service");
        assert!(ends_with_word("QWidget", "widget"));
        assert!(!ends_with_word("Teleport", "port"));
        assert!(!ends_with_word("x", "widget"));
    }

    /// A class is a property when its name or an ancestor's ends with
    /// `Property`, a command by its own name, and a plain class otherwise;
    /// a pack's prefix and base-class lines come first.
    ///
    /// # Panics
    ///
    /// When a role differs.
    #[test]
    fn a_role_follows_the_lineage() {
        let mut a = Analysis::default();
        let class = |name: &str, parent: Option<&str>| ClassInfo {
            name: name.to_owned(),
            parent: parent.map(str::to_owned),
            ..ClassInfo::default()
        };
        a.classes
            .by_name
            .insert("Base::Property".into(), class("Base::Property", None));
        a.classes.by_name.insert(
            "Properties::Base".into(),
            class("Properties::Base", Some("Base::Property")),
        );
        a.classes.by_name.insert(
            "Properties::Mover".into(),
            class("Properties::Mover", Some("Properties::Base")),
        );
        a.classes
            .by_name
            .insert("Util::Thing".into(), class("Util::Thing", None));
        let rules = Roles::of(&a);
        assert_eq!(role_of(&a, &rules, "Properties::Mover"), "property");
        assert_eq!(
            role_of(&a, &rules, "Base::Property"),
            "property",
            "a base plays its role by its own name"
        );
        assert_eq!(role_of(&a, &rules, "Cmd::MoveCommand"), "command");
        assert_eq!(role_of(&a, &rules, "Util::Thing"), "class");
        assert_eq!(role_of(&a, &rules, "Ui::QPushWidget<int>"), "widget");
        let text = map_tsv(&a, &Overlay::default(), "", 10);
        assert!(text.starts_with("# 4 classes in 3 namespaces"), "{text}");
        assert!(
            text.contains("namespace\tclasses\tproperties\tsingletons\tmethods\n"),
            "{text}"
        );
        assert!(text.contains("\nProperties\t2\t2\t"), "{text}");
        assert_eq!(plural("property"), "properties");
        assert_eq!(plural("class"), "classes");
        assert_eq!(plural("key"), "keys");
        let one = map_tsv(&a, &Overlay::default(), "Properties", 10);
        assert!(
            one.starts_with("# 2 classes under Properties: 2 property"),
            "{one}"
        );
        assert!(
            one.contains("Properties::Mover\tproperty\tProperties::Base\t0\t-\n"),
            "{one}"
        );
        let (pack, _) = crate::pack::Pack::parse(
            "pack t 1\n[roles]\nprefix Util:: utility\nclass Properties::Base mover\n",
            "t",
        )
        .expect("reads");
        a.packs = std::sync::Arc::new(crate::pack::Packs { packs: vec![pack] });
        let rules = Roles::of(&a);
        assert_eq!(role_of(&a, &rules, "Util::Thing"), "utility");
        assert_eq!(role_of(&a, &rules, "Properties::Mover"), "mover");
        assert_eq!(role_of(&a, &rules, "Properties::Base"), "property");
    }
}
