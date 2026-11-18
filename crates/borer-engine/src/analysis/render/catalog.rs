//! Program-wide catalogs read from asserts: asserted fields, the source tree,
//! class ids and singletons, and the legend that keeps a repeated name out
//! of every row of a catalog.

use super::*;
use crate::analysis::members::Receiver;
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
/// against are written down. The listed members a class's asserts spell
/// follow, each paired with the field offset its code reads, strong,
/// contested or weak, with the sites that say so; last, the names asserts
/// spell bare paired the same way, each in the tier of its own
/// ([`bare_members`]).
pub fn asserted_fields_tsv(p: &Program, a: &Analysis, o: &Overlay, filter: &str) -> String {
    let want = filter.to_lowercase();
    let (fields, members) = asserted_members(p, a, o);
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
    let shown: BTreeSet<&str> = rows
        .iter()
        .take(FIELDS_MAX)
        .map(|(name, _)| name.as_str())
        .collect();
    out.push_str(&pairs_tsv(p, a, o, &members, &shown, &want, Receiver::This));
    let bare = bare_members(p, a, o);
    let names: BTreeSet<&str> = bare.keys().map(|(_, m)| m.as_str()).collect();
    out.push_str(&pairs_tsv(p, a, o, &bare, &names, &want, Receiver::Bare));
    out
}

/// Gathers what the binary's assertions say of the members of `this`.
///
/// It lists each member name with the functions, classes and conditions that
/// assert it, and each class's members with the functions that assert them
/// ([`Named`]).
///
/// The names are read from the listed literal, as far as the listing
/// reads one; the members to pair are read from the bytes at the
/// reference, as the pairing's votes read them
/// ([`crate::analysis::members::this_members`]): only a member read as a
/// value, within the first
/// [`MEMBER_STRING_CAP`](crate::analysis::members::MEMBER_STRING_CAP)
/// characters.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading the strings.
/// * `a` - Cross-references and functions.
/// * `o` - User names, for each function's class.
fn asserted_members(p: &Program, a: &Analysis, o: &Overlay) -> (BTreeMap<String, Asserted>, Named) {
    use crate::analysis::members::{MEMBER_STRING_CAP, Spelled, this_members};
    let mut fields: BTreeMap<String, Asserted> = BTreeMap::new();
    let mut members = Named::new();
    for (target, lit) in literal_targets(p, a).iter() {
        let sites = a.xrefs_to(*target);
        let mut owners: Vec<(String, u64)> = Vec::new();
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
            owners.clear();
            for site in sites {
                let Some(entry) = site.from_entry else {
                    continue;
                };
                e.functions.insert(entry);
                if let Some(class) = crate::analysis::classes::class_of(&name_of(a, o, entry)) {
                    e.classes.insert(class.to_owned());
                    owners.push((class.to_owned(), entry));
                }
            }
        }
        let Some((_, raw)) = cstr_at(p, *target, 4, MEMBER_STRING_CAP) else {
            continue;
        };
        for (name, how) in this_members(&raw) {
            if how != Spelled::Member {
                continue;
            }
            for (class, entry) in &owners {
                members
                    .entry((class.clone(), name.to_owned()))
                    .or_default()
                    .insert(*entry);
            }
        }
    }
    (fields, members)
}

/// Gathers the members each class's asserts spell bare (`!m_stop`), with
/// the methods that assert them.
///
/// A literal spelling no member after `this->` is read only where a
/// function passes it to an assert reporter
/// ([`crate::analysis::members::assert_conditions`]), and its candidates
/// are its identifiers read as values
/// ([`crate::analysis::members::condition_members`]). A local or a
/// parameter is spelled the same way, so these are never listed as names
/// and are paired only in a tier of their own. Each function's conditions
/// are read once per analysis and looked up by address, and a raised
/// cancel flag
/// ([`crate::cancel::Cancel`]) reads no further literal.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading the strings.
/// * `a` - Cross-references and functions.
/// * `o` - User names, for each function's class.
fn bare_members(p: &Program, a: &Analysis, o: &Overlay) -> Named {
    use crate::analysis::members::{
        CONDITION_MIN, MEMBER_STRING_CAP, Spelled, assert_conditions, condition_members,
    };
    let mut named = Named::new();
    for (target, _) in literal_targets(p, a)
        .iter()
        .take_while(|_| !crate::cancel::Cancel::raised())
    {
        let Some((_, raw)) = cstr_at(p, *target, CONDITION_MIN, MEMBER_STRING_CAP) else {
            continue;
        };
        let (spelled, how) = condition_members(&raw);
        let members: Vec<&String> = spelled
            .iter()
            .filter(|(_, s)| *s == Spelled::Member)
            .map(|(m, _)| m)
            .collect();
        if how != Receiver::Bare || members.is_empty() {
            continue;
        }
        let entries: BTreeSet<u64> = a
            .xrefs_to(*target)
            .iter()
            .filter_map(|s| s.from_entry)
            .collect();
        for entry in entries {
            let passed = assert_conditions(p, a, entry).contains_key(target);
            let name = name_of(a, o, entry);
            let Some(class) = passed
                .then(|| crate::analysis::classes::class_of(&name))
                .flatten()
            else {
                continue;
            };
            for member in &members {
                let key = (class.to_owned(), (*member).clone());
                named.entry(key).or_default().insert(entry);
            }
        }
    }
    named
}

/// The functions whose asserts spell each member of `this`, by class and
/// member; a member called as a method (`this->IsSet()`) is a getter, not
/// a member, and is left out.
pub(super) type Named = BTreeMap<(String, String), BTreeSet<u64>>;

/// Most functions whose asserts one read pairs with offsets.
pub(super) const PAIR_FUNCTIONS_MAX: usize = 400;

/// Fewest distinct functions whose single-offset assert sites agree on
/// one offset that make a pairing strong.
pub(super) const STRONG_SITES: usize = 2;

/// Most pairing rows listed in one read.
pub(super) const PAIRS_MAX: usize = 200;

/// Most evidence sites one pairing lists.
pub(super) const SITES_SHOWN: usize = 4;

/// How firmly the code around a class's asserts ties a member to one
/// field offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Tier {
    /// The single-offset sites of [`STRONG_SITES`] or more functions
    /// agree on the offset, no site names another member there, and every
    /// asserting function of the class was read.
    Strong,
    /// Single-offset sites put the member at two offsets, or another
    /// member at its offset; listed per offset, never resolved.
    Contested,
    /// Fewer than [`STRONG_SITES`] functions' single-offset sites, whose
    /// offset the row gives, or none; or a pairing that would be strong in
    /// a class whose asserting functions were not all read.
    Weak,
    /// Single-offset sites whose asserts spell the name bare: a local or a
    /// parameter that holds the field is spelled the same way, so the
    /// pairing is never strong and never stated.
    Bare,
}

impl Tier {
    /// Returns the word a pairing row spells the tier with.
    fn word(self) -> &'static str {
        match self {
            Tier::Strong => "strong",
            Tier::Contested => "contested",
            Tier::Weak => "weak",
            Tier::Bare => "bare",
        }
    }
}

/// One pairing row: tier, class, member, offset (`None` when no site reads
/// one field), evidence.
type PairRow<'a> = (Tier, &'a str, &'a str, Option<u64>, String);

/// Pairs each member a class's asserts spell with the field offset the
/// code around the asserts reads.
///
/// A site is one guarded assert whose guard reads exactly one field of
/// `this` directly and whose expression spells exactly one member
/// ([`crate::analysis::classes::assert_votes`]): `if (*(uint32_t*)(this +
/// 0x270) == 0) { assert("this->m_name", ...) }` puts `m_name` at 0x270.
/// A member whose sites agree is strong when [`STRONG_SITES`] distinct
/// functions hold them and weak below; one whose sites disagree, or whose
/// offset another member's sites claim, is contested, and every offset is
/// listed with its own sites, since a missed pairing costs a reader less
/// than a false one. A member no site reads one field for is weak with no
/// offset, its evidence the functions that assert it. Names spelled bare
/// ([`Receiver::Bare`]) are all [`Tier::Bare`], each offset with its own
/// sites, and one no site reads one field for is left out, since nothing
/// shows it is a member and not a local. The listed classes'
/// asserting functions are read round-robin by class, at most
/// [`PAIR_FUNCTIONS_MAX`] ([`budgeted`]), since another member's site can
/// contest an offset; a class with functions left unread says how many,
/// and a pairing it would make strong is weak, not verified.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
/// * `named` - Every class's asserted members ([`Named`]).
/// * `shown` - The member names the listing shows.
/// * `want` - The listing's filter, lower-cased: a shown member is
///   paired when its name or its class contains it.
/// * `receiver` - How the asserts in `named` spell the members.
///
/// # Returns
///
/// The section as text ([`render_pairs`]), empty when no listed member
/// has a class.
fn pairs_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    named: &Named,
    shown: &BTreeSet<&str>,
    want: &str,
    receiver: Receiver,
) -> String {
    let keep = |class: &str, member: &str| {
        shown.contains(member)
            && (want.is_empty()
                || member.to_lowercase().contains(want)
                || class.to_lowercase().contains(want))
    };
    let classes: BTreeSet<&str> = named
        .keys()
        .filter(|(class, member)| keep(class.as_str(), member.as_str()))
        .map(|(class, _)| class.as_str())
        .collect();
    if classes.is_empty() {
        return String::new();
    }
    let mut by_class: BTreeMap<&str, BTreeSet<u64>> = BTreeMap::new();
    for ((class, _), entries) in named {
        if classes.contains(class.as_str()) {
            by_class.entry(class.as_str()).or_default().extend(entries);
        }
    }
    let read = budgeted(&by_class, PAIR_FUNCTIONS_MAX);
    let unread: BTreeMap<&str, usize> = by_class
        .iter()
        .map(|(class, entries)| {
            let n = entries
                .iter()
                .filter(|e| read.binary_search(e).is_err())
                .count();
            (*class, n)
        })
        .collect();
    let asserting: usize = by_class.values().map(BTreeSet::len).sum();
    let (sites, owners) = assert_sites(p, a, o, &read, receiver);
    let mut rows: Vec<PairRow<'_>> = Vec::new();
    for ((class, member), entries) in named
        .iter()
        .filter(|((c, m), _)| keep(c.as_str(), m.as_str()))
    {
        let missed = unread.get(class.as_str()).copied().unwrap_or(0);
        let note = if missed > 0 {
            format!("; {missed} of the class's asserting functions not read")
        } else {
            String::new()
        };
        let Some(by_off) = sites.get(&(class.clone(), member.clone())) else {
            if receiver == Receiver::Bare {
                continue;
            }
            let evidence = site_list(entries.iter().map(|&e| (e, 1)));
            rows.push((
                Tier::Weak,
                class.as_str(),
                member.as_str(),
                None,
                format!("{evidence}{note}"),
            ));
            continue;
        };
        let others = |off: u64| {
            owners
                .get(&(class.clone(), off))
                .into_iter()
                .flatten()
                .filter(|m| *m != member)
                .map(String::as_str)
                .collect::<Vec<&str>>()
        };
        let contested = by_off.len() > 1 || by_off.keys().any(|&off| !others(off).is_empty());
        for (&off, at) in by_off {
            let tier = match (receiver, contested, at.len() >= STRONG_SITES, missed > 0) {
                (Receiver::Bare, ..) => Tier::Bare,
                (Receiver::This, true, ..) => Tier::Contested,
                (Receiver::This, false, true, false) => Tier::Strong,
                (Receiver::This, false, ..) => Tier::Weak,
            };
            let mut evidence = site_list(at.iter().map(|(&e, &n)| (e, n)));
            let also = others(off);
            if !also.is_empty() {
                let _ = write!(evidence, "; {off:#x} also asserted as {}", also.join(", "));
            }
            if tier == Tier::Weak && at.len() >= STRONG_SITES && missed > 0 {
                evidence.push_str("; strong by these sites, not verified against the rest");
            }
            rows.push((
                tier,
                class.as_str(),
                member.as_str(),
                Some(off),
                format!("{evidence}{note}"),
            ));
        }
    }
    rows.sort_by_key(|row| row.0);
    render_pairs(o, &rows, read.len(), asserting, receiver)
}

/// Picks the functions to read, round-robin by group (a class, a source
/// file): each group's first, then each one's second, until `max`, so a
/// group late in the order is read as far as an early one.
///
/// # Arguments
///
/// * `groups` - Each group's functions, by group.
/// * `max` - Most functions picked.
///
/// # Returns
///
/// The functions, in address order.
fn budgeted<K, V: std::borrow::Borrow<BTreeSet<u64>>>(
    groups: &BTreeMap<K, V>,
    max: usize,
) -> Vec<u64> {
    let lists: Vec<Vec<u64>> = groups
        .values()
        .map(|entries| entries.borrow().iter().copied().collect())
        .collect();
    let longest = lists.iter().map(Vec::len).max().unwrap_or(0);
    let mut picked: BTreeSet<u64> = BTreeSet::new();
    for round in 0..longest {
        for entry in lists.iter().filter_map(|l| l.get(round)) {
            if picked.len() >= max {
                return picked.into_iter().collect();
            }
            picked.insert(*entry);
        }
    }
    picked.into_iter().collect()
}

/// The single-offset assert sites of some functions: by class and member,
/// each offset's functions with how many sites each holds; and by class
/// and offset, the members asserted there.
type Sites = (
    BTreeMap<(String, String), BTreeMap<u64, BTreeMap<u64, usize>>>,
    BTreeMap<(String, u64), BTreeSet<String>>,
);

/// Gathers the single-offset assert sites of the functions in `read`
/// ([`crate::analysis::classes::assert_votes`]) under one spelling,
/// getters left out.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force, for each function's class.
/// * `read` - The functions, in address order.
/// * `receiver` - The spelling read.
fn assert_sites(p: &Program, a: &Analysis, o: &Overlay, read: &[u64], receiver: Receiver) -> Sites {
    let votes = crate::analysis::striped(read, |&entry| {
        crate::analysis::classes::assert_votes(p, a, o, entry, receiver)
    });
    let mut sites: Sites = (BTreeMap::new(), BTreeMap::new());
    for (&entry, votes) in read.iter().zip(&votes) {
        let Some(class) =
            crate::analysis::classes::class_of(&name_of(a, o, entry)).map(str::to_owned)
        else {
            continue;
        };
        for (off, member, n) in votes.iter().filter(|(_, m, _)| !m.ends_with(')')) {
            *sites
                .0
                .entry((class.clone(), member.clone()))
                .or_default()
                .entry(*off)
                .or_default()
                .entry(entry)
                .or_default() += n;
            sites
                .1
                .entry((class.clone(), *off))
                .or_default()
                .insert(member.clone());
        }
    }
    sites
}

/// Lists evidence sites as `0x1100, 0x1140 x2`, at most [`SITES_SHOWN`].
///
/// # Arguments
///
/// * `sites` - Each function with how many sites it holds, in address
///   order.
fn site_list(sites: impl Iterator<Item = (u64, usize)>) -> String {
    let all: Vec<String> = sites
        .map(|(entry, n)| {
            if n > 1 {
                format!("{entry:#x} x{n}")
            } else {
                format!("{entry:#x}")
            }
        })
        .collect();
    let shown: Vec<&str> = all.iter().take(SITES_SHOWN).map(String::as_str).collect();
    format!("{}{}", shown.join(", "), plus_more(all.len(), SITES_SHOWN))
}

/// Renders the pairing rows under their header, then the `set_type` call
/// that states each class's strong pairs the overlay does not state yet.
///
/// A strong pair is offered only under a name `set_type` takes, and never
/// over a different name the overlay already states at its offset; each
/// left out says why on a line of its own.
///
/// # Arguments
///
/// * `o` - Names in force, for what is stated already.
/// * `rows` - The rows, strong first.
/// * `read` - How many asserting functions were read.
/// * `asserting` - How many there were.
/// * `receiver` - How the rows' asserts spell their members.
///
/// # Returns
///
/// A header with the tiers' counts, a column header, one tab-separated
/// row per pairing (per offset for a contested one), at most
/// [`PAIRS_MAX`] with a `# N more` line for the rest, then one
/// `# state <class>'s strong pairs: set_type(...)` line per class and one
/// `#` line per pair left out. Bare rows have a header of their own and
/// nothing to state, and none is nothing at all.
fn render_pairs(
    o: &Overlay,
    rows: &[PairRow<'_>],
    read: usize,
    asserting: usize,
    receiver: Receiver,
) -> String {
    let count = |tier: Tier| rows.iter().filter(|row| row.0 == tier).count();
    let mut out = match receiver {
        Receiver::Bare if rows.is_empty() => return String::new(),
        Receiver::Bare => format!(
            "# {} bare pairings of names asserts spell without this-> with the field offsets their guards read: a bare name may be a local or a parameter that holds the field, so none is strong or stated",
            rows.len()
        ),
        Receiver::This => format!(
            "# {} pairings of asserted members with field offsets, from the code around each assert: {} strong (two or more functions' single-offset sites agree), {} contested (sites disagree; not resolved), {} weak (fewer than two functions, or not verified against the rest; offset - when no site reads one field)",
            rows.len(),
            count(Tier::Strong),
            count(Tier::Contested),
            count(Tier::Weak),
        ),
    };
    if read < asserting {
        let _ = write!(out, "; read {read} of {asserting} asserting functions");
    }
    out.push_str("\n# tier\tclass\tmember\toffset\tsites (function entries, xN for N sites)\n");
    let mut strong: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    let mut left: Vec<String> = Vec::new();
    for (tier, class, member, off, evidence) in rows.iter().take(PAIRS_MAX) {
        let _ = writeln!(
            out,
            "{}\t{class}\t{member}\t{}\t{evidence}",
            tier.word(),
            hex_or_dash(*off)
        );
        let Some(off) = off.filter(|_| *tier == Tier::Strong) else {
            continue;
        };
        match crate::analysis::stated::labels(o, class)
            .get(&off)
            .map(ToString::to_string)
        {
            Some(stated) if stated == *member => {}
            Some(stated) => left.push(format!(
                "# {class} +{off:#x} is stated as {stated}, not {member}: left as stated"
            )),
            None if !crate::analysis::utypes::is_ident(member) => left.push(format!(
                "# {class} +{off:#x} {member} is no name set_type takes: left out"
            )),
            None => strong
                .entry(*class)
                .or_default()
                .push(format!("\"{off:#x}:{member}\"")),
        }
    }
    more_line(
        &mut out,
        rows.len(),
        PAIRS_MAX,
        "pairings not listed; borer://asserts/<filter> narrows them",
    );
    for (class, fields) in strong {
        let _ = writeln!(
            out,
            "# state {class}'s strong pairs: set_type(name=\"{}\", fields=[{}])",
            class.replace('\\', "\\\\").replace('"', "\\\""),
            fields.join(", ")
        );
    }
    for line in left {
        out.push_str(&line);
        out.push('\n');
    }
    out
}

/// Most rows in one read of the source tree.
pub(super) const SOURCES_MAX: usize = 200;

/// Most functions one read of the matched files' assert expressions
/// decompiles.
pub(super) const EXPRESSION_FUNCTIONS_MAX: usize = 200;

/// Most assert expression rows listed in one read.
pub(super) const EXPRESSIONS_MAX: usize = 200;

/// One source file an assertion cites, and the functions that cite it.
#[derive(Debug)]
pub(super) struct SourceFile {
    /// The path as the binary cites it, separators normalized to `/`.
    pub(super) full: String,
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
/// is the files that match, each with the functions that came from it;
/// their assert expressions are [`source_vocabulary_tsv`]'s.
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
    let want = filter.to_lowercase();
    let files = cited_sources(p, a);
    let root = common_root(files.keys());
    let mut by_dir: BTreeMap<String, (usize, BTreeSet<u64>)> = BTreeMap::new();
    let mut total = 0usize;
    for (path, entries) in &files {
        let short = path.strip_prefix(&root).unwrap_or(path);
        total += entries.len();
        let dir = short.rsplit_once('/').map_or("(root)", |(d, _)| d);
        let e = by_dir.entry(dir.to_owned()).or_default();
        e.0 += 1;
        e.1.extend(entries.iter().copied());
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
        out.push_str(
            "# functions\tfiles\tdirectory (borer://sources/<filter> for the files and their assert expressions)\n",
        );
        for (dir, (n, entries)) in dirs.iter().take(SOURCES_MAX) {
            let _ = writeln!(out, "{}\t{n}\t{dir}", entries.len());
        }
        return out;
    }
    let rows = source_rows(&files, &root, &want);
    let mut out = format!(
        "# {} files match {}\n{base}",
        rows.len(),
        crate::text::quoted(filter)
    );
    out.push_str("# functions\tfirst\tfile\n");
    for r in rows.iter().take(SOURCES_MAX) {
        let _ = writeln!(out, "{}\t{:#x}\t{}", r.functions, r.first, r.path);
    }
    more_line(&mut out, rows.len(), SOURCES_MAX, "not listed");
    if !rows.is_empty() {
        let _ = writeln!(
            out,
            "# borer://vocab/{filter} lists the assert expressions of these files"
        );
    }
    out
}

/// Returns the cited files whose path, the build root dropped, holds
/// `want`, the busiest first.
///
/// # Arguments
///
/// * `files` - Every cited path with the functions citing it.
/// * `root` - The build root ([`common_root`]).
/// * `want` - The lower-cased filter; empty matches every file.
fn source_rows(files: &BTreeMap<String, BTreeSet<u64>>, root: &str, want: &str) -> Vec<SourceFile> {
    let mut rows: Vec<SourceFile> = files
        .iter()
        .filter_map(|(path, entries)| {
            let short = path.strip_prefix(root).unwrap_or(path);
            short.to_lowercase().contains(want).then(|| SourceFile {
                full: path.clone(),
                path: short.to_owned(),
                functions: entries.len(),
                first: entries.iter().copied().min().unwrap_or_default(),
            })
        })
        .collect();
    rows.sort_by_key(|r| (std::cmp::Reverse(r.functions), r.path.clone()));
    rows
}

/// Lists the assert expressions of the source files whose path contains
/// the filter, each file's most frequent first ([`expressions_tsv`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force, for the decompiled text.
/// * `filter` - Case-insensitive substring of the path, or empty for
///   every file.
///
/// # Returns
///
/// The table, or a `#` line saying no file matched.
pub fn source_vocabulary_tsv(p: &Program, a: &Analysis, o: &Overlay, filter: &str) -> String {
    let files = cited_sources(p, a);
    let root = common_root(files.keys());
    let rows = source_rows(&files, &root, &filter.to_lowercase());
    let matched: Vec<(&SourceFile, &BTreeSet<u64>)> = rows
        .iter()
        .filter_map(|r| files.get(&r.full).map(|e| (r, e)))
        .collect();
    if matched.is_empty() {
        return format!(
            "# no cited source file matches {}\n",
            crate::text::quoted(filter)
        );
    }
    expressions_tsv(p, a, o, &files, &matched)
}

/// Lists the assert expressions of the matched source files, each file's
/// most frequent first.
///
/// The asserts of one translation unit are its developers' own words for
/// the state its code guards (`speed <= maxSpeed`, `entity.IsValid()`),
/// which a decompiled body spells as offsets. The functions citing the
/// files are decompiled round-robin by file, at most
/// [`EXPRESSION_FUNCTIONS_MAX`] ([`budgeted`]), and each assert call
/// ([`crate::analysis::decompile::assert_calls`]) counts toward the file its own file argument names
/// (the text's escaped `\\` and a bare `\` read as `/`): a function's
/// assert citing another file, a header whose template it inlined, counts
/// there and not here.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
/// * `cited` - Every cited path with the functions citing it, which the
///   text's cut spelling of a path is matched back to ([`spelled_as`]).
/// * `matched` - The files, in the listing's order, with the functions
///   citing each.
///
/// # Returns
///
/// A header with the counts and how many functions were read, a column
/// header, and one tab-separated row per file and expression: the assert
/// calls, the functions holding them, the file and the expression, at
/// most [`EXPRESSIONS_MAX`] with a `# N more` line; empty when no file
/// matched.
fn expressions_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    cited: &BTreeMap<String, BTreeSet<u64>>,
    matched: &[(&SourceFile, &BTreeSet<u64>)],
) -> String {
    if matched.is_empty() {
        return String::new();
    }
    let citing: BTreeSet<u64> = matched
        .iter()
        .flat_map(|(_, e)| e.iter().copied())
        .collect();
    let by_file: BTreeMap<usize, &BTreeSet<u64>> = matched
        .iter()
        .enumerate()
        .map(|(at, (_, e))| (at, *e))
        .collect();
    let read = budgeted(&by_file, EXPRESSION_FUNCTIONS_MAX);
    let key = o.fingerprint();
    let texts = crate::analysis::striped(&read, |&entry| {
        crate::analysis::plain_text_cached(p, a, o, key, entry)
    });
    let file_of: BTreeMap<&str, usize> = matched
        .iter()
        .enumerate()
        .map(|(at, (f, _))| (f.full.as_str(), at))
        .collect();
    let wanted: BTreeSet<u64> = read.iter().copied().collect();
    let mut of: BTreeMap<u64, Vec<&str>> = BTreeMap::new();
    for (path, entries) in cited {
        for &e in entries.iter().filter(|e| wanted.contains(e)) {
            of.entry(e).or_default().push(path.as_str());
        }
    }
    let mut counts: BTreeMap<(usize, &str), (usize, BTreeSet<u64>)> = BTreeMap::new();
    let mut unplaced = 0usize;
    for (&entry, text) in read.iter().zip(&texts) {
        let paths = of.get(&entry).map_or(&[][..], Vec::as_slice);
        for line in text.as_deref().into_iter().flat_map(str::lines) {
            for (condition, spelled) in crate::analysis::decompile::assert_calls(line) {
                let Ok(path) = spelled_as(paths, spelled) else {
                    unplaced += 1;
                    continue;
                };
                let Some(&at) = file_of.get(path) else {
                    continue;
                };
                let e = counts.entry((at, condition)).or_default();
                e.0 += 1;
                e.1.insert(entry);
            }
        }
    }
    let mut rows: Vec<_> = counts.into_iter().collect();
    rows.sort_by_key(|((at, expr), (sites, fns))| {
        (
            *at,
            std::cmp::Reverse(*sites),
            std::cmp::Reverse(fns.len()),
            *expr,
        )
    });
    let decompiled = texts.iter().filter(|t| t.is_some()).count();
    let failed = read.len() - decompiled;
    let mut read_note = format!(
        "{decompiled} of the {} functions citing them read",
        citing.len()
    );
    if read.len() < citing.len() {
        let _ = write!(
            read_note,
            ", {EXPRESSION_FUNCTIONS_MAX} at most in total; a narrower filter reads the rest"
        );
    }
    if failed > 0 {
        let _ = write!(read_note, "; {failed} did not decompile");
    }
    if unplaced > 0 {
        let _ = write!(
            read_note,
            "; {unplaced} assert calls left out, their cut path fitting none or several of the paths their function cites"
        );
    }
    let mut out = format!(
        "# {} of {} assert expressions in the {} matched files, each file's most frequent first; {read_note}\n# asserts\tfunctions\tfile\texpression\n",
        rows.len().min(EXPRESSIONS_MAX),
        rows.len(),
        matched.len()
    );
    for ((at, expr), (sites, fns)) in rows.iter().take(EXPRESSIONS_MAX) {
        let file = matched.get(*at).map_or("", |(f, _)| f.path.as_str());
        let expr = expr.replace(['\t', '\n', '\r'], " ");
        let _ = writeln!(out, "{sites}\t{}\t{file}\t{expr}", fns.len());
    }
    more_line(
        &mut out,
        rows.len(),
        EXPRESSIONS_MAX,
        "expressions not listed",
    );
    out
}

/// Returns a path with an escaped `\\` and a bare `\` read as `/`.
///
/// # Arguments
///
/// * `path` - The path as a literal or a text spells it.
#[must_use]
pub(crate) fn slashed(path: &str) -> String {
    path.replace("\\\\", "/").replace('\\', "/")
}

/// Returns the one path among `paths` a cut spelling names.
///
/// The decompiler writes a cited path by its last two components
/// (`util/fourcc.h` for `C:\\ws\\util/fourcc.h`), so the spelling names the
/// paths equal to it or ending in `/` and it.
///
/// # Arguments
///
/// * `paths` - The full paths, `/`-separated.
/// * `spelled` - The spelling, in either separator.
///
/// # Returns
///
/// The path, or how many fit when that is not one.
///
/// # Errors
///
/// `0` when no path fits, or the count when several do.
pub(crate) fn spelled_as<'a, S: AsRef<str>>(
    paths: &'a [S],
    spelled: &str,
) -> Result<&'a str, usize> {
    let want = slashed(spelled);
    let tail = format!("/{want}");
    let fits: Vec<&str> = paths
        .iter()
        .map(AsRef::as_ref)
        .filter(|p| *p == want || p.ends_with(&tail))
        .collect();
    match fits.as_slice() {
        [one] => Ok(one),
        more => Err(more.len()),
    }
}

/// Returns the source paths the binary's literals name, each with the
/// functions referencing it.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading the strings.
/// * `a` - Cross-references and functions.
///
/// # Returns
///
/// The functions by path, separators normalized to `/`; a path nothing
/// references from a function is left out.
pub(crate) fn cited_sources(p: &Program, a: &Analysis) -> BTreeMap<String, BTreeSet<u64>> {
    let mut files: BTreeMap<String, BTreeSet<u64>> = BTreeMap::new();
    for (target, lit) in literal_targets(p, a).iter() {
        let sites = a.xrefs_to(*target);
        let Some(path) = lit.strip_prefix('"').and_then(|t| t.strip_suffix('"')) else {
            continue;
        };
        if !crate::analysis::decompile::is_source_path(path) {
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
    files
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
pub(crate) fn common_root<'a>(paths: impl Iterator<Item = &'a String>) -> String {
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

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{Receiver, Tier, budgeted, render_pairs, site_list};
    use crate::analysis::Overlay;
    use crate::analysis::stated::Field;

    /// The read budget is spent round-robin by class, so a class late in
    /// the order is read as far as an early one, and never past the cap.
    #[test]
    fn the_read_budget_reaches_every_class() {
        let mut by_class: BTreeMap<&str, BTreeSet<u64>> = BTreeMap::new();
        by_class.insert("A", (0..10).collect());
        by_class.insert("B", (100..103).collect());
        by_class.insert("C", BTreeSet::from([200]));
        assert_eq!(budgeted(&by_class, 5), [0, 1, 100, 101, 200]);
        assert_eq!(budgeted(&by_class, 100).len(), 14);
        assert!(budgeted(&by_class, 0).is_empty());
    }

    /// A pairing lists at most four sites and counts the rest, and a
    /// function holding several sites says how many.
    #[test]
    fn evidence_is_capped_and_counted() {
        let six = site_list((1..=6).map(|e| (e, 1)));
        assert_eq!(six, "0x1, 0x2, 0x3, 0x4 (+2 more)");
        assert_eq!(site_list([(0x10, 3)].into_iter()), "0x10 x3");
    }

    /// A strong pair is offered to `set_type` only under a name it takes and
    /// never over a different name stated at its offset.
    ///
    /// Each pair left out says why, one already stated is not offered again,
    /// and a read the budget cut says how far it got.
    #[test]
    fn a_strong_pair_never_overwrites_what_is_stated() {
        let strong = |member: &'static str, off: u64| {
            (
                Tier::Strong,
                "Widget",
                member,
                Some(off),
                "0x1100, 0x1140".to_owned(),
            )
        };
        let rows = [
            strong("m_name", 0x270),
            strong("m_size", 0x10),
            strong("m_kept", 0x20),
            strong("9lives", 0x30),
        ];
        let mut o = Overlay::default();
        let fields = o.fields.entry("Widget".to_owned()).or_default();
        for (off, name) in [(0x270, "m_name"), (0x10, "m_count")] {
            fields.insert(
                off,
                Field {
                    name: name.to_owned(),
                    ty: None,
                },
            );
        }
        let text = render_pairs(&o, &rows, 3, 5, Receiver::This);
        for line in [
            "; read 3 of 5 asserting functions\n",
            "# state Widget's strong pairs: set_type(name=\"Widget\", fields=[\"0x20:m_kept\"])\n",
            "# Widget +0x10 is stated as m_count, not m_size: left as stated\n",
            "# Widget +0x30 9lives is no name set_type takes: left out\n",
        ] {
            assert!(text.contains(line), "{line}{text}");
        }
        assert!(!text.contains("0x270:m_name"), "{text}");
        let odd = [(Tier::Strong, r#"Q"\x"#, "m_a", Some(8), String::new())];
        let quoted = render_pairs(&Overlay::default(), &odd, 1, 1, Receiver::This);
        assert!(
            quoted.contains(r#"set_type(name="Q\"\\x", fields=["0x8:m_a"])"#),
            "{quoted}"
        );
    }
}
