//! Cross-reference listings: the sites referencing an address, one row
//! per function making them, as rows and as the text spelled from them.

use super::*;

/// Reference groups listed per page unless a limit says otherwise.
pub const XREF_ROWS_DEFAULT: usize = 60;
/// Most reference groups one page lists.
pub const XREF_ROWS_MAX: usize = 500;

/// What a cross-reference listing shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum XrefView {
    /// The header line only.
    Count,
    /// One page of groups.
    Page {
        /// Groups to skip first.
        offset: usize,
        /// Most groups to list; clamped to [`XREF_ROWS_MAX`].
        limit: usize,
    },
}

/// Renders the cross-references to one address, collapsing the sites whose
/// functions run the same code.
///
/// [`xrefs`] with the page spelled as `offset`, `limit` and `count_only`.
///
/// # Arguments
///
/// * `p` - The loaded image, for its imports.
/// * `a` - The analysis.
/// * `o` - User names for the containing functions.
/// * `target` - The referenced address.
/// * `offset` - Groups to skip first.
/// * `limit` - Most groups to list; clamped to [`XREF_ROWS_MAX`].
/// * `count_only` - Only the header line.
///
/// # Returns
///
/// As [`xrefs`].
pub fn xrefs_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    target: u64,
    offset: usize,
    limit: usize,
    count_only: bool,
) -> String {
    let view = if count_only {
        XrefView::Count
    } else {
        XrefView::Page { offset, limit }
    };
    xrefs(p, a, o, target, view)
}

/// Renders the cross-references to one address ([`xref_rows`],
/// [`XrefRows::spell`]).
///
/// # Arguments
///
/// * `p` - The loaded image, for its imports.
/// * `a` - The analysis.
/// * `o` - User names for the containing functions.
/// * `target` - The referenced address.
/// * `view` - The header alone, or which page of groups.
///
/// # Returns
///
/// The text [`XrefRows::spell`] spells.
pub fn xrefs(p: &Program, a: &Analysis, o: &Overlay, target: u64, view: XrefView) -> String {
    xref_rows(p, a, o, target, view).spell()
}

/// One row of a cross-reference listing: a function's sites, standing for
/// every function that runs the same code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XrefRow {
    /// The function the sites are in; `None` for a pointer stored in data.
    pub entry: Option<u64>,
    /// The function's name in force; `-` for a pointer stored in data.
    pub name: String,
    /// Its sites in address order, each with what it does.
    pub sites: Vec<(u64, RefKind)>,
    /// Entries of the other functions running the same code, in address
    /// order; their sites are counted in the group, not listed.
    pub folded: Vec<u64>,
    /// Names of the first [`SAME_CODE_NAMES_MAX`] of [`XrefRow::folded`].
    pub folded_names: Vec<String>,
}

/// One page of a cross-reference listing, with what its header counts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XrefRows {
    /// The referenced addresses: the one asked for, then, for an import,
    /// its other slots and the stubs jumping through one, in address order
    /// ([`xref_rows_of_import`]).
    pub targets: Vec<u64>,
    /// Reference sites to the targets.
    pub sites: usize,
    /// A target filled the sites kept per target, so more exist than
    /// [`XrefRows::sites`] counts.
    pub capped: bool,
    /// Groups in all, on every page.
    pub groups: usize,
    /// The walk ran out of instruction budget ([`Analysis::incomplete`]).
    pub incomplete: bool,
    /// The calls and jumps left unresolved, said when the target has few
    /// callers ([`unseen_line`]); `None` when there is nothing to say.
    pub unseen: Option<String>,
    /// Groups skipped before the page; `None` for the header alone
    /// ([`XrefView::Count`]).
    pub offset: Option<usize>,
    /// The page's rows, the group covering the most sites first.
    pub rows: Vec<XrefRow>,
}

impl XrefRows {
    /// Returns the listing as the `xrefs` tool and the CLI print it.
    ///
    /// # Returns
    ///
    /// A `# N xrefs to <target> in G groups, showing S of G from O` header,
    /// the incomplete-walk and unresolved-call lines when they apply, a
    /// column header, then one `function: site kind, site kind` row per
    /// group, ending with how many more functions run the same code when
    /// the group folds several, and the next page's offset when more groups
    /// follow; a pointer stored in data is in function `-`. The count-only
    /// view is the first line and its notes alone.
    #[must_use]
    pub fn spell(&self) -> String {
        let count = if self.capped {
            format!(
                "{}+ (capped: more sites exist than are kept per target)",
                self.sites
            )
        } else {
            self.sites.to_string()
        };
        let targets: Vec<String> = self.targets.iter().map(|t| format!("{t:#x}")).collect();
        let groups_word = if self.groups == 1 { "group" } else { "groups" };
        let mut out = format!(
            "# {count} xrefs to {} in {} {groups_word}",
            targets.join(", "),
            self.groups
        );
        let notes = incomplete_line(self.incomplete) + self.unseen.as_deref().unwrap_or_default();
        let Some(offset) = self.offset else {
            let _ = write!(out, "\n{notes}");
            return out;
        };
        let _ = write!(
            out,
            ", showing {} of {} from {offset}\n{notes}# function: site kind, ...\n",
            self.rows.len(),
            self.groups
        );
        for r in &self.rows {
            let sites: Vec<String> = r
                .sites
                .iter()
                .map(|(va, kind)| format!("{va:#x} {}", kind.word()))
                .collect();
            let _ = write!(out, "{}: {}", r.name, sites.join(", "));
            out.push_str(&same_code_spelled(r.folded.len(), &r.folded_names));
            out.push('\n');
        }
        let next = offset.saturating_add(self.rows.len());
        if next < self.groups {
            let _ = writeln!(
                out,
                "# {} more groups; offset={next} for the next page",
                self.groups - next
            );
        }
        out
    }
}

/// Returns the cross-references to one address as rows, one per function
/// making them, the functions that run the same code folded into one.
///
/// A hot function is called from hundreds of sites, and a row per site
/// named its function on every one: 525 of 585 consecutive rows on a game
/// client repeated the function of the row before. Each function is one
/// row, its sites in address order with their kinds, so the name is
/// printed once. A registration table points hundreds of one-shape thunks
/// at one string, and listing every one buries the functions that differ,
/// so the functions whose code is the same are one row too: the lowest
/// entry stands for them and the row counts the rest. A target with a
/// handful of distinct callers is one row per caller.
///
/// The rows page: `offset` groups are skipped and at most `limit` listed,
/// and the header counts them all, so a target with more callers than one
/// page holds is read in pages rather than cut off. The group covering the
/// most sites comes first.
///
/// # Arguments
///
/// * `p` - The loaded image, for its imports.
/// * `a` - The analysis.
/// * `o` - User names for the containing functions.
/// * `target` - The referenced address.
/// * `view` - The header alone, or which page of groups.
///
/// # Returns
///
/// The page's rows, none for the header alone, with what the header
/// counts.
#[must_use]
pub fn xref_rows(p: &Program, a: &Analysis, o: &Overlay, target: u64, view: XrefView) -> XrefRows {
    let sites = a.xrefs_to(target);
    let capped = sites.len() >= crate::analysis::functions::XREF_SITES_PER_TARGET;
    rows_of_sites(p, a, o, vec![target], sites, capped, view)
}

/// Returns the cross-references to one library's symbol as rows: those to
/// every slot the loader lists for it and to every stub that jumps through
/// one, each site once.
///
/// An import's references are per slot, and a call through a thunk is a
/// call of the thunk, so asking who calls an import at one slot misses the
/// rest. The slots are the ones the decompiled text groups as one import
/// ([`crate::analysis::decompile::view`]): an ELF import's GOT and PLT
/// slots are one, two libraries exporting one name are two.
///
/// # Arguments
///
/// * `p` - The loaded image, for its imports.
/// * `a` - The analysis.
/// * `o` - User names for the containing functions.
/// * `import` - One slot of the import.
/// * `view` - The header alone, or which page of groups.
///
/// # Returns
///
/// The rows as [`xref_rows`] gives them, the targets `import` first and the
/// rest in address order, each once; `None`
/// when no import symbol has a slot at `import`.
#[must_use]
pub fn xref_rows_of_import(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    import: u64,
    view: XrefView,
) -> Option<XrefRows> {
    let slots = crate::analysis::decompile::view::import_slots(p, a, import)?;
    let stubs = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_some_and(|t| slots.contains(&t)))
        .map(|f| f.entry);
    let others: BTreeSet<u64> = slots
        .iter()
        .copied()
        .chain(stubs)
        .filter(|&t| t != import)
        .collect();
    let targets: Vec<u64> = std::iter::once(import).chain(others).collect();
    let mut sites: Vec<RefSite> = targets
        .iter()
        .flat_map(|&t| a.xrefs_to(t).iter().cloned())
        .collect();
    sites.sort_by_key(|s| s.va);
    sites.dedup_by(|x, y| x.va == y.va && x.kind == y.kind);
    let capped = targets
        .iter()
        .any(|&t| a.xrefs_to(t).len() >= crate::analysis::functions::XREF_SITES_PER_TARGET);
    Some(rows_of_sites(p, a, o, targets, &sites, capped, view))
}

/// Groups reference sites into a listing's rows ([`xref_rows`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names for the containing functions.
/// * `targets` - The referenced addresses, the one asked for first.
/// * `sites` - Their sites, in address order.
/// * `capped` - Whether a target filled the sites kept per target.
/// * `view` - The header alone, or which page of groups.
///
/// # Returns
///
/// The page's rows with what the header counts.
fn rows_of_sites(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    targets: Vec<u64>,
    sites: &[RefSite],
    capped: bool,
    view: XrefView,
) -> XrefRows {
    let mut by_function: BTreeMap<Option<u64>, Vec<&RefSite>> = BTreeMap::new();
    for s in sites {
        by_function.entry(s.from_entry).or_default().push(s);
    }
    let mut families: BTreeMap<u64, XrefGroup<'_>> = BTreeMap::new();
    let mut ordered: Vec<XrefGroup<'_>> = Vec::new();
    for (&entry, fn_sites) in &by_function {
        let group = XrefGroup {
            entry,
            sites: fn_sites,
            others: Vec::new(),
            total: fn_sites.len(),
        };
        match entry.and_then(|e| a.function(e).map(|f| (e, f.shape_hash))) {
            Some((e, shape)) => {
                if let Some(held) = families.get_mut(&shape) {
                    held.others.push(e);
                    held.total += fn_sites.len();
                } else {
                    families.insert(shape, group);
                }
            }
            None => ordered.push(group),
        }
    }
    ordered.extend(families.into_values());
    ordered.sort_by_key(|g| (std::cmp::Reverse(g.total), g.sites.first().map(|s| s.va)));
    let target = targets.first().copied().unwrap_or_default();
    let callers = sites.iter().filter(|s| s.is_branch()).count();
    let short = callers < unseen::SHORT_CALLERS && (callers > 0 || a.function_at(target).is_some());
    let unseen = short
        .then(|| unseen_line(p, a, Reach::Program, "#"))
        .flatten();
    let (offset, rows) = match view {
        XrefView::Count => (None, Vec::new()),
        XrefView::Page { offset, limit } => {
            let rows = ordered
                .iter()
                .skip(offset)
                .take(limit.clamp(1, XREF_ROWS_MAX))
                .map(|g| XrefRow {
                    entry: g.entry,
                    name: g.entry.map_or_else(|| "-".to_owned(), |e| name_of(a, o, e)),
                    sites: g.sites.iter().map(|s| (s.va, s.kind)).collect(),
                    folded: g.others.clone(),
                    folded_names: g
                        .others
                        .iter()
                        .take(SAME_CODE_NAMES_MAX)
                        .map(|&e| name_of(a, o, e))
                        .collect(),
                })
                .collect();
            (Some(offset), rows)
        }
    };
    XrefRows {
        targets,
        sites: sites.len(),
        capped,
        groups: ordered.len(),
        incomplete: a.incomplete,
        unseen,
        offset,
        rows,
    }
}

/// Names the functions a row folds in because they run the same code as
/// the one it shows, so each stays reachable from the listing.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names.
/// * `others` - Entries of the folded functions, in address order.
///
/// # Returns
///
/// As [`same_code_spelled`].
pub(super) fn same_code(a: &Analysis, o: &Overlay, others: &[u64]) -> String {
    let names: Vec<String> = others
        .iter()
        .take(SAME_CODE_NAMES_MAX)
        .map(|&e| name_of(a, o, e))
        .collect();
    same_code_spelled(others.len(), &names)
}

/// Spells the functions a row folds in because they run the same code.
///
/// # Arguments
///
/// * `folded` - How many functions were folded.
/// * `names` - The names of the first [`SAME_CODE_NAMES_MAX`] of them.
///
/// # Returns
///
/// ` (+N functions running the same code): name, name` with `...` past the
/// names when more were folded; empty when nothing was.
fn same_code_spelled(folded: usize, names: &[String]) -> String {
    if folded == 0 {
        return String::new();
    }
    let more = if folded > SAME_CODE_NAMES_MAX {
        ", ..."
    } else {
        ""
    };
    format!(
        " (+{folded} function{} running the same code): {}{more}",
        plural(folded),
        names.join(", ")
    )
}

/// Most folded functions a listing row names; the count covers the rest.
pub const SAME_CODE_NAMES_MAX: usize = 8;

/// A function's sites in a cross-reference listing while it is grouped,
/// standing for every function that runs the same code.
#[derive(Debug, Clone)]
struct XrefGroup<'a> {
    /// The function the sites are in; `None` for a pointer stored in data.
    entry: Option<u64>,
    /// Its sites, in address order.
    sites: &'a [&'a RefSite],
    /// The other functions running the same code, in address order.
    others: Vec<u64>,
    /// Sites across the whole family, what the groups are ordered by.
    total: usize,
}
