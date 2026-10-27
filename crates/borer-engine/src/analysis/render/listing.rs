//! Function and symbol tables, one function's detail and cross-references,
//! and whole-function disassembly.

use super::*;
use crate::analysis::qt::QtMethodKind;
use crate::isa::{Isa, a64};
use crate::num::lo8;
use crate::program::Symbol;
use crate::search::demangled_or_raw;

/// The order a function listing is in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FunctionOrder {
    /// By entry address, ascending.
    #[default]
    Address,
    /// By size in bytes, the largest first, ties by entry: the biggest
    /// functions of a 94,000-function image without paging through it.
    Size,
}

/// Renders the paged function table.
///
/// An import thunk, `jmp [slot]` under an address of the program's own, is
/// left out unless the filter is `thunk`, which lists only them: 272 of
/// one Qt launcher's 2,233 discovered functions are thunks, and a count or
/// a filtered page that holds them says less about the program's code.
/// The header says how many were left out.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names, applied to the `name` column and the filter.
/// * `filter` - Case-insensitive substring matched against the name or the
///   entry hex, which is also matched with a leading `0x` stripped.
/// * `order` - By entry, or the largest first.
/// * `offset` - Matches to skip first (paging).
/// * `limit` - Maximum rows to render.
///
/// # Returns
///
/// `(shown, total, text)`: the text starts with `# showing N of M functions`
/// (`, largest first` under [`FunctionOrder::Size`]), a `# warning:` line
/// when the analysis ran out of instruction budget, and a column header,
/// then one `entry size blocks instrs callers callees name` row per
/// function.
pub fn functions_tsv(
    a: &Analysis,
    o: &Overlay,
    filter: Option<&str>,
    order: FunctionOrder,
    offset: usize,
    limit: usize,
) -> (usize, usize, String) {
    let q = filter.map(str::to_lowercase);
    let only_thunks = q.as_deref() == Some("thunk");
    let only_funclets = q.as_deref() == Some("funclet");
    let hex_q = q
        .as_deref()
        .map_or("", |q| q.strip_prefix("0x").unwrap_or(q));
    let mut thunks = 0usize;
    let mut funclets = 0usize;
    let mut matched: Vec<&Function> = a
        .functions
        .iter()
        .filter(|f| {
            if only_thunks {
                return f.thunk.is_some();
            }
            if only_funclets {
                return f.funclet.is_some();
            }
            if f.thunk.is_some() {
                thunks += 1;
                return false;
            }
            if f.funclet.is_some() {
                funclets += 1;
                return false;
            }
            match &q {
                Some(q) => function_matches(f, o, q, hex_q),
                None => true,
            }
        })
        .collect();
    let order_note = match order {
        FunctionOrder::Address => "",
        FunctionOrder::Size => {
            matched.sort_by_cached_key(|f| (std::cmp::Reverse(f.size()), f.entry));
            ", largest first"
        }
    };
    let total = matched.len();
    let shown = total.saturating_sub(offset).min(limit);
    let mut left_out = String::new();
    if thunks > 0 {
        let _ = write!(
            left_out,
            "; {thunks} import thunks left out, filter=thunk lists them"
        );
    }
    if funclets > 0 {
        let _ = write!(
            left_out,
            "; {funclets} exception funclets left out, filter=funclet lists them"
        );
    }
    let noun = if only_thunks {
        "import thunks"
    } else if only_funclets {
        "exception funclets"
    } else {
        "functions"
    };
    let mut out = format!("# showing {shown} of {total} {noun}{order_note}{left_out}\n");
    if a.incomplete {
        out.push_str(INCOMPLETE_NOTE);
        out.push('\n');
    }
    out.push_str("# entry size blocks instrs callers callees src name\n");
    for f in matched.iter().skip(offset).take(limit) {
        let src = if o.names.contains_key(&f.entry) {
            "usr"
        } else {
            f.name_source.code()
        };
        let _ = writeln!(
            out,
            "{:#x} {} {} {} {} {} {src} {}",
            f.entry,
            f.size(),
            f.blocks.len(),
            f.instr_count,
            f.callers.len(),
            f.callees.len(),
            name_of(a, o, f.entry)
        );
    }
    (shown, total, out)
}

/// The digits `{:x}` spells a value with.
const HEX_DIGITS: &[u8; 16] = b"0123456789abcdef";

/// Whether one function passes [`functions_tsv`]'s lowered filter, testing
/// nothing a row would have to build.
///
/// A filtered listing tests every function, so the test borrows the overlay
/// or symbol name where it lies and folds case in place, and spells the
/// entry's hex into one stack buffer: no `name_of` clone, no lowered copy,
/// no `format!` per function. It answers exactly what testing [`name_of`]'s
/// spelling lowered against `q`, and the entry's hex against `hex_q`,
/// answered; the `sub_` spelling is that of a nameless function only.
///
/// # Arguments
///
/// * `f` - The function tested.
/// * `o` - User names, which win over the symbol name.
/// * `q` - The lowered filter.
/// * `hex_q` - The filter with a leading `0x` stripped, for the hex test.
///
/// # Returns
/// Whether the function is listed.
fn function_matches(f: &Function, o: &Overlay, q: &str, hex_q: &str) -> bool {
    let name = o
        .names
        .get(&f.entry)
        .map(String::as_str)
        .or(f.name.as_deref());
    if name.is_some_and(|n| lower_contains(n, q)) {
        return true;
    }
    let mut buf = [0u8; 20];
    buf[..4].copy_from_slice(b"sub_");
    let digits = hex_written(f.entry, &mut buf[4..]);
    (name.is_none() && ascii_lower_contains(&buf[..4 + digits], q.as_bytes()))
        || ascii_lower_contains(&buf[4..4 + digits], hex_q.as_bytes())
}

/// Case-insensitive substring test, what `hay.to_lowercase().contains(needle)`
/// answers, without the lowered copy of `hay`.
///
/// A filter runs this over every row, so an ASCII `hay` is folded byte by
/// byte in place, which is all `to_lowercase` does to it; any other `hay`
/// takes the allocating spelling, so the answer never differs. The needle
/// is already lowered by the caller.
///
/// # Arguments
///
/// * `hay` - The text searched.
/// * `needle` - The lowered substring sought.
///
/// # Returns
/// Whether `needle` appears in `hay` in any case.
fn lower_contains(hay: &str, needle: &str) -> bool {
    if needle.is_empty() {
        return true;
    }
    if hay.is_ascii() {
        return ascii_lower_contains(hay.as_bytes(), needle.as_bytes());
    }
    hay.to_lowercase().contains(needle)
}

/// Case-insensitive substring test over ASCII bytes.
///
/// # Arguments
///
/// * `hay` - The ASCII bytes searched.
/// * `needle` - The bytes sought, already in the case compared.
///
/// # Returns
/// Whether `needle` appears in `hay` case-folded; `true` for an empty
/// needle.
fn ascii_lower_contains(hay: &[u8], needle: &[u8]) -> bool {
    needle.is_empty()
        || hay
            .windows(needle.len())
            .any(|w| w.iter().zip(needle).all(|(a, b)| a.eq_ignore_ascii_case(b)))
}

/// Spells `v` as lowercase hex at the start of `buf`, the digits
/// `format!("{v:x}")` prints.
///
/// # Arguments
///
/// * `v` - The value to spell.
/// * `buf` - Receives the digits, 16 bytes for a `u64`'s worst case.
///
/// # Returns
/// How many bytes were written; one for zero itself.
fn hex_written(v: u64, buf: &mut [u8]) -> usize {
    let n = if v == 0 {
        1
    } else {
        usize::try_from(64 - v.leading_zeros())
            .unwrap_or(64)
            .div_ceil(4)
    };
    for (i, slot) in buf.iter_mut().enumerate().take(n) {
        let shift = (n - 1 - i) * 4;
        *slot = HEX_DIGITS[usize::from(lo8((v >> shift) & 0xf))];
    }
    n
}

/// Most blocks one page of a function's block table lists.
pub const FUNCTION_BLOCKS_MAX: usize = 300;

/// Renders one function's detail with one page of its basic-block table.
///
/// A block's end is the next row's start in all but the last row, so a row
/// carries the block's size instead, and the table pages at
/// [`FUNCTION_BLOCKS_MAX`] blocks: a 2,900-block dispatcher printed 76 KB
/// at once.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names for the function and its callers/callees.
/// * `entry` - The function's entry address.
/// * `offset` - Blocks to skip first (paging).
///
/// # Returns
///
/// Name, entry, range, counts, callees, callers, then a `# showing N of M
/// blocks` line, which says the offset of the next page when there is one,
/// and one `start size term successors` row per block of the page; `None`
/// when no function starts at `entry`.
pub fn function_detail(a: &Analysis, o: &Overlay, entry: u64, offset: usize) -> Option<String> {
    let f = a.function(entry)?;
    let names = |v: &[u64]| -> String {
        v.iter()
            .map(|&e| name_of(a, o, e))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let thunk = f.thunk.map_or(String::new(), |slot| {
        format!("thunk:   jmp [{slot:#x}], the import under an address of the program's own\n")
    });
    let funclet = f.funclet.map_or(String::new(), |fl| {
        format!(
            "funclet: {} of {}, run on that function's frame\n",
            fl.role.describe(),
            name_of(a, o, fl.parent)
        )
    });
    let mut out = format!(
        "name:    {}\n{thunk}{funclet}entry:   {:#x}\nrange:   {:#x}..{:#x} ({} bytes)\ninstrs:  {}  blocks: {}\ncallees: {}\ncallers: {}\n",
        name_of(a, o, f.entry),
        f.entry,
        f.start,
        f.end,
        f.size(),
        f.instr_count,
        f.blocks.len(),
        names(&f.callees),
        names(&f.callers)
    );
    let total = f.blocks.len();
    let page_end = offset.saturating_add(FUNCTION_BLOCKS_MAX).min(total);
    let shown = page_end.saturating_sub(offset.min(page_end));
    let _ = write!(out, "# showing {shown} of {total} blocks");
    if page_end < total {
        let _ = write!(out, "; offset={page_end} for the next page");
    }
    out.push_str("\n# start size term successors\n");
    for b in f.blocks.iter().skip(offset).take(FUNCTION_BLOCKS_MAX) {
        let _ = write!(
            out,
            "{:#x} {} {}",
            b.start,
            b.end.saturating_sub(b.start),
            b.term.name()
        );
        for s in &b.successors {
            let _ = write!(out, " {s:#x}");
        }
        out.push('\n');
    }
    Some(out)
}

/// Longest forwarding text a forwarded export's row reads.
const FORWARD_MAX: usize = 256;

/// Renders the paged symbol table.
///
/// A PE import is `module!name`, and a page of three hundred imports from
/// a dozen modules spelled the module on every row: a `# module: X` line
/// opens each run of imports from one module and the rows carry the bare
/// name; a `# module: -` line closes the run when rows without a module
/// follow, so an export is not read as one more import of the module above
/// it. The `kind` column is left out when one kind was asked for, since
/// every row would say it. An import nothing references is a redirected or
/// leftover slot, the shape a patched binary leaves behind, so its row says
/// so. A forwarded export's address holds the name of the export it
/// forwards to, not code, so its row ends with `-> MODULE.name`.
///
/// # Arguments
///
/// * `p` - The loaded image, for its symbol table.
/// * `a` - The analysis, for which import slots are referenced, directly
///   or through a thunk something calls.
/// * `kind` - One kind of symbol, or every kind.
/// * `filter` - Case-insensitive substring of the full name, module
///   included, or of the demangled name a row shows.
/// * `offset` - Matches to skip first (paging).
/// * `limit` - Maximum rows to render.
///
/// # Returns
///
/// `(shown, total, text)`: the text starts with `# showing N of M symbols`
/// (and the next page's offset when more follow) and a column header, then
/// one `kind addr name` row per symbol (`addr name` under one kind), each
/// run of one module's imports under its `# module:` line.
pub fn symbols_tsv(
    p: &Program,
    a: &Analysis,
    kind: Option<SymbolKind>,
    filter: Option<&str>,
    offset: usize,
    limit: usize,
) -> (usize, usize, String) {
    let q = filter.map(str::to_lowercase);
    let matched: Vec<&Symbol> = p
        .symbols
        .iter()
        .filter(|s| {
            kind.is_none_or(|k| s.kind == k)
                && q.as_ref().is_none_or(|q| {
                    s.name.to_lowercase().contains(q.as_str())
                        || demangled_or_raw(bare_name(&s.name))
                            .to_lowercase()
                            .contains(q.as_str())
                })
        })
        .collect();
    let total = matched.len();
    let shown = total.saturating_sub(offset).min(limit);
    let mut out = format!("# showing {shown} of {total} symbols");
    let next = offset.saturating_add(shown);
    if next < total {
        let _ = write!(out, "; offset={next} for the next page");
    }
    out.push('\n');
    out.push_str(if kind.is_some() {
        "# addr name\n"
    } else {
        "# kind addr name\n"
    });
    let called_slots: BTreeSet<u64> = a
        .functions
        .iter()
        .filter(|f| a.xrefs.get(&f.entry).is_some_and(|v| !v.is_empty()))
        .filter_map(|f| f.thunk)
        .collect();
    let mut module: Option<&str> = None;
    for s in matched.into_iter().skip(offset).take(limit) {
        let bare = bare_name(&s.name);
        let owner = s.name.strip_suffix(bare).and_then(|m| m.strip_suffix('!'));
        if owner != module {
            let _ = writeln!(out, "# module: {}", owner.unwrap_or("-"));
        }
        module = owner;
        let dead = s.kind == SymbolKind::Import
            && s.addr != 0
            && a.xrefs.get(&s.addr).is_none_or(Vec::is_empty)
            && !called_slots.contains(&s.addr);
        if kind.is_none() {
            let _ = write!(out, "{} ", s.kind.name());
        }
        let target = (s.kind == SymbolKind::Forwarder)
            .then(|| p.read_va_upto(s.addr, FORWARD_MAX))
            .flatten()
            .map(|b| b.split(|&c| c == 0).next().unwrap_or_default())
            .filter(|b| !b.is_empty())
            .map_or_else(String::new, |b| {
                format!(" -> {}", crate::text::one_line(&String::from_utf8_lossy(b)))
            });
        let _ = writeln!(
            out,
            "{:#x} {}{target}{}",
            s.addr,
            demangled_or_raw(bare),
            if dead { "  unreferenced" } else { "" }
        );
    }
    (shown, total, out)
}

/// Lists the classes `moc` described: signals, slots, methods and
/// properties, each method with the function it maps to when known.
///
/// # Arguments
///
/// * `a` - The analysis.
///
/// # Returns
///
/// A header counting classes and methods, then one block per class.
pub fn qt_tsv(a: &Analysis) -> String {
    let methods: usize = a.qt.iter().map(|c| c.methods.len()).sum();
    let mapped: usize =
        a.qt.iter()
            .flat_map(|c| c.methods.iter())
            .filter(|m| m.entry.is_some())
            .count();
    let mut out = format!(
        "# {} Qt classes from moc metadata: {methods} signals/slots/methods, {mapped} mapped to functions\n",
        a.qt.len()
    );
    for c in &a.qt {
        let parent = c
            .parent
            .as_deref()
            .map_or(String::new(), |p| format!(" : {p}"));
        let dispatcher = c
            .metacall
            .map_or(String::new(), |m| format!(", qt_static_metacall {m:#x}"));
        let _ = writeln!(
            out,
            "class {}{parent}  (staticMetaObject {:#x}{dispatcher})",
            c.name, c.meta_object
        );
        for kind in QtMethodKind::ALL {
            let rows: Vec<String> = c
                .methods
                .iter()
                .filter(|m| m.kind == kind)
                .map(|m| match m.entry {
                    Some(e) => format!("{}@{e:#x}", m.name),
                    None => m.name.clone(),
                })
                .collect();
            if !rows.is_empty() {
                let _ = writeln!(out, "  {}s: {}", kind.word(), rows.join(", "));
            }
        }
        if !c.properties.is_empty() {
            let _ = writeln!(out, "  properties: {}", c.properties.join(", "));
        }
    }
    out
}

/// Reference groups listed per page unless a limit says otherwise.
pub const XREF_ROWS_DEFAULT: usize = 60;
/// Most reference groups one page lists.
pub const XREF_ROWS_MAX: usize = 500;

/// Ranks functions by what every binary can answer: the distinct string
/// literals and imports each one references.
///
/// The evidence ranking looks for what a protected program does, packing,
/// hidden strings, keystreams, and an ordinary program has none of it; the
/// function that references a hundred strings and a dozen imports is still
/// the one to read first, and that count is free. A call through an import
/// thunk counts as the import.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `skip` - Functions already listed.
/// * `take` - Most functions to return.
///
/// # Returns
///
/// `(entry, reasons)` pairs, the widest function first; a function with
/// fewer than [`EVERYDAY_MIN`] references combined is not listed.
pub(super) fn everyday_reading_list(
    p: &Program,
    a: &Analysis,
    skip: &BTreeSet<u64>,
    take: usize,
) -> Vec<(u64, Vec<String>)> {
    let slots: BTreeSet<u64> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| s.addr)
        .collect();
    let mut scored: Vec<(usize, usize, u64)> = Vec::new();
    for f in &a.functions {
        if skip.contains(&f.entry) || f.thunk.is_some() || f.funclet.is_some() {
            continue;
        }
        let mut strings: BTreeSet<u64> = BTreeSet::new();
        let mut imports: BTreeSet<u64> = BTreeSet::new();
        for (target, _) in a.refs_from(f.entry) {
            if slots.contains(&target) {
                imports.insert(target);
            } else if let Some((start, _)) = string_literal(p, target, 8) {
                strings.insert(start);
            }
        }
        for c in &f.callees {
            if let Some(slot) = a.function(*c).and_then(|g| g.thunk) {
                imports.insert(slot);
            }
        }
        if strings.len() + imports.len() >= EVERYDAY_MIN {
            scored.push((strings.len(), imports.len(), f.entry));
        }
    }
    scored.sort_by(|l, r| (r.0 + r.1).cmp(&(l.0 + l.1)).then(l.2.cmp(&r.2)));
    scored
        .into_iter()
        .take(take)
        .map(|(strings, imports, entry)| {
            (
                entry,
                vec![format!(
                    "references {strings} strings and {imports} imports"
                )],
            )
        })
        .collect()
}

/// Fewest strings and imports combined that make a function worth listing.
pub(super) const EVERYDAY_MIN: usize = 3;

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
    xrefs(a, o, target, view)
}

/// Renders the cross-references to one address, one row per function
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
/// and the header says how many there are in all, so a target with more
/// callers than one page holds is read in pages rather than cut off. The
/// group covering the most sites comes first.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names for the containing functions.
/// * `target` - The referenced address.
/// * `view` - The header alone, or which page of groups.
///
/// # Returns
///
/// A `# N xrefs to <target> in G groups, showing S of G from O` header, a column
/// header, then one `function: site kind, site kind` row per group of the
/// page, ending with how many more functions run the same code when the
/// group folds several; a pointer stored in data is in function `-`. The
/// count-only view is the first line alone.
pub fn xrefs(a: &Analysis, o: &Overlay, target: u64, view: XrefView) -> String {
    let sites = a.xrefs_to(target);
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
    let groups_word = if ordered.len() == 1 {
        "group"
    } else {
        "groups"
    };
    let count = if sites.len() >= crate::analysis::functions::XREF_SITES_PER_TARGET {
        format!(
            "{}+ (capped: more sites exist than are kept per target)",
            sites.len()
        )
    } else {
        sites.len().to_string()
    };
    let callers = sites.iter().filter(|s| s.is_branch()).count();
    let short = callers < unseen::SHORT_CALLERS && (callers > 0 || a.function_at(target).is_some());
    let unseen = short
        .then(|| unseen_line(a, Reach::Program, "#"))
        .flatten()
        .unwrap_or_default();
    let incomplete = if a.incomplete {
        format!("{INCOMPLETE_NOTE}\n{unseen}")
    } else {
        unseen
    };
    let XrefView::Page { offset, limit } = view else {
        return format!(
            "# {count} xrefs to {target:#x} in {} {groups_word}\n{incomplete}",
            ordered.len()
        );
    };
    let limit = limit.clamp(1, XREF_ROWS_MAX);
    let page_end = offset.saturating_add(limit).min(ordered.len());
    let shown = page_end.saturating_sub(offset.min(page_end));
    let mut out = format!(
        "# {count} xrefs to {target:#x} in {} {groups_word}, showing {shown} of {} from {offset}\n{incomplete}# function: site kind, ...\n",
        ordered.len(),
        ordered.len()
    );
    for g in ordered.iter().skip(offset).take(limit) {
        let name = g.entry.map_or_else(|| "-".to_owned(), |e| name_of(a, o, e));
        let sites: Vec<String> = g
            .sites
            .iter()
            .map(|s| format!("{:#x} {}", s.va, s.kind.word()))
            .collect();
        let _ = write!(out, "{name}: {}", sites.join(", "));
        out.push_str(&same_code(a, o, &g.others));
        out.push('\n');
    }
    if page_end < ordered.len() {
        let _ = writeln!(
            out,
            "# {} more groups; offset={page_end} for the next page",
            ordered.len() - page_end
        );
    }
    out
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
/// ` (+N functions running the same code): name, name` with at most
/// [`SAME_CODE_NAMES_MAX`] names and `...` past them; empty when nothing
/// was folded.
pub(super) fn same_code(a: &Analysis, o: &Overlay, others: &[u64]) -> String {
    if others.is_empty() {
        return String::new();
    }
    let names: Vec<String> = others
        .iter()
        .take(SAME_CODE_NAMES_MAX)
        .map(|&e| name_of(a, o, e))
        .collect();
    let more = if others.len() > SAME_CODE_NAMES_MAX {
        ", ..."
    } else {
        ""
    };
    format!(
        " (+{} function{} running the same code): {}{more}",
        others.len(),
        plural(others.len()),
        names.join(", ")
    )
}

/// Most folded functions a listing row names; the count covers the rest.
const SAME_CODE_NAMES_MAX: usize = 8;

/// One row of a cross-reference listing: a function's sites, standing for
/// every function that runs the same code.
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

/// Makes a name safe inside a quoted mermaid node label.
///
/// The characters mermaid reads inside a quoted label, the angle brackets
/// of a template and the quote itself, become the entity codes it defines
/// for them, so `Core::Ptr<UI::Canvas>::operator ->` stays legible; the
/// rest of a C++ name passes through, and anything else becomes `_`.
///
/// # Arguments
///
/// * `s` - Any name.
pub(super) fn sanitize_label(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '<' => out.push_str("#lt;"),
            '>' => out.push_str("#gt;"),
            '"' => out.push_str("#quot;"),
            '&' => out.push_str("#amp;"),
            c if c.is_ascii_alphanumeric()
                || matches!(
                    c,
                    ' ' | '_'
                        | '.'
                        | '?'
                        | ':'
                        | '@'
                        | '$'
                        | '-'
                        | '+'
                        | '('
                        | ')'
                        | ','
                        | '*'
                        | '~'
                        | '!'
                        | '='
                        | '/'
                        | '\''
                ) =>
            {
                out.push(c);
            }
            _ => out.push('_'),
        }
    }
    out
}

/// Whether a listing shows the encoded bytes beside each instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bytes {
    /// Address and text only.
    Hidden,
    /// A hex column between the address and the text.
    Shown,
}

/// Renders a whole function's disassembly block by block.
///
/// [`disasm_function_with`] with the bytes column as a flag.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the code bytes.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
/// * `max_instrs` - Hard cap on instructions; a `# instruction cap` line marks a cut.
/// * `with_bytes` - Adds the raw-bytes column.
///
/// # Returns
///
/// As [`disasm_function_with`].
pub fn disasm_function(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    max_instrs: usize,
    with_bytes: bool,
) -> Option<String> {
    let bytes = if with_bytes {
        Bytes::Shown
    } else {
        Bytes::Hidden
    };
    disasm_function_with(p, a, o, entry, max_instrs, bytes)
}

/// Renders a whole function's disassembly block by block.
///
/// Block starts get `L_<addr>:` labels, overlay names and comments appear
/// inline, and branch targets that are functions or named addresses get a
/// `; name` suffix: an x86 near call or jmp, whose target is read from its
/// text, and any direct arm64 branch, whose decoder states it. A Linux
/// syscall site is tagged with its call the same way, `; syscall socket`
/// ([`crate::analysis::syscalls`]), and a call that sends an Objective-C
/// message gets the message, `; [recv sel]`, instead of its target.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the code bytes.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
/// * `max_instrs` - Hard cap on instructions; a `# instruction cap` line marks a cut.
/// * `bytes` - Whether the raw-bytes column is shown.
///
/// # Returns
///
/// The header comment and the rows, or `None` when no function starts at
/// `entry` or the architecture has no disassembler.
pub fn disasm_function_with(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    max_instrs: usize,
    bytes: Bytes,
) -> Option<String> {
    let f = a.function(entry)?;
    let isa = p.isa_for(Feature::Disasm).ok()?;
    let mut out = format!(
        "// {} @ {:#x}: {} instructions, {} blocks\n",
        name_of(a, o, f.entry),
        f.entry,
        f.instr_count,
        f.blocks.len()
    );
    let mut budget = max_instrs;
    let sites = crate::analysis::syscalls::syscall_sites(p, a);
    for b in &f.blocks {
        let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(0);
        let Some(code) = p.read_va_upto(b.start, len.max(1)) else {
            continue;
        };
        if b.start != f.entry {
            let _ = writeln!(out, "L_{:x}:", b.start);
        }
        let lines = disasm::disassemble_program(p, code, b.start, isa, budget);
        for l in &lines {
            if let Some(n) = o.names.get(&l.va) {
                let _ = writeln!(out, "            ; = {n} =");
            }
            let mut text = l.text.clone();
            let target = l.target.or_else(|| {
                if text.starts_with("call ") || text.starts_with("jmp ") {
                    text.split_whitespace()
                        .nth(1)
                        .and_then(|t| u64::from_str_radix(t.trim_end_matches('h'), 16).ok())
                } else {
                    None
                }
            });
            if let Some(message) = a.objc.messages.get(&l.va) {
                let _ = write!(text, "  ; {}", message.text());
            } else if let Some(target) = target
                && (a.function(target).is_some() || o.names.contains_key(&target))
            {
                let _ = write!(text, "  ; {}", short_name(a, o, target));
            } else if let Some(name) = memory_import(p, &text) {
                let _ = write!(text, "  ; {name}");
            } else if let Ok(k) = sites.binary_search_by_key(&l.va, |s| s.at) {
                let _ = write!(text, "  ; {}", sites[k].label());
            }
            if let Some(c) = o.comments.get(&l.va) {
                let _ = write!(text, "  // {c}");
            }
            match bytes {
                Bytes::Shown => {
                    let hexb: Vec<String> = l.bytes.iter().map(|b| format!("{b:02x}")).collect();
                    let _ = writeln!(out, "{:#x}  {:<24} {text}", l.va, hexb.join(" "));
                }
                Bytes::Hidden => {
                    let _ = writeln!(out, "{:#x}  {text}", l.va);
                }
            }
        }
        budget = budget.saturating_sub(lines.len());
        if budget == 0 {
            let _ = writeln!(out, "# instruction cap ({max_instrs}) reached");
            break;
        }
    }
    Some(out)
}

/// Bytes around an address whose entropy decides the packed caveat: enough
/// for a byte histogram to tell code (about 6) from ciphertext (about 8).
const PACKED_WINDOW: u64 = 4096;

/// Says when a listing starts where no code runs.
///
/// A byte sequence in `.rdata` decodes as x86 like any other, and a
/// `cpuid` read out of a lookup table looks like an anti-VM check to a
/// reader who was not told the section never executes. Executable bytes a
/// packer has not decrypted yet do not disassemble to anything real either,
/// so the caveat says so rather than let confident garbage stand as if it
/// were the program's code. The packed test reads the [`PACKED_WINDOW`]
/// bytes around the address, not the whole section: one section can hold
/// ordinary code and an encrypted blob side by side, and the blob's
/// megabytes would outvote the code and call plain code "packed". The section is looked up in the full table, not
/// through [`Program::section_at`], so a protector's virtual-only section
/// that the file backs with no bytes (`.themida`) is found.
///
/// # Arguments
///
/// * `p` - The loaded image, for the section's permissions.
/// * `a` - The analysis, for the discovered functions.
/// * `va` - Where the listing starts.
///
/// # Returns
///
/// A sentence for a non-executable section (`0x42c0ba is in .rdata (r--),
/// which never executes: the bytes decode, nothing runs them`) or for an
/// executable address no discovered function covers (`0x401800 is outside
/// every discovered function`, said only where functions are discovered),
/// and an empty string for code inside one.
pub fn listing_caveat(p: &Program, a: &Analysis, va: u64) -> String {
    let covering = p
        .sections
        .iter()
        .find(|s| va >= s.va.0 && va < s.va.0.saturating_add(s.vsize.max(s.file_size)));
    if let Some(s) = covering {
        if !s.executable {
            return format!(
                "{va:#x} is in {} ({}), which never executes: the bytes decode, nothing runs them",
                s.name,
                s.perms()
            );
        }
        if s.file_size == 0 {
            return format!(
                "{va:#x} is in {} ({}), which the file backs with no bytes: packed, nothing is here \
                 until the program unpacks itself at run time. Try unpack.",
                s.name,
                s.perms()
            );
        }
        let backed_end = s.va.0.saturating_add(s.file_size);
        let to = va
            .saturating_sub(PACKED_WINDOW / 2)
            .max(s.va.0)
            .saturating_add(PACKED_WINDOW)
            .min(backed_end);
        let from = to.saturating_sub(PACKED_WINDOW).max(s.va.0);
        let e = p
            .read_va(from, usize::try_from(to.saturating_sub(from)).unwrap_or(0))
            .map_or(0.0, crate::entropy::shannon);
        if e >= PACKED_ENTROPY {
            return format!(
                "{va:#x} is in {} ({}), whose bytes around it are packed (entropy {e:.2}): they \
                 decode, but this is not the original code until it is unpacked. Try unpack, or \
                 the live debugger.",
                s.name,
                s.perms()
            );
        }
    }
    if p.arch.supports(Feature::Discover) && a.function_at(va).is_none() {
        return format!("{va:#x} is outside every discovered function");
    }
    String::new()
}

/// Finds the instruction boundary at or before `va` inside its function.
///
/// A byte search lands on an operand, not on an instruction, and decoding
/// from the operand yields confident garbage; the function's block already
/// says where the instructions start, so the last one starting at or before
/// `va` is where a listing should begin. Every arm64 instruction is an
/// aligned word, so there the boundary is `va` aligned down, with no block
/// to ask.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the block holding `va`.
/// * `va` - Any address.
///
/// # Returns
///
/// The boundary; `None` for x86 when no discovered block covers `va`, and
/// for an architecture borer does not disassemble.
pub fn instruction_at_or_before(p: &Program, a: &Analysis, va: u64) -> Option<u64> {
    let bitness = match p.isa_for(Feature::Disasm).ok()? {
        Isa::X86 { bits } => bits,
        Isa::A64 => return Some(va - va % from_usize(a64::INSN_LEN)),
        Isa::A32 => {
            let Some(b) = a
                .function_at(va)
                .and_then(|f| f.blocks.iter().find(|b| b.start <= va && va < b.end))
            else {
                return Some(va & !1);
            };
            let len = usize::try_from(b.end - b.start).ok()?;
            let code = p.read_va(b.start, len)?;
            return disasm::disassemble_program(p, code, b.start, Isa::A32, len)
                .iter()
                .map(|l| l.va)
                .take_while(|&at| at <= va)
                .last();
        }
    };
    let f = a.function_at(va)?;
    let b = f.blocks.iter().find(|b| b.start <= va && va < b.end)?;
    let len = usize::try_from(b.end - b.start).ok()?;
    let code = p.read_va(b.start, len)?;
    let mut decoder = Decoder::with_ip(bitness, code, b.start, DecoderOptions::NONE);
    let mut at = b.start;
    while decoder.can_decode() {
        let i = decoder.decode();
        if i.ip() > va {
            break;
        }
        at = i.ip();
    }
    Some(at)
}

/// Returns where a linear sweep starting at `va` runs out of code.
///
/// Bytes that no block of the containing function covers are not code. A
/// compiler embeds a string by pointing a `lea` just past an unconditional
/// jump, and sweeping into it prints instructions that were never there:
/// `"127.0.0.1"` decodes as `xor [rdx],esi`, `(bad)`, `xor [rsi],ch`. The
/// function walker already stops at the jump, so its blocks say where the
/// code ends.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `va` - Where the sweep starts.
///
/// # Returns
///
/// The end of the run of blocks covering `va`, or `None` when `va` is not
/// inside a discovered function, where a sweep has nothing better to go on.
///
/// Alignment padding between two blocks of the function (`nop` forms and
/// `int3`, at most 15 bytes) does not end the run: a compiler
/// aligns a loop head that way, and the sweep stopped there and called the
/// rest of the function data.
///
/// # Arguments
///
/// * `p` - The loaded image, whose bytes say what a gap holds.
/// * `a` - The analysis.
/// * `va` - Where the sweep starts.
pub fn sweep_limit(p: &Program, a: &Analysis, va: u64) -> Option<u64> {
    /// Most bytes of padding a sweep crosses between two blocks.
    const PAD_MAX: u64 = 15;
    let f = a.function(va)?;
    let padding = |from: u64, to: u64| {
        let (Some(bits), Some(code)) = (
            p.arch.bitness(),
            usize::try_from(to - from)
                .ok()
                .and_then(|n| p.read_va(from, n)),
        ) else {
            return false;
        };
        let mut d = Decoder::with_ip(bits, code, from, DecoderOptions::NONE);
        d.iter()
            .all(|i| matches!(i.mnemonic(), Mnemonic::Nop | Mnemonic::Int3))
    };
    let mut limit = va;
    loop {
        if let Some(b) = f.blocks.iter().find(|b| b.start <= limit && limit < b.end) {
            limit = b.end;
            continue;
        }
        let next = f
            .blocks
            .iter()
            .map(|b| b.start)
            .filter(|&s| s > limit && s - limit <= PAD_MAX)
            .min();
        match next {
            Some(s) if limit > va && padding(limit, s) => limit = s,
            Some(_) | None => break,
        }
    }
    (limit > va).then_some(limit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::NameSource;

    /// A target whose sites filled the per-target cap says its count is a
    /// floor, and an analysis whose walk ran out says so under the xrefs
    /// header; a short list and a finished walk say neither.
    ///
    /// # Panics
    ///
    /// When a cap or a cut walk goes unsaid, or one is said of neither.
    #[test]
    fn a_capped_xref_list_and_a_cut_walk_say_so() {
        let cap = crate::analysis::functions::XREF_SITES_PER_TARGET;
        let site = |va| RefSite {
            va,
            kind: RefKind::Call,
            from_entry: None,
        };
        let mut a = Analysis::default();
        a.xrefs.insert(
            0x1000,
            (0..cap).map(|i| site(0x2000 + from_usize(i))).collect(),
        );
        a.xrefs.insert(0x3000, vec![site(0x4000)]);
        let o = Overlay::default();
        let page = XrefView::Page {
            offset: 0,
            limit: 1,
        };
        let capped = xrefs(&a, &o, 0x1000, page);
        assert!(
            capped.starts_with(&format!("# {cap}+ (capped: ")),
            "{capped}"
        );
        let short = xrefs(&a, &o, 0x3000, page);
        assert!(short.starts_with("# 1 xrefs to 0x3000"), "{short}");
        assert!(!short.contains(INCOMPLETE_NOTE), "{short}");
        a.incomplete = true;
        let cut = xrefs(&a, &o, 0x3000, XrefView::Count);
        assert!(
            cut.ends_with(&format!(
                "{INCOMPLETE_NOTE}
"
            )),
            "{cut}"
        );
    }

    /// Builds the bare function a filter test needs: an entry, a name when
    /// one was given, and nothing else discovered.
    fn bare(entry: u64, name: Option<&str>) -> Function {
        Function {
            entry,
            start: entry,
            end: entry,
            instr_count: 0,
            blocks: Vec::new(),
            callees: Vec::new(),
            callers: Vec::new(),
            name: name.map(str::to_owned),
            name_inferred: false,
            name_source: NameSource::None,
            thunk: None,
            bound: None,
            funclet: None,
            signature: None,
            body_hash: 0,
            shape_hash: 0,
            returns_value: None,
            ret_width: None,
            ret_partial: None,
            ret_float: None,
            preserves_rax: false,
            hands_back_rdx: false,
            param_hints: BTreeMap::new(),
            ret_hint: None,
            stack_args: 0,
            stack_pop: 0,
        }
    }

    /// The filter test answers what the lowered spellings it replaced
    /// answered, for the overlay name, the symbol name, the `sub_`
    /// fallback and the `0x`-stripped entry hex.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn filter_matches_the_spelled_names() {
        let mut overlay = Overlay::default();
        overlay.names.insert(0x402000, "Overlaid".to_owned());
        for (entry, name, filter) in [
            (0x401000u64, None, ""),
            (0x401000, None, "sub_401"),
            (0x401000, None, "SUB_401"),
            (0x401000, None, "0x401"),
            (0x401000, None, "0X401"),
            (0x401000, None, "401"),
            (0x401000, None, "402"),
            (0x401000, Some("Borer_Tool"), "borer_"),
            (0x401000, Some("Borer_Tool"), "tool"),
            (0x401000, Some("Borer_Tool"), "401"),
            (0x401000, Some("Borer_Tool"), "sub_401"),
            (0x140001000, Some("Named"), "sub_1"),
            (0x140001000, None, "sub_1"),
            (0x402000, None, "overlaid"),
            (0x402000, None, "borer"),
            (0xabcdef, None, "0xab"),
            (0xabcdef, None, "0xAB"),
        ] {
            let f = bare(entry, name);
            let q = filter.to_lowercase();
            let spelled = overlay
                .names
                .get(&entry)
                .cloned()
                .or_else(|| f.name.clone())
                .unwrap_or_else(|| format!("sub_{entry:x}"));
            let spelled_test = spelled.to_lowercase().contains(&q)
                || format!("{entry:x}").contains(q.strip_prefix("0x").unwrap_or(&q));
            let hex_q = q.strip_prefix("0x").unwrap_or(&q);
            assert_eq!(
                function_matches(&f, &overlay, &q, hex_q),
                spelled_test,
                "entry {entry:x}, filter {filter:?}"
            );
        }
    }

    /// The case-folded contains answers what the lowered copy answered,
    /// ASCII and not.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn lower_contains_matches_to_lowercase() {
        for (hay, needle) in [
            ("Borer_Tool", "bor"),
            ("borer_tool", "tool"),
            ("ÜBER-flow", "über"),
            ("ÜBER-flow", "flow"),
            ("abc", "d"),
            ("", ""),
            ("abc", ""),
        ] {
            assert_eq!(
                lower_contains(hay, needle),
                hay.to_lowercase().contains(needle),
                "hay {hay:?}, needle {needle:?}"
            );
        }
    }

    /// An arm64 function lists word by word, its call named.
    ///
    /// The call reads the name of the function it reaches, as an x86
    /// listing's does, and an address no discovered function covers draws
    /// the caveat that says so, as on x86.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn an_arm64_listing_names_its_call() {
        let bytes: Vec<u8> = [
            // ASM: bl 0x1010
            0x9400_0004u32,
            // ASM: ret
            0xd65f_03c0,
            // ASM: nop
            0xd503_201f,
            // ASM: nop
            0xd503_201f,
            // ASM: ret
            0xd65f_03c0,
        ]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
        let text = Section::mapped(".text", 0x1000, 0, 0x14, false, true);
        let p = Program::raw(
            bytes,
            crate::program::Arch::Arm64,
            0,
            Some(0x1000),
            vec![text],
        );
        let block = |start: u64, end: u64| BasicBlock {
            start,
            end,
            term: BlockTerm::Ret,
            successors: smallvec::SmallVec::new(),
        };
        let mut main = bare(0x1000, None);
        main.blocks = vec![block(0x1000, 0x1008)];
        let mut helper = bare(0x1010, Some("helper"));
        helper.blocks = vec![block(0x1010, 0x1014)];
        let mut a = Analysis {
            functions: vec![main, helper],
            ..Analysis::default()
        };
        a.finish_index(&p);
        let out = disasm_function_with(&p, &a, &Overlay::default(), 0x1000, 10, Bytes::Hidden)
            .expect("a function starts there");
        assert!(
            out.ends_with("\n0x1000  bl 0x1010  ; helper\n0x1004  ret\n"),
            "{out}"
        );
        assert_eq!(
            listing_caveat(&p, &a, 0x1008),
            "0x1008 is outside every discovered function"
        );
    }

    /// The stack-buffer hex spells what `format!("{:x}")` prints.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn hex_written_spells_what_format_does() {
        for v in [
            0u64,
            1,
            9,
            10,
            0x10,
            0xdead_beef,
            u64::from(u32::MAX),
            u64::MAX,
        ] {
            let mut buf = [0u8; 16];
            let n = hex_written(v, &mut buf);
            assert_eq!(&buf[..n], format!("{v:x}").as_bytes(), "value {v}");
        }
    }

    /// The symbol table closes a module's run of imports before the rows that
    /// have no module.
    ///
    /// It also names what a forwarded export forwards to, and filters on the demangled
    /// name a row shows as well as the raw one.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn symbols_close_modules_name_forwards_and_filter_demangled() {
        use crate::program::{Arch, Section, Symbol};
        let mut bytes = vec![0u8; 0x100];
        bytes[0x40..0x4d].copy_from_slice(b"NTDLL.RtlFoo\0");
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0x1000,
            None,
            vec![Section::mapped(".rdata", 0x1000, 0, 0x100, false, false)],
        );
        let symbol = |name: &str, addr: u64, kind: SymbolKind| Symbol {
            name: name.to_owned(),
            addr,
            kind,
        };
        p.symbols = vec![
            symbol("KERNEL32.dll!GetTickCount", 0, SymbolKind::Import),
            symbol("AcquireLock", 0x1040, SymbolKind::Forwarder),
            symbol("_ZN3foo3barEv", 0x1080, SymbolKind::Export),
        ];
        let a = Analysis::default();
        let (_, _, all) = symbols_tsv(&p, &a, None, None, 0, 50);
        assert!(
            all.contains(
                "# module: KERNEL32.dll\nimport 0x0 GetTickCount\n# module: -\nforward 0x1040 AcquireLock -> NTDLL.RtlFoo\n"
            ),
            "{all}"
        );
        let (shown, total, found) = symbols_tsv(&p, &a, None, Some("foo::bar"), 0, 50);
        assert_eq!((shown, total), (1, 1), "{found}");
        assert!(found.contains("export 0x1080 foo::bar()"), "{found}");
        let (_, forwards, _) = symbols_tsv(&p, &a, Some(SymbolKind::Forwarder), None, 0, 50);
        assert_eq!(forwards, 1);
        let summary = p.summary();
        assert!(summary.contains("exports: 2 (1 forwarded)"), "{summary}");
    }
}
