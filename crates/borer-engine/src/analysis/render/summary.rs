//! One-call function triage, the strings a function references, and the
//! functions sharing its shape.

use super::*;

/// Reads the quoted string literal at `va`, if a readable non-code string lives there.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `va` - Address of the candidate string.
/// * `cap` - Longest text returned in full.
///
/// # Returns
///
/// `(start of the string, `"text"` or `L"text"`)`, or `None` when `va` is
/// unmapped, inside code, or holds no string of at least four characters.
///
/// A reference into the middle of a literal resolves to the literal, not to
/// the tail it points at: code comparing a long string in 16-byte chunks
/// references it at `+0x10` and `+0x20`, and reading forward from there
/// reports each tail as a string of its own, every one cut mid-word.
pub(super) fn string_literal(p: &Program, va: u64, cap: usize) -> Option<(u64, String)> {
    string_literal_in(p, va, cap, false)
}

/// Reads the string literal a reference points at, in a data section or,
/// for a reference the code makes, in a code section too.
///
/// A linker can merge the read-only data into the code section, and a
/// string there is as much a string as one in `.rdata`: what makes the
/// bytes of a code section suspect is that instructions can spell
/// printable text, so a code-section literal counts only where no
/// discovered function's code lies, and only for an address something
/// references.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Discovery results, for where the code is.
/// * `va` - The referenced address.
/// * `cap` - Longest text returned in full.
///
/// # Returns
///
/// As [`string_literal`].
pub(super) fn referenced_literal(
    p: &Program,
    a: &Analysis,
    va: u64,
    cap: usize,
) -> Option<(u64, String)> {
    string_literal_in(p, va, cap, a.function_at(va).is_none())
}

/// [`string_literal`], with code sections allowed when `in_code` is set.
///
/// Walking back only relocates a reference that already resolves to a
/// string; starting the walk from bytes that are not one would invent
/// literals out of binary data that happens to end in printable bytes. A
/// wide string walks back a code unit at a time, as an ASCII one walks
/// back a byte: a reference into the middle of `L"..."` reported its tail.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `va` - Address of the candidate string.
/// * `cap` - Longest text returned in full.
/// * `in_code` - Whether a literal inside an executable section counts.
fn string_literal_in(p: &Program, va: u64, cap: usize, in_code: bool) -> Option<(u64, String)> {
    /// Longest walk back to a literal's first byte.
    const WINDOW: u64 = 256;
    let sec = p.section_at(va).filter(|s| in_code || !s.executable)?;
    if cstr_at(p, va, 4, cap).is_some() {
        let floor = va.saturating_sub(WINDOW).max(sec.va);
        let mut start = va;
        while start > floor
            && p.read_va_upto(start - 1, 1)
                .and_then(|b| b.first().copied())
                .is_some_and(literal_byte)
        {
            start -= 1;
        }
        if let Some((_, t)) = cstr_at(p, start, 4, cap) {
            return Some((start, format!("\"{t}\"")));
        }
    }
    wstr_at(p, va, 4, cap)?;
    let floor = va.saturating_sub(WINDOW).max(sec.va);
    let mut start = va;
    while start >= floor.saturating_add(2)
        && p.read_va_upto(start - 2, 2)
            .is_some_and(|u| matches!(u, [lo, 0] if crate::strings::printable(*lo)))
    {
        start -= 2;
    }
    if start < va && !crate::strings::wide_run_start(p, start) {
        start += 2;
    }
    wstr_at(p, start, 4, cap).map(|(_, t)| (start, format!("L\"{t}\"")))
}

/// Whether a function's code is scattered far across its address span.
///
/// The technique-agnostic mark of control-flow obfuscation: a virtual machine,
/// a flattened dispatcher or a junk-jump chain leaves the bytes that actually
/// decode a small fraction of the range they sit in, where ordinary code is
/// contiguous. Catches what [`flattening_tsv`] misses, whose signal is a switch
/// dispatcher specifically.
///
/// # Arguments
///
/// * `code_bytes` - Bytes the function's blocks actually cover.
/// * `span` - Distance from its lowest to its highest address.
/// * `blocks` - How many basic blocks it has.
///
/// # Returns
///
/// `true` when the span dwarfs the code over enough blocks to mean it.
pub(super) fn control_flow_dispersed(code_bytes: u64, span: u64, blocks: usize) -> bool {
    blocks >= 4 && span >= 0x1000 && span >= code_bytes.saturating_mul(8)
}

/// Most names or items a summary lists per line before `(+N more)`.
pub(super) const SUMMARY_LIST_MAX: usize = 12;

/// Joins at most [`SUMMARY_LIST_MAX`] items with `sep`, counting the rest.
///
/// # Arguments
///
/// * `items` - The items.
/// * `sep` - What goes between them.
fn capped(items: &[String], sep: &str) -> String {
    let shown: Vec<&str> = items
        .iter()
        .take(SUMMARY_LIST_MAX)
        .map(String::as_str)
        .collect();
    format!(
        "{}{}",
        shown.join(sep),
        plus_more(items.len(), SUMMARY_LIST_MAX)
    )
}

/// Renders the one-call triage of a function.
///
/// Built once per function and overlay through [`Analysis::derived`], and
/// the decompilation it reads is the memoized one, so a `decompile` of the
/// same function right after pays only for the naming and the polish.
///
/// Cheaper than a decompile and usually enough to decide whether to read one:
/// identity, the comment the overlay holds at the entry (what an agent
/// concluded about the function last time), size and shape (loops, jump
/// tables), what it writes, what it
/// asserts about its inputs, the source file it came from, the constants
/// its callers pass it, the wire format when it serializes, callers and
/// callees by name, and the strings and data the function touches. A
/// function with Itanium throw sites says what their landing pads catch. A
/// function whose code is scattered across a span far larger than the code
/// itself is reported as control-flow obfuscated (a VM, a flattened
/// dispatcher or a junk-jump chain), since ordinary code is contiguous.
///
/// # Arguments
///
/// * `p` - The loaded image, read for string literals and section names.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The `name/entry/range/shape/callers/callees/strings/data` block, with a
/// `comment:` line after the range when the overlay comments the entry, or
/// `None` when no function starts at `entry`.
pub fn function_summary(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> Option<String> {
    a.derived
        .get_or_build_item(
            "summary",
            o.fingerprint(),
            entry,
            || summary_of(p, a, o, entry),
            |s| s.as_ref().map_or(0, String::capacity),
        )
        .as_ref()
        .clone()
}

/// Builds the triage block [`function_summary`] memoizes.
///
/// # Arguments
///
/// * `p` - The loaded image, read for string literals and section names.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// As [`function_summary`].
fn summary_of(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> Option<String> {
    let f = a.function(entry)?;
    let names = |v: &[u64]| -> String {
        capped(
            &v.iter().map(|&e| name_of(a, o, e)).collect::<Vec<_>>(),
            ", ",
        )
    };
    let loops = f
        .blocks
        .iter()
        .any(|b| b.successors.iter().any(|s| *s <= b.start && *s >= f.start));
    let refs = a.refs_from(entry);
    let mut callees: Vec<String> = f.callees.iter().map(|&c| name_of(a, o, c)).collect();
    let called: BTreeSet<u64> = refs
        .iter()
        .filter(|(_, s)| s.kind == RefKind::Call)
        .map(|(t, _)| *t)
        .collect();
    let mut imported: BTreeMap<u64, &str> = BTreeMap::new();
    for s in &p.symbols {
        if matches!(s.kind, SymbolKind::Import) && called.contains(&s.addr) {
            imported.entry(s.addr).or_insert(&s.name);
        }
    }
    callees.extend(imported.into_values().map(str::to_owned));
    callees.sort_unstable();
    callees.dedup();
    let mut strings: Vec<String> = Vec::new();
    let mut data: Vec<String> = Vec::new();
    let mut seen = BTreeSet::new();
    for (target, site) in &refs {
        if site.kind != RefKind::Data || !seen.insert(*target) {
            continue;
        }
        if let Some((start, lit)) = string_literal(p, *target, 60) {
            let at = if start == *target {
                String::new()
            } else {
                format!(" +{:#x}", target - start)
            };
            strings.push(format!("{start:#x} {lit}{at}"));
        } else if a.function(*target).is_none() {
            let sec = p.section_at(*target).map_or("?", |s| s.name.as_str());
            let named = o
                .names
                .get(target)
                .cloned()
                .or_else(|| {
                    a.classes
                        .vtables
                        .get(target)
                        .map(|c| format!("{c}::vftable"))
                })
                .map_or(String::new(), |n| format!(" {n}"));
            data.push(format!("{target:#x} ({sec}){named}"));
        }
    }
    let list = |v: &[String]| -> String {
        if v.is_empty() {
            "-".to_owned()
        } else {
            capped(v, "; ")
        }
    };
    let tables: usize = f
        .blocks
        .iter()
        .map(|b| a.jump_tables.range(b.start..b.end).count())
        .sum();
    let virtuals = crate::analysis::decompile::virtual_callees(p, a, o, entry);
    let virt = if virtuals.is_empty() {
        String::new()
    } else {
        format!("virtual:  {} [{}]\n", virtuals.len(), names(&virtuals))
    };
    let declared = f.signature.as_ref().map_or(String::new(), |s| {
        format!(
            "declared: {} {}({}){}\n",
            s.ret,
            s.name,
            s.params.join(", "),
            if s.is_const { " const" } else { "" }
        )
    });
    let mut typed: Vec<String> = f
        .param_hints
        .iter()
        .map(|(i, c)| format!("a{}: {c} *", u32::from(*i) + 1))
        .collect();
    if let Some(c) = &f.ret_hint {
        typed.push(format!("result: {c} *"));
    }
    let hints = if typed.is_empty() {
        String::new()
    } else {
        format!("hints:    {}\n", typed.join(", "))
    };
    let class = f
        .name
        .as_deref()
        .and_then(crate::analysis::classes::class_of)
        .map_or(String::new(), |c| {
            format!("class:    {c} (class_layout(\"{c}\") for the fields)\n")
        });
    let returns = match f.returns_value {
        Some(false) => "returns:  nothing a caller uses\n",
        _ => "",
    };
    let throws = a.throw_sites.get(&entry).map_or(String::new(), |sites| {
        let mut kinds: Vec<String> = Vec::new();
        let mut seen = BTreeSet::new();
        let mut cleanup = false;
        for s in sites {
            for c in &s.catches {
                if seen.insert(c.clone()) {
                    kinds.push(c.clone());
                }
            }
            cleanup |= s.cleanup;
        }
        let one = sites.len() == 1;
        let what = match (kinds.is_empty(), cleanup) {
            (true, false) => "catch nothing".to_owned(),
            (true, true) => "clean up".to_owned(),
            (false, false) => {
                format!(
                    "catch{} {}",
                    if one { "es" } else { "" },
                    capped(&kinds, ", ")
                )
            }
            (false, true) => format!(
                "catch{} {} and clean{} up",
                if one { "es" } else { "" },
                capped(&kinds, ", "),
                if one { "s" } else { "" }
            ),
        };
        format!(
            "throws:   {} throw site{} {what}\n",
            sites.len(),
            plural(sites.len())
        )
    });
    let span = f.end.saturating_sub(f.start);
    let scattered = if control_flow_dispersed(f.size(), span, f.blocks.len()) {
        format!(
            "scattered: {} bytes of code across {span:#x} in {} blocks \u{2014} control flow is obfuscated (a VM, flattening or junk jumps)\n",
            f.size(),
            f.blocks.len()
        )
    } else {
        String::new()
    };
    let decompiled = crate::analysis::decompile::decompile(p, a, o, entry);
    let header = |tag: &str| -> Option<String> {
        decompiled.as_ref().and_then(|text| {
            text.lines()
                .find_map(|l| l.strip_prefix(tag).map(str::to_owned))
        })
    };
    let effects = header("// effects: ").map_or(String::new(), |e| format!("effects:  {e}\n"));
    let asserts = header("// asserts: ").map_or(String::new(), |a| format!("asserts:  {a}\n"));
    let passed = header("// callers pass: ").map_or(String::new(), |v| format!("passed:   {v}\n"));
    let wire = header("// wire: ").map_or(String::new(), |w| format!("wire:     {w}\n"));
    let source = header("// source: ").map_or(String::new(), |f| format!("source:   {f}\n"));
    let clones = a.clones_of(entry);
    let clones = if clones.len() > 1 {
        let others: Vec<u64> = clones.iter().copied().filter(|e| *e != entry).collect();
        format!(
            "clones:   {} other function{} {} this code [{}]\n",
            others.len(),
            plural(others.len()),
            if others.len() == 1 { "runs" } else { "run" },
            names(&others)
        )
    } else {
        String::new()
    };
    let comment = o
        .comments
        .get(&f.entry)
        .map_or(String::new(), |c| format!("comment:  {c}\n"));
    Some(format!(
        "name:     {}\nentry:    {:#x}\nrange:    {:#x}..{:#x} ({} bytes)\n{comment}{declared}{hints}{class}{source}{returns}{throws}{scattered}{clones}{effects}{asserts}{passed}{wire}shape:    {} blocks, {} instrs{}{}\ncallers:  {} [{}]\ncallees:  {} [{}]\n{virt}strings:  {}\ndata:     {}\n",
        name_of(a, o, f.entry),
        f.entry,
        f.start,
        f.end,
        f.size(),
        f.blocks.len(),
        f.instr_count,
        if loops { ", has loops" } else { "" },
        if tables > 0 {
            format!(", {tables} jump table(s)")
        } else {
            String::new()
        },
        f.callers.len(),
        names(&f.callers),
        callees.len(),
        capped(&callees, ", "),
        list(&strings),
        list(&data),
    ))
}

/// Renders every string a function references, deduplicated by target.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the literals.
/// * `a` - The analysis.
/// * `o` - User names for the header.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// A `# N strings referenced by <name>` header, a column header, then up to
/// 100 `site string_va text` rows; `None` when no function starts at `entry`.
pub fn function_strings_tsv(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> Option<String> {
    /// Hard cap on rows.
    const CAP: usize = 100;
    let f = a.function(entry)?;
    let mut rows: Vec<String> = Vec::new();
    let mut seen = BTreeSet::new();
    for (target, site) in a.refs_from(entry) {
        let Some((start, lit)) = referenced_literal(p, a, target, 120) else {
            continue;
        };
        if !seen.insert(start) {
            continue;
        }
        let at = if start == target {
            String::new()
        } else {
            format!(" +{:#x}", target - start)
        };
        rows.push(format!("{:<#12x} {start:<#12x} {lit}{at}", site.va));
    }
    let total = rows.len();
    let mut out = format!(
        "# {} strings referenced by {} (showing {})\n# site        string_va    text\n",
        total,
        name_of(a, o, f.entry),
        total.min(CAP)
    );
    for r in rows.iter().take(CAP) {
        out.push_str(r);
        out.push('\n');
    }
    Some(out)
}

/// Renders a shape class with what differs per member.
///
/// Every function that runs the same code as `entry` over other operands is
/// listed with the string literals and data addresses that make it
/// different: a family of registrations, one row per registered thing. A
/// shape class is what a compiler leaves when one function template or
/// one macro is instantiated per item, an attribute registered by name, a
/// message class by its four-character code; the sibling list read this way
/// is the item table the source held.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Discovery results.
/// * `o` - Names in force.
/// * `entry` - Any member of the shape class.
/// * `limit` - Rows shown at most.
///
/// # Returns
///
/// The table, or `None` when `entry` is not a function.
pub fn shape_siblings_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    limit: usize,
) -> Option<String> {
    /// Literals and addresses spelled per row at most.
    const PER_ROW: usize = 6;
    let f = a.function(entry)?;
    let mut members: Vec<u64> = a.shapes_of(f.entry).to_vec();
    if members.is_empty() {
        members.push(f.entry);
    }
    members.sort_unstable();
    members.dedup();
    let total = members.len();
    let mut out = format!(
        "# {total} functions share the shape of {}, showing {}\n",
        name_of(a, o, f.entry),
        total.min(limit)
    );
    out.push_str("entry\tname\tstrings\tdata\n");
    for &member in members.iter().take(limit) {
        let mut strings: Vec<String> = Vec::new();
        let mut data: Vec<String> = Vec::new();
        let mut seen = BTreeSet::new();
        for (target, site) in a.refs_from(member) {
            if site.is_branch() || !seen.insert(target) {
                continue;
            }
            match string_literal(p, target, 60) {
                Some((_, lit)) if strings.len() < PER_ROW => strings.push(shown_text(&lit)),
                Some(_) => {}
                None if data.len() < PER_ROW => data.push(
                    o.names
                        .get(&target)
                        .cloned()
                        .or_else(|| a.classes.global_hints.get(&target).cloned())
                        .unwrap_or_else(|| format!("{target:#x}")),
                ),
                None => {}
            }
        }
        let _ = writeln!(
            out,
            "{member:#x}\t{}\t{}\t{}",
            name_of(a, o, member),
            strings.join(" "),
            data.join(" ")
        );
    }
    Some(out)
}

/// Longest string read when matching a search against it.
///
/// A build path is most of eighty characters before it names a file, so
/// matching the display text would hide every `foo.cc` in this binary
/// behind the machine it was built on.
pub(super) const STRING_MATCH_CAP: usize = 400;

/// Longest string shown in a row.
pub(super) const STRING_SHOWN_MAX: usize = 76;

/// Shortens a matched string for display, keeping the end of a path.
///
/// A path's prefix is the build machine and repeats on every string in the
/// image; its tail is the file, which is what the reader asked for.
///
/// # Arguments
///
/// * `lit` - The full literal, quotes included.
///
/// # Returns
///
/// The literal, or a shortened form marked with `...`.
pub(super) fn shown_text(lit: &str) -> String {
    if lit.chars().count() <= STRING_SHOWN_MAX {
        return lit.to_owned();
    }
    let body = lit.trim_matches('"');
    let keep = STRING_SHOWN_MAX - 4;
    if body.contains('/') || body.contains('\\') {
        let tail: String = body
            .chars()
            .skip(body.chars().count().saturating_sub(keep))
            .collect();
        return format!("\"...{tail}\"");
    }
    let head: String = body.chars().take(keep).collect();
    format!("\"{head}...\"")
}
