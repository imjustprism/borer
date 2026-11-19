//! The tools that read bytes and find things.
//!
//! They are disassembly at an address, typed reads, hex dumps, entropy,
//! strings, symbols, byte and text search, crypto constants, the functions
//! that use a string, the session's ledger and its types, and the `query`
//! tool over the resources.

use std::fmt::Write as _;

use borer_engine::analysis::{Analysis, Overlay, parse_off, render, stated};
use borer_engine::answer::Need;
use borer_engine::program::Feature;
use borer_engine::strings::walk::string_rows;
use borer_engine::{disasm, entropy, hexdump as hexfmt, memory, num};

use super::params::{
    AnnotationsParams, CryptoParams, DisassembleParams, EntropyParams, FindFunctionByStringParams,
    HexdumpParams, Page, QueryParams, ReadParams, SearchKind, SearchParams, StringsParams,
    SymbolsParams, TypesParams, count_param, to_usize,
};
use super::{Failure, Held, run, tabled};

/// Disassembles a run of instructions at an address or name.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded, the address does not resolve or is unmapped, or
/// the architecture has no decoder.
pub fn disassemble(h: &dyn Held, p: &DisassembleParams) -> Result<String, Failure> {
    let count = count_param(p.count, 32, 256, "count")?;
    let n = count.n;
    let with_bytes = p.bytes.unwrap_or(false);
    run(h, Need::Best(Feature::Discover), |s| {
        let (prog, a) = (s.program(), s.analysis());
        let asked = s.addr(&p.address)?;
        let isa = prog.isa_for(Feature::Disasm)?;
        let va = render::instruction_at_or_before(prog, a, asked).unwrap_or(asked);
        let snapped = if va == asked {
            String::new()
        } else {
            format!("; {asked:#x} is inside an instruction, listing from {va:#x}")
        };
        let code = prog
            .read_va_upto(va, 16 * 1024)
            .ok_or_else(|| prog.no_bytes_at(va))?;
        let limit = render::sweep_limit(prog, a, va);
        let window = limit
            .and_then(|end| usize::try_from(end - va).ok())
            .and_then(|n| code.get(..n.min(code.len())))
            .unwrap_or(code);
        let lines = disasm::disassemble_program(prog, window, va, isa, n);
        let o = s.overlay();
        let ends = limit.map_or(String::new(), |end| {
            format!("; code ends at {end:#x}, what follows is data")
        });
        let caveat = Some(render::listing_caveat(prog, a, va))
            .filter(|c| !c.is_empty())
            .map_or(String::new(), |c| format!("; {c}"));
        let mut out = format!(
            "# {} instructions at {:#x}{snapped}{ends}{caveat}\n",
            lines.len(),
            va
        );
        for l in &lines {
            if let Some(n) = o.names.get(&l.va) {
                out.push_str(&format!("            ; = {n} =\n"));
            }
            let mut text = l.text.clone();
            if let Some(c) = o.comments.get(&l.va) {
                text.push_str(&format!("  // {c}"));
            }
            if with_bytes {
                let mut hexb = String::new();
                for b in &l.bytes {
                    hexb.push_str(&format!("{b:02x} "));
                }
                out.push_str(&format!("{:#x}  {:<24} {text}\n", l.va, hexb.trim_end()));
            } else {
                out.push_str(&format!("{:#x}  {text}\n", l.va));
            }
        }
        Ok(out)
    })
    .map(|text| count.noted(text))
}

/// Reads typed values at an address or name.
///
/// Reading stops at the first address that is not there, and the header
/// says so: returning fewer values than were asked for without a word
/// would leave the caller to notice the shortfall by counting rows. With
/// `type`, a user type is laid over the bytes instead
/// ([`render::typed_tsv`]): `count` records of it, or as many as the type's
/// own array states.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// For both a kind and a type, a type that does not parse, an address that
/// does not resolve or bytes that are not mapped.
pub fn read(h: &dyn Held, p: &ReadParams) -> Result<String, Failure> {
    let count = count_param(p.count, 1, 256, "count")?;
    let n = count.n;
    let address = &p.address;
    if let Some(spelled) = &p.r#type {
        if p.kind.is_some() {
            return Err(Failure::asked(
                "`kind` and `type` both say what the bytes are; give one",
            ));
        }
        let parsed = borer_engine::analysis::utypes::parse_type(spelled)
            .map_err(|e| Failure::asked(e.to_string()))?;
        let parsed = if n > 1 {
            borer_engine::analysis::utypes::TypeExpr::Array(Box::new(parsed), num::from_usize(n))
        } else {
            parsed
        };
        return run(h, Need::File, |s| {
            if parse_off(address).is_some() {
                return Err("a typed read takes an address; off: reads by `kind`".to_owned());
            }
            let va = s.addr(address)?;
            render::typed_tsv(s.program(), s.kept(), s.overlay(), va, &parsed)
        })
        .map(|text| count.noted(text));
    }
    let kind_text = p.kind.unwrap_or_default();
    let kind: memory::Kind = kind_text.into();
    run(h, Need::File, |s| {
        let prog = s.program();
        let (start, values, place) = match parse_off(address) {
            Some(off) => (
                off,
                memory::read_values_at_offset(prog, off, kind, n)?,
                "off:",
            ),
            None => {
                let va = s.addr(address)?;
                (va, memory::read_values(prog, va, kind, n)?, "")
            }
        };
        let o = s.overlay();
        let sec = if place.is_empty() {
            prog.section_at(start)
                .map_or_else(String::new, |s| format!(" in {}", s.name))
        } else {
            String::from(", rows by file offset")
        };
        let mut out = format!("# {} x {kind_text} at {place}{start:#x}{sec}", values.len());
        if values.len() < n {
            let next = values
                .last()
                .map_or(start, |v| v.at.wrapping_add(num::from_usize(v.size)));
            out.push_str(&format!(
                "; asked for {n}, nothing readable at {place}{next:#x}"
            ));
        }
        out.push('\n');
        for v in &values {
            let mut text = v.text.clone();
            if let Some(name) = v
                .target
                .and_then(|t| render::pointee_name(prog, s.kept(), o, t))
            {
                text.push_str(&format!(" -> {name}"));
            }
            if let Some(s) = prog
                .signing(v.at)
                .filter(|_| place.is_empty() && v.size == 8)
            {
                text.push_str(&format!(" signed {s}"));
            }
            if let Some(rest) = memory::rest_of_cut(v, kind) {
                text.push_str(&format!(", cut: the rest reads from {place}{rest:#x}"));
            }
            out.push_str(&format!("{:<12} {text}\n", format!("{:#x}", v.at)));
        }
        Ok(out)
    })
    .map(|text| count.noted(text))
}

/// Lists high-entropy regions over every byte of the file.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded, the threshold is outside 0..8 or the limit is
/// zero.
pub fn entropy(h: &dyn Held, p: &EntropyParams) -> Result<String, Failure> {
    let window = to_usize(p.window.unwrap_or(1024));
    let threshold = entropy_threshold(p.threshold.unwrap_or(7.2)).map_err(Failure::asked)?;
    let page = Page::new(
        p.offset,
        p.limit,
        None,
        entropy::REGIONS_MAX,
        entropy::REGIONS_MAX,
    )?;
    run(h, Need::File, |s| {
        Ok(entropy::report(
            s.program(),
            window,
            threshold,
            page.offset,
            page.limit.n,
        ))
    })
    .map(|text| page.limit.noted(text))
}

/// Reads an entropy threshold, the same for `entropy` and the command line.
///
/// # Arguments
///
/// * `threshold` - Minimum bits per byte, as given.
///
/// # Errors
///
/// When the threshold is outside `0..=8` bits per byte: no window holds
/// more than eight, and a negative one would report every window
/// ([`entropy::threshold_error`]).
pub fn entropy_threshold(threshold: f64) -> Result<f64, String> {
    entropy::threshold_error(threshold).map_or(Ok(threshold), Err)
}

/// Hexdumps a byte range at an address or name.
///
/// A hexdump is a "show me what is there" tool, so a length that runs off
/// the end of the section gives back the bytes that are there rather than
/// nothing: the header states the range it actually covers, so the short
/// answer says so itself. Only an address with nothing at all behind it is
/// refused, and then the message blames the address rather than the length,
/// which is what was actually wrong.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the range is not entirely mapped.
pub fn hexdump(h: &dyn Held, p: &HexdumpParams) -> Result<String, Failure> {
    let length = count_param(p.length, 64, hexfmt::HEXDUMP_MAX, "length")?;
    run(h, Need::File, |s| {
        if let Some(off) = parse_off(&p.address) {
            return hexfmt::file_hexdump(s.program(), off, length.n);
        }
        let va = s.addr(&p.address)?;
        hexfmt::hex_rows(s.program(), va, length.n).spell(s.program())
    })
    .map(|text| length.noted(text))
}

/// Scans every byte of the file for known crypto and hash constants,
/// grouped by algorithm, with one page of the per-site rows.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded.
pub fn find_crypto_constants(h: &dyn Held, p: &CryptoParams) -> Result<String, Failure> {
    let page = Page::new(p.offset, p.limit, None, 200, 500)?;
    run(h, Need::Best(Feature::Discover), |s| {
        Ok(render::crypto_tsv(
            s.program(),
            s.analysis(),
            s.overlay(),
            page.offset,
            page.limit.n,
        ))
    })
    .map(|text| page.limit.noted(text))
}

/// Lists the functions referencing a string that matches a filter.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the analysis is unavailable.
pub fn find_function_by_string(
    h: &dyn Held,
    p: &FindFunctionByStringParams,
) -> Result<String, Failure> {
    let offset = to_usize(p.offset.unwrap_or(0));
    let limit = count_param(p.limit, 50, 300, "limit")?;
    run(h, Need::Code(Feature::Discover), |s| {
        Ok(render::functions_by_string_tsv(
            s.program(),
            s.analysis(),
            s.overlay(),
            &p.filter,
            offset,
            limit.n,
        ))
    })
    .map(|text| limit.noted(text))
}

/// Lists printable strings with filtering and paging.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the encoding is unknown.
pub fn strings(h: &dyn Held, p: &StringsParams) -> Result<String, Failure> {
    let min = to_usize(p.min_length.unwrap_or(5).max(4));
    let encoding = p.encoding.unwrap_or_default().into();
    let page = Page::new(p.offset, p.limit, p.count_only, 200, 500)?;
    run(h, Need::Best(Feature::Discover), |s| {
        let limit = if page.count_only { 0 } else { page.limit.n };
        let rows = string_rows(
            s.program(),
            s.analysis(),
            encoding,
            min,
            p.filter.as_deref(),
            page.offset,
            limit,
        );
        Ok(if page.count_only {
            rows.counted()
        } else {
            rows.spell()
        })
    })
    .map(|text| page.limit.noted(text))
}

/// Lists imports and exports with filtering and paging.
///
/// An import nothing references is a redirected or leftover slot, the shape
/// a patched binary leaves behind, so its row says so.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded.
pub fn symbols(h: &dyn Held, p: &SymbolsParams) -> Result<String, Failure> {
    let want = p.kind.map(borer_engine::program::SymbolKind::from);
    let page = Page::new(p.offset, p.limit, p.count_only, 50, 1000)?;
    run(h, Need::Best(Feature::Discover), |s| {
        let rows = render::symbol_rows(
            s.program(),
            s.analysis(),
            want,
            p.filter.as_deref(),
            page.offset,
            page.limit.n,
        );
        Ok(if page.count_only {
            rows.counted()
        } else {
            rows.spell()
        })
    })
    .map(|text| page.limit.noted(text))
}

/// Searches every section, then the bytes no section maps, for a byte
/// pattern or a text substring.
///
/// A text query of spaces or a tab is text to find; only a byte pattern
/// with no token is empty.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded, the query is empty, the pattern does not
/// parse, or the kind is unknown.
pub fn search(h: &dyn Held, p: &SearchParams) -> Result<String, Failure> {
    let kind = p.kind.unwrap_or_default();
    let offset = p.offset.unwrap_or(0);
    let limit = count_param(p.limit, 200, borer_engine::search::HITS_MAX, "limit")?;
    let count_only = p.count_only.unwrap_or(false);
    let query = &p.query;
    let empty = match kind {
        SearchKind::Bytes => query.trim().is_empty(),
        SearchKind::Text => query.is_empty(),
    };
    if empty {
        return Err(Failure::asked(
            "the query is empty: give hex bytes with ?? wildcards, or kind=text and a substring",
        ));
    }
    run(h, Need::Best(Feature::Discover), |s| {
        let prog = s.program();
        let mut hits = match kind {
            SearchKind::Bytes => {
                let lanes = borer_engine::search::parse_masked(query).map_err(|why| {
                    format!(
                        "bad byte pattern {}: {why}",
                        borer_engine::text::quoted(query)
                    )
                })?;
                borer_engine::search::find_masked(prog, &lanes, offset)
            }
            SearchKind::Text => borer_engine::search::find_text(prog, query, offset),
        };
        hits.hits.truncate(limit.n);
        Ok(render_hits(
            &hits,
            offset,
            count_only,
            (s.analysis(), s.overlay()),
        ))
    })
    .map(|text| limit.noted(text))
}

/// Renders one page of search hits, one `function: va va` row per run of
/// hits inside one function, under a header that says how many there are
/// in all and where the page starts.
///
/// A byte pattern hits a hundred times inside one function, and a row per
/// hit named the function on every one: 321 of 500 rows on kernel32 shared
/// a function with the row before. Consecutive hits in one function share a
/// row; a hit outside every function is under `-`. The file offset is left
/// out where it follows from the address and the section table; a hit in
/// bytes no section maps has no address, so it is written `off=<n>`, the
/// form `hexdump` and `read` take back.
///
/// # Arguments
///
/// * `page` - The page and the total.
/// * `offset` - Where the page starts, for the header.
/// * `count_only` - Answer the count alone, with no page to speak of.
/// * `names` - The analysis and the overlay, for the function names.
///
/// # Returns
///
/// A `# N hits, showing S of N from O` header, a column header and the
/// rows; `# N hits` alone for a count.
#[must_use]
pub fn render_hits(
    page: &borer_engine::search::Hits,
    offset: usize,
    count_only: bool,
    names: (&Analysis, &Overlay),
) -> String {
    let (a, o) = names;
    if count_only {
        return format!("# {} hits\n", page.total);
    }
    let mut out = format!(
        "# {} hits, showing {} of {} from {offset}\n# function: va ...\n",
        page.total,
        page.hits.len(),
        page.total
    );
    let entry_of =
        |h: &borer_engine::search::Hit| h.va.and_then(|v| a.function_at(v)).map(|f| f.entry);
    for run in page.hits.chunk_by(|x, y| entry_of(x) == entry_of(y)) {
        let Some(first) = run.first() else {
            continue;
        };
        let name = entry_of(first).map_or_else(
            || "-".to_owned(),
            |e| borer_engine::analysis::name_of(a, o, e),
        );
        let _ = write!(out, "{name}:");
        for h in run {
            match h.va {
                Some(va) => {
                    let _ = write!(out, " {va:#x}");
                }
                None => {
                    let _ = write!(out, " off={:#x}", h.file_off);
                }
            }
        }
        out.push('\n');
    }
    out
}

/// Lists the user types and where they are applied.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When `limit` is zero.
pub fn types(h: &dyn Held, p: &TypesParams) -> Result<String, Failure> {
    let page = Page::new(
        p.offset,
        p.limit,
        p.count_only,
        50,
        borer_engine::analysis::utypes::TYPES_ROWS_MAX,
    )?;
    let o = tabled(&h.user_overlay());
    let rows = stated::rows(&o);
    let (_, total, table) = borer_engine::analysis::utypes::list_tsv(
        &o.types,
        &o.applied,
        &rows,
        p.filter.as_deref(),
        page.offset,
        page.limit.n,
    );
    if page.count_only {
        return Ok(format!(
            "# {total} rows ({} type(s), {} applied)\n",
            o.types.len(),
            o.applied.len()
        ));
    }
    Ok(page.limit.noted(table))
}

/// Lists the session's ledger: names, stated fields, findings and open
/// questions, a page at a time ([`render::annotations_tsv`]).
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When `limit` is zero.
pub fn annotations(h: &dyn Held, p: &AnnotationsParams) -> Result<String, Failure> {
    let page = Page::new(
        p.offset,
        p.limit,
        p.count_only,
        render::LEDGER_ROWS_DEFAULT,
        render::LEDGER_ROWS_MAX,
    )?;
    let out = render::annotations_tsv(
        &tabled(&h.user_overlay()),
        &borer_engine::text::Filter::new(p.filter.as_deref()),
        page.offset,
        page.limit.n,
        page.count_only,
    );
    if page.count_only {
        return Ok(out);
    }
    Ok(page.limit.noted(out))
}

/// Reads a `borer://` resource by URI, for a caller whose host has no way
/// to read MCP resources ([`Held::read`]).
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When the URI names no resource, a suffix does not read, or the resource
/// refuses.
pub fn query(h: &dyn Held, p: &QueryParams) -> Result<String, Failure> {
    h.read(&p.uri)
}
