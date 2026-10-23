//! The tools that find things: strings, symbols, byte and text search,
//! crypto constants, and the functions that use a string.

use std::fmt::Write as _;

use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::program::Feature;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::errors::err_params;
use crate::params::{
    CryptoParams, Filter, FindFunctionByStringParams, Page, SearchKind, SearchParams,
    StringsParams, SymbolsParams, count_param, to_usize,
};
use crate::strwalk;
use crate::strwalk::{StringRow, strings_page, walk_rows};

#[tool_router(router = search_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Scans every byte of the file for known crypto and hash constants,
    /// grouped by algorithm, with one page of the per-site rows.
    ///
    /// The tool takes paging parameters and so refuses one it does not
    /// know, where it took no parameters and ignored any it was given.
    ///
    /// # Arguments
    ///
    /// * `CryptoParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    #[tool(
        description = "Find crypto constants and tables (AES, SHA, MD5, CRC-32, ChaCha, Blowfish, FNV, Base64) and hashed API names as `va section algorithm` rows, paged. Use it to locate crypto code, then xrefs a hit; not for strings (use strings).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn find_crypto_constants(
        &self,
        Parameters(CryptoParams { offset, limit }): Parameters<CryptoParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, None, 200, 500)?;
        self.with_program(|p| {
            Ok(render::crypto_tsv(
                p,
                &self.analysis_or_empty(),
                &self.overlay(),
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
    /// * `FindFunctionByStringParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the analysis is unavailable.
    #[tool(
        description = "Find the functions whose strings contain a text, case-insensitively: a numbered string legend, then `entry name: 1 2` rows, paged. Not for one function's strings (use function_strings).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn find_function_by_string(
        &self,
        Parameters(FindFunctionByStringParams {
            filter,
            offset,
            limit,
        }): Parameters<FindFunctionByStringParams>,
    ) -> Result<String, ErrorData> {
        let offset = to_usize(offset.unwrap_or(0));
        let limit = count_param(limit, 50, 300, "limit")?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            Ok(render::functions_by_string_tsv(
                p, a, o, &filter, offset, limit.n,
            ))
        })
        .map(|text| limit.noted(text))
    }

    /// Lists printable strings with filtering and paging.
    ///
    /// # Arguments
    ///
    /// * `StringsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the encoding is unknown.
    #[tool(
        description = "List printable ASCII and UTF-16LE strings as `va len enc text` rows, paged, skipping bytes of code. Not for the code using one (use find_function_by_string).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn strings(
        &self,
        Parameters(StringsParams {
            min_length,
            filter,
            encoding,
            offset,
            limit,
            count_only,
        }): Parameters<StringsParams>,
    ) -> Result<String, ErrorData> {
        let min = to_usize(min_length.unwrap_or(5).max(4));
        let filter = Filter::new(filter.as_deref());
        let encoding = encoding.unwrap_or_default();
        let page = Page::new(offset, limit, count_only, 200, 500)?;
        self.with_program(|p| {
            let a = self.analysis_or_empty();
            let rows: Vec<StringRow> = if min >= strwalk::WALK_MIN {
                strwalk::load_or_build(&self.strings, p, &a).rows(encoding, min)
            } else {
                walk_rows(p, &a, encoding, min)
            };
            Ok(strings_page(
                p,
                rows,
                &filter,
                (min, encoding),
                (page.offset, page.limit.n),
                page.count_only,
            ))
        })
        .map(|text| page.limit.noted(text))
    }

    /// Lists imports and exports with filtering and paging.
    ///
    /// An import nothing references is a redirected or leftover slot, the
    /// shape a patched binary leaves behind, so its row says so.
    ///
    /// # Arguments
    ///
    /// * `SymbolsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    #[tool(
        description = "List imports, exports, forwards, locals and data as demangled `kind addr name` rows by module, paged. Not for discovered code (use functions) or call sites (use xrefs).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn symbols(
        &self,
        Parameters(SymbolsParams {
            kind,
            filter,
            offset,
            limit,
            count_only,
        }): Parameters<SymbolsParams>,
    ) -> Result<String, ErrorData> {
        let want = kind.map(borer_engine::program::SymbolKind::from);
        let page = Page::new(offset, limit, count_only, 50, 1000)?;
        self.with_program(|p| {
            let (_, total, text) = render::symbols_tsv(
                p,
                &self.analysis_or_empty(),
                want,
                filter.as_deref(),
                page.offset,
                page.limit.n,
            );
            if page.count_only {
                return Ok(format!("# {total} symbols\n"));
            }
            Ok(text)
        })
        .map(|text| page.limit.noted(text))
    }

    /// Searches every section, then the bytes no section maps, for a byte
    /// pattern or a text substring.
    ///
    /// A text query of spaces or a tab is text to find; only a byte
    /// pattern with no token is empty.
    ///
    /// # Arguments
    ///
    /// * `SearchParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the query is empty, the pattern does not
    /// parse, or the kind is unknown.
    #[tool(
        description = "Search every byte of the file for a hex pattern with ?? wildcards, or text with kind=text, as `function: va ...` rows, paged. Not for listing strings (use strings).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn search(
        &self,
        Parameters(SearchParams {
            query,
            kind,
            offset,
            limit,
            count_only,
        }): Parameters<SearchParams>,
    ) -> Result<String, ErrorData> {
        let kind = kind.unwrap_or_default();
        let offset = offset.unwrap_or(0);
        let limit = count_param(limit, 200, borer_engine::search::HITS_MAX, "limit")?;
        let count_only = count_only.unwrap_or(false);
        let empty = match kind {
            SearchKind::Bytes => query.trim().is_empty(),
            SearchKind::Text => query.is_empty(),
        };
        if empty {
            return Err(err_params(
                "the query is empty: give hex bytes with ?? wildcards, or kind=text and a substring",
            ));
        }
        self.with_program(|p| {
            let mut hits = match kind {
                SearchKind::Bytes => {
                    let pattern = borer_engine::search::parse_pattern(&query).ok_or_else(|| {
                        format!(
                            "bad byte pattern {}: use hex tokens or ??",
                            borer_engine::text::quoted(&query)
                        )
                    })?;
                    borer_engine::search::find_bytes(p, &pattern, offset)
                }
                SearchKind::Text => borer_engine::search::find_text(p, &query, offset),
            };
            hits.hits.truncate(limit.n);
            let a = self.analysis_or_empty();
            let o = self.overlay();
            Ok(render_hits(&hits, offset, count_only, (&a, &o)))
        })
        .map(|text| limit.noted(text))
    }
}

/// Renders one page of search hits, one `function: va va` row per run of
/// hits inside one function, under a header that says how many there are
/// in all and where the page starts.
///
/// A byte pattern hits a hundred times inside one function, and a row per
/// hit named the function on every one: 321 of 500 rows on kernel32 shared
/// a function with the row before. Consecutive hits in one function share
/// a row; a hit outside every function is under `-`. The file offset is
/// left out where it follows from the address and the section table; a hit
/// in bytes no section maps has no address, so it is written `off=<n>`,
/// the form `hexdump` and `read` take back.
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
pub(crate) fn render_hits(
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

#[cfg(test)]
mod tests {
    use crate::testing::raw_server;

    /// A search page says `showing N of M`, and a count states no page.
    ///
    /// # Panics
    ///
    /// When either header is worded otherwise.
    #[test]
    fn a_search_page_says_showing_n_of_m() {
        use crate::params::SearchParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        let search = |count_only| {
            server
                .search(Parameters(SearchParams {
                    query: "c3".to_owned(),
                    kind: None,
                    offset: None,
                    limit: None,
                    count_only: Some(count_only),
                }))
                .expect("searches")
        };
        let page = search(false);
        assert!(
            page.starts_with("# 256 hits, showing 200 of 256 from 0\n"),
            "{page}"
        );
        assert_eq!(search(true), "# 256 hits\n");
    }
}
