//! `borer://find`, and the tests of the search tools.
//!
//! The tools that find things (strings, symbols, byte and text search, crypto
//! constants, the functions that use a string) are the catalog's
//! ([`borer_front::tools`]).

use borer_engine::analysis::find;
use borer_engine::program::Feature;
use rmcp::ErrorData;

use crate::BorerServer;
pub(crate) use borer_front::tools::render_hits;

impl BorerServer {
    /// One search over every name table, ranked
    /// ([`borer_engine::analysis::find::everywhere`]).
    ///
    /// # Arguments
    ///
    /// * `query` - The query as typed ([`find::Query::parse`]).
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn find_text(&self, query: &str) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Discover, |p, a, o| {
            let q = find::Query::parse(query);
            Ok(find::everywhere(p, a, o, &q, usize::MAX).spell())
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::raw_server;

    /// `borer://find` answers every name table at once, an address form
    /// first, and a prefix narrows it.
    ///
    /// # Panics
    ///
    /// When a row or the header differs.
    #[test]
    fn find_answers_every_table_and_an_address_first() {
        let server = raw_server();
        let named = server
            .resource_text("borer://find/SUB_1000")
            .expect("answers");
        assert!(
            named.starts_with("# showing 1 of 1 hits: function 1 of 1\n# rank kind addr source text\nexact function 0x1000 - sub_1000\n"),
            "{named}"
        );
        let at = server
            .resource_text("borer://find/0x1000")
            .expect("answers");
        assert!(
            at.contains("\n# rank kind addr source text\nexact address 0x1000 va sub_1000\n"),
            "{at}"
        );
        let strings = server
            .resource_text("borer://find/%22SUB_1000")
            .expect("answers");
        assert!(strings.starts_with("# showing 0 of 0 hits\n"), "{strings}");
    }

    /// `borer://find` reads its query percent-decoded: `%22` is the `"`
    /// that narrows it to the strings, which the encoded text would not find.
    ///
    /// # Panics
    ///
    /// When the string is not found as the decoded query asks.
    #[test]
    fn find_decodes_its_query() {
        use borer_engine::program::{Arch, Program, Section};
        let mut bytes = vec![0xc3; 0x10];
        bytes.extend_from_slice(b"crypto_box\0");
        bytes.resize(0x20, 0);
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![
                Section::mapped(".text", 0x1000, 0, 0x10, false, true),
                Section::mapped(".rdata", 0x2000, 0x10, 0x10, false, false),
            ],
        );
        let server = crate::testing::server_with(p);
        let text = server
            .resource_text("borer://find/%22crypto")
            .expect("answers");
        assert!(
            text.contains(
                "# rank kind addr source text\nprefix string 0x2000 .rdata:ascii crypto_box\n"
            ),
            "{text}"
        );
    }

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

    /// The string search's `filter` doc gives the engine's literal floor,
    /// under which a string matches only whole.
    ///
    /// # Panics
    ///
    /// When the doc names another floor or none.
    #[test]
    fn the_string_search_documents_the_engines_floor() {
        use borer_engine::analysis::render::PRINTABLE_MIN;
        let tools = crate::BorerServer::tool_router().list_all();
        let doc = tools
            .iter()
            .find(|t| t.name == "find_function_by_string")
            .and_then(|t| {
                t.input_schema
                    .get("properties")?
                    .get("filter")?
                    .get("description")
            })
            .and_then(serde_json::Value::as_str)
            .unwrap_or_default();
        assert!(
            doc.contains(&format!("under {PRINTABLE_MIN} printable characters")),
            "{doc}"
        );
    }

    /// The string search's description names the table of texts built at
    /// run time, which follows its rows or stands in for them.
    ///
    /// # Panics
    ///
    /// When the description leaves the table out.
    #[test]
    fn the_string_search_names_its_table_of_built_texts() {
        let tools = crate::BorerServer::tool_router().list_all();
        let said = tools
            .iter()
            .find(|t| t.name == "find_function_by_string")
            .and_then(|t| t.description.as_deref())
            .unwrap_or_default();
        assert!(said.contains("`built_by written_at text` rows"), "{said}");
    }
}
