//! The tests of the tools that read resources and run scripts, which the
//! catalog answers ([`borer_front::tools`]).

#[cfg(test)]
mod tests {
    use crate::testing::{raw_server, without_evidence};

    /// The `script` tool runs inline code and applies only on request.
    ///
    /// Its `query` calls are answered from the resources, `borer://script`
    /// refused; proposals stay a preview until `dry_run=false`, and then
    /// only those the listings can show at an address a section holds land.
    ///
    /// # Panics
    ///
    /// When an answer, a refusal or the overlay differs.
    #[test]
    fn script_runs_inline_code_queries_resources_and_applies_on_request() {
        use crate::params::ScriptParams;
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![0x90; 0x20];
        code.push(0xc3);
        let text = Section::mapped(".text", 0x1000, 0, 0x21, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let script = |code: &str, dry_run: Option<bool>| {
            crate::testing::call(
                borer_front::tools::script,
                &server,
                &ScriptParams {
                    code: code.to_owned(),
                    dry_run,
                },
            )
            .expect("a script answers")
        };
        let out = script(
            r#"print(functions().len);
               print(query("borer://disasm/0x1000").contains("nop"));
               print(help().contains("query(uri)"));"#,
            None,
        );
        assert!(out.starts_with("1\ntrue\ntrue\n"), "{out}");
        let out = script(r#"query("borer://script/x.rhai");"#, None);
        assert!(out.contains("scripts do not run scripts"), "{out}");
        let out = script(r#"query("borer://nope");"#, None);
        assert!(
            out.contains("# script failed: Runtime error: unknown resource borer://nope"),
            "{out}"
        );
        let propose =
            r#"rename(0x1000, "start"); rename(0x9000, "gone"); comment(0x1001, "here");"#;
        let out = script(propose, None);
        assert!(out.contains("# dry-run: pass dry_run=false"), "{out}");
        assert!(crate::state::read_lock(&server.overlay).names.is_empty());
        let out = script(propose, Some(false));
        assert!(
            out.contains("# applied names at 1 addresses and comments at 1, the last proposal for an address winning; 1 skipped"),
            "{out}"
        );
        let overlay = crate::state::read_lock(&server.overlay);
        assert_eq!(
            overlay.names.get(&0x1000).map(String::as_str),
            Some("start")
        );
        assert_eq!(
            overlay.comments.get(&0x1001).map(String::as_str),
            Some("here")
        );
    }

    /// A script's `query` applies no layout, however the URI spells
    /// `dry_run=false`.
    ///
    /// The guard read the URI as the script wrote it and the resource reads
    /// it percent-decoded, so `dry_run%3Dfalse` passed the one and applied
    /// through the other, with the script's own `dry_run` at its default.
    ///
    /// # Panics
    ///
    /// When the escaped form is not refused, or the overlay changed.
    #[test]
    fn a_script_applies_no_layout_through_an_escaped_query() {
        use crate::params::ScriptParams;
        let server = crate::testing::code_server(
            borer_engine::program::Arch::X86_64,
            &[
                0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
                0xc3, // ASM: ret
            ],
        );
        let before = crate::state::read_lock(&server.overlay).fingerprint();
        let out = crate::testing::call(
            borer_front::tools::script,
            &server,
            &ScriptParams {
                code: r#"print(query("borer://layout/0x1000,apply=Rec,dry_run%3Dfalse"));"#
                    .to_owned(),
                dry_run: None,
            },
        )
        .expect("a script answers");
        assert!(out.contains("applies nothing through query"), "{out}");
        assert_eq!(
            crate::state::read_lock(&server.overlay).fingerprint(),
            before,
            "{out}"
        );
    }

    /// A script lands nothing on a program `load_binary` put in place of the
    /// one it ran over.
    ///
    /// The script reads the program it found loaded, outside the program's
    /// lock, and applies what it proposed after it ends; names it found on
    /// one build must not land at the same addresses of the next one,
    /// where other code sits.
    ///
    /// The threads meet through the server's own locks, never a clock. The
    /// test holds the overlay's write lock, so the script, once it holds the
    /// first program (its count of holders rises), waits to snapshot the
    /// overlay; the second load then takes the program's write lock and
    /// waits for the overlay too. Letting go of the overlay lets both on:
    /// the script's run ends whichever goes first, and its edit reads the
    /// program after the load has put the second one in place.
    ///
    /// # Panics
    ///
    /// When the new program's overlay holds the script's name.
    #[test]
    fn a_script_lands_nothing_on_a_program_loaded_while_it_ran() {
        use crate::params::ScriptParams;
        use crate::testing::load_raw;
        let dir = std::env::temp_dir().join(format!("borer-script-swap-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        let (one, two) = (dir.join("one.bin"), dir.join("two.bin"));
        std::fs::write(&one, [0xc3; 16]).expect("written");
        std::fs::write(&two, [0x90; 16]).expect("written");
        let server = crate::BorerServer::default();
        let load = |path: &std::path::Path| load_raw(&server, path, "0x10000");
        load(&one).expect("the first program loads");
        let first = server
            .require_loaded()
            .expect("the first program is loaded");
        let holders = std::sync::Arc::strong_count(&first);
        let held = crate::state::write_lock(&server.overlay);
        std::thread::scope(|s| {
            let ran = s.spawn(|| {
                crate::testing::call(
                    borer_front::tools::script,
                    &server,
                    &ScriptParams {
                        code: r#"rename(0x10000, "from_one");"#.to_owned(),
                        dry_run: Some(false),
                    },
                )
            });
            while std::sync::Arc::strong_count(&first) <= holders && !ran.is_finished() {
                std::thread::yield_now();
            }
            let loads = s.spawn(|| load(&two));
            while server.program.try_read().is_ok() && !loads.is_finished() {
                std::thread::yield_now();
            }
            drop(held);
            loads
                .join()
                .expect("the load ends")
                .expect("the second program loads");
            let said = ran.join().expect("the script ends").expect("it answers");
            assert!(said.contains("from_one"), "{said}");
            assert!(said.contains("no longer the loaded binary"), "{said}");
        });
        let names = crate::state::read_lock(&server.overlay).names.clone();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert!(
            names.is_empty(),
            "a name the script found on the first program landed on the second: {names:?}"
        );
    }

    /// A script's `help("query")` lists every template with an example
    /// built from the loaded binary, and `rows` reads a page of a listing
    /// as maps.
    ///
    /// # Panics
    ///
    /// When a template is missing, its example is not filled in, or the
    /// rows differ.
    #[test]
    fn a_script_reads_every_resource_by_help_and_tables_by_rows() {
        use crate::params::ScriptParams;
        let server = raw_server();
        let out = crate::testing::call(
            borer_front::tools::script,
            &server,
            &ScriptParams {
                code: r#"print(help("query"));
                         let r = rows("borer://help!offset=1!limit=2");
                         print(`${r.len} ${r[0].text}`);"#
                    .to_owned(),
                dry_run: None,
            },
        )
        .expect("a script answers");
        for &(uri, _, _) in borer_engine::answer::catalog::RESOURCE_TEMPLATES {
            assert!(out.contains(&format!("\n{uri}\t")), "{uri}: {out}");
        }
        assert!(
            out.contains("\te.g. borer://emulate/0x1000,a1=5,steps=10000\n"),
            "{out}"
        );
        assert!(out.contains("\n2 borer://info\t"), "{out}");
    }

    /// `query` answers a URI exactly as `resources/read` does.
    ///
    /// Both go through one answer memory: a URI without a tag is whole with
    /// its tag line every time, however often it was read before (a reader
    /// may no longer hold it); the URI with that tag appended is a note
    /// naming the read that returns the text, whichever way it is read;
    /// `!fresh` after the tag is whole again, and a tag that is not one is
    /// refused. An unknown URI is the same refusal both ways, listing every
    /// resource there is. The evidence line, the answer's last, names the
    /// emission and so differs between two reads of one answer; these
    /// assertions compare with it taken off.
    ///
    /// # Panics
    ///
    /// When the two ways answer differently, a repeat without a tag is not
    /// the whole text, or the note does not name the read returning it.
    #[test]
    fn query_answers_a_uri_as_resources_read_does() {
        use crate::params::QueryParams;
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![0x90; 0x200];
        code.push(0xc3);
        let text = Section::mapped(".text", 0x1000, 0, 0x201, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let query = |uri: &str| {
            borer_front::tools::query(
                &server,
                &QueryParams {
                    uri: uri.to_owned(),
                },
            )
            .map_err(crate::errors::failed)
        };
        let uri = "borer://disasm/0x1000";
        let (read_as, whole) = server.read_uri(uri).expect("reads");
        assert_eq!(read_as, uri);
        assert!(whole.len() > 512, "long enough to be remembered: {whole}");
        assert_eq!(
            without_evidence(&query(uri).expect("reads")),
            without_evidence(&whole),
            "a repeat is whole but for its evidence line"
        );
        let tag = whole
            .lines()
            .find_map(|l| l.strip_prefix("# since="))
            .expect("a long answer carries its tag");
        let tagged = format!("{uri}!since={tag}");
        let note = query(&tagged).expect("reads");
        assert!(
            note.starts_with(&format!("# unchanged since the answer tagged {tag}: ")),
            "{note}"
        );
        assert!(
            without_evidence(&note)
                .ends_with("; this note stands in for that text, and reading borer://disasm/0x1000 (resources/read or the query tool) returns it in full\n"),
            "{note}"
        );
        let (read_as, noted) = server.read_uri(&tagged).expect("reads");
        assert_eq!(
            (read_as.as_str(), without_evidence(&noted)),
            (uri, without_evidence(&note)),
            "one memory for both ways"
        );
        assert_eq!(
            without_evidence(&query(&format!("{tagged}!fresh")).expect("reads")),
            without_evidence(&whole)
        );
        assert_eq!(
            without_evidence(&query(&format!("{uri}!fresh")).expect("reads")),
            without_evidence(&whole)
        );
        let bad = query(&format!("{uri}!since=zz")).expect_err("not a tag");
        assert_eq!(bad.code, rmcp::model::ErrorCode::INVALID_PARAMS);
        let refused = server.read_uri("borer://nope").expect_err("unknown");
        let queried = query("borer://nope").expect_err("unknown");
        assert_eq!(
            (refused.code, &refused.message),
            (queried.code, &queried.message)
        );
        assert!(
            refused
                .message
                .starts_with("unknown resource borer://nope; ")
                && refused
                    .message
                    .ends_with("; borer://help lists every resource"),
            "{}",
            refused.message
        );
    }
}
