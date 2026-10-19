//! The decompile tools and the paging, cutting and headers of the
//! pseudo-C they answer.

use std::fmt::Write as _;

use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::program::{Feature, Program};
use rayon::prelude::*;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::params::{DecompileBatchParams, DecompileParams, Detail, Filter, count_param, to_usize};

/// Lines of pseudo-C one `decompile` answer holds unless a limit says
/// otherwise.
pub(crate) const DECOMPILE_LINES_DEFAULT: usize = 300;

/// Narrows a decompiled function to the lines a caller asked for.
///
/// A function of a few thousand instructions renders to a few thousand lines, and an agent
/// that wants one call site pays for all of them. The filter is spelled the way the rest of
/// borer spells one - plain text, case-insensitive, no pattern language to get wrong.
///
/// A function that fits the page is returned untouched when nothing was asked for, so the
/// usual answer and its determinism are exactly what they were; one longer than
/// [`DECOMPILE_LINES_DEFAULT`] lines is paged unasked, since a 2,500-line function was 98 KB
/// in one answer. Once anything is asked for, or the page cuts, every line is numbered from
/// one, because a filtered line is worth little without the address of the window to ask
/// for next. A cut page's header names that window, `offset=N continues`, and an unfiltered
/// page that starts inside the declarations says the line they end on
/// ([`borer_engine::analysis::decompile::declarations_end`]): on optimized code the first
/// page can be mostly declarations, and the agent paged blind past them.
///
/// A filtered or paged line is shown under the signature and the `if`/`else`/loop/`switch`/
/// `case` headers enclosing it ([`render::scope_headers`]), each once, numbered `^N` so it
/// reads as context and not as a line the filter kept: most lines of a function run only
/// under a condition the line does not carry, and the bare line states it as unconditional.
///
/// A filter that statements carry leaves out the declaration lines it also hits, and the
/// header counts them: one declaration line names every local, so a filter for a `local_N`
/// repeated it in every answer. A filter only declarations carry keeps them.
///
/// # Arguments
///
/// * `text` - The decompiled function.
/// * `filter` - Keep only lines containing this text, case-insensitively.
/// * `offset` - Lines to skip, counted after filtering.
/// * `limit` - Most lines to return; absent is the default page, zero is every line.
///
/// # Returns
///
/// The chosen lines with their enclosing headers, numbered, under a header saying what was
/// shown of what.
pub(crate) fn window(
    text: &str,
    filter: Option<&str>,
    offset: Option<u32>,
    limit: Option<u32>,
) -> String {
    let take = match limit {
        None => DECOMPILE_LINES_DEFAULT,
        Some(0) => usize::MAX,
        Some(n) => to_usize(n),
    };
    let lines: Vec<&str> = text.lines().collect();
    let total = lines.len();
    if filter.is_none() && offset.is_none() && total <= take {
        return text.to_owned();
    }
    let needle = Filter::new(filter);
    let mut picked: Vec<usize> = (0..total).filter(|&i| needle.accepts(lines[i])).collect();
    let declared = borer_engine::analysis::decompile::declarations_end(text);
    let mut left_out = String::new();
    if let (Some(_), Some(end)) = (needle.needle(), declared) {
        let declaration = |i: usize| i < end && !lines[i].starts_with("//");
        let kept: Vec<usize> = picked
            .iter()
            .copied()
            .filter(|&i| !declaration(i))
            .collect();
        if !kept.is_empty() && kept.len() < picked.len() {
            left_out = format!(
                " ({} more in the declarations, offset=0 limit={end} without filter reads them)",
                picked.len() - kept.len()
            );
            picked = kept;
        }
    }
    let from = to_usize(offset.unwrap_or(0));
    let shown: Vec<usize> = picked.iter().skip(from).take(take).copied().collect();
    let context = render::scope_headers(&lines, &shown);
    let next = from + shown.len();
    let more = if next < picked.len() {
        format!("; offset={next} continues")
    } else {
        String::new()
    };
    let mut out = match needle.needle() {
        Some(n) => format!(
            "// {} of {total} lines carry {n:?}{left_out}, showing {} from {from}{more}",
            picked.len(),
            shown.len()
        ),
        None => {
            let declared = declared
                .filter(|&end| from < end)
                .map_or(String::new(), |end| {
                    format!("; declarations end at line {end}")
                });
            format!(
                "// showing {} of {total} lines from {from}{declared}{more}",
                shown.len()
            )
        }
    };
    if !context.is_empty() {
        out.push_str(render::SCOPE_NOTE);
    }
    out.push('\n');
    let mut rows = shown;
    rows.extend(&context);
    rows.sort_unstable();
    for i in rows {
        let number = if context.contains(&i) {
            format!("^{}", i + 1)
        } else {
            (i + 1).to_string()
        };
        let _ = writeln!(out, "{number:>5}  {}", lines[i]);
    }
    out
}

/// One function of a `decompile_batch` answer cut at its share: whole lines
/// up to `cap` bytes, then a note naming where `decompile` picks it up.
///
/// The note counts lines as `decompile` numbers them, its header lines
/// ([`decompile_header`]) included, so the offset it gives continues from
/// the last line shown; it also names the line the declarations end on,
/// since the share of a function with hundreds of locals can be all
/// declarations.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C, without the header lines.
/// * `cap` - Most bytes kept.
/// * `entry` - The function's entry.
/// * `header` - How many lines `decompile` puts under the text's first line.
///
/// # Returns
///
/// The kept lines and the note, ending in a newline.
pub(crate) fn truncated(text: &str, cap: usize, entry: u64, header: usize) -> String {
    let end = text[..text.floor_char_boundary(cap)]
        .rfind('\n')
        .map_or(0, |i| i + 1);
    let kept = &text[..end];
    let shift = |line: usize| if line > 1 { line + header } else { line };
    let shown = shift(kept.lines().count());
    let total = shift(text.lines().count());
    let declared = borer_engine::analysis::decompile::declarations_end(text)
        .map_or(String::new(), |end| {
            format!("; declarations end at line {}", shift(end))
        });
    format!(
        "{kept}// truncated at line {shown} of {total}{declared}; decompile(address={entry:#x}, offset={shown}) continues\n"
    )
}

/// Returns the lines a `decompile` answer puts under its first line.
///
/// They are what of the text was checked against the binary, the
/// `// warn:` line naming what is known wrong in the text
/// ([`borer_engine::analysis::decompile::warnings`]), then a `// next:`
/// line per resource the function's facts point at
/// ([`render::next_steps`]).
///
/// The check is read first, so the decompilation it memoizes keeps the
/// lifter's witness, and the text the answer shows reads the same cell.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis.
/// * `o` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The lines without a final newline, or `None` when there are none.
pub(crate) fn decompile_header(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
) -> Option<String> {
    use borer_engine::analysis::decompile;
    let mut lines: Vec<String> = decompile::checked_header(p, a, o, entry)
        .into_iter()
        .collect();
    lines.extend(
        decompile::decompile_named(p, a, o, entry)
            .and_then(|text| decompile::warnings(p, a, o, entry, &text)),
    );
    lines.extend(
        render::next_steps(p, a, o, entry)
            .iter()
            .map(|step| format!("// next: {step}")),
    );
    (!lines.is_empty()).then(|| lines.join("\n"))
}

#[tool_router(router = decompile_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Returns the pseudo-C of one function.
    ///
    /// `detail` is an enum: anything but `skeleton` used to fall through to
    /// the whole function, so a caller who misspelled it read a complete
    /// decompilation believing it was the outline and was never told
    /// otherwise. Every other choice of words in these tools refuses one it
    /// does not know.
    ///
    /// The answer's second line says what of it was checked against the
    /// binary ([`borer_engine::analysis::decompile::checked_header`]); only
    /// this rendering carries it, never the text other readers parse.
    ///
    /// # Arguments
    ///
    /// * `DecompileParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address is not inside a discovered function,
    /// or the decompiler produces nothing.
    #[tool(
        description = "Pseudo-C with locals local_N/arg_N (local_N is N hex bytes below the entry stack pointer: higher N, lower address), named calls and if/else/while/for/switch; /* asm */ marks unmodeled code, goto unproven flow. Line 2 says what the binary checked; a `// warn:` line names what is known wrong in the text (none: no check fired, not proof), `// next:` lines what to read next.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn decompile(
        &self,
        Parameters(DecompileParams {
            address,
            detail,
            filter,
            offset,
            limit,
        }): Parameters<DecompileParams>,
    ) -> Result<String, ErrorData> {
        use borer_engine::analysis::decompile;
        self.with_program(|p| {
            if let Some(why) = p.refuses(Feature::Decompile) {
                return Err(why);
            }
            let a = self.ensure_analysis()?;
            let entry = self.function_entry(p, &a, &address)?;
            let o = self.overlay();
            let header = decompile_header(p, &a, &o, entry);
            let text = decompile::decompile_named(p, &a, &o, entry)
                .ok_or_else(|| format!("decompilation failed at {entry:#x}"))?;
            let text = match detail.unwrap_or_default() {
                Detail::Full => text,
                Detail::Skeleton => decompile::skeleton(&text),
            };
            let text = decompile::with_header(&text, header.as_deref());
            Ok(window(&text, filter.as_deref(), offset, limit))
        })
    }

    /// Returns the pseudo-C of several functions, decompiled in parallel and
    /// emitted in discovery order.
    ///
    /// # Arguments
    ///
    /// * `DecompileBatchParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the analysis is unavailable.
    #[tool(
        description = "Pseudo-C for many functions: filter on name or entry hex, max_functions (10, max 50); 6000 chars per function, 40000 total; out=<file.c> writes every function there uncapped, leaves first.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn decompile_batch(
        &self,
        Parameters(DecompileBatchParams {
            filter,
            max_functions,
            out,
            library,
        }): Parameters<DecompileBatchParams>,
    ) -> Result<String, ErrorData> {
        if let Some(out) = out {
            if filter.is_some() || max_functions.is_some() {
                return Err(crate::errors::err_params(
                    "out writes every function; leave filter and max_functions out with it",
                ));
            }
            let library = if library.unwrap_or(false) {
                borer_engine::analysis::decompile::export::Library::Include
            } else {
                borer_engine::analysis::decompile::export::Library::Skip
            };
            return self.with_program(|p| {
                if let Some(why) = p.refuses(Feature::Decompile) {
                    return Err(why);
                }
                let a = self.ensure_analysis()?;
                let o = self.overlay();
                borer::export::write_c(p, &a, &o, library, &out)
                    .map(|w| w.line(&out))
                    .map_err(|e| format!("{e:#}"))
            });
        }
        /// Longest text kept per function.
        const PER_FN: usize = 6_000;
        /// Longest total output.
        const TOTAL: usize = 40_000;
        let cap = count_param(max_functions, 10, 50, "max_functions")?;
        let max = cap.n;
        let filter = Filter::new(filter.as_deref());
        self.with_program(|p| {
            if let Some(why) = p.refuses(Feature::Decompile) {
                return Err(why);
            }
            let a = self.ensure_analysis()?;
            let o = self.overlay();
            let matches = |f: &&borer_engine::analysis::Function| match filter.needle() {
                Some(q) => {
                    borer_engine::analysis::name_of(&a, &o, f.entry)
                        .to_lowercase()
                        .contains(q)
                        || format!("{:x}", f.entry).contains(q.strip_prefix("0x").unwrap_or(q))
                }
                None => true,
            };
            let all: Vec<u64> = a
                .functions
                .iter()
                .filter(matches)
                .map(|f| f.entry)
                .collect();
            let total_matching = all.len();
            let classes: Vec<(u64, Vec<u64>)> =
                a.dedupe_clones(&all).into_iter().take(max).collect();
            let matched: Vec<u64> = classes.iter().map(|(e, _)| *e).collect();
            let skipped: std::collections::BTreeMap<u64, Vec<u64>> = classes.into_iter().collect();
            let texts: Vec<(u64, String)> = matched
                .par_iter()
                .map(|&entry| {
                    (
                        entry,
                        borer_engine::analysis::decompile::decompile_named(p, &a, &o, entry)
                            .unwrap_or_else(|| format!("// decompilation failed at {entry:#x}")),
                    )
                })
                .collect();
            let mut spent = 0usize;
            let printed = texts
                .iter()
                .take_while(|(_, text)| {
                    let room = spent < TOTAL;
                    spent += text.len().min(PER_FN);
                    room
                })
                .count();
            let headers: std::collections::BTreeMap<u64, usize> = texts[..printed]
                .par_iter()
                .filter(|(_, text)| text.len() > PER_FN)
                .map(|(entry, _)| {
                    let lines = decompile_header(p, &a, &o, *entry).map_or(0, |h| h.lines().count());
                    (*entry, lines)
                })
                .collect();
            let mut body = String::new();
            let (mut shown, mut folded) = (0usize, 0usize);
            for (entry, text) in &texts[..printed] {
                let name = borer_engine::analysis::name_of(&a, &o, *entry);
                let same = skipped.get(entry).filter(|c| !c.is_empty());
                let clones = same.map_or(String::new(), |c| {
                    let named: Vec<String> = c
                        .iter()
                        .take(6)
                        .map(|e| borer_engine::analysis::name_of(&a, &o, *e))
                        .collect();
                    let more = c.len().saturating_sub(6);
                    if more > 0 {
                        format!(" (same code: {}, +{more} more)", named.join(", "))
                    } else {
                        format!(" (same code: {})", named.join(", "))
                    }
                });
                let _ = write!(body, "
==== {name} @ {entry:#x} ===={clones}
");
                if text.len() > PER_FN {
                    body.push_str(&truncated(
                        text,
                        PER_FN,
                        *entry,
                        headers.get(entry).copied().unwrap_or(0),
                    ));
                } else {
                    body.push_str(text);
                }
                shown += 1;
                folded += same.map_or(0, Vec::len);
            }
            let mut out = format!(
                "# decompiled {shown} of {total_matching} matching functions (max {max}){}
",
                if folded > 0 {
                    format!("; {folded} more are clones of these")
                } else {
                    String::new()
                }
            );
            out.push_str(&body);
            let cut = texts.len().saturating_sub(shown);
            if let Some((first, _)) = texts.get(shown) {
                let _ = writeln!(
                    out,
                    "# total output cap of {TOTAL} chars reached: {cut} more decompiled, not shown, the first {} @ {first:#x}; narrow the filter or lower max_functions",
                    borer_engine::analysis::name_of(&a, &o, *first)
                );
            }
            Ok(out)
        })
        .map(|text| cap.noted(text))
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::raw_server;

    /// Asking for nothing returns a function that fits the page exactly as
    /// it was.
    ///
    /// The usual answer is what every existing caller and the determinism contract
    /// depend on, so the window is only opened on request or when the page cuts.
    ///
    /// # Panics
    ///
    /// When a decompile nobody narrowed comes back changed.
    #[test]
    fn a_decompile_nobody_narrowed_is_returned_whole() {
        let text = "// head\nint main() {\n  return 0;\n}\n";
        assert_eq!(super::window(text, None, None, None), text);
    }

    /// A function longer than the page is paged unasked, and `limit=0`
    /// asks for every line.
    ///
    /// # Panics
    ///
    /// When a long function comes back whole by default, or cut at zero.
    #[test]
    fn a_long_decompile_is_paged_by_default_and_zero_means_all() {
        let long: String = (0..super::DECOMPILE_LINES_DEFAULT + 1)
            .map(|i| format!("line {i}\n"))
            .collect();
        let paged = super::window(&long, None, None, None);
        let head = format!(
            "// showing {} of {} lines from 0; offset={} continues\n",
            super::DECOMPILE_LINES_DEFAULT,
            super::DECOMPILE_LINES_DEFAULT + 1,
            super::DECOMPILE_LINES_DEFAULT
        );
        assert!(paged.starts_with(&head), "{paged}");
        assert_eq!(paged.lines().count(), super::DECOMPILE_LINES_DEFAULT + 1);
        assert_eq!(super::window(&long, None, None, Some(0)), long);
    }

    /// A cut page names the line the declarations end on while it starts
    /// inside them, and the offset the next page starts at while one is
    /// left; the last page names neither.
    ///
    /// # Panics
    ///
    /// When a header misnames the declarations or the next offset.
    #[test]
    fn a_cut_page_names_where_the_declarations_end_and_what_comes_next() {
        let text: String = ["// f @ 0x1000\n// signature: void f(void)\n".to_owned()]
            .into_iter()
            .chain((0..400).map(|i| format!("uint64_t local_{i};\n")))
            .chain(std::iter::once("\n".to_owned()))
            .chain((0..600).map(|i| format!("x = {i};\n")))
            .collect();
        let head = |offset| {
            super::window(&text, None, offset, None)
                .lines()
                .next()
                .unwrap_or_default()
                .to_owned()
        };
        assert_eq!(
            head(None),
            "// showing 300 of 1003 lines from 0; declarations end at line 402; offset=300 continues"
        );
        assert_eq!(
            head(Some(300)),
            "// showing 300 of 1003 lines from 300; declarations end at line 402; offset=600 continues"
        );
        assert_eq!(
            head(Some(500)),
            "// showing 300 of 1003 lines from 500; offset=800 continues"
        );
        assert_eq!(head(Some(900)), "// showing 103 of 1003 lines from 900");
        let filtered = super::window(&text, Some("x = 1"), None, Some(5));
        assert!(
            filtered.starts_with(
                "// 111 of 1003 lines carry \"x = 1\", showing 5 from 0; offset=5 continues\n"
            ),
            "{filtered}"
        );
    }

    /// A batch with `out` writes every function to a C file whole, past the
    /// share a batch answer cuts at, and refuses a filter beside it.
    ///
    /// # Panics
    ///
    /// When the file is cut or the filter is taken.
    #[test]
    fn a_batch_with_out_writes_the_whole_function_to_a_file() {
        use crate::params::DecompileBatchParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut code = Vec::new();
        for n in 0u32..400 {
            // ASM: mov dword [rcx + n*8], n
            code.extend_from_slice(&[0xc7, 0x81]);
            code.extend_from_slice(&(n * 8).to_le_bytes());
            code.extend_from_slice(&n.to_le_bytes());
        }
        code.push(0xc3); // ASM: ret
        let len = u64::try_from(code.len()).expect("small");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let dir = std::env::temp_dir().join(format!("borer-batch-out-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("all.c").display().to_string();
        let batch = |filter: Option<&str>| {
            server.decompile_batch(Parameters(DecompileBatchParams {
                filter: filter.map(str::to_owned),
                max_functions: None,
                out: Some(out.clone()),
                library: None,
            }))
        };
        let refused = batch(Some("sub")).expect_err("a filter with out");
        let said = batch(None).expect("writes");
        let c = std::fs::read_to_string(&out).expect("reads");
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert!(refused.message.contains("leave filter"), "{refused:?}");
        assert!(said.starts_with("wrote 1 functions to "), "{said}");
        assert!(
            c.contains("= 399;") || c.contains("= 0x18f;"),
            "the last store is written: {c}"
        );
        assert!(!c.contains("// truncated"), "{c}");
    }

    /// A function a batch cuts at its share ends with a note whose offset,
    /// passed to `decompile`, picks it up at the line after the last one
    /// the batch shows, counted as `decompile` numbers its lines.
    ///
    /// # Panics
    ///
    /// When the note is missing or its offset skips or repeats a line.
    #[test]
    fn a_cut_batch_function_says_where_decompile_continues() {
        use crate::params::DecompileBatchParams;
        use crate::params::DecompileParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut code = Vec::new();
        for n in 0u32..400 {
            // ASM: mov dword [rcx + n*8], n
            code.extend_from_slice(&[0xc7, 0x81]);
            code.extend_from_slice(&(n * 8).to_le_bytes());
            code.extend_from_slice(&n.to_le_bytes());
        }
        code.push(0xc3); // ASM: ret
        let len = u64::try_from(code.len()).expect("small");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let batch = server
            .decompile_batch(Parameters(DecompileBatchParams {
                filter: None,
                max_functions: Some(1),
                out: None,
                library: None,
            }))
            .expect("batch");
        let note = batch
            .lines()
            .find(|l| l.starts_with("// truncated at line "))
            .unwrap_or_else(|| panic!("no cut note: {batch}"));
        let offset: u32 = note
            .split_once("offset=")
            .and_then(|(_, rest)| rest.split(')').next())
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no offset: {note}"));
        assert!(
            note.ends_with(&format!(
                "; decompile(address=0x1000, offset={offset}) continues"
            )),
            "{note}"
        );
        let decompile = |offset, limit| {
            server
                .decompile(Parameters(DecompileParams {
                    address: "0x1000".to_owned(),
                    detail: None,
                    filter: None,
                    offset,
                    limit: Some(limit),
                }))
                .expect("decompiles")
        };
        let whole = decompile(None, 0);
        let lines: Vec<&str> = whole.lines().collect();
        let at = usize::try_from(offset).expect("small");
        let kept: Vec<&str> = batch.lines().take_while(|l| *l != note).collect();
        assert_eq!(kept.last().copied(), lines.get(at - 1).copied(), "{batch}");
        let page = decompile(Some(offset), 1);
        let first = page
            .lines()
            .find(|l| !l.starts_with("//") && !l.trim_start().starts_with('^'))
            .unwrap_or_default();
        assert_eq!(
            first,
            format!(
                "{:>5}  {}",
                at + 1,
                lines.get(at).copied().unwrap_or_default()
            ),
            "{page}"
        );
    }

    /// A filter keeps the lines carrying the text, numbered where they were.
    ///
    /// The number is the point: a filtered line is worth little without the window to
    /// ask for next.
    ///
    /// # Panics
    ///
    /// When a carried line is dropped, renumbered, or a bystander kept.
    #[test]
    fn a_filter_keeps_the_lines_that_carry_it_with_their_own_numbers() {
        let text = "one\ntwo\nthree\ntwo again\n";
        let out = super::window(text, Some("two"), None, None);
        assert!(out.starts_with("// 2 of 4 lines carry"), "{out}");
        assert!(out.contains("    2  two\n"), "{out}");
        assert!(out.contains("    4  two again\n"), "{out}");
        assert!(!out.contains("three"), "{out}");
    }

    /// The filter ignores case, as every other filter in this tool does.
    ///
    /// # Panics
    ///
    /// When a line is kept only on an exact-case match.
    #[test]
    fn a_filter_ignores_case() {
        let out = super::window("Alpha\nbeta\n", Some("ALPHA"), None, None);
        assert!(out.contains("    1  Alpha\n"), "{out}");
    }

    /// Offset and limit page the answer, counting after the filter.
    ///
    /// # Panics
    ///
    /// When the window falls outside what was asked for.
    #[test]
    fn offset_and_limit_page_what_the_filter_left() {
        let text = "a\nb\nc\nd\n";
        let out = super::window(text, None, Some(1), Some(2));
        assert!(out.contains("    2  b\n"), "{out}");
        assert!(out.contains("    3  c\n"), "{out}");
        assert!(!out.contains("    1  a\n"), "{out}");
        assert!(!out.contains("    4  d\n"), "{out}");
    }

    /// A filter leaves out the declaration lines that also carry it, and
    /// says how many and how to read them.
    ///
    /// The one line declaring every local names each of them, so on
    /// optimized code it carried every filter for a `local_N` and repeated
    /// a few hundred bytes in each answer. A filter only the declarations
    /// carry still finds them.
    ///
    /// # Panics
    ///
    /// When a declaration line is kept beside statement hits, the count is
    /// missing, or a declaration-only hit is dropped.
    #[test]
    fn a_filter_leaves_out_declarations_beside_statement_hits() {
        let text = "// f @ 0x1000\n// signature: void f(void)\nuint64_t rax, rcx, local_58, local_60;\nchar *p;\n\nlocal_58 = 1;\nreturn local_58;\n";
        let out = super::window(text, Some("local_58"), None, None);
        assert!(!out.contains("uint64_t"), "{out}");
        assert!(out.contains("    6  local_58 = 1;\n"), "{out}");
        assert!(
            out.starts_with("// 2 of 7 lines carry \"local_58\" (1 more in the declarations, offset=0 limit=4 without filter reads them)"),
            "{out}"
        );
        let only = super::window(text, Some("char *"), None, None);
        assert!(only.contains("    4  char *p;\n"), "{only}");
    }

    /// The `decompile` description says which way the stack slots run.
    ///
    /// `local_58` is 0x58 bytes below the stack pointer at entry, so
    /// `local_60` sits below it; agents read the number as an offset upward
    /// and ordered a structure's fields backwards.
    ///
    /// # Panics
    ///
    /// When the description does not say it.
    #[test]
    fn decompile_says_which_way_stack_slots_run() {
        let tools = crate::BorerServer::tool_router().list_all();
        let said = tools
            .iter()
            .find(|t| t.name == "decompile")
            .and_then(|t| t.description.as_deref())
            .unwrap_or_default();
        assert!(said.contains("higher N, lower address"), "{said}");
    }

    /// A filter nothing carries says so rather than returning the whole text.
    ///
    /// # Panics
    ///
    /// When an empty answer is spelled as the whole function.
    #[test]
    fn a_filter_that_matches_nothing_returns_no_lines() {
        let out = super::window("a\nb\n", Some("zzz"), None, None);
        assert!(out.starts_with("// 0 of 2 lines carry"), "{out}");
        assert_eq!(out.lines().count(), 1, "{out}");
    }

    /// A filtered or paged line comes under the headers of the scopes
    /// enclosing it.
    ///
    /// Each header comes once, numbered `^N` and indented as in the text,
    /// and the header line says what `^N` means; a line no scope encloses
    /// comes alone, under the header it always had.
    ///
    /// A bare `rax = DeleteFileA(...)` reads as "always deletes"; under its
    /// `if` it reads as what it is.
    ///
    /// # Panics
    ///
    /// When a header is missing, a context line is numbered as a match, or
    /// an unnested line gains context.
    #[test]
    fn a_fragment_comes_with_the_headers_enclosing_it() {
        let text = "// f\n\nif ((a3 & 0x200) != 0) {\n  while (1) {\n    rax = DeleteFileA(a2);\n    rbx = DeleteFileA(a1);\n  }\n} else {\n  rax = 0;\n}\nreturn rax;\n";
        let note = borer_engine::analysis::render::SCOPE_NOTE;
        assert_eq!(
            super::window(text, Some("deletefilea"), None, None),
            format!(
                "// 2 of 11 lines carry \"deletefilea\", showing 2 from 0{note}\n   ^3  if ((a3 & 0x200) != 0) {{\n   ^4    while (1) {{\n    5      rax = DeleteFileA(a2);\n    6      rbx = DeleteFileA(a1);\n"
            )
        );
        assert_eq!(
            super::window(text, None, Some(8), Some(1)),
            format!(
                "// showing 1 of 11 lines from 8; offset=9 continues{note}\n   ^3  if ((a3 & 0x200) != 0) {{\n   ^8  }} else {{\n    9    rax = 0;\n"
            ),
            "a page opening inside an else"
        );
        assert_eq!(
            super::window(text, Some("return"), None, None),
            "// 1 of 11 lines carry \"return\", showing 1 from 0\n   11  return rax;\n"
        );
    }

    /// The `decompile` answer says on its second line what of it was
    /// checked against the binary, and the outline does too; the batch and
    /// the text the other tools read do not carry the line.
    ///
    /// # Panics
    ///
    /// When the line is missing from the answer or found anywhere else.
    #[test]
    fn a_decompile_answer_says_what_was_checked() {
        use crate::params::DecompileBatchParams;
        use crate::params::DecompileParams;
        use crate::params::Detail;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        let answer = |detail| {
            server
                .decompile(Parameters(DecompileParams {
                    address: "0x1000".to_owned(),
                    detail,
                    filter: None,
                    offset: None,
                    limit: Some(0),
                }))
                .expect("decompiles")
        };
        for detail in [None, Some(Detail::Skeleton)] {
            let text = answer(detail);
            let line = text.lines().nth(1).unwrap_or_default();
            assert!(
                line.starts_with("// checked vs binary: statements as emitted, 1/1 blocks"),
                "{text}"
            );
            assert!(
                text.lines().next().is_some_and(|l| l.contains("0x1000")),
                "{text}"
            );
        }
        let batch = server
            .decompile_batch(Parameters(DecompileBatchParams {
                filter: None,
                max_functions: Some(1),
                out: None,
                library: None,
            }))
            .expect("batch");
        assert!(!batch.contains("checked vs binary"), "{batch}");
        let a = server
            .analysis(borer_engine::program::Feature::Decompile)
            .expect("analyzed");
        let plain = server
            .with_program(|p| {
                borer_engine::analysis::decompile::decompile_named(p, &a, &server.overlay(), 0x1000)
                    .ok_or_else(|| "no text".to_owned())
            })
            .expect("text");
        assert!(!plain.contains("checked vs binary"), "{plain}");
    }

    /// The `decompile` answer lists, under the line saying what was
    /// checked, a `// next:` line per resource the function's facts point
    /// at, and the summary ends with the same steps as `# next:` lines.
    ///
    /// # Panics
    ///
    /// When a step is missing from either answer.
    #[test]
    fn a_decompile_answer_names_the_next_reads() {
        use crate::params::DecompileParams;
        use crate::params::FunctionParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut code = vec![
            0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
            0x0f, 0x94, 0xc0, // ASM: sete al
            0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
            0xc3, // ASM: ret
        ];
        code.resize(0x10, 0xcc);
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let step = "borer://solve/0x1000 (compares against 0x1337abcd: solve tries it as a1)";
        let answer = server
            .decompile(Parameters(DecompileParams {
                address: "0x1000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: Some(0),
            }))
            .expect("decompiles");
        let lines: Vec<&str> = answer.lines().collect();
        assert!(
            lines
                .get(1)
                .is_some_and(|l| l.starts_with("// checked vs binary")),
            "{answer}"
        );
        assert_eq!(
            lines.get(2).copied(),
            Some(format!("// next: {step}").as_str()),
            "{answer}"
        );
        let summary = server
            .function_summary(Parameters(FunctionParams {
                address: "0x1000".to_owned(),
            }))
            .expect("summarizes");
        assert!(summary.ends_with(&format!("# next: {step}\n")), "{summary}");
    }

    /// The `decompile` answer names, on a `// warn:` line under the check
    /// line, a call to a function of the binary the text gives no
    /// prototype; the callee's own text, which calls nothing, has no such
    /// line. The callee's name is one C reserves for the implementation,
    /// which the translation-unit closure leaves undeclared.
    ///
    /// # Panics
    ///
    /// When the warning is missing from the caller's answer or found in
    /// the callee's.
    #[test]
    fn a_decompile_answer_warns_of_a_callee_with_no_prototype() {
        use crate::params::DecompileParams;
        use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};
        use rmcp::handler::server::wrapper::Parameters;
        let mut code = vec![
            0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
            0xc3, // ASM: ret
        ];
        code.resize(0x10, 0xcc);
        code.extend([
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
        ]);
        code.resize(0x20, 0xcc);
        let text = Section::mapped(".text", 0x1000, 0, 0x20, false, true);
        let mut program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        program.symbols = vec![Symbol {
            name: "_callee".to_owned(),
            addr: 0x1010,
            kind: SymbolKind::Local,
        }];
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let answer = |address: &str| {
            server
                .decompile(Parameters(DecompileParams {
                    address: address.to_owned(),
                    detail: None,
                    filter: None,
                    offset: None,
                    limit: Some(0),
                }))
                .expect("decompiles")
        };
        let caller = answer("0x1000");
        let lines: Vec<&str> = caller.lines().collect();
        assert!(
            lines
                .get(1)
                .is_some_and(|l| l.starts_with("// checked vs binary")),
            "{caller}"
        );
        assert_eq!(
            lines.get(2).copied(),
            Some(
                "// warn: callee _callee: no prototype in the text, so arguments and result are guesses"
            ),
            "{caller}"
        );
        assert!(!answer("0x1010").contains("// warn:"), "{caller}");
    }

    /// The `decompile` answer leaves a line that reads a register no line
    /// sets as the text writes it: such a read is as often harmless as not,
    /// so it is no mark.
    ///
    /// # Panics
    ///
    /// When the answer marks the line.
    #[test]
    fn a_decompile_answer_does_not_mark_an_unset_read() {
        use crate::params::DecompileParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut code = vec![
            0x4c, 0x89, 0xd0, // ASM: mov rax, r10
            0xc3, // ASM: ret
        ];
        code.resize(0x10, 0xcc);
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let answer = server
            .decompile(Parameters(DecompileParams {
                address: "0x1000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: Some(0),
            }))
            .expect("decompiles");
        assert!(answer.contains("r10"), "{answer}");
        assert!(!answer.contains("!unset"), "{answer}");
    }

    /// A batch the total output cap cuts short counts in its header the
    /// functions it prints, not the ones it decompiled and left out, and
    /// says how many those are.
    ///
    /// The image's entry calls twelve functions of 150 stores each, whose
    /// texts run past the total long before the twelfth.
    ///
    /// # Panics
    ///
    /// When the header counts a function the body does not print.
    #[test]
    fn a_batch_cut_by_the_total_cap_counts_what_it_prints() {
        use crate::params::DecompileBatchParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        /// Functions the entry calls.
        const CALLEES: u32 = 12;
        /// Bytes between two callees.
        const STRIDE: u32 = 0x800;
        let mut code = Vec::new();
        for k in 0..CALLEES {
            let at = u32::try_from(code.len()).expect("small") + 5;
            // ASM: call 0x1000 + STRIDE * (k + 1)
            code.push(0xe8);
            code.extend_from_slice(&(STRIDE * (k + 1) - at).to_le_bytes());
        }
        code.push(0xc3); // ASM: ret
        for k in 0..CALLEES {
            code.resize(usize::try_from(STRIDE * (k + 1)).expect("small"), 0xcc);
            for n in 0u32..150 {
                // ASM: mov dword [rcx + n*8 + k], n
                code.extend_from_slice(&[0xc7, 0x81]);
                code.extend_from_slice(&(n * 8 + k).to_le_bytes());
                code.extend_from_slice(&n.to_le_bytes());
            }
            code.push(0xc3); // ASM: ret
        }
        let len = u64::try_from(code.len()).expect("small");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let batch = server
            .decompile_batch(Parameters(DecompileBatchParams {
                filter: None,
                max_functions: Some(50),
                out: None,
                library: None,
            }))
            .expect("batch");
        let printed = batch.lines().filter(|l| l.starts_with("==== ")).count();
        assert!(printed < 13, "the cap cuts the batch short: {batch}");
        let header = batch.lines().next().unwrap_or_default();
        assert_eq!(
            header,
            format!("# decompiled {printed} of 13 matching functions (max 50)"),
            "{batch}"
        );
        assert!(
            batch.contains(&format!(
                "# total output cap of 40000 chars reached: {} more decompiled, not shown",
                13 - printed
            )),
            "{batch}"
        );
    }
}
