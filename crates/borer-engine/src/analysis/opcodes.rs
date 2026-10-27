//! Opcode protocols: a dispatcher that reads an opcode off a stream and
//! switches on it, and senders that write a constant opcode first and
//! then the fields through the same writer.
//!
//! A protocol of the class-per-message kind is read from its vtables
//! ([`super::protocol`]). Many older programs have no class per message:
//! one function reads a byte or a word off the packet and `switch`es on
//! it, through a jump table or a tree of compares (which the decompiler
//! folds into a `switch` as well), to a handler that reads on from the same
//! stream. Outbound, a function hands its writer the opcode as a constant
//! and then its fields. Both are read from pseudo-C: the dispatcher's
//! `switch`, the read that set its value, and each case's call handing the
//! stream on, whose record is the handler's [`schema_of`]; a sender's
//! first write and the rest of its writes, read by [`encoding_through`].

use std::fmt::Write as _;

use super::encode::{Encoding, compact_writes, encoding_through, literal};
use super::schema::{
    Call, Field, calls_in_order, compact_fields, declared_names, ident_char, is_call_of, reads_in,
    returned_bytes, schema_of, signature_line,
};
use super::{Analysis, Overlay, RefKind, name_of, plain_text_cached, resolve};
use crate::program::Program;

/// Lines searched back from a `switch` for the read that set its value.
const READ_BACK: usize = 40;
/// Plain copies followed back from the switched value to its read.
const HOPS_MAX: usize = 4;
/// Most functions decompiled by one search for dispatchers or senders.
const SCAN_MAX: usize = 4000;
/// Fewest functions worth a worker each when a search decompiles them.
const PAR_MIN: usize = 8;
/// Fewest cases that read on from the stream before a switch found by a
/// search counts as a dispatcher; one given by the caller needs one.
const HANDLED_MIN: usize = 2;
/// Fewest two-way blocks a function without a jump table needs before a
/// search reads it as a possible compare tree.
const FORKS_MIN: usize = 3;

/// How a dispatcher picks its case.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Route {
    /// An indirect jump through a table of case addresses.
    Table {
        /// The jump's address.
        site: u64,
        /// The table's entries.
        entries: usize,
    },
    /// No jump table in the function: compares the decompiler folded into
    /// a `switch`.
    Compare,
    /// Jump tables and switches the text does not tie one to one: which
    /// table, if any, picks this switch's case is not known.
    Untied {
        /// Jump tables in the function.
        tables: usize,
        /// Switches in its text.
        switches: usize,
    },
}

/// One case of a dispatcher.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Case {
    /// The case labels as the text spells them: `16`, `default`.
    pub labels: Vec<String>,
    /// The handler the case hands the stream to, when it calls exactly
    /// one function with it and that function reads a record.
    pub handler: Option<u64>,
    /// The record read: the handler's schema, or the reads the case makes
    /// itself off the stream.
    pub fields: Vec<Field>,
}

/// A function that reads an opcode off a stream and switches on it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dispatch {
    /// The function.
    pub entry: u64,
    /// The stream's identifier in its text.
    pub stream: String,
    /// The switched variable.
    pub opcode: String,
    /// The opcode's kind as its reader stores or returns it: a call that
    /// does neither at a known width is not a read, and its switch no
    /// dispatcher.
    pub kind: String,
    /// The reader as the text names it.
    pub reader: String,
    /// The first call to the reader in the function, when one was found.
    pub read_at: Option<u64>,
    /// The reader returns the opcode rather than storing it through an out
    /// pointer.
    pub returned: bool,
    /// How the case is picked.
    pub route: Route,
    /// The cases in text order.
    pub cases: Vec<Case>,
    /// Other switches in the function on a value read off a stream.
    pub other_switches: usize,
}

impl Case {
    /// Tells whether the case reads something off the stream that borer
    /// can size: a field of known kind or width, not only calls handed the
    /// stream that write nothing borer sees.
    #[must_use]
    pub fn reads(&self) -> bool {
        sized(&self.fields)
    }
}

impl Dispatch {
    /// Returns how many cases read something off the stream.
    #[must_use]
    pub fn handled(&self) -> usize {
        self.cases.iter().filter(|c| c.reads()).count()
    }
}

/// A function that writes a constant opcode first and then fields through
/// the same writer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpcodeSend {
    /// The function.
    pub entry: u64,
    /// The opcode it writes first, cut to the width its writer stores.
    pub opcode: u64,
    /// The writer it hands the opcode, as the text names it.
    pub writer: String,
    /// The first call to the writer in the function, when one was found.
    pub write_at: Option<u64>,
    /// What it writes, the opcode first and constants as written, at least
    /// one write after the opcode of a known kind.
    pub encoding: Encoding,
}

/// Tells whether `s` is one identifier.
///
/// # Arguments
///
/// * `s` - The text.
fn is_ident(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && s.chars().all(ident_char)
}

/// Strips leading casts: `(uint8_t)local_c` is `local_c`.
///
/// # Arguments
///
/// * `s` - The expression.
fn strip_casts(mut s: &str) -> &str {
    while let Some(rest) = s.strip_prefix('(')
        && let Some(close) = rest.find(')')
        && let ty = rest[..close].trim()
        && (ty.ends_with("_t") || ty.ends_with('*') || ty == "char" || ty == "int")
    {
        s = rest[close + 1..].trim_start();
    }
    s.trim()
}

/// Returns the net braces a line opens, outside string and character
/// literals.
///
/// # Arguments
///
/// * `t` - The line.
fn braces(t: &str) -> i32 {
    let mut quote = None;
    let mut escaped = false;
    let mut n = 0;
    for c in t.chars() {
        match (quote, c) {
            (Some(_), '\\') if !escaped => {
                escaped = true;
                continue;
            }
            (Some(q), c) if c == q && !escaped => quote = None,
            (None, '"' | '\'') => quote = Some(c),
            (None, '{') => n += 1,
            (None, '}') => n -= 1,
            _ => {}
        }
        escaped = false;
    }
    n
}

/// Returns the labels a case line opens and what follows them: `case 1:
/// case 2: {` is `1`, `2` and `{`; `case 3: break;` is `3` and `break;`.
///
/// A label ends at the first colon that is not half of a `::`, so an
/// enum member's qualified name stays whole.
///
/// # Arguments
///
/// * `t` - The trimmed line.
///
/// # Returns
///
/// The labels and the rest of the line, or `None` when the line opens no
/// case.
fn case_labels(t: &str) -> Option<(Vec<String>, &str)> {
    let mut labels = Vec::new();
    let mut rest = t.trim();
    loop {
        if let Some(r) = rest.strip_prefix("default:") {
            labels.push("default".to_owned());
            rest = r.trim_start();
        } else if let Some(r) = rest.strip_prefix("case ") {
            let bytes = r.as_bytes();
            let end = (0..bytes.len()).find(|&i| {
                bytes[i] == b':'
                    && bytes.get(i + 1) != Some(&b':')
                    && (i == 0 || bytes[i - 1] != b':')
            })?;
            labels.push(r[..end].trim().to_owned());
            rest = r[end + 1..].trim_start();
        } else {
            break;
        }
    }
    (!labels.is_empty()).then_some((labels, rest.trim_end()))
}

/// Returns the cases of the `switch` opening on line `at`, each with its
/// body lines.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `at` - The `switch` line's index.
fn cases_of<'l>(lines: &[&'l str], at: usize) -> Vec<(Vec<String>, Vec<&'l str>)> {
    let mut out: Vec<(Vec<String>, Vec<&str>)> = Vec::new();
    let mut depth = 0;
    for &t in lines.iter().skip(at + 1) {
        let after = depth + braces(t);
        if depth == 0 {
            if t.starts_with('}') {
                break;
            }
            match case_labels(t) {
                Some((labels, "" | "{")) => out.push((labels, Vec::new())),
                Some((labels, rest)) => out.push((labels, vec![rest])),
                None => {
                    if let Some((_, body)) = out.last_mut() {
                        body.push(t);
                    }
                }
            }
        } else if after > 0
            && let Some((_, body)) = out.last_mut()
        {
            body.push(t);
        }
        depth = after;
        if depth < 0 {
            break;
        }
    }
    out
}

/// Finds the read that set `var` before line `at`: a call handed `&var`
/// right after its stream, the out pointer [`reads_in`] sizes, or one whose result `var` is assigned, following
/// plain copies back.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `calls` - Its calls.
/// * `at` - The `switch` line's index.
/// * `var` - The switched variable.
///
/// # Returns
///
/// The read and whether it returns the value, or `None` when no read
/// sets it within [`READ_BACK`] lines.
fn opcode_read<'c>(
    lines: &[&str],
    calls: &'c [Call],
    mut at: usize,
    var: &str,
) -> Option<(&'c Call, bool)> {
    let mut var = var.to_owned();
    for _ in 0..HOPS_MAX {
        let out_arg = format!("&{var}");
        let assign = format!("{var} = ");
        let changes = |t: &str| {
            let lhs = t.split([' ', ';']).next().unwrap_or_default();
            let op = t[lhs.len()..]
                .trim_start()
                .split(' ')
                .next()
                .unwrap_or_default();
            let compound = op.len() >= 2 && op.ends_with('=') && op != "==";
            lhs.trim_start_matches(['+', '-'])
                .trim_end_matches(['+', '-'])
                == var
                && (compound || op == "=" || lhs != var)
        };
        let i = (at.saturating_sub(READ_BACK)..at).rev().find(|&i| {
            changes(lines[i])
                || calls
                    .iter()
                    .any(|c| c.line == i + 1 && c.args.contains(&out_arg))
        })?;
        let on_line = |c: &&Call| c.line == i + 1;
        if let Some(c) = calls
            .iter()
            .filter(on_line)
            .find(|c| c.args.contains(&out_arg))
        {
            return (c.args.get(1) == Some(&out_arg)).then_some((c, false));
        }
        if !lines[i].starts_with(&assign) {
            return None;
        }
        let rhs = strip_casts(lines[i][assign.len()..].trim_end_matches(';'));
        if is_ident(rhs) {
            rhs.clone_into(&mut var);
            at = i;
            continue;
        }
        return calls
            .iter()
            .filter(on_line)
            .find(|c| is_call_of(rhs, &c.callee))
            .map(|c| (c, true));
    }
    None
}

/// Returns the first call site in `entry` that calls the function `callee`
/// names.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The calling function.
/// * `callee` - The callee as the text names it.
fn first_call(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    callee: &str,
) -> Option<u64> {
    let target = resolve(program, analysis, overlay, callee).ok()?;
    analysis
        .refs_from(entry)
        .into_iter()
        .filter(|(t, s)| *t == target && s.kind == RefKind::Call)
        .map(|(_, s)| s.va)
        .min()
}

/// Tells whether a record holds a read borer can size: a field of known
/// kind or width, not only calls handed the stream that write nothing
/// borer sees.
///
/// # Arguments
///
/// * `fields` - The record.
fn sized(fields: &[Field]) -> bool {
    fields.iter().any(|f| f.bytes > 0 || f.kind != "?")
}

/// Returns a handler's record as its caller reads it: every top-level
/// field not repeated in the handler repeats under the loop around the
/// call.
///
/// # Arguments
///
/// * `fields` - The handler's record.
/// * `repeat` - The loop bound the call sits under, when it does.
fn repeated(mut fields: Vec<Field>, repeat: Option<&String>) -> Vec<Field> {
    for f in fields.iter_mut().filter(|f| f.repeat.is_none()) {
        f.repeat = repeat.cloned();
    }
    fields
}

/// Returns a handler's text and the parameter `call` hands it `stream` in.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `handler` - The handler's entry.
/// * `call` - The case's call of the handler.
/// * `stream` - The dispatcher's stream.
///
/// # Returns
///
/// `None` when the handler does not decompile or declares no parameter at
/// the stream's position.
fn handler_input(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    handler: u64,
    call: &Call,
    stream: &str,
) -> Option<(String, String)> {
    let text = plain_text_cached(program, analysis, overlay, overlay.fingerprint(), handler)?;
    let at = call.args.iter().position(|a| a == stream)?;
    let param = declared_names(signature_line(&text)?).into_iter().nth(at)?;
    Some((text, param))
}

/// Reads one case's record off the stream.
///
/// A case handing the stream to one handler has that handler's reads off
/// the parameter it receives the stream in; any other case has, in call
/// order, the reads it makes off the stream itself and those of each
/// function it hands the stream to in another argument.
///
/// The handler's record is its reads off that parameter, returned reads
/// included; failing those, its [`schema_of`] when that schema's stream is
/// the same parameter. A handler that reads only another input has no
/// record here.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `labels` - The case's labels.
/// * `body` - The case's lines.
/// * `stream` - The stream's identifier.
fn case_of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    labels: Vec<String>,
    body: &[&str],
    stream: &str,
) -> Case {
    let text = body.join("\n");
    let calls = calls_in_order(&text);
    let passing: Vec<&Call> = calls
        .iter()
        .filter(|c| !c.callee.starts_with("(*") && c.args.iter().any(|a| a == stream))
        .collect();
    if let [one] = passing.as_slice()
        && let Ok(handler) = resolve(program, analysis, overlay, &one.callee)
    {
        let input = handler_input(program, analysis, overlay, handler, one, stream);
        let direct = input.as_ref().map_or_else(Vec::new, |(text, param)| {
            reads_in(
                program,
                analysis,
                overlay,
                text,
                &calls_in_order(text),
                param,
            )
        });
        let schema = schema_of(program, analysis, overlay, handler).filter(|s| sized(&s.fields));
        if sized(&direct) || schema.is_some() {
            let fields = if sized(&direct) {
                direct
            } else {
                schema
                    .filter(|s| {
                        input
                            .as_ref()
                            .is_some_and(|(_, p)| s.stream.split(' ').next() == Some(p.as_str()))
                    })
                    .map(|s| s.fields)
                    .unwrap_or_default()
            };
            return Case {
                labels,
                handler: Some(handler),
                fields: repeated(fields, one.repeat.as_ref()),
            };
        }
    }
    let fields = passing
        .iter()
        .flat_map(|c| {
            if c.args.first().is_some_and(|a| a == stream) {
                return reads_in(
                    program,
                    analysis,
                    overlay,
                    &text,
                    std::slice::from_ref(*c),
                    stream,
                );
            }
            resolve(program, analysis, overlay, &c.callee)
                .ok()
                .and_then(|h| handler_input(program, analysis, overlay, h, c, stream))
                .map_or_else(Vec::new, |(text, param)| {
                    let reads = reads_in(
                        program,
                        analysis,
                        overlay,
                        &text,
                        &calls_in_order(&text),
                        &param,
                    );
                    repeated(reads, c.repeat.as_ref())
                })
        })
        .collect();
    Case {
        labels,
        handler: None,
        fields,
    }
}

/// Reads `entry` as a dispatcher: the `switch` on a value read off a
/// stream whose cases read the most on from it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The dispatch, or `None` when the function does not decompile, switches
/// on no value read off a stream, or no case reads on from it.
#[must_use]
pub fn dispatch_of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<Dispatch> {
    let text = plain_text_cached(program, analysis, overlay, overlay.fingerprint(), entry)?;
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let calls = calls_in_order(&text);
    let f = analysis.function(entry)?;
    let tables: Vec<(&u64, &Vec<u64>)> = analysis.jump_tables.range(f.start..f.end).collect();
    let switches = lines.iter().filter(|t| t.starts_with("switch (")).count();
    let route = match (tables.as_slice(), switches) {
        ([], _) => Route::Compare,
        ([(site, t)], 1) => Route::Table {
            site: **site,
            entries: t.len(),
        },
        _ => Route::Untied {
            tables: tables.len(),
            switches,
        },
    };
    let mut found: Vec<Dispatch> = Vec::new();
    for (i, t) in lines.iter().enumerate() {
        let Some(inner) = t
            .strip_prefix("switch (")
            .and_then(|r| r.strip_suffix(") {"))
        else {
            continue;
        };
        let var = strip_casts(inner);
        let direct = calls
            .iter()
            .find(|c| c.line == i + 1 && is_call_of(var, &c.callee));
        let found_read = match direct {
            Some(c) => Some((c, true)),
            None if is_ident(var) => opcode_read(&lines, &calls, i, var),
            None => None,
        };
        let Some((read, returned)) = found_read else {
            continue;
        };
        let Some(stream) = read.args.first().filter(|s| is_ident(s)) else {
            continue;
        };
        let kind = if returned {
            returned_bytes(program, analysis, overlay, &read.callee).map(|b| format!("u{}", b * 8))
        } else {
            reads_in(
                program,
                analysis,
                overlay,
                &text,
                std::slice::from_ref(read),
                stream,
            )
            .first()
            .map(|f| f.kind.clone())
            .filter(|k| k != "?")
        };
        let Some(kind) = kind else {
            continue;
        };
        let cases = cases_of(&lines, i)
            .into_iter()
            .map(|(labels, body)| case_of(program, analysis, overlay, labels, &body, stream))
            .collect();
        found.push(Dispatch {
            entry,
            stream: stream.clone(),
            opcode: var.to_owned(),
            kind,
            reader: read.callee.clone(),
            read_at: first_call(program, analysis, overlay, entry, &read.callee),
            returned,
            route,
            cases,
            other_switches: 0,
        });
    }
    let others = found.len().saturating_sub(1);
    let mut best = found
        .into_iter()
        .rev()
        .max_by_key(Dispatch::handled)
        .filter(|d| d.handled() > 0)?;
    best.other_switches = others;
    Some(best)
}

/// Spells a case's labels, a number in hex: `0x10,0x11`.
///
/// # Arguments
///
/// * `labels` - The labels.
fn spell_labels(labels: &[String]) -> String {
    labels
        .iter()
        .map(|l| literal(strip_casts(l)).map_or_else(|| l.clone(), |v| format!("{v:#x}")))
        .collect::<Vec<_>>()
        .join(",")
}

/// Spells how a dispatcher picks its case, for one cell.
///
/// # Arguments
///
/// * `route` - The route.
fn spell_route(route: Route) -> String {
    match route {
        Route::Table { site, entries } => format!("table@{site:#x}:{entries}"),
        Route::Compare => "compare".to_owned(),
        Route::Untied { tables, .. } => format!("untied:{tables}"),
    }
}

/// Spells an address or `-`.
///
/// # Arguments
///
/// * `at` - The address, when known.
fn spell_at(at: Option<u64>) -> String {
    at.map_or_else(|| "-".to_owned(), |a| format!("{a:#x}"))
}

/// Renders one dispatcher: its opcode read, how it picks a case, what is
/// unsure, and per opcode the handler with the record it reads.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The dispatcher's entry.
/// * `filter` - Case-insensitive substring of the opcode or the handler's
///   name; empty for all.
/// * `limit` - Rows shown at most.
///
/// # Returns
///
/// The table, or `None` as for [`dispatch_of`].
#[must_use]
pub fn dispatch_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    filter: &str,
    limit: usize,
) -> Option<String> {
    let d = dispatch_of(program, analysis, overlay, entry)?;
    let q = filter.to_lowercase();
    let rows: Vec<(String, String, &Case)> = d
        .cases
        .iter()
        .map(|c| {
            let handler = c.handler.map_or_else(
                || "inline".to_owned(),
                |h| format!("{}@{h:#x}", name_of(analysis, overlay, h)),
            );
            (spell_labels(&c.labels), handler, c)
        })
        .filter(|(op, h, _)| {
            q.is_empty() || op.to_lowercase().contains(&q) || h.to_lowercase().contains(&q)
        })
        .collect();
    let shown = rows.len().min(limit);
    let mut out = format!(
        "# {} @ {entry:#x} dispatches {} cases on an opcode read off {}: {} read on from it, showing {shown} of {}\n",
        name_of(analysis, overlay, entry),
        d.cases.len(),
        d.stream,
        d.handled(),
        rows.len()
    );
    let how = if d.returned {
        "returned by"
    } else {
        "stored through its out pointer by"
    };
    let _ = writeln!(
        out,
        "# opcode {} ({}) {how} {} at {} (the function's first call to it)",
        d.opcode,
        d.kind,
        d.reader,
        spell_at(d.read_at)
    );
    let _ = match d.route {
        Route::Table { site, entries } => writeln!(
            out,
            "# picked by a jump table: indirect jump at {site:#x}, {entries} entries"
        ),
        Route::Compare => writeln!(
            out,
            "# picked by compares: no jump table in the function, the decompiler folded a compare tree into the switch"
        ),
        Route::Untied { tables, switches } => writeln!(
            out,
            "# unsure how the case is picked: {tables} jump tables and {switches} switches in the function, none tied to this switch"
        ),
    };
    let blind: Vec<String> = d
        .cases
        .iter()
        .filter(|c| !c.reads() && c.labels != ["default"])
        .map(|c| spell_labels(&c.labels))
        .collect();
    if !blind.is_empty() {
        let _ = writeln!(
            out,
            "# unsure: {} read nothing borer ties to the stream; their records are unknown",
            blind.join(" ")
        );
    }
    if d.other_switches > 0 {
        let _ = writeln!(
            out,
            "# unsure: {} other switches on a value read off a stream; this one reads on in the most cases",
            d.other_switches
        );
    }
    out.push_str("opcode\thandler\treads\tfields\n");
    for (op, handler, c) in rows.into_iter().take(limit) {
        let _ = writeln!(
            out,
            "{op}\t{handler}\t{}\t{}",
            c.fields.len(),
            compact_fields(&c.fields)
        );
    }
    Some(out)
}

/// Tells whether the function at `entry` has two call sites or more, to
/// one callee or to several.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `entry` - The function's entry.
fn two_calls(analysis: &Analysis, entry: u64) -> bool {
    analysis
        .refs_from(entry)
        .iter()
        .filter(|(_, s)| s.kind == RefKind::Call)
        .nth(1)
        .is_some()
}

/// Decompiles up to [`SCAN_MAX`] functions in address order and keeps
/// what `read` finds in each.
///
/// # Arguments
///
/// * `candidates` - The function entries worth reading.
/// * `read` - Reads one function.
fn scan<R: Send>(candidates: &[u64], read: impl Fn(u64) -> Option<R> + Sync) -> Vec<R> {
    let scanned = &candidates[..candidates.len().min(SCAN_MAX)];
    super::striped_with(scanned, PAR_MIN, || (), |(), &e| read(e))
        .into_iter()
        .flatten()
        .flatten()
        .collect()
}

/// Renders every function switching on an opcode read off a stream with
/// at least [`HANDLED_MIN`] cases reading on from it, most cases first.
///
/// Only functions holding a jump table, or [`FORKS_MIN`] two-way blocks,
/// and making two calls or more are decompiled, at most
/// [`SCAN_MAX`] of them; the header says how many.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `filter` - Case-insensitive substring of the dispatcher's name; empty
///   for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn dispatchers_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    filter: &str,
    limit: usize,
) -> String {
    let candidates: Vec<u64> = analysis
        .functions
        .iter()
        .filter(|f| f.thunk.is_none() && two_calls(analysis, f.entry))
        .filter(|f| {
            analysis.jump_tables.range(f.start..f.end).next().is_some()
                || f.blocks.iter().filter(|b| b.successors.len() == 2).count() >= FORKS_MIN
        })
        .map(|f| f.entry)
        .collect();
    let q = filter.to_lowercase();
    let mut found: Vec<(String, Dispatch)> = scan(&candidates, |e| {
        dispatch_of(program, analysis, overlay, e).filter(|d| d.handled() >= HANDLED_MIN)
    })
    .into_iter()
    .map(|d| (name_of(analysis, overlay, d.entry), d))
    .filter(|(n, _)| q.is_empty() || n.to_lowercase().contains(&q))
    .collect();
    found.sort_by_key(|(_, d)| (std::cmp::Reverse(d.handled()), d.entry));
    let shown = found.len().min(limit);
    let mut out = format!(
        "# {} functions switch on an opcode read off a stream with {HANDLED_MIN} or more cases reading on from it (decompiled {} of {} candidates: a jump table or {FORKS_MIN} two-way blocks, two calls), showing {shown} of {}\n",
        found.len(),
        candidates.len().min(SCAN_MAX),
        candidates.len(),
        found.len()
    );
    out.push_str("dispatcher\taddress\tcases\thandled\treader\tread_at\troute\n");
    for (name, d) in found.into_iter().take(limit) {
        let _ = writeln!(
            out,
            "{name}\t{:#x}\t{}\t{}\t{}\t{}\t{}",
            d.entry,
            d.cases.len(),
            d.handled(),
            d.reader,
            spell_at(d.read_at),
            spell_route(d.route)
        );
    }
    out
}

/// Reads `entry` as a sender that writes a constant opcode first.
///
/// Its first call handing a stream on passes a constant and nothing else
/// to a writer that stores it at a width borer reads,
/// a later call hands the same stream a value that is not a constant, and
/// one of the later writes has a kind [`encoding_through`] can tell: a
/// call passing a handle and a command code, whose callee stores neither,
/// is not a write.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The sender, or `None` when the function does not decompile or does not
/// write that way.
#[must_use]
pub fn send_of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<OpcodeSend> {
    let text = plain_text_cached(program, analysis, overlay, overlay.fingerprint(), entry)?;
    let calls = calls_in_order(&text);
    calls.iter().enumerate().find_map(|(at, first)| {
        let [stream, value] = first.args.as_slice() else {
            return None;
        };
        let opcode = literal(strip_casts(value)).filter(|_| is_ident(stream))?;
        let earlier = calls[..at].iter().any(|c| c.args.first() == Some(stream));
        let writer = resolve(program, analysis, overlay, &first.callee).ok()?;
        if earlier || analysis.function(writer).is_none_or(|f| f.thunk.is_some()) {
            return None;
        }
        let encoding = encoding_through(program, analysis, overlay, entry, stream).filter(|e| {
            e.fields
                .first()
                .is_some_and(|w| w.via == first.callee && w.kind != "?")
                && e.fields.iter().skip(1).any(|w| w.kind != "?")
        })?;
        let bits = u32::try_from(encoding.fields.first()?.bits).ok()?;
        let wire = opcode
            & u64::MAX
                .checked_shr(64u32.saturating_sub(bits))
                .unwrap_or(u64::MAX);
        Some(OpcodeSend {
            entry,
            opcode: wire,
            writer: first.callee.clone(),
            write_at: first_call(program, analysis, overlay, entry, &first.callee),
            encoding,
        })
    })
}

/// Renders every function writing a constant opcode first and then fields
/// through the same writer, by opcode, with what it writes after it.
///
/// Only functions making two calls or more are decompiled, at most
/// [`SCAN_MAX`] of them; the header says how many.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `filter` - Case-insensitive substring of the opcode, the sender's or
///   the writer's name; empty for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn sends_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    filter: &str,
    limit: usize,
) -> String {
    let candidates: Vec<u64> = analysis
        .functions
        .iter()
        .filter(|f| f.thunk.is_none() && two_calls(analysis, f.entry))
        .map(|f| f.entry)
        .collect();
    let q = filter.to_lowercase();
    let mut found: Vec<(String, OpcodeSend)> =
        scan(&candidates, |e| send_of(program, analysis, overlay, e))
            .into_iter()
            .map(|s| (name_of(analysis, overlay, s.entry), s))
            .filter(|(n, s)| {
                q.is_empty()
                    || n.to_lowercase().contains(&q)
                    || s.writer.to_lowercase().contains(&q)
                    || format!("{:#x}", s.opcode).contains(&q)
            })
            .collect();
    found.sort_by_key(|(_, s)| (s.opcode, s.entry));
    let shown = found.len().min(limit);
    let mut out = format!(
        "# {} functions write a constant opcode first and then fields through the same writer (decompiled {} of {} candidates: two calls or more), showing {shown} of {}\n",
        found.len(),
        candidates.len().min(SCAN_MAX),
        candidates.len(),
        found.len()
    );
    out.push_str("opcode\tsender\taddress\twriter\twrite_at\twrites\tfields\n");
    for (name, s) in found.into_iter().take(limit) {
        let _ = writeln!(
            out,
            "{:#x}\t{name}\t{:#x}\t{}\t{}\t{}\t{}",
            s.opcode,
            s.entry,
            s.writer,
            spell_at(s.write_at),
            s.encoding.fields.len(),
            compact_writes(&s.encoding.fields)
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Case lines give their labels, a fall-through and a default
    /// included; braces in a literal do not count; casts come off the
    /// switched value.
    ///
    /// # Panics
    ///
    /// When a line is read wrongly.
    #[test]
    fn case_lines_braces_and_casts_are_read_from_the_text() {
        let labels = |t| case_labels(t).map(|(l, rest)| (l.join(","), rest));
        assert_eq!(labels("case 1: case 2: {"), Some(("1,2".to_owned(), "{")));
        assert_eq!(
            labels("case 3: default: {"),
            Some(("3,default".to_owned(), "{"))
        );
        assert_eq!(labels("case 4: break;"), Some(("4".to_owned(), "break;")));
        assert_eq!(
            labels("case Op::Move: {"),
            Some(("Op::Move".to_owned(), "{"))
        );
        assert_eq!(case_labels("x = 1;"), None);
        assert_eq!(braces(r#"if (s == "{") {"#), 1);
        assert_eq!(braces("} else {"), 0);
        assert_eq!(strip_casts("(uint8_t)local_c"), "local_c");
        assert_eq!(strip_casts("(a1 + 1)"), "(a1 + 1)");
        assert_eq!(literal(strip_casts("(uint8_t)0x21")), Some(0x21));
        assert_eq!(literal("33"), Some(33));
        assert_eq!(literal("a2"), None);
        assert_eq!(literal("12 + a2"), None);
        let field = |kind: &str, bytes| Field {
            order: String::new(),
            dest: "a2".to_owned(),
            kind: kind.to_owned(),
            bytes,
            via: "f".to_owned(),
            repeat: None,
            children: Vec::new(),
            name: String::new(),
        };
        let case = |fields| Case {
            labels: vec!["1".to_owned()],
            handler: None,
            fields,
        };
        let read = |text: &str| {
            let lines: Vec<&str> = text.lines().collect();
            let calls = calls_in_order(text);
            opcode_read(&lines, &calls, lines.len() - 1, "v").map(|(c, r)| (c.callee.clone(), r))
        };
        assert_eq!(
            read("f(a1, &v);\nw = v;\nswitch (v) {"),
            Some(("f".to_owned(), false))
        );
        assert_eq!(
            read("v = g(a1);\nswitch (v) {"),
            Some(("g".to_owned(), true))
        );
        assert_eq!(read("f(a1, &v);\nv ^= 1;\nswitch (v) {"), None);
        assert_eq!(read("v = g(a1) ^ 1;\nswitch (v) {"), None);
        assert_eq!(read("f(a1, &v);\nv++;\nswitch (v) {"), None);
        assert_eq!(read("f(a1, &v);\nh(&v);\nswitch (v) {"), None);
        assert!(!case(vec![field("?", 0)]).reads());
        assert!(case(vec![field("?", 0), field("u16", 2)]).reads());
        let inner = Field {
            repeat: Some("m".to_owned()),
            ..field("u8", 1)
        };
        let looped = repeated(vec![field("u16", 2), inner], Some(&"n".to_owned()));
        let repeats: Vec<Option<&str>> = looped.iter().map(|f| f.repeat.as_deref()).collect();
        assert_eq!(repeats, [Some("n"), Some("m")]);
        let lines = [
            "switch (v) {",
            "case 1: {",
            "if (x) {",
            "f(a1);",
            "}",
            "}",
            "case 2: h(a1);",
            "break;",
            "}",
            "g(a1);",
        ];
        let cases = cases_of(&lines, 0);
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].1, ["if (x) {", "f(a1);", "}"]);
        assert_eq!(cases[1], (vec!["2".to_owned()], vec!["h(a1);", "break;"]));
    }
}
