//! The skeleton view: control flow and calls only, with repeated and elided
//! statements folded.

use super::*;

/// Reduces pseudo-C to its skeleton: header, control flow, calls, returns.
///
/// The `// signature:` line folds into the header (`// T name(params) @
/// address: ...`) and `// note:` lines go. Declarations, assignments and
/// stores without a call are dropped; a run of dropped lines inside a block
/// leaves one `...` at its indentation so the reader knows work was elided.
/// An assert reads `assert(expr);` whether its helper is guarded by an `if`
/// or called outright with the expression, message, source path and line.
/// Labels, `goto`, `break`, `continue`,
/// `if`/`else`/`while`/`for`/`switch`/`case` lines and block closers stay.
/// String literals longer than [`SKELETON_STRING_MAX`] characters are clipped
/// (an assert's file path says nothing an agent triaging needs) and template
/// argument lists shrink to `<..>` (`Util::Array<..>::Alloc`). An agent
/// reads this first and asks for the full text only when it matters.
///
/// # Arguments
///
/// * `text` - Output of [`decompile`].
///
/// # Returns
///
/// The skeleton, ending in a newline.
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::decompile::skeleton;
///
/// let full = "// f @ 0x1000\nuint64_t rax;\n\nrax = a1 + 1;\nif (rax != 0) {\n  *(uint64_t*)a2 = rax;\n  g(rax, \"a long literal that runs past the clip\");\n}\nreturn rax;\n";
/// assert_eq!(
///     skeleton(full),
///     "// f @ 0x1000\n...\nif (rax != 0) {\n  ...\n  g(rax, \"a long literal that runs past...\");\n}\nreturn rax;\n"
/// );
/// ```
pub fn skeleton(text: &str) -> String {
    let mut out: Vec<String> = Vec::new();
    let mut elided: Option<usize> = None;
    for line in text.lines() {
        let t = line.trim();
        if t.is_empty() || t.starts_with("// note: ") {
            continue;
        }
        if let Some(sig) = t.strip_prefix("// signature: ")
            && out.len() == 1
            && let Some(merged) = out
                .first()
                .and_then(|head| head.split_once(" @ 0x"))
                .map(|(_, tail)| format!("// {sig} @ 0x{tail}"))
            && let Some(head) = out.first_mut()
        {
            *head = merged;
            continue;
        }
        if keeps_in_skeleton(t) {
            if let Some(ind) = elided.take() {
                out.push(format!("{}...", " ".repeat(ind)));
            }
            out.push(
                fold_assert_call(line).unwrap_or_else(|| clip_strings(line, SKELETON_STRING_MAX)),
            );
        } else if elided.is_none() {
            elided = Some(indent_of(line));
        }
    }
    if let Some(ind) = elided {
        out.push(format!("{}...", " ".repeat(ind)));
    }
    fold_asserts(&mut out);
    fold_guarded_runs(&mut out);
    fold_repeated_statements(&mut out);
    fold_elided_blocks(&mut out);
    for line in &mut out {
        *line = elide_templates(line);
        clip_statement(line);
    }
    let mut s = out.join("\n");
    s.push('\n');
    s
}

/// Reads the guarded single-call statement that starts at `i`, if one does.
///
/// The shape is three lines: `if (...) {`, one call statement, and `}`.
///
/// # Arguments
///
/// * `lines` - The skeleton's lines.
/// * `i` - Index of the candidate `if`.
///
/// # Returns
///
/// `(indent of the guard, called name)`, or `None` when the three lines are
/// not that shape.
pub(super) fn guarded_call(lines: &[String], i: usize) -> Option<(usize, String)> {
    let open = lines.get(i)?;
    let body = lines.get(i + 1)?;
    let close = lines.get(i + 2)?;
    let o = open.trim_start();
    if if_opener(o).is_none() || close.trim() != "}" {
        return None;
    }
    let b = body.trim();
    let name = b.split_once('(')?.0;
    if !b.ends_with(");") || name.is_empty() || name.contains(' ') {
        return None;
    }
    Some((indent_of(open), name.to_owned()))
}

/// Collapses runs of guarded single-call statements that repeat one call.
///
/// A C++ function holding many objects ends in one inlined destructor per
/// object, each an `if (p != &buf) { release(p); }` over a different local.
/// Forty in a row state one thing forty times and bury the logic between
/// them; the run renders as the call it repeats and how many times, which
/// keeps the call in the text while dropping the repetition.
///
/// A run is only folded when every guard holds the same call and nothing
/// labelled sits inside it, so no `goto` can land in what was removed.
///
/// # Arguments
///
/// * `lines` - The skeleton's lines, folded in place.
pub(super) fn fold_guarded_runs(lines: &mut Vec<String>) {
    /// Shortest run worth folding.
    const MIN_RUN: usize = 3;
    let mut i = 0;
    while i + MIN_RUN * 3 <= lines.len() {
        let Some((ind, name)) = guarded_call(lines, i) else {
            i += 1;
            continue;
        };
        let mut end = i;
        while guarded_call(lines, end).is_some_and(|(d, n)| d == ind && n == name) {
            end += 3;
        }
        let runs = (end - i) / 3;
        if runs < MIN_RUN {
            i += 1;
            continue;
        }
        lines.splice(
            i..end,
            [format!(
                "{}// {runs} guarded {name}(...) calls elided",
                " ".repeat(ind)
            )],
        );
        i += 1;
    }
}

/// Collapses a run of identical statements into one and a count.
///
/// A C++ function that builds strings carries one cold throw site per
/// operation, and a compiler emits them next to each other, so a skeleton
/// shows `throw_logic_error("basic_string::append")` thirty times over.
/// Repeating a statement says nothing the first one did not.
///
/// Only statements fold, and only when byte-identical, which means a label
/// between two of them ends the run: nothing a `goto` names is ever inside
/// what was removed.
///
/// # Arguments
///
/// * `lines` - The skeleton's lines, folded in place.
pub(super) fn fold_repeated_statements(lines: &mut Vec<String>) {
    /// Shortest run worth folding: a second identical line is already pure
    /// repetition, so a pair folds.
    const MIN_RUN: usize = 2;
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].clone();
        let statement = line.trim_end().ends_with(");") && !line.trim_start().starts_with("//");
        if !statement {
            i += 1;
            continue;
        }
        let mut end = i + 1;
        while lines.get(end) == Some(&line) {
            end += 1;
        }
        let run = end - i;
        if run < MIN_RUN {
            i = end;
            continue;
        }
        let folded = format!("{line}   // and {} more the same", run - 1);
        lines.splice(i..end, [folded]);
        i += 1;
    }
}

/// Puts a block whose whole body was elided back on one line.
///
/// A skeleton keeps the shape of the code and drops the detail, so a block
/// holding nothing but detail renders as three lines that together say one
/// thing: there was a body here. `if (c) { ... }` says it in one, and on a
/// function of five hundred lines the difference is most of the page.
///
/// # Arguments
///
/// * `lines` - The skeleton's lines, folded in place.
pub(super) fn fold_elided_blocks(lines: &mut Vec<String>) {
    let mut i = 0;
    while i + 2 < lines.len() {
        let open = lines[i].clone();
        let closes = lines[i + 2].trim().starts_with('}');
        let body_is_all_elided = lines[i + 1].trim() == "...";
        if !open.trim_end().ends_with('{') || !body_is_all_elided || !closes {
            i += 1;
            continue;
        }
        // The closing line has to belong to this block, not to an outer one.
        if indent_of(&lines[i + 2]) != indent_of(&open) {
            i += 1;
            continue;
        }
        let folded = format!("{} ... {}", open.trim_end(), lines[i + 2].trim());
        lines.splice(i..=i + 2, [folded]);
        i += 1;
    }
}

/// Cuts an over-long skeleton statement in place, keeping a trailing `goto`.
///
/// A plain cut takes the tail, and on a conditional jump the tail is the
/// destination, so `goto L_14000a58f;` becomes `goto L_140...;` and names
/// nowhere. The `goto` clause is reserved out of the budget and the
/// condition pays for it instead.
///
/// # Arguments
///
/// * `line` - The rendered statement; untouched unless it is over
///   [`SKELETON_LINE_MAX`] and ends in `;`.
pub(super) fn clip_statement(line: &mut String) {
    if line.len() <= SKELETON_LINE_MAX || !line.ends_with(';') {
        return;
    }
    let goto = line.rfind(" goto ").map(|i| line[i..].to_owned());
    let budget = SKELETON_LINE_MAX.saturating_sub(goto.as_ref().map_or(0, String::len) + 4);
    let cut = line
        .char_indices()
        .map(|(i, _)| i)
        .take_while(|i| *i <= budget)
        .last()
        .unwrap_or(0);
    line.truncate(cut);
    match &goto {
        Some(g) => {
            line.push_str("...");
            line.push_str(g);
        }
        None => line.push_str("...;"),
    }
}

/// Longest string literal a skeleton line keeps in full.
pub(super) const SKELETON_STRING_MAX: usize = 32;
/// Longest statement line a skeleton keeps in full.
///
/// A line cut to this length loses its tail, and on a conditional jump the
/// tail is the destination: `goto L_140...;` names nowhere. A line ending in
/// a `goto` therefore spends the budget on the condition and keeps the label
/// whole.
pub(super) const SKELETON_LINE_MAX: usize = 120;

/// Replaces each guarded assert (`if (c) { helper("expr", ..., __FUNCSIG__...); }`)
/// in skeleton lines with `assert(expr);` at the `if`'s indentation.
///
/// # Arguments
///
/// * `lines` - Skeleton lines, edited in place.
pub(super) fn fold_asserts(lines: &mut Vec<String>) {
    let mut i = 0;
    while i + 2 < lines.len() {
        let head = lines[i].trim_start();
        let call = lines[i + 1].trim();
        let close = lines[i + 2].trim();
        let is_assert = if_opener(head).is_some()
            && call.contains("__FUNCSIG__")
            && call.ends_with(");")
            && close == "}";
        if !is_assert {
            i += 1;
            continue;
        }
        let expr = call
            .split_once('"')
            .and_then(|(_, rest)| rest.split_once('"'))
            .map_or("...", |(e, _)| e);
        let folded = format!("{}assert({expr});", pad_of(&lines[i]));
        lines.splice(i..i + 3, [folded]);
        i += 1;
    }
}

/// Source file extensions that mark an assert helper's path argument.
pub(super) const SOURCE_EXTENSIONS: [&str; 7] = [".cc", ".cpp", ".cxx", ".c", ".h", ".hpp", ".inl"];

/// Folds an assert helper called outright into `assert(expr);`.
///
/// Such a helper takes the expression text, a message, the source path and
/// the line: `f("n == 1", "n must be one", "src/a.cc", 0x1c2);`. The fold
/// keeps the expression, as [`fold_asserts`] does for guarded helpers.
///
/// # Arguments
///
/// * `line` - One pseudo-C line, indentation included.
///
/// # Returns
///
/// The folded line at the same indentation, or `None` when the line is not
/// such a call statement.
pub(super) fn fold_assert_call(line: &str) -> Option<String> {
    let t = line.trim_start();
    let (callee, rest) = t.split_once('(')?;
    if callee.is_empty() || callee.contains([' ', '=']) {
        return None;
    }
    let args = rest.strip_suffix(");")?;
    let [expr, message, path, line_no] = split_arguments(args)[..] else {
        return None;
    };
    let expr = expr.strip_prefix('"')?.strip_suffix('"')?;
    let path = path.strip_prefix('"')?.strip_suffix('"')?;
    if !message.starts_with('"')
        || !SOURCE_EXTENSIONS.iter().any(|e| path.ends_with(e))
        || parse_const(line_no).is_none()
    {
        return None;
    }
    Some(format!("{}assert({expr});", pad_of(line)))
}

/// Clips every string literal in a line to `cap` characters, ending clipped
/// ones in `...` inside the quotes.
///
/// Escaped quotes and backslashes inside literals are honored.
///
/// # Arguments
///
/// * `line` - One pseudo-C line.
/// * `cap` - Longest literal kept whole.
pub(super) fn clip_strings(line: &str, cap: usize) -> String {
    let mut out = String::with_capacity(line.len());
    let mut chars = line.chars();
    while let Some(c) = chars.next() {
        if c != '"' {
            out.push(c);
            continue;
        }
        let mut lit = String::new();
        let mut escaped = false;
        for c in chars.by_ref() {
            if escaped {
                lit.push(c);
                escaped = false;
            } else if c == '\\' {
                lit.push(c);
                escaped = true;
            } else if c == '"' {
                break;
            } else {
                lit.push(c);
            }
        }
        out.push('"');
        if lit.chars().count() > cap {
            out.extend(lit.chars().take(cap.saturating_sub(3)));
            out.push_str("...");
        } else {
            out.push_str(&lit);
        }
        out.push('"');
    }
    out
}

/// Shrinks every template argument list in a skeleton line to `<..>`.
///
/// A `<` right after an identifier character opens a list that runs to its
/// balanced `>`; a list of two characters or fewer stays, since the mark is
/// no shorter. String literals are skipped, and `<=` and `<<` are operators.
///
/// # Arguments
///
/// * `line` - One skeleton line.
///
/// # Returns
///
/// The line with `Util::Array<Util::KeyValuePair<unsigned int,T> >::Alloc`
/// reading `Util::Array<..>::Alloc`.
pub(super) fn elide_templates(line: &str) -> String {
    let b = line.as_bytes();
    let mut out = String::with_capacity(line.len());
    let mut kept = 0;
    let mut in_string = false;
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if in_string {
            if c == b'\\' {
                i += 1;
            } else if c == b'"' {
                in_string = false;
            }
        } else if c == b'"' {
            in_string = true;
        } else if c == b'<'
            && i > 0
            && (b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_')
            && b.get(i + 1)
                .is_some_and(|n| !matches!(n, b'=' | b'<' | b' '))
        {
            let mut depth = 0usize;
            let mut j = i;
            while j < b.len() {
                match b[j] {
                    b'<' => depth += 1,
                    b'>' => {
                        depth = depth.saturating_sub(1);
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            if j < b.len() && j - i > 3 {
                out.push_str(&line[kept..=i]);
                out.push_str("..");
                kept = j;
                i = j;
                continue;
            }
        }
        i += 1;
    }
    out.push_str(&line[kept..]);
    out
}

/// Tells whether a trimmed pseudo-C line belongs in the skeleton.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn keeps_in_skeleton(t: &str) -> bool {
    const HEADS: [&str; 13] = [
        "//", "if (", "} else", "else", "while", "for (", "switch", "case ", "default:", "return",
        "goto ", "do {", "} while",
    ];
    if t == "}" || t == "break;" || t == "continue;" || is_label(t) {
        return true;
    }
    if HEADS.iter().any(|h| t.starts_with(h)) {
        return true;
    }
    t.find('(').is_some_and(|i| {
        t[..i]
            .chars()
            .next_back()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_' || c == '>' || c == ':')
    }) && !t.starts_with("uint")
        && !t.starts_with("int")
        && !t.starts_with("float")
        && !t.starts_with("double")
}
