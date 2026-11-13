//! The answer `decompile` gives: a function's text with the lines under
//! its first line that say what of it was checked against the binary, what
//! is known wrong in it and what to read next.
//!
//! The tool, the `borer://decompile` resource and the command line answer
//! with [`answer`]; the index stores the form [`shown`] makes, without the
//! repair search, and the batch counts the lines of [`answer_header`].

use std::collections::BTreeSet;

use super::{checked_header, decompile_named, skeleton, stack, warn};
use crate::analysis::{Analysis, Overlay, name_of, render};
use crate::program::Program;

/// How much of a function's text an answer shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Detail {
    /// The whole text.
    Full,
    /// The control flow and the calls only ([`skeleton`]).
    Skeleton,
}

/// Returns the answer `decompile` gives for one function: its text at the
/// detail asked for, with [`answer_header`]'s lines under its first line.
///
/// The text is rendered under the names the repair search picks, which
/// runs only where the text check flags the function
/// ([`render::answered_flagged`]). When the search ends with the text still
/// differing in a value its run leaves behind (a result, a byte of a
/// buffer, an import called), its note ([`render::Repair::note`]) ends the
/// `// warn:` line; a disagreement only the replay finds gets none. The
/// header is read before the text, so the check memoizes the decompilation
/// with the lifter's witness and the text reads the same cell.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `detail` - The whole text or its skeleton.
///
/// # Returns
///
/// The answer, or `None` when the function does not decompile
/// ([`decompile_named`]).
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::decompile::{Detail, answer};
/// use borer_engine::analysis::{Analysis, Overlay};
/// use borer_engine::program::{Arch, Program, Section};
///
/// // ASM: cmp ecx, 0x1337abcd ; sete al ; movzx eax, al ; ret
/// let code = vec![0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, 0x0f, 0x94, 0xc0, 0x0f, 0xb6, 0xc0, 0xc3];
/// let section = Section::mapped(".text", 0x1000, 0, 13, false, true);
/// let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![section]);
/// let a = Analysis::compute(&p);
/// let text = answer(&p, &a, &Overlay::default(), 0x1000, Detail::Full).expect("decompiles");
/// let mut lines = text.lines().skip(1);
/// assert!(lines.next().is_some_and(|l| l.starts_with("// checked vs binary")));
/// assert_eq!(
///     lines.next(),
///     Some("// next: borer://solve/0x1000,a1 (compares against 0x1337abcd: solve tries it as a1)")
/// );
/// ```
#[must_use]
pub fn answer(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    detail: Detail,
) -> Option<String> {
    let (overlay, differs) = render::answered_flagged(program, analysis, overlay, entry);
    let header = answer_header(program, analysis, &overlay, entry, differs.as_deref());
    let text = decompile_named(program, analysis, &overlay, entry)?;
    let text = match detail {
        Detail::Full => text,
        Detail::Skeleton => skeleton(&text),
    };
    Some(with_header(&text, header.as_deref()))
}

/// Returns the lines a `decompile` answer puts under its first line.
///
/// They are what of the text was checked against the binary
/// ([`checked_header`]), the note that the analysis ran out of budget when
/// it did ([`render::INCOMPLETE_NOTE`]), the `// warn:` line naming what is
/// known wrong in the text ([`warnings`]), then a `// next:` line per
/// resource the function's facts point at ([`render::next_steps`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `differs` - The repair search's note ([`render::answered_flagged`]),
///   which it gives only when its run of the text still leaves a value
///   differing ([`render::Repair::note`]).
///
/// # Returns
///
/// The lines without a final newline, or `None` when there are none.
#[must_use]
pub fn answer_header(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    differs: Option<&str>,
) -> Option<String> {
    header_lines(program, analysis, overlay, entry, differs, None)
}

/// Returns [`answer_header`]'s lines, read from `body` when the caller
/// already rendered it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `differs` - The repair search's note, as [`answer_header`] takes it.
/// * `body` - The rendered text, or `None` to decompile it.
///
/// # Returns
///
/// The lines without a final newline, or `None` when there are none.
fn header_lines(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    differs: Option<&str>,
    body: Option<&str>,
) -> Option<String> {
    let mut lines: Vec<String> = checked_header(program, analysis, overlay, entry)
        .into_iter()
        .chain(
            analysis
                .incomplete
                .then(|| format!("//{}", render::INCOMPLETE_NOTE.trim_start_matches('#'))),
        )
        .collect();
    lines.extend(header_warnings(
        program, analysis, overlay, entry, differs, body,
    ));
    let steps = body.map_or_else(
        || render::next_steps(program, analysis, overlay, entry),
        |text| render::next_steps_for(program, analysis, overlay, entry, text),
    );
    lines.extend(steps.iter().map(|step| format!("// next: {step}")));
    (!lines.is_empty()).then(|| lines.join("\n"))
}

/// Returns the `// warn:` line for `body`, decompiling when the caller has
/// no text.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `differs` - The repair search's note, as [`answer_header`] takes it.
/// * `body` - The rendered text, or `None` to decompile it.
///
/// # Returns
///
/// The line, or `None` when nothing is known wrong.
fn header_warnings(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    differs: Option<&str>,
    body: Option<&str>,
) -> Option<String> {
    match body {
        Some(text) => warnings(program, analysis, overlay, entry, text, differs),
        None => decompile_named(program, analysis, overlay, entry)
            .and_then(|text| warnings(program, analysis, overlay, entry, &text, differs)),
    }
}

/// Returns the form the index stores of an answer: a body the caller
/// already rendered with the answer's lines under its first line, made
/// without the repair search.
///
/// The warning and the next lines read `text`, so this does not decompile
/// the function again. The check line does not: it is the memoized check
/// of `entry` under `overlay` ([`checked_header`]), so `text` must be the
/// text that check was made from, as
/// [`decompile_checked_all`](super::decompile_checked_all) writes it; over
/// any other text the line would claim a replay nobody ran. With no repair
/// search, a function the text check flags gets no note and keeps the text
/// the decompiler wrote ([`render::answered_flagged`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `text` - The function's text under `overlay`, or `None` when
///   decompilation produced nothing.
///
/// # Returns
///
/// The body with its check, warning and next lines under the first line,
/// or `None` when there is no body or it is empty.
#[must_use]
pub fn shown(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: Option<&str>,
) -> Option<String> {
    let text = text.filter(|body| !body.is_empty())?;
    let header = header_lines(program, analysis, overlay, entry, None, Some(text));
    Some(with_header(text, header.as_deref()))
}

/// Returns a text with the lines of [`answer_header`] put under its first
/// line.
///
/// # Arguments
///
/// * `text` - The answer's text.
/// * `header` - The lines, or `None` to leave the text as it is.
///
/// # Returns
///
/// The text with the lines after its first line, or the text as it is
/// when there are none.
#[must_use]
pub fn with_header(text: &str, header: Option<&str>) -> String {
    let Some(header) = header else {
        return text.to_owned();
    };
    match text.split_once('\n') {
        Some((first, rest)) => format!("{first}\n{header}\n{rest}"),
        None => format!("{text}\n{header}\n"),
    }
}

/// Returns the `// warn:` line a `decompile` answer prints under its check
/// line: what keeps the text from being the C it claims.
///
/// Each item says what it means in a few words: a computed `goto`, a
/// callee of the binary with no prototype, a helper with no definition, a
/// name nothing declares, an operator C refuses on a float, a pointer or
/// an integer, a missing label, an instruction left as asm.
///
/// The decompile answer and the index carry it, like [`checked_header`]. Each
/// warning is a fact of the text, never a guess, so it flags no right
/// text; a text with no line may still be wrong in ways no fact of the
/// text shows. In the answer, never the index, the last item can be the
/// repair search's note: the input a run of the text still leaves a value
/// differing on ([`crate::analysis::render::Repair::note`]).
///
/// The text is read on a decompile's stack ([`stack::roomy`]): its
/// statements nest as deep as the function's, and a caller's thread may
/// have too little room for that.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, which say what the function calls.
/// * `overlay` - The names the text was written under.
/// * `entry` - The function's entry.
/// * `text` - Its text as [`decompile_named`] wrote it.
/// * `differs` - The repair search's note, as [`answer_header`] takes it.
///
/// # Returns
///
/// The line without its newline, `None` when nothing is known wrong.
#[must_use]
pub fn warnings(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: &str,
    differs: Option<&str>,
) -> Option<String> {
    let word = if program.is_64 { 64 } else { 32 };
    let in_binary: BTreeSet<String> = analysis
        .function(entry)
        .map(|f| f.callees.as_slice())
        .unwrap_or_default()
        .iter()
        .filter_map(|&c| {
            let g = analysis.function(c)?;
            let target = g.bound.unwrap_or(c);
            (g.thunk.is_none() && target != entry).then(|| name_of(analysis, overlay, target))
        })
        .collect();
    let line = stack::roomy(|| warn::line(text, &in_binary, word));
    match (line, differs) {
        (Some(line), Some(d)) => Some(format!("{line}; {d}")),
        (None, Some(d)) => Some(format!("{} {d}", warn::WARN)),
        (line, None) => line,
    }
}
