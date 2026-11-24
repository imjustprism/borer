//! A rotated loop whose first test the values set right before it decide
//! ([`decided_do`]).

use super::super::ctext::Ast;
use super::super::interp::pure;
use super::linear::{Declared, Eval, read};
use super::*;

/// Most plain assignments in front of a loop a decision reads.
pub(super) const RUN_MAX: usize = 16;

/// Writes each `do` of a function whose first test is true on entry as a
/// `while` or a `for` ([`decided_do`]).
///
/// It runs right after the registers are split into variables
/// ([`super::super::vars::split_webs`]), which reads a `do` as a loop that
/// runs at least once: a `while` before the split would leave it a path
/// past the loop that the entry values rule out, and a copy to carry a
/// value along it. The declarations it adds give the decision its widths.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `word` - The image's word in bits (32 or 64): the width of a pointer
///   and of a register no line declares.
///
/// # Returns
///
/// The text with those loops rewritten.
pub(in crate::analysis::decompile) fn decided_loops(text: String, word: u8) -> String {
    sweep(text, |lines, k, declared| {
        decided_do(lines, k, word, declared)
    })
}

/// Runs a loop rewrite at every line of a function's text.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `at` - The rewrite at one line, told the declarations read so far;
///   whether it rewrote.
///
/// # Returns
///
/// The text rewritten, the same string when nothing was.
pub(super) fn sweep(
    text: String,
    mut at: impl FnMut(&mut Vec<String>, usize, &mut Declared) -> bool,
) -> String {
    if !text.contains("do {") {
        return text;
    }
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let mut declared = Declared::default();
    let mut changed = false;
    let mut k = 0;
    while k < lines.len() {
        changed |= at(&mut lines, k, &mut declared);
        k += 1;
    }
    if !changed {
        return text;
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Rewrites the `do` that opens on line `k + 1` as a `while` or a `for`
/// when its first test is true on entry.
///
/// `do { B } while (C);` is `while (C) { B }` when the values the lines in
/// front of it set make `C` true, and `for (v = e; C; step) { B' }` when
/// line `k` is that `v = e;` and `B` ends with `v`'s step ([`step`]).
///
/// `do { B } while (C);` and `while (C) { B }` run the same statements
/// exactly when `C` holds the first time: the guard the compiler left out
/// because it knew. The lines in front are the plain assignments to names
/// directly above the `do` at its level, up to a call, a store, a label or
/// a block; [`decided`] puts their values into `C` and keeps the loop when
/// the result is not proven true. No rewrite takes a loop that holds a
/// label or an empty one, which [`spin`] reads.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line before the `do {`.
/// * `word` - The image's word in bits.
/// * `declared` - The declarations looked up so far, which no rewrite
///   here changes.
///
/// # Returns
///
/// Whether the `do` became a `while` or a `for`.
fn decided_do(lines: &mut Vec<String>, k: usize, word: u8, declared: &mut Declared) -> bool {
    let Some(open) = lines.get(k + 1).filter(|l| l.trim() == "do {") else {
        return false;
    };
    let pad = indent_of(open);
    let Some(latch) = closing(lines, k + 1, pad) else {
        return false;
    };
    let Some(cond) = lines
        .get(latch)
        .and_then(|l| l.trim().strip_prefix("} while (")?.strip_suffix(");"))
        .map(str::to_owned)
    else {
        return false;
    };
    let body = lines.get(k + 2..latch).unwrap_or(&[]);
    if body.is_empty() || body.iter().any(|l| is_label(l)) {
        return false;
    }
    let mut steps: Vec<Ast> = (0..=k)
        .rev()
        .take(RUN_MAX)
        .map_while(|j| {
            lines
                .get(j)
                .filter(|l| indent_of(l) == pad && !impure(l))
                .and_then(|l| assignment(l, word))
        })
        .collect();
    steps.reverse();
    let run = lines.get(k + 1 - steps.len()..=k).unwrap_or(&[]);
    if !decided(lines, &steps, &cond, word, declared) {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let close = format!("{pad_s}}}");
    let counted = run
        .last()
        .and_then(|l| plain_assignment(l))
        .filter(|(v, _)| mentions_ident(&cond, v))
        .and_then(|(v, value)| Some((v, value, step(body, pad, v)?)));
    let (at, rewritten): (usize, Vec<String>) = match counted {
        Some((v, value, (idx, step))) => {
            let step = step
                .strip_prefix(&format!("{v} = {v} + "))
                .filter(|inc| parse_const(inc).is_some())
                .map_or(step.clone(), |inc| format!("{v} += {inc}"));
            let head = format!("{pad_s}for ({v} = {value}; {cond}; {step}) {{");
            let kept = body
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != idx)
                .map(|(_, l)| l.clone());
            let out = std::iter::once(head)
                .chain(kept)
                .chain(std::iter::once(close))
                .collect();
            (k, out)
        }
        None => {
            let out = std::iter::once(format!("{pad_s}while ({cond}) {{"))
                .chain(body.iter().cloned())
                .chain(std::iter::once(close))
                .collect();
            (k + 1, out)
        }
    };
    lines.splice(at..=latch, rewritten);
    true
}

/// Returns the step a `for` header takes from a loop body.
///
/// That is its last line ([`step_of`]), or a constant step of `v` just
/// before a last plain assignment that does not read `v`, which may run
/// after it: `v` is then a register or a numbered variable, which no
/// address reaches, so the last line cannot read it through memory either.
///
/// # Arguments
///
/// * `body` - The loop body's lines.
/// * `pad` - The indentation of the loop's opener.
/// * `v` - The loop variable.
///
/// # Returns
///
/// The step's line in `body` and its text; `None` when the body ends with
/// no such step or continues at its own level.
pub(super) fn step(body: &[String], pad: usize, v: &str) -> Option<(usize, String)> {
    if let Some(step) = step_of(body, pad + 2, v) {
        return Some((body.len() - 1, step.to_owned()));
    }
    let at = body.len().checked_sub(2)?;
    let (line, tail) = (body.get(at)?, body.last()?);
    let tail_lhs = plain_assignment(tail)
        .or_else(|| tail.trim().strip_suffix(';')?.split_once(" += "))
        .map(|(lhs, _)| lhs);
    let apart = indent_of(line) == pad + 2
        && indent_of(tail) == pad + 2
        && !mentions_ident(tail, v)
        && !impure(tail)
        && tail_lhs.is_some_and(|lhs| is_register_name(lhs) || vars::is_var_name(lhs))
        && (is_register_name(v) || vars::is_var_name(v))
        && !continues_at_top(body);
    let s = line.trim().strip_suffix(';').filter(|_| apart)?;
    let inc = s
        .strip_prefix(&format!("{v} += "))
        .or_else(|| s.strip_prefix(&format!("{v} = {v} + ")))
        .filter(|inc| parse_const(inc).is_some_and(|c| c > 0))?;
    Some((at, format!("{v} += {inc}")))
}

/// Reads a line as a chain of plain assignments to names of one pure
/// value, `a = b = e;`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `word` - The machine word in bits, the width of `size_t` in a cast.
///
/// # Returns
///
/// The assignment, or `None` for any other line.
pub(super) fn assignment(line: &str, word: u8) -> Option<Ast> {
    /// Tells whether `e` is a chain of `=` to names ending in a pure value.
    fn chain(e: &Ast) -> bool {
        match e {
            Ast::Assign(None, t, v) => matches!(**t, Ast::Name(_)) && (chain(v) || pure(v)),
            _ => false,
        }
    }
    let e = read(line.trim().strip_suffix(';')?, word)?;
    chain(&e).then_some(e)
}

/// Tells whether a loop's test is true on entry, after the assignments in
/// front of it ran.
///
/// Each value is followed as C computes it at the widths the text states
/// ([`Eval`]); a name nothing in front sets stands for what it held, the
/// same at every read, and no read of memory is followed. The test is
/// decided when both sides' forms differ by a constant (two constants, or
/// one name or the frame base plus two offsets, nothing narrowed below the
/// compared width) or are two constants in order. Anything else is
/// undecided: nothing is sampled.
///
/// # Arguments
///
/// * `lines` - The function's lines, for the declarations.
/// * `steps` - The assignments in front of the loop, in order
///   ([`assignment`]).
/// * `cond` - The loop's test.
/// * `word` - The image's word in bits.
/// * `declared` - The declarations looked up so far ([`decided_do`]).
fn decided(lines: &[String], steps: &[Ast], cond: &str, word: u8, declared: &mut Declared) -> bool {
    let Some(test) = read(cond, word) else {
        return false;
    };
    let mut eval = Eval::new(lines, word, declared, false);
    for step in steps {
        eval.assign(step);
    }
    eval.truth(&test) == Some(true)
}
