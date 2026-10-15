//! Rust's source locations read off the calls that hand them over, and
//! its overflow and bounds checks folded into notes.
//!
//! A Rust panic (and any function marked `#[track_caller]`) is handed the
//! address of a `core::panic::Location`, a `&str` naming the source file
//! followed by the line and column, which the text prints as a bare
//! address (`panic_bounds_check(a1, a2, 0x1427605b8)`). The location is
//! read back from the image and written beside the call (`// at
//! core/src/slice/mod.rs:1015:32`). A path under a cargo registry keeps
//! the crate and its file (`rhai-1.26.1/src/parser.rs`), one in the
//! standard library its own (`core/src/slice/mod.rs`).
//!
//! Release Rust also leaves the checks themselves as diamonds: an `if`
//! whose only statement is a panic call. A checked arithmetic's
//! `panic_const_*_overflow` and a slice index's `panic_bounds_check`
//! leave with the diamond, and the statement the check guards gains
//! `/* checked */` or `/* bounds-checked */`; where no guarded statement
//! follows, the block stays and the call alone becomes a note. The
//! callees whose calls left are returned for the header to say so.

use super::line::{
    if_opener, indent_of, is_case, is_ident_char, is_label, matching_paren, mentions_ident,
    parse_const, split_arguments, tokens, transfers, word_positions,
};
use crate::program::Program;

/// Longest source path a location is read with, in bytes.
const PATH_MAX: u64 = 512;
/// Highest line a location may name.
const LINE_MAX: u32 = 10_000_000;
/// Highest column a location may name.
const COLUMN_MAX: u32 = 100_000;

/// The source path a location names, shortened to what identifies it.
///
/// # Arguments
///
/// * `raw` - The path as compiled in, either separator.
fn short_path(raw: &str) -> String {
    let path = raw.replace('\\', "/");
    if let Some((_, rest)) = path.split_once("/registry/src/")
        && let Some((_, krate)) = rest.split_once('/')
    {
        return krate.to_owned();
    }
    if (path.contains("/rustlib/") || path.starts_with("/rustc/"))
        && let Some((_, rest)) = path.split_once("/library/")
    {
        return rest.to_owned();
    }
    path
}

/// Reads the `core::panic::Location` at `addr`: the file's `&str` (its
/// address and length), then the line and the column as 32-bit words.
///
/// # Arguments
///
/// * `program` - The image.
/// * `addr` - Where the location may sit.
///
/// # Returns
///
/// `path:line:column`, or `None` when the bytes there are no location: a
/// file that is no readable text ending in `.rs`, or a line or column out
/// of range.
pub(super) fn location_at(program: &Program, addr: u64) -> Option<String> {
    /// Bytes of a location: a pointer, a length, two 32-bit words.
    const SIZE: usize = 24;
    let raw = program.read_va(addr, SIZE)?;
    let word = |at: usize| -> Option<u64> {
        Some(u64::from_le_bytes(raw.get(at..at + 8)?.try_into().ok()?))
    };
    let half = |at: usize| -> Option<u32> {
        Some(u32::from_le_bytes(raw.get(at..at + 4)?.try_into().ok()?))
    };
    let (ptr, len, line, column) = (word(0)?, word(8)?, half(16)?, half(20)?);
    if !(4..=PATH_MAX).contains(&len) || !(1..=LINE_MAX).contains(&line) || column > COLUMN_MAX {
        return None;
    }
    let bytes = program.read_va(ptr, usize::try_from(len).ok()?)?;
    let file = std::str::from_utf8(bytes).ok()?;
    if !file.ends_with(".rs") || file.chars().any(char::is_control) {
        return None;
    }
    Some(format!("{}:{line}:{column}", short_path(file)))
}

/// The callee a statement calls, when the statement is a call: `f(...)`,
/// `v = f(...)` or `return f(...)`.
///
/// # Arguments
///
/// * `t` - The line without indentation.
fn callee(t: &str) -> Option<&str> {
    let call = t
        .strip_prefix("return ")
        .or_else(|| t.split_once(" = ").map(|(_, c)| c))
        .unwrap_or(t);
    let (name, _) = call.split_once('(')?;
    (!name.is_empty()
        && name
            .chars()
            .all(|c| is_ident_char(c) || c == ':' || c == '~'))
    .then_some(name)
}

/// Writes the source location each call is handed beside it.
///
/// A call's arguments are read left to right and the first constant
/// address holding a location ([`location_at`]) is written as `// at
/// path:line:column`.
///
/// # Arguments
///
/// * `body` - The function's body.
/// * `program` - The image the locations are read from.
pub(super) fn annotate(body: &str, program: &Program) -> String {
    let mut out = String::with_capacity(body.len());
    for line in body.lines() {
        out.push_str(&with_location(line, program));
        out.push('\n');
    }
    out
}

/// A call line with the location its arguments hand over written beside
/// it, or the line as it was.
///
/// # Arguments
///
/// * `line` - One line of the body.
/// * `program` - The image the locations are read from.
fn with_location(line: &str, program: &Program) -> String {
    let t = line.trim_start();
    let call = t
        .strip_prefix("if (")
        .and_then(|r| r.rsplit_once(") "))
        .map_or(t, |(_, c)| c);
    if !t.ends_with(';') || callee(call).is_none() || line.contains("//") {
        return line.to_owned();
    }
    let args = call.split_once('(').map_or("", |(_, a)| a);
    let at = args
        .split(|c: char| !c.is_ascii_alphanumeric())
        .filter_map(|w| w.strip_prefix("0x"))
        .filter_map(|h| u64::from_str_radix(h, 16).ok())
        .find_map(|a| location_at(program, a));
    match at {
        Some(at) => format!("{line}  // at {at}"),
        None => line.to_owned(),
    }
}

/// The spaced arithmetic operators a checked statement computes with,
/// binary and compound.
const ARITH: [&str; 14] = [
    " + ", " - ", " * ", " / ", " % ", " << ", " >> ", " += ", " -= ", " *= ", " /= ", " %= ",
    " <<= ", " >>= ",
];

/// A check diamond: the failing call's callee, its arguments as written,
/// and whether the location was read back beside the call.
struct Diamond<'l> {
    /// The callee (`panic_bounds_check`, `panic_const_mul_overflow`).
    callee: &'l str,
    /// The call's arguments, in order, the location last.
    args: Vec<&'l str>,
    /// Whether the call line carries an `// at` note, which the last
    /// argument then is.
    located: bool,
}

/// Smallest constant a `core::panic::Location` address names: an offset
/// into the image, never a small operand a check guards.
const LOCATION_MIN: u64 = 0x1000;

/// The operands a check guards: the call's arguments less the trailing
/// location, read back beside the call or an address-shaped constant.
///
/// # Arguments
///
/// * `args` - The call's arguments, in order.
/// * `located` - Whether the call line carries an `// at` note.
fn without_location<'a>(args: &'a [&'a str], located: bool) -> &'a [&'a str] {
    let Some((last, operands)) = args.split_last() else {
        return args;
    };
    let is_location =
        located || parse_const(last).is_some_and(|v| v >= LOCATION_MIN && last.starts_with("0x"));
    if is_location { operands } else { args }
}

/// Tells whether a condition is one plain comparison, `l OP r` with one
/// operator and no logic around it, as the renderer writes one (`a1 >=
/// a2`, `mulhi64(a1, 4) != 0`).
///
/// # Arguments
///
/// * `cond` - The condition text.
fn is_plain_comparison(cond: &str) -> bool {
    /// The comparison operators.
    const RELS: [&str; 6] = ["==", "!=", ">=", "<=", ">", "<"];
    RELS.iter().any(|rel| {
        cond.split_once(&format!(" {rel} ")).is_some_and(|(l, r)| {
            RELS.iter()
                .all(|o| !l.contains(&format!(" {o} ")) && !r.contains(&format!(" {o} ")))
                && !l.contains(" && ")
                && !r.contains(" && ")
                && !l.contains(" || ")
                && !r.contains(" || ")
        })
    })
}

/// A bare call's callee and its arguments: `f(a, b)`, `return` apart.
///
/// # Arguments
///
/// * `t` - The statement without its semicolon.
///
/// # Returns
///
/// The callee and its argument texts in order, or `None` for anything
/// else around the call.
fn bare_call(t: &str) -> Option<(&str, Vec<&str>)> {
    let t = t.strip_prefix("return ").unwrap_or(t);
    let (name, _) = t.split_once('(')?;
    let close = matching_paren(t, name.len())?;
    if !t.ends_with(')')
        || close + 1 != t.len()
        || name.is_empty()
        || !name
            .chars()
            .all(|c| is_ident_char(c) || c == ':' || c == '~')
    {
        return None;
    }
    Some((name, split_arguments(&t[name.len() + 1..close])))
}

/// Reads the check diamond at `at`: `if (a plain comparison) {` whose
/// only statement is a call to a Rust panic entry, closed at the `if`'s
/// own depth with no `else`.
///
/// # Arguments
///
/// * `lines` - The body.
/// * `at` - The line the `if` may open.
///
/// # Returns
///
/// The diamond, or `None` for any other shape.
fn diamond_at<'l>(lines: &[&'l str], at: usize) -> Option<Diamond<'l>> {
    let line = lines.get(at)?;
    let t = line.trim_start();
    if !is_plain_comparison(if_opener(t)?) {
        return None;
    }
    let pad = indent_of(line);
    let call_line = lines.get(at + 1)?;
    if indent_of(call_line) <= pad {
        return None;
    }
    let close = lines.get(at + 2)?;
    if indent_of(close) != pad || close.trim() != "}" {
        return None;
    }
    let bare = call_line.trim_start();
    let located = bare.contains("// at ");
    let stmt = bare.split_once("//").map_or(bare, |(s, _)| s);
    let stmt = stmt.trim().strip_suffix(';')?.trim();
    let (callee, args) = bare_call(stmt)?;
    (callee == "panic_bounds_check"
        || (callee.starts_with("panic_const_") && callee.ends_with("_overflow")))
    .then_some(Diamond {
        callee,
        args,
        located,
    })
}

/// Tells whether a statement names an operand: the same word, or the same
/// number in another spelling (`4` and `0x4`).
///
/// # Arguments
///
/// * `t` - The statement without indentation.
/// * `operand` - The operand as the call wrote it.
fn operand_in(t: &str, operand: &str) -> bool {
    mentions_ident(t, operand)
        || parse_const(operand).is_some_and(|v| tokens(t).any(|w| parse_const(w) == Some(v)))
}

/// Tells whether a statement negates an operand, `-x`, the arithmetic a
/// `panic_const_neg_overflow` guards.
///
/// # Arguments
///
/// * `t` - The statement without indentation.
/// * `operand` - The operand as the call wrote it.
fn negates(t: &str, operand: &str) -> bool {
    word_positions(t, operand)
        .iter()
        .any(|&p| t[..p].ends_with('-'))
}

/// Tells whether a statement is the one the check guards.
///
/// A bounds check's statement indexes with the checked index (`...[idx`);
/// an overflow check's computes with every checked operand under an
/// arithmetic operator, or negates its one operand.
///
/// # Arguments
///
/// * `t` - The statement without indentation.
/// * `d` - The check.
fn guards_statement(t: &str, d: &Diamond<'_>) -> bool {
    if d.callee == "panic_bounds_check" {
        return d.args.first().is_some_and(|idx| {
            word_positions(t, idx)
                .iter()
                .any(|&p| t[..p].ends_with('['))
        });
    }
    let operands = without_location(&d.args, d.located);
    !operands.is_empty()
        && operands.iter().all(|o| operand_in(t, o))
        && (ARITH.iter().any(|op| t.contains(op)) || operands.iter().any(|o| negates(t, o)))
}

/// Finds the statement a check diamond guards.
///
/// The first one after it at the diamond's own depth, stopping where
/// control flow could reach the rest unguarded (a branch, a loop, a
/// label, a jump or a return that does not itself index or compute with
/// the operands).
///
/// # Arguments
///
/// * `lines` - The body.
/// * `from` - The first line after the diamond.
/// * `pad` - The diamond's indentation.
/// * `d` - The check.
///
/// # Returns
///
/// The guarded statement's line, or `None` when none follows guarded.
fn guarded_statement(lines: &[&str], from: usize, pad: usize, d: &Diamond<'_>) -> Option<usize> {
    for (j, line) in lines.iter().enumerate().skip(from) {
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        if indent_of(line) != pad
            || t.starts_with('}')
            || t.ends_with('{')
            || is_label(t)
            || is_case(t)
            || t.contains("goto")
            || !t.ends_with(';')
        {
            return None;
        }
        if guards_statement(t, d) {
            return Some(j);
        }
        if transfers(line) {
            return None;
        }
    }
    None
}

/// Folds Rust's overflow and bounds checks out of a body.
///
/// A check diamond whose guarded statement follows ([`guarded_statement`])
/// leaves whole, and that statement gains `/* checked */` or
/// `/* bounds-checked */`; where none follows, the block stays and the
/// call alone becomes `/* overflow panics */` or `/* bounds panic */`.
/// The callees whose calls left either way are returned for the header.
///
/// # Arguments
///
/// * `body` - The body, the locations already written beside the calls.
///
/// # Returns
///
/// The folded body and the callees whose calls left it.
pub(super) fn fold_checks(body: &str) -> (String, Vec<String>) {
    let lines: Vec<&str> = body.lines().collect();
    let mut gone: Vec<bool> = vec![false; lines.len()];
    let mut replaces: Vec<Option<&'static str>> = vec![None; lines.len()];
    let mut tails: Vec<Option<String>> = vec![None; lines.len()];
    let mut callees: Vec<String> = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let Some(d) = diamond_at(&lines, i) else {
            i += 1;
            continue;
        };
        let bounds = d.callee == "panic_bounds_check";
        match guarded_statement(&lines, i + 3, indent_of(lines[i]), &d) {
            Some(at) => {
                gone[i] = true;
                gone[i + 1] = true;
                gone[i + 2] = true;
                let note = if bounds {
                    "  /* bounds-checked */"
                } else {
                    "  /* checked */"
                };
                match &mut tails[at] {
                    Some(t) if !t.contains(note.trim()) => t.push_str(note),
                    Some(_) => {}
                    None => tails[at] = Some(note.to_owned()),
                }
            }
            None => {
                replaces[i + 1] = Some(if bounds {
                    "/* bounds panic */"
                } else {
                    "/* overflow panics */"
                });
            }
        }
        if !callees.iter().any(|c| c == d.callee) {
            callees.push(d.callee.to_owned());
        }
        i += 3;
    }
    let mut out = String::with_capacity(body.len());
    for (j, line) in lines.iter().enumerate() {
        if gone[j] {
            continue;
        }
        if let Some(note) = replaces[j] {
            out.push_str(&line[..indent_of(line)]);
            out.push_str(note);
        } else {
            out.push_str(line);
            if let Some(tail) = &tails[j] {
                out.push_str(tail);
            }
        }
        out.push('\n');
    }
    (out, callees)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{annotate, fold_checks, location_at, short_path};
    use crate::program::{Arch, Program, Section};

    /// An image holding a file name at `0x2000` and a location naming it
    /// at `0x2100`.
    fn image() -> Program {
        let mut bytes = vec![0u8; 0x200];
        let file = br"C:\Users\me\.cargo\registry\src\index.crates.io-1949cf8c6b5b557f\rhai-1.26.1\src\parser.rs";
        bytes[..file.len()].copy_from_slice(file);
        let len = u64::try_from(file.len()).expect("a short path");
        bytes[0x100..0x108].copy_from_slice(&0x2000u64.to_le_bytes());
        bytes[0x108..0x110].copy_from_slice(&len.to_le_bytes());
        bytes[0x110..0x114].copy_from_slice(&1015u32.to_le_bytes());
        bytes[0x114..0x118].copy_from_slice(&32u32.to_le_bytes());
        let data = Section::mapped(".rdata", 0x2000, 0, 0x200, false, false);
        Program::raw(bytes, Arch::X86_64, 0, None, vec![data])
    }

    /// A location reads back as its crate's path, line and column, and
    /// bytes that are no location read as none.
    #[test]
    fn a_location_reads_back_as_path_line_and_column() {
        let p = image();
        assert_eq!(
            location_at(&p, 0x2100).as_deref(),
            Some("rhai-1.26.1/src/parser.rs:1015:32")
        );
        assert_eq!(location_at(&p, 0x2000), None);
        assert_eq!(
            short_path("/rustc/abc/library/core/src/slice/mod.rs"),
            "core/src/slice/mod.rs"
        );
    }

    /// A call handed a location carries it beside it; a constant that is
    /// no location leaves its line as it was.
    #[test]
    fn a_call_handed_a_location_carries_it() {
        let p = image();
        let body = "if (a1 >= a3) {\n  panic_bounds_check(a1, a3, 0x2100);\n}\nreturn f(0x2000);\n";
        assert_eq!(
            annotate(body, &p),
            "if (a1 >= a3) {\n  panic_bounds_check(a1, a3, 0x2100);  // at rhai-1.26.1/src/parser.rs:1015:32\n}\nreturn f(0x2000);\n"
        );
    }

    /// A checked multiply's diamond leaves whole, and the multiply after
    /// it gains the note; the callee whose call left is returned.
    #[test]
    fn a_mul_overflow_diamond_folds_onto_the_multiply() {
        let body = "if (mulhi64(a1, 4) != 0) {\n  \
                    panic_const_mul_overflow(a1, 4, 0x2100);  // at rhai-1.26.1/src/parser.rs:1015:32\n\
                    }\n\
                    rax = a1 * 4;\n\
                    return rax;\n";
        let (out, callees) = fold_checks(body);
        assert_eq!(out, "rax = a1 * 4;  /* checked */\nreturn rax;\n", "{out}");
        assert_eq!(callees, vec!["panic_const_mul_overflow".to_owned()]);
    }

    /// A checked add's diamond folds onto a compound increment, and a
    /// negation check onto the statement that negates.
    #[test]
    fn an_add_overflow_diamond_folds_onto_the_increment() {
        let body = "while (1) {\n  if (uaddo64(i, 1) != 0) {\n    \
                    panic_const_add_overflow(i, 1, 0x2100);  // at core/src/num/int_macros.rs:2100:9\n  \
                    }\n  \
                    i += 1;\n\
                    }\n";
        let (out, callees) = fold_checks(body);
        assert!(
            out.contains("i += 1;  /* checked */") && !out.contains("panic_const"),
            "{out}"
        );
        assert_eq!(callees, vec!["panic_const_add_overflow".to_owned()]);
        let neg = "if (a2 != 0) {\n  panic_const_neg_overflow(a2, 0x2100);\n}\nrax = -a2;\n";
        let (out, _) = fold_checks(neg);
        assert_eq!(out, "rax = -a2;  /* checked */\n", "{out}");
    }

    /// A bounds check's diamond leaves whole, and the indexing statement
    /// after it gains the note.
    #[test]
    fn a_bounds_diamond_folds_onto_the_indexing() {
        let body = "if (a1 >= a2) {\n  \
                    panic_bounds_check(a1, a2, 0x2100);  // at library/core/src/slice/index.rs:2100:9\n\
                    }\n\
                    return ((uint64_t*)a3)[a1];\n";
        let (out, callees) = fold_checks(body);
        assert_eq!(
            out, "return ((uint64_t*)a3)[a1];  /* bounds-checked */\n",
            "{out}"
        );
        assert_eq!(callees, vec!["panic_bounds_check".to_owned()]);
    }

    /// A diamond whose `if` holds more than the call stays as it was.
    #[test]
    fn a_diamond_with_an_extra_statement_stays() {
        let body = "if (a1 >= a2) {\n  panic_bounds_check(a1, a2, 0x2100);\n  rax = 1;\n}\n\
                    return ((uint64_t*)a3)[a1];\n";
        let (out, callees) = fold_checks(body);
        assert_eq!(out, body);
        assert!(callees.is_empty());
    }

    /// A diamond nothing guarded follows keeps its block, and the call
    /// alone becomes the note; the callee still left the text.
    #[test]
    fn an_unmatched_diamond_keeps_its_block() {
        let body = "if (mulhi64(a1, 4) != 0) {\n  \
                    panic_const_mul_overflow(a1, 4, 0x2100);\n\
                    }\n\
                    return f(a1);\n";
        let (out, callees) = fold_checks(body);
        assert_eq!(
            out, "if (mulhi64(a1, 4) != 0) {\n  /* overflow panics */\n}\nreturn f(a1);\n",
            "{out}"
        );
        assert_eq!(callees, vec!["panic_const_mul_overflow".to_owned()]);
        let bounds = "if (a1 >= a2) {\n  panic_bounds_check(a1, a2, 0x2100);\n}\nreturn a2;\n";
        let (out, callees) = fold_checks(bounds);
        assert_eq!(
            out, "if (a1 >= a2) {\n  /* bounds panic */\n}\nreturn a2;\n",
            "{out}"
        );
        assert_eq!(callees, vec!["panic_bounds_check".to_owned()]);
    }
}
