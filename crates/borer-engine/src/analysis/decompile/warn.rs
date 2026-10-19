//! The `// warn:` line of a `decompile` answer: what keeps a function's
//! text from being the C it claims, each in a few words.
//!
//! Every warning is a fact of the text itself that a compiler would refuse
//! or a reader cannot fill in: a computed `goto`, a name read that nothing
//! declares, a call to a function of the binary with no prototype, a
//! helper called without its definition, an operator C does not apply to
//! a float or a pointer, a `goto` to a missing label, an instruction left
//! as `/* asm */`. None is a guess about the text, so a function with no
//! `// warn:` line is not thereby right, but one with it is wrong where it
//! says. The names come from the typed tree ([`cir::check`]) of the body,
//! the declarations from the lines above it. A line the tree cannot read
//! and a name that is no C identifier (`Class::method`) are not flagged:
//! vector code and C++ names read that way and are often right.

use super::cir::{self, Holds, Violation};
use super::helper::Helper;
use super::traces::INTRINSICS;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

/// Most names one warning lists before it counts the rest.
const NAMES_SHOWN: usize = 4;

/// The names C23 and its headers give a value without a declaration in
/// the function.
const CONSTANTS: [&str; 4] = ["true", "false", "nullptr", "NULL"];

/// The prefix of the line [`line()`] writes.
pub(super) const WARN: &str = "// warn:";

/// Writes the `// warn:` line of a finished text, `None` when nothing in
/// it is known wrong.
///
/// The text's declarations are the lines before its first empty line, the
/// body the lines after; a text with no empty line has no body to check
/// and gets only the `/* asm */` count.
///
/// # Arguments
///
/// * `text` - The text as `decompile_named` wrote it, before any marks.
/// * `in_binary` - The names of the functions of the binary the function
///   calls, its own name left out: a call to one of them the text does not
///   declare guesses its arguments and result.
/// * `word` - The machine word's width in bits, which says which helpers
///   need a definition.
///
/// # Returns
///
/// The line without its newline, or `None`.
pub(super) fn line(text: &str, in_binary: &BTreeSet<String>, word: u8) -> Option<String> {
    let lines: Vec<&str> = text.lines().collect();
    let base = lines.iter().position(|l| l.trim().is_empty());
    let body_lines = base.map_or(&lines[..], |b| lines.get(b + 1..).unwrap_or(&[]));
    let asm = body_lines
        .iter()
        .filter(|l| l.trim_start().starts_with("/* asm"))
        .count();
    let mut items: Vec<String> = Vec::new();
    if let Some(b) = base {
        let head = lines.get(..b).unwrap_or(&[]);
        let declared = declarations(head);
        let mut body = body_lines.join("\n");
        body.push('\n');
        items = found(&cir::check(&cir::build(&body), &declared), in_binary, word);
    }
    if asm > 0 {
        let what = if asm == 1 {
            "instruction: not modeled, so its effect is missing"
        } else {
            "instructions: not modeled, so their effects are missing"
        };
        items.push(format!("asm {asm} {what}"));
    }
    (!items.is_empty()).then(|| format!("{WARN} {}", items.join("; ")))
}

/// Turns the violations of a body into warnings, one per kind.
///
/// # Arguments
///
/// * `violations` - What [`cir::check`] found.
/// * `in_binary` - As [`line()`] takes it.
/// * `word` - As [`line()`] takes it.
///
/// # Returns
///
/// The warnings, in a fixed order of kinds.
fn found(violations: &[Violation], in_binary: &BTreeSet<String>, word: u8) -> Vec<String> {
    let (mut gotos, mut reads, mut callees, mut helpers, mut ops, mut labels) = (
        0usize,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    for v in violations {
        match v {
            Violation::ComputedGoto(_) => gotos += 1,
            Violation::Undeclared(n) => reads.push(n.clone()),
            Violation::UndeclaredCall(n) => match Helper::parse(n) {
                Some(h) if !h.define(word).is_empty() => helpers.push(n.clone()),
                Some(_) => {}
                None if INTRINSICS.contains(&n.as_str()) => {}
                None if n.starts_with("sub_") || in_binary.contains(n) => {
                    callees.push(n.clone());
                }
                None => {}
            },
            Violation::BadOperand(op, holds) => {
                let what = match holds {
                    Holds::Float => "a float",
                    Holds::Pointer => "a pointer",
                    Holds::Integer => "an integer",
                    Holds::Other => "a value",
                };
                ops.push(format!("{op} on {what}"));
            }
            Violation::DanglingGoto(l) => labels.push(format!("L_{:x}", l.0)),
            Violation::NotIdent(_) | Violation::Raw(_) => {}
        }
    }
    let mut out = Vec::new();
    if gotos > 0 {
        out.push(format!(
            "goto * {gotos}x: an indirect jump whose targets were not recovered"
        ));
    }
    if !callees.is_empty() {
        out.push(format!(
            "callee {}: no prototype in the text, so arguments and result are guesses",
            listed(&callees)
        ));
    }
    if !helpers.is_empty() {
        out.push(format!(
            "helper {}: called but not defined",
            listed(&helpers)
        ));
    }
    if !reads.is_empty() {
        out.push(format!(
            "undeclared {}: read but declared nowhere",
            listed(&reads)
        ));
    }
    if !ops.is_empty() {
        out.push(format!(
            "operand {}: not C, so a type in the text is wrong",
            listed(&ops)
        ));
    }
    if !labels.is_empty() {
        out.push(format!(
            "label {}: a goto to a label the text lacks",
            listed(&labels)
        ));
    }
    out
}

/// Lists names, at most [`NAMES_SHOWN`] of them, then how many more.
///
/// # Arguments
///
/// * `names` - The names, in order.
///
/// # Returns
///
/// The names joined by `, `.
fn listed(names: &[String]) -> String {
    let mut out = names
        .iter()
        .take(NAMES_SHOWN)
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join(", ");
    let more = names.len().saturating_sub(NAMES_SHOWN);
    if more > 0 {
        let _ = write!(out, " (+{more} more)");
    }
    out
}

/// Reads the names a text's declaration lines declare, each with what it
/// holds.
///
/// Every identifier on a line that is code, and on the `// signature:`
/// line, counts as declared, so a type, a helper or a macro the lines
/// define is never taken for an undeclared read. The parameters of the
/// signature and the names of a plain declaration (`uint32_t a, *b;`) then
/// get what their type holds.
///
/// # Arguments
///
/// * `head` - The lines before the body.
///
/// # Returns
///
/// The names, each with what it holds.
fn declarations<'t>(head: &[&'t str]) -> BTreeMap<&'t str, Holds> {
    let mut out: BTreeMap<&'t str, Holds> = CONSTANTS.iter().map(|c| (*c, Holds::Other)).collect();
    for l in head {
        let sig = l.strip_prefix("// signature: ");
        if sig.is_none() && l.trim_start().starts_with("//") {
            continue;
        }
        let code = sig.unwrap_or(l);
        for word in identifiers(code) {
            out.entry(word).or_insert(Holds::Other);
        }
        if let Some(sig) = sig {
            for (name, holds) in parameters(sig) {
                out.insert(name, holds);
            }
        } else {
            for (name, holds) in declared_names(code) {
                out.insert(name, holds);
            }
        }
    }
    out
}

/// The identifiers of a line of C, string and character literals skipped.
///
/// # Arguments
///
/// * `code` - The line.
///
/// # Returns
///
/// Each identifier, in order.
fn identifiers(code: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut start: Option<usize> = None;
    let mut quote: Option<char> = None;
    let mut escaped = false;
    for (i, c) in code
        .char_indices()
        .chain(std::iter::once((code.len(), ' ')))
    {
        if let Some(q) = quote {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == q {
                quote = None;
            }
            continue;
        }
        if c.is_ascii_alphanumeric() || c == '_' {
            start.get_or_insert(i);
            continue;
        }
        if let Some(s) = start.take()
            && let Some(w) = code.get(s..i)
            && w.starts_with(|f: char| !f.is_ascii_digit())
        {
            out.push(w);
        }
        if c == '"' || c == '\'' {
            quote = Some(c);
        }
    }
    out
}

/// The parameters of a signature, each with what it holds.
///
/// # Arguments
///
/// * `sig` - The signature, `ret name(type a1, type *a2)`.
///
/// # Returns
///
/// Each named parameter with what its type holds.
fn parameters(sig: &str) -> Vec<(&str, Holds)> {
    let Some((open, close)) = sig.find('(').zip(sig.rfind(')')) else {
        return Vec::new();
    };
    let Some(inner) = sig.get(open + 1..close) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let (mut depth, mut from) = (0usize, 0usize);
    for (i, c) in inner
        .char_indices()
        .chain(std::iter::once((inner.len(), ',')))
    {
        match c {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                if let Some(p) = inner.get(from..i) {
                    out.extend(parameter(p.trim()));
                }
                from = i + 1;
            }
            _ => {}
        }
    }
    out
}

/// One parameter's name and what it holds.
///
/// # Arguments
///
/// * `p` - The parameter as the signature spells it: `uint32_t a1`,
///   `void *a2`, `uint64_t (*a3)(uint64_t)`.
///
/// # Returns
///
/// The name and what it holds, `None` for `void`, `...` or an unnamed one.
fn parameter(p: &str) -> Option<(&str, Holds)> {
    if let Some((_, rest)) = p.split_once("(*") {
        let name = identifiers(rest).into_iter().next()?;
        return Some((name, Holds::Pointer));
    }
    let name = identifiers(p).into_iter().last()?;
    let ty = p.get(..p.len().checked_sub(name.len())?)?.trim();
    if ty.is_empty() || !p.ends_with(name) {
        return None;
    }
    let holds = if ty.ends_with('*') {
        Holds::Pointer
    } else {
        Holds::of(&cir::CTy::parse(ty))
    };
    Some((name, holds))
}

/// The names a plain declaration line declares, each with what it holds:
/// `uint32_t a, *b, c[4]; // note`.
///
/// # Arguments
///
/// * `code` - The line.
///
/// # Returns
///
/// Each name with what it holds; nothing for a line that is no plain
/// declaration (a typedef, a helper's definition, a macro).
fn declared_names(code: &str) -> Vec<(&str, Holds)> {
    let code = code.split_once("//").map_or(code, |(c, _)| c).trim();
    let Some(code) = code.strip_suffix(';') else {
        return Vec::new();
    };
    if code.starts_with("typedef ")
        || code.starts_with("static ")
        || code.starts_with("extern ")
        || code.starts_with('#')
        || code.contains(['(', '{', '='])
    {
        return Vec::new();
    }
    let mut parts = code.split(',');
    let Some((ty, first)) = parts.next().and_then(|p| p.trim().rsplit_once(' ')) else {
        return Vec::new();
    };
    let ty = ty.trim();
    let base = if ty.ends_with('*') {
        Holds::Pointer
    } else {
        Holds::of(&cir::CTy::parse(ty))
    };
    std::iter::once(first)
        .chain(parts)
        .filter_map(|n| {
            let n = n.trim();
            let bare = n.trim_start_matches('*');
            let (name, array) = bare
                .split_once('[')
                .map_or((bare, false), |(n, _)| (n, true));
            let holds = if array || bare.len() < n.len() {
                Holds::Pointer
            } else {
                base
            };
            cir::Ident::new(name).map(|_| (name, holds))
        })
        .collect()
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::line;
    use std::collections::BTreeSet;

    /// The binary's functions a test text calls.
    fn in_binary() -> BTreeSet<String> {
        ["h_is_odd".to_owned()].into_iter().collect()
    }

    /// A text a compiler takes whole gets no line: parameters, locals,
    /// helpers it defines, its own name and C's library are all declared.
    #[test]
    fn a_text_that_is_c_gets_no_warning() {
        let text = "// f @ 0x1000: 3 instructions, 1 blocks\n\
                    // signature: uint64_t f(uint64_t a1, double *a2)\n\
                    static inline uint64_t rotr64(uint64_t x, uint64_t n) { return x; }\n\
                    float local_8;\n\
                    uint32_t var1, *var2;\n\
                    \n\
                    var1 = rotr64(a1, 3) & 0xff;\n\
                    local_8 = (float)*a2 + 1.5;\n\
                    var2 = (uint32_t*)a2 + 1;\n\
                    if (var2 != nullptr) {\n\
                      return f(a1 - 1) + strlen(\"x\");\n\
                    }\n\
                    return llabs(var1);\n";
        assert_eq!(line(text, &in_binary(), 64), None);
    }

    /// Each kind of fault is named with what it means, in a fixed order.
    #[test]
    fn each_fault_is_named_with_what_it_means() {
        let text = "// f @ 0x1000: 3 instructions, 1 blocks\n\
                    // signature: float f(void *a1)\n\
                    float local_8;\n\
                    \n\
                    /* asm: scvtf s1, s0 */\n\
                    local_8 = ((float)local_8 + 1.0) & 0xffffffff;\n\
                    local_8 = h_is_odd(a1) + sub_4010(v1) + rotr64(a1, 2) + puts(\"x\");\n\
                    if (FLAGS_UNKNOWN) goto L_1010;\n\
                    goto *(a1 & 7);\n\
                    return local_8;\n";
        let got = line(text, &in_binary(), 64).unwrap_or_default();
        assert_eq!(
            got,
            "// warn: goto * 1x: an indirect jump whose targets were not recovered; \
             callee h_is_odd, sub_4010: no prototype in the text, so arguments and result are guesses; \
             helper rotr64: called but not defined; \
             undeclared v1, FLAGS_UNKNOWN: read but declared nowhere; \
             operand & on a float: not C, so a type in the text is wrong; \
             label L_1010: a goto to a label the text lacks; \
             asm 1 instruction: not modeled, so its effect is missing"
        );
    }

    /// A text with no empty line has no body to read, and is not flagged
    /// for names it may well declare.
    #[test]
    fn a_text_with_no_body_is_not_read_for_names() {
        assert_eq!(line("// f\nx = y;\n", &in_binary(), 64), None);
    }
}
