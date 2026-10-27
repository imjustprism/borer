//! The pointer types the functions a parameter is passed to give their own
//! parameters.
//!
//! `sub_621f(a1, ...)` says nothing of `a1` until `sub_621f`'s own body
//! does: it hands its first parameter to `strcmp`, so its signature reads
//! `char *a1`, and so is the value passed to it. The notes are
//! `// callee sub_621f: char *|-` lines, one type per parameter of the
//! callee (`-` for one that is no pointer to a named type), for the type
//! pass to read and then drop.
//!
//! A callee's types come from its own text with these notes left out, so
//! they are what its body shows of its parameters and no caller's guess
//! is passed on, and no text waits on one that waits on it.

use super::super::lexer::{Lex, Line, lex};
use super::super::passes::Pass;
use super::*;
use crate::analysis::typelib;

/// Most callees one function's notes name.
const CALLEES_MAX: usize = 8;

/// Most instructions a callee may have for its own text to be built for a
/// caller's notes.
const CALLEE_INSTRUCTIONS_MAX: usize = 1024;

/// Bytes a callee's parameter types are charged in the memo.
const TYPES_WEIGHT: usize = 256;

/// Writes the callee notes under the signature line.
///
/// A callee is named when one of the function's parameters still typed
/// only by its width (the machine word or `void *`) is passed to it
/// whole, the callee is a function of the image (not one the type library
/// declares, nor the function itself), and its own text gives one of its
/// parameters a pointer to a named type.
///
/// # Arguments
///
/// * `text` - The function as the type pass is about to read it.
/// * `word` - The machine word's type.
/// * `callers` - The image, the analysis, the names in force and the
///   function. `None` leaves the text as it is.
///
/// # Returns
///
/// The text with one note per callee that types a parameter.
pub(super) fn noted(text: &str, word: &str, callers: Option<Scope<'_>>) -> String {
    let Some(scope) = callers else {
        return text.to_owned();
    };
    let notes = callee_lines(text, word, scope);
    if notes.is_empty() {
        return text.to_owned();
    }
    let mut out = String::with_capacity(text.len().saturating_add(notes.len().saturating_mul(64)));
    let mut placed = false;
    for line in text.lines() {
        out.push_str(line);
        out.push('\n');
        if !placed && line.starts_with("// signature: ") {
            for note in &notes {
                out.push_str(note);
                out.push('\n');
            }
            placed = true;
        }
    }
    if placed { out } else { text.to_owned() }
}

/// What a callee note is built from: the image, the analysis, the names
/// in force and the function's entry.
pub(super) type Scope<'a> = (&'a Program, &'a Analysis, &'a Overlay, u64);

/// The callee notes of a text ([`noted`]).
///
/// # Arguments
///
/// * `text` - The function, header lines included.
/// * `word` - The machine word's type.
/// * `scope` - What the notes are built from.
///
/// # Returns
///
/// The notes, in the order the text first passes a parameter to each
/// callee.
fn callee_lines(text: &str, word: &str, scope: Scope<'_>) -> Vec<String> {
    let (program, analysis, overlay, entry) = scope;
    let untyped: Vec<String> = signature_params(text)
        .into_iter()
        .filter(|(_, ty)| ty == word || ty == "void *")
        .map(|(name, _)| name)
        .collect();
    if untyped.is_empty() {
        return Vec::new();
    }
    let mut named: Vec<(String, u64)> = Vec::new();
    for line in text.lines().filter(|l| !l.starts_with("//")) {
        let l = Line {
            text: line,
            toks: lex(line),
        };
        for k in 0..l.toks.len() {
            if l.toks.get(k).is_none_or(|t| t.lex != Lex::Name)
                || !untyped.iter().any(|p| p == l.word(k))
            {
                continue;
            }
            let Some((callee, _, _)) = evidence::argument_of(&l, k) else {
                continue;
            };
            if named.iter().any(|(n, _)| n == callee)
                || typelib::declared(callee, program.format).is_some()
            {
                continue;
            }
            if let Some(g) =
                unit::function_named(program, analysis, overlay, callee).filter(|&g| g != entry)
            {
                named.push((callee.to_owned(), g));
            }
        }
        if named.len() >= CALLEES_MAX {
            break;
        }
    }
    named
        .into_iter()
        .take(CALLEES_MAX)
        .filter_map(|(name, g)| {
            let types = pointer_params(program, analysis, overlay, g);
            types.iter().any(Option::is_some).then(|| {
                let spelled: Vec<&str> =
                    types.iter().map(|t| t.as_deref().unwrap_or("-")).collect();
                format!("// callee {name}: {}", spelled.join("|"))
            })
        })
        .collect()
}

/// The pointer to a named type a function's own text gives each of its
/// parameters, built once per function under the names in force through
/// [`Analysis::derived`].
///
/// The text is the function's own, polished up to its parameter types
/// with the callee notes left out, so its types are what its body shows.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - The names in force, and the passes left out.
/// * `entry` - The callee's entry.
///
/// # Returns
///
/// One entry per parameter: the type as the signature spells it, or
/// `None` for one that is no pointer to a named type. Empty for a callee
/// too large to build a text for, or one with no text.
fn pointer_params(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> std::sync::Arc<Vec<Option<String>>> {
    analysis.derived.get_or_build_item(
        "callee_pointers",
        overlay.fingerprint(),
        entry,
        || {
            if analysis
                .function(entry)
                .is_none_or(|f| f.entry != entry || f.instr_count > CALLEE_INSTRUCTIONS_MAX)
            {
                return Vec::new();
            }
            let d = decompiled_cached(program, analysis, overlay, overlay.fingerprint(), entry);
            let Some(d) = d.as_ref().as_ref() else {
                return Vec::new();
            };
            let skip = Pass::ALL
                .iter()
                .skip_while(|p| **p != Pass::TypeLocals)
                .fold(overlay.passes.without(Pass::CalleeTypes), |s, p| {
                    s.without(*p)
                });
            let own = polish_at(&d.text, skip, program, analysis, overlay, entry);
            signature_params(&own)
                .into_iter()
                .map(|(_, ty)| named_pointer(&ty))
                .collect()
        },
        |_| TYPES_WEIGHT,
    )
}

/// The type a signature gives a parameter, when it is a pointer to a
/// named type: not `void *`, nor a function pointer.
///
/// # Arguments
///
/// * `ty` - The parameter's type as the signature spells it.
fn named_pointer(ty: &str) -> Option<String> {
    let ty = ty.trim();
    (ty.ends_with('*') && !ty.contains('(') && ty.trim_end_matches(['*', ' ']) != "void")
        .then(|| ty.to_owned())
}
