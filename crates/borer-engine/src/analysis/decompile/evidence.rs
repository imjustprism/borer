//! Names and types from evidence.
//!
//! The variables the webs pass made (`var1` to `varN`, [`super::vars`])
//! are named and typed by what the text shows they hold, the constants an
//! API takes are named by the group its declaration gives, and the test of
//! a call that answers yes or no is spelled as the call.
//!
//! First match wins, as a reader names them: the parameter of a declared
//! API a variable is passed to whole (`hKey`), the field a variable is
//! loaded from (`count` from `p->count`), and what its type says it holds
//! (`fp` for a C stream, `hFile` for the handle `CreateFileW` hands back).
//! A `for` loop's counter no line outside the loop names is `i`, `j` or
//! `k` by how deep the loop nests. A name the text already holds takes a
//! number or the next letter, so nothing shadows a function, a global or
//! a parameter, and a variable no evidence names keeps its number. Names
//! are spelling: no line reads anything else for them.

use super::lexer::{Lex, Line, lex};
use super::vars::{declaration, is_var_name, parts};
use super::*;
use crate::analysis::typelib::{self, Decl, Os, Pass};
use crate::program::BinaryFormat;

/// The kinds of evidence, strongest first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Rank {
    /// Passed whole as a declared API's parameter.
    Param,
    /// Loaded from a named field.
    Field,
    /// Holding a C stream or a handle, by the API's declared types.
    Type,
}

/// The names a loop counter takes, by how deep its loop nests, the next
/// one when the text already holds the first.
const COUNTERS: [&str; 5] = ["i", "j", "k", "m", "n"];

/// The verbs a handle API's name opens with, whose rest names the handle.
const HANDLE_VERBS: [&str; 6] = ["Create", "Open", "Get", "Duplicate", "Find", "Load"];

/// The type a C stream has, as the type library spells it.
const STREAM: &str = "FILE *";

/// The handle types a run reads as a pointer to nothing: what one holds
/// and how it compares are a machine word's.
const VOID_POINTERS: [&str; 8] = [
    "HANDLE",
    "HMODULE",
    "HINSTANCE",
    "HKEY",
    "PVOID",
    "LPVOID",
    "LPCVOID",
    "void *",
];

/// Words a name may not be: C's keywords and the type words a cast spells.
const RESERVED: [&str; 34] = [
    "if", "else", "while", "for", "do", "switch", "case", "default", "return", "goto", "break",
    "continue", "sizeof", "this", "int", "char", "short", "long", "void", "float", "double",
    "signed", "unsigned", "const", "struct", "union", "enum", "static", "uint64_t", "int64_t",
    "size_t", "bool", "true", "false",
];

/// The declaration of a function the text calls: a Windows binary's row,
/// else a POSIX one's. The C library's rows name their parameters `s` and
/// `n`, which tell a reader nothing, so they give no names.
///
/// # Arguments
///
/// * `name` - The callee's name.
fn decl(name: &str) -> Option<&'static Decl> {
    typelib::declared(name, BinaryFormat::Pe)
        .or_else(|| typelib::declared(name, BinaryFormat::Elf))
        .filter(|d| d.os != Os::C)
}

/// Any declaration of a function the text calls, the C library's rows
/// included, with the format whose rows it is.
///
/// # Arguments
///
/// * `name` - The callee's name.
fn any_decl(name: &str) -> Option<(&'static Decl, BinaryFormat)> {
    typelib::declared(name, BinaryFormat::Pe)
        .map(|d| (d, BinaryFormat::Pe))
        .or_else(|| typelib::declared(name, BinaryFormat::Elf).map(|d| (d, BinaryFormat::Elf)))
}

/// Tells whether a word can name a variable: an identifier no pass reads
/// as a register, a parameter, a slot, a temporary, a keyword, a type or
/// a constant.
///
/// # Arguments
///
/// * `w` - The word.
fn nameable(w: &str) -> bool {
    is_ident(w)
        && w.starts_with(|c: char| c.is_ascii_alphabetic())
        && !is_register_name(w)
        && !is_param_name(w)
        && !is_global_name(w)
        && !is_var_name(w)
        && !w
            .bytes()
            .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'_')
        && !["local_", "home_", "arg_", "field_", "sub_", "tmp_"]
            .iter()
            .any(|p| w.starts_with(p))
        && narrow_type(w).is_none()
        && !RESERVED.contains(&w)
}

/// The call a whole argument at token `k` is passed to, and its position.
///
/// # Arguments
///
/// * `l` - The line.
/// * `k` - The token.
///
/// # Returns
///
/// The callee's name and the argument's index from zero, or `None` when
/// the token is not a whole argument of a call by a plain name.
fn argument_of<'t>(l: &Line<'t>, k: usize) -> Option<(&'t str, usize)> {
    let prev = k.checked_sub(1)?;
    if !(l.is(prev, "(") || l.is(prev, ",")) || !(l.is(k + 1, ")") || l.is(k + 1, ",")) {
        return None;
    }
    let (mut depth, mut commas, mut p) = (0usize, 0usize, k);
    let open = loop {
        p = p.checked_sub(1)?;
        if l.is(p, ")") || l.is(p, "]") {
            depth += 1;
        } else if l.is(p, "(") || l.is(p, "[") {
            if depth == 0 {
                break p;
            }
            depth -= 1;
        } else if depth == 0 && l.is(p, ",") {
            commas += 1;
        }
    };
    let c = open.checked_sub(1)?;
    let t = l.toks.get(c)?;
    let qualified = c
        .checked_sub(1)
        .is_some_and(|q| l.is(q, "::") || l.is(q, "->") || l.is(q, "."));
    (l.is(open, "(") && t.lex == Lex::Name && !qualified)
        .then(|| (l.text.get(t.at..t.end).unwrap_or(""), commas))
}

/// A whole-line assignment to one variable: `v = rhs;`.
///
/// # Arguments
///
/// * `l` - The line.
///
/// # Returns
///
/// The variable and the right side, or `None`.
fn assignment<'t>(l: &Line<'t>) -> Option<(&'t str, &'t str)> {
    let (lhs, rhs) = l.text.trim().strip_suffix(';')?.split_once(" = ")?;
    (is_var_name(lhs) && !rhs.contains(" = ")).then_some((lhs, rhs))
}

/// Names and types the variables the webs pass made from the evidence the
/// text holds, names the constants declared APIs take, and spells the
/// tests of yes-or-no APIs as the call.
///
/// # Arguments
///
/// * `text` - A decompiled function after the webs pass and the typing.
/// * `word` - The machine word in bits (32 or 64).
///
/// # Returns
///
/// The text renamed, or unchanged when no evidence says anything.
pub(super) fn name_vars(text: &str, word: u8) -> String {
    let typed = retype(text, word).unwrap_or_else(|| text.to_owned());
    let named = rename(&typed).unwrap_or(typed);
    let constants = name_constants(&named, word).unwrap_or(named);
    bool_tests(&constants).unwrap_or(constants)
}

/// Types the variables whose every value is a handle or pointer API's
/// result, of one type, by that type (`HANDLE` where `uint64_t` said only
/// how wide).
///
/// A variable takes the type only when every write is `v = Api(...)` with
/// that declared result, it is declared at the machine word (a narrower
/// declaration says its uses read part of it), and every read hands the
/// value on whole (an argument, a return, an assignment, a test against
/// zero), where a pointer to nothing and a word read the same.
///
/// # Arguments
///
/// * `text` - A decompiled function.
/// * `word` - The machine word in bits.
///
/// # Returns
///
/// The text retyped, or `None` when nothing changes.
fn retype(text: &str, word: u8) -> Option<String> {
    let word_ty = if word == 32 { "uint32_t" } else { "uint64_t" };
    let p = parts(text)?;
    let mut found: BTreeMap<&str, Option<&'static str>> = BTreeMap::new();
    for d in p.head.get(p.decls..)? {
        if let Some((_, items)) = declaration(d).filter(|(ty, _)| *ty == word_ty) {
            for (stars, n) in items {
                if stars.is_empty() && is_var_name(n) {
                    found.insert(n, None);
                }
            }
        }
    }
    if found.is_empty() {
        return None;
    }
    let mut refused: BTreeSet<&str> = BTreeSet::new();
    for t in &p.body {
        let l = Line {
            text: t,
            toks: lex(t),
        };
        let def = assignment(&l).filter(|(_, rhs)| lone_call(rhs));
        for (k, tok) in l.toks.iter().enumerate() {
            let Some(w) = l
                .text
                .get(tok.at..tok.end)
                .filter(|w| found.contains_key(w))
            else {
                continue;
            };
            if k == 0 && def.is_some_and(|(v, _)| v == w) {
                let ret = def
                    .and_then(|(_, rhs)| rhs.split_once('('))
                    .and_then(|(callee, _)| any_decl(callee))
                    .map(|(d, _)| d.ret)
                    .filter(|r| VOID_POINTERS.contains(r));
                match (ret, found.get(w).copied().flatten()) {
                    (Some(r), None) => {
                        found.insert(w, Some(r));
                    }
                    (Some(r), Some(seen)) if r == seen => {}
                    (Some(_) | None, _) => {
                        refused.insert(w);
                    }
                }
                continue;
            }
            if !whole_read(&l, k) {
                refused.insert(w);
            }
        }
    }
    let typed: BTreeMap<&str, &str> = found
        .into_iter()
        .filter(|(n, _)| !refused.contains(n))
        .filter_map(|(n, r)| Some((n, r?)))
        .collect();
    if typed.is_empty() {
        return None;
    }
    let mut out: Vec<String> = p
        .head
        .iter()
        .take(p.decls)
        .map(|l| (*l).to_owned())
        .collect();
    for d in p.head.iter().skip(p.decls) {
        match declaration(d) {
            Some((ty, items)) if ty == word_ty => {
                let kept: Vec<String> = items
                    .iter()
                    .filter(|(_, n)| !typed.contains_key(n))
                    .map(|(stars, n)| format!("{stars}{n}"))
                    .collect();
                if !kept.is_empty() {
                    out.push(format!("{ty} {};", kept.join(", ")));
                }
            }
            Some(_) | None => out.push((*d).to_owned()),
        }
    }
    let mut by_type: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (n, ty) in &typed {
        by_type.entry(ty).or_default().push(n);
    }
    for (ty, names) in by_type {
        out.push(match ty.strip_suffix('*') {
            Some(base) => format!("{} *{};", base.trim_end(), names.join(", *")),
            None => format!("{ty} {};", names.join(", ")),
        });
    }
    out.push(String::new());
    out.extend(p.body.iter().map(|l| (*l).to_owned()));
    let mut joined = out.join("\n");
    if text.ends_with('\n') {
        joined.push('\n');
    }
    Some(joined)
}

/// Tells whether the read at token `k` hands the value on whole: an
/// argument, a returned value, an assignment's right side, a test, or a
/// comparison with a non-negative literal or another value.
///
/// # Arguments
///
/// * `l` - The line.
/// * `k` - The token.
fn whole_read(l: &Line<'_>, k: usize) -> bool {
    const BEFORE: [&str; 11] = [
        "(", ",", "=", "==", "!=", "!", "&&", "||", "?", ":", "return",
    ];
    const AFTER: [&str; 9] = [")", ",", ";", "==", "!=", "&&", "||", "?", ":"];
    let before = k.checked_sub(1).is_none_or(|p| BEFORE.contains(&l.word(p)));
    let after = AFTER.contains(&l.word(k + 1)) || k + 1 == l.toks.len();
    let negative = (l.is(k + 1, "==") || l.is(k + 1, "!=")) && l.is(k + 2, "-");
    let prev_cmp = k
        .checked_sub(1)
        .is_some_and(|p| l.is(p, "==") || l.is(p, "!="))
        && k.checked_sub(2).is_some_and(|p| l.is(p, "-"));
    before && after && !negative && !prev_cmp
}

/// Names the constants a declared API takes by the group its parameter
/// gives them, where the text spells a number or a guess.
///
/// The lifter names the bare numbers it passes; a constant the webs pass
/// folded into the call later, and a status name the renderer guessed for
/// a value it saw alone (`STATUS_DATATYPE_MISALIGNMENT` for an `HKEY` of
/// `0x80000002`), are named here: by the parameter's group, else `NULL`
/// for a zero pointer, else a guessed status name passed as a pointer
/// reads as its number.
///
/// # Arguments
///
/// * `text` - A decompiled function.
/// * `word` - The machine word in bits.
///
/// # Returns
///
/// The text with the constants named, or `None` when none changes.
fn name_constants(text: &str, word: u8) -> Option<String> {
    let mut changed = false;
    let mut out: Vec<String> = Vec::new();
    let mut in_body = false;
    for line in text.lines() {
        if !in_body || !line.contains('(') {
            in_body |= line.trim().is_empty();
            out.push(line.to_owned());
            continue;
        }
        let l = Line {
            text: line,
            toks: lex(line),
        };
        let mut edits: Vec<(usize, usize, String)> = Vec::new();
        for (k, tok) in l.toks.iter().enumerate() {
            let w = l.text.get(tok.at..tok.end).unwrap_or("");
            let (value, guessed) = match tok.lex {
                Lex::Number => (parse_const(w), false),
                Lex::Name => (crate::winconst::value(w).map(u64::from), true),
                Lex::Literal | Lex::Punct => (None, false),
            };
            let Some(v) = value else {
                continue;
            };
            if k.checked_sub(1).is_some_and(|p| l.is(p, "-")) {
                continue;
            }
            let Some((callee, i)) = argument_of(&l, k) else {
                continue;
            };
            let Some((d, format)) = any_decl(callee) else {
                continue;
            };
            let Some(param) = d.params.get(i) else {
                continue;
            };
            let pass = typelib::pass_of(param.ty, word, format);
            let bits = pass.map_or(word, |p| p.bits(word)).max(8);
            let named = match (param.group.and_then(typelib::group), pass) {
                (Some(g), _) if guessed => typelib::render(g, v, bits)
                    .or_else(|| typelib::render(g, crate::num::sext32(v), bits)),
                (Some(g), _) => typelib::render(g, v, bits),
                (None, Some(Pass::Pointer)) if v == 0 && !guessed => Some("NULL".to_owned()),
                (None, Some(Pass::Pointer)) if guessed => Some(format!("{v:#x}")),
                (None, _) => None,
            };
            if let Some(n) = named.filter(|n| n != w) {
                edits.push((tok.at, tok.end, n));
            }
        }
        let mut s = line.to_owned();
        for (at, end, with) in edits.into_iter().rev() {
            if s.get(at..end).is_some() {
                s.replace_range(at..end, &with);
                changed = true;
            }
        }
        out.push(s);
    }
    if !changed {
        return None;
    }
    let mut joined = out.join("\n");
    if text.ends_with('\n') {
        joined.push('\n');
    }
    Some(joined)
}

/// Spells the test of a call that answers yes or no (a declared `BOOL`,
/// `BOOLEAN` or `bool` result) as the call: `if (Api(..) != 0)` as
/// `if (Api(..))` and `if (Api(..) == 0)` as `if (!Api(..))`.
///
/// The same value is tested either way: a condition reads any scalar as
/// its comparison with zero.
///
/// # Arguments
///
/// * `text` - A decompiled function.
///
/// # Returns
///
/// The text respelled, or `None` when it holds no such test.
fn bool_tests(text: &str) -> Option<String> {
    let mut changed = false;
    let mut out: Vec<String> = Vec::new();
    for line in text.lines() {
        let t = line.trim_start();
        let cond = ["if (", "} else if (", "while (", "} while ("]
            .iter()
            .any(|p| t.starts_with(p));
        if !cond {
            out.push(line.to_owned());
            continue;
        }
        let l = Line {
            text: line,
            toks: lex(line),
        };
        let mut edits: Vec<(usize, usize, &str)> = Vec::new();
        for c in 0..l.toks.len() {
            if !l.is(c + 1, "(") {
                continue;
            }
            let yes_no = any_decl(l.word(c))
                .is_some_and(|(d, _)| matches!(d.ret, "BOOL" | "BOOLEAN" | "bool"));
            let Some(close) = l.closing(c + 1).filter(|_| yes_no) else {
                continue;
            };
            let eq = l.is(close + 1, "==");
            let tested = (eq || l.is(close + 1, "!=")) && l.word(close + 2) == "0";
            let ends = ["", ")", "&&", "||"].contains(&l.word(close + 3));
            let opens = c
                .checked_sub(1)
                .is_none_or(|b| l.is(b, "(") || l.is(b, "&&") || l.is(b, "||"));
            let (Some(end), Some(zero), Some(callee)) =
                (l.toks.get(close), l.toks.get(close + 2), l.toks.get(c))
            else {
                continue;
            };
            if tested && ends && opens {
                edits.push((end.end, zero.end, ""));
                if eq {
                    edits.push((callee.at, callee.at, "!"));
                }
            }
        }
        if edits.is_empty() {
            out.push(line.to_owned());
            continue;
        }
        changed = true;
        edits.sort_unstable_by_key(|e| std::cmp::Reverse(e.0));
        let mut s = line.to_owned();
        for (at, end, with) in edits {
            if s.get(at..end).is_some() {
                s.replace_range(at..end, with);
            }
        }
        out.push(s);
    }
    if !changed {
        return None;
    }
    let mut joined = out.join("\n");
    if text.ends_with('\n') {
        joined.push('\n');
    }
    Some(joined)
}

/// [`name_vars`], `None` when nothing changes.
///
/// # Arguments
///
/// * `text` - A decompiled function.
fn rename(text: &str) -> Option<String> {
    let p = parts(text)?;
    let mut vars: BTreeMap<&str, Option<(Rank, String)>> = BTreeMap::new();
    for d in p.head.get(p.decls..)? {
        for (_, n) in declaration(d).map(|(_, items)| items).unwrap_or_default() {
            if is_var_name(n) {
                vars.insert(n, None);
            }
        }
    }
    if vars.is_empty() {
        return None;
    }
    let lines: Vec<Line<'_>> = p
        .body
        .iter()
        .map(|t| Line {
            text: t,
            toks: lex(t),
        })
        .collect();
    let mut offer = |var: &str, rank: Rank, name: &str| {
        if let Some(slot) = vars.get_mut(var)
            && nameable(name)
            && slot.as_ref().is_none_or(|(r, _)| rank < *r)
        {
            *slot = Some((rank, name.to_owned()));
        }
    };
    let handles: BTreeSet<&str> = p
        .head
        .get(p.decls..)
        .unwrap_or_default()
        .iter()
        .filter_map(|d| declaration(d))
        .filter(|(ty, _)| *ty == "HANDLE")
        .flat_map(|(_, items)| items.into_iter().map(|(_, n)| n))
        .collect();
    for l in &lines {
        for (k, tok) in l.toks.iter().enumerate() {
            let Some(w) = l.text.get(tok.at..tok.end).filter(|w| is_var_name(w)) else {
                continue;
            };
            let Some((callee, i)) = argument_of(l, k) else {
                continue;
            };
            if let Some(param) = decl(callee).and_then(|d| d.params.get(i)) {
                offer(w, Rank::Param, param.name);
            }
            if any_decl(callee)
                .and_then(|(d, _)| d.params.get(i))
                .is_some_and(|param| param.ty == STREAM)
            {
                offer(w, Rank::Type, "fp");
            }
        }
        if let Some((var, rhs)) = assignment(l)
            && let Some((_, field)) = rhs.rsplit_once("->")
            && !rhs.contains(['(', ' ', '['])
            && !field.starts_with("field_")
        {
            offer(var, Rank::Field, field);
        }
        if let Some((var, rhs)) = assignment(l).filter(|(_, rhs)| lone_call(rhs))
            && let Some((callee, _)) = rhs.split_once('(')
            && let Some((d, _)) = any_decl(callee)
        {
            if d.ret == STREAM {
                offer(var, Rank::Type, "fp");
            } else if d.ret == "HANDLE" && handles.contains(var) {
                offer(var, Rank::Type, &handle_name(callee));
            }
        }
    }
    let counters = loop_counters(&lines);
    let mut taken: BTreeSet<String> = BTreeSet::new();
    for h in &p.head {
        taken.extend(tokens(h).map(str::to_owned));
    }
    for l in &lines {
        for (k, t) in l.toks.iter().enumerate() {
            let field = k
                .checked_sub(1)
                .is_some_and(|q| l.is(q, "->") || l.is(q, "."));
            if t.lex == Lex::Name && !field {
                taken.insert(l.word(k).to_owned());
            }
        }
    }
    let mut order: Vec<(usize, &str)> = vars
        .iter()
        .filter(|(_, e)| e.is_some())
        .filter_map(|(v, _)| Some((v.strip_prefix("var")?.parse::<usize>().ok()?, *v)))
        .collect();
    order.sort_unstable();
    let mut renames: BTreeMap<&str, String> = BTreeMap::new();
    for (_, var) in order {
        let Some(Some((_, base))) = vars.get(var) else {
            continue;
        };
        let mut name = base.clone();
        let mut n = 2usize;
        while taken.contains(&name) {
            name = format!("{base}{n}");
            n += 1;
        }
        taken.insert(name.clone());
        renames.insert(var, name);
    }
    for (var, depth) in counters {
        if !matches!(vars.get(var), Some(None)) {
            continue;
        }
        let free = COUNTERS.iter().skip(depth).find(|c| !taken.contains(**c));
        if let Some(c) = free {
            taken.insert((*c).to_owned());
            renames.insert(var, (*c).to_owned());
        }
    }
    if renames.is_empty() {
        return None;
    }
    let mut out: Vec<String> = Vec::with_capacity(p.head.len() + p.body.len() + 1);
    for h in &p.head {
        out.push(renames.iter().fold((*h).to_owned(), |line, (old, new)| {
            rename_word(&line, old, new)
        }));
    }
    out.push(String::new());
    for l in &lines {
        let mut line = l.text.to_owned();
        for t in l.toks.iter().rev() {
            if let Some(new) = l.text.get(t.at..t.end).and_then(|w| renames.get(w)) {
                line.replace_range(t.at..t.end, new);
            }
        }
        out.push(line);
    }
    let mut joined = out.join("\n");
    if text.ends_with('\n') {
        joined.push('\n');
    }
    Some(joined)
}

/// The name of the handle a handle API hands back.
///
/// It is `h` and the API's name after its verb, without a trailing `A` or
/// `W` or `Handle`: `hFile` from `CreateFileW`, `hProcess` from
/// `OpenProcess`.
///
/// # Arguments
///
/// * `callee` - The API's name.
fn handle_name(callee: &str) -> String {
    let base = callee
        .strip_suffix(['A', 'W'])
        .filter(|b| b.ends_with(|c: char| c.is_ascii_lowercase()))
        .unwrap_or(callee);
    let rest = HANDLE_VERBS
        .iter()
        .find_map(|v| {
            base.strip_prefix(v)
                .filter(|r| r.starts_with(|c: char| c.is_ascii_uppercase()))
        })
        .unwrap_or(base);
    let rest = rest
        .strip_suffix("Handle")
        .filter(|r| !r.is_empty())
        .unwrap_or(rest);
    format!("h{rest}")
}

/// The counters of the `for` loops whose counter no line outside the
/// loop names, each with how many such loops enclose its own.
///
/// A counter is the variable a header starts (`for (v = 0; ...`) and steps
/// by one (`v += 1`, `v++`, `v -= 1`, `v--`), named by its condition, and
/// named by no line before the header or after the loop's closing brace:
/// the loop is its whole life, which is what `i` says.
///
/// # Arguments
///
/// * `lines` - The body's lines.
///
/// # Returns
///
/// The counters in the order their loops open.
fn loop_counters<'t>(lines: &[Line<'t>]) -> Vec<(&'t str, usize)> {
    let mut loops: Vec<(&'t str, usize, usize)> = Vec::new();
    for (a, l) in lines.iter().enumerate() {
        let t = l.text.trim();
        let Some(header) = t.strip_prefix("for (").and_then(|h| h.strip_suffix(") {")) else {
            continue;
        };
        let clauses: Vec<&str> = header.split("; ").collect();
        let [init, cond, step] = clauses.as_slice() else {
            continue;
        };
        let Some((var, _)) = init.split_once(" = ") else {
            continue;
        };
        let steps = [
            format!("{var} += 1"),
            format!("{var}++"),
            format!("++{var}"),
            format!("{var} -= 1"),
            format!("{var}--"),
            format!("--{var}"),
        ];
        if !is_var_name(var)
            || !steps.iter().any(|s| s == step)
            || word_positions(cond, var).is_empty()
        {
            continue;
        }
        let pad = indent_of(l.text);
        let Some(b) = (a + 1..lines.len()).find(|&b| {
            lines
                .get(b)
                .is_some_and(|e| indent_of(e.text) == pad && e.text.trim_start().starts_with('}'))
        }) else {
            continue;
        };
        let alone = lines
            .iter()
            .enumerate()
            .filter(|(k, _)| *k < a || *k > b)
            .all(|(_, o)| word_positions(o.text, var).is_empty());
        if alone {
            loops.push((var, a, b));
        }
    }
    loops
        .iter()
        .map(|&(var, a, b)| {
            let depth = loops
                .iter()
                .filter(|&&(_, oa, ob)| oa < a && b <= ob)
                .count();
            (var, depth)
        })
        .collect()
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::name_vars;

    /// The machine word the tests read as.
    const WORD: u8 = 64;

    /// A function text: a header, the declarations, a blank line, the body.
    ///
    /// # Arguments
    ///
    /// * `decls` - The declaration lines.
    /// * `body` - The body lines.
    fn function(decls: &[&str], body: &[&str]) -> String {
        let mut out = String::from(
            "// f @ 0x1000: 9 instructions, 1 blocks\n// signature: uint64_t f(uint64_t a1, uint64_t a2)\n",
        );
        for l in decls.iter().chain(&[""]).chain(body) {
            out.push_str(l);
            out.push('\n');
        }
        out
    }

    /// The body of a function text: the lines after the first blank one.
    ///
    /// # Arguments
    ///
    /// * `text` - The text.
    fn body(text: &str) -> Vec<&str> {
        text.lines().skip_while(|l| !l.is_empty()).skip(1).collect()
    }

    /// A variable passed whole to a declared API takes the parameter's
    /// name. A handle result is named for what its API opens; a length
    /// keeps its number.
    #[test]
    fn apis_name_what_they_take_and_hand_back() {
        let t = function(
            &["uint64_t var1, var2, var3;"],
            &[
                "var1 = GetProcessHeap();",
                "var2 = lstrlenW(a1);",
                "var3 = sub_1(a2);",
                "CloseHandle(var3);",
                "sub_2(var1, var2);",
                "return 0;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert_eq!(
            body(&out),
            [
                "hProcessHeap = GetProcessHeap();",
                "var2 = lstrlenW(a1);",
                "hObject = sub_1(a2);",
                "CloseHandle(hObject);",
                "sub_2(hProcessHeap, var2);",
                "return 0;",
            ],
            "{out}"
        );
        assert!(
            out.contains(
                "uint64_t var2, hObject;
HANDLE hProcessHeap;"
            ),
            "{out}"
        );
    }

    /// Nested counters keep the numbers the text gave them.
    #[test]
    fn counters_are_named_by_depth() {
        let t = function(
            &["uint64_t var1, var2, var3;"],
            &[
                "var1 = 0;",
                "while (var1 < a1) {",
                "  var2 = 0;",
                "  while (var2 < a2) {",
                "    var3 = sub_1(var1, var2);",
                "    sub_2(var3);",
                "    var2 += 1;",
                "  }",
                "  var1 += 1;",
                "}",
                "return 0;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert_eq!(
            body(&out),
            [
                "var1 = 0;",
                "while (var1 < a1) {",
                "  var2 = 0;",
                "  while (var2 < a2) {",
                "    var3 = sub_1(var1, var2);",
                "    sub_2(var3);",
                "    var2 += 1;",
                "  }",
                "  var1 += 1;",
                "}",
                "return 0;",
            ],
            "{out}"
        );
    }

    /// A `for` header's counter no line outside the loop names is `i`, a
    /// nested one `j`, and a later loop at the first depth takes the next
    /// free letter. A counter read after its loop keeps its number.
    #[test]
    fn a_for_counter_is_i() {
        let t = function(
            &["uint64_t var1, var2, var3, var4;"],
            &[
                "for (var1 = 0; var1 < a1; var1 += 1) {",
                "  for (var2 = a2; var2 < a1; var2++) {",
                "    sub_1(var1, var2);",
                "  }",
                "}",
                "for (var3 = 0; var3 < a2; var3 += 1) {",
                "  sub_1(var3);",
                "}",
                "for (var4 = 0; var4 < a2; var4 += 1) {",
                "  sub_1(var4);",
                "}",
                "return var4;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert_eq!(
            body(&out),
            [
                "for (i = 0; i < a1; i += 1) {",
                "  for (j = a2; j < a1; j++) {",
                "    sub_1(i, j);",
                "  }",
                "}",
                "for (k = 0; k < a2; k += 1) {",
                "  sub_1(k);",
                "}",
                "for (var4 = 0; var4 < a2; var4 += 1) {",
                "  sub_1(var4);",
                "}",
                "return var4;",
            ],
            "{out}"
        );
    }

    /// A C stream is `fp`, by the API that opens it or one it is passed
    /// to, and a handle typed by the API that hands it back is named for
    /// what that API opens.
    #[test]
    fn streams_and_handles_are_named_by_their_types() {
        let t = function(
            &["uint64_t var1, var2, var3;"],
            &[
                "var1 = fopen(a1, \"r\");",
                "var2 = sub_1(a2);",
                "fclose(var2);",
                "var3 = CreateFileW(a1, 0, 0, 0, 3, 0, 0);",
                "sub_2(var3);",
                "return var1;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert!(out.contains("fp = fopen(a1, \"r\");"), "{out}");
        assert!(out.contains("fclose(fp2);"), "{out}");
        assert!(out.contains("hFile = CreateFileW("), "{out}");
        assert!(out.contains("HANDLE hFile;"), "{out}");
    }

    /// A field names what is loaded from it. A length keeps its number
    /// beside a `len` the text already declared.
    #[test]
    fn names_never_shadow() {
        let t = function(
            &["uint64_t var1, var2, len;"],
            &[
                "var1 = a1->count;",
                "var2 = strlen(a2);",
                "len = var1 + var2;",
                "return len;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert_eq!(
            body(&out),
            [
                "count = a1->count;",
                "var2 = strlen(a2);",
                "len = count + var2;",
                "return len;",
            ],
            "{out}"
        );
        assert!(out.contains("uint64_t count, var2, len;"), "{out}");
    }

    /// A variable holding only one handle API's results is declared by
    /// that type and named for what the API opens; one read in arithmetic
    /// keeps its width and its number.
    #[test]
    fn handles_are_typed_by_their_api() {
        let t = function(
            &["uint64_t var1, var2;"],
            &[
                "var1 = OpenProcess(a1, 0, a2);",
                "var2 = GetProcessHeap();",
                "sub_1(var1, var2 + 8);",
                "return 0;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert!(out.contains("uint64_t var2;\nHANDLE hProcess;"), "{out}");
        assert!(!out.contains("HANDLE Process;"), "{out}");
    }

    /// A constant folded into a declared API's call, or guessed as a
    /// status, reads by the parameter's group.
    #[test]
    fn constants_read_by_the_parameters_group() {
        let t = function(
            &["uint64_t local_8;"],
            &[
                "RegOpenKeyExW(STATUS_DATATYPE_MISALIGNMENT, L\"Software\", 0, 0x20019, &local_8);",
                "CloseHandle(0);",
                "return 0;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert_eq!(
            body(&out),
            [
                "RegOpenKeyExW(HKEY_LOCAL_MACHINE, L\"Software\", REG_OPTION_NON_VOLATILE, KEY_READ, &local_8);",
                "CloseHandle(NULL);",
                "return 0;",
            ],
            "{out}"
        );
    }

    /// A yes-or-no API's test reads as the call; a count's test does not.
    #[test]
    fn yes_or_no_tests_read_as_the_call() {
        let t = function(
            &[],
            &[
                "if (CloseHandle(a1) == 0) {",
                "  return 1;",
                "}",
                "if (CloseHandle(a2) != 0 && GetFileSize(a1, 0) == 0) {",
                "  return 2;",
                "}",
                "return 0;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert_eq!(
            body(&out),
            [
                "if (!CloseHandle(a1)) {",
                "  return 1;",
                "}",
                "if (CloseHandle(a2) && GetFileSize(a1, NULL) == 0) {",
                "  return 2;",
                "}",
                "return 0;",
            ],
            "{out}"
        );
    }
}
