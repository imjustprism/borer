//! Names and types from evidence.
//!
//! The variables the webs pass made (`var1` to `varN`, [`super::vars`])
//! are named and typed by what the text shows they hold, the constants an
//! API takes are named by the group its declaration gives, and the test of
//! a call that answers yes or no is spelled as the call.
//!
//! First match wins, as a reader names them: the parameter of a declared
//! API a variable is passed to whole (`hKey`), the thing a handle or
//! pointer API hands back (`ProcessHeap` from `GetProcessHeap`), `len` for
//! a string's length, `i`, `j` and `k` for the counters of nested loops,
//! and the field a variable is loaded from (`count` from `p->count`). A
//! name the text already holds takes a number, so nothing shadows a
//! function, a global or a parameter, and a variable no evidence names
//! keeps its number. Names are spelling: no line reads anything else for
//! them.

use super::vars::{Lex, Line, declaration, is_var_name, lex, parts, safe_slot_names, slot_parts};
use super::*;
use crate::analysis::typelib::{self, Decl, Os, Pass};
use crate::program::BinaryFormat;

/// The kinds of evidence, strongest first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Rank {
    /// Passed whole as a declared API's parameter.
    Param,
    /// The result of a handle or pointer API.
    Result,
    /// A string's length.
    Length,
    /// A loop's counter.
    Counter,
    /// Loaded from a named field.
    Field,
}

/// The names a counter takes by how deep its loop nests.
const COUNTERS: [&str; 5] = ["i", "j", "k", "m", "n"];

/// The verbs a handle or pointer API's name opens with, whose rest names
/// what it hands back.
const VERBS: [&str; 6] = ["Get", "Create", "Open", "Load", "Find", "Alloc"];

/// The functions whose result is a string's length.
const LENGTHS: [&str; 8] = [
    "strlen", "wcslen", "strnlen", "wcsnlen", "lstrlenA", "lstrlenW", "lstrlen", "_mbslen",
];

/// The types a handle or pointer API hands back.
const HANDLES: [&str; 12] = [
    "HANDLE",
    "HMODULE",
    "HINSTANCE",
    "HKEY",
    "LPVOID",
    "PVOID",
    "FARPROC",
    "HLOCAL",
    "HGLOBAL",
    "HINTERNET",
    "SC_HANDLE",
    "HWND",
];

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

/// What a handle or pointer API's result is: the rest of its name after
/// its verb, without a trailing `A` or `W` or `Handle`.
///
/// # Arguments
///
/// * `callee` - The API's name.
/// * `d` - Its declaration.
fn result_name(callee: &str, d: &Decl) -> Option<String> {
    if d.os != Os::Win || !HANDLES.contains(&d.ret) {
        return None;
    }
    let base = callee
        .strip_suffix(['A', 'W'])
        .filter(|b| b.ends_with(|c: char| c.is_ascii_lowercase()))
        .unwrap_or(callee);
    let rest = VERBS.iter().find_map(|v| {
        base.strip_prefix(v)
            .filter(|r| r.starts_with(|c: char| c.is_ascii_uppercase()))
    })?;
    let rest = rest
        .strip_suffix("Handle")
        .filter(|r| !r.is_empty())
        .unwrap_or(rest);
    Some(rest.to_owned())
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

/// Tells whether `w` is a `varN` temporary or a stack slot (`local_*` or
/// `home_*`).
///
/// # Arguments
///
/// * `w` - The identifier.
fn is_candidate(w: &str) -> bool {
    is_var_name(w) || slot_parts(w).is_some()
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
    (is_candidate(lhs) && !rhs.contains(" = ")).then_some((lhs, rhs))
}

/// The variable a line counts up by one, if it does: `v += 1;`, `v++;`,
/// `v = v + 1;` or `v = (v + 1) & 0xff..;`.
///
/// # Arguments
///
/// * `l` - The line.
fn counter<'t>(l: &Line<'t>) -> Option<&'t str> {
    let t = l.text.trim().strip_suffix(';')?;
    if let Some(v) = t.strip_suffix(" += 1").or_else(|| t.strip_suffix("++")) {
        return is_candidate(v).then_some(v);
    }
    let (v, rhs) = t.split_once(" = ")?;
    let plus = format!("{v} + 1");
    let stepped = rhs == plus
        || rhs
            .strip_prefix(&format!("({plus}) & 0x"))
            .is_some_and(|m| m.bytes().all(|b| b == b'f'));
    (is_candidate(v) && stepped).then_some(v)
}

/// The variable a `for` header counts up by one: `for (v = ..; ..; v += 1) {`.
///
/// # Arguments
///
/// * `t` - The trimmed line.
fn for_counter(t: &str) -> Option<&str> {
    let header = t.strip_prefix("for (")?.strip_suffix(") {")?;
    let (init, rest) = header.split_once("; ")?;
    let (_, step) = rest.rsplit_once("; ")?;
    let v = init.split_once(" = ")?.0;
    let stepped = step == format!("{v} += 1") || step == format!("{v}++");
    (is_candidate(v) && stepped).then_some(v)
}

/// The variables an ordering comparison reads, as a loop's counter is.
///
/// # Arguments
///
/// * `lines` - The body's lines.
fn compared<'t>(lines: &[Line<'t>]) -> BTreeSet<&'t str> {
    let mut out = BTreeSet::new();
    for l in lines {
        for k in 0..l.toks.len() {
            if !["<", "<=", ">", ">=", "!="].iter().any(|op| l.is(k, op)) {
                continue;
            }
            for side in [k.checked_sub(1), Some(k + 1)].into_iter().flatten() {
                if let Some(t) = l.toks.get(side)
                    && let Some(w) = l.text.get(t.at..t.end)
                    && is_candidate(w)
                {
                    out.insert(w);
                }
            }
        }
    }
    out
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
    let safe = safe_slot_names(&p);
    let mut found: BTreeMap<&str, Option<&'static str>> = BTreeMap::new();
    for d in p.head.get(p.decls..)? {
        if let Some((_, items)) = declaration(d).filter(|(ty, _)| *ty == word_ty) {
            for (stars, n) in items {
                if stars.is_empty() && (is_var_name(n) || safe.contains(n)) {
                    found.insert(n, None);
                }
            }
        }
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
                    .map(|(d, _)| match d.ret {
                        "HLOCAL" | "HGLOBAL" => "void *",
                        r => r,
                    })
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

/// Tells whether the read at token `k` hands the value on whole.
///
/// Accepts an argument, a returned value, an assignment's right side, a test,
/// a field access, or a comparison with a non-negative literal or another
/// value.
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
    let before = k
        .checked_sub(1)
        .is_none_or(|p| BEFORE.contains(&l.word(p)) || (l.is(p, "&") && l.is(k + 1, "->")));
    let arrow = l.is(k + 1, "->")
        && l.toks
            .get(k + 3)
            .is_none_or(|t| t.lex != Lex::Punct || l.word(k + 3) != "(");
    let after = AFTER.contains(&l.word(k + 1)) || arrow || k + 1 == l.toks.len();
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
        if !in_body {
            in_body = line.trim().is_empty();
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
    let safe = safe_slot_names(&p);
    let mut vars: BTreeMap<&str, Option<(Rank, String)>> = BTreeMap::new();
    for d in p.head.get(p.decls..)? {
        for (_, n) in declaration(d).map(|(_, items)| items).unwrap_or_default() {
            if is_var_name(n) || safe.contains(n) {
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
    let compared = compared(&lines);
    let mut open: Vec<bool> = Vec::new();
    for l in &lines {
        let t = l.text.trim();
        if t.starts_with('}') {
            open.pop();
        }
        for (k, tok) in l.toks.iter().enumerate() {
            let Some(w) = l.text.get(tok.at..tok.end).filter(|w| is_candidate(w)) else {
                continue;
            };
            if let Some((callee, i)) = argument_of(l, k)
                && let Some(param) = decl(callee).and_then(|d| d.params.get(i))
            {
                offer(w, Rank::Param, param.name);
            }
        }
        if let Some((var, rhs)) = assignment(l) {
            if let Some((callee, _)) = rhs.split_once('(').filter(|_| lone_call(rhs)) {
                if LENGTHS.contains(&callee) {
                    offer(var, Rank::Length, "len");
                }
                if let Some(n) = decl(callee).and_then(|d| result_name(callee, d)) {
                    offer(var, Rank::Result, &n);
                }
            }
            if let Some((_, field)) = rhs.rsplit_once("->")
                && !rhs.contains(['(', ' ', '['])
                && !field.starts_with("field_")
            {
                offer(var, Rank::Field, field);
            }
        }
        let depth = open.iter().filter(|is_loop| **is_loop).count();
        if let Some(var) = counter(l).filter(|v| depth > 0 && compared.contains(v)) {
            offer(
                var,
                Rank::Counter,
                COUNTERS.get(depth - 1).copied().unwrap_or("i"),
            );
        }
        if let Some(var) = for_counter(t) {
            offer(
                var,
                Rank::Counter,
                COUNTERS.get(depth).copied().unwrap_or("i"),
            );
        }
        if t.ends_with('{') {
            open.push(t.starts_with("while (") || t.starts_with("for (") || t == "do {");
        }
    }
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
    let mut order: Vec<((u8, usize), &str)> = vars
        .iter()
        .filter(|(_, e)| e.is_some())
        .filter_map(|(v, _)| {
            let key = if let Some(n) = v.strip_prefix("var").and_then(|s| s.parse::<usize>().ok()) {
                (0, n)
            } else if let Some((home, off)) = slot_parts(v) {
                (1 + u8::from(home), usize::try_from(off).ok()?)
            } else {
                return None;
            };
            Some((key, *v))
        })
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
    /// name, a handle API's result the rest of its name, a length `len`.
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
                "ProcessHeap = GetProcessHeap();",
                "len = lstrlenW(a1);",
                "hObject = sub_1(a2);",
                "CloseHandle(hObject);",
                "sub_2(ProcessHeap, len);",
                "return 0;",
            ],
            "{out}"
        );
        assert!(
            out.contains(
                "uint64_t len, hObject;
HANDLE ProcessHeap;"
            ),
            "{out}"
        );
    }

    /// Counters of nested loops are `i` and `j`; a variable no evidence
    /// names keeps its number.
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
                "i = 0;",
                "while (i < a1) {",
                "  j = 0;",
                "  while (j < a2) {",
                "    var3 = sub_1(i, j);",
                "    sub_2(var3);",
                "    j += 1;",
                "  }",
                "  i += 1;",
                "}",
                "return 0;",
            ],
            "{out}"
        );
    }

    /// A `for` header's counter is `i`.
    #[test]
    fn a_for_counter_is_i() {
        let t = function(
            &["uint64_t var1;"],
            &[
                "for (var1 = 0; var1 < a1; var1 += 1) {",
                "  sub_1(var1);",
                "}",
                "return 0;",
            ],
        );
        let out = name_vars(&t, WORD);
        assert_eq!(
            body(&out),
            [
                "for (i = 0; i < a1; i += 1) {",
                "  sub_1(i);",
                "}",
                "return 0;"
            ],
            "{out}"
        );
    }

    /// A name the text already holds takes a number, and a field names
    /// what is loaded from it.
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
                "len2 = strlen(a2);",
                "len = count + len2;",
                "return len;",
            ],
            "{out}"
        );
    }

    /// A variable holding only one handle API's results is declared by
    /// that type; one read in arithmetic keeps its width.
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
        assert!(
            out.contains("uint64_t ProcessHeap;\nHANDLE Process;"),
            "{out}"
        );
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
