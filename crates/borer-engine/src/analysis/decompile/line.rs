//! The line vocabulary: the shapes one emitted pseudo-C line takes, read
//! back by every text pass.
//!
//! The emitter writes labels, gotos, guards, loop openers and statements in
//! fixed spellings, and the passes after it re-read those spellings. Each
//! shape is recognized or built here, once, so a pass never re-derives what
//! a `goto` looks like or where a line's indentation ends.

use std::collections::BTreeMap;

/// Tells whether a character can be part of an identifier.
///
/// # Arguments
///
/// * `c` - The character.
pub(super) fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Tells whether a word is one identifier: non-empty, identifier
/// characters only.
///
/// # Arguments
///
/// * `w` - The word.
pub(super) fn is_ident(w: &str) -> bool {
    !w.is_empty() && w.chars().all(is_ident_char)
}

/// The identifier-shaped words of a text, in order.
///
/// # Arguments
///
/// * `text` - Any text.
pub(super) fn tokens(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !is_ident_char(c))
        .filter(|w| !w.is_empty())
}

/// Tells whether a word is `prefix` followed by one or more decimal digits.
///
/// # Arguments
///
/// * `w` - The word.
/// * `prefix` - The letters before the number.
fn numbered(w: &str, prefix: &str) -> bool {
    w.strip_prefix(prefix)
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// Tells whether a word names a parameter, `a<n>`.
///
/// # Arguments
///
/// * `w` - The word.
pub(super) fn is_param_name(w: &str) -> bool {
    numbered(w, "a")
}

/// Tells whether a word names an emission temporary, `tmp_<n>`.
///
/// # Arguments
///
/// * `w` - The word.
pub(super) fn is_temp_name(w: &str) -> bool {
    numbered(w, "tmp_")
}

/// Tells whether a name is one of the machine's registers or a temporary.
///
/// The names are the ones the lifters give their registers: x64's `rax`
/// to `r15` and `xmm<n>`, x86's `eax` to `edi`, and arm64's `x0` to `x30`
/// and `v0` to `v31`.
///
/// # Arguments
///
/// * `name` - The left side of an assignment.
pub(super) fn is_register_name(name: &str) -> bool {
    if !matches!(
        name.as_bytes().first(),
        Some(b'r' | b'e' | b'x' | b'v' | b't')
    ) {
        return false;
    }
    if is_temp_name(name) || numbered(name, "xmm") {
        return true;
    }
    matches!(
        name,
        "rax"
            | "rbx"
            | "rcx"
            | "rdx"
            | "rsi"
            | "rdi"
            | "rbp"
            | "rsp"
            | "eax"
            | "ebx"
            | "ecx"
            | "edx"
            | "esi"
            | "edi"
            | "ebp"
            | "esp"
    ) || register_number(name, 'r').is_some_and(|n| (8..=15).contains(&n))
        || register_number(name, 'x').is_some_and(|n| n <= 30)
        || register_number(name, 'v').is_some_and(|n| n <= 31)
}

/// Reads the number of a register name `<prefix><n>`, written as the
/// lifters write it: decimal, without a leading zero.
///
/// # Arguments
///
/// * `name` - The word.
/// * `prefix` - The register bank's letter.
fn register_number(name: &str, prefix: char) -> Option<u8> {
    let digits = name.strip_prefix(prefix)?;
    if digits.len() > 1 && digits.starts_with('0') {
        return None;
    }
    digits
        .bytes()
        .all(|b| b.is_ascii_digit())
        .then(|| digits.parse().ok())
        .flatten()
}

/// Tells whether a word names a hoisted global, `g<bits>_<hex address>`.
///
/// # Arguments
///
/// * `w` - The word.
pub(super) fn is_global_name(w: &str) -> bool {
    w.strip_prefix('g')
        .and_then(|rest| rest.split_once('_'))
        .is_some_and(|(bits, addr)| {
            bits.chars().all(|c| c.is_ascii_digit())
                && !addr.is_empty()
                && addr.chars().all(|c| c.is_ascii_hexdigit())
        })
}

/// Tells whether `v` names a register, temporary, local or parameter: an
/// identifier that is not a `g{bits}_{addr}` global.
///
/// # Arguments
///
/// * `v` - The text before ` = `.
pub(super) fn is_plain_var(v: &str) -> bool {
    let mut chars = v.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == '_') || !chars.all(is_ident_char) {
        return false;
    }
    !(first == 'g'
        && v.get(1..2)
            .is_some_and(|c| c.chars().all(|ch| ch.is_ascii_digit())))
}

/// Tells whether `text` contains `ident` as a whole word.
///
/// # Arguments
///
/// * `text` - The text to search.
/// * `ident` - The identifier.
pub(super) fn mentions_ident(text: &str, ident: &str) -> bool {
    tokens(text).any(|w| w == ident)
}

/// The byte positions where `word` occurs as a whole identifier.
///
/// # Arguments
///
/// * `line` - The text.
/// * `word` - The identifier.
pub(super) fn word_positions(line: &str, word: &str) -> Vec<usize> {
    let mut out = Vec::new();
    let mut from = 0;
    while let Some(i) = line.get(from..).and_then(|t| t.find(word)) {
        let at = from + i;
        from = at + word.len();
        let before = line.get(..at).and_then(|h| h.chars().next_back());
        let after = line.get(at + word.len()..).and_then(|t| t.chars().next());
        if !before.is_some_and(is_ident_char) && !after.is_some_and(is_ident_char) {
            out.push(at);
        }
    }
    out
}

/// Rewrites every whole-word `old` in a line as `new`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `old` - The identifier replaced.
/// * `new` - What replaces it.
pub(super) fn rename_word(line: &str, old: &str, new: &str) -> String {
    let positions = word_positions(line, old);
    if positions.is_empty() {
        return line.to_owned();
    }
    let mut out = String::with_capacity(line.len() + positions.len() * new.len());
    let mut last = 0;
    for p in positions {
        out.push_str(&line[last..p]);
        out.push_str(new);
        last = p + old.len();
    }
    out.push_str(&line[last..]);
    out
}

/// Parses a decimal or `0x` hexadecimal number at the start of `s`.
///
/// # Arguments
///
/// * `s` - The text.
///
/// # Returns
///
/// The value and the number of digit bytes it took (the `0x` prefix not
/// counted), or `None`.
pub(super) fn number(s: &str) -> Option<(u64, usize)> {
    let t = s.trim();
    let (digits, radix) = match t.strip_prefix("0x") {
        Some(h) => (h, 16),
        None => (t, 10),
    };
    let len = digits
        .find(|c: char| !c.is_ascii_hexdigit())
        .unwrap_or(digits.len());
    let v = u64::from_str_radix(digits.get(..len)?, radix).ok()?;
    Some((v, len))
}

/// Parses a token that is wholly a decimal or `0x` constant, as the code
/// renders one.
///
/// # Arguments
///
/// * `t` - The token.
pub(super) fn parse_const(t: &str) -> Option<u64> {
    let t = t.trim();
    let digits = t.strip_prefix("0x").unwrap_or(t);
    number(t)
        .filter(|&(_, len)| len == digits.len())
        .map(|(v, _)| v)
}

/// Returns the indentation width of a line in spaces.
///
/// # Arguments
///
/// * `line` - One emitted line.
pub(super) fn indent_of(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// Returns the indentation of a line, to write another line at its depth.
///
/// # Arguments
///
/// * `line` - One emitted line.
pub(super) fn pad_of(line: &str) -> &str {
    &line[..indent_of(line)]
}

/// Counts the `//` header lines a function's text opens with: where a
/// header line is inserted.
///
/// # Arguments
///
/// * `lines` - The function's lines, header first.
pub(super) fn header_len<S: AsRef<str>>(lines: &[S]) -> usize {
    lines
        .iter()
        .position(|l| !l.as_ref().starts_with("//"))
        .unwrap_or(lines.len())
}

/// The label of the block starting at `va`: `L_<va>:`.
///
/// # Arguments
///
/// * `va` - The block's start address.
pub(super) fn label(va: u64) -> String {
    format!("L_{va:x}:")
}

/// A jump to the block starting at `va`: `goto L_<va>;`.
///
/// # Arguments
///
/// * `va` - The block's start address.
pub(super) fn goto(va: u64) -> String {
    format!("goto L_{va:x};")
}

/// Tells whether a line is a block label (`L_<addr>:`).
///
/// # Arguments
///
/// * `line` - One emitted line.
pub(super) fn is_label(line: &str) -> bool {
    label_name(line).is_some()
}

/// The name a block label line declares, without its colon.
///
/// # Arguments
///
/// * `line` - One emitted line.
pub(super) fn label_name(line: &str) -> Option<&str> {
    line.trim()
        .strip_suffix(':')
        .filter(|name| name.starts_with("L_"))
}

/// Tells whether a trimmed line is a plain `goto`.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn is_goto(t: &str) -> bool {
    t.starts_with("goto ")
}

/// The label a line's trailing `goto` names: `goto L;`, `if (c) goto L;`
/// or `case 3: goto L;`.
///
/// # Arguments
///
/// * `line` - One emitted line.
pub(super) fn goto_target(line: &str) -> Option<&str> {
    line.trim()
        .rsplit_once("goto ")
        .and_then(|(_, target)| target.strip_suffix(';'))
}

/// The address a line's trailing `goto L_<va>;` jumps to.
///
/// # Arguments
///
/// * `line` - One emitted line.
///
/// # Returns
///
/// The address, or `None` for a line without a goto or with a computed one.
pub(super) fn goto_address(line: &str) -> Option<u64> {
    let hex = goto_target(line)?.strip_prefix("L_")?;
    u64::from_str_radix(hex, 16).ok()
}

/// The condition and label of an `if (COND) goto LABEL;` line.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn conditional_goto(t: &str) -> Option<(&str, &str)> {
    let (cond, target) = t.strip_prefix("if (")?.rsplit_once(") goto ")?;
    Some((cond, target.strip_suffix(';')?))
}

/// Indexes the lines carrying a `goto` by the label each names.
///
/// # Arguments
///
/// * `lines` - The body lines.
pub(super) fn goto_index(lines: &[String]) -> BTreeMap<String, Vec<usize>> {
    let mut jumps: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (i, l) in lines.iter().enumerate() {
        if let Some(target) = goto_target(l) {
            jumps.entry(target.to_owned()).or_default().push(i);
        }
    }
    jumps
}

/// Tells whether every jump to each of `labels` lies strictly inside
/// `(from, to)`, so nothing enters that run from outside.
///
/// # Arguments
///
/// * `jumps` - The goto index ([`goto_index`]).
/// * `labels` - The labels declared inside the run.
/// * `from` - The line before the run.
/// * `to` - The line after the run.
pub(super) fn jumps_contained(
    jumps: &BTreeMap<String, Vec<usize>>,
    labels: &[String],
    from: usize,
    to: usize,
) -> bool {
    labels.iter().all(|l| {
        jumps
            .get(l)
            .is_some_and(|sites| sites.iter().all(|&f| f > from && f < to))
    })
}

/// Tells whether a trimmed line begins with the keyword `kw` as a whole
/// word: `return;` and `return x;` begin with `return`, a call to a
/// function named `returnBuffer` does not.
///
/// Function names come from the binary (exports, debug information,
/// asserts), so a prefix test without the word boundary lets a hostile name
/// pass for a keyword.
///
/// # Arguments
///
/// * `t` - The line without indentation.
/// * `kw` - The keyword.
pub(super) fn starts_with_keyword(t: &str, kw: &str) -> bool {
    t.strip_prefix(kw)
        .is_some_and(|rest| !rest.starts_with(is_ident_char))
}

/// Tells whether a trimmed line is a `return` statement.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn is_return(t: &str) -> bool {
    starts_with_keyword(t, "return")
}

/// Tells whether a line leaves unconditionally (nothing textually after it runs).
///
/// # Arguments
///
/// * `line` - One emitted line.
pub(super) fn transfers(line: &str) -> bool {
    let t = line.trim();
    is_goto(t)
        || is_return(t)
        || t == "break;"
        || t == "continue;"
        || t.ends_with("__builtin_trap();")
}

/// Tells whether a trimmed line breaks out, bare or under a condition or a
/// case label.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn breaks(t: &str) -> bool {
    t == "break;" || t.ends_with(" break;")
}

/// Tells whether a trimmed line continues a loop, bare or under a
/// condition.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn continues(t: &str) -> bool {
    t == "continue;" || t.ends_with(" continue;")
}

/// The condition of an `if (COND) {` line.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn if_opener(t: &str) -> Option<&str> {
    t.strip_prefix("if (")?.strip_suffix(") {")
}

/// The condition of an `if (COND) {` or `} else if (COND) {` line.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn guard_opener(t: &str) -> Option<&str> {
    t.strip_prefix("} else if (")
        .or_else(|| t.strip_prefix("if ("))?
        .strip_suffix(") {")
}

/// The value a `switch (VALUE) {` line dispatches on.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn switch_opener(t: &str) -> Option<&str> {
    t.strip_prefix("switch (")?.strip_suffix(") {")
}

/// Tells whether a trimmed line opens a loop: `while (...) {`, `for (...)
/// {` or `do {`.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn opens_loop(t: &str) -> bool {
    t.ends_with('{') && (t == "do {" || t.starts_with("while (") || t.starts_with("for ("))
}

/// Tells whether a trimmed line opens a `switch`.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn opens_switch(t: &str) -> bool {
    t.ends_with('{') && t.starts_with("switch (")
}

/// A braced block the text holds open, as the nesting scans track it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Scope {
    /// `while`, `for` or `do`: what `break` and `continue` bind to.
    Loop,
    /// `switch`: what `break` binds to and `continue` passes through.
    Switch,
    /// Any other block: an `if` or `else` arm, a `case` arm.
    Block,
}

/// Tells whether a trimmed line closes the innermost open block: it begins
/// with `}` (`}`, `} else {`, `} while (...);`).
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn closes_scope(t: &str) -> bool {
    t.starts_with('}')
}

/// The block a trimmed line opens: a line ending in `{` opens one, a loop,
/// a `switch` or any other block (`if`, `} else {`, `case 3: {`).
///
/// The emitter writes one brace per line edge, so a statement (which ends
/// in `;`) never opens a block, whatever braces its string literals hold.
///
/// # Arguments
///
/// * `t` - The line without indentation.
///
/// # Returns
///
/// The block opened, or `None` when the line opens none.
pub(super) fn opens_scope(t: &str) -> Option<Scope> {
    if !t.ends_with('{') || t.starts_with("//") {
        return None;
    }
    Some(if opens_loop(t) {
        Scope::Loop
    } else if opens_switch(t) {
        Scope::Switch
    } else {
        Scope::Block
    })
}

/// Tells whether a trimmed line is a `case N:` or `default:` label.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn is_case(t: &str) -> bool {
    t.starts_with("case ") || t == "default:"
}

/// The net number of blocks a line opens: its `{` count less its `}`
/// count.
///
/// # Arguments
///
/// * `t` - The line.
pub(super) fn brace_delta(t: &str) -> i32 {
    i32::try_from(t.matches('{').count()).unwrap_or(0)
        - i32::try_from(t.matches('}').count()).unwrap_or(0)
}

/// Tells whether a line stands in the loop being emitted, keeping the blocks
/// the text opens on the way in `open`.
///
/// `break` binds to the innermost loop or switch around it, so a jump to
/// this loop's exit written inside a loop or switch the body itself opens
/// has to stay a jump.
///
/// # Arguments
///
/// * `line` - The line being scanned, in order.
/// * `open` - The blocks still open, innermost last; starts empty.
///
/// # Returns
///
/// Whether the line is in this loop rather than in a nested one.
pub(super) fn at_loop_level(line: &str, open: &mut Vec<Scope>) -> bool {
    at_level(line, open, Nesting::LoopsAndSwitches)
}

/// Tells whether a `continue` written on a line would continue the loop
/// being emitted, keeping the blocks the text opens on the way in `open`.
///
/// `continue` binds to the innermost loop around it and passes through a
/// switch, so a jump to this loop's head or latch inside a switch arm the
/// body opens is a `continue`, where a jump to its exit there has to stay
/// a jump ([`at_loop_level`]).
///
/// # Arguments
///
/// * `line` - The line being scanned, in order.
/// * `open` - The blocks still open, innermost last; starts empty.
///
/// # Returns
///
/// Whether the line is in this loop rather than in a nested one.
pub(super) fn at_continue_level(line: &str, open: &mut Vec<Scope>) -> bool {
    at_level(line, open, Nesting::Loops)
}

/// What opens a nesting level for [`at_level`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Nesting {
    /// Loops only: what a `continue` passes through.
    Loops,
    /// Loops and switches: what a `break` binds to.
    LoopsAndSwitches,
}

/// The scan behind [`at_loop_level`] and [`at_continue_level`].
///
/// Nesting is read from the braces, never from indentation: a `switch`
/// writes its `case N: {` arms and their closing braces at its own
/// indentation, so an indentation scan takes the first arm's `}` for the
/// switch's and reads every later arm as standing in the loop, where a
/// `break` leaves the switch instead.
///
/// # Arguments
///
/// * `line` - The line being scanned, in order.
/// * `open` - The blocks still open, innermost last.
/// * `nesting` - Whether a `switch` opens a level.
///
/// # Returns
///
/// Whether no loop (or switch, for [`Nesting::LoopsAndSwitches`]) is open
/// around the line; a line opening or closing one is in neither.
fn at_level(line: &str, open: &mut Vec<Scope>, nesting: Nesting) -> bool {
    let binds = |s: Scope| match nesting {
        Nesting::Loops => s == Scope::Loop,
        Nesting::LoopsAndSwitches => s != Scope::Block,
    };
    let t = line.trim();
    let mut edge = false;
    if closes_scope(t) {
        edge |= open.pop().is_some_and(binds);
    }
    let inside = open.iter().copied().any(binds);
    if let Some(s) = opens_scope(t) {
        edge |= binds(s);
        open.push(s);
    }
    !inside && !edge
}

/// Splits a plain assignment line `lhs = rhs;`.
///
/// # Arguments
///
/// * `line` - One emitted line.
///
/// # Returns
///
/// `(lhs, rhs)` when the left side is one identifier and the right side is
/// not itself an assignment (compound assignments and comparisons excluded).
pub(super) fn plain_assignment(line: &str) -> Option<(&str, &str)> {
    let t = line.trim().strip_suffix(';')?;
    let (l, r) = t.split_once(" = ")?;
    if !is_ident(l) || r.contains(" = ") || r.starts_with('=') {
        return None;
    }
    Some((l, r))
}

/// Tells whether a line writes `var`: an assignment, a compound one, an
/// increment, or an assignment nested in a condition or a chain.
///
/// # Arguments
///
/// * `t` - The trimmed line.
/// * `var` - The variable.
pub(super) fn writes_var(t: &str, var: &str) -> bool {
    /// What follows a variable that is being written.
    const WRITERS: [&str; 13] = [
        " = ", " += ", " -= ", " *= ", " /= ", " %= ", " &= ", " |= ", " ^= ", " <<= ", " >>= ",
        "++", "--",
    ];
    t.match_indices(var).any(|(i, _)| {
        let before = t.get(..i).unwrap_or("");
        let after = t.get(i + var.len()..).unwrap_or("");
        if before.ends_with(is_ident_char) || after.starts_with(is_ident_char) {
            return false;
        }
        before.ends_with("++")
            || before.ends_with("--")
            || WRITERS.iter().any(|w| after.starts_with(w))
    })
}

/// Tells whether a line takes the address of `var`, after which a callee
/// may change it.
///
/// # Arguments
///
/// * `line` - The line.
/// * `var` - The variable.
pub(super) fn takes_address(line: &str, var: &str) -> bool {
    line.match_indices(&format!("&{var}")).any(|(i, m)| {
        !line
            .get(i + m.len()..)
            .unwrap_or("")
            .starts_with(is_ident_char)
    })
}

/// Tells whether an expression may do something besides produce a value.
///
/// A call is impure: dropping it would drop what it does. Everything the
/// renderer writes with a name followed by `(`, and every indirect call
/// through a vtable slot, counts. A template instantiation's `(` follows the
/// `>` that closes its argument list (`Class::method<T>(...)`), so that too is
/// a call site; missing it dropped a whole tail call from a `void` function.
/// An operator's name ends in its symbol or its type
/// (`Array<int>::operator =(...)`, `operator ()(...)`,
/// `Ptr<T>::operator T *(...)`), so the first `(` after `operator` is one
/// too. A call through a pointer, `(*rax)(rcx)`, opens its arguments after
/// the parenthesized pointer read, where a cast's parentheses hold a type.
///
/// # Arguments
///
/// * `rhs` - The right side of an assignment, without its semicolon.
pub(super) fn impure(rhs: &str) -> bool {
    let bytes = rhs.as_bytes();
    rhs.char_indices().any(|(i, c)| {
        c == '('
            && i > 0
            && (bytes.get(i - 1).is_some_and(|b| {
                b.is_ascii_alphanumeric() || *b == b'_' || *b == b']' || *b == b'>'
            }) || ends_in_operator(rhs.get(..i).unwrap_or(""))
                || (bytes.get(i - 1) == Some(&b')')
                    && opening_paren(rhs, i - 1)
                        .is_some_and(|o| rhs.get(o..).is_some_and(|t| t.starts_with("(*")))))
    })
}

/// The index of the `(` the `)` at `close` closes.
///
/// # Arguments
///
/// * `text` - The line.
/// * `close` - Index of the closing parenthesis.
pub(super) fn opening_paren(text: &str, close: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in text.get(..=close)?.char_indices().rev() {
        match c {
            ')' => depth += 1,
            '(' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Tells whether text ends in an operator's name: `operator` and its symbol
/// or type, `operator =`, `operator ()`, `operator T *`, which a call's `(`
/// follows.
///
/// # Arguments
///
/// * `head` - The text before a `(`.
pub(super) fn ends_in_operator(head: &str) -> bool {
    head.rfind("operator").is_some_and(|k| {
        let rest = head.get(k + "operator".len()..).unwrap_or("");
        !head.get(..k).unwrap_or("").ends_with(is_ident_char)
            && !rest.starts_with(is_ident_char)
            && (rest.trim() == "()" || !rest.contains(['(', ')', ',', ';']))
    })
}

/// The index of the `)` closing the `(` at `open`.
///
/// # Arguments
///
/// * `text` - The line.
/// * `open` - Index of the opening parenthesis.
pub(super) fn matching_paren(text: &str, open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in text.char_indices().skip(open) {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Splits a call's argument text at the commas outside strings and brackets.
///
/// # Arguments
///
/// * `args` - The text between the call's parentheses.
///
/// # Returns
///
/// The trimmed arguments in order; one empty argument for empty text.
pub(super) fn split_arguments(args: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut depth, mut in_string, mut escaped, mut start) = (0usize, false, false, 0);
    for (i, c) in args.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' | '[' => depth += 1,
            ')' | ']' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                out.push(args[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(args[start..].trim());
    out
}

#[cfg(test)]
mod tests {
    use super::impure;

    /// A call to an operator is impure, whatever symbol ends its name.
    ///
    /// `Util::Array<int>::operator =(a1 + 8, a2 + 8)` is a tail call a
    /// `void` function makes; read as pure, its `return` dropped the call
    /// and the text claimed the function only copied a field.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn an_operator_call_counts_as_impure() {
        assert!(impure("Util::Array<int>::operator =(a1 + 8, a2 + 8)"));
        assert!(impure("Util::SubscriberNoParam<void>::operator ()(rcx)"));
        assert!(impure("Foo::operator ==(a1, a2)"));
        assert!(impure(
            "Core::Ptr<Game::GameActor>::operator Game::GameActor *(rcx)"
        ));
        assert!(!impure("(rax == operand) + 1"));
        assert!(!impure("rax + (rcx)"));
    }

    /// A call through a pointer is impure: `(*rax)(rcx)` and
    /// `(*(a1 + 8))(a1)` call what the pointer holds.
    ///
    /// A `void` function's `return (*rax)(rcx);` read as pure dropped the
    /// call whole and returned. A cast's parentheses (`(uint32_t)(a1)`) are
    /// no call.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_call_through_a_pointer_counts_as_impure() {
        assert!(impure("(*rax)(rcx)"));
        assert!(impure("(*(a1 + 8))(a1)"));
        assert!(impure("1 + (*rax)()"));
        assert!(!impure("(uint32_t)(a1)"));
        assert!(!impure("(uint8_t*)(a1 + 4)"));
    }
}
