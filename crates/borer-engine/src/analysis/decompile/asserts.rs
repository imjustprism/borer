//! Assertions: the calls to an assert reporter folded into `assert(...)` lines
//! with their source paths.

use super::*;

/// Longest `// asserts:` line before the rest is counted instead of listed.
pub(super) const ASSERTS_WIDTH: usize = 160;

/// The conditions a function asserts, as the header line `// asserts: ...`.
///
/// An assert macro compiles to a call that carries the text of the
/// condition, the source file and the line: a call whose first argument is
/// a string literal, whose second is a literal naming a C or C++ source
/// file, and whose third is a number. The first argument is what the code
/// promises about its inputs and state, so listing those conditions gives
/// the function's contract without reading its body. Conditions repeat
/// across a body and are listed once, in the order they appear.
///
/// The text lands in a comment, so a condition carrying a brace is skipped
/// and the quotes of one that names a string literal become single quotes:
/// a comment holding an escaped double quote leaves a reader that tracks
/// string literals inside one for the rest of the text.
///
/// # Arguments
///
/// * `body` - The decompiled body.
///
/// # Returns
///
/// The conditions joined by `, `, or `None` when the body asserts nothing.
pub fn asserts_of(body: &str) -> Option<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut conditions: Vec<String> = Vec::new();
    for line in body.lines() {
        for start in call_starts(line) {
            let Some(open) = line
                .get(start..)
                .and_then(|t| t.find('('))
                .map(|i| start + i)
            else {
                continue;
            };
            let Some(close) = matching_paren(line, open) else {
                continue;
            };
            let args = split_arguments(line.get(open + 1..close).unwrap_or(""));
            let [condition, path, number, ..] = args.as_slice() else {
                continue;
            };
            if !source_path(path) || parse_const(number).is_none() {
                continue;
            }
            let Some(text) = condition
                .strip_prefix('"')
                .and_then(|c| c.strip_suffix('"'))
                .filter(|c| !c.is_empty() && !c.contains(['{', '}']))
                .map(quotes_to_ticks)
            else {
                continue;
            };
            if seen.insert(text.clone()) {
                conditions.push(text);
            }
        }
    }
    if conditions.is_empty() {
        return None;
    }
    let mut out = String::new();
    let mut listed = 0;
    for c in &conditions {
        if !out.is_empty() && out.len() + c.len() + 2 > ASSERTS_WIDTH {
            break;
        }
        if !out.is_empty() {
            out.push_str(", ");
        }
        out.push_str(c);
        listed += 1;
    }
    if listed < conditions.len() {
        let _ = write!(out, ", +{} more", conditions.len() - listed);
    }
    Some(out)
}

/// Rewrites the quotes of an asserted condition as single quotes.
///
/// # Arguments
///
/// * `text` - The condition as the literal spelled it.
///
/// # Returns
///
/// The text with every double quote, escaped or not, a single quote.
pub(super) fn quotes_to_ticks(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' if chars.peek() == Some(&'"') => {
                chars.next();
                out.push('\'');
            }
            '"' => out.push('\''),
            other => out.push(other),
        }
    }
    out
}

/// The byte positions where a call's name starts on a line.
///
/// # Arguments
///
/// * `line` - One emitted line.
pub(super) fn call_starts(line: &str) -> Vec<usize> {
    let ident = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == ':' || c == '<' || c == '>';
    let mut out = Vec::new();
    let mut name: Option<usize> = None;
    for (i, c) in line.char_indices() {
        if ident(c) {
            name.get_or_insert(i);
            continue;
        }
        if c == '('
            && let Some(s) = name
        {
            out.push(s);
        }
        name = None;
    }
    out
}

/// Tells whether an argument is a literal naming a C or C++ source file.
///
/// # Arguments
///
/// * `arg` - The argument as rendered, quotes included.
pub(super) fn source_path(arg: &str) -> bool {
    const EXTENSIONS: [&str; 10] = [
        ".h", ".hpp", ".hh", ".hxx", ".inl", ".c", ".cc", ".cpp", ".cxx", ".inc",
    ];
    arg.strip_prefix('"')
        .and_then(|a| a.strip_suffix('"'))
        .is_some_and(|a| !a.contains(' ') && EXTENSIONS.iter().any(|e| a.ends_with(e)))
}

/// Most variables the asserts name in one function.
const ASSERT_NAMES_MAX: usize = 32;

/// Words an asserted condition uses that name no variable of the source.
const NOT_NAMES: &[&str] = &[
    "this",
    "true",
    "false",
    "nullptr",
    "NULL",
    "sizeof",
    "static_cast",
    "dynamic_cast",
    "reinterpret_cast",
    "const_cast",
    "int",
    "unsigned",
    "float",
    "double",
    "char",
    "bool",
    "void",
    "long",
    "short",
    "size_t",
    "return",
    "if",
    "else",
    "while",
    "for",
    "new",
    "delete",
    "and",
    "or",
    "not",
];

/// The registers the lifter leaves as variables.
const REGISTERS: &[&str] = &[
    "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8", "r9", "r10", "r11", "r12", "r13", "r14",
    "r15", "eax", "ebx", "ecx", "edx", "esi", "edi", "ebp",
];

/// The names a function's asserts give its parameters and locals.
///
/// An assert compiles to a guarded call: `if (a2 == 0) {
/// assert_failed("reader.isvalid()", "x.cc", 335); }`. The guard tests the
/// variable the condition speaks of, and the condition spells its source
/// name, so `a2` is `reader`. The guard must read exactly one parameter or
/// local, directly, through a dereference or through a register a smart
/// pointer's accessor loaded from it ([`guarded_variable`]); the condition
/// must name exactly one subject ([`subject_of`]). A name two variables
/// would take goes to neither, a variable two conditions name differently
/// keeps its own, and a name the text already uses outside its literals
/// and comments stays with its owner.
///
/// The rename covers the whole function while the name is only known to
/// hold where the guard tests it, and the text has no live ranges: one
/// stack slot or register carries unrelated values when the compiler
/// reuses it (`loadingElem = 0x500;` two hundred lines before the slot
/// holds the element). So only a variable that holds one value is renamed:
/// a parameter the body never assigns, a local assigned one value at most
/// ([`assigned_values`]).
///
/// # Arguments
///
/// * `lines` - The decompiled lines, the header included.
///
/// # Returns
///
/// The renames, in the order the asserts appear.
pub(super) fn assert_names(lines: &[String]) -> Vec<Rename> {
    let used: BTreeSet<String> = lines
        .iter()
        .filter(|l| !l.trim_start().starts_with("//"))
        .flat_map(|l| {
            let code = without_literals(l);
            words(&code)
                .map(|(w, _, _)| w.to_owned())
                .collect::<Vec<_>>()
        })
        .collect();
    let mut pairs: Vec<Rename> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let Some(condition) = asserted_condition(line) else {
            continue;
        };
        let Some(name) = subject_of(&condition) else {
            continue;
        };
        let Some(var) = guarded_variable(lines, i) else {
            continue;
        };
        if used.contains(&name) {
            continue;
        }
        let pair = Rename { var, name };
        if !pairs.contains(&pair) {
            pairs.push(pair);
        }
    }
    let all = pairs.clone();
    pairs.retain(|r| {
        all.iter().filter(|x| x.var == r.var).count() == 1
            && all.iter().filter(|x| x.name == r.name).count() == 1
            && assigned_values(lines, &r.var) + usize::from(is_param_name(&r.var)) <= 1
    });
    pairs.truncate(ASSERT_NAMES_MAX);
    pairs
}

/// Counts the values the code assigns a variable: by a plain, chained
/// (`a = b = 0;`) or nested (`if ((a = f()) != 0)`) assignment, a compound
/// one, or an increment.
///
/// One constant assigned in several places is one value (`tmpItem = 0;` on
/// two paths); any other assignment counts as a value of its own, since
/// `x = rax;` twice may store two. A store through the variable (`*(T*)a2
/// = 0;`) writes what it points at, not the variable, and a line inside a
/// comment or a literal writes nothing.
///
/// # Arguments
///
/// * `lines` - The decompiled lines.
/// * `var` - The variable.
pub(super) fn assigned_values(lines: &[String], var: &str) -> usize {
    /// Operators that write their left side from its old value.
    const UPDATES: [&str; 12] = [
        "++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=",
    ];
    let mut constants: BTreeSet<u64> = BTreeSet::new();
    let mut others = 0usize;
    for line in lines.iter().filter(|l| !l.trim_start().starts_with("//")) {
        let code = without_literals(line);
        for (w, start, end) in words(&code) {
            if w != var {
                continue;
            }
            let before = code[..start].trim_end();
            let after = code[end..].trim_start();
            let chained = before.ends_with('=')
                && !["==", "!=", "<=", ">="]
                    .iter()
                    .any(|op| before.ends_with(op));
            let starts_statement =
                before.is_empty() || before.ends_with(['{', ';', '(', ',']) || chained;
            if before.ends_with("++") || before.ends_with("--") {
                others += 1;
                continue;
            }
            if !starts_statement {
                continue;
            }
            if UPDATES.iter().any(|op| after.starts_with(op)) {
                others += 1;
            } else if let Some(rest) = after.strip_prefix('=').filter(|r| !r.starts_with('=')) {
                let value = rest.rsplit(" = ").next().unwrap_or(rest);
                match parse_const(value.trim().trim_end_matches(';')) {
                    Some(c) => {
                        constants.insert(c);
                    }
                    None => others += 1,
                }
            }
        }
    }
    constants.len() + others
}

/// A variable and the name the function's asserts give it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Rename {
    /// The variable as the lifter named it (`a2`, `local_8`, `rax`).
    pub(super) var: String,
    /// The source name the asserted condition spells.
    pub(super) name: String,
}

/// The condition an assert line carries, when the line is one.
///
/// # Arguments
///
/// * `line` - A decompiled line.
fn asserted_condition(line: &str) -> Option<String> {
    for start in call_starts(line) {
        let open = line.get(start..)?.find('(')? + start;
        let Some(close) = matching_paren(line, open) else {
            continue;
        };
        let args = split_arguments(line.get(open + 1..close)?);
        let [condition, path, number, ..] = args.as_slice() else {
            continue;
        };
        if !source_path(path) || parse_const(number).is_none() {
            continue;
        }
        return condition
            .strip_prefix('"')
            .and_then(|c| c.strip_suffix('"'))
            .map(str::to_owned);
    }
    None
}

/// The one subject an asserted condition speaks of, when it has one.
///
/// A subject is an identifier used as a value or an object (`reader` in
/// `reader.isvalid()`, `index` in `index < this->count`): not a keyword,
/// not a member after `.` or `->`, not a scope before or after `::`, not
/// a constant spelled in capitals. A free call (`IsValid(reader)`) tests
/// its result, not its argument, so a condition with one has no subject;
/// a condition with two subjects (`offers.Size() == amounts.Size()`) says
/// nothing about which variable is which.
///
/// # Arguments
///
/// * `condition` - The condition as the literal spelled it.
fn subject_of(condition: &str) -> Option<String> {
    let text = without_literals(condition);
    let mut subjects: Vec<&str> = Vec::new();
    for (w, start, end) in words(&text) {
        let before = text[..start].trim_end();
        let after = text[end..].trim_start();
        if after.starts_with('(') {
            if before.ends_with('.') || before.ends_with("->") {
                continue;
            }
            return None;
        }
        if NOT_NAMES.contains(&w)
            || w.chars().all(|c| c.is_ascii_uppercase() || c == '_')
            || before.ends_with('.')
            || before.ends_with("->")
            || before.ends_with("::")
            || after.starts_with("::")
        {
            continue;
        }
        if !subjects.contains(&w) {
            subjects.push(w);
        }
    }
    match subjects.as_slice() {
        [one] => Some((*one).to_owned()),
        _ => None,
    }
}

/// The parameter or local the guard of an assert tests, when it tests one.
///
/// The guard is the `if (...) {` line before the assert. It names the
/// variable when it reads exactly one parameter or local and no register
/// (`a2 == 0`, `*(uint64_t*)a3 == 0`, `!local_8`); when it reads one
/// register and nothing else, the line before the guard must have loaded
/// that register from the variable: a copy (`rax = a2;`), a dereference
/// (`rax = *(uint64_t*)a2;`) or a smart pointer's accessor
/// (`rax = Core::Ptr<T>::operator ->(a2);`).
///
/// # Arguments
///
/// * `lines` - The decompiled lines.
/// * `at` - The index of the assert line.
fn guarded_variable(lines: &[String], at: usize) -> Option<String> {
    let guard = if_opener(lines.get(at.checked_sub(1)?)?.trim())?;
    let mut vars: Vec<&str> = Vec::new();
    let mut regs: Vec<&str> = Vec::new();
    for (w, _, _) in words(guard) {
        if is_variable(w) && !vars.contains(&w) {
            vars.push(w);
        } else if REGISTERS.contains(&w) && !regs.contains(&w) {
            regs.push(w);
        }
    }
    match (vars.as_slice(), regs.as_slice()) {
        ([var], []) => Some((*var).to_owned()),
        ([], [reg]) => {
            let (lhs, rhs) = plain_assignment(lines.get(at.checked_sub(2)?)?)?;
            (lhs == *reg).then(|| loaded_variable(rhs)).flatten()
        }
        _ => None,
    }
}

/// The parameter or local a register was loaded from, when the
/// right-hand side is a copy, a dereference or an accessor call of one.
///
/// # Arguments
///
/// * `rhs` - The right-hand side of the register's assignment.
fn loaded_variable(rhs: &str) -> Option<String> {
    let rhs = rhs.trim();
    if is_variable(rhs) {
        return Some(rhs.to_owned());
    }
    if let Some(inner) = rhs.strip_prefix("*(")
        && let Some(cast) = inner.find("*)")
        && let Some(var) = inner.get(cast + 2..)
        && is_variable(var)
    {
        return Some(var.to_owned());
    }
    let callee = callee_of(rhs)?;
    accessor_class(callee)?;
    let arg = rhs
        .get(callee.len()..)?
        .trim()
        .strip_prefix('(')?
        .strip_suffix(')')?
        .trim();
    is_variable(arg).then(|| arg.to_owned())
}

/// Tells whether a word is a parameter or a local the text could rename.
///
/// # Arguments
///
/// * `w` - The word.
fn is_variable(w: &str) -> bool {
    is_param_name(w) || w.starts_with("local_") || w.starts_with("home_") || w.starts_with("tmp_")
}

/// The identifier-shaped words of a text with their byte spans, in order.
///
/// # Arguments
///
/// * `text` - Any text.
fn words(text: &str) -> impl Iterator<Item = (&str, usize, usize)> {
    let mut at = 0;
    tokens(text).filter_map(move |w| {
        let start = text[at..].find(w).map(|i| at + i)?;
        at = start + w.len();
        (!w.starts_with(|c: char| c.is_ascii_digit())).then_some((w, start, start + w.len()))
    })
}

/// A line with its string literals blanked, so their words are not words
/// of the code.
///
/// # Arguments
///
/// * `line` - The line.
fn without_literals(line: &str) -> String {
    let mut out = String::with_capacity(line.len());
    let mut in_literal = false;
    let mut escaped = false;
    for c in line.chars() {
        match (in_literal, c) {
            (false, '"') => {
                in_literal = true;
                out.push(' ');
            }
            (false, c) => out.push(c),
            (true, '\\') if !escaped => escaped = true,
            (true, '"') if !escaped => in_literal = false,
            (true, _) => escaped = false,
        }
    }
    out
}

#[cfg(test)]
mod naming_tests {
    use super::{Rename, assert_names, guarded_variable, subject_of};

    /// The subject is the one identifier the condition uses as a value;
    /// members, scopes, keywords, constants and free calls are not it.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn subjects_are_the_one_value_a_condition_names() {
        assert_eq!(subject_of("reader.isvalid()").as_deref(), Some("reader"));
        assert_eq!(subject_of("index < this->count").as_deref(), Some("index"));
        assert_eq!(subject_of("node != nullptr").as_deref(), Some("node"));
        assert_eq!(
            subject_of("0 <= index && index < MAX_SLOTS").as_deref(),
            Some("index")
        );
        assert_eq!(
            subject_of("ptr->IsA(Game::Entity::RTTI)").as_deref(),
            Some("ptr")
        );
        assert_eq!(subject_of("offers.Size() == amounts.Size()"), None);
        assert_eq!(subject_of("IsValid(reader)"), None);
        assert_eq!(subject_of("this->handled"), None);
        assert_eq!(subject_of("0 == strcmp(name, \"x\")"), None);
    }

    /// The guard names its one variable: directly, through a dereference,
    /// or through a register an accessor loaded from it.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn guards_name_the_variable_they_test() {
        let lines = |v: &[&str]| v.iter().map(|l| (*l).to_owned()).collect::<Vec<_>>();
        let direct = lines(&["if (a2 == 0) {", "  fail();"]);
        assert_eq!(guarded_variable(&direct, 1).as_deref(), Some("a2"));
        let deref = lines(&["if (*(uint64_t*)a3 == 0) {", "  fail();"]);
        assert_eq!(guarded_variable(&deref, 1).as_deref(), Some("a3"));
        let accessor = lines(&[
            "rax = Core::Ptr<Game::Offer>::operator ->(a2);",
            "if (rax == 0) {",
            "  fail();",
        ]);
        assert_eq!(guarded_variable(&accessor, 2).as_deref(), Some("a2"));
        let two = lines(&["if (a1 == a2) {", "  fail();"]);
        assert_eq!(guarded_variable(&two, 1), None);
        let computed = lines(&["rax = sub_1(a2);", "if (rax == 0) {", "  fail();"]);
        assert_eq!(guarded_variable(&computed, 2), None);
    }

    /// Two asserts name two parameters; a name the code already uses and a
    /// name two variables would take are given to no one.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn asserts_name_parameters_once() {
        let text = [
            "// signature: bool f(void *this, void *a2, void *a3, void *a4, void *a5)",
            "if (a2 == 0) {",
            "  assert(\"reader.isvalid()\", \"x.cc\", 10);",
            "}",
            "if (*(uint64_t*)a3 == 0) {",
            "  assert(\"group.isvalid()\", \"x.cc\", 11);",
            "}",
            "if (a4 == 0) {",
            "  assert(\"group.isvalid()\", \"x.cc\", 12);",
            "}",
            "if (a5 == 0) {",
            "  assert(\"table != nullptr\", \"x.cc\", 13);",
            "}",
            "table = sub_1(a5);",
        ];
        let lines: Vec<String> = text.iter().map(|l| (*l).to_owned()).collect();
        assert_eq!(
            assert_names(&lines),
            vec![Rename {
                var: "a2".to_owned(),
                name: "reader".to_owned()
            }]
        );
    }

    /// Only a variable that holds one value takes an assert's name.
    ///
    /// A slot the compiler reused for an unrelated value earlier, or a
    /// parameter the body overwrites, keeps the lifter's name, while a
    /// store through a parameter, a local assigned once and a local zeroed
    /// on two paths do not stop the rename.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn asserts_name_only_variables_holding_one_value() {
        let text = [
            "// signature: void f(void *this, void *a2, void *a3)",
            "local_10 = 0x500;",
            "sub_1(local_10);",
            "local_10 = sub_2(this);",
            "if (local_10 == 0) {",
            "  assert(\"loadingElem.isvalid()\", \"x.cc\", 10);",
            "}",
            "local_18 = sub_3(this);",
            "if (local_18 == 0) {",
            "  assert(\"label.isvalid()\", \"x.cc\", 11);",
            "}",
            "*(uint64_t*)a2 = local_18;",
            "if (a2 == 0) {",
            "  assert(\"reader.isvalid()\", \"x.cc\", 12);",
            "}",
            "if (a3 == 0) {",
            "  assert(\"group.isvalid()\", \"x.cc\", 13);",
            "}",
            "for (a3 = sub_4(); a3 != 0; a3 = sub_5(a3)) {",
            "}",
            "local_20 = 0;",
            "if (a3 == 0) {",
            "  local_20 = 0;",
            "}",
            "sub_6(&local_20);",
            "if (local_20 == 0) {",
            "  assert(\"item.isvalid()\", \"x.cc\", 14);",
            "}",
        ];
        let lines: Vec<String> = text.iter().map(|l| (*l).to_owned()).collect();
        let renamed: Vec<(String, String)> = assert_names(&lines)
            .into_iter()
            .map(|r| (r.var, r.name))
            .collect();
        assert_eq!(
            renamed,
            vec![
                ("local_18".to_owned(), "label".to_owned()),
                ("a2".to_owned(), "reader".to_owned()),
                ("local_20".to_owned(), "item".to_owned()),
            ]
        );
    }
}
