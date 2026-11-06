//! Machine-word variables the text reads as signed, declared signed.

use super::*;

/// What something other than the code typed in a function, which
/// [`signed_words`] leaves as it is.
#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Stated {
    /// A prototype, debug information, the user or a known signature typed
    /// the parameters.
    pub(super) params: bool,
    /// Debug information or the user typed the locals.
    pub(super) locals: bool,
}

/// Text that computes in the operand's type, where a signed type's
/// overflow is undefined and an unsigned one's wraps.
const ARITH_OPS: [&str; 4] = [" + ", " - ", " * ", " << "];

/// The types an integer converts to by its sign: the floats and the
/// 128-bit integers, and pointers to them, through which a store converts.
const WIDE_TYPES: [&str; 3] = ["double", "float", "int128_t"];

/// Tells whether a type is or points to one of [`WIDE_TYPES`].
///
/// # Arguments
///
/// * `ty` - The type as the text spells it.
fn wide_type(ty: &str) -> bool {
    WIDE_TYPES.iter().any(|w| ty.contains(w))
}

/// The writes of a variable whose result is the same in either sign: a
/// store, the sign-blind compound assignments, an increment.
const STEPS: [&str; 9] = [
    " = ", " += ", " -= ", " *= ", " &= ", " |= ", " ^= ", "++", "--",
];

/// Text that makes a read's meaning depend on its operand's sign: an
/// ordered compare, a division, a right shift.
const SIGNED_OPS: [&str; 10] = [
    " < ", " > ", " <= ", " >= ", " / ", " % ", " >> ", " /= ", " %= ", " >>= ",
];

/// Declares signed a machine word the text reads only as signed.
///
/// A `uint64_t` parameter or local is `int64_t` when the text casts it
/// `(int64_t)` and reads it nowhere else in a way its sign changes, and a
/// `uint32_t` one `int32_t` the same way on a 32-bit target, where a
/// function naming a 64-bit type keeps its words: there a copy widens.
///
/// Unoptimized code compares a `long` loop counter signed, and the text
/// prints each compare `(int64_t)i < (int64_t)n`. The bitwise operators,
/// an equality, an index, a copy and a call give the same bits in either
/// type, so where a line reads the variable outside a cast, it may hold
/// none of [`SIGNED_OPS`]; nor any of [`ARITH_OPS`] or a negation, whose
/// signed overflow C leaves undefined where the unsigned one wraps. A
/// store, a step or a compound assignment of it computes as its source
/// spells, as for the `int32_t` locals [`super::type_locals`] signs. A
/// variable whose
/// address is taken, that is read as a pointer, or that is read on a line
/// naming one of [`WIDE_TYPES`] or a variable of one, or holding a float
/// literal, keeps
/// its type, as does one a function returning a float or 128 bits returns.
/// A line holding a string, a character or a comment decides nothing, so
/// a variable it names keeps its type too.
///
/// # Arguments
///
/// * `text` - A decompiled function, types already applied.
/// * `stated` - What something other than the code typed, which a read
///   does not overrule.
/// * `word` - The machine word's type, `uint64_t` or `uint32_t`.
pub(super) fn signed_words(text: &str, stated: Stated, word: &str) -> String {
    let Some(int) = word.strip_prefix('u') else {
        return text.to_owned();
    };
    if word != "uint64_t" && text.contains("int64_t") {
        return text.to_owned();
    }
    let decl = format!("{word} ");
    let lines: Vec<&str> = text.lines().collect();
    let all = signature_params(text);
    let params: Vec<String> = all
        .iter()
        .filter(|(_, ty)| !stated.params && ty == word)
        .map(|(name, _)| name.clone())
        .collect();
    let locals: Vec<String> = lines
        .iter()
        .filter(|_| !stated.locals)
        .filter_map(|l| declared(l, &decl))
        .flatten()
        .collect();
    let floats: Vec<String> = lines
        .iter()
        .filter_map(|l| {
            let (ty, names) = l.trim().strip_suffix(';')?.split_once(' ')?;
            let names: Vec<String> = names
                .split(", ")
                .map(|n| n.trim_start_matches('*').to_owned())
                .collect();
            (wide_type(ty) && names.iter().all(|n| is_ident(n))).then_some(names)
        })
        .flatten()
        .chain(
            all.iter()
                .filter(|(_, ty)| wide_type(ty))
                .map(|(name, _)| name.clone()),
        )
        .collect();
    let header: Vec<String> = lines
        .iter()
        .filter(|l| l.starts_with("// signature: "))
        .map(|l| (*l).to_owned())
        .collect();
    let float_result = signature_result(&header).is_some_and(wide_type);
    let signed: Vec<&String> = params
        .iter()
        .chain(&locals)
        .filter(|n| reads_signed(&lines, n, (&decl, int), &floats, float_result))
        .collect();
    if signed.is_empty() {
        return text.to_owned();
    }
    let mut out = String::with_capacity(text.len());
    for line in &lines {
        let mut line = (*line).to_owned();
        if line.starts_with("// signature: ") {
            for name in &signed {
                line = line
                    .replace(&format!("{word} {name},"), &format!("{int} {name},"))
                    .replace(&format!("{word} {name})"), &format!("{int} {name})"));
            }
        } else if let Some(names) = declared(&line, &decl) {
            let (moved, kept): (Vec<String>, Vec<String>) =
                names.into_iter().partition(|n| signed.contains(&n));
            let pad = pad_of(&line).to_owned();
            line = [(word, kept), (int, moved)]
                .into_iter()
                .filter(|(_, names)| !names.is_empty())
                .map(|(ty, names)| format!("{pad}{ty} {};", names.join(", ")))
                .collect::<Vec<_>>()
                .join("\n");
        } else if !line.starts_with("//") {
            for name in &signed {
                line = uncast(&line, name, int);
            }
        }
        out.push_str(&line);
        out.push('\n');
    }
    out
}

/// The names a declaration line of `ty` declares, without initializers.
///
/// # Arguments
///
/// * `line` - One line.
/// * `ty` - The type with its trailing space (`"uint64_t "`).
fn declared(line: &str, ty: &str) -> Option<Vec<String>> {
    let names = line.trim().strip_prefix(ty)?.strip_suffix(';')?;
    let names: Vec<String> = names.split(", ").map(str::to_owned).collect();
    names.iter().all(|n| is_ident(n)).then_some(names)
}

/// Tells whether `name` is read through `(int64_t)` at least once and in
/// no way its sign changes.
///
/// # Arguments
///
/// * `lines` - The function.
/// * `name` - The variable.
/// * `floats` - The float and 128-bit variables.
/// * `float_result` - Whether the function returns a float or 128 bits.
fn reads_signed(
    lines: &[&str],
    name: &str,
    (decl, int): (&str, &str),
    floats: &[String],
    float_result: bool,
) -> bool {
    let cast = format!("({int}){name}");
    let mut cast_seen = false;
    for line in lines
        .iter()
        .filter(|l| !l.starts_with("//") && declared(l, decl).is_none() && mentions_ident(l, name))
    {
        let t = line.trim();
        if t.contains(['"', '\'']) || t.contains("/*") {
            return false;
        }
        cast_seen |= cast_reads(t, &cast).next().is_some();
        let rest = without_casts(t, &cast);
        let float_line =
            floats.iter().any(|f| mentions_ident(t, f)) || wide_type(t) || float_literal(&rest);
        let mut read = false;
        for at in word_positions(&rest, name) {
            let head = rest.get(..at).unwrap_or("").trim_end();
            let tail = rest.get(at + name.len()..).unwrap_or("");
            if head.ends_with('&') && !head.ends_with("&&")
                || dereferences(head)
                || tail.starts_with(['[', '.'])
                || tail.starts_with("->")
            {
                return false;
            }
            let target = head.is_empty() || head.ends_with(';') || head.ends_with("for (");
            if target
                && [" /= ", " %= ", " >>= "]
                    .iter()
                    .any(|op| tail.starts_with(op))
            {
                return false;
            }
            if target && STEPS.iter().any(|op| tail.starts_with(op)) {
                continue;
            }
            if !float_line && equality_operand(head, tail) {
                continue;
            }
            read = true;
        }
        if !read {
            continue;
        }
        let with_float = floats.iter().any(|f| mentions_ident(t, f)) || wide_type(t);
        let returned = float_result && starts_with_keyword(t, "return");
        let arith = ARITH_OPS.iter().any(|op| rest.contains(op)) || negates(&rest);
        if with_float
            || returned
            || arith
            || float_literal(&rest)
            || SIGNED_OPS.iter().any(|op| rest.contains(op))
        {
            return false;
        }
    }
    cast_seen
}

/// Tells whether a read is a whole side of an equality, `a1 == 5` in a
/// condition, a select or an argument, whose value is the same in either
/// sign whatever the rest of its line computes.
///
/// An operator binding tighter than `==` in front of it (`x + a1 == 5`,
/// `x <= a1 == 1`) makes it that operator's operand instead, and a decimal
/// literal past `INT_MAX` on the other side (`a1 == 4294967295`) is of a
/// wider type, which widens the word by its sign.
///
/// # Arguments
///
/// * `head` - The line before the read, trimmed at the end.
/// * `tail` - The line after it.
fn equality_operand(head: &str, tail: &str) -> bool {
    let opens = head.is_empty()
        || ["(", "&&", "||", "?", ":", ","]
            .iter()
            .any(|p| head.ends_with(p))
        || (head.ends_with(" =") && !head.ends_with("==") && !head.ends_with("!="));
    let Some(other) = tail
        .strip_prefix(" == ")
        .or_else(|| tail.strip_prefix(" != "))
    else {
        return false;
    };
    let digits = other.trim_start_matches('-');
    let end = digits
        .find(|c: char| !c.is_ascii_alphanumeric())
        .unwrap_or(digits.len());
    let literal = digits.get(..end).unwrap_or("");
    let narrow = literal.starts_with("0x")
        || !literal.starts_with(|c: char| c.is_ascii_digit())
        || literal.parse::<u32>().is_ok_and(|v| v <= 0x7fff_ffff);
    opens && narrow
}

/// Tells whether a line negates something: a `-` that no operand
/// precedes.
///
/// # Arguments
///
/// * `line` - One line.
fn negates(line: &str) -> bool {
    line.match_indices('-').any(|(at, _)| {
        let before = line.get(..at).unwrap_or("").trim_end();
        let next = line.get(at + 1..).unwrap_or("");
        !next.starts_with([' ', '=', '-', '>']) && !operand_ends(before)
    })
}

/// Tells whether a line holds a float literal (`1.5`, `2.0f`), which
/// converts an integer it meets by its sign.
///
/// # Arguments
///
/// * `line` - One line.
fn float_literal(line: &str) -> bool {
    line.as_bytes()
        .windows(3)
        .any(|w| matches!(w, [a, b'.', c] if a.is_ascii_digit() && c.is_ascii_digit()))
}

/// The offsets of each `(int64_t)` read of a name in `line`.
///
/// # Arguments
///
/// * `line` - One line.
/// * `cast` - `(int64_t)` followed by the name.
fn cast_reads<'a>(line: &'a str, cast: &'a str) -> impl Iterator<Item = usize> + 'a {
    line.match_indices(cast)
        .map(|(at, _)| at)
        .filter(move |&at| {
            !line
                .get(at + cast.len()..)
                .is_some_and(|r| r.starts_with(is_ident_char))
        })
}

/// Tells whether the text before a name ends in a dereference, a `*` no
/// operand precedes.
///
/// # Arguments
///
/// * `head` - The line up to the name, trailing spaces trimmed.
fn dereferences(head: &str) -> bool {
    let Some(before) = head.strip_suffix('*').map(str::trim_end) else {
        return false;
    };
    !operand_ends(before)
}

/// Tells whether text ends in an operand: a name, a constant or a closing
/// bracket, not a keyword such as `return`.
///
/// # Arguments
///
/// * `before` - The text, trailing spaces trimmed.
fn operand_ends(before: &str) -> bool {
    let word = before
        .rsplit(|c: char| !is_ident_char(c))
        .next()
        .unwrap_or("");
    before.ends_with(|c: char| is_ident_char(c) || matches!(c, ')' | ']')) && word != "return"
}

/// The line with each `(int64_t)` read of a name replaced by `_`.
///
/// # Arguments
///
/// * `line` - One line.
/// * `cast` - `(int64_t)` followed by the variable's name.
fn without_casts(line: &str, cast: &str) -> String {
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(at) = cast_reads(rest, cast).next() {
        out.push_str(rest.get(..at).unwrap_or(""));
        out.push('_');
        rest = rest.get(at + cast.len()..).unwrap_or("");
    }
    out.push_str(rest);
    out
}

/// The line with each `(int64_t)` directly before `name` dropped.
///
/// # Arguments
///
/// * `line` - One line.
/// * `name` - A variable now declared `int64_t`.
fn uncast(line: &str, name: &str, int: &str) -> String {
    let cast = format!("({int}){name}");
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(at) = rest.find(&cast) {
        out.push_str(rest.get(..at).unwrap_or(""));
        let after = rest.get(at + cast.len()..).unwrap_or("");
        if after.starts_with(is_ident_char) {
            out.push_str(&cast);
        } else {
            out.push_str(name);
        }
        rest = after;
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::{Stated, signed_words};

    /// Runs the pass on a body under `sig`, no type stated.
    fn run(sig: &str, body: &str) -> String {
        signed_words(
            &format!("// signature: {sig}\n{body}"),
            Stated::default(),
            "uint64_t",
        )
    }

    /// On a 32-bit target a word compared signed is `int32_t`.
    ///
    /// A whole side of an equality reads the same in either sign, whatever
    /// its line adds; an operand of a sum compared, an equality with a
    /// float, or a function naming a 64-bit type keeps the word.
    ///
    /// # Panics
    ///
    /// When a signed word keeps its cast, or a kept one loses it.
    #[test]
    fn a_32_bit_word_compared_signed_is_signed() {
        let run32 = |body: &str| {
            signed_words(
                &format!("// signature: void f(uint32_t a1)\n{body}"),
                Stated::default(),
                "uint32_t",
            )
        };
        let out = run32("if ((int32_t)a1 > 5) {\n  r0 = (a1 == 7 ? 3 : 4) + 1;\n}\n");
        assert!(out.contains("void f(int32_t a1)"), "{out}");
        assert!(out.contains("if (a1 > 5) {"), "{out}");
        for body in [
            "if ((int32_t)a1 > 5 && r0 + a1 == 9) {\n  return;\n}\n",
            "uint64_t v;\n\nif ((int32_t)a1 > 5) {\n  v = a1;\n}\n",
            "if ((int32_t)a1 > 5 || (a1 == 4294967295.0 ? 1 : 0) + 1) {\n  return;\n}\n",
            "if ((int32_t)a1 > 5) {\n  r0 = (a1 == 4294967295 ? 1 : 0) + 1;\n}\n",
        ] {
            let out = run32(body);
            assert!(out.contains("void f(uint32_t a1)"), "{out}");
            assert!(out.contains("(int32_t)a1 > 5"), "{out}");
        }
    }

    /// A loop counter and its bound compared signed are `int64_t`; their
    /// indices, bitwise operations and steps read the same in either type.
    ///
    /// # Panics
    ///
    /// When a signed word keeps its cast or its unsigned type.
    #[test]
    fn a_word_compared_signed_is_signed() {
        let out = run(
            "void f(uint64_t a1)",
            "uint64_t local_20, local_28;\n\nif ((int64_t)a1 <= 0) {\n  return;\n}\nfor (local_20 = 0; (int64_t)local_20 < (int64_t)a1; local_20 += 1) {\n  ((uint64_t*)local_28)[local_20] = local_20 ^ 5;\n}\n",
        );
        assert!(out.contains("void f(int64_t a1)"), "{out}");
        assert!(
            out.contains("uint64_t local_28;\nint64_t local_20;"),
            "{out}"
        );
        assert!(out.contains("if (a1 <= 0) {"), "{out}");
        assert!(out.contains("local_20 < a1;"), "{out}");
        assert!(!out.contains("(int64_t)"), "{out}");
    }

    /// A stated parameter type stands while an unstated local is typed, and
    /// a stated local type stands too.
    ///
    /// # Panics
    ///
    /// When a stated type changes or an unstated local keeps its cast.
    #[test]
    fn a_stated_type_stands() {
        let text = "// signature: void f(uint64_t a1)\nuint64_t local_8;\n\nif ((int64_t)a1 <= 0 || (int64_t)local_8 > 3) {\n  return;\n}\n";
        let params = Stated {
            params: true,
            locals: false,
        };
        let out = signed_words(text, params, "uint64_t");
        assert!(out.contains("void f(uint64_t a1)"), "{out}");
        assert!(out.contains("int64_t local_8;"), "{out}");
        assert!(out.contains("(int64_t)a1 <= 0 || local_8 > 3"), "{out}");
        let locals = Stated {
            params: false,
            locals: true,
        };
        let out = signed_words(text, locals, "uint64_t");
        assert!(out.contains("void f(int64_t a1)"), "{out}");
        assert!(out.contains("uint64_t local_8;"), "{out}");
    }

    /// A read whose meaning its sign changes, or whose arithmetic would
    /// overflow a signed type where the unsigned one wraps, keeps the
    /// variable unsigned.
    ///
    /// # Panics
    ///
    /// When a word read unsigned is declared signed.
    #[test]
    fn a_word_read_unsigned_keeps_its_type() {
        let test = "if ((int64_t)a1 <= 0) {\n  return;\n}\n";
        for tail in [
            "return a1 / 3;\n",
            "return a1 >> 3;\n",
            "return (int64_t)(a1 >> 1);\n",
            "if (a1 < 9) {\n  return;\n}\n",
            "return (double)(a1 | 1);\n",
            "f(&a1);\n",
            "return a1 * a1;\n",
            "return a1 + 1;\n",
            "return -a1;\n",
            "return a1 ^ 1.5;\n",
            "puts(\"a1 / 2\");\n",
            "return *a1;\n",
        ] {
            let out = run("void f(uint64_t a1)", &format!("{test}{tail}"));
            assert!(out.contains("void f(uint64_t a1)"), "{out}");
        }
        let out = run("void f(uint64_t a1)", "if (a1 <= 0) {\n  return;\n}\n");
        assert!(out.contains("void f(uint64_t a1)"), "{out}");
        for (sig, decl) in [
            ("void f(uint64_t a1)", "double d;\n\n"),
            ("void f(uint64_t a1)", "uint128_t d;\n\n"),
            ("void f(uint64_t a1, double d)", ""),
            ("void f(uint64_t a1, double *d)", ""),
        ] {
            let out = run(sig, &format!("{decl}{test}d = a1;\n"));
            assert!(out.contains("(uint64_t a1"), "{out}");
        }
        for (sig, store) in [
            ("void f(uint64_t a1, double *p)", "*p = a1;\n"),
            ("void f(uint64_t a1, uint64_t p)", "*(double*)p = a1;\n"),
        ] {
            let out = run(sig, &format!("{test}{store}"));
            assert!(out.contains("(uint64_t a1"), "{out}");
        }
    }
}
