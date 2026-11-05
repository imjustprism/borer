//! Unsigned compares of a value an earlier test proved non-negative,
//! written as the signed compares a source spells.

use super::*;

/// The largest constant a compare or a guard may take: the largest
/// `int32_t`, so the constant is an `int` in C and the compare is signed.
const INT32_MAX: u64 = 0x7fff_ffff;

/// One open block as [`guarded_compares`] tracks it.
#[derive(Debug, Default)]
struct Open {
    /// The names the block's own test proved non-negative.
    facts: Vec<String>,
    /// The names an early exit inside the block proved non-negative from
    /// that exit on.
    after: Vec<String>,
    /// The names the block's test proved negative or zero, when the block
    /// is an `if` that could be an early exit.
    exits: Vec<String>,
    /// Whether the block's last statement leaves it whatever happens: a
    /// `return`, `goto`, `break` or `continue` of its own, not one under an
    /// `if` on the same line.
    leaves: bool,
}

/// Drops the `(uint32_t)` of an `int32_t` compared with a small constant
/// where an earlier test proved it non-negative.
///
/// A compiler that knows `n > 0` compares `n < 4` unsigned, and the text
/// prints `(uint32_t)n < 4`. Inside `if (n > 0) {`, and after `if (n <= 0)
/// { return ...; }`, the two compares agree for every value that gets
/// there, so the cast says nothing. Only a name nothing assigns or takes
/// the address of counts, and a label or `case` ends every fact, since a
/// jump to it can come from where the test did not run. A line holding a
/// string literal is left alone.
///
/// # Arguments
///
/// * `text` - A decompiled function, types already applied.
pub(super) fn guarded_compares(text: &str) -> String {
    let signed: Vec<String> = signed_names(text)
        .into_iter()
        .filter(|n| !written(text, n))
        .collect();
    if signed.is_empty() {
        return text.to_owned();
    }
    let mut open: Vec<Open> = vec![Open::default()];
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        let t = line.trim();
        if t.starts_with("//") {
            out.push_str(line);
            out.push('\n');
            continue;
        }
        if is_label(t) || is_case(t) {
            for o in &mut open {
                o.facts.clear();
                o.after.clear();
            }
        }
        if closes_scope(t) && open.len() > 1 {
            let done = open.pop().unwrap_or_default();
            if t == "}"
                && done.leaves
                && let Some(top) = open.last_mut()
            {
                top.after.extend(done.exits);
            }
        }
        let known: Vec<&str> = open
            .iter()
            .flat_map(|o| o.facts.iter().chain(&o.after))
            .map(String::as_str)
            .collect();
        let mut rewritten = line.to_owned();
        for name in known.into_iter().filter(|_| !t.contains('"')) {
            rewritten = unsign(&rewritten, name);
        }
        if let Some(top) = open.last_mut() {
            top.leaves = is_return(t) || is_goto(t) || matches!(t, "break;" | "continue;");
        }
        if opens_scope(t).is_some() {
            let plain = |c: &&str| !c.contains('"');
            let test = guard_opener(t).filter(plain).unwrap_or("");
            let exit = if_opener(t).filter(plain).unwrap_or("");
            open.push(Open {
                facts: proved(test, &signed, Proof::NonNegative),
                exits: proved(exit, &signed, Proof::Exit),
                ..Open::default()
            });
        }
        out.push_str(&rewritten);
        out.push('\n');
    }
    out
}

/// What a test must prove of a name for [`proved`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Proof {
    /// The name is non-negative where the test holds: `n > k` or `n >= k`.
    NonNegative,
    /// The name is non-negative where the test fails: `n <= k` or `n < k`.
    Exit,
}

/// The names of `signed` a test proves non-negative, where it holds or
/// where it fails.
///
/// # Arguments
///
/// * `test` - The condition of an `if`: plain compares joined by `&&` or
///   by `||`, with no parentheses, `!` or `?` that could nest one.
/// * `signed` - The names that may count.
/// * `proof` - Where the test must prove it.
fn proved(test: &str, signed: &[String], proof: Proof) -> Vec<String> {
    if test.contains(['(', '!', '?']) {
        return Vec::new();
    }
    let parts: Vec<&str> = match proof {
        Proof::NonNegative if !test.contains("||") => test.split(" && ").collect(),
        Proof::Exit if !test.contains("&&") => test.split(" || ").collect(),
        _ => Vec::new(),
    };
    parts
        .into_iter()
        .filter_map(|part| {
            let (name, rest) = part.split_once(' ')?;
            let (op, k) = rest.split_once(' ')?;
            let floor = match (proof, op, k) {
                (Proof::NonNegative, ">", "-1") | (Proof::Exit, "<=", "-1") => true,
                (Proof::NonNegative, ">" | ">=", k) | (Proof::Exit, "<=" | "<", k) => {
                    parse_const(k).is_some_and(|k| k <= INT32_MAX)
                }
                _ => false,
            };
            (floor && signed.iter().any(|s| s == name)).then(|| name.to_owned())
        })
        .collect()
}

/// The parameters and locals declared `int32_t`.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
fn signed_names(text: &str) -> Vec<String> {
    let mut out: Vec<String> = signature_params(text)
        .into_iter()
        .filter(|(_, ty)| ty == "int32_t")
        .map(|(name, _)| name)
        .collect();
    for line in text.lines() {
        if let Some(names) = line
            .trim()
            .strip_prefix("int32_t ")
            .and_then(|r| r.strip_suffix(';'))
        {
            out.extend(names.split(", ").filter(|n| is_ident(n)).map(str::to_owned));
        }
    }
    out
}

/// Tells whether a line of the body assigns `name`, steps it or takes its
/// address.
///
/// # Arguments
///
/// * `text` - The function.
/// * `name` - The variable.
fn written(text: &str, name: &str) -> bool {
    const STEPS: [&str; 12] = [
        "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "++", "--",
    ];
    text.lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .any(|line| {
            word_positions(line, name).into_iter().any(|at| {
                let head = line.get(..at).unwrap_or("").trim_end();
                let tail = line.get(at + name.len()..).unwrap_or("").trim_start();
                let assigns = tail.starts_with('=') && !tail.starts_with("==");
                let address = head.ends_with('&') && !head.ends_with("&&");
                assigns
                    || address
                    || STEPS.iter().any(|s| tail.starts_with(s))
                    || head.ends_with("++")
                    || head.ends_with("--")
            })
        })
}

/// Drops the `(uint32_t)` from each compare of `name` with a constant no
/// larger than [`INT32_MAX`] that stands alone as its operand.
///
/// # Arguments
///
/// * `line` - One line.
/// * `name` - A name proved non-negative here.
fn unsign(line: &str, name: &str) -> String {
    let cast = format!("(uint32_t){name} ");
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(at) = rest.find(&cast) {
        let (head, tail) = rest.split_at(at);
        out.push_str(head);
        let after = tail.get(cast.len()..).unwrap_or("");
        let alone = ["(", "&& ", "|| ", "? ", ": ", "return "]
            .iter()
            .any(|e| out.ends_with(e))
            || (out.ends_with("= ")
                && !["== ", "!= ", "<= ", ">= "]
                    .iter()
                    .any(|e| out.ends_with(e)));
        let small = ["< ", "<= ", "> ", ">= "].iter().find_map(|op| {
            let k = after.strip_prefix(op)?;
            let end = k
                .find(|c: char| !c.is_ascii_alphanumeric())
                .unwrap_or(k.len());
            let next = k.get(end..).unwrap_or("");
            (parse_const(k.get(..end)?)? <= INT32_MAX
                && [")", ";", " &&", " ||", " ?"]
                    .iter()
                    .any(|e| next.starts_with(e)))
            .then_some(())
        });
        if alone && small.is_some() {
            out.push_str(name);
            out.push(' ');
        } else {
            out.push_str(&cast);
        }
        rest = after;
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::guarded_compares;

    /// Runs the pass on a body under a one-parameter signature.
    fn run(body: &str) -> String {
        guarded_compares(&format!("// signature: uint32_t f(int32_t a1)\n{body}"))
    }

    /// An early exit and an enclosing test each prove the name
    /// non-negative where the compare runs.
    ///
    /// # Panics
    ///
    /// When a proved compare keeps its cast.
    #[test]
    fn a_proved_name_compares_signed() {
        let out = run("if (a1 <= 0) {\n  return 0;\n}\nif ((uint32_t)a1 < 4) {\n  return 1;\n}\n");
        assert!(out.contains("if (a1 < 4) {"), "{out}");
        let out = run("if (a1 > 0) {\n  if ((uint32_t)a1 < 4) {\n    return 1;\n  }\n}\n");
        assert!(out.contains("  if (a1 < 4) {"), "{out}");
    }

    /// No proof, an `else` arm, a label, an assignment, a constant past
    /// `INT32_MAX` in the compare or the guard, or a string keep the cast.
    ///
    /// # Panics
    ///
    /// When an unproved compare loses its cast.
    #[test]
    fn an_unproved_compare_keeps_its_cast() {
        for body in [
            "if ((uint32_t)a1 < 4) {\n  return 1;\n}\n",
            "if (a1 > 0) {\n  return 2;\n} else {\n  if ((uint32_t)a1 < 4) {\n    return 1;\n  }\n}\n",
            "if (a1 <= 0) {\n  return 0;\n}\nL_1:\nif ((uint32_t)a1 < 4) {\n  return 1;\n}\n",
            "if (a1 <= 0) {\n  a1 = 3;\n}\nif ((uint32_t)a1 < 4) {\n  return 1;\n}\n",
            "if (a1 <= 0) {\n  f();\n}\nif ((uint32_t)a1 < 4) {\n  return 1;\n}\n",
            "if (a1 > 0) {\n  if ((uint32_t)a1 < 0x80000000) {\n    return 1;\n  }\n}\n",
            "if (a1 > 0) {\n  if (x - (uint32_t)a1 < 4) {\n    return 1;\n  }\n}\n",
            "if (a1 >= 0x80000000) {\n  if ((uint32_t)a1 < 4) {\n    return 1;\n  }\n}\n",
            "if (a1 > 0) {\n  puts(\"((uint32_t)a1 < 4)\");\n}\n",
            "if (!(a2 && a1 > 0 && a3)) {\n  return (uint32_t)a1 < 4;\n}\n",
            "if (a1 > 0) {\n  return a2 <= (uint32_t)a1 < 1;\n}\n",
            "if (a1 <= 0) {\n  if (a2) __builtin_trap();\n}\nreturn (uint32_t)a1 < 4;\n",
            "if (a1 <= 0) {\n  if (a2) goto L_1;\n}\nreturn (uint32_t)a1 < 4;\n",
            "if (a2 || (a1 > 0 && a3)) {\n  return (uint32_t)a1 < 4;\n}\n",
            "if (f(\" || a1 <= 0 || \")) {\n  return 0;\n}\nif ((uint32_t)a1 < 4) {\n  return 1;\n}\n",
        ] {
            let out = run(body);
            assert!(out.contains("(uint32_t)a1"), "{out}");
        }
    }
}
