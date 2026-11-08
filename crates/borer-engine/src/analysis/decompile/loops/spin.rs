//! A loop that only computes its own test, read as `while (test);`
//! ([`spins`]).

use super::super::ctext::Un;
use super::*;

/// Rewrites the loop at line `k` whose body only computes its own test as
/// `while (test);`, the empty loop a wait on a device or a flag is.
///
/// `do { } while (c);` tests `c` until it is false, as `while (c);` does.
/// `do { t = e; } while (c);` is `while (c);` with `e` put in for `t`
/// when that runs `e` as often and in the same order as the loop did
/// ([`spin_temp`]). `while (1) { if (c) { tail } }` is `while (!c);` then
/// `tail` when `tail` is the loop's only way out ([`exit_spin`]).
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
/// * `k` - The line the loop opens on.
///
/// # Returns
///
/// Whether the loop became a `while (test);`.
pub(super) fn spins(lines: &mut Vec<String>, k: usize) -> bool {
    spin_do(lines, k) || exit_spin(lines, k)
}

/// Rewrites the `do` at line `k` whose body is empty or one assignment
/// [`spin_temp`] takes, as [`spins`] says.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `do {`.
///
/// # Returns
///
/// Whether the `do` became a `while (test);`.
fn spin_do(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k).filter(|l| l.trim() == "do {") else {
        return false;
    };
    let pad = indent_of(open);
    let Some(close) = closing(lines, k, pad) else {
        return false;
    };
    let Some(cond) = lines
        .get(close)
        .and_then(|l| l.trim().strip_prefix("} while ("))
        .and_then(|r| r.strip_suffix(");"))
    else {
        return false;
    };
    let body: Vec<&str> = lines[k + 1..close]
        .iter()
        .map(|l| l.trim())
        .filter(|l| !l.is_empty())
        .collect();
    let test = match body.as_slice() {
        [] => cond.to_owned(),
        [one] => match spin_temp(lines, k, close, one, cond) {
            Some(test) => test,
            None => return false,
        },
        _ => return false,
    };
    let line = format!("{}while ({test});", " ".repeat(pad));
    lines.splice(k..=close, [line]);
    true
}

/// The test of `do { t = e; } while (c);` with `e` put in for `t`, when
/// that is the same loop.
///
/// The loop runs `e` once before each test and keeps its value in `t`
/// alone. The rewrite holds when `t` is a register or a web's variable
/// ([`is_temp`]), so dropping its write drops no store; `e` does not read
/// `t`; `c` names `t` once and nothing else but constants, through casts
/// and operators that evaluate every operand ([`reads_only`]), so no `&&`,
/// `||` or `?:` can skip `e` and no other load or call in `c` runs before
/// or after it; and no line outside the loop names `t`, so its value is
/// read nowhere else. A declaration counts as such a line: the cleanup's
/// text declares nothing yet (declarations are written after it, from the
/// names left), and a declared type may be narrower than `e`, which the
/// assignment cut.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `do {`.
/// * `close` - The line of the `} while (c);`.
/// * `body` - The loop's one statement, trimmed.
/// * `cond` - The loop's test `c`.
///
/// # Returns
///
/// The new test, or `None` when the loop does not qualify.
fn spin_temp(lines: &[String], k: usize, close: usize, body: &str, cond: &str) -> Option<String> {
    let (t, e) = plain_assignment(body)?;
    if !is_temp(t) || mentions_ident(e, t) || word_positions(cond, t).len() != 1 {
        return None;
    }
    let tree = expression(&c_tokens(cond).ok()?, &|n| named_type(n, 64).is_none(), 64).ok()?;
    let elsewhere = || {
        lines[..k]
            .iter()
            .chain(&lines[close + 1..])
            .any(|l| mentions_ident(l, t))
    };
    (reads_only(&tree, t) && !elsewhere()).then(|| rename_word(cond, t, &grouped(e)))
}

/// Tells whether a name is a register or a web's variable.
///
/// It is one of [`is_register_name`]'s, `var<n>` ([`vars::is_var_name`]),
/// or an ARM32 core register, `r0` to `r12` or `lr`
/// ([`verify_a32::GENERAL`]), which [`is_register_name`] reads only from
/// `r8` up.
///
/// # Arguments
///
/// * `name` - The name.
fn is_temp(name: &str) -> bool {
    is_register_name(name)
        || vars::is_var_name(name)
        || verify_a32::GENERAL.iter().any(|&(r, _)| r == name)
}

/// Tells whether an expression reads nothing but `t` and constants, every
/// operand evaluated: no load, call, field, string, other name, `&&`, `||`,
/// `?:`, assignment or step.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `t` - The one name it may read.
fn reads_only(e: &Ast, t: &str) -> bool {
    match e {
        Ast::Int(..) | Ast::Float(..) => true,
        Ast::Name(n) => n == t,
        Ast::Un(op, x) => !matches!(op, Un::Deref | Un::Addr) && reads_only(x, t),
        Ast::Cast(_, x) => reads_only(x, t),
        Ast::Bin(_, l, r) => reads_only(l, t) && reads_only(r, t),
        Ast::Str(_)
        | Ast::Logic(..)
        | Ast::Pick(..)
        | Ast::Call(..)
        | Ast::Index(..)
        | Ast::Arrow(..)
        | Ast::Assign(..)
        | Ast::Step(..) => false,
    }
}

/// Rewrites the `while (1)` at line `k` whose body is one `if` that leaves
/// the function, as [`spins`] says.
///
/// The `if` arm is the loop's only way out when its last line is a
/// `return`, at the arm's own level since every block the arm opens ends
/// in its `}`, and it holds no `break` or `continue`, which would bind to
/// something else once moved, and, as for every loop rewrite here, no
/// label. The arm then runs after `while (!c);` exactly when it ran inside
/// the loop. It moves out two levels, four columns, as the renderer indents
/// by two; a blank line, the one line the renderer writes at no
/// indentation, stays blank.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `while (1) {`.
///
/// # Returns
///
/// Whether the loop became a `while (test);` and its arm.
fn exit_spin(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k).filter(|l| l.trim() == "while (1) {") else {
        return false;
    };
    let pad = indent_of(open);
    let (Some(close), Some(cond)) = (
        closing(lines, k, pad),
        lines.get(k + 1).and_then(|l| if_opener(l.trim())),
    ) else {
        return false;
    };
    let inner = close - 1;
    if closing(lines, k + 1, pad + 2) != Some(inner) {
        return false;
    }
    let tail = &lines[k + 2..inner];
    let returns = tail
        .iter()
        .rfind(|l| !l.trim().is_empty())
        .is_some_and(|l| is_return(l.trim()));
    let leaves = tail.iter().any(|l| {
        let t = l.trim();
        breaks(t) || continues(t) || is_label(l)
    });
    if !returns || leaves {
        return false;
    }
    let mut out = vec![format!(
        "{}while ({});",
        " ".repeat(pad),
        invert_condition(cond)
    )];
    out.extend(
        tail.iter()
            .map(|l| l.strip_prefix("    ").unwrap_or(l).to_owned()),
    );
    lines.splice(k..=close, out);
    true
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    //! The spins on hand-written text, beside loops that keep their form.

    use super::super::tests::run;

    /// An empty `do` and one that sets a register its test alone reads
    /// read as `while (test);`, the value put in for the register.
    #[test]
    fn a_do_computing_only_its_test_is_a_spin() {
        assert_eq!(
            run("do {\n} while ((*(uint32_t*)0x40023808 & 2) == 0);\nreturn;\n"),
            "while ((*(uint32_t*)0x40023808 & 2) == 0);\nreturn;\n"
        );
        assert_eq!(
            run(
                "local_9 = a1;\ndo {\n  r0 = sub_8000384(local_9);\n} while (((r0 ^ 1) & 0xff) != 0);\nreturn;\n"
            ),
            "local_9 = a1;\nwhile (((sub_8000384(local_9) ^ 1) & 0xff) != 0);\nreturn;\n"
        );
        assert_eq!(
            run(
                "if (a1 != 0) {\n  do {\n    rax = *(uint32_t*)0x40021000;\n  } while ((uint32_t)(rax & 2) == 0);\n}\nreturn 0;\n"
            ),
            "if (a1 != 0) {\n  while ((uint32_t)((*(uint32_t*)0x40021000) & 2) == 0);\n}\nreturn 0;\n"
        );
    }

    /// A `do` whose temp is no register, is read elsewhere (after the loop,
    /// before it in an enclosing loop, or declared with a type), or is read
    /// by its own value keeps its form.
    #[test]
    fn a_do_whose_temp_lives_on_keeps_its_form() {
        for text in [
            "do {\n  *(uint32_t*)a1 = 1;\n} while (a2 != 0);\nreturn;\n",
            "do {\n  local_9 = sub_1();\n} while (local_9 != 0);\nreturn;\n",
            "do {\n  var1 = *(uint32_t*)a1;\n} while (var1 != 0);\nreturn var1;\n",
            "while (a1 != 0) {\n  sub_2(var1);\n  do {\n    var1 = sub_1();\n  } while (var1 != 0);\n}\nreturn;\n",
            "uint32_t var1;\n\ndo {\n  var1 = sub_1();\n} while (var1 != 0);\nreturn;\n",
            "do {\n  var1 = var1 + 1;\n} while (var1 != 9);\nreturn;\n",
        ] {
            assert_eq!(run(text), text);
        }
    }

    /// A `do` whose test could skip the temp's value, reorder it against
    /// another load or call, or read it twice keeps its form.
    #[test]
    fn a_do_whose_test_reads_more_keeps_its_form() {
        for text in [
            "do {\n  var1 = sub_1();\n} while (0 && var1 != 0);\nreturn;\n",
            "do {\n  var1 = sub_1();\n} while (var1 != 0 ? 1 : 0);\nreturn;\n",
            "do {\n  var1 = sub_1();\n} while (var1 != *(uint32_t*)0x40021000);\nreturn;\n",
            "do {\n  var1 = sub_1();\n} while (var1 != sub_2());\nreturn;\n",
            "do {\n  var1 = sub_1();\n} while (var1 != g32_2000013c);\nreturn;\n",
            "do {\n  var1 = sub_1();\n} while (var1 == 9 || var1 == 32);\nreturn;\n",
            "do {\n  var1 = sub_1();\n} while (var1 * var1 != 4);\nreturn;\n",
        ] {
            assert_eq!(run(text), text);
        }
    }

    /// A `while (1)` whose one `if` returns reads as the negated test, then
    /// the arm, moved out two levels, its blank line kept blank.
    #[test]
    fn an_endless_loop_left_by_one_return_is_a_spin() {
        assert_eq!(
            run("while (1) {\n  if (sub_1() != 0) {\n    g = 1;\n    return;\n  }\n}\n"),
            "while (sub_1() == 0);\ng = 1;\nreturn;\n"
        );
        assert_eq!(
            run(
                "  while (1) {\n    if (a1 == 0 || g2 != g1) {\n      v = 0;\n      if (g2 != g1) {\n        v = g1;\n      }\n\n      return v;\n    }\n  }\n"
            ),
            "  while (a1 != 0 && g2 == g1);\n  v = 0;\n  if (g2 != g1) {\n    v = g1;\n  }\n\n  return v;\n"
        );
    }

    /// A `while (1)` doing more than its test, or whose arm falls back into
    /// it, breaks, continues, holds a label or only calls a function named
    /// like `return`, keeps its form.
    #[test]
    fn an_endless_loop_with_another_way_keeps_its_form() {
        for text in [
            "while (1) {\n  f();\n  if (a1 != 0) {\n    return;\n  }\n}\n",
            "while (1) {\n  if (a1 != 0) {\n    g = 1;\n  }\n  if (a2 != 0) {\n    return;\n  }\n}\n",
            "while (1) {\n  if (a1 != 0) {\n    g = 1;\n  }\n}\n",
            "while (1) {\n  if (a1 != 0) {\n    if (a2 != 0) break;\n    return;\n  }\n}\ng = 1;\nreturn;\n",
            "while (1) {\n  if (a1 != 0) {\n    if (a2 != 0) continue;\n    return;\n  }\n}\n",
            "while (1) {\n  if (a1 != 0) {\n    L_10:\n    return;\n  }\n}\n",
            "while (1) {\n  if (a1 != 0) {\n    returned(a1);\n  }\n}\n",
        ] {
            assert_eq!(run(text), text);
        }
    }
}
