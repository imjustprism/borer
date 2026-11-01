//! Chains of tests that each return a truth value, written as the one
//! short-circuit test a source returns.

use super::*;

/// Rewrites a chain of tests returning one truth value as the test it is.
///
/// The chain at line `k` ends with a return of the other value: `if (A) {
/// return 0; } if (B) { return 0; } return 1;` is `return !A && !B;`, and
/// with the values swapped `return A || B;`.
///
/// The tests run in order and the first that holds decides, which is what
/// `&&` and `||` evaluate, calls included. One test returning `0` or `1`
/// stays an `if`, the statement a source wrote (`truth_diamond`).
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the first `if`.
///
/// # Returns
///
/// Whether the chain became one `return`.
pub(super) fn return_chain(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(pad) = lines.get(k).map(|l| indent_of(l)) else {
        return false;
    };
    let at = |n: usize, text: &str, ind: usize| {
        lines
            .get(n)
            .is_some_and(|l| indent_of(l) == ind && l.trim() == text)
    };
    let guard = |n: usize| -> Option<(String, &'static str, usize)> {
        let t = lines.get(n).filter(|l| indent_of(l) == pad)?.trim();
        ["0", "1"].into_iter().find_map(|z| {
            let ret = format!("return {z};");
            t.strip_prefix("if (")
                .and_then(|c| c.strip_suffix(&format!(") {ret}")))
                .map(|c| (c.to_owned(), z, 1))
                .or_else(|| {
                    if_opener(t)
                        .filter(|_| at(n + 1, &ret, pad + 2) && at(n + 2, "}", pad))
                        .map(|c| (c.to_owned(), z, 3))
                })
        })
    };
    let Some((first, z, len)) = guard(k) else {
        return false;
    };
    let mut conds = vec![first];
    let mut j = k + len;
    while let Some((c, _, n)) = guard(j).filter(|g| g.1 == z) {
        conds.push(c);
        j += n;
    }
    let end = if z == "0" { "return 1;" } else { "return 0;" };
    if conds.len() < 2 || !at(j, end, pad) {
        return false;
    }
    let (join, terms): (&str, Vec<String>) = if z == "0" {
        (" && ", conds.iter().map(|c| invert_condition(c)).collect())
    } else {
        (" || ", conds)
    };
    let parts: Vec<String> = terms
        .into_iter()
        .map(|t| {
            if t.contains("&&") || t.contains("||") || t.contains('?') {
                format!("({t})")
            } else {
                t
            }
        })
        .collect();
    let pad_s = " ".repeat(pad);
    lines.splice(k..=j, [format!("{pad_s}return {};", parts.join(join))]);
    true
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    //! The chain rewrite on hand-written text, beside the shapes that stay.

    use super::super::selects::select_statements;

    /// Tests that each return `0`, then a return of `1`, return their
    /// conjunction, and with the values swapped their disjunction; one
    /// test, or a chain that ends otherwise, stays.
    #[test]
    fn a_chain_of_truth_returns_is_one_test() {
        let text = "r0 = sub_2(a1);\nif (sub_1(a1) == 0) {\n  return 0;\n}\nif (a2 < 3 || a3 != 0) return 0;\nreturn 1;\n";
        assert_eq!(
            select_statements(text),
            "r0 = sub_2(a1);\nreturn sub_1(a1) != 0 && (a2 >= 3 && a3 == 0);\n"
        );
        let any = "if (a1 == 0) {\n  return 1;\n}\nif (a2 == 0) {\n  return 1;\n}\nreturn 0;\n";
        assert_eq!(select_statements(any), "return a1 == 0 || a2 == 0;\n");
        let one = "if (a1 == 0) {\n  return 0;\n}\nreturn 1;\n";
        assert_eq!(select_statements(one), one);
        let other = "if (a1 == 0) {\n  return 0;\n}\nif (a2 == 0) {\n  return 0;\n}\nreturn 2;\n";
        assert_eq!(select_statements(other), other);
    }
}
