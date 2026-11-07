//! A `min` or `max` of a variable read back as the choice that keeps it,
//! where that choice is a clamp a source wrote as an `if` ([`unspell`]).

use super::*;

/// The extremum helpers: each name, the compare under which it takes its
/// other operand over the kept one, and whether it compares unsigned.
const SPELLED: [(&str, &str, bool); 4] = [
    ("umax", "<", true),
    ("umin", ">", true),
    ("max", "<", false),
    ("min", ">", false),
];

/// Reads a `min` or `max` of a variable back as the choice that keeps it,
/// where the choice then is an `if` that sets the variable.
///
/// `umax(a5, 2)` is `a5 < 2 ? 2 : a5`. A source clamps that way, `if (pllr
/// < 2) pllr = 2;`, and [`kept_select`] or [`clamp_hoist`] writes that `if`
/// from the choice; but a word compare is spelled as the helper before
/// either runs, which hides the choice from both. The variable is declared
/// with the helper's signedness, so the compare reads as the helper does,
/// and the bound is a constant, which a clamp is against and which the
/// choice may name twice where it would read nothing twice; a `min` or
/// `max` neither rule takes stays as it is.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
/// * `k` - The line.
///
/// # Returns
///
/// How many lines the rewrite spans, or `None` when it made none.
pub(super) fn unspell(lines: &mut Vec<String>, k: usize) -> Option<usize> {
    let line = lines
        .get(k)
        .filter(|l| !l.trim_start().starts_with("//"))?
        .clone();
    let declared: Vec<String> = lines
        .iter()
        .filter(|l| l.trim_start().starts_with("// signature:") || declares(l))
        .cloned()
        .collect();
    for (name, op, unsigned) in SPELLED {
        for at in word_positions(&line, name) {
            let open = at + name.len();
            let Some(close) = line
                .get(open..)
                .filter(|t| t.starts_with('('))
                .and_then(|_| matching_paren(&line, open))
            else {
                continue;
            };
            let args = split_arguments(line.get(open + 1..close).unwrap_or(""));
            let [a, b] = args.as_slice() else {
                continue;
            };
            for (v, other) in [(a.trim(), b.trim()), (b.trim(), a.trim())] {
                let typed = decl_type(&declared, v).is_some_and(|t| {
                    let t = t.trim_start_matches("const ");
                    if unsigned {
                        t.starts_with("uint")
                    } else {
                        t.starts_with("int")
                    }
                });
                if !typed || !is_ident(v) || parse_const(other).is_none() {
                    continue;
                }
                let choice = format!("({v} {op} {other} ? {other} : {v})");
                let candidate = format!(
                    "{}{choice}{}",
                    line.get(..at).unwrap_or(""),
                    line.get(close + 1..).unwrap_or("")
                );
                if let Some(rewritten) = kept_select(&candidate) {
                    let n = rewritten.len();
                    lines.splice(k..=k, rewritten);
                    return Some(n);
                }
                let mut scratch = lines.clone();
                if let Some(slot) = scratch.get_mut(k) {
                    *slot = candidate;
                }
                if clamp_hoist(&mut scratch, k) {
                    *lines = scratch;
                    return Some(3);
                }
            }
        }
    }
    None
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::super::select_statements;

    /// A clamp spelled as `umax` or `max` reads as the `if` it was.
    ///
    /// That holds inside a statement and as one; a variable of the other
    /// signedness either way, a bound that is no constant (a memory read
    /// the choice would read twice) and a value returned keep the helper.
    #[test]
    fn a_spelled_clamp_reads_as_the_if_it_was() {
        let text = concat!(
            "// signature: uint32_t f(uint32_t a1, uint32_t a2, int32_t a3, int32_t a4, uint32_t *a5, uint32_t a6)\n",
            "*(uint32_t*)0x40023804 = a2 | ((umax(a1, 2) << 0x1c) & 0x70000000);\n",
            "a2 = umax(a2, 7);\n",
            "a3 = umax(a3, 4);\n",
            "a6 = max(a6, 5);\n",
            "a4 = max(0, a4);\n",
            "a2 = umax(*(uint32_t*)a5, a2);\n",
            "return max(a3, a2) + a4;\n",
        );
        let want = concat!(
            "// signature: uint32_t f(uint32_t a1, uint32_t a2, int32_t a3, int32_t a4, uint32_t *a5, uint32_t a6)\n",
            "if (a1 < 2) {\n",
            "  a1 = 2;\n",
            "}\n",
            "*(uint32_t*)0x40023804 = a2 | ((a1 << 0x1c) & 0x70000000);\n",
            "if (a2 < 7) {\n",
            "  a2 = 7;\n",
            "}\n",
            "a3 = umax(a3, 4);\n",
            "a6 = max(a6, 5);\n",
            "if (a4 < 0) {\n",
            "  a4 = 0;\n",
            "}\n",
            "a2 = umax(*(uint32_t*)a5, a2);\n",
            "return max(a3, a2) + a4;\n",
        );
        assert_eq!(select_statements(text), want);
    }
}
