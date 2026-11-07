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

/// The largest bound a signed helper's compare reads as its literal does:
/// a positive `int`, whatever the width the helper compares at.
const SIGNED_BOUND_MAX: u64 = 0x7fff_ffff;

/// Reads a `min` or `max` of a variable back as the choice that keeps it,
/// where the choice then is an `if` that sets the variable.
///
/// `umax(a5, 2)` is `a5 < 2 ? 2 : a5`. A source clamps that way, `if (pllr
/// < 2) pllr = 2;`, and [`kept_select`] or [`clamp_hoist`] writes that `if`
/// from the choice; but a word compare is spelled as the helper before
/// either runs, which hides the choice from both. The variable is declared
/// with the helper's signedness and no wider than the machine word the
/// helper compares at, so the compare reads as the helper does, and is no
/// `const`, which the `if` would assign,
/// and the bound is a constant, which a clamp is against and which the
/// choice may name twice where it would read nothing twice; a signed
/// helper's bound is a positive `int`, which compares the same signed or
/// not. A name in a string literal is no call, and a `min` or `max`
/// neither rule takes stays as it is. Inside a larger statement the
/// variable is as wide as the machine word, as the helper's result is, so
/// the statement computes at the width it did, the variable is the
/// function's own (a value only its text holds, or a parameter whose
/// address no line of code takes, a header's note on the machine's frame
/// being no such line), so the `if` writes nothing another reader sees,
/// and the helper is unsigned:
/// a signed `min` or `max` hands back an unsigned word, which a signed
/// variable in its place would shift or compare as signed.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
/// * `k` - The line.
/// * `word` - The machine word's type, which the helpers compare at.
/// * `taken` - The helpers' names a function of the image holds.
///
/// # Returns
///
/// How many lines the rewrite spans, or `None` when it made none.
pub(super) fn unspell(
    lines: &mut Vec<String>,
    k: usize,
    word: &str,
    taken: &[&str],
) -> Option<usize> {
    let line = lines
        .get(k)
        .filter(|l| !l.trim_start().starts_with("//"))?
        .clone();
    if !SPELLED.iter().any(|(name, ..)| line.contains(name)) {
        return None;
    }
    let declared: Vec<String> = lines
        .iter()
        .filter(|l| l.trim_start().starts_with("// signature:") || declares(l))
        .cloned()
        .collect();
    for (name, op, unsigned) in SPELLED {
        let real = lines.iter().any(|l| {
            let t = l.trim_start();
            t.starts_with("extern ")
                && (t.contains(&format!(" {name}(")) || t.contains(&format!("*{name}(")))
        });
        if real || taken.contains(&name) {
            continue;
        }
        for at in word_positions(&line, name) {
            if in_literal(line.get(..at).unwrap_or("")) {
                continue;
            }
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
                let ty = decl_type(&declared, v);
                let typed = parse_const(other)
                    .is_some_and(|bound| ty.as_deref().is_some_and(|t| fits(t, bound, unsigned)));
                let bits = ty
                    .as_deref()
                    .filter(|t| !t.trim_start().starts_with("const "))
                    .and_then(width);
                if !typed || !is_ident(v) || bits.is_none_or(|b| width(word).is_none_or(|w| b > w))
                {
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
                let taken = lines
                    .iter()
                    .filter(|l| !l.trim_start().starts_with("//"))
                    .any(|l| l.contains(&format!("&{v}")));
                let own = private(lines, v) || (is_param_name(v) && !taken);
                if bits != width(word) || !unsigned || !own {
                    continue;
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

/// Tells whether a variable of type `ty` compares with `bound` as a helper
/// of that signedness does.
///
/// That is an integer of the helper's signedness whose width holds the
/// bound, so setting the variable to the bound keeps it, and a signed one
/// whose bound is a positive `int`.
///
/// # Arguments
///
/// * `ty` - The variable's declared type.
/// * `bound` - The constant bound.
/// * `unsigned` - Whether the helper compares unsigned.
fn fits(ty: &str, bound: u64, unsigned: bool) -> bool {
    let Some(width) = width(ty) else {
        return false;
    };
    let ty = ty.trim_start_matches("const ");
    if unsigned {
        ty.starts_with("uint") && bound.checked_shr(width).is_none_or(|high| high == 0)
    } else {
        ty.starts_with("int")
            && bound <= SIGNED_BOUND_MAX
            && bound
                .checked_shr(width.saturating_sub(1))
                .is_none_or(|high| high == 0)
    }
}

/// The width in bits of an integer type a declaration gives, the 64-bit
/// ones ([`integer_bits`] stops at 32) included.
///
/// # Arguments
///
/// * `ty` - The declared type.
fn width(ty: &str) -> Option<u32> {
    let ty = ty.trim_start_matches("const ");
    integer_bits(ty)
        .map(u32::from)
        .or_else(|| matches!(ty, "uint64_t" | "int64_t").then_some(64))
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
            "// note: &a1 escapes; locals from there up are reloaded after calls\n",
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
            "// note: &a1 escapes; locals from there up are reloaded after calls\n",
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
        assert_eq!(select_statements(text, "uint32_t", &[]), want);
    }

    /// A helper that is no clamp keeps its name.
    ///
    /// A helper's name in a string literal is no call, a function the text
    /// declares by a helper's name is that function, and a bound the
    /// variable cannot hold, or a signed helper's bound that reads
    /// negative, keeps the helper.
    #[test]
    fn a_quoted_helper_a_real_call_or_a_bound_out_of_reach_stays() {
        let text = concat!(
            "// signature: void f(uint32_t a1, int64_t a2, uint32_t a3, int8_t a4, uint32_t a5, uint64_t a6)\n",
            "extern uint32_t umin(uint32_t, uint32_t);\n",
            "uint64_t var1, var2;\n",
            "\n",
            "var1 = \"umax(a1, 2)\";\n",
            "a2 = max(a2, 0xffffffffffffffff);\n",
            "var2 = umax(a3, 0x100000000);\n",
            "a4 = max(a4, 200);\n",
            "a5 = umin(a5, 9);\n",
            "a6 = umax(a6, 2);\n",
        );
        assert_eq!(select_statements(text, "uint32_t", &[]), text);
    }

    /// On a 64-bit target a 32-bit clamp inside a wider statement stays.
    ///
    /// A helper computes at 64 bits there, so the result's width shows in
    /// the statement; set back into the variable it is the `if`, and an
    /// unsigned 64-bit variable's clamp is the `if` either way, a signed
    /// one's only when set back: a signed helper hands back an unsigned
    /// word.
    #[test]
    fn a_narrow_clamp_inside_a_wide_statement_stays() {
        let text = concat!(
            "// signature: uint64_t f(uint32_t a1, uint32_t a2, uint64_t a3, int64_t a4, int64_t a5)\n",
            "uint64_t var1, var2, var3;\n",
            "\n",
            "var1 = umax(a1, 2) << 0x1c;\n",
            "a2 = umax(a2, 3);\n",
            "var2 = umax(a3, 4) << 0x1c;\n",
            "a4 = max(a4, 5);\n",
            "var3 = min(a5, 2) >> 1;\n",
            "return var1 + a2 + var2 + a4 + var3;\n",
        );
        let out = select_statements(text, "uint64_t", &[]);
        assert!(out.contains("var1 = umax(a1, 2) << 0x1c;\n"), "{out}");
        assert!(out.contains("if (a2 < 3) {\n  a2 = 3;\n}\n"), "{out}");
        assert!(
            out.contains("if (a3 < 4) {\n  a3 = 4;\n}\nvar2 = a3 << 0x1c;\n"),
            "{out}"
        );
        assert!(out.contains("if (a4 < 5) {\n  a4 = 5;\n}\n"), "{out}");
        assert!(out.contains("var3 = min(a5, 2) >> 1;\n"), "{out}");
        let fixed = concat!(
            "// signature: uint64_t f(const uint64_t a1)\n",
            "uint64_t var1;\n",
            "\n",
            "var1 = umax(a1, 2) << 1;\n",
            "return var1;\n",
        );
        assert_eq!(select_statements(fixed, "uint64_t", &[]), fixed);
        let shared = concat!(
            "// signature: uint64_t f()\n",
            "uint64_t var1, g64_1000;\n",
            "\n",
            "var1 = umax(g64_1000, 2) << 1;\n",
            "return var1;\n",
        );
        assert_eq!(select_statements(shared, "uint64_t", &[]), shared);
        let named = concat!(
            "// signature: uint64_t f(uint64_t a1)\n",
            "\n",
            "a1 = umax(a1, 2);\n",
            "return a1;\n",
        );
        assert_eq!(select_statements(named, "uint64_t", &["umax"]), named);
    }
}
