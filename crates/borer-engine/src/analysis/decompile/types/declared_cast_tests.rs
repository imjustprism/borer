use super::type_locals;

/// A masked value written to a narrow local the mask covers loses the
/// mask; a narrower mask, a mask under `|`, and a wider local keep it.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_narrow_local_drops_the_mask_of_what_it_stores() {
    let text = concat!(
        "uint32_t local_dc, local_d0;
",
        "uint8_t local_8a;
",
        "uint64_t local_c0;
",
        "
",
        "local_dc = a1 & 0xffffffff;
",
        "local_d0 = (a2 + a1) & 0xffffffff;
",
        "local_8a = (a2 >> 3) & 0xffff;
",
        "local_dc = a2 & 0xffff;
",
        "local_d0 = a1 | a2 & 0xffffffff;
",
        "local_c0 = a1 & 0xffffffff;
",
        "return local_dc + local_d0 + local_8a + local_c0;
",
    );
    let out = type_locals(text);
    assert!(out.contains("local_dc = a1;"), "{out}");
    assert!(out.contains("local_d0 = a2 + a1;"), "{out}");
    assert!(out.contains("local_8a = a2 >> 3;"), "{out}");
    assert!(out.contains("local_dc = a2 & 0xffff;"), "{out}");
    assert!(out.contains("local_d0 = a1 | a2 & 0xffffffff;"), "{out}");
    assert!(out.contains("local_c0 = a1 & 0xffffffff;"), "{out}");
}

/// A local already declared at the cast's width does not need the cast.
/// A different width, a cast of a sum, a nonzero equality, and a zero
/// test of a `uint64_t` stay.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_name_declared_at_the_cast_width_drops_the_cast() {
    let text = concat!(
        "uint32_t var1;\n",
        "int32_t var2;\n",
        "uint64_t var3;\n",
        "\n",
        "if ((uint32_t)var1 < 5) {\n",
        "  return var1;\n",
        "}\n",
        "if ((uint32_t)(var1) != 0) {\n",
        "  return 1;\n",
        "}\n",
        "if ((uint32_t)var2 == 6) {\n",
        "  return 2;\n",
        "}\n",
        "if ((int32_t)(var2 + 1) < 0) {\n",
        "  return 3;\n",
        "}\n",
        "var3 = var3 << 4;\n",
        "if ((uint32_t)var3 != 0) {\n",
        "  return 4;\n",
        "}\n",
    );
    let out = type_locals(text);
    assert!(out.contains("if (var1 < 5) {"), "{out}");
    assert!(out.contains("if (var1 != 0) {"), "{out}");
    assert!(!out.contains("(uint32_t)var1"), "{out}");
    assert!(!out.contains("(uint32_t)(var1)"), "{out}");
    assert!(out.contains("if ((uint32_t)var2 == 6) {"), "{out}");
    assert!(out.contains("if ((int32_t)(var2 + 1) < 0) {"), "{out}");
    assert!(out.contains("if ((uint32_t)var3 != 0) {"), "{out}");
    assert!(out.contains("uint64_t var3;"), "{out}");
}

/// A 32-bit mask over arithmetic C already does in `unsigned int`
/// changes nothing, so it goes, with the parentheses it needed.
///
/// `var1` and `var2` are `uint32_t`, so `(var2 - var1) & 0xffffffff`
/// is `var2 - var1`; `a2` is wider and a constant past `INT_MAX` is not
/// an `int`, so those masks stay.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_mask_over_unsigned_int_arithmetic_goes() {
    let text = concat!(
        "uint32_t var1, var2;\n",
        "\n",
        "var1 = ((var2 - var1) & 0xffffffff) >> 1;\n",
        "var2 = a1[((var1 + 1) & 0xffffffff)];\n",
        "var1 = ((var2 + var1) & 0xffffffff);\n",
        "return ((a2 - var1) & 0xffffffff) + ((var1 ^ 0x80000000) & 0xffffffff);\n",
    );
    let out = type_locals(text);
    assert!(out.contains("var1 = (var2 - var1) >> 1;"), "{out}");
    assert!(out.contains("var2 = a1[var1 + 1];"), "{out}");
    assert!(out.contains("var1 = var2 + var1;"), "{out}");
    assert!(out.contains("((a2 - var1) & 0xffffffff)"), "{out}");
    assert!(out.contains("((var1 ^ 0x80000000) & 0xffffffff)"), "{out}");
}
