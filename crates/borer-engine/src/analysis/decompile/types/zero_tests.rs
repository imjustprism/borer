use super::quiet_zero_tests;

/// A zero test of a call drops the register cast. A `uint64_t` the
/// function also uses whole keeps it, and a store of a parameter at 32
/// bits declares the parameter at that width.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_zero_test_of_a_call_drops_its_cast() {
    let text = concat!(
        "// signature: uint32_t f(uint64_t a1, uint64_t a2)\n",
        "uint64_t var1;\n",
        "\n",
        "if ((uint32_t)sub_1() != 0) {\n",
        "  *(uint32_t*)a2 = a1;\n",
        "}\n",
        "var1 = var1 + a2;\n",
        "if ((uint32_t)var1 != 0) {\n",
        "  return a1;\n",
        "}\n",
        "return 0;\n",
    );
    let out = super::type_parameters(text, "uint64_t");
    let out = quiet_zero_tests(&super::type_locals(&out));
    assert!(out.contains("if (sub_1() != 0)"), "{out}");
    assert!(!out.contains("(uint32_t)sub_1"), "{out}");
    assert!(out.contains("uint32_t a1"), "{out}");
    assert!(out.contains("*(uint32_t*)a2 = a1;"), "{out}");
    assert!(out.contains("(uint32_t)var1 != 0"), "{out}");
}
