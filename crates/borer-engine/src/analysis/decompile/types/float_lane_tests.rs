use super::float_lanes;

/// A register only scalar singles replace the low lane of is a `float`,
/// and a `float` function's merged `return` returns the lane.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_register_only_singles_write_is_a_float() {
    let text = [
        "// signature: float f(float *a1, uint64_t a2, float a3)",
        "uint64_t var1, var2;",
        "",
        "var2 = 0;",
        "do {",
        "  var2 = (var2 & 0xffffffff00000000) | ((var2 * a3 + a1[var1]) & 0xffffffff);",
        "  var1 += 1;",
        "} while (var1 != a2);",
        "return var2;",
    ]
    .join("\n");
    let out = float_lanes(&text);
    assert!(out.contains("float var2;"), "{out}");
    assert!(out.contains("uint64_t var1;"), "{out}");
    assert!(out.contains("  var2 = var2 * a3 + a1[var1];"), "{out}");
    let ret = "// signature: float g(float a1, float a2)\n\nreturn (a2 & 0xffffffff00000000) | ((a2 - a1) & 0xffffffff);\n";
    assert!(
        float_lanes(ret).contains("return a2 - a1;"),
        "{}",
        float_lanes(ret)
    );
}

/// A read of the bits (an integer cast) keeps the register as it was.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_bit_read_keeps_the_merge() {
    let text = [
        "// signature: uint32_t f(float a1)",
        "uint64_t var2;",
        "",
        "var2 = (var2 & 0xffffffff00000000) | ((var2 + a1) & 0xffffffff);",
        "return (uint32_t)var2;",
    ]
    .join("\n");
    let out = float_lanes(&text);
    assert!(out.contains("uint64_t var2;"), "{out}");
    assert!(out.contains("0xffffffff00000000"), "{out}");
}
