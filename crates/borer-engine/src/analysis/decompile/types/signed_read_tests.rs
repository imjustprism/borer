use super::type_locals;

/// A `uint32_t` local or global the text only reads sign-extended is
/// an `int32_t`, and its casts go; one read any other way keeps its
/// type.
#[test]
fn a_name_read_only_signed_is_declared_signed() {
    let text = [
        "// signature: uint32_t f(const char *str)",
        "uint32_t local_10, local_c;",
        "uint32_t limit; // @ 0x4010",
        "",
        "for (local_10 = 0; str[(int64_t)(int32_t)local_10] != 0; local_10 += 1) {",
        "  if ((int32_t)local_10 > (int32_t)limit) {",
        "    return local_c >> 1;",
        "  }",
        "}",
        "return limit;",
    ]
    .join("\n");
    let out = type_locals(&text);
    assert!(out.contains("uint32_t local_c;"), "{out}");
    assert!(out.contains("int32_t local_10;"), "{out}");
    assert!(out.contains("int32_t limit; // @ 0x4010"), "{out}");
    assert!(out.contains("str[local_10] != 0"), "{out}");
    assert!(out.contains("if (local_10 > limit) {"), "{out}");
    let unsigned = text.replace("return local_c >> 1;", "return local_10 >> 1;");
    let out = type_locals(&unsigned);
    assert!(out.contains("uint32_t local_10, local_c;"), "{out}");
    assert!(out.contains("(int64_t)(int32_t)local_10"), "{out}");
}
