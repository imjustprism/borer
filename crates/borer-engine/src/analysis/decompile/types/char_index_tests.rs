use super::spell_index;

/// A byte load through a `char` pointer is the element it reads.
///
/// The signed read stays as it is, the unsigned one is cast, a store
/// and a zero test take no cast, an index's own parentheses go, and a
/// pointer to something else is untouched.
#[test]
fn a_byte_load_through_a_char_pointer_is_an_element() {
    let text = [
        "// signature: int f(const char *str, int *n, char *out)",
        "uint64_t var1;",
        "",
        "if (*(int8_t*)(str + var1 + 1) > 127) {",
        "  *(uint8_t*)(out + var1) = 32;",
        "}",
        "if (*(uint8_t*)(str + var1) != 0 && *(uint8_t*)n == 1) {",
        "  return *(uint8_t*)(str + (var1 & 3));",
        "}",
        "return *(int8_t*)str + *(uint8_t*)(str + var1);",
    ]
    .join("\n");
    let out = spell_index(&text);
    assert!(out.contains("if (str[var1 + 1] > 127) {"), "{out}");
    assert!(out.contains("  out[var1] = 32;"), "{out}");
    assert!(
        out.contains("if (str[var1] != 0 && *(uint8_t*)n == 1) {"),
        "{out}"
    );
    assert!(out.contains("return (uint8_t)str[var1 & 3];"), "{out}");
    assert!(out.contains("return *str + (uint8_t)str[var1];"), "{out}");
}
