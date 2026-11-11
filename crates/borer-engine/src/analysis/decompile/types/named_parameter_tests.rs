use super::type_parameters;

/// A parameter the debug information names with a signed type drops
/// the casts that type makes redundant, as an `aN` one does.
#[test]
fn a_named_signed_parameter_drops_its_casts() {
    let text = [
        "// signature: uint32_t f(int total, unsigned int mask)",
        "",
        "return ((int64_t)(int32_t)total >> 5) + (int32_t)total / 3 + (mask & 0xffffffff);",
    ]
    .join("\n");
    let out = type_parameters(&text, "uint64_t");
    assert!(
        out.contains("return (total >> 5) + total / 3 + (mask & 0xffffffff);"),
        "{out}"
    );
}
