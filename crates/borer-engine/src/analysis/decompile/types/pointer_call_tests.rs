use super::{callable_pointers, float_bit_reads};

/// A parameter only ever called is a function pointer parameter, and
/// any other callee is cast to one taking the call's arguments.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn calls_through_pointers_are_typed() {
    let text = [
        "// signature: uint64_t f(uint64_t a1, uint64_t a2)",
        "uint64_t var1;",
        "",
        "var1 = (*a1)(a2);",
        "return (*(*(uint64_t*)(a2 + 8)))(var1, 3);",
    ]
    .join("\n");
    let out = callable_pointers(&text, "uint64_t");
    assert!(
        out.contains("uint64_t f(uint64_t (*a1)(uint64_t), uint64_t a2)"),
        "{out}"
    );
    assert!(out.contains("var1 = a1(a2);"), "{out}");
    assert!(
        out.contains("return ((uint64_t (*)(uint64_t, uint64_t))(*(uint64_t*)(a2 + 8)))(var1, 3);"),
        "{out}"
    );
    let global = [
        "// signature: void f(uint64_t a1)",
        "uint64_t var1, var2;",
        "uint64_t g64_1008; // @ 0x1008",
        "",
        "var1 = (*g64_1008)(a1, 1);",
        "var2 = (*g64_1008)(var1, 2);",
    ]
    .join("\n");
    let out = callable_pointers(&global, "uint64_t");
    assert!(
        out.contains("uint64_t (*g64_1008)(uint64_t, uint64_t); // @ 0x1008"),
        "{out}"
    );
    assert!(out.contains("var2 = g64_1008(var1, 2);"), "{out}");
    let named = "// signature: void f(uint64_t a1)\n\nmap_err<u8, u8 (*)(u32)>(a1);\n";
    assert_eq!(callable_pointers(named, "uint64_t"), named);
    assert!(out.contains("uint64_t var1, var2;"), "{out}");
}

/// A bitwise operation on a float parameter reads its bits; an
/// arithmetic one keeps the value.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn bitwise_reads_of_a_float_read_its_bits() {
    let text = "// signature: uint32_t f(float a1, double a2)\nreturn (a1 & 0x7fffffff) + (a2 >> 52) + (uint32_t)(a1 * 2);\n";
    let out = float_bit_reads(text);
    assert!(out.contains("(*(uint32_t*)&a1 & 0x7fffffff)"), "{out}");
    assert!(out.contains("(*(uint64_t*)&a2 >> 52)"), "{out}");
    assert!(out.contains("(uint32_t)(a1 * 2)"), "{out}");
}
