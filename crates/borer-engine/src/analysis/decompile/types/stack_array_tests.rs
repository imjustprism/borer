use super::stack_arrays;

/// Slots a computed index reads through the first one's address are
/// one array; slots only named directly stay apart.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn an_indexed_run_of_slots_is_an_array() {
    let text = [
        "// signature: uint32_t f(uint64_t a1)",
        "uint64_t local_28, local_20, local_18, local_8;",
        "",
        "local_28 = 1;",
        "local_20 = 2;",
        "local_18 = 3;",
        "local_8 = 4;",
        "return ((uint32_t*)&local_28)[a1 & 3] + local_8;",
    ]
    .join("\n");
    let out = stack_arrays(&text);
    assert!(out.contains("uint64_t local_28[3];"), "{out}");
    assert!(out.contains("uint64_t local_8;"), "{out}");
    assert!(out.contains("local_28[1] = 2;"), "{out}");
    assert!(out.contains("local_28[2] = 3;"), "{out}");
    assert!(out.contains("((uint32_t*)local_28)[a1 & 3]"), "{out}");
    let direct = "uint64_t local_28, local_20;\n\nreturn local_28 + local_20;\n";
    assert_eq!(stack_arrays(direct), direct);
}

/// A lone indexed slot is the object up to the next slot the text
/// names, and a member of an indexed run is no object of its own.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_lone_indexed_slot_runs_up_to_the_next_named_one() {
    let text = [
        "// signature: uint32_t f(uint64_t a1)",
        "uint32_t local_5c, local_c;",
        "uint64_t local_58;",
        "",
        "local_c = a1;",
        "((uint32_t*)&local_58)[local_5c] = 1;",
        "return ((uint32_t*)&local_58)[local_c & 0xf];",
    ]
    .join("\n");
    let out = stack_arrays(&text);
    assert!(out.contains("uint64_t local_58[10];"), "{out}");
    assert!(
        out.contains("return ((uint32_t*)local_58)[local_c & 0xf];"),
        "{out}"
    );
    let run = [
        "uint64_t local_8, local_0;",
        "",
        "((uint32_t*)&local_8)[a1] = 1;",
        "return ((uint8_t*)&local_0)[a1];",
    ]
    .join("\n");
    let out = stack_arrays(&run);
    assert!(out.contains("uint64_t local_8[2];"), "{out}");
    assert!(out.contains("((uint8_t*)&local_8[1])[a1]"), "{out}");
}
