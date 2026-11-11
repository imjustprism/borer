use super::type_parameters;

/// A `double` on a 32-bit stack owns the word after it: the signature
/// drops that word unless the body reads it by itself.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_double_takes_the_word_after_it_on_a_32_bit_stack() {
    let text = concat!(
        "// signature: uint32_t f(void *this, double a2, uint32_t a3, double a4, uint32_t a5)\n",
        "return a2 > a4 && (a5 & 0x80000000) == 0;\n",
    );
    let typed = type_parameters(text, "uint32_t");
    let sig = typed.lines().next().unwrap_or("");
    assert!(
        sig.ends_with("(void *this, double a2, double a4, uint32_t a5)"),
        "{sig}"
    );
}

/// A cast in front of a field read casts the field, not the pointer.
///
/// `(int32_t)a1->field_0x0` compares the field signed; `a1` stays the
/// pointer the layout pass named the field on.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_cast_before_a_field_read_types_the_field() {
    let text = concat!(
        "// signature: uint32_t f(uint64_t a1, int32_t a2)\n",
        "// layout a1: 0x0 u32, 0x8 u32\n",
        "if (a2 >= (int32_t)a1->field_0x0) {\n",
        "  return a2 < (int32_t)a1->field_0x8;\n",
        "}\n",
        "return 0;\n",
    );
    let typed = type_parameters(text, "uint64_t");
    let sig = typed.lines().next().unwrap_or("");
    assert!(sig.contains("(void *a1, int32_t a2)"), "{sig}");
}

/// A parameter the body loads or stores through is a pointer, one on
/// the stack included.
///
/// It is typed by what it points at only when it is read at its start.
/// An index into an absolute address, a parameter the body reassigns
/// and one it uses only as a number are no pointers.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_parameter_loaded_through_is_a_pointer() {
    let text = concat!(
        "// signature: uint32_t f(uint32_t a1, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5, uint32_t a6, uint32_t a7)\n",
        "edx = *(uint32_t*)(a1 + 0x3c);\n",
        "*(uint32_t*)a2 = edx;\n",
        "*(uint32_t*)(a2 + 4) = 0;\n",
        "eax = *(uint8_t*)(a3 + 0x4d1234);\n",
        "a4 = sub_1(a4);\n",
        "*(uint32_t*)a4 = 0;\n",
        "*(uint16_t*)a7 = 0;\n",
        "return a5 + a6->field_0x8;\n",
    );
    let typed = type_parameters(text, "uint32_t");
    let sig = typed.lines().next().unwrap_or("");
    assert!(sig.contains("(void *a1, void *a2, uint32_t a3,"), "{sig}");
    assert!(
        sig.contains("uint32_t a4, uint32_t a5, void *a6, uint16_t *a7)"),
        "{sig}"
    );
}

/// A switch on a narrowed parameter keeps the parentheses C requires
/// around the value, and an operator's call those of its argument: the
/// mask or cast the type makes redundant goes, and they stay.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_narrowed_parameter_keeps_the_parentheses_c_requires() {
    let text = "// signature: void f(uint16_t a1)
switch (a1 & 0xffff) {
case 5: {
  return;
}
}
if (a1 & 0xffff) {
  return;
}
";
    let typed = type_parameters(text, "uint64_t");
    assert!(typed.contains("switch (a1) {"), "{typed}");
    assert!(typed.contains("if (a1) {"), "{typed}");
    assert_eq!(
        super::unwrap_parens("rax = Ptr<Item>::operator ->(a2);", "a2"),
        "rax = Ptr<Item>::operator ->(a2);"
    );
}

/// Two parameters the text widens before multiplying keep a 64-bit
/// product once both are narrowed.
///
/// `(a2 & 0xffffffff) * (int64_t)(int32_t)a1` multiplies in 64 bits;
/// `a2 * a1` of a `uint32_t` and an `int32_t` would multiply in 32 and
/// lose the high half, so each factor keeps a cast to the word.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_product_of_narrowed_parameters_stays_wide() {
    let text = "// signature: uint64_t f(uint64_t a1, uint64_t a2, uint64_t a3)\nreturn (a2 & 0xffffffff) * (int64_t)(int32_t)a1 + a3 * 3;\n";
    let typed = type_parameters(text, "uint64_t");
    assert!(
        typed.contains("f(int32_t a1, uint32_t a2, uint64_t a3)"),
        "{typed}"
    );
    assert!(
        typed.contains("return (uint64_t)a2 * (int64_t)a1 + a3 * 3;"),
        "{typed}"
    );
}

/// Narrowing a parameter drops the parentheses of a cast around it,
/// never the parentheses of a call it is the one argument of.
#[test]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
fn a_narrowed_parameter_keeps_its_call_parentheses() {
    let text = "// signature: uint64_t f(uint64_t a1)\nrax = sub_1(a1);\nif ((uint32_t)a1 == 0) {\n  return (a1);\n}\n";
    let typed = type_parameters(text, "uint64_t");
    assert!(typed.contains("sub_1(a1)"), "{typed}");
    assert!(!typed.contains("sub_1a1"), "{typed}");
}
