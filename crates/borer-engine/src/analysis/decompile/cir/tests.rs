//! Tests of the tree, its printer, its builder and its checks.

use super::*;
use std::collections::BTreeSet;

/// A structured body with every statement form the structurer writes.
const BODY: &str = "rax = 0;
/* asm: fnstcw [esp] */
rax = ((uint64_t (*)(uint64_t, uint8_t*))g_1)(a1);
L_401000:
if ((uint32_t)a4 >= 32) {
  do {
    *(uint128_t*)(r11 + rdi) = *(uint128_t*)(r9 + rdi);
    rdi -= 32;
  } while (rsi != rdi);
  if ((r10 & 0x18) != 0) goto L_401020;
} else if (a1 == 'a') {
  r8 = sub_1(a1, \"x\\\"y\", -1);
} else {
  r8 = a1 ? a2 : ~a3;
}

L_401020:
while (rbx != 0) {
  rbx = rbx->next;
}
for (rcx = 0; rcx < a1; rcx += 1) {
  rax += rcx;
}
switch (a2) {
case 1: case 2: break;
case 3: goto L_401000;
default: {
  Foo::bar(&rax);
  break;
}
}
return rax;
";

/// A body with every statement form reads into the tree and prints back as written.
#[test]
fn a_body_prints_back_byte_for_byte() {
    let body = build(BODY);
    assert_eq!(print(&body), BODY);
    let raw: Vec<Violation> = check(&body, &BTreeSet::new())
        .into_iter()
        .filter(|v| matches!(v, Violation::Raw(_)))
        .collect();
    assert!(raw.is_empty(), "lines left as text: {raw:?}");
    assert!(matches!(body.stmts[4].kind, StmtKind::If { .. }));
    assert_eq!(body.prov, vec![vec![], vec![0x40_1000], vec![0x40_1020]]);
    assert_eq!(body.stmts[4].prov, Prov(1));
}

/// An expression reads with C's precedence: `*` binds tighter than `+`.
#[test]
fn an_expression_reads_at_c_precedence() {
    let body = build("x = a + b * c;\n");
    let StmtKind::Expr(e) = &body.stmts[0].kind else {
        panic!("not an expression statement");
    };
    let ExprKind::Assign(None, _, value) = &e.kind else {
        panic!("not an assignment");
    };
    assert!(matches!(
        &value.kind,
        ExprKind::Binary(BinOp::Add, _, r) if matches!(r.kind, ExprKind::Binary(BinOp::Mul, ..))
    ));
}

/// A cast reads its type, a pointer included.
#[test]
fn a_cast_reads_its_type() {
    let body = build("return *(uint64_t*)(int32_t)a1;\n");
    let StmtKind::Return(Some(e)) = &body.stmts[0].kind else {
        panic!("not a return");
    };
    let ExprKind::Unary(UnOp::Deref, inner) = &e.kind else {
        panic!("not a load");
    };
    let ExprKind::Cast(CTy::Ptr(to), _) = &inner.kind else {
        panic!("not a cast to a pointer");
    };
    assert_eq!(
        **to,
        CTy::Int {
            bits: 64,
            signed: false
        }
    );
}

/// Text the builder cannot read stays raw and prints back as written.
#[test]
fn text_that_is_not_c_stays_as_written() {
    for text in [
        "rax = cpuid(); /* asm: cpuid */\n",
        "x = a +  b;\n",
        "  misindented;\n",
        "if (a) {\n",
        "}\n",
    ] {
        assert_eq!(print(&build(text)), text);
    }
    let body = build("x = a +  b;\n");
    assert_eq!(
        check(&body, &BTreeSet::new()),
        vec![Violation::Raw("x = a +  b;".to_owned())]
    );
}

/// The checks name undeclared reads, symbols that are not identifiers and dangling gotos.
#[test]
fn the_checks_name_what_is_not_c() {
    let body = build("x = y;\nFoo::bar(z);\ngoto L_10;\ngoto *x;\n");
    let declared: BTreeSet<&str> = ["x"].into_iter().collect();
    assert_eq!(
        check(&body, &declared),
        vec![
            Violation::Undeclared("y".to_owned()),
            Violation::NotIdent("Foo::bar".to_owned()),
            Violation::Undeclared("z".to_owned()),
            Violation::ComputedGoto("goto *x;".to_owned()),
            Violation::DanglingGoto(Label(0x10)),
        ]
    );
}

/// An identifier is never built from text that is not one.
#[test]
fn an_identifier_is_only_ever_c() {
    assert!(Ident::new("local_8").is_some());
    assert!(Ident::new("_x1").is_some());
    for bad in ["field_-0x1", "1a", "", "while", "a::b", "a b"] {
        assert!(Ident::new(bad).is_none(), "{bad}");
    }
}

/// Declarations print as the function header writes them.
#[test]
fn declarations_print_as_the_header_writes_them() {
    let mut out = String::new();
    print_decls(
        &[
            Decl {
                ty: CTy::parse("uint64_t"),
                names: vec![Name::of("rbx"), Name::of("rsi")],
                note: None,
            },
            Decl {
                ty: CTy::parse("Foo *"),
                names: vec![Name::of("a"), Name::of("b")],
                note: None,
            },
            Decl {
                ty: CTy::parse("uint32_t"),
                names: vec![Name::of("g_4000")],
                note: Some("@ 0x4000".to_owned()),
            },
        ],
        &mut out,
    );
    assert_eq!(
        out,
        "uint64_t rbx, rsi;\nFoo *a, *b;\nuint32_t g_4000; // @ 0x4000\n"
    );
}
