//! Choices a source wrote as `?:`: an `if`/`else` whose arms store two
//! names in one variable ([`named_choice`]), or whose arms each only set
//! one register temp ([`register_choice`]).

use super::super::super::ctext::{Ast, Base, Bin, CTy, Un, expression, named_type, tokens};
use super::*;

/// Rewrites `if (c) { x = a; } else { x = b; }` at line `k`, when `a` and
/// `b` are names, as `x = c ? a : b;`.
///
/// The arms store nothing but a name, and `x` is private ([`private`]), so
/// the choice and the two `if` arms write the same name into `x`. The two
/// names must be declared with one type: a `?:` converts its arms to a
/// common type before the store, which is a different value when the arms
/// differ. A test that calls something, or an arm that is not one name,
/// stays an `if`: that is the shape a source wrote as a statement. A test
/// binding looser than the `?:` keeps its parentheses ([`choice_test`]).
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
///
/// # Returns
///
/// Whether the `if` became a choice.
pub(super) fn named_choice(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(cond) = if_opener(open.trim()) else {
        return false;
    };
    if cond.contains('?') || cond.contains(',') || impure(cond) {
        return false;
    }
    let Some(mid) = loops::closing(lines, k, pad)
        .filter(|&m| lines.get(m).is_some_and(|l| l.trim() == "} else {"))
    else {
        return false;
    };
    let Some(end) =
        loops::closing(lines, mid, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    let Some((x, a)) = only_assign(lines, k + 1..mid, pad + 2) else {
        return false;
    };
    let Some((y, b)) = only_assign(lines, mid + 1..end, pad + 2) else {
        return false;
    };
    let name =
        |w: &str| w.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && is_ident(w);
    let same_type =
        decl_type(lines, &a).is_some_and(|ta| decl_type(lines, &b).as_ref() == Some(&ta));
    if x != y
        || !name(&a)
        || !name(&b)
        || a == b
        || a == x
        || b == x
        || !same_type
        || !private(lines, &x)
        || mentions_ident(cond, &x)
    {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let test = choice_test(cond);
    lines.splice(k..=end, [format!("{pad_s}{x} = {test} ? {a} : {b};")]);
    true
}

/// Returns an `if`'s test as the `?:` that replaces the `if` takes it: bare
/// when it reads as one expression binding tighter than the `?:`, else in
/// parentheses.
///
/// An assignment binds looser, and so does a comma, which the reader does
/// not take as one expression; any other test it does not read keeps its
/// parentheses too, since nothing says how it binds.
///
/// # Arguments
///
/// * `cond` - The test's text.
fn choice_test(cond: &str) -> String {
    if read(cond).is_some_and(|e| !matches!(e, Ast::Assign(..))) {
        cond.to_owned()
    } else {
        format!("({cond})")
    }
}

/// Rewrites `if (c) { t = a; } else { t = b; }` at line `k`, `t` a register
/// temp of an integer or pointer type, as `t = c ? a : b;`.
///
/// A temp is the compiler's own: at `-O0` every variable a source names
/// lives in a stack slot, so a register both arms set and nothing else is
/// the value of a `?:`. The function must show that shape, a scalar it
/// keeps in a stack slot; optimized code keeps its variables in registers,
/// where such an `if` is as likely the source's. Two names stay with
/// [`named_choice`]. An arm may also be `t = x; t op= y;`, one value when
/// the temp and `y` are integers: `(T)x op y`, `x` converted first as its
/// store did. C does not order the operands of `op`, so when `x` or `y`
/// has an effect the other must be a literal or a register temp, which
/// nothing it does can change. Each other arm is spelled as [`spelled`]
/// says. A floating temp stays an `if`: the `?:` would first convert its
/// integer arms to their common type, which turns `-1` beside an unsigned
/// arm positive before the store converts it. So does a temp wider than
/// `int` whose arms are a negative literal and one C types `unsigned int`.
/// A test that does not read as one expression binding tighter than the
/// `?:` (a comma, an assignment) keeps its parentheses ([`choice_test`]).
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
///
/// # Returns
///
/// Whether the `if` became a choice.
pub(super) fn register_choice(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(cond) = if_opener(open.trim()) else {
        return false;
    };
    let Some(mid) = loops::closing(lines, k, pad)
        .filter(|&m| lines.get(m).is_some_and(|l| l.trim() == "} else {"))
    else {
        return false;
    };
    let Some(end) =
        loops::closing(lines, mid, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    let (Some((t, a)), Some((u, b))) = (
        arm(lines, k + 1..mid, pad + 2),
        arm(lines, mid + 1..end, pad + 2),
    ) else {
        return false;
    };
    let temp = vars::is_var_name(&t) || is_register_name(&t);
    let names = matches!((&a, &b), (Arm::Set(x), Arm::Set(y)) if is_ident(x) && is_ident(y));
    if t != u || !temp || names || !slotted(lines) {
        return false;
    }
    let int = |ty: &str| ctype(ty).is_some_and(integer);
    let Some(ty) = decl_type(lines, &t).filter(|ty| int(ty) || ty.ends_with('*')) else {
        return false;
    };
    let settled = |v: &str| {
        read(v).is_some_and(|e| literal(&e)) || vars::is_var_name(v) || is_register_name(v)
    };
    let value = |arm: &Arm| match arm {
        Arm::Set(x) => Some(spelled(lines, x, &ty)),
        Arm::Updated(x, op, y) => {
            let ordered = (!changes_state(x) || settled(y)) && (!changes_state(y) || settled(x));
            let first = if known(lines, x, &ty) {
                x.clone()
            } else {
                format!("({ty}){}", grouped(x))
            };
            (int(&ty) && ordered && read(y).is_some_and(|e| integral(lines, &e)))
                .then(|| format!("{first} {op} {}", grouped(y)))
        }
    };
    let (Some(a), Some(b)) = (value(&a), value(&b)) else {
        return false;
    };
    let negative = |v: &str| read(v).is_some_and(|e| magnitude(&e).is_some());
    let unsigned = |v: &str| matches!(read(v), Some(Ast::Int(_, c)) if c == CTy::int(32, false));
    let positive = negative(&a) && unsigned(&b) || negative(&b) && unsigned(&a);
    if [cond, a.as_str(), b.as_str()]
        .iter()
        .any(|s| s.contains('?'))
        || integer_bits(&ty).is_none() && positive
    {
        return false;
    }
    let test = choice_test(cond);
    let line = format!("{}{t} = {test} ? {a} : {b};", " ".repeat(pad));
    lines.splice(k..=end, [line]);
    true
}

/// One arm's value, before the temp's type converts it.
enum Arm {
    /// `t = x;`: the value `x`.
    Set(String),
    /// `t = x; t op= y;`: `x`, the operator and `y`.
    Updated(String, &'static str, String),
}

/// Tells whether the function keeps a scalar in a stack slot, the shape of
/// code built without optimization.
///
/// # Arguments
///
/// * `lines` - The function text.
fn slotted(lines: &[String]) -> bool {
    lines.iter().any(|l| {
        l.trim()
            .strip_suffix(';')
            .and_then(|d| d.rsplit_once(' '))
            .is_some_and(|(ty, name)| {
                !ty.is_empty() && name.starts_with("local_") && is_ident(name)
            })
    })
}

/// Returns the one value an arm sets, `t = x;` or `t = x; t op= y;`, when
/// the arm holds nothing else at indentation `pad`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `span` - The lines inside the arm.
/// * `pad` - The arm's indentation.
///
/// # Returns
///
/// The temp and the value, or `None`.
fn arm(lines: &[String], span: std::ops::Range<usize>, pad: usize) -> Option<(String, Arm)> {
    let body: Vec<&str> = lines
        .get(span)?
        .iter()
        .map(String::as_str)
        .filter(|l| !l.trim().is_empty())
        .collect();
    if body.iter().any(|l| indent_of(l) != pad) {
        return None;
    }
    let (t, x) = plain_assignment(body.first()?)?;
    match body.as_slice() {
        [_] => Some((t.to_owned(), Arm::Set(x.to_owned()))),
        [_, update] => {
            let s = update.trim().strip_suffix(';')?;
            ["<<", ">>", "+", "-", "*", "/", "%", "&", "|", "^"]
                .into_iter()
                .find_map(|op| {
                    let (l, y) = s.split_once(&format!(" {op}= "))?;
                    (l == t && !y.contains(" = ") && !mentions_ident(y, t))
                        .then(|| (t.to_owned(), Arm::Updated(x.to_owned(), op, y.to_owned())))
                })
        }
        _ => None,
    }
}

/// Returns an arm's value as the temp's assignment converted it, spelled so
/// the `?:` holding it converts it the same way.
///
/// The `?:` converts both arms to their common type before the store
/// converts that to the temp's. When both arms are integers the common
/// type is at least `int`, so it keeps every bit a temp no wider than
/// `int` keeps; a wider temp needs an arm of its own width. So an arm
/// stays as it is when the text types it as the temp ([`known`]), when it
/// is an integer literal of an integer temp (the one pair of literals the
/// conversion changes keeps its `if`, [`register_choice`]), or when the
/// temp is no wider than `int` and the text makes the arm an integer
/// ([`integral`]). A negative literal of an unsigned temp is spelled as
/// its pattern and a zero for a pointer as `(void *)0`; every other arm is
/// cast, a pointer temp's other literals too.
///
/// # Arguments
///
/// * `lines` - The body lines, for the declarations.
/// * `value` - The arm's value.
/// * `ty` - The temp's declared type.
fn spelled(lines: &[String], value: &str, ty: &str) -> String {
    let e = read(value);
    let pointer = ty.ends_with('*');
    if pointer && matches!(e, Some(Ast::Int(0, _))) {
        return "(void *)0".to_owned();
    }
    if !pointer && e.as_ref().is_some_and(literal) {
        let bits = ty
            .strip_prefix("uint")
            .and_then(|r| r.strip_suffix("_t"))
            .and_then(|w| w.parse::<u32>().ok())
            .filter(|w| [8, 16, 32, 64].contains(w));
        return match (e.as_ref().and_then(magnitude), bits) {
            (Some(k), Some(w)) => {
                let all = u64::MAX >> (64 - w);
                format!("{:#x}", all.wrapping_sub(k).wrapping_add(1) & all)
            }
            _ => value.to_owned(),
        };
    }
    let integer = integer_bits(ty).is_some() && e.is_some_and(|e| integral(lines, &e));
    if integer || known(lines, value, ty) {
        value.to_owned()
    } else {
        format!("({ty}){}", grouped(value))
    }
}

/// Reads one value of the text as an expression.
///
/// # Arguments
///
/// * `value` - The value's text.
///
/// # Returns
///
/// The expression, or `None` when the text does not read as one (a cast
/// to a type the reader does not know, say).
fn read(value: &str) -> Option<Ast> {
    expression(&tokens(value).ok()?, &|n| named_type(n, 64).is_none(), 64).ok()
}

/// Returns the C type a type's text names.
///
/// # Arguments
///
/// * `ty` - The type's text, as a declaration gives it.
///
/// # Returns
///
/// The type, or `None` when the reader does not know the name.
fn ctype(ty: &str) -> Option<CTy> {
    let Ast::Cast(c, _) = read(&format!("({ty})0"))? else {
        return None;
    };
    Some(c)
}

/// Tells whether a type is an integer: no pointer, no floating value.
///
/// # Arguments
///
/// * `c` - The type.
fn integer(c: CTy) -> bool {
    c.ptr == 0 && matches!(c.base, Base::Int(..))
}

/// Tells whether an expression is an integer literal, `-k` included when C
/// gives `k` a signed type, so that `-k` is negative.
///
/// # Arguments
///
/// * `e` - The expression.
fn literal(e: &Ast) -> bool {
    matches!(e, Ast::Int(..)) || magnitude(e).is_some()
}

/// Returns `k` when an expression is the negative literal `-k`.
///
/// # Arguments
///
/// * `e` - The expression.
///
/// # Returns
///
/// `k`, or `None` for anything else, `-k` of an unsigned `k` included: C
/// makes that a positive value.
fn magnitude(e: &Ast) -> Option<u64> {
    let Ast::Un(Un::Neg, k) = e else {
        return None;
    };
    let Ast::Int(v, c) = **k else {
        return None;
    };
    c.signed().then_some(v)
}

/// Tells whether the text types a value as `ty`: a name declared with it,
/// a call whose `extern` declaration returns it, or a cast to it.
///
/// # Arguments
///
/// * `lines` - The body lines, for the declarations.
/// * `value` - The value's text.
/// * `ty` - The type's text, as [`decl_type`] gives it.
fn known(lines: &[String], value: &str, ty: &str) -> bool {
    let Some(e) = read(value) else {
        return false;
    };
    let text = if matches!(e, Ast::Cast(..)) {
        let cast = value.strip_prefix('(').and_then(|r| r.split_once(')'));
        cast.map(|(c, _)| norm_ty(c))
    } else {
        declared_type(lines, &e)
    };
    text.as_deref() == Some(ty)
}

/// Returns the type's text the declarations give a name, or the result an
/// `extern` declaration gives a called name.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `e` - The value.
///
/// # Returns
///
/// The type's text, or `None` for any other value or a name nothing
/// declares.
fn declared_type(lines: &[String], e: &Ast) -> Option<String> {
    if let Ast::Call(f, _) = e
        && let Ast::Name(callee) = &**f
    {
        return lines.iter().find_map(|l| {
            let (head, _) = l.trim().strip_prefix("extern ")?.split_once('(')?;
            declarator_type(head, callee)
        });
    }
    let Ast::Name(n) = e else {
        return None;
    };
    decl_type(lines, n)
}

/// Returns the type the text states for a value: a cast's, or what
/// [`declared_type`] reads.
///
/// # Arguments
///
/// * `lines` - The body lines, for the declarations.
/// * `e` - The value.
///
/// # Returns
///
/// The type, or `None` when the text states none.
fn stated(lines: &[String], e: &Ast) -> Option<CTy> {
    if let Ast::Cast(c, _) = e {
        return Some(*c);
    }
    ctype(&declared_type(lines, e)?)
}

/// Tells whether the text makes a value an integer, never a pointer or a
/// floating value.
///
/// A literal, a comparison, a logical, bitwise, shift or remainder
/// operation is one, since C takes or gives only integers there; a sum,
/// difference, product or quotient is one when both its operands are; and
/// so is a value whose type the text states as an integer ([`stated`]), or
/// a dereference or index through a pointer to one.
///
/// # Arguments
///
/// * `lines` - The body lines, for the declarations.
/// * `e` - The value.
fn integral(lines: &[String], e: &Ast) -> bool {
    match e {
        Ast::Int(..) | Ast::Logic(..) | Ast::Un(Un::Not | Un::LogNot, _) => true,
        Ast::Bin(
            Bin::Rem
            | Bin::Shl
            | Bin::Shr
            | Bin::Lt
            | Bin::Le
            | Bin::Gt
            | Bin::Ge
            | Bin::Eq
            | Bin::Ne
            | Bin::And
            | Bin::Xor
            | Bin::Or,
            ..,
        ) => true,
        Ast::Bin(Bin::Add | Bin::Sub | Bin::Mul | Bin::Div, x, y) => {
            integral(lines, x) && integral(lines, y)
        }
        Ast::Un(Un::Neg | Un::Plus, x) => integral(lines, x),
        Ast::Un(Un::Deref, p) | Ast::Index(p, _) => {
            stated(lines, p).and_then(CTy::pointee).is_some_and(integer)
        }
        Ast::Cast(..) | Ast::Name(_) | Ast::Call(..) => stated(lines, e).is_some_and(integer),
        Ast::Float(..)
        | Ast::Str(_)
        | Ast::Un(Un::Addr, _)
        | Ast::Pick(..)
        | Ast::Arrow(..)
        | Ast::Assign(..)
        | Ast::Step(..) => false,
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    //! The choice on hand-written text, beside the arms that keep an `if`.

    use super::super::select_statements;

    /// Runs the selects over a body, the declarations first.
    ///
    /// # Arguments
    ///
    /// * `text` - The body.
    fn run(text: &str) -> String {
        select_statements(text, "uint64_t", &[])
    }

    /// Arms that only set one register temp are the choice they were, each
    /// converted as its assignment converted it; an update converts the
    /// first value before it applies.
    #[test]
    fn a_temp_both_arms_set_is_a_choice() {
        let text = concat!(
            "uint64_t var2;\n",
            "void *var3;\n",
            "uint32_t var4;\n",
            "uint32_t local_18;\n",
            "\n",
            "if (sub_10(a1, 1) < 0) {\n",
            "  var2 = -1;\n",
            "} else {\n",
            "  var2 = sub_10(a1, 1);\n",
            "  var2 *= 2;\n",
            "}\n",
            "if (a2 == 0) {\n",
            "  var3 = nullptr;\n",
            "} else {\n",
            "  var3 = a2 + 8;\n",
            "}\n",
            "if (a3 != 0) {\n",
            "  var4 = 7;\n",
            "} else {\n",
            "  var4 = a1;\n",
            "  var4 >>= 1;\n",
            "}\n",
        );
        assert_eq!(
            run(text),
            concat!(
                "uint64_t var2;\n",
                "void *var3;\n",
                "uint32_t var4;\n",
                "uint32_t local_18;\n",
                "\n",
                "var2 = sub_10(a1, 1) < 0 ? 0xffffffffffffffff : (uint64_t)sub_10(a1, 1) * 2;\n",
                "var3 = a2 == 0 ? (void *)0 : (void *)(a2 + 8);\n",
                "var4 = a3 != 0 ? 7 : (uint32_t)a1 >> 1;\n",
            )
        );
    }

    /// A stack slot, a store, an arm doing more, a temp the declarations do
    /// not type, an update of a float or a pointer temp, and any temp in a
    /// function keeping no scalar in a stack slot all keep the `if`.
    #[test]
    fn other_arms_keep_the_if() {
        for text in [
            "uint32_t local_10;\nif (a1) {\n  local_10 = 1;\n} else {\n  local_10 = 2;\n}\n",
            "uint32_t var1;\nuint32_t local_10;\nif (a1) {\n  *(uint32_t*)a2 = 1;\n} else {\n  var1 = 2;\n}\n",
            "uint32_t var1;\nuint32_t local_10;\nif (a1) {\n  var1 = 1;\n  f(var1);\n} else {\n  var1 = 2;\n}\n",
            "uint32_t local_10;\nif (a1) {\n  var1 = 1;\n} else {\n  var1 = 2;\n}\n",
            "uint32_t var1;\nif (a1) {\n  var1 = 1;\n} else {\n  var1 = 2;\n}\n",
            "double var1;\nuint32_t local_10;\nif (a1) {\n  var1 = 1;\n} else {\n  var1 = a2;\n  var1 /= a3;\n}\n",
            "uint32_t *var1;\nuint32_t local_10;\nif (a1) {\n  var1 = a4;\n} else {\n  var1 = a2;\n  var1 += 8;\n}\n",
        ] {
            assert_eq!(run(text), text);
        }
    }

    /// An arm the text types as the temp is not cast again.
    ///
    /// Such an arm is a declared name, a call its `extern` declaration
    /// types, or a cast; an integer arm of a temp no wider than `int` is
    /// not cast either. A pointer or floating arm of such a temp still is,
    /// a sum through a pointer too, and so is an integer arm of another
    /// type for a wider temp.
    #[test]
    fn an_arm_the_text_types_is_not_cast() {
        let text = concat!(
            "extern uint64_t sub_20(uint64_t a1);\n",
            "uint32_t var1;\n",
            "uint64_t var2;\n",
            "uint64_t var3;\n",
            "uint32_t var4;\n",
            "uint32_t var5;\n",
            "uint8_t *var6;\n",
            "int64_t var7;\n",
            "uint32_t var8;\n",
            "uint32_t var9;\n",
            "uint32_t local_18;\n",
            "double local_60;\n",
            "\n",
            "if (a1 == 0) {\n",
            "  var1 = *(uint16_t*)a2;\n",
            "} else {\n",
            "  var1 = *(int16_t*)a2 & 0xff;\n",
            "}\n",
            "if (a3 != 0) {\n",
            "  var2 = sub_20(a1);\n",
            "} else {\n",
            "  var2 = (uint64_t)a4;\n",
            "}\n",
            "if (a5 != 0) {\n",
            "  var3 = sub_20(a1);\n",
            "  var3 *= 2;\n",
            "} else {\n",
            "  var3 = 0;\n",
            "}\n",
            "if (a6 == 1) {\n",
            "  var4 = &local_18;\n",
            "} else {\n",
            "  var4 = local_18 + 1;\n",
            "}\n",
            "if (a7 == 1) {\n",
            "  var5 = var6 + 1;\n",
            "} else {\n",
            "  var5 = 2;\n",
            "}\n",
            "if (a8 != 0) {\n",
            "  var7 = (int32_t)a2;\n",
            "} else {\n",
            "  var7 = 0xffffffff;\n",
            "}\n",
            "if (a9 != 0) {\n",
            "  var8 = -local_60;\n",
            "} else {\n",
            "  var8 = 1;\n",
            "}\n",
            "if (a10 != 0) {\n",
            "  var9 = sub_20(a1);\n",
            "} else {\n",
            "  var9 = 5;\n",
            "}\n",
        );
        let out = run(text);
        for line in [
            "var1 = a1 == 0 ? *(uint16_t*)a2 : *(int16_t*)a2 & 0xff;\n",
            "var2 = a3 != 0 ? sub_20(a1) : (uint64_t)a4;\n",
            "var3 = a5 != 0 ? sub_20(a1) * 2 : 0;\n",
            "var4 = a6 == 1 ? (uint32_t)(&local_18) : local_18 + 1;\n",
            "var5 = a7 == 1 ? (uint32_t)(var6 + 1) : 2;\n",
            "var7 = a8 != 0 ? (int64_t)((int32_t)a2) : 0xffffffff;\n",
            "var8 = a9 != 0 ? (uint32_t)(-local_60) : 1;\n",
            "var9 = a10 != 0 ? sub_20(a1) : 5;\n",
        ] {
            assert!(out.contains(line), "{line}{out}");
        }
    }

    /// An update whose two values a `?:` could run in either order keeps
    /// the `if`.
    ///
    /// That is a call beside another call, a memory read or a slot, each an
    /// integer the declarations type; beside a register temp it is still
    /// the choice.
    #[test]
    fn an_update_that_could_run_out_of_order_keeps_the_if() {
        for text in [
            "extern uint64_t sub_2(uint64_t a1);\nuint64_t var1;\nuint32_t local_10;\nif (a1) {\n  var1 = sub_1(a2);\n  var1 += sub_2(a3);\n} else {\n  var1 = 0;\n}\n",
            "extern uint64_t sub_2(uint64_t a1);\nuint64_t var1;\nuint32_t local_10;\nif (a1) {\n  var1 = *(uint64_t*)a2;\n  var1 += sub_2(a3);\n} else {\n  var1 = 0;\n}\n",
            "uint64_t var1;\nuint32_t local_10;\nif (a1) {\n  var1 = sub_1(a2);\n  var1 += local_10;\n} else {\n  var1 = 0;\n}\n",
        ] {
            assert_eq!(run(text), text);
        }
        let text = "uint64_t var1, var2;\nuint32_t local_10;\nif (a1) {\n  var1 = sub_1(a2);\n  var1 += var2;\n} else {\n  var1 = 0;\n}\n";
        assert_eq!(
            run(text),
            "uint64_t var1, var2;\nuint32_t local_10;\nvar1 = a1 ? (uint64_t)sub_1(a2) + var2 : 0;\n"
        );
    }

    /// A floating temp keeps the `if`, and so does an update by a floating
    /// value; a pointer temp casts a literal other than zero.
    #[test]
    fn a_choice_converts_no_integer_through_a_float() {
        for text in [
            "double var1;\nuint32_t local_10;\nif (a1) {\n  var1 = -1;\n} else {\n  var1 = 0xffffffffffffffff;\n}\n",
            "uint32_t var1;\nuint32_t local_10;\nif (a1) {\n  var1 = a2;\n  var1 *= 2.5;\n} else {\n  var1 = 0;\n}\n",
        ] {
            assert_eq!(run(text), text);
        }
        let text = "void *var3;\nuint32_t local_10;\nif (a1) {\n  var3 = 0x1000;\n} else {\n  var3 = a2 + 8;\n}\n";
        assert!(
            run(text).contains("var3 = a1 ? (void *)0x1000 : (void *)(a2 + 8);\n"),
            "{}",
            run(text)
        );
    }

    /// Literal arms are a choice only where the `?:` keeps their values.
    ///
    /// A temp wider than `int` keeps the `if` whose arms are a negative
    /// literal and one C types `unsigned int`, which the `?:` would turn
    /// the negative one into; with a signed literal, or for a temp no
    /// wider than `int`, it is the choice. `-k` of an unsigned `k` is no
    /// negative literal, so it is cast as it is.
    #[test]
    fn literal_arms_keep_their_values() {
        let pair = "int64_t var1;\nuint32_t local_10;\nif (a1) {\n  var1 = -1;\n} else {\n  var1 = 0xffffffff;\n}\n";
        assert_eq!(run(pair), pair);
        for (ty, other, want) in [
            ("int64_t", "0x7fffffff", "var1 = a1 ? -1 : 0x7fffffff;\n"),
            ("int32_t", "0xffffffff", "var1 = a1 ? -1 : 0xffffffff;\n"),
            (
                "uint64_t",
                "a2",
                "var1 = a1 ? (uint64_t)(-0x80000000) : (uint64_t)a2;\n",
            ),
        ] {
            let first = if ty == "uint64_t" {
                "-0x80000000"
            } else {
                "-1"
            };
            let text = format!(
                "{ty} var1;\nuint32_t local_10;\nif (a1) {{\n  var1 = {first};\n}} else {{\n  var1 = {other};\n}}\n"
            );
            assert!(run(&text).contains(want), "{}", run(&text));
        }
    }

    /// A test that binds looser than the `?:`, a comma or an assignment,
    /// keeps its parentheses; one that binds tighter needs none.
    #[test]
    fn a_loose_test_keeps_its_parentheses() {
        for (cond, test) in [
            ("a1, a2", "(a1, a2)"),
            ("a4 = a1", "(a4 = a1)"),
            ("a1 && a2", "a1 && a2"),
        ] {
            let text = format!(
                "uint32_t var1;\nuint32_t local_10;\nif ({cond}) {{\n  var1 = -1;\n}} else {{\n  var1 = a3 + 1;\n}}\n"
            );
            let want = format!("var1 = {test} ? 0xffffffff : (uint32_t)(a3 + 1);\n");
            assert!(run(&text).contains(&want), "{}", run(&text));
        }
    }

    /// A choice of two names keeps a test that binds looser than the `?:`
    /// in its parentheses too.
    ///
    /// C reads `x = a4 = a1 ? a : b;` as `x = (a4 = (a1 ? a : b));`, which
    /// stores the choice in `a4` where the `if` stored `a1`.
    #[test]
    fn a_named_choice_keeps_a_loose_test_in_parentheses() {
        for (cond, test) in [("a4 = a1", "(a4 = a1)"), ("a1 == 0", "a1 == 0")] {
            let text = format!(
                "uint64_t var1;\nFILE *stdout; // @ 0x7160\nFILE *stderr; // @ 0x71a0\n\nif ({cond}) {{\n  var1 = stdout;\n}} else {{\n  var1 = stderr;\n}}\nfprintf(var1, s);\n"
            );
            let want = format!("var1 = {test} ? stdout : stderr;\n");
            assert!(run(&text).contains(&want), "{}", run(&text));
        }
    }
}
