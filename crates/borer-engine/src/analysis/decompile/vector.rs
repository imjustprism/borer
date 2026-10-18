//! Packed vector operations as GNU C vector-extension expressions.
//!
//! A lifter keeps a packed instruction whole, as a call named for it:
//! `paddd(a, b)` on x86, `__add_4s(a, b)` on arm64. No C compiler knows
//! those names, so the text spells each lane operation the way GCC and
//! clang write vector code: operands cast to a vector type (`u32x4`, a
//! `typedef uint32_t u32x4 __attribute__((vector_size(16), aligned(1)));`),
//! lane-wise arithmetic as C's operators, a lane permutation as
//! `__builtin_shufflevector`, and the few operations no operator writes as
//! the compiler's own builtin for the instruction
//! (`__builtin_ia32_pmaddwd128`). A register stays the 128-bit integer the
//! rest of the text holds it in, so an operand is that integer cast to the
//! lanes it is read as, and the whole expression is cast back:
//! `var2 = (uint128_t)((u64x2)(uint128_t)var2 + (u64x2)(uint128_t)var3);`.
//!
//! [`declare`] then puts the typedefs the text names at the top of its
//! declarations, along with the value of every read-only 128-bit constant
//! the text reads, which the declaration alone would leave undefined.
//!
//! A call this module does not know keeps its name; nothing is guessed.

use super::expr::{ATOM, Expr, Key, Ty, UNARY};
use super::expr_render::Names;
use crate::program::Program;

/// One lane's C type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Elem {
    /// `int8_t`.
    I8,
    /// `uint8_t`.
    U8,
    /// `int16_t`.
    I16,
    /// `uint16_t`.
    U16,
    /// `int32_t`.
    I32,
    /// `uint32_t`.
    U32,
    /// `int64_t`.
    I64,
    /// `uint64_t`.
    U64,
    /// `float`.
    F32,
    /// `double`.
    F64,
}

impl Elem {
    /// Every lane type, in the order the typedefs are written.
    const ALL: [Elem; 10] = [
        Elem::I8,
        Elem::U8,
        Elem::I16,
        Elem::U16,
        Elem::I32,
        Elem::U32,
        Elem::I64,
        Elem::U64,
        Elem::F32,
        Elem::F64,
    ];

    /// The lane's width in bits.
    fn bits(self) -> u32 {
        match self {
            Elem::I8 | Elem::U8 => 8,
            Elem::I16 | Elem::U16 => 16,
            Elem::I32 | Elem::U32 | Elem::F32 => 32,
            Elem::I64 | Elem::U64 | Elem::F64 => 64,
        }
    }

    /// The lane's C type name.
    fn c(self) -> &'static str {
        match self {
            Elem::I8 => "int8_t",
            Elem::U8 => "uint8_t",
            Elem::I16 => "int16_t",
            Elem::U16 => "uint16_t",
            Elem::I32 => "int32_t",
            Elem::U32 => "uint32_t",
            Elem::I64 => "int64_t",
            Elem::U64 => "uint64_t",
            Elem::F32 => "float",
            Elem::F64 => "double",
        }
    }

    /// The short spelling a vector type's name starts with.
    fn short(self) -> &'static str {
        match self {
            Elem::I8 => "i8",
            Elem::U8 => "u8",
            Elem::I16 => "i16",
            Elem::U16 => "u16",
            Elem::I32 => "i32",
            Elem::U32 => "u32",
            Elem::I64 => "i64",
            Elem::U64 => "u64",
            Elem::F32 => "f32",
            Elem::F64 => "f64",
        }
    }

    /// The unsigned integer lane of a width.
    ///
    /// # Arguments
    ///
    /// * `bits` - The width, 8 to 64.
    fn unsigned(bits: u32) -> Elem {
        match bits {
            8 => Elem::U8,
            16 => Elem::U16,
            32 => Elem::U32,
            _ => Elem::U64,
        }
    }

    /// The signed integer lane of a width.
    ///
    /// # Arguments
    ///
    /// * `bits` - The width, 8 to 64.
    fn signed(bits: u32) -> Elem {
        match bits {
            8 => Elem::I8,
            16 => Elem::I16,
            32 => Elem::I32,
            _ => Elem::I64,
        }
    }
}

/// A vector type: its lane and whether it spans 128 bits or the low 64.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Vt {
    /// The lane type.
    elem: Elem,
    /// Whether the vector is 16 bytes; otherwise 8.
    whole: bool,
}

impl Vt {
    /// A 16-byte vector of a lane type.
    ///
    /// # Arguments
    ///
    /// * `elem` - The lane type.
    fn whole(elem: Elem) -> Vt {
        Vt { elem, whole: true }
    }

    /// How many lanes the vector holds.
    fn lanes(self) -> u32 {
        (if self.whole { 128 } else { 64 }) / self.elem.bits()
    }

    /// The type's name in the text: `u32x4`.
    fn name(self) -> String {
        format!("{}x{}", self.elem.short(), self.lanes())
    }

    /// The integer the text holds a vector of this size in.
    fn word(self) -> &'static str {
        if self.whole { "uint128_t" } else { "uint64_t" }
    }
}

/// A packed operation's text, of a vector type.
#[derive(Debug, Clone, PartialEq, Eq)]
struct V {
    /// The expression.
    text: String,
    /// Its C type; `None` for a builtin's or a comparison's own vector
    /// type, which is the right size but no typedef this module names.
    ty: Option<Vt>,
    /// The size the value has, whatever its type.
    whole: bool,
    /// The text binds as tightly as a cast's operand needs.
    tight: bool,
}

impl V {
    /// An operation of a named vector type.
    ///
    /// # Arguments
    ///
    /// * `text` - The expression.
    /// * `ty` - Its type.
    /// * `tight` - The text binds as tightly as a cast's operand needs.
    fn of(text: String, ty: Vt, tight: bool) -> V {
        V {
            text,
            ty: Some(ty),
            whole: ty.whole,
            tight,
        }
    }

    /// A value of a vector type no typedef names: a comparison, a builtin.
    ///
    /// # Arguments
    ///
    /// * `text` - The expression.
    /// * `whole` - The value is 16 bytes; otherwise 8.
    /// * `tight` - The text binds as tightly as a cast's operand needs.
    fn untyped(text: String, whole: bool, tight: bool) -> V {
        V {
            text,
            ty: None,
            whole,
            tight,
        }
    }

    /// The text as a cast's operand.
    fn operand(&self) -> String {
        if self.tight {
            self.text.clone()
        } else {
            format!("({})", self.text)
        }
    }
}

/// Renders a call as the vector expression it names, cast back to the
/// integer the text holds a register in.
///
/// # Arguments
///
/// * `f` - The call's name.
/// * `args` - Its arguments.
/// * `n` - Name resolution.
///
/// # Returns
///
/// `(text, precedence)`, or `None` for a call that is no packed operation
/// this module spells.
pub(super) fn render(f: &str, args: &[Expr], n: &Names<'_>) -> Option<(String, u8)> {
    if let Some(mask) = movemask(f, args, n) {
        return Some((mask, ATOM));
    }
    if let Some(lane) = lane_result(f, args, n) {
        return Some(lane);
    }
    let v = packed(f, args, n)?;
    let word = if v.whole { "uint128_t" } else { "uint64_t" };
    Some((format!("({word}){}", v.operand()), UNARY))
}

/// Renders a packed call's lowest lane as the float a scalar operation
/// reads there, when the call's lanes are floats.
///
/// # Arguments
///
/// * `e` - The operand of the scalar operation.
/// * `n` - Name resolution.
///
/// # Returns
///
/// `((f64x2)v)[0]`, or `None` when `e` is no packed float operation.
pub(super) fn float_lane(e: &Expr, n: &Names<'_>) -> Option<String> {
    let Expr::Call(f, args) = e else {
        return None;
    };
    let v = packed(f, args, n)?;
    let ty = v.ty.filter(|t| matches!(t.elem, Elem::F32 | Elem::F64))?;
    Some(format!("{}[0]", cast_to(&v, ty)))
}

/// A sign-bit gather (`pmovmskb`, `movmskps`, `movmskpd`) as the builtin
/// that computes it, an `int`.
///
/// # Arguments
///
/// * `f` - The call's name.
/// * `args` - Its arguments.
/// * `n` - Name resolution.
fn movemask(f: &str, args: &[Expr], n: &Names<'_>) -> Option<String> {
    let [a] = args else {
        return None;
    };
    let (builtin, lane) = match f {
        "pmovmskb" => ("__builtin_ia32_pmovmskb128", Elem::I8),
        "movmskps" => ("__builtin_ia32_movmskps", Elem::F32),
        "movmskpd" => ("__builtin_ia32_movmskpd", Elem::F64),
        _ => return None,
    };
    Some(format!("{builtin}({})", operand(a, Vt::whole(lane), n)))
}

/// The vector expression a packed call names.
///
/// # Arguments
///
/// * `f` - The call's name: an x86 mnemonic, or `__op_arrangement` on
///   arm64.
/// * `args` - Its arguments.
/// * `n` - Name resolution.
fn packed(f: &str, args: &[Expr], n: &Names<'_>) -> Option<V> {
    match f.strip_prefix("__") {
        Some(rest) => neon(rest, args, n),
        None => sse(f, args, n),
    }
}

/// An x86 packed operation.
///
/// # Arguments
///
/// * `f` - The mnemonic, lowercased.
/// * `args` - Its arguments, the destination first where it is read.
/// * `n` - Name resolution.
fn sse(f: &str, args: &[Expr], n: &Names<'_>) -> Option<V> {
    let w = Vt::whole;
    Some(match (f, args) {
        ("pxor" | "xorps" | "xorpd", [a, b]) => bitwise("^", a, b, n),
        ("pand" | "andps" | "andpd", [a, b]) => bitwise("&", a, b, n),
        ("por" | "orps" | "orpd", [a, b]) => bitwise("|", a, b, n),
        ("pandn" | "andnps" | "andnpd", [a, b]) => {
            let t = bitwise_ty(a, b, n);
            V::of(
                format!("~{} & {}", operand(a, t, n), operand(b, t, n)),
                t,
                false,
            )
        }
        ("paddb" | "paddw" | "paddd" | "paddq", [a, b]) => {
            binary("+", w(Elem::unsigned(lane_of(f)?)), a, b, n)
        }
        ("psubb" | "psubw" | "psubd" | "psubq", [a, b]) => {
            binary("-", w(Elem::unsigned(lane_of(f)?)), a, b, n)
        }
        ("pmullw", [a, b]) => binary("*", w(Elem::U16), a, b, n),
        ("pmulld", [a, b]) => binary("*", w(Elem::U32), a, b, n),
        ("pmuludq", [a, b]) => {
            let t = w(Elem::U64);
            V::of(
                format!(
                    "({} & 0xffffffff) * ({} & 0xffffffff)",
                    operand(a, t, n),
                    operand(b, t, n)
                ),
                t,
                false,
            )
        }
        ("pcmpeqb" | "pcmpeqw" | "pcmpeqd" | "pcmpeqq", [a, b]) => {
            compare("==", w(Elem::signed(lane_of(f)?)), a, b, n)
        }
        ("pcmpgtb" | "pcmpgtw" | "pcmpgtd" | "pcmpgtq", [a, b]) => {
            compare(">", w(Elem::signed(lane_of(f)?)), a, b, n)
        }
        ("addps", [a, b]) => binary("+", w(Elem::F32), a, b, n),
        ("subps", [a, b]) => binary("-", w(Elem::F32), a, b, n),
        ("mulps", [a, b]) => binary("*", w(Elem::F32), a, b, n),
        ("divps", [a, b]) => binary("/", w(Elem::F32), a, b, n),
        ("addpd", [a, b]) => binary("+", w(Elem::F64), a, b, n),
        ("subpd", [a, b]) => binary("-", w(Elem::F64), a, b, n),
        ("mulpd", [a, b]) => binary("*", w(Elem::F64), a, b, n),
        ("divpd", [a, b]) => binary("/", w(Elem::F64), a, b, n),
        ("pshufd", [s, Expr::Const(o)]) => shuffle(
            w(Elem::U32),
            s,
            None,
            &(0..4).map(|k| pick(*o, k, 2)).collect::<Vec<_>>(),
            n,
        ),
        ("pshuflw", [s, Expr::Const(o)]) => {
            let order: Vec<u32> = (0..4).map(|k| pick(*o, k, 2)).chain(4..8).collect();
            shuffle(w(Elem::U16), s, None, &order, n)
        }
        ("pshufhw", [s, Expr::Const(o)]) => {
            let order: Vec<u32> = (0..4).chain((0..4).map(|k| 4 + pick(*o, k, 2))).collect();
            shuffle(w(Elem::U16), s, None, &order, n)
        }
        ("shufps", [a, b, Expr::Const(o)]) => {
            let order = [
                pick(*o, 0, 2),
                pick(*o, 1, 2),
                4 + pick(*o, 2, 2),
                4 + pick(*o, 3, 2),
            ];
            shuffle(w(Elem::F32), a, Some(b), &order, n)
        }
        ("shufpd", [a, b, Expr::Const(o)]) => shuffle(
            w(Elem::F64),
            a,
            Some(b),
            &[pick(*o, 0, 1), 2 + pick(*o, 1, 1)],
            n,
        ),
        (
            "punpcklbw" | "punpcklwd" | "punpckldq" | "punpcklqdq" | "punpckhbw" | "punpckhwd"
            | "punpckhdq" | "punpckhqdq",
            [a, b],
        ) => {
            let lane = match f.get(7..)? {
                "bw" => 8,
                "wd" => 16,
                "dq" => 32,
                _ => 64,
            };
            interleave(w(Elem::unsigned(lane)), f.starts_with("punpckh"), a, b, n)
        }
        ("unpcklps", [a, b]) => interleave(w(Elem::F32), false, a, b, n),
        ("unpckhps", [a, b]) => interleave(w(Elem::F32), true, a, b, n),
        ("unpcklpd", [a, b]) => interleave(w(Elem::F64), false, a, b, n),
        ("unpckhpd", [a, b]) => interleave(w(Elem::F64), true, a, b, n),
        ("movhlps", [a, b]) => shuffle(w(Elem::F32), a, Some(b), &[6, 7, 2, 3], n),
        ("movlhps", [a, b]) => shuffle(w(Elem::F32), a, Some(b), &[0, 1, 4, 5], n),
        ("psllw" | "pslld" | "psllq", [s, Expr::Const(k)]) => {
            shift("<<", w(Elem::unsigned(lane_of(f)?)), s, *k, n)
        }
        ("psrlw" | "psrld" | "psrlq", [s, Expr::Const(k)]) => {
            shift(">>", w(Elem::unsigned(lane_of(f)?)), s, *k, n)
        }
        ("psraw" | "psrad", [s, Expr::Const(k)]) => {
            let t = w(Elem::signed(lane_of(f)?));
            let k = (*k).min(u64::from(t.elem.bits() - 1));
            V::of(format!("{} >> {k}", operand(s, t, n)), t, false)
        }
        ("pslldq" | "psrldq", [s, Expr::Const(k)]) => {
            let k = u32::try_from(*k).unwrap_or(u32::MAX).min(16);
            let order: Vec<u32> = (0..16u32)
                .map(|i| match f {
                    "pslldq" => i.checked_sub(k).unwrap_or(16),
                    _ => (i + k).min(16),
                })
                .collect();
            let t = w(Elem::U8);
            let zero = format!("({}){{0}}", t.name());
            V::of(
                format!(
                    "__builtin_shufflevector({}, {zero}, {})",
                    operand(s, t, n),
                    list(&order)
                ),
                t,
                true,
            )
        }
        ("pmaddwd", [a, b]) => builtin("__builtin_ia32_pmaddwd128", Elem::I16, a, b, n),
        ("packsswb", [a, b]) => builtin("__builtin_ia32_packsswb128", Elem::I16, a, b, n),
        ("packssdw", [a, b]) => builtin("__builtin_ia32_packssdw128", Elem::I32, a, b, n),
        ("packuswb", [a, b]) => builtin("__builtin_ia32_packuswb128", Elem::I16, a, b, n),
        ("cvtdq2ps", [a]) => V::of(
            format!(
                "__builtin_convertvector({}, f32x4)",
                operand(a, w(Elem::I32), n)
            ),
            w(Elem::F32),
            true,
        ),
        ("cvtdq2pd", [a]) => {
            let t = w(Elem::I32);
            let s = operand(a, t, n);
            V::of(
                format!("__builtin_convertvector(__builtin_shufflevector({s}, {s}, 0, 1), f64x2)"),
                w(Elem::F64),
                true,
            )
        }
        ("cvtps2pd", [a]) => {
            let t = w(Elem::F32);
            let s = operand(a, t, n);
            V::of(
                format!("__builtin_convertvector(__builtin_shufflevector({s}, {s}, 0, 1), f64x2)"),
                w(Elem::F64),
                true,
            )
        }
        _ => return None,
    })
}

/// The operation and arrangement an arm64 call's name holds:
/// `cmeq_16b` is `cmeq` over byte lanes, all 128 bits.
///
/// # Arguments
///
/// * `f` - The name after its leading `__`.
///
/// # Returns
///
/// `(operation, lane bits, whole)`, or `None` for a name with no
/// arrangement of 64 or 128 bits.
fn arrangement(f: &str) -> Option<(&str, u32, bool)> {
    let (op, arrangement) = f.rsplit_once('_')?;
    let split = arrangement.find(|c: char| !c.is_ascii_digit())?;
    let count: u32 = arrangement.get(..split)?.parse().ok()?;
    let bits = match arrangement.get(split..)? {
        "b" => 8,
        "h" => 16,
        "s" => 32,
        "d" => 64,
        _ => return None,
    };
    let whole = match count.checked_mul(bits)? {
        128 => true,
        64 => false,
        _ => return None,
    };
    Some((op, bits, whole))
}

/// An arm64 operation whose result is one lane, not a vector.
///
/// `addv` is the sum of every lane, the scalar `addp` the sum of two,
/// `sminv` and its kin the extreme lane as the compiler's reduction
/// builtin, and `umov` the lane an index names.
///
/// # Arguments
///
/// * `f` - The call's name.
/// * `args` - Its arguments.
/// * `n` - Name resolution.
///
/// # Returns
///
/// `(text, precedence)`, or `None` for any other call.
fn lane_result(f: &str, args: &[Expr], n: &Names<'_>) -> Option<(String, u8)> {
    let (op, bits, whole) = arrangement(f.strip_prefix("__")?)?;
    let t = Vt {
        elem: Elem::unsigned(bits),
        whole,
    };
    match (op, args) {
        ("addv", [a]) => {
            let v = format!("({})", operand(a, t, n));
            let sum: Vec<String> = (0..t.lanes()).map(|k| format!("{v}[{k}]")).collect();
            Some((format!("({})({})", t.elem.c(), sum.join(" + ")), UNARY))
        }
        ("umov", [a, Expr::Const(k)]) => Some((format!("({})[{k}]", operand(a, t, n)), ATOM)),
        ("addp", [a]) => {
            let v = format!("({})", operand(a, t, n));
            Some((format!("({})({v}[0] + {v}[1])", t.elem.c()), UNARY))
        }
        ("sminv" | "smaxv", [a]) => {
            let signed = Vt {
                elem: Elem::signed(bits),
                whole,
            };
            let kind = if op == "sminv" { "min" } else { "max" };
            Some((
                format!("__builtin_reduce_{kind}({})", operand(a, signed, n)),
                ATOM,
            ))
        }
        ("uminv" | "umaxv", [a]) => {
            let kind = if op == "uminv" { "min" } else { "max" };
            Some((
                format!("__builtin_reduce_{kind}({})", operand(a, t, n)),
                ATOM,
            ))
        }
        _ => None,
    }
}

/// A scalar converted to a lane type, as a vector operation with it
/// broadcasts it.
///
/// # Arguments
///
/// * `e` - The scalar.
/// * `elem` - The lane type.
/// * `n` - Name resolution.
fn scalar(e: &Expr, elem: Elem, n: &Names<'_>) -> String {
    match e {
        Expr::Const(v) => format!("({}){v:#x}", elem.c()),
        Expr::Var(_) => format!("({}){}", elem.c(), e.render(n)),
        _ => format!("({})({})", elem.c(), e.render(n)),
    }
}

/// An arm64 packed operation, `op_arrangement`: `add_4s`.
///
/// # Arguments
///
/// * `f` - The name after its leading `__`.
/// * `args` - Its arguments.
/// * `n` - Name resolution.
fn neon(f: &str, args: &[Expr], n: &Names<'_>) -> Option<V> {
    let (op, bits, whole) = arrangement(f)?;
    let int = |e: Elem| Vt { elem: e, whole };
    let float = || {
        Some(Vt {
            elem: match bits {
                32 => Elem::F32,
                64 => Elem::F64,
                _ => return None,
            },
            whole,
        })
    };
    let unsigned = int(Elem::unsigned(bits));
    let signed = int(Elem::signed(bits));
    Some(match (op, args) {
        ("add", [a, b]) => binary("+", unsigned, a, b, n),
        ("sub", [a, b]) => binary("-", unsigned, a, b, n),
        ("mul", [a, b]) => binary("*", unsigned, a, b, n),
        ("neg", [a]) => V::of(format!("-{}", operand(a, unsigned, n)), unsigned, false),
        ("abs", [a]) => {
            let s = operand(a, signed, n);
            let sign = format!("({s} >> {})", bits - 1);
            V::of(format!("({s} ^ {sign}) - {sign}"), signed, false)
        }
        ("fadd", [a, b]) => binary("+", float()?, a, b, n),
        ("fsub", [a, b]) => binary("-", float()?, a, b, n),
        ("fmul", [a, b]) => binary("*", float()?, a, b, n),
        ("fdiv", [a, b]) => binary("/", float()?, a, b, n),
        ("cmeq", [a, b]) => compare("==", unsigned, a, b, n),
        ("cmhi", [a, b]) => compare(">", unsigned, a, b, n),
        ("cmhs", [a, b]) => compare(">=", unsigned, a, b, n),
        ("cmgt", [a, b]) => compare(">", signed, a, b, n),
        ("cmge", [a, b]) => compare(">=", signed, a, b, n),
        ("cmle", [a, b]) => compare("<=", signed, a, b, n),
        ("cmlt", [a, b]) => compare("<", signed, a, b, n),
        ("ushll" | "ushll2" | "sshll" | "sshll2", [a, Expr::Const(k)]) => {
            let to = if op.starts_with('s') {
                signed
            } else {
                unsigned
            };
            let wide = widened(a, Vt::whole(to.elem), op.ends_with('2'), n);
            if *k == 0 {
                V::of(wide, Vt::whole(to.elem), true)
            } else {
                V::of(format!("{wide} << {k}"), Vt::whole(to.elem), false)
            }
        }
        ("ext", [a, b, Expr::Const(k)]) => {
            let t = int(Elem::U8);
            let from = u32::try_from(*k).ok()?;
            let order: Vec<u32> = (from..from + t.lanes()).collect();
            shuffle(t, a, Some(b), &order, n)
        }
        ("ins", [d, x, Expr::Const(k)]) => {
            let t = Vt::whole(Elem::unsigned(bits));
            let count = t.lanes();
            let at = u32::try_from(*k).ok()?;
            let order: Vec<u32> = (0..count)
                .map(|i| if i == at { count } else { i })
                .collect();
            let splat = format!("({}){{0}} + {}", t.name(), scalar(x, t.elem, n));
            V::of(
                format!(
                    "__builtin_shufflevector({}, {splat}, {})",
                    operand(d, t, n),
                    list(&order)
                ),
                t,
                true,
            )
        }
        ("smin" | "smax", [a, b]) => elementwise(&op[1..], signed, a, b, n),
        ("umin" | "umax", [a, b]) => elementwise(&op[1..], unsigned, a, b, n),
        ("mla", [acc, a, b]) => V::of(
            format!(
                "{} + {} * {}",
                operand(acc, unsigned, n),
                operand(a, unsigned, n),
                operand(b, unsigned, n)
            ),
            unsigned,
            false,
        ),
        ("addp", [a, b]) => {
            let count = unsigned.lanes();
            let evens: Vec<u32> = (0..count).map(|k| 2 * k).collect();
            let odds: Vec<u32> = evens.iter().map(|k| k + 1).collect();
            let (x, y) = (operand(a, unsigned, n), operand(b, unsigned, n));
            V::of(
                format!(
                    "__builtin_shufflevector({x}, {y}, {}) + __builtin_shufflevector({x}, {y}, {})",
                    list(&evens),
                    list(&odds)
                ),
                unsigned,
                false,
            )
        }
        (
            "smlal" | "smlal2" | "umlal" | "umlal2" | "smull" | "smull2" | "umull" | "umull2"
            | "saddw" | "saddw2" | "uaddw" | "uaddw2",
            _,
        ) => {
            let to = Vt::whole(if op.starts_with('s') {
                Elem::signed(bits)
            } else {
                Elem::unsigned(bits)
            });
            let upper = op.ends_with('2');
            let wide = |e: &Expr| widened(e, to, upper, n);
            let text = match (&op[1..4], args) {
                ("mla", [acc, a, b]) => {
                    format!("{} + {} * {}", operand(acc, to, n), wide(a), wide(b))
                }
                ("mul", [a, b]) => format!("{} * {}", wide(a), wide(b)),
                ("add", [acc, b]) => format!("{} + {}", operand(acc, to, n), wide(b)),
                _ => return None,
            };
            V::of(text, to, false)
        }
        ("scvtf" | "ucvtf", [a]) => {
            let from = if op == "scvtf" { signed } else { unsigned };
            let to = float()?;
            V::of(
                format!(
                    "__builtin_convertvector({}, {})",
                    operand(a, from, n),
                    to.name()
                ),
                to,
                true,
            )
        }
        ("dup", [x]) => V::of(
            format!(
                "({}){{0}} + {}",
                unsigned.name(),
                scalar(x, unsigned.elem, n)
            ),
            unsigned,
            false,
        ),
        _ => return None,
    })
}

/// A lane-wise minimum or maximum, as the compiler's element-wise builtin.
///
/// # Arguments
///
/// * `kind` - `min` or `max`.
/// * `t` - The lanes' type, whose signedness picks the comparison.
/// * `a` - The first vector.
/// * `b` - The second.
/// * `n` - Name resolution.
fn elementwise(kind: &str, t: Vt, a: &Expr, b: &Expr, n: &Names<'_>) -> V {
    V::of(
        format!(
            "__builtin_elementwise_{kind}({}, {})",
            operand(a, t, n),
            operand(b, t, n)
        ),
        t,
        true,
    )
}

/// Half the lanes of a vector at twice their width, as a widening
/// operation reads its narrow sources.
///
/// # Arguments
///
/// * `e` - The narrow vector.
/// * `to` - The wide lanes, whose signedness extends them.
/// * `upper` - The upper half is read; otherwise the lower.
/// * `n` - Name resolution.
fn widened(e: &Expr, to: Vt, upper: bool, n: &Names<'_>) -> String {
    let narrow = Vt::whole(if matches!(to.elem, Elem::I16 | Elem::I32 | Elem::I64) {
        Elem::signed(to.elem.bits() / 2)
    } else {
        Elem::unsigned(to.elem.bits() / 2)
    });
    let count = to.lanes();
    let first = if upper { count } else { 0 };
    let order: Vec<u32> = (first..first + count).collect();
    let half = shuffle(narrow, e, None, &order, n);
    format!("__builtin_convertvector({}, {})", half.text, to.name())
}

/// The lane width an x86 integer mnemonic's last letter names: `b`, `w`,
/// `d` or `q`.
///
/// # Arguments
///
/// * `f` - The mnemonic.
fn lane_of(f: &str) -> Option<u32> {
    match f.chars().next_back()? {
        'b' => Some(8),
        'w' => Some(16),
        'd' => Some(32),
        'q' => Some(64),
        _ => None,
    }
}

/// The lane an immediate's `k`th field picks: a shuffle's selector.
///
/// # Arguments
///
/// * `o` - The immediate.
/// * `k` - The field's position.
/// * `width` - The field's width in bits, 1 or 2.
fn pick(o: u64, k: u32, width: u32) -> u32 {
    u32::try_from((o >> (k * width)) & ((1 << width) - 1)).unwrap_or(0)
}

/// A shuffle's indices as the builtin lists them.
///
/// # Arguments
///
/// * `order` - The indices.
fn list(order: &[u32]) -> String {
    order
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// A lane permutation of one or two vectors.
///
/// # Arguments
///
/// * `t` - The lanes' type.
/// * `a` - The first vector.
/// * `b` - The second, `None` when every index picks from the first: a
///   short first operand is passed twice, a longer one beside a zero
///   vector, so the text spells it once.
/// * `order` - Which lane each result lane takes, the second vector's
///   lanes numbered after the first's.
/// * `n` - Name resolution.
fn shuffle(t: Vt, a: &Expr, b: Option<&Expr>, order: &[u32], n: &Names<'_>) -> V {
    let first = operand(a, t, n);
    let second = match b {
        Some(b) => operand(b, t, n),
        None if matches!(a, Expr::Var(_) | Expr::Const(_) | Expr::Deref(..)) => first.clone(),
        None => format!("({}){{0}}", t.name()),
    };
    V::of(
        format!(
            "__builtin_shufflevector({first}, {second}, {})",
            list(order)
        ),
        t,
        true,
    )
}

/// An unpack: the low or high halves of two vectors' lanes, interleaved.
///
/// # Arguments
///
/// * `t` - The lanes' type.
/// * `high` - The high halves are taken.
/// * `a` - The vector whose lanes come first in each pair.
/// * `b` - The other.
/// * `n` - Name resolution.
fn interleave(t: Vt, high: bool, a: &Expr, b: &Expr, n: &Names<'_>) -> V {
    let lanes = t.lanes();
    let first = if high { lanes / 2 } else { 0 };
    let order: Vec<u32> = (0..lanes / 2)
        .flat_map(|k| [first + k, lanes + first + k])
        .collect();
    shuffle(t, a, Some(b), &order, n)
}

/// A lane-wise shift by a constant; a count past the lane is zero.
///
/// # Arguments
///
/// * `sym` - The operator.
/// * `t` - The lanes' type.
/// * `s` - The shifted vector.
/// * `k` - The count.
/// * `n` - Name resolution.
fn shift(sym: &str, t: Vt, s: &Expr, k: u64, n: &Names<'_>) -> V {
    if k >= u64::from(t.elem.bits()) {
        return V::of(format!("({}){{0}}", t.name()), t, true);
    }
    V::of(format!("{} {sym} {k}", operand(s, t, n)), t, false)
}

/// A lane-wise operator.
///
/// # Arguments
///
/// * `sym` - The operator.
/// * `t` - The lanes' type.
/// * `a` - The left vector.
/// * `b` - The right.
/// * `n` - Name resolution.
fn binary(sym: &str, t: Vt, a: &Expr, b: &Expr, n: &Names<'_>) -> V {
    V::of(
        format!("{} {sym} {}", operand(a, t, n), operand(b, t, n)),
        t,
        false,
    )
}

/// A lane-wise comparison: every bit of a lane set where it holds.
///
/// # Arguments
///
/// * `sym` - The operator.
/// * `t` - The compared lanes' type.
/// * `a` - The left vector.
/// * `b` - The right.
/// * `n` - Name resolution.
fn compare(sym: &str, t: Vt, a: &Expr, b: &Expr, n: &Names<'_>) -> V {
    V::untyped(
        format!("{} {sym} {}", operand(a, t, n), operand(b, t, n)),
        t.whole,
        false,
    )
}

/// A bitwise operator, over the integer lanes an operand already has.
///
/// # Arguments
///
/// * `sym` - The operator.
/// * `a` - The left vector.
/// * `b` - The right.
/// * `n` - Name resolution.
fn bitwise(sym: &str, a: &Expr, b: &Expr, n: &Names<'_>) -> V {
    binary(sym, bitwise_ty(a, b, n), a, b, n)
}

/// The lanes a bitwise operation reads its operands as: an operand's own
/// integer lanes where one is a packed operation, so neither is cast
/// twice, else 64-bit lanes.
///
/// # Arguments
///
/// * `a` - The left vector.
/// * `b` - The right.
/// * `n` - Name resolution.
fn bitwise_ty(a: &Expr, b: &Expr, n: &Names<'_>) -> Vt {
    [a, b]
        .into_iter()
        .find_map(|e| match e {
            Expr::Call(f, args) => packed(f, args, n)?
                .ty
                .filter(|t| t.whole && !matches!(t.elem, Elem::F32 | Elem::F64)),
            _ => None,
        })
        .unwrap_or(Vt::whole(Elem::U64))
}

/// A two-operand instruction no operator writes, as the compiler's builtin
/// for it.
///
/// # Arguments
///
/// * `name` - The builtin.
/// * `elem` - The lanes it reads.
/// * `a` - The first operand.
/// * `b` - The second.
/// * `n` - Name resolution.
fn builtin(name: &str, elem: Elem, a: &Expr, b: &Expr, n: &Names<'_>) -> V {
    let t = Vt::whole(elem);
    V::untyped(
        format!("{name}({}, {})", operand(a, t, n), operand(b, t, n)),
        true,
        true,
    )
}

/// A packed value cast to a vector type, unless it has that type already.
///
/// # Arguments
///
/// * `v` - The value.
/// * `want` - The type.
fn cast_to(v: &V, want: Vt) -> String {
    if v.ty == Some(want) {
        return v.operand();
    }
    if v.whole == want.whole {
        return format!("({}){}", want.name(), v.operand());
    }
    let from = if v.whole { "uint128_t" } else { "uint64_t" };
    format!("({})({})({from}){}", want.name(), want.word(), v.operand())
}

/// An operand of a packed operation as a vector of the lanes it reads.
///
/// A register or a narrower load is the integer the text holds it in, and
/// the bits above a narrower value are zero, as `movd` and `movq` leave
/// them, so it is widened to the vector's size before the cast. A load of
/// the vector's whole size reads through a pointer to the vector type,
/// which [`declare`] gives an alignment of one: `movdqu` reads any
/// address, and a load of a 16-byte-aligned type would not.
///
/// # Arguments
///
/// * `e` - The operand.
/// * `want` - The lanes it is read as.
/// * `n` - Name resolution.
fn operand(e: &Expr, want: Vt, n: &Names<'_>) -> String {
    if let Expr::Call(f, args) = e
        && let Some(v) = packed(f, args, n)
    {
        return cast_to(&v, want);
    }
    let name = want.name();
    let word = want.word();
    let exact = |ty: Ty| (ty == Ty::U128) == want.whole && matches!(ty, Ty::U128 | Ty::U64);
    let inner = match e {
        Expr::Const(0) | Expr::FConst(0, _) => return format!("({name}){{0}}"),
        Expr::Const(v) | Expr::FConst(v, _) => format!("({word}){v:#x}"),
        Expr::Deref(a, ty) if exact(*ty) => {
            let at = match &**a {
                Expr::Var(_) => a.render(n),
                _ => format!("({})", a.render(n)),
            };
            return format!("*({name}*){at}");
        }
        Expr::Deref(a, Ty::F32 | Ty::F64) => {
            let bits = if matches!(e, Expr::Deref(_, Ty::F32)) {
                Ty::U32
            } else {
                Ty::U64
            };
            format!("({word}){}", Expr::Deref(a.clone(), bits).render(n))
        }
        Expr::Var(Key::Global(_, 128)) if want.whole => e.render(n),
        _ => match float_elem(e) {
            Some(elem) => {
                let lanes = Vt {
                    elem,
                    whole: want.whole,
                };
                return format!("({name})({}){{{}}}", lanes.name(), e.render(n));
            }
            None if matches!(
                e,
                Expr::Var(_) | Expr::Deref(..) | Expr::Call(..) | Expr::Cast(..)
            ) =>
            {
                format!("({word}){}", e.render(n))
            }
            None => format!("({word})({})", e.render(n)),
        },
    };
    format!("({name}){inner}")
}

/// The lane a scalar float expression is, `None` for an integer.
///
/// # Arguments
///
/// * `e` - The expression.
fn float_elem(e: &Expr) -> Option<Elem> {
    match e {
        Expr::Deref(_, Ty::F32) | Expr::Cast(_, Ty::F32) | Expr::FConst(_, Ty::F32) => {
            Some(Elem::F32)
        }
        Expr::Deref(_, Ty::F64) | Expr::Cast(_, Ty::F64) | Expr::FConst(_, Ty::F64) => {
            Some(Elem::F64)
        }
        Expr::Bin(op, l, r) if op.is_float() => float_elem(l).or_else(|| float_elem(r)),
        Expr::Un(_, inner) => float_elem(inner),
        Expr::Ternary(_, a, b) => float_elem(a).or_else(|| float_elem(b)),
        Expr::Const(_)
        | Expr::FConst(..)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Call(..)
        | Expr::Cast(..)
        | Expr::Sext(..)
        | Expr::Bin(..)
        | Expr::Cond(_)
        | Expr::Deref(..) => None,
    }
}

/// Puts what a finished text's vector code needs into its declarations:
/// the typedef of every vector type it names, and the value of every
/// 128-bit constant it reads from read-only data.
///
/// A declared global the image holds in a readable section that is
/// neither writable nor executable is a constant: its declaration becomes
/// `static const` with the bytes the file holds, so the text computes with
/// what the binary does.
///
/// # Arguments
///
/// * `text` - A finished decompilation.
/// * `program` - The image the constants are read from.
///
/// # Returns
///
/// The text with its vector types and constants declared, or unchanged.
pub(super) fn declare(text: &str, program: &Program) -> String {
    let body_names = |name: &str| {
        text.lines().filter(|l| !l.starts_with("//")).any(|l| {
            l.match_indices(name).any(|(at, _)| {
                let before = l.get(..at).and_then(|s| s.chars().next_back());
                let after = l.get(at + name.len()..).and_then(|s| s.chars().next());
                !before.is_some_and(is_word) && !after.is_some_and(is_word)
            })
        })
    };
    let typedefs: Vec<String> = Elem::ALL
        .into_iter()
        .flat_map(|elem| [Vt { elem, whole: true }, Vt { elem, whole: false }])
        .filter(|t| body_names(&t.name()))
        .map(|t| {
            format!(
                "typedef {} {} __attribute__((vector_size({}), aligned(1)));",
                t.elem.c(),
                t.name(),
                if t.whole { 16 } else { 8 }
            )
        })
        .collect();
    let mut changed = !typedefs.is_empty();
    let mut lines: Vec<String> = text
        .lines()
        .map(|l| match constant(l, program) {
            Some(c) => {
                changed = true;
                c
            }
            None => l.to_owned(),
        })
        .collect();
    if !changed {
        return text.to_owned();
    }
    let at = lines.iter().take_while(|l| l.starts_with("//")).count();
    lines.splice(at..at, typedefs);
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Whether a character continues an identifier.
///
/// # Arguments
///
/// * `c` - The character.
fn is_word(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// A 128-bit global's declaration with the constant the image holds, when
/// the line declares one in read-only data.
///
/// # Arguments
///
/// * `line` - One line of the text, `uint128_t g128_1090; // @ 0x1090`.
/// * `program` - The image.
fn constant(line: &str, program: &Program) -> Option<String> {
    let rest = line.strip_prefix("uint128_t g128_")?;
    let (hex, at) = rest.split_once("; // @ 0x")?;
    let addr = u64::from_str_radix(hex, 16).ok()?;
    if u64::from_str_radix(at, 16).ok()? != addr {
        return None;
    }
    let readonly = program
        .section_at(addr)
        .is_some_and(|s| s.readable && !s.writable && !s.executable);
    if !readonly {
        return None;
    }
    let bytes: [u8; 16] = program.read_va(addr, 16)?.try_into().ok()?;
    let v = u128::from_le_bytes(bytes);
    let hi = v >> 64;
    let lo = v & u128::from(u64::MAX);
    let value = if hi == 0 {
        format!("{lo:#x}")
    } else {
        format!("(uint128_t){hi:#x} << 64 | {lo:#x}")
    };
    Some(format!(
        "static const uint128_t g128_{hex} = {value}; // @ {addr:#x}"
    ))
}
