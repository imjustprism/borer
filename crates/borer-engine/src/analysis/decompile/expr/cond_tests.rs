//! Conditions read back as C: a small evaluator of the C the renderer
//! writes for a condition, and the property that every rendering means
//! what the flags mean and its inversion is its negation.

use std::sync::Arc;

use crate::isa::x86::{ConditionCode, Register};

use super::{Cc, Cond, Expr, Flags, Key, Names, Op, Ty};
use crate::analysis::{Analysis, Overlay};
use crate::program::{Arch, Program, Section};

/// A C value: an integer with its width and signedness, or a double.
#[derive(Debug, Clone, Copy)]
enum V {
    /// An integer, held exactly, of this many bits, signed or not.
    I(i128, u8, bool),
    /// A floating-point value.
    F(f64),
}

impl V {
    /// The value wrapped to an integer type, as a C conversion does.
    ///
    /// # Arguments
    ///
    /// * `bits` - The type's width.
    /// * `signed` - The type is signed.
    fn to_int(self, bits: u8, signed: bool) -> V {
        let raw = match self {
            V::I(v, ..) => v,
            #[expect(clippy::cast_possible_truncation, reason = "C truncates toward zero")]
            V::F(f) => f as i128,
        };
        let m = (1i128 << bits) - 1;
        let mut v = raw & m;
        if signed && v >> (bits - 1) & 1 == 1 {
            v -= 1i128 << bits;
        }
        V::I(v, bits, signed)
    }

    /// The value as a double.
    #[expect(clippy::cast_precision_loss, reason = "the test values are exact")]
    fn to_f(self) -> f64 {
        match self {
            V::I(v, ..) => v as f64,
            V::F(f) => f,
        }
    }

    /// The value is nonzero, as a condition reads it.
    fn truth(self) -> bool {
        match self {
            V::I(v, ..) => v != 0,
            V::F(f) => f != 0.0,
        }
    }

    /// A C boolean result.
    ///
    /// # Arguments
    ///
    /// * `b` - The truth.
    fn of(b: bool) -> V {
        V::I(i128::from(b), 32, true)
    }
}

/// Promotes two operands to their common type (the usual arithmetic
/// conversions).
///
/// # Arguments
///
/// * `a` - Left operand.
/// * `b` - Right operand.
fn common(a: V, b: V) -> (V, V) {
    match (promote(a), promote(b)) {
        (x @ V::I(_, xb, xs), y @ V::I(_, yb, ys)) => {
            let (bits, signed) = match xb.cmp(&yb) {
                std::cmp::Ordering::Equal => (xb, xs && ys),
                std::cmp::Ordering::Greater => (xb, xs),
                std::cmp::Ordering::Less => (yb, ys),
            };
            (x.to_int(bits, signed), y.to_int(bits, signed))
        }
        (x, y) => (V::F(x.to_f()), V::F(y.to_f())),
    }
}

/// Promotes an integer narrower than `int` to `int`.
///
/// # Arguments
///
/// * `v` - The value.
fn promote(v: V) -> V {
    match v {
        V::I(_, bits, _) if bits < 32 => v.to_int(32, true),
        other => other,
    }
}

/// A recursive-descent reader of the C a condition renders as.
struct P<'s> {
    /// The text.
    s: &'s [u8],
    /// The read position.
    i: usize,
    /// The two integer variables' values.
    ints: (u32, u32),
    /// The two float variables' values.
    floats: (f64, f64),
}

impl P<'_> {
    /// Skips blanks and comments.
    fn ws(&mut self) {
        loop {
            while self.s.get(self.i).is_some_and(u8::is_ascii_whitespace) {
                self.i += 1;
            }
            if self.s[self.i..].starts_with(b"/*") {
                let end = self.s[self.i..]
                    .windows(2)
                    .position(|w| w == b"*/")
                    .unwrap_or(0);
                self.i += end + 2;
            } else {
                return;
            }
        }
    }

    /// Consumes `tok` when it comes next and is not the start of a longer
    /// operator.
    ///
    /// # Arguments
    ///
    /// * `tok` - The operator.
    fn eat(&mut self, tok: &str) -> bool {
        self.ws();
        let t = tok.as_bytes();
        if !self.s[self.i..].starts_with(t) {
            return false;
        }
        let next = self.s.get(self.i + t.len()).copied();
        let longer = match tok {
            "&" => next == Some(b'&'),
            "|" => next == Some(b'|'),
            "<" | ">" => matches!(next, Some(b'=' | b'<' | b'>')),
            "!" => next == Some(b'='),
            _ => false,
        };
        if longer {
            return false;
        }
        self.i += t.len();
        true
    }

    /// Reads a whole expression, the conditional operator included.
    fn expr(&mut self) -> V {
        let c = self.binary(0);
        if self.eat("?") {
            let a = self.expr();
            assert!(self.eat(":"));
            let b = self.expr();
            return if c.truth() { a } else { b };
        }
        c
    }

    /// Reads binary operators of precedence `level` and up.
    ///
    /// # Arguments
    ///
    /// * `level` - Index into the precedence table.
    fn binary(&mut self, level: usize) -> V {
        /// The binary operators by precedence, loosest first.
        const LEVELS: [&[&str]; 10] = [
            &["||"],
            &["&&"],
            &["|"],
            &["^"],
            &["&"],
            &["==", "!="],
            &["<=", ">=", "<", ">"],
            &["<<", ">>"],
            &["+", "-"],
            &["*", "/", "%"],
        ];
        let Some(ops) = LEVELS.get(level) else {
            return self.unary();
        };
        let mut l = self.binary(level + 1);
        'outer: loop {
            for op in *ops {
                if self.eat(op) {
                    let r = self.binary(level + 1);
                    l = apply(op, l, r);
                    continue 'outer;
                }
            }
            return l;
        }
    }

    /// Reads a prefix operator, a cast, or a primary.
    fn unary(&mut self) -> V {
        self.ws();
        if self.eat("!") {
            return V::of(!self.unary().truth());
        }
        if self.eat("-") {
            return match promote(self.unary()) {
                V::F(f) => V::F(-f),
                V::I(x, bits, signed) => V::I(-x, bits, signed).to_int(bits, signed),
            };
        }
        if self.eat("~") {
            return match promote(self.unary()) {
                V::F(f) => V::F(f),
                V::I(x, bits, signed) => V::I(!x, bits, signed).to_int(bits, signed),
            };
        }
        let save = self.i;
        if self.eat("(") {
            let start = self.i;
            while self
                .s
                .get(self.i)
                .is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_')
            {
                self.i += 1;
            }
            let name = std::str::from_utf8(&self.s[start..self.i]).unwrap_or("");
            let ty = match name {
                "int8_t" => Some((8, true)),
                "int16_t" => Some((16, true)),
                "int32_t" => Some((32, true)),
                "int64_t" => Some((64, true)),
                "uint8_t" => Some((8, false)),
                "uint16_t" => Some((16, false)),
                "uint32_t" => Some((32, false)),
                "uint64_t" => Some((64, false)),
                "float" | "double" => Some((0, true)),
                _ => None,
            };
            if let Some((bits, signed)) = ty
                && self.eat(")")
            {
                let v = self.unary();
                return if bits == 0 {
                    V::F(v.to_f())
                } else {
                    v.to_int(bits, signed)
                };
            }
            self.i = save;
            assert!(self.eat("("));
            let v = self.expr();
            assert!(self.eat(")"), "unclosed at {}", self.i);
            return v;
        }
        self.primary()
    }

    /// Reads a literal, a variable or a call.
    fn primary(&mut self) -> V {
        self.ws();
        let start = self.i;
        while self
            .s
            .get(self.i)
            .is_some_and(|c| c.is_ascii_alphanumeric() || matches!(c, b'_' | b'.'))
        {
            self.i += 1;
        }
        let word = std::str::from_utf8(&self.s[start..self.i]).unwrap_or("");
        assert!(!word.is_empty(), "nothing to read at {start}");
        if word.starts_with(|c: char| c.is_ascii_digit()) {
            if let Some(h) = word.strip_prefix("0x") {
                let v = i128::from_str_radix(h, 16).unwrap_or(0);
                let (bits, signed) = if v <= i128::from(i32::MAX) {
                    (32, true)
                } else if v <= i128::from(u32::MAX) {
                    (32, false)
                } else {
                    (64, v <= i128::from(i64::MAX))
                };
                return V::I(v, bits, signed);
            }
            if word.contains('.') {
                return V::F(word.trim_end_matches('f').parse().unwrap_or(0.0));
            }
            let v: i128 = word.parse().unwrap_or(0);
            return V::I(v, if v <= i128::from(i32::MAX) { 32 } else { 64 }, true);
        }
        match word {
            "rax" => return V::I(i128::from(self.ints.0), 32, false),
            "rcx" => return V::I(i128::from(self.ints.1), 32, false),
            "xmm0" => return V::F(self.floats.0),
            "xmm1" => return V::F(self.floats.1),
            "NAN" => return V::F(f64::NAN),
            "INFINITY" => return V::F(f64::INFINITY),
            "FLAGS_UNKNOWN" => return V::of(opaque(word, &[])),
            _ => {}
        }
        assert!(self.eat("("), "unknown name {word}");
        let mut args = Vec::new();
        if !self.eat(")") {
            loop {
                args.push(self.expr());
                if self.eat(")") {
                    break;
                }
                assert!(self.eat(","), "bad call at {}", self.i);
            }
        }
        call(word, &args)
    }
}

/// A stable pseudo-random truth for a test the renderer cannot decide,
/// the same for the same call.
///
/// # Arguments
///
/// * `name` - The opaque test's name.
/// * `args` - Its arguments.
fn opaque(name: &str, args: &[V]) -> bool {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in name.bytes() {
        h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
    }
    for a in args {
        let V::I(v, ..) = a.to_int(64, false) else {
            continue;
        };
        h = (h ^ u64::try_from(v).unwrap_or(0)).wrapping_mul(0x0100_0000_01b3);
    }
    h >> 63 == 1
}

/// Evaluates one of the calls the renderer writes in a condition.
///
/// # Arguments
///
/// * `name` - The function.
/// * `args` - Its evaluated arguments.
fn call(name: &str, args: &[V]) -> V {
    let f = |i: usize| args.get(i).map_or(0.0, |a| a.to_f());
    let u = |i: usize, bits: u8| match args.get(i).map(|a| a.to_int(bits, false)) {
        Some(V::I(v, ..)) => v,
        _ => 0,
    };
    let s = |i: usize, bits: u8| match args.get(i).map(|a| a.to_int(bits, true)) {
        Some(V::I(v, ..)) => v,
        _ => 0,
    };
    let width = |prefix: &str| name.strip_prefix(prefix).and_then(|w| w.parse::<u8>().ok());
    let signed_out = |t: i128, w: u8| t >= 1i128 << (w - 1) || t < -(1i128 << (w - 1));
    if let Some(w) = width("uaddo") {
        return V::of(u(0, w) + u(1, w) >= 1i128 << w);
    }
    if let Some(w) = width("saddo") {
        return V::of(signed_out(s(0, w) + s(1, w), w));
    }
    if let Some(w) = width("ssubo") {
        return V::of(signed_out(s(0, w) - s(1, w), w));
    }
    if name.starts_with("flags_") {
        return V::of(opaque(name, args));
    }
    V::of(match name {
        "isgreater" => f(0) > f(1),
        "isgreaterequal" => f(0) >= f(1),
        "isless" => f(0) < f(1),
        "islessequal" => f(0) <= f(1),
        "isunordered" => f(0).is_nan() || f(1).is_nan(),
        "parity8" => u(0, 8).count_ones().is_multiple_of(2),
        _ => panic!("unknown call {name}"),
    })
}

/// Applies a binary operator under C's conversions.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `l` - Left operand.
/// * `r` - Right operand.
fn apply(op: &str, l: V, r: V) -> V {
    if op == "&&" {
        return V::of(l.truth() && r.truth());
    }
    if op == "||" {
        return V::of(l.truth() || r.truth());
    }
    let (l, r) = common(l, r);
    match (l, r) {
        (V::F(a), V::F(b)) => match op {
            "==" => V::of(a == b),
            "!=" => V::of(a != b),
            "<" => V::of(a < b),
            "<=" => V::of(a <= b),
            ">" => V::of(a > b),
            ">=" => V::of(a >= b),
            "+" => V::F(a + b),
            "-" => V::F(a - b),
            "*" => V::F(a * b),
            _ => panic!("float {op}"),
        },
        (V::I(a, bits, signed), V::I(b, ..)) => {
            let v = match op {
                "==" => return V::of(a == b),
                "!=" => return V::of(a != b),
                "<" => return V::of(a < b),
                "<=" => return V::of(a <= b),
                ">" => return V::of(a > b),
                ">=" => return V::of(a >= b),
                "+" => a + b,
                "-" => a - b,
                "*" => a * b,
                "&" => a & b,
                "|" => a | b,
                "^" => a ^ b,
                "<<" => a << (b & 63),
                ">>" => a >> (b & 63),
                _ => panic!("int {op}"),
            };
            V::I(v, bits, signed).to_int(bits, signed)
        }
        _ => panic!("mixed operands"),
    }
}

/// Evaluates a rendered condition.
///
/// # Arguments
///
/// * `text` - The condition.
/// * `ints` - `rax` and `rcx`.
/// * `floats` - `xmm0` and `xmm1`.
fn eval(text: &str, ints: (u32, u32), floats: (f64, f64)) -> bool {
    let mut p = P {
        s: text.as_bytes(),
        i: 0,
        ints,
        floats,
    };
    let v = p.expr();
    p.ws();
    assert_eq!(p.i, text.len(), "unread text in {text:?}");
    v.truth()
}

/// The flags x86 leaves, as a condition reads them.
#[derive(Debug, Clone, Copy, Default)]
struct Machine {
    /// Carry.
    cf: Option<bool>,
    /// Zero.
    zf: Option<bool>,
    /// Sign.
    sf: Option<bool>,
    /// Overflow.
    of: Option<bool>,
    /// Parity.
    pf: Option<bool>,
}

impl Machine {
    /// The flags an integer result sets, carry and overflow given.
    ///
    /// # Arguments
    ///
    /// * `r` - The 32-bit result.
    /// * `cf` - The carry, when defined.
    /// * `of` - The overflow, when defined.
    fn of_result(r: u32, cf: Option<bool>, of: Option<bool>) -> Machine {
        Machine {
            cf,
            zf: Some(r == 0),
            sf: Some(r >> 31 == 1),
            of,
            pf: Some((r & 0xff).count_ones().is_multiple_of(2)),
        }
    }

    /// The truth of a condition code over these flags, when every flag
    /// it reads is defined (a condition reading an undefined flag is
    /// undecided even where the defined one would settle it).
    ///
    /// # Arguments
    ///
    /// * `cc` - The condition code.
    fn holds(self, cc: ConditionCode) -> Option<bool> {
        use ConditionCode as C;
        let (cf, zf) = (self.cf, self.zf);
        let lt = || Some(self.sf? != self.of?);
        Some(match cc {
            C::o => self.of?,
            C::no => !self.of?,
            C::b => cf?,
            C::ae => !cf?,
            C::e => zf?,
            C::ne => !zf?,
            C::be => {
                let (c, z) = (cf?, zf?);
                c || z
            }
            C::a => {
                let (c, z) = (cf?, zf?);
                !c && !z
            }
            C::s => self.sf?,
            C::ns => !self.sf?,
            C::p => self.pf?,
            C::np => !self.pf?,
            C::l => lt()?,
            C::ge => !lt()?,
            C::le => {
                let (z, l) = (zf?, lt()?);
                z || l
            }
            C::g => {
                let (z, l) = (zf?, lt()?);
                !z && !l
            }
            C::None => return None,
        })
    }
}

/// Every condition code, `None` included.
const CCS: [ConditionCode; 17] = [
    ConditionCode::None,
    ConditionCode::o,
    ConditionCode::no,
    ConditionCode::b,
    ConditionCode::ae,
    ConditionCode::e,
    ConditionCode::ne,
    ConditionCode::be,
    ConditionCode::a,
    ConditionCode::s,
    ConditionCode::ns,
    ConditionCode::p,
    ConditionCode::np,
    ConditionCode::l,
    ConditionCode::ge,
    ConditionCode::le,
    ConditionCode::g,
];

/// What a flag shape sets on given values of its two variables.
type Sets = Box<dyn Fn(u32, u32) -> Machine>;

/// Boxes a flag model.
///
/// # Arguments
///
/// * `f` - The model.
fn sets(f: impl Fn(u32, u32) -> Machine + 'static) -> Sets {
    Box::new(f)
}

/// The flags `sub a, b` sets.
///
/// # Arguments
///
/// * `a` - The minuend.
/// * `b` - The subtrahend.
fn sub(a: u32, b: u32) -> Machine {
    let of = a.cast_signed().overflowing_sub(b.cast_signed()).1;
    Machine::of_result(a.wrapping_sub(b), Some(a < b), Some(of))
}

/// The flags `add a, b` sets.
///
/// # Arguments
///
/// * `a` - One addend.
/// * `b` - The other.
fn add(a: u32, b: u32) -> Machine {
    let of = a.cast_signed().overflowing_add(b.cast_signed()).1;
    Machine::of_result(a.wrapping_add(b), Some(a.overflowing_add(b).1), Some(of))
}

/// The flag shapes the lifter builds, over two 32-bit variables, with
/// what each sets on given values.
fn shapes() -> Vec<(Flags, Sets)> {
    let x = Expr::Var(Key::Reg(Register::RAX));
    let y = Expr::Var(Key::Reg(Register::RCX));
    let low_bit = Expr::Bin(Op::And, Box::new(y.clone()), Box::new(Expr::Const(1)));
    let truth = |cc: ConditionCode, flags: Flags| Expr::Cond(Box::new(Cond { cc: Cc(cc), flags }));
    let below = truth(ConditionCode::b, Flags::Cmp(x.clone(), y.clone(), 32));
    let five = truth(ConditionCode::e, Flags::Cmp(x.clone(), Expr::Const(5), 32));
    let none = truth(ConditionCode::e, Flags::Test(y.clone(), y.clone(), 32));
    let either = Expr::Bin(Op::Or, Box::new(below.clone()), Box::new(five.clone()));
    let both = Expr::Bin(
        Op::And,
        Box::new(below),
        Box::new(Expr::Bin(Op::Or, Box::new(five), Box::new(none))),
    );
    let bits = |a: u32, b: u32| (u32::from(a < b), u32::from(a == 5), u32::from(b == 0));
    vec![
        (
            Flags::Result(either.clone(), 32),
            sets(move |a, b| {
                let (l, f, _) = bits(a, b);
                Machine::of_result(l | f, None, None)
            }),
        ),
        (
            Flags::Test(both.clone(), both, 32),
            sets(move |a, b| {
                let (l, f, z) = bits(a, b);
                Machine::of_result(l & (f | z), Some(false), Some(false))
            }),
        ),
        (
            Flags::Truth(either, Cc(ConditionCode::ne)),
            sets(move |a, b| {
                let (l, f, _) = bits(a, b);
                Machine {
                    zf: Some((l | f) == 0),
                    ..Machine::default()
                }
            }),
        ),
        (Flags::Cmp(x.clone(), y.clone(), 32), sets(sub)),
        (
            Flags::Cmp(x.clone(), Expr::Const(5), 32),
            sets(|a, _| sub(a, 5)),
        ),
        (
            Flags::Cmp(x.clone(), Expr::Const(0x8000_0000), 32),
            sets(|a, _| sub(a, 0x8000_0000)),
        ),
        (
            Flags::Test(x.clone(), y.clone(), 32),
            sets(|a, b| Machine::of_result(a & b, Some(false), Some(false))),
        ),
        (
            Flags::Test(x.clone(), x.clone(), 32),
            sets(|a, _| Machine::of_result(a, Some(false), Some(false))),
        ),
        (Flags::Add(x.clone(), y, 32), sets(add)),
        (
            Flags::Add(x.clone(), Expr::Const(1), 32),
            sets(|a, _| add(a, 1)),
        ),
        (
            Flags::Add(x.clone(), Expr::Const(0xffff_ffff), 32),
            sets(|a, _| add(a, 0xffff_ffff)),
        ),
        (Flags::Add(x.clone(), x.clone(), 32), sets(|a, _| add(a, a))),
        (
            Flags::Result(x.clone(), 32),
            sets(|a, _| Machine::of_result(a, None, None)),
        ),
        (
            Flags::Carry(x.clone()),
            sets(|a, _| Machine {
                cf: Some(a != 0),
                of: Some(a != 0),
                ..Machine::default()
            }),
        ),
        (
            Flags::Shift(x.clone(), 32, low_bit),
            sets(|a, b| Machine::of_result(a, Some(b & 1 == 1), None)),
        ),
        (
            Flags::Truth(x, Cc(ConditionCode::b)),
            sets(|a, _| Machine {
                cf: Some(a != 0),
                ..Machine::default()
            }),
        ),
        (Flags::Unknown, sets(|_, _| Machine::default())),
    ]
}

/// Builds the names a rendering needs, over an empty image.
///
/// # Arguments
///
/// * `p` - The image.
/// * `a` - Its analysis.
/// * `o` - The overlay.
fn names<'a>(p: &'a Program, a: &'a Analysis, o: &'a Overlay) -> Names<'a> {
    Names {
        program: p,
        analysis: a,
        overlay: o,
        this_param: false,
        result_param: None,
        own_name: Arc::from("f"),
        debug_params: Arc::from(Vec::new()),
        debug_locals: Arc::default(),
        first_stack: 8,
        stack_params: 0,
        reg_params: 0,
        word: 8,
        slot_types: Arc::default(),
        global_types: Arc::default(),
    }
}

/// Every condition renders as C that means what the flags mean, and
/// its inversion renders as that C's negation.
///
/// Each flag shape the lifter builds is paired with each condition
/// code and read back on 32-bit values around the overflow edges and
/// on floats including NaN. A condition the flags decide must evaluate
/// to the processor's outcome (a sign test after `dec` misses it at
/// `INT_MIN`, a flipped float compare at NaN); one they do not decide
/// renders as an opaque call whose inversion is the same call under
/// `!`. A lone float `e` is equality or unordered, and `ne` is that
/// test inverted: C's `==` and `!=` hold on NaN the other way from the
/// zero flag. With the parity test before them, as compilers emit
/// them, the pair folds to exactly C's comparison, so only their
/// inversion is checked here.
#[test]
fn a_condition_means_its_flags_and_inverts_to_its_negation() {
    let mut bytes = vec![0u8; 0x2000];
    bytes[0] = 0xc3;
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0x40_0000,
        Some(0x40_1000),
        vec![
            Section::mapped(".text", 0x40_1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x40_2000, 0x1000, 0x1000, false, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let n = names(&p, &a, &o);
    let ints: [u32; 10] = [
        0,
        1,
        2,
        5,
        0x7f,
        0x80,
        0x7fff_ffff,
        0x8000_0000,
        0x8000_0001,
        u32::MAX,
    ];
    for (flags, machine) in shapes() {
        for cc in CCS {
            let cond = Cond {
                cc: Cc(cc),
                flags: flags.clone(),
            };
            let (normal, inverted) = (cond.render(&n, false), cond.render(&n, true));
            for &x in &ints {
                for &y in &ints {
                    let yes = eval(&normal, (x, y), (0.0, 0.0));
                    let no = eval(&inverted, (x, y), (0.0, 0.0));
                    assert_ne!(yes, no, "{cc:?} {flags:?}: {normal} vs {inverted}");
                    match machine(x, y).holds(cc) {
                        Some(want) => assert_eq!(yes, want, "{cc:?} {flags:?}: {normal}"),
                        None => assert!(normal.starts_with("flags_") || normal == "FLAGS_UNKNOWN"),
                    }
                }
            }
        }
    }
    let floats = [f64::NAN, -1.0, 0.0, 1.0, f64::INFINITY, f64::NEG_INFINITY];
    let fx = Expr::Var(Key::Reg(Register::XMM0));
    for flags in [
        Flags::Cmp(fx.clone(), Expr::Var(Key::Reg(Register::XMM1)), 32),
        Flags::Cmp(fx, Expr::FConst(1.0f32.to_bits().into(), Ty::F32), 32),
    ] {
        for cc in CCS {
            let cond = Cond {
                cc: Cc(cc),
                flags: flags.clone(),
            };
            let normal = cond.render(&n, false);
            let inverted = cond.render(&n, true);
            for &a in &floats {
                for &b in &floats {
                    let b = if matches!(flags, Flags::Cmp(_, Expr::FConst(..), _)) {
                        1.0
                    } else {
                        b
                    };
                    let yes = eval(&normal, (0, 0), (a, b));
                    let no = eval(&inverted, (0, 0), (a, b));
                    assert_ne!(yes, no, "{cc:?}: {normal} vs {inverted} at {a}, {b}");
                    let unordered = a.is_nan() || b.is_nan();
                    let m = Machine {
                        cf: Some(unordered || a < b),
                        zf: Some(unordered || a == b),
                        pf: Some(unordered),
                        ..Machine::default()
                    };
                    let decided = matches!(
                        cc,
                        ConditionCode::a
                            | ConditionCode::ae
                            | ConditionCode::b
                            | ConditionCode::be
                            | ConditionCode::p
                            | ConditionCode::np
                    );
                    if decided && let Some(want) = m.holds(cc) {
                        assert_eq!(yes, want, "{cc:?}: {normal} at {a}, {b}");
                    }
                }
            }
        }
    }
}

/// A guard chain a text pass negates reads as each operand negated
/// under the other operator, and means the chain's negation.
///
/// Nested chains keep their parentheses, a negated operand loses its
/// `!`, and a float relation, a comparison macro in the text, negates
/// as a whole call.
#[test]
fn a_negated_chain_negates_each_operand() {
    use super::super::rewrite::invert_condition;
    let ints: [u32; 6] = [0, 1, 2, 5, 9, 0xffff_ffff];
    for chain in [
        "rax < rcx && rax != 5",
        "rax == 0 || rcx > 3 || rax >= rcx",
        "(rax == 0 || rcx > 3) && rax < 7",
        "rax != 1 && (rcx == 2 || (rax > rcx && rcx != 0))",
        "!(rax < rcx) || rcx == 9",
    ] {
        let negated = invert_condition(chain);
        assert!(!negated.starts_with("!("), "{chain}: {negated}");
        for &x in &ints {
            for &y in &ints {
                assert_ne!(
                    eval(chain, (x, y), (0.0, 0.0)),
                    eval(&negated, (x, y), (0.0, 0.0)),
                    "{chain} vs {negated} at {x:#x}, {y:#x}"
                );
            }
        }
    }
    assert_eq!(
        invert_condition("rax < rcx && rax != 5"),
        "rax >= rcx || rax == 5"
    );
    assert_eq!(
        invert_condition("isless(xmm0, xmm1) && rax == 0"),
        "!isless(xmm0, xmm1) || rax != 0"
    );
    for whole in [
        "a2 ? a3 < a4 : a5",
        "a1 ? a2 && a3 : a4",
        "var1 = f(a1)",
        "var1 += 1",
    ] {
        assert_eq!(invert_condition(whole), format!("!({whole})"));
    }
    assert_eq!(invert_condition("a1 == '?'"), "a1 != '?'");
    assert_eq!(invert_condition("'\"' == a1"), "'\"' != a1");
}

/// A float compare means its predicate, NaN order included, through
/// every way the text reaches C.
///
/// Each of the sixteen predicates, and each code over a float compare's
/// flags, renders as the predicate and inverts to its negation, both by
/// the renderer and by the text pass that inverts a written condition,
/// and still means the same once the comparison macros are spelled as
/// operators.
#[test]
fn a_float_predicate_survives_inversion_and_spelling() {
    use super::super::fcmp::FPred;
    use super::super::rewrite::{invert_condition, spell_float_relations};
    let mut bytes = vec![0u8; 0x2000];
    bytes[0] = 0xc3;
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0x40_0000,
        Some(0x40_1000),
        vec![Section::mapped(".text", 0x40_1000, 0, 0x1000, false, true)],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let n = names(&p, &a, &o);
    let (x, y) = (
        Expr::Var(Key::Reg(Register::XMM0)),
        Expr::Var(Key::Reg(Register::XMM1)),
    );
    let mut conds: Vec<Cond> = FPred::ALL
        .iter()
        .map(|&pred| Cond {
            cc: Cc(ConditionCode::ne),
            flags: Flags::FCmp(pred, x.clone(), y.clone(), 64),
        })
        .collect();
    conds.extend(CCS.iter().map(|&cc| Cond {
        cc: Cc(cc),
        flags: Flags::Float(x.clone(), y.clone(), 64),
    }));
    let floats = [f64::NAN, -1.0, 0.0, 1.0, f64::INFINITY];
    for cond in conds {
        let Some((pred, ..)) = cond.fcmp() else {
            continue;
        };
        let normal = cond.render(&n, false);
        let inverted = cond.render(&n, true);
        let flipped = invert_condition(&normal);
        let shown = |t: &str| {
            spell_float_relations(&format!("if ({t}) {{"))
                .trim()
                .to_owned()
        };
        for &fa in &floats {
            for &fb in &floats {
                let want = pred.holds(fa, fb);
                let at = |t: &str| eval(t, (0, 0), (fa, fb));
                let spelled = |t: &str| {
                    let line = shown(t);
                    let inner = line
                        .strip_prefix("if (")
                        .and_then(|l| l.strip_suffix(") {"))
                        .unwrap_or_default()
                        .to_owned();
                    at(&inner)
                };
                assert_eq!(at(&normal), want, "{pred:?}: {normal} at {fa}, {fb}");
                assert_eq!(at(&inverted), !want, "{pred:?}: {inverted} at {fa}, {fb}");
                assert_eq!(at(&flipped), !want, "{pred:?}: {flipped} at {fa}, {fb}");
                assert_eq!(
                    spelled(&normal),
                    want,
                    "{pred:?}: {} at {fa}, {fb}",
                    shown(&normal)
                );
                assert_eq!(
                    spelled(&flipped),
                    !want,
                    "{pred:?}: {} at {fa}, {fb}",
                    shown(&flipped)
                );
            }
        }
    }
}
