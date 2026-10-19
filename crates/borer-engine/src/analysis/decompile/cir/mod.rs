//! CIR: a function's pseudo-C as one typed C tree, printed once.
//!
//! The tree has one node kind per C construct borer prints: declarations
//! ([`Decl`]), the file-scope items of the unit around the function
//! ([`Item`]), statements ([`Stmt`]), expressions ([`Expr`]), C types
//! ([`CTy`]) and casts ([`ExprKind::Cast`]). Every statement and expression
//! keeps a provenance id ([`Prov`]) naming the instruction addresses it came
//! from, so a later check that finds a wrong line can say which code it
//! stands for.
//!
//! [`print`](print::print) is a plain recursive walk and the only place the tree becomes
//! text. [`build`](build::build) reads the structurer's text into the tree. The structurer
//! still writes text, so the tree is read from it once, at the boundary,
//! and printed back byte for byte; the text passes after it still run on
//! that text. The steps after this one build the tree directly (typed
//! lowering from the lifter's expressions), search over its choice points,
//! and turn the text passes into tree transforms.
//!
//! The invariants of a printable tree, and how each is held:
//!
//! - No computed `goto`: [`StmtKind::Goto`] names a [`Label`], so `goto
//!   *expr` cannot be built.
//! - Every name is a C identifier: [`Ident::new`] refuses anything else. A
//!   name the binary gave that is not one (a `Class::method`) is a
//!   [`Name::Sym`], which [`check`](check::check) reports.
//! - Every identifier is declared and every `goto` has its label:
//!   [`check`](check::check) lists the names and labels that break this.
//! - Every expression is C: text the builder could not read stays an
//!   [`ExprKind::Raw`] or [`StmtKind::Raw`], which [`check`](check::check) reports, a
//!   computed `goto` the structurer wrote among them.
//!
//! [`check`](check::check) reports, and the `// warn:` line of a
//! `decompile` answer says what it found; nothing enforces the invariants
//! yet.

mod build;
mod check;
mod print;

pub(super) use build::build;
pub(super) use check::{Holds, Violation, check};
pub(super) use print::{print, print_decls, print_items};

/// A provenance id: the index of a set of instruction addresses in
/// [`Body::prov`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Prov(u32);

impl Prov {
    /// The id of the code before the first block label: the values the
    /// function's entry state sets.
    pub(super) const ENTRY: Self = Self(0);
}

/// A C identifier: a letter or `_`, then letters, digits and `_`, and no
/// keyword.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Ident(String);

/// The C keywords [`Ident::new`] refuses.
const KEYWORDS: [&str; 32] = [
    "auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else",
    "enum", "extern", "float", "for", "goto", "if", "int", "long", "register", "return", "short",
    "signed", "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned", "void",
    "volatile", "while",
];

impl Ident {
    /// Builds an identifier from its text.
    ///
    /// # Arguments
    ///
    /// * `text` - The spelling.
    ///
    /// # Returns
    ///
    /// The identifier, or `None` when the text is not a C identifier or is
    /// a keyword.
    pub(super) fn new(text: &str) -> Option<Self> {
        let mut chars = text.chars();
        let first = chars.next()?;
        let ok = (first.is_ascii_alphabetic() || first == '_')
            && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
            && !KEYWORDS.contains(&text);
        ok.then(|| Self(text.to_owned()))
    }

    /// Returns the spelling.
    pub(super) fn as_str(&self) -> &str {
        &self.0
    }
}

/// A name an expression or declaration uses.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum Name {
    /// A C identifier.
    Ident(Ident),
    /// A symbol from the binary that is not a C identifier (`Class::method`,
    /// `operator new`), kept as spelled.
    Sym(String),
}

impl Name {
    /// Builds a name from its text: an identifier when it is one, else a
    /// symbol.
    ///
    /// # Arguments
    ///
    /// * `text` - The spelling.
    pub(super) fn of(text: &str) -> Self {
        Ident::new(text).map_or_else(|| Self::Sym(text.to_owned()), Self::Ident)
    }

    /// Returns the spelling.
    pub(super) fn as_str(&self) -> &str {
        match self {
            Self::Ident(i) => i.as_str(),
            Self::Sym(s) => s,
        }
    }
}

/// A block label: the start address of the block it marks, printed
/// `L_<va>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Label(pub(super) u64);

/// A C type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum CTy {
    /// `void`.
    Void,
    /// A fixed-width integer, spelled `int32_t`, `uint64_t` and so on.
    Int {
        /// Width in bits: 8, 16, 32, 64 or 128.
        bits: u8,
        /// Whether the type is signed.
        signed: bool,
    },
    /// `float` (32 bits) or `double` (64 bits).
    Float(u8),
    /// A pointer to the type.
    Ptr(Box<CTy>),
    /// A pointer to a function, `ret (*)(params)`; a function of no
    /// parameters lists `void`, as C spells it.
    FnPtr {
        /// The return type.
        ret: Box<CTy>,
        /// The parameter types, in order.
        params: Vec<CTy>,
    },
    /// A type known by its spelling only: a typedef, an aggregate, a vector
    /// typedef, a type the binary's debug information or the user stated.
    Named(String),
}

/// A literal as spelled.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Literal {
    /// What kind of literal it is.
    pub(super) kind: LitKind,
    /// The spelling, suffix and quotes included.
    pub(super) text: String,
}

/// The kinds of literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum LitKind {
    /// An integer: decimal, hex or octal, with any suffix.
    Int,
    /// A floating constant, decimal or hex.
    Float,
    /// A character constant.
    Char,
    /// A string literal, narrow or wide.
    Str,
}

/// A prefix unary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum UnOp {
    /// `-x`.
    Neg,
    /// `+x`.
    Plus,
    /// `~x`.
    BitNot,
    /// `!x`.
    Not,
    /// `*x`.
    Deref,
    /// `&x`.
    AddrOf,
    /// `++x`.
    PreInc,
    /// `--x`.
    PreDec,
}

/// A postfix unary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum PostOp {
    /// `x++`.
    Inc,
    /// `x--`.
    Dec,
}

/// A binary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum BinOp {
    /// `*`.
    Mul,
    /// `/`.
    Div,
    /// `%`.
    Rem,
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `<<`.
    Shl,
    /// `>>`.
    Shr,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `&`.
    BitAnd,
    /// `^`.
    BitXor,
    /// `|`.
    BitOr,
    /// `&&`.
    And,
    /// `||`.
    Or,
}

/// An expression with its C type and provenance.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Expr {
    /// What the expression is.
    pub(super) kind: ExprKind,
    /// The type C's rules give it, `None` until a typed lowering builds it.
    pub(super) ty: Option<CTy>,
    /// The code it came from.
    pub(super) prov: Prov,
}

/// The kinds of expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum ExprKind {
    /// A literal.
    Lit(Literal),
    /// A variable, parameter, function or global.
    Name(Name),
    /// A prefix operator applied.
    Unary(UnOp, Box<Expr>),
    /// A postfix operator applied.
    Postfix(PostOp, Box<Expr>),
    /// A binary operator applied.
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// `=`, or a compound assignment with its operator: place, then value.
    Assign(Option<BinOp>, Box<Expr>, Box<Expr>),
    /// `c ? a : b`.
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
    /// A conversion to the type.
    Cast(CTy, Box<Expr>),
    /// A call: the callee, then the arguments.
    Call(Box<Expr>, Vec<Expr>),
    /// `a[i]`.
    Index(Box<Expr>, Box<Expr>),
    /// `p->field` when `arrow`, else `s.field`.
    Member {
        /// The object or the pointer to it.
        base: Box<Expr>,
        /// The member.
        field: Name,
        /// Whether the base is a pointer.
        arrow: bool,
    },
    /// Parentheses the text writes.
    Paren(Box<Expr>),
    /// Text the builder could not read as C, kept as spelled.
    Raw(String),
}

/// A statement with its provenance.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Stmt {
    /// What the statement is.
    pub(super) kind: StmtKind,
    /// The code it came from.
    pub(super) prov: Prov,
}

/// The kinds of statement.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum StmtKind {
    /// An expression evaluated for its effect: `e;`.
    Expr(Expr),
    /// `return;` or `return e;`.
    Return(Option<Expr>),
    /// `goto L_<va>;`.
    Goto(Label),
    /// `L_<va>:`.
    Label(Label),
    /// `break;`.
    Break,
    /// `continue;`.
    Continue,
    /// `if (c) { ... }` with an optional `else`.
    If {
        /// The condition.
        cond: Expr,
        /// The statements run when it holds.
        then: Vec<Stmt>,
        /// The `else` arm.
        other: Option<Else>,
    },
    /// `if (c) s` written on one line: a single unbraced statement.
    Guard {
        /// The condition.
        cond: Expr,
        /// The statement run when it holds.
        then: Box<Stmt>,
    },
    /// `while (c) { ... }`.
    While {
        /// The condition, tested before each round.
        cond: Expr,
        /// The body.
        body: Vec<Stmt>,
    },
    /// `do { ... } while (c);`.
    DoWhile {
        /// The body.
        body: Vec<Stmt>,
        /// The condition, tested after each round.
        cond: Expr,
    },
    /// `for (init; cond; step) { ... }`.
    For {
        /// Run once before the loop.
        init: Expr,
        /// Tested before each round.
        cond: Expr,
        /// Run after each round.
        step: Expr,
        /// The body.
        body: Vec<Stmt>,
    },
    /// `switch (v) { ... }`.
    Switch {
        /// The value dispatched on.
        value: Expr,
        /// The arms, in order.
        arms: Vec<Arm>,
    },
    /// A braced block of its own: `{ ... }`.
    Block(Vec<Stmt>),
    /// A guarded region and its handlers: `try { ... } catch (T) { ... }`,
    /// or `__try { ... } __except (f) { ... }` and `__finally`.
    Try {
        /// Whether it is structured exception handling, written `__try`.
        seh: bool,
        /// The protected statements.
        body: Vec<Stmt>,
        /// The handlers in the order the runtime tries them; never empty.
        handlers: Vec<Handler>,
    },
    /// A whole-line comment: the text after `//`.
    Comment(String),
    /// An instruction the lifter did not model, `/* asm: text */`: the
    /// instruction's text.
    Asm(String),
    /// An empty line.
    Blank,
    /// A line the builder could not read as C, kept as spelled.
    Raw(String),
}

/// The `else` arm of an [`StmtKind::If`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum Else {
    /// `else { ... }`.
    Block(Vec<Stmt>),
    /// `else if (...)`: a statement that is itself an [`StmtKind::If`].
    If(Box<Stmt>),
}

/// One handler of an [`StmtKind::Try`]: what it handles and what runs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Handler {
    /// What it handles.
    pub(super) head: Head,
    /// The statements it runs.
    pub(super) body: Vec<Stmt>,
}

/// What a handler handles.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum Head {
    /// `catch (decl)`: the declaration as C++ writes it, `...` for all.
    Catch(String),
    /// `__except (filter)`.
    Except(Expr),
    /// `__finally`.
    Finally,
}

/// One arm of a `switch`: its labels and what runs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Arm {
    /// The labels, in order.
    pub(super) labels: Vec<CaseLabel>,
    /// What runs.
    pub(super) body: ArmBody,
    /// The code it came from.
    pub(super) prov: Prov,
}

/// A `switch` label.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum CaseLabel {
    /// `case v:`.
    Value(Expr),
    /// `default:`.
    Default,
}

/// What a `switch` arm runs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum ArmBody {
    /// One statement on the labels' line: `case 1: break;`.
    Inline(Box<Stmt>),
    /// A braced block: `case 1: { ... }`.
    Block(Vec<Stmt>),
}

/// A function body: its statements and the addresses each provenance id
/// stands for.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) struct Body {
    /// The statements, in order.
    pub(super) stmts: Vec<Stmt>,
    /// The instruction addresses each [`Prov`] stands for, indexed by it:
    /// a block's start address, or none for [`Prov::ENTRY`].
    pub(super) prov: Vec<Vec<u64>>,
}

/// A declaration of one or more names of one type, with an optional
/// trailing note.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Decl {
    /// The type every name has.
    pub(super) ty: CTy,
    /// The names declared, in order.
    pub(super) names: Vec<Name>,
    /// A comment written after the declaration (`@ 0x1000`).
    pub(super) note: Option<String>,
}

/// A function's prototype: its result type, its name and its parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Proto {
    /// The result type.
    pub(super) ret: CTy,
    /// The function's name.
    pub(super) name: Name,
    /// The parameters in order: each one's type and, when the prototype
    /// gives one, its name.
    pub(super) params: Vec<(CTy, Option<Name>)>,
    /// Whether it takes `...` past them.
    pub(super) variadic: bool,
}

/// A file-scope item of the translation unit around a function: what the
/// body uses that it does not declare itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Item {
    /// `extern T f(P);`: a function defined outside the unit.
    Extern(Proto),
    /// `static inline T f(P) { ... }`: a function the unit defines, its
    /// body printed on the prototype's line.
    Inline(Proto, Body),
    /// `static T (*const t[n])(P) = {f, g};`: a table of function
    /// designators.
    Table {
        /// The array's name.
        name: Name,
        /// The entries' one pointer type, [`CTy::FnPtr`]; `None` when
        /// their types differ, and the array holds `void *`.
        ty: Option<CTy>,
        /// The functions, in table order.
        entries: Vec<Name>,
    },
}

impl CTy {
    /// Reads a type from its spelling: the fixed-width integers, `float`,
    /// `double` and `void` by name, a trailing `*` as a pointer, anything
    /// else as [`CTy::Named`].
    ///
    /// # Arguments
    ///
    /// * `text` - The spelling, as a cast or a declaration writes it.
    ///
    /// # Returns
    ///
    /// The type, which [`print()`] spells back as `text` when `text` has no
    /// space before a `*` (`uint8_t*`).
    pub(super) fn parse(text: &str) -> Self {
        if let Some((ret, params)) = text.strip_suffix(')').and_then(|t| t.split_once(" (*)(")) {
            return Self::FnPtr {
                ret: Box::new(Self::parse(ret)),
                params: params.split(", ").map(Self::parse).collect(),
            };
        }
        if let Some(inner) = text.strip_suffix('*') {
            return Self::Ptr(Box::new(Self::parse(inner)));
        }
        let int = |rest: &str, signed| match rest {
            "8_t" => Some(Self::Int { bits: 8, signed }),
            "16_t" => Some(Self::Int { bits: 16, signed }),
            "32_t" => Some(Self::Int { bits: 32, signed }),
            "64_t" => Some(Self::Int { bits: 64, signed }),
            "128_t" => Some(Self::Int { bits: 128, signed }),
            _ => None,
        };
        let known = match text {
            "void" => Some(Self::Void),
            "float" => Some(Self::Float(32)),
            "double" => Some(Self::Float(64)),
            _ => text
                .strip_prefix("uint")
                .and_then(|r| int(r, false))
                .or_else(|| text.strip_prefix("int").and_then(|r| int(r, true))),
        };
        known.unwrap_or_else(|| Self::Named(text.to_owned()))
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests;
