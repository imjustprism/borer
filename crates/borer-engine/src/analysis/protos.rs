//! Prototypes and variables an agent states: what a function takes and
//! returns, and the names and types of its parameters and stack locals.
//!
//! Debug information (PDB, DWARF) states these for the functions it
//! covers; a stripped binary states none, and the agent reading it learns
//! them. A stated prototype is held in the overlay
//! ([`Overlay::prototypes`](super::Overlay::prototypes)) and feeds the
//! decompiler where debug information would, ahead of it: the function's
//! signature, its parameters' names and types in the body, the fields read
//! through a typed pointer parameter, and the arity and the result every
//! call to it shows. A stated variable
//! ([`Overlay::vars`](super::Overlay::vars)) names one parameter or stack
//! slot, and types it.
//!
//! A prototype is stated as C (`int __fastcall f(Player *p, uint32_t n)`),
//! parsed here at the boundary into [`Proto`]: a return type, a calling
//! convention, the parameters as type and name, and `...`. Each type is a
//! [`CType`], its base words and the pointers over them, resolved against
//! the overlay's user types and the type library's C type words where the
//! machine's view of it is asked for. Function-pointer parameters and
//! register-level conventions (`__usercall`, `@<reg>`) are refused with a
//! message naming them.

use std::collections::BTreeMap;

use super::typelib::{self, Pass};
use super::utypes::{self, TypeExpr, UserStruct, UserType};
use crate::program::BinaryFormat;

/// Most parameters one stated prototype lists.
pub const PARAMS_MAX: usize = 32;

/// Most prototypes one overlay holds.
pub const PROTOTYPES_MAX: usize = 1 << 16;

/// Most variables one overlay names, across its functions.
pub const VARS_MAX: usize = 1 << 16;

/// A C type as an agent stated it: the words before the pointers, and the
/// pointers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CType {
    /// The base words as written, qualifiers kept and spaces single
    /// (`const char`, `unsigned int`, `Player`).
    pub base: String,
    /// The pointers over the base.
    pub stars: usize,
}

impl CType {
    /// Parses a type with no name in it: `const char *`, `Player*`, `u32`.
    ///
    /// # Arguments
    ///
    /// * `text` - The type as written.
    ///
    /// # Errors
    ///
    /// When the text holds no word, a word that is not an identifier, a
    /// star before every word, or more pointers than
    /// [`utypes::PTR_DEPTH_MAX`].
    pub fn parse(text: &str) -> anyhow::Result<Self> {
        let toks = tokens(text)?;
        type_of(&toks, text)
    }

    /// Spells the type: `const char *`, `int`, `Player **`.
    #[must_use]
    pub fn spell(&self) -> String {
        if self.stars == 0 {
            self.base.clone()
        } else {
            format!("{} {}", self.base, "*".repeat(self.stars))
        }
    }

    /// The base word that names a user type, qualifiers and tags dropped,
    /// when there is one word left.
    fn user_name(&self) -> Option<&str> {
        let mut words = self
            .base
            .split(' ')
            .filter(|w| !matches!(*w, "const" | "volatile" | "struct" | "union" | "enum"));
        let word = words.next()?;
        words.next().is_none().then_some(word)
    }

    /// The type in the user-type language, when the base names a user type
    /// the overlay defines: what field and enum lookups take.
    ///
    /// # Arguments
    ///
    /// * `types` - The overlay's user types.
    fn as_user(&self, types: &BTreeMap<String, UserType>) -> Option<TypeExpr> {
        let name = self.user_name()?;
        types.get(name)?;
        Some(
            (0..self.stars).fold(TypeExpr::Named(name.to_owned()), |t, _| {
                TypeExpr::Ptr(Box::new(t))
            }),
        )
    }

    /// Reads what the machine passes the type as.
    ///
    /// A user type the overlay defines is followed: an enum passes as an
    /// integer of its width, a typedef as what it names. A struct passed
    /// by value, and a name neither the overlay nor the type library knows,
    /// pass as nothing known, which reads as a word in its register.
    ///
    /// # Arguments
    ///
    /// * `types` - The overlay's user types.
    /// * `word` - The machine word in bits (32 or 64).
    /// * `format` - The binary's format.
    ///
    /// # Returns
    ///
    /// The pass, or `None` when nothing says how the type passes.
    #[must_use]
    pub fn pass(
        &self,
        types: &BTreeMap<String, UserType>,
        word: u8,
        format: BinaryFormat,
    ) -> Option<Pass> {
        if self.stars > 0 {
            return Some(Pass::Pointer);
        }
        match self.as_user(types) {
            Some(ty) => user_pass(types, &ty),
            None => typelib::pass_of(&self.base, word, format),
        }
    }

    /// The user struct the type points at, through a pointer or a typedef
    /// of one: what the fields read through a value of the type are named
    /// by.
    ///
    /// # Arguments
    ///
    /// * `types` - The overlay's user types.
    #[must_use]
    pub fn pointee<'t>(&self, types: &'t BTreeMap<String, UserType>) -> Option<&'t UserStruct> {
        let ty = self.as_user(types)?;
        let pointer = matches!(ty, TypeExpr::Ptr(_))
            || matches!(&ty, TypeExpr::Named(n) if matches!(types.get(n), Some(UserType::Alias(TypeExpr::Ptr(_)))));
        if !pointer {
            return None;
        }
        utypes::pointee_struct(types, &ty)
    }
}

/// What the machine passes a type of the user-type language as.
///
/// # Arguments
///
/// * `types` - The overlay's user types.
/// * `ty` - The type.
fn user_pass(types: &BTreeMap<String, UserType>, ty: &TypeExpr) -> Option<Pass> {
    let int = |bits, signed| Some(Pass::Int { bits, signed });
    let mut current = ty;
    for _ in 0..=utypes::PTR_DEPTH_MAX {
        current = match current {
            TypeExpr::Ptr(_) => return Some(Pass::Pointer),
            TypeExpr::U8 | TypeExpr::Char => return int(8, false),
            TypeExpr::U16 => return int(16, false),
            TypeExpr::U32 => return int(32, false),
            TypeExpr::U64 => return int(64, false),
            TypeExpr::I8 => return int(8, true),
            TypeExpr::I16 => return int(16, true),
            TypeExpr::I32 => return int(32, true),
            TypeExpr::I64 => return int(64, true),
            TypeExpr::F32 => return Some(Pass::Float(32)),
            TypeExpr::F64 => return Some(Pass::Float(64)),
            TypeExpr::Named(n) => match types.get(n)? {
                UserType::Enum(e) => return int(u8::try_from(e.size * 8).ok()?, false),
                UserType::Struct(_) => return None,
                UserType::Alias(inner) => inner,
            },
        };
    }
    None
}

/// A calling convention a prototype states.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallConv {
    /// `__cdecl`: arguments on the stack, the caller pops them.
    Cdecl,
    /// `__stdcall` (`WINAPI`): arguments on the stack, the callee pops them.
    Stdcall,
    /// `__fastcall`: the first two in `ecx` and `edx`.
    Fastcall,
    /// `__thiscall`: the first in `ecx`.
    Thiscall,
}

impl CallConv {
    /// The keyword the convention is spelled with.
    #[must_use]
    pub fn keyword(self) -> &'static str {
        match self {
            Self::Cdecl => "__cdecl",
            Self::Stdcall => "__stdcall",
            Self::Fastcall => "__fastcall",
            Self::Thiscall => "__thiscall",
        }
    }

    /// Reads a convention keyword, `WINAPI` and its kin included.
    ///
    /// # Arguments
    ///
    /// * `word` - A word of a declaration.
    fn of(word: &str) -> Option<Self> {
        match word {
            "__cdecl" | "_cdecl" | "cdecl" => Some(Self::Cdecl),
            "__stdcall" | "_stdcall" | "stdcall" | "WINAPI" | "APIENTRY" | "CALLBACK" | "NTAPI" => {
                Some(Self::Stdcall)
            }
            "__fastcall" | "_fastcall" | "fastcall" => Some(Self::Fastcall),
            "__thiscall" | "thiscall" => Some(Self::Thiscall),
            _ => None,
        }
    }
}

/// One stated parameter.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param {
    /// Its name; empty when the prototype gave none, which renders as the
    /// position's own `aN`.
    pub name: String,
    /// Its type.
    pub ty: CType,
}

/// A prototype an agent stated for a function.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Proto {
    /// The return type; `None` for `void`.
    pub ret: Option<CType>,
    /// The calling convention, when one was stated.
    pub conv: Option<CallConv>,
    /// The fixed parameters, in order.
    pub params: Vec<Param>,
    /// A variable argument list follows the fixed parameters.
    pub variadic: bool,
}

impl Proto {
    /// Parses a prototype as C states one.
    ///
    /// `int f(int a)`, `void __stdcall (HANDLE h, const char *s)`,
    /// `Player *get(void)` and `int printf(const char *fmt, ...)` all
    /// parse; the function's own name is optional and not kept, since the
    /// function keeps the name it has. A parameter's name is optional too.
    ///
    /// # Arguments
    ///
    /// * `text` - The declaration, a trailing `;` allowed.
    ///
    /// # Errors
    ///
    /// When the text has no parameter list, no return type, a type the
    /// grammar does not read, a function-pointer parameter, a
    /// register-level convention, two parameters of one name, a name a
    /// decompiled text cannot carry, `...` before the last parameter, or
    /// more than [`PARAMS_MAX`] parameters; the message names what was
    /// refused.
    pub fn parse(text: &str) -> anyhow::Result<Self> {
        let t = text.trim().trim_end_matches(';').trim_end();
        let shown = crate::text::quoted(text);
        if t.contains("@<") || t.contains("__usercall") || t.contains("__userpurge") {
            return Err(anyhow::anyhow!(
                "{shown} states registers by hand (`__usercall`, `@<reg>`), which is not read yet; state the parameters in convention order"
            ));
        }
        let (head, rest) = t.split_once('(').ok_or_else(|| {
            anyhow::anyhow!("{shown} has no parameter list: write it as `int f(int a, char *s)`")
        })?;
        let inner = rest
            .strip_suffix(')')
            .ok_or_else(|| anyhow::anyhow!("{shown} does not end its parameter list with `)`"))?;
        if inner.contains(['(', ')']) {
            return Err(anyhow::anyhow!(
                "{shown} has a function-pointer parameter; state it as `void *name`"
            ));
        }
        let mut conv = None;
        let mut toks: Vec<Tok> = Vec::new();
        for tok in tokens(head)? {
            match &tok {
                Tok::Word(w) => match CallConv::of(w) {
                    Some(c) => conv = Some(c),
                    None if matches!(w.as_str(), "extern" | "static" | "inline") => {}
                    None => toks.push(tok),
                },
                Tok::Star => toks.push(tok),
            }
        }
        if toks.len() > 1
            && let Some(Tok::Word(last)) = toks.last()
            && !is_type_word(last)
        {
            toks.pop();
        }
        if toks.is_empty() {
            return Err(anyhow::anyhow!(
                "{shown} states no return type; write `void` for none"
            ));
        }
        let ret = type_of(&toks, text)?;
        let ret = (ret
            != CType {
                base: "void".to_owned(),
                stars: 0,
            })
        .then_some(ret);
        let mut params: Vec<Param> = Vec::new();
        let mut variadic = false;
        let pieces: Vec<&str> = inner.split(',').map(str::trim).collect();
        let none = matches!(pieces.as_slice(), ["" | "void"]);
        for (i, piece) in pieces.iter().enumerate().filter(|_| !none) {
            if variadic {
                return Err(anyhow::anyhow!("{shown} lists a parameter after `...`"));
            }
            if *piece == "..." {
                variadic = true;
                continue;
            }
            params.push(param_of(piece, i, text)?);
        }
        if params.len() > PARAMS_MAX {
            return Err(anyhow::anyhow!(
                "{shown} lists {} parameters; {PARAMS_MAX} is the most",
                params.len()
            ));
        }
        for (i, p) in params.iter().enumerate() {
            if !p.name.is_empty() && params.iter().skip(i + 1).any(|q| q.name == p.name) {
                return Err(anyhow::anyhow!("{shown} names two parameters {}", p.name));
            }
        }
        Ok(Self {
            ret,
            conv,
            params,
            variadic,
        })
    }

    /// Spells the prototype without a function name, as the project file
    /// holds it: `int __fastcall (Player *p, uint32_t n)`. [`Proto::parse`]
    /// of the spelling is the prototype again.
    #[must_use]
    pub fn spell(&self) -> String {
        let ret = self
            .ret
            .as_ref()
            .map_or_else(|| "void".to_owned(), CType::spell);
        let conv = self
            .conv
            .map_or_else(String::new, |c| format!(" {}", c.keyword()));
        let mut params: Vec<String> = self.params.iter().map(Param::spell).collect();
        if self.variadic {
            params.push("...".to_owned());
        }
        if params.is_empty() {
            params.push("void".to_owned());
        }
        format!("{ret}{conv} ({})", params.join(", "))
    }
}

impl Param {
    /// Spells the parameter: `Player *p`, `int n`, or its type alone.
    #[must_use]
    pub fn spell(&self) -> String {
        declarator(&self.ty, &self.name)
    }
}

/// Spells a type and a name as C declares them: `char *s`, `int n`, or the
/// type alone when the name is empty.
///
/// # Arguments
///
/// * `ty` - The type.
/// * `name` - The name, possibly empty.
#[must_use]
pub fn declarator(ty: &CType, name: &str) -> String {
    let spelled = ty.spell();
    match (name.is_empty(), ty.stars) {
        (true, _) => spelled,
        (false, 0) => format!("{spelled} {name}"),
        (false, _) => format!("{spelled}{name}"),
    }
}

/// Which variable of a function a stated name and type are for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VarKey {
    /// A parameter, by its position from zero (`a1` is 0).
    Param(u8),
    /// A stack slot, by its offset from the stack pointer at entry
    /// (`local_58` is -0x58).
    Slot(i64),
}

impl VarKey {
    /// Reads the name the text gives a variable: `a1`, `local_58`,
    /// `home_8`, `arg_28`.
    ///
    /// # Arguments
    ///
    /// * `text` - The name.
    /// * `word` - The stack word in bytes (4 or 8), which the slots above
    ///   the return address count from.
    ///
    /// # Errors
    ///
    /// When the text names no parameter or stack slot: a register, which
    /// holds many values over a function, is refused with that reason.
    pub fn parse(text: &str, word: i64) -> anyhow::Result<Self> {
        let hex = |s: &str| {
            (!s.is_empty() && s.len() <= 8)
                .then(|| i64::from_str_radix(s, 16).ok())
                .flatten()
        };
        if let Some(n) = text
            .strip_prefix('a')
            .filter(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()))
            .and_then(|d| d.parse::<u8>().ok())
            .filter(|n| (1..=u8::try_from(PARAMS_MAX).unwrap_or(u8::MAX)).contains(n))
        {
            return Ok(Self::Param(n - 1));
        }
        if let Some(off) = text.strip_prefix("local_").and_then(hex) {
            return Ok(Self::Slot(-off));
        }
        if let Some(off) = text
            .strip_prefix("home_")
            .or_else(|| text.strip_prefix("arg_"))
            .and_then(hex)
        {
            return Ok(Self::Slot(off + word));
        }
        Err(anyhow::anyhow!(
            "{} is no parameter or stack slot: name `aN` or `local_N` as the text shows them (a register holds many values, so it takes no name)",
            crate::text::quoted(text)
        ))
    }

    /// Spells the key the way a project file keys it, which no word size
    /// changes: `a1`, `local_58` below the return address, `sp+0x30` above
    /// it. [`VarKey::parse_saved`] reads it back.
    #[must_use]
    pub fn spell_saved(self) -> String {
        match self {
            Self::Param(i) => format!("a{}", u32::from(i) + 1),
            Self::Slot(off) if off < 0 => format!("local_{:x}", -off),
            Self::Slot(off) => format!("sp+{off:#x}"),
        }
    }

    /// Reads a key as [`VarKey::spell_saved`] writes it.
    ///
    /// # Arguments
    ///
    /// * `text` - The key.
    ///
    /// # Errors
    ///
    /// When the text is no saved key.
    pub fn parse_saved(text: &str) -> anyhow::Result<Self> {
        if let Some(off) = text
            .strip_prefix("sp+0x")
            .and_then(|h| i64::from_str_radix(h, 16).ok())
            .filter(|off| (0..crate::dwarf::FRAME_SPAN).contains(off))
        {
            return Ok(Self::Slot(off));
        }
        if text.starts_with("home_") || text.starts_with("arg_") {
            return Err(anyhow::anyhow!(
                "{} is keyed by the text's name; a project keys a slot above the return address as sp+0xN",
                crate::text::quoted(text)
            ));
        }
        Self::parse(text, 0)
    }

    /// Spells the key as the text names the variable before any name.
    ///
    /// # Arguments
    ///
    /// * `word` - The stack word in bytes.
    /// * `shadow` - The callee-owned home space above the return address
    ///   in bytes: 32 under the Microsoft x64 convention, else 0.
    #[must_use]
    pub fn spell(self, word: i64, shadow: i64) -> String {
        match self {
            Self::Param(i) => format!("a{}", u32::from(i) + 1),
            Self::Slot(off) if off < 0 => format!("local_{:x}", -off),
            Self::Slot(off) if off < word + shadow => format!("home_{:x}", off - word),
            Self::Slot(off) => format!("arg_{:x}", off - word),
        }
    }
}

/// A name and maybe a type an agent stated for one variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var {
    /// The name the text renders the variable by.
    pub name: String,
    /// Its type, when one was stated.
    pub ty: Option<CType>,
}

impl Var {
    /// Parses a variable's declaration: a name alone (`path`), or a type
    /// and a name (`wchar_t *path`).
    ///
    /// # Arguments
    ///
    /// * `text` - The declaration.
    ///
    /// # Errors
    ///
    /// When the text names nothing, or names something a decompiled text
    /// cannot carry, or its type does not parse.
    pub fn parse(text: &str) -> anyhow::Result<Self> {
        let toks = tokens(text)?;
        match toks.as_slice() {
            [Tok::Word(name)] => {
                check_name(name, text)?;
                Ok(Self {
                    name: name.clone(),
                    ty: None,
                })
            }
            [.., Tok::Word(name)] => {
                check_name(name, text)?;
                Ok(Self {
                    name: name.clone(),
                    ty: Some(type_of(toks.get(..toks.len() - 1).unwrap_or(&[]), text)?),
                })
            }
            _ => Err(anyhow::anyhow!(
                "{} names no variable: write `name` or `type name`",
                crate::text::quoted(text)
            )),
        }
    }

    /// Spells the variable: `wchar_t *path`, or its name alone.
    #[must_use]
    pub fn spell(&self) -> String {
        match &self.ty {
            Some(ty) => declarator(ty, &self.name),
            None => self.name.clone(),
        }
    }
}

/// Lists the stated prototypes and variables as rows of the `types`
/// listing ([`super::utypes::list_tsv`]).
///
/// A `prototype` row holds the function's address, `-` and the prototype;
/// a `var` row the function's address, the variable and its declaration.
/// In address order, then variable order.
///
/// # Arguments
///
/// * `prototypes` - The stated prototypes, by function.
/// * `vars` - The stated variables, by function.
#[must_use]
pub fn rows(
    prototypes: &BTreeMap<u64, Proto>,
    vars: &BTreeMap<u64, BTreeMap<VarKey, Var>>,
) -> Vec<String> {
    let mut out: Vec<String> = prototypes
        .iter()
        .map(|(at, p)| format!("prototype\t{at:#x}\t-\t{}", p.spell()))
        .collect();
    for (at, table) in vars {
        for (key, var) in table {
            out.push(format!(
                "var\t{at:#x}\t{}\t{}",
                key.spell_saved(),
                var.spell()
            ));
        }
    }
    out
}

/// A piece of a declaration: a word or a pointer.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    /// An identifier.
    Word(String),
    /// A `*`, or a `[]` after a name, which a parameter list reads as one.
    Star,
}

/// Splits a declaration into words and pointers.
///
/// # Arguments
///
/// * `text` - The declaration, or a part of one.
///
/// # Errors
///
/// When a character is neither part of an identifier, a `*`, `[]`, nor
/// space.
fn tokens(text: &str) -> anyhow::Result<Vec<Tok>> {
    let mut out: Vec<Tok> = Vec::new();
    let mut word = String::new();
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c.is_ascii_alphanumeric() || c == '_' {
            word.push(c);
            continue;
        }
        if !word.is_empty() {
            out.push(Tok::Word(std::mem::take(&mut word)));
        }
        match c {
            '*' => out.push(Tok::Star),
            '[' if chars.next_if_eq(&']').is_some() => out.push(Tok::Star),
            c if c.is_whitespace() => {}
            _ => {
                return Err(anyhow::anyhow!(
                    "{} holds {}, which no type or name spells",
                    crate::text::quoted(text),
                    crate::text::quoted(&c.to_string())
                ));
            }
        }
    }
    if !word.is_empty() {
        out.push(Tok::Word(word));
    }
    Ok(out)
}

/// Reads a type from its tokens: words first, then pointers.
///
/// # Arguments
///
/// * `toks` - The type's tokens.
/// * `text` - The whole declaration, for the message.
///
/// # Errors
///
/// When no word leads, a word follows a pointer (`char * const` reads,
/// `char * x y` does not), a word is not an identifier, or the pointers
/// pass [`utypes::PTR_DEPTH_MAX`].
fn type_of(toks: &[Tok], text: &str) -> anyhow::Result<CType> {
    let shown = || crate::text::quoted(text);
    let mut words: Vec<&str> = Vec::new();
    let mut stars = 0usize;
    for tok in toks {
        match tok {
            Tok::Word(w) if stars == 0 => words.push(w),
            Tok::Word(w) if w == "const" || w == "volatile" => {}
            Tok::Word(w) => {
                return Err(anyhow::anyhow!(
                    "{} has {} after a pointer; a type is words, then pointers",
                    shown(),
                    crate::text::quoted(w)
                ));
            }
            Tok::Star => stars += 1,
        }
    }
    if words.is_empty() || words.iter().all(|w| matches!(*w, "const" | "volatile")) {
        return Err(anyhow::anyhow!("{} states no type", shown()));
    }
    if let Some(bad) = words
        .iter()
        .find(|w| !utypes::is_ident(w) || w.starts_with(|c: char| c.is_ascii_digit()))
    {
        return Err(anyhow::anyhow!(
            "{} is not a type word in {}",
            crate::text::quoted(bad),
            shown()
        ));
    }
    if stars > utypes::PTR_DEPTH_MAX {
        return Err(anyhow::anyhow!(
            "{} stacks {stars} pointers; {} is the most",
            shown(),
            utypes::PTR_DEPTH_MAX
        ));
    }
    Ok(CType {
        base: words.join(" "),
        stars,
    })
}

/// Tells whether a word is part of a type rather than a name: a C keyword
/// of one, or a type word the library or the overlay may spell.
///
/// # Arguments
///
/// * `word` - The word.
fn is_type_word(word: &str) -> bool {
    matches!(
        word,
        "const"
            | "volatile"
            | "struct"
            | "union"
            | "enum"
            | "unsigned"
            | "signed"
            | "short"
            | "long"
            | "int"
            | "char"
            | "void"
            | "float"
            | "double"
    ) || typelib::pass_of(word, 64, BinaryFormat::Pe).is_some()
}

/// Reads one parameter: `Player *p`, `int`, `char buf[]`.
///
/// # Arguments
///
/// * `piece` - The parameter's text.
/// * `i` - Its position, for the message.
/// * `text` - The whole declaration, for the message.
///
/// # Errors
///
/// When it states no type, its type does not parse, or its name is one a
/// decompiled text cannot carry.
fn param_of(piece: &str, i: usize, text: &str) -> anyhow::Result<Param> {
    let mut toks = tokens(piece)?;
    if toks.is_empty() {
        return Err(anyhow::anyhow!(
            "parameter {} of {} is empty",
            i + 1,
            crate::text::quoted(text)
        ));
    }
    let array = toks.last() == Some(&Tok::Star) && piece.trim_end().ends_with("[]");
    if array {
        toks.pop();
    }
    let named = toks.len() > 1
        && matches!(toks.last(), Some(Tok::Word(w)) if !is_type_word(w) || toks.get(toks.len() - 2) == Some(&Tok::Star));
    let name = if let (true, Some(Tok::Word(w))) = (named, toks.last()) {
        check_name(w, text)?;
        let w = w.clone();
        toks.pop();
        w
    } else {
        String::new()
    };
    let mut ty = type_of(&toks, text)?;
    ty.stars += usize::from(array);
    Ok(Param { name, ty })
}

/// Refuses a name the decompiled text cannot carry
/// ([`crate::dwarf::local_name_ok`]): not an identifier, a word the text's
/// grammar reads, or a name it synthesizes (`a3`, `local_8`).
///
/// # Arguments
///
/// * `name` - The name.
/// * `text` - The declaration, for the message.
///
/// # Errors
///
/// When the name is refused; the message names it.
fn check_name(name: &str, text: &str) -> anyhow::Result<()> {
    if crate::dwarf::local_name_ok(name) && name.len() <= crate::text::OUTSIDE_MAX {
        return Ok(());
    }
    Err(anyhow::anyhow!(
        "{} in {} is not a name the text can carry: an identifier, no keyword, and none of the names it makes up (aN, local_N, tmp_N)",
        crate::text::quoted(name),
        crate::text::quoted(text)
    ))
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::collections::BTreeMap;

    use super::{CType, CallConv, Proto, Var, VarKey};
    use crate::analysis::typelib::Pass;
    use crate::analysis::utypes::{TypeExpr, UserType, build_struct};
    use crate::program::BinaryFormat;

    /// Prototypes parse with and without names, conventions and `...`, and
    /// spell back to themselves.
    #[test]
    fn prototypes_parse_and_spell_back() {
        let p = Proto::parse("int __fastcall f(Player *p, uint32_t n);").expect("parses");
        assert_eq!(p.conv, Some(CallConv::Fastcall));
        assert_eq!(p.ret.as_ref().map(CType::spell).as_deref(), Some("int"));
        assert_eq!(p.params.len(), 2);
        assert_eq!(
            (p.params[0].name.as_str(), p.params[0].ty.spell().as_str()),
            ("p", "Player *")
        );
        assert_eq!(p.spell(), "int __fastcall (Player *p, uint32_t n)");
        assert_eq!(Proto::parse(&p.spell()).expect("round trip"), p);
        let v = Proto::parse("void f(void)").expect("void");
        assert_eq!((v.ret.clone(), v.params.len()), (None, 0));
        assert_eq!(v.spell(), "void (void)");
        let pf = Proto::parse("int printf(const char *fmt, ...)").expect("variadic");
        assert!(pf.variadic);
        assert_eq!(pf.params[0].ty.spell(), "const char *");
        let unnamed = Proto::parse("char *(int, unsigned int)").expect("unnamed");
        assert_eq!(
            unnamed.ret.as_ref().map(CType::spell).as_deref(),
            Some("char *")
        );
        assert!(unnamed.params.iter().all(|p| p.name.is_empty()));
        assert_eq!(unnamed.params[1].ty.spell(), "unsigned int");
        let arr = Proto::parse("void WINAPI g(HANDLE h, char buf[])").expect("array");
        assert_eq!(arr.conv, Some(CallConv::Stdcall));
        assert_eq!(arr.params[1].ty.spell(), "char *");
        assert_eq!(arr.params[1].name, "buf");
    }

    /// What the grammar does not read is refused with the reason.
    #[test]
    fn prototypes_refuse_what_they_cannot_state() {
        let err = |t: &str| Proto::parse(t).expect_err(t).to_string();
        assert!(err("int f").contains("no parameter list"));
        assert!(err("(int a)").contains("no return type"));
        assert!(err("int f(int (*cb)(int))").contains("function-pointer"));
        assert!(err("int __usercall f@<eax>(int a@<ecx>)").contains("registers"));
        assert!(err("int f(int a, int a)").contains("two parameters"));
        assert!(err("int f(int a3)").contains("not a name"));
        assert!(err("int f(..., int a)").contains("after `...`"));
        assert!(err("int f(int $x)").contains("no type or name"));
        let many = format!("int f({})", vec!["int"; 40].join(", "));
        assert!(err(&many).contains("most"));
    }

    /// Variables key by the name the text shows, and refuse registers.
    #[test]
    fn variable_keys_read_the_texts_names() {
        assert_eq!(VarKey::parse("a1", 8).ok(), Some(VarKey::Param(0)));
        assert_eq!(VarKey::parse("local_58", 8).ok(), Some(VarKey::Slot(-0x58)));
        assert_eq!(VarKey::parse("arg_28", 8).ok(), Some(VarKey::Slot(0x30)));
        assert_eq!(VarKey::parse("home_8", 8).ok(), Some(VarKey::Slot(0x10)));
        assert!(VarKey::parse("rax", 8).is_err());
        assert!(VarKey::parse("a0", 8).is_err());
        for key in [
            VarKey::Param(2),
            VarKey::Slot(-0x58),
            VarKey::Slot(0x30),
            VarKey::Slot(0x10),
        ] {
            assert_eq!(VarKey::parse(&key.spell(8, 32), 8).ok(), Some(key));
        }
        let v = Var::parse("wchar_t *path").expect("typed");
        assert_eq!(
            (v.name.as_str(), v.spell().as_str()),
            ("path", "wchar_t *path")
        );
        assert_eq!(Var::parse("count").expect("bare").ty, None);
        assert!(Var::parse("local_8").is_err());
        for key in [VarKey::Param(0), VarKey::Slot(-0x58), VarKey::Slot(0x30)] {
            assert_eq!(VarKey::parse_saved(&key.spell_saved()).ok(), Some(key));
        }
        assert!(VarKey::parse_saved("arg_28").is_err());
    }

    /// Types pass through user types first, then the library's words, and
    /// a pointer to a user struct reaches its fields.
    #[test]
    fn types_resolve_against_user_types() {
        let mut types: BTreeMap<String, UserType> = BTreeMap::new();
        let player = build_struct(
            "Player",
            None,
            &[(0x10, "hp".to_owned(), TypeExpr::U32)],
            &types,
            8,
        )
        .expect("struct");
        types.insert("Player".to_owned(), player);
        let pe = BinaryFormat::Pe;
        let ty = CType::parse("Player *").expect("type");
        assert_eq!(ty.pass(&types, 64, pe), Some(Pass::Pointer));
        assert!(
            ty.pointee(&types)
                .is_some_and(|s| s.fields.contains_key(&0x10))
        );
        assert!(
            CType::parse("Player")
                .expect("type")
                .pointee(&types)
                .is_none()
        );
        assert_eq!(
            CType::parse("const int").expect("int").pass(&types, 64, pe),
            Some(Pass::Int {
                bits: 32,
                signed: true
            })
        );
        assert_eq!(
            CType::parse("Mystery")
                .expect("opaque")
                .pass(&types, 64, pe),
            None
        );
    }
}
