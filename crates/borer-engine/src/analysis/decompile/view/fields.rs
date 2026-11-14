//! Field links, aggregate layouts and constant classification for decompile
//! views.
//!
//! Reads struct, typedef and constant declarations from the unit alongside
//! user types, debug types, SDK layouts and class field tables, while keeping
//! overlay lookups per-key so no whole overlay map is noted.

use std::cell::{OnceCell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use super::super::fields::api_pointee_tags;
use super::super::lexer::{Lex, Piece};
use super::super::line::is_ident;
use super::super::{cir, ctext, defs, enums, unit};
use super::{At, Declared, Facts, Role, Spanned, Tally, code, code_before, word};
use crate::analysis::attributes::global_addr;
use crate::analysis::utypes::{ALIAS_DEPTH_MAX, TypeExpr, UserStruct, UserType};
use crate::analysis::{Analysis, EnumSource, Overlay, classes, sdk, typelib};
use crate::program::{Arch, BinaryFormat, Program};
use crate::view::{Kind, Ref};

/// Maximum recursion depth when resolving chained member or cast expressions.
const EXPR_DEPTH_MAX: usize = 8;

/// Maximum code tokens inspected backward for a single `->` or `.` receiver.
const RECEIVER_TOKENS_MAX: usize = 128;

/// Code piece triple `(piece, text, span)` used when inspecting expressions.
type Tok<'t> = (Piece, &'t str, Range<usize>);

/// Normalized C or user type spelling reduced to base name, indirections and
/// array flag.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct TypeSpec {
    /// Unqualified base type name (`Widget`, `_IO_FILE`, `uint32_t`).
    pub(super) base: String,
    /// Pointer or reference indirection count (`*` and `&`).
    pub(super) ptrs: usize,
    /// Whether the declarator carries `[...]` array bounds.
    pub(super) array: bool,
}

/// One member of a unit-defined `struct Tag { ... };` line.
#[derive(Debug, Clone)]
struct UnitField {
    /// Byte offset from the start of the struct.
    offset: u64,
    /// Member identifier.
    name: String,
    /// Parsed member type.
    spec: TypeSpec,
}

/// Layout parsed from a unit-defined `struct Tag { ... };` line.
#[derive(Debug, Clone, Default)]
struct UnitStruct {
    /// Total byte size including tail padding when every member layout is known.
    size: Option<u64>,
    /// Required aggregate alignment in bytes when every member layout is known.
    align: Option<u64>,
    /// Members in declaration order.
    fields: Vec<UnitField>,
}

/// Per-function type, struct and constant tables read from the text's lines.
#[derive(Debug, Default)]
pub(super) struct Types<'t> {
    /// Parameter types declared on the `// signature: ` line.
    params: BTreeMap<&'t str, TypeSpec>,
    /// Local variable types declared in `Role::Declaration` lines.
    locals: BTreeMap<&'t str, TypeSpec>,
    /// Unit-scope `extern` or `static` object types.
    globals: BTreeMap<&'t str, TypeSpec>,
    /// Unit-scope `typedef` and `#define` type aliases.
    aliases: BTreeMap<&'t str, TypeSpec>,
    /// Struct definitions emitted in the unit header (`Role::Struct`).
    unit_structs: BTreeMap<String, UnitStruct>,
    /// Lazily inferred SDK struct tags and smart-pointer classes by variable.
    inferred_ptrs: OnceCell<BTreeMap<String, String>>,
    /// Last `Role::Inline` line's inferred pointer tags keyed by line index.
    inline_ptrs: RefCell<Option<(usize, BTreeMap<String, String>)>>,
    /// Lazily gathered enum member identifiers active in this function's text.
    enum_members: OnceCell<BTreeSet<String>>,
}

/// Parses `field_0x<hex>` into its byte offset.
///
/// # Arguments
///
/// * `w` - Candidate field token text.
pub(crate) fn field_hex_offset(w: &str) -> Option<u64> {
    let hex = w.strip_prefix("field_0x")?;
    (!hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit()))
        .then(|| u64::from_str_radix(hex, 16).ok())
        .flatten()
}

/// Tells whether `w` is a C type qualifier or aggregate tag keyword dropped
/// from [`TypeSpec::base`].
///
/// # Arguments
///
/// * `w` - Token word.
fn is_qualifier_or_tag(w: &str) -> bool {
    matches!(
        w,
        "const"
            | "volatile"
            | "restrict"
            | "__restrict"
            | "__unaligned"
            | "__ptr32"
            | "__ptr64"
            | "struct"
            | "union"
            | "class"
            | "enum"
            | "extern"
            | "static"
            | "typedef"
    )
}

/// Parses a spelled C type string (`const struct Foo *`, `Widget[4]`) into a
/// [`TypeSpec`].
///
/// # Arguments
///
/// * `spelled` - Raw C type text.
fn spec_from_str(spelled: &str) -> Option<TypeSpec> {
    if spelled.contains("(*") {
        return None;
    }
    let mut base_words = Vec::new();
    let mut ptrs = 0usize;
    let mut array = false;
    let mut in_brackets = 0usize;
    let mut pieces = Vec::new();
    super::split(spelled, 0, &mut pieces);
    for (_, w, _) in code(spelled, &pieces) {
        match w {
            "[" => {
                array = true;
                in_brackets += 1;
            }
            "]" => in_brackets = in_brackets.saturating_sub(1),
            _ if in_brackets > 0 => {}
            "*" | "&" => ptrs += 1,
            "(" | ")" | "," | ";" => return None,
            _ if is_qualifier_or_tag(w) => {}
            _ => base_words.push(w),
        }
    }
    (!base_words.is_empty()).then(|| TypeSpec {
        base: base_words.join(" "),
        ptrs,
        array,
    })
}

/// Converts a [`TypeExpr`] into a [`TypeSpec`].
///
/// # Arguments
///
/// * `expr` - Structured user or debug type expression.
fn spec_from_expr(expr: &TypeExpr) -> TypeSpec {
    let mut cur = expr;
    let mut ptrs = 0usize;
    let mut array = false;
    loop {
        match cur {
            TypeExpr::Ptr(inner) => {
                ptrs += 1;
                cur = inner;
            }
            TypeExpr::Array(inner, _) => {
                array = true;
                cur = inner;
            }
            TypeExpr::Named(n) => {
                return TypeSpec {
                    base: n.clone(),
                    ptrs,
                    array,
                };
            }
            TypeExpr::U8
            | TypeExpr::U16
            | TypeExpr::U32
            | TypeExpr::U64
            | TypeExpr::I8
            | TypeExpr::I16
            | TypeExpr::I32
            | TypeExpr::I64
            | TypeExpr::F32
            | TypeExpr::F64
            | TypeExpr::Char => {
                return TypeSpec {
                    base: cur.spell(),
                    ptrs,
                    array,
                };
            }
        }
    }
}

/// Parses parameter `(name, TypeSpec)` pairs from a signature, prototype or
/// `static inline` line.
///
/// # Arguments
///
/// * `line` - Source line containing a parameter list.
/// * `pieces` - Scanned pieces of `line`.
fn param_specs<'t>(line: &'t str, pieces: &[Spanned]) -> BTreeMap<&'t str, TypeSpec> {
    let mut out = BTreeMap::new();
    let mut code_iter = pieces
        .iter()
        .filter(|(p, _)| !matches!(p, Piece::Space | Piece::Comment))
        .map(|(p, r)| (*p, line.get(r.clone()).unwrap_or(""), r.clone()));
    let mut brackets = 0usize;
    let mut opened = false;
    for (_, w, _) in &mut code_iter {
        if w == "(" && brackets == 0 {
            opened = true;
            break;
        }
        brackets = match w {
            "[" | "{" => brackets + 1,
            "]" | "}" => brackets.saturating_sub(1),
            _ => brackets,
        };
    }
    if !opened {
        return out;
    }
    let mut depth = 0usize;
    let mut cur: Vec<Tok<'t>> = Vec::new();
    for tok in code_iter {
        let w = tok.1;
        if depth == 0 && matches!(w, "," | ")") {
            if let Some((name, spec)) = one_param_spec(&cur) {
                out.insert(name, spec);
            }
            cur.clear();
            if w == ")" {
                break;
            }
            continue;
        }
        depth = match w {
            "(" | "[" | "{" => depth + 1,
            ")" | "]" | "}" => depth.saturating_sub(1),
            _ => depth,
        };
        cur.push(tok);
    }
    out
}

/// Parses one parameter slice into `(name, TypeSpec)`.
///
/// # Arguments
///
/// * `slice` - Code tokens of a single parameter declaration.
fn one_param_spec<'t>(slice: &[Tok<'t>]) -> Option<(&'t str, TypeSpec)> {
    if slice.len() < 2 || slice.iter().any(|(_, w, _)| *w == "(" || *w == "...") {
        return None;
    }
    let mut in_brackets = 0usize;
    let mut name_idx = None;
    for (i, (p, w, _)) in slice.iter().enumerate() {
        match *w {
            "[" => in_brackets += 1,
            "]" => in_brackets = in_brackets.saturating_sub(1),
            _ if in_brackets == 0 && *p == Piece::Token(Lex::Name) => name_idx = Some(i),
            _ => {}
        }
    }
    let name_idx = name_idx?;
    let name = slice[name_idx].1;
    let mut base_words = Vec::new();
    let mut ptrs = 0usize;
    let mut array = false;
    in_brackets = 0;
    for (i, (_, w, _)) in slice.iter().enumerate() {
        if i == name_idx {
            continue;
        }
        match *w {
            "[" => {
                array = true;
                in_brackets += 1;
            }
            "]" => in_brackets = in_brackets.saturating_sub(1),
            _ if in_brackets > 0 => {}
            "*" | "&" => ptrs += 1,
            _ if is_qualifier_or_tag(w) => {}
            _ => base_words.push(*w),
        }
    }
    (!base_words.is_empty()).then(|| {
        (
            name,
            TypeSpec {
                base: base_words.join(" "),
                ptrs,
                array,
            },
        )
    })
}

/// Parses declarators from a declaration statement (`Foo *a, b[4];`) into
/// `(name, TypeSpec, array_count)` triples.
///
/// # Arguments
///
/// * `stmt` - Code tokens of one `;`-terminated declaration without `;`.
fn parse_decl_stmt<'t>(stmt: &[Tok<'t>]) -> Vec<(&'t str, TypeSpec, Option<u64>)> {
    let mut out = Vec::new();
    if stmt.is_empty() || stmt.iter().any(|(_, w, _)| *w == "(") {
        return out;
    }
    let first_comma = stmt
        .iter()
        .position(|(_, w, _)| *w == ",")
        .unwrap_or(stmt.len());
    let before_comma = &stmt[..first_comma];
    let first_eq = before_comma
        .iter()
        .position(|(_, w, _)| *w == "=")
        .unwrap_or(before_comma.len());
    let first = &before_comma[..first_eq];
    let first_star = first.iter().position(|(_, w, _)| matches!(*w, "*" | "&"));
    let mut in_brackets = 0usize;
    let mut first_name = None;
    for (i, (p, w, _)) in first.iter().enumerate() {
        match *w {
            "[" => in_brackets += 1,
            "]" => in_brackets = in_brackets.saturating_sub(1),
            _ if in_brackets == 0 && *p == Piece::Token(Lex::Name) => first_name = Some(i),
            _ => {}
        }
    }
    let Some(first_name) = first_name else {
        return out;
    };
    let spec_end = first_star.unwrap_or(first_name).min(first_name);
    let base_words: Vec<&str> = first[..spec_end]
        .iter()
        .map(|(_, w, _)| *w)
        .filter(|w| !is_qualifier_or_tag(w))
        .collect();
    if base_words.is_empty() {
        return out;
    }
    let base = base_words.join(" ");
    for part in stmt[spec_end..].split(|(_, w, _)| *w == ",") {
        let head = part
            .iter()
            .position(|(_, w, _)| *w == "=")
            .map_or(part, |eq| &part[..eq]);
        if let Some((n, ptrs, arr_len)) = one_declarator(head) {
            out.push((
                n,
                TypeSpec {
                    base: base.clone(),
                    ptrs,
                    array: arr_len.is_some(),
                },
                arr_len.flatten(),
            ));
        }
    }
    out
}

/// Parses one declarator tail (`*a`, `buf[0x28]`) into `(name, ptrs, array)`.
///
/// # Arguments
///
/// * `decl` - Code tokens after the declaration's shared type specifiers.
fn one_declarator<'t>(decl: &[Tok<'t>]) -> Option<(&'t str, usize, Option<Option<u64>>)> {
    let mut ptrs = 0usize;
    let mut name = None;
    let mut in_brackets = 0usize;
    let mut arr: Option<Option<u64>> = None;
    let mut arr_toks: Vec<&str> = Vec::new();
    for (p, w, _) in decl {
        match *w {
            "[" => {
                if in_brackets == 0 {
                    arr_toks.clear();
                }
                in_brackets += 1;
            }
            "]" => {
                in_brackets = in_brackets.saturating_sub(1);
                if in_brackets == 0 {
                    let count = (arr_toks.len() == 1)
                        .then(|| parse_u64(arr_toks[0]))
                        .flatten();
                    arr = Some(if arr.is_none() { count } else { None });
                }
            }
            _ if in_brackets > 0 => arr_toks.push(*w),
            "*" | "&" => ptrs += 1,
            _ if *p == Piece::Token(Lex::Name) => name = Some(*w),
            _ => return None,
        }
    }
    Some((name?, ptrs, arr))
}

/// Parses a decimal or `0x`-prefixed hexadecimal literal into `u64`.
///
/// # Arguments
///
/// * `s` - Literal token text.
fn parse_u64(s: &str) -> Option<u64> {
    match s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None => s.parse::<u64>().ok(),
    }
}

/// Returns the natural struct-member alignment in bytes of a scalar of `width`
/// bytes under `program`'s architecture and container ABI, or `None` when
/// layout rules are unknown.
///
/// # Arguments
///
/// * `width` - Scalar width in bytes.
/// * `program` - Loaded image supplying [`Arch`] and [`BinaryFormat`].
fn scalar_align(width: u64, program: &Program) -> Option<u64> {
    if width == 0 || !width.is_power_of_two() || width > 16 {
        return None;
    }
    match program.arch {
        Arch::X86_64 | Arch::Arm64 | Arch::RiscV64 | Arch::Arm | Arch::RiscV32 => Some(width),
        Arch::X86 => match program.format {
            BinaryFormat::Pe => Some(width),
            BinaryFormat::Elf | BinaryFormat::MachO => Some(width.min(4)),
            BinaryFormat::Archive | BinaryFormat::Raw => (width <= 4).then_some(width),
        },
        Arch::Unknown => None,
    }
}

/// Rounds `offset` up to the next multiple of power-of-two `align`.
///
/// # Arguments
///
/// * `offset` - Current byte offset.
/// * `align` - Required alignment in bytes.
fn align_up(offset: u64, align: u64) -> Option<u64> {
    if align == 0 || !align.is_power_of_two() {
        return None;
    }
    let mask = align - 1;
    offset.checked_add(mask).map(|v| v & !mask)
}

/// Returns `(element_width, member_alignment)` in bytes of a member type inside
/// a unit `struct` definition.
///
/// # Arguments
///
/// * `spec` - Member type specification.
/// * `word_bytes` - Target pointer width in bytes (`4` or `8`).
/// * `unit_structs` - Previously parsed unit structs.
/// * `program` - Loaded image for ABI layout rules.
fn unit_member_layout(
    spec: &TypeSpec,
    word_bytes: u64,
    unit_structs: &BTreeMap<String, UnitStruct>,
    program: &Program,
) -> Option<(u64, u64)> {
    if spec.ptrs > 0 {
        return Some((word_bytes, scalar_align(word_bytes, program)?));
    }
    let word_bits = u8::try_from(word_bytes.saturating_mul(8)).unwrap_or(64);
    if let Some(ty) = ctext::named_type(&spec.base, word_bits) {
        let w = (ty.ptr > 0 || ty.base != ctext::Base::Void)
            .then(|| ty.size(word_bits))
            .flatten()?;
        return Some((w, scalar_align(w, program)?));
    }
    if let Some(pass) = typelib::pass_of(&spec.base, word_bits, program.format) {
        let bits = pass.bits(word_bits);
        let w = (bits > 0 && bits % 8 == 0).then_some(u64::from(bits / 8))?;
        return Some((w, scalar_align(w, program)?));
    }
    if let Some(u) = unit_structs.get(&spec.base) {
        return Some((u.size?, u.align?));
    }
    None
}

/// Parses a `Role::Struct` line (`struct Tag { ... };`) into `(tag, UnitStruct)`.
///
/// # Arguments
///
/// * `toks` - Code tokens of the struct definition line.
/// * `word_bytes` - Target pointer width in bytes.
/// * `unit_structs` - Previously parsed unit structs.
/// * `program` - Loaded image.
fn parse_unit_struct(
    toks: &[Tok<'_>],
    word_bytes: u64,
    unit_structs: &BTreeMap<String, UnitStruct>,
    program: &Program,
) -> Option<(String, UnitStruct)> {
    let tag = toks
        .get(1)
        .filter(|(p, ..)| *p == Piece::Token(Lex::Name))
        .map(|(_, w, _)| (*w).to_owned())?;
    let open = toks.iter().position(|(_, w, _)| *w == "{")?;
    let close = toks.iter().rposition(|(_, w, _)| *w == "}")?;
    let body = toks.get(open + 1..close)?;
    let mut fields = Vec::new();
    let mut offset: Option<u64> = Some(0);
    let mut max_align: Option<u64> = Some(1);
    for stmt in body.split(|(_, w, _)| *w == ";") {
        if stmt.is_empty() {
            continue;
        }
        let decls = parse_decl_stmt(stmt);
        if decls.is_empty() {
            offset = None;
            max_align = None;
            continue;
        }
        for (name, spec, arr_count) in decls {
            let layout = unit_member_layout(&spec, word_bytes, unit_structs, program);
            if let (Some(cur), Some((elem_w, member_align))) = (offset, layout)
                && let Some(field_off) = align_up(cur, member_align)
            {
                fields.push(UnitField {
                    offset: field_off,
                    name: name.to_owned(),
                    spec: spec.clone(),
                });
                max_align = max_align.map(|a| a.max(member_align));
                let total = match (spec.array, arr_count) {
                    (false, _) => Some(elem_w),
                    (true, Some(n)) => elem_w.checked_mul(n),
                    (true, None) => None,
                };
                offset = total.and_then(|w| field_off.checked_add(w));
                if offset.is_none() {
                    max_align = None;
                }
            } else {
                offset = None;
                max_align = None;
            }
        }
    }
    let size = offset
        .zip(max_align)
        .and_then(|(off, al)| align_up(off, al));
    Some((
        tag,
        UnitStruct {
            size,
            align: max_align,
            fields,
        },
    ))
}

impl<'t> Types<'t> {
    /// Records parameter types from the function's `// signature: ` line.
    ///
    /// # Arguments
    ///
    /// * `line` - Signature line.
    /// * `pieces` - Scanned pieces of `line`.
    pub(super) fn read_signature(&mut self, line: &'t str, pieces: &[Spanned]) {
        self.params.extend(param_specs(line, pieces));
    }

    /// Records type, alias, struct or variable declarations from one header or
    /// declaration line.
    ///
    /// # Arguments
    ///
    /// * `role` - Line role classified by [`Declared::read`].
    /// * `line` - Source line.
    /// * `pieces` - Scanned pieces of `line`.
    /// * `program` - Loaded image.
    pub(super) fn read_line(
        &mut self,
        role: Role,
        line: &'t str,
        pieces: &[Spanned],
        program: &Program,
    ) {
        let toks = code(line, pieces);
        let word_bytes = if program.is_64 { 8 } else { 4 };
        match role {
            Role::Struct => {
                if defs::defines(line)
                    && let Some((tag, st)) =
                        parse_unit_struct(&toks, word_bytes, &self.unit_structs, program)
                {
                    self.unit_structs.insert(tag, st);
                }
            }
            Role::Declaration => {
                let end = toks
                    .iter()
                    .position(|(_, w, _)| *w == ";")
                    .unwrap_or(toks.len());
                let stmt = toks.get(..end).unwrap_or_default();
                for (name, spec, _) in parse_decl_stmt(stmt) {
                    self.locals.insert(name, spec);
                }
            }
            Role::Item => self.read_item(line, &toks),
            Role::Header
            | Role::Signature
            | Role::Prototype
            | Role::Macro
            | Role::Inline
            | Role::Body => {}
        }
    }

    /// Records typedefs, `#define` type aliases and `extern`/`static` object
    /// declarations from a `Role::Item` line.
    ///
    /// # Arguments
    ///
    /// * `line` - Source line.
    /// * `toks` - Code tokens of `line`.
    fn read_item(&mut self, line: &'t str, toks: &[Tok<'t>]) {
        if line.starts_with("#define ") {
            if let (
                Some((Piece::Token(Lex::Name), alias, _)),
                Some((Piece::Token(Lex::Name), target, _)),
            ) = (toks.get(2), toks.get(3))
                && toks.len() == 4
            {
                self.aliases.insert(
                    alias,
                    TypeSpec {
                        base: (*target).to_owned(),
                        ptrs: 0,
                        array: false,
                    },
                );
            }
            return;
        }
        let end = toks
            .iter()
            .position(|(_, w, _)| *w == ";")
            .unwrap_or(toks.len());
        if line.starts_with("typedef ") {
            for (name, spec, _) in parse_decl_stmt(&toks[..end]) {
                self.aliases.insert(name, spec);
            }
        } else if line.starts_with("extern ") || line.starts_with("static ") {
            for (name, spec, _) in parse_decl_stmt(&toks[..end]) {
                self.globals.insert(name, spec);
            }
        }
    }
}

/// Context borrowed while resolving a member token or constant identifier.
pub(super) struct FieldCtx<'a, 't> {
    /// Loaded image.
    pub(super) program: &'a Program,
    /// Discovery results.
    pub(super) analysis: &'a Analysis,
    /// Active overlay.
    pub(super) overlay: &'a Overlay,
    /// Full decompile text being viewed.
    pub(super) text: &'t str,
    /// Owning function's body slice, excluding header and `static inline` lines.
    pub(super) body: &'t str,
    /// Machine word in bits (`32` or `64`).
    pub(super) word_bits: u8,
    /// Unit declarations.
    pub(super) declared: &'a Declared<'t>,
    /// Parsed types and structs from the text.
    pub(super) types: &'a Types<'t>,
}

impl FieldCtx<'_, '_> {
    /// Resolves a `Kind::Field` token right after `->` or `.`.
    ///
    /// # Arguments
    ///
    /// * `w` - Member token text.
    /// * `prev` - Immediately preceding operator (`"->"` or `"."`).
    /// * `at` - Token position and scope.
    /// * `tally` - Counts ambiguous and uncorroborated member names.
    pub(super) fn resolve_member(
        &self,
        w: &str,
        prev: &str,
        at: &At<'_>,
        tally: &mut Tally,
    ) -> (Kind, Option<Ref>, bool) {
        let arrow = prev == "->";
        let op_idx = code_before(at.pieces, at.k);
        if let Some(offset) = field_hex_offset(w) {
            let ty = op_idx
                .filter(|_| arrow)
                .and_then(|op| self.declared_base_pointee(op, at))
                .filter(|t| self.offset_fits(t, offset))
                .map(Into::into);
            return (Kind::Field, Some(Ref::Field { ty, offset }), false);
        }
        let Some(op) = op_idx else {
            return (Kind::Field, None, false);
        };
        let toks = code_before_op(at.line, at.pieces, op);
        let Some(base_spec) = self.expr_type(&toks, at, 0, false) else {
            return (Kind::Field, None, false);
        };
        let spec = self.resolve_aliases(base_spec);
        let expect_ptrs = usize::from(arrow);
        if spec.ptrs != expect_ptrs || spec.array || !self.is_named_aggregate(&spec.base) {
            return (Kind::Field, None, false);
        }
        self.lookup_named_field(&spec.base, w, tally)
    }

    /// Returns the declared pointee aggregate type when the expression before
    /// `->` is a bare variable or parameter declared in scope.
    ///
    /// # Arguments
    ///
    /// * `op_piece` - Piece index of `->`.
    /// * `at` - Token position and scope.
    fn declared_base_pointee(&self, op_piece: usize, at: &At<'_>) -> Option<String> {
        let base_piece = code_before(at.pieces, op_piece)?;
        let (piece, _) = at.pieces.get(base_piece)?;
        if *piece != Piece::Token(Lex::Name) {
            return None;
        }
        if let Some(before) = code_before(at.pieces, base_piece) {
            let bw = word(at.line, at.pieces, before);
            if matches!(bw, "->" | "." | "]") {
                return None;
            }
        }
        let var = word(at.line, at.pieces, base_piece);
        let raw = self.scope_var_spec(var, at)?;
        let spec = self.resolve_aliases(raw);
        (spec.ptrs == 1 && !spec.array && self.is_named_aggregate(&spec.base)).then_some(spec.base)
    }

    /// Looks up a declared variable or parameter's [`TypeSpec`] in `at`'s scope.
    ///
    /// # Arguments
    ///
    /// * `var` - Variable or parameter identifier.
    /// * `at` - Token position and scope.
    fn scope_var_spec(&self, var: &str, at: &At<'_>) -> Option<TypeSpec> {
        match at.role {
            Role::Inline | Role::Prototype => param_specs(at.line, at.pieces).remove(var),
            Role::Signature | Role::Declaration | Role::Body => self
                .types
                .locals
                .get(var)
                .or_else(|| self.types.params.get(var))
                .cloned(),
            Role::Header | Role::Macro | Role::Struct | Role::Item => None,
        }
    }

    /// Resolves typedef and `#define` alias chains up to [`ALIAS_DEPTH_MAX`].
    ///
    /// # Arguments
    ///
    /// * `spec` - Initial type specification.
    fn resolve_aliases(&self, mut spec: TypeSpec) -> TypeSpec {
        let mut seen = BTreeSet::new();
        for _ in 0..ALIAS_DEPTH_MAX {
            if !seen.insert(spec.base.clone()) {
                break;
            }
            let next = if let Some(a) = self.types.aliases.get(spec.base.as_str()) {
                Some(a.clone())
            } else if let Some(UserType::Alias(expr)) = self.overlay.types.get(&spec.base) {
                Some(spec_from_expr(expr))
            } else if let Some(spelled) = self.program.debug_typedefs.get(&spec.base) {
                spec_from_str(spelled)
            } else if let Some(spelled) = typelib::type_definition(&spec.base, self.program.format)
            {
                spec_from_str(spelled)
            } else if let Some(td) = sdk::typedef(&spec.base) {
                match td.tag {
                    Some(tag) => Some(TypeSpec {
                        base: tag.to_owned(),
                        ptrs: td.stars,
                        array: false,
                    }),
                    None => break,
                }
            } else {
                None
            };
            let Some(next) = next else {
                break;
            };
            spec = TypeSpec {
                base: next.base,
                ptrs: spec.ptrs.saturating_add(next.ptrs),
                array: spec.array || next.array,
            };
        }
        spec
    }

    /// Tells whether `base` names a struct, union or class aggregate rather
    /// than a scalar or enum.
    ///
    /// # Arguments
    ///
    /// * `base` - Unqualified base type name.
    fn is_named_aggregate(&self, base: &str) -> bool {
        if base.is_empty()
            || cir::KEYWORDS.contains(&base)
            || unit::C_WORDS.contains(&base)
            || ctext::named_type(base, self.word_bits).is_some()
        {
            return false;
        }
        if matches!(
            self.overlay
                .types
                .get(base)
                .or_else(|| self.program.debug_types.get(base)),
            Some(UserType::Enum(_))
        ) {
            return false;
        }
        self.is_known_struct(base)
            || typelib::pass_of(base, self.word_bits, self.program.format).is_none()
    }

    /// Tells whether `base` is an explicitly defined C or user struct.
    ///
    /// # Arguments
    ///
    /// * `base` - Aggregate name.
    fn is_known_struct(&self, base: &str) -> bool {
        matches!(self.overlay.types.get(base), Some(UserType::Struct(_)))
            || matches!(
                self.program.debug_types.get(base),
                Some(UserType::Struct(_))
            )
            || self.types.unit_structs.contains_key(base)
            || sdk::structure(base).is_some()
    }

    /// Returns the known byte size of aggregate `ty`, when any source states it.
    ///
    /// # Arguments
    ///
    /// * `ty` - Aggregate type name.
    fn type_size(&self, ty: &str) -> Option<u64> {
        if let Some(UserType::Struct(s)) = self.overlay.types.get(ty) {
            return Some(s.size);
        }
        if let Some(UserType::Struct(s)) = self.program.debug_types.get(ty)
            && s.size > 0
        {
            return Some(s.size);
        }
        if let Some(u) = self.types.unit_structs.get(ty)
            && let Some(sz) = u.size
            && sz > 0
        {
            return Some(sz);
        }
        if let Some(s) = sdk::structure(ty) {
            let sz = if self.word_bits == 64 {
                Some(s.size64)
            } else {
                s.size32
            };
            return sz.filter(|&n| n > 0);
        }
        None
    }

    /// Tells whether `offset` lies strictly within `ty`'s known byte size.
    ///
    /// # Arguments
    ///
    /// * `ty` - Aggregate type name.
    /// * `offset` - Candidate field offset in bytes.
    fn offset_fits(&self, ty: &str, offset: u64) -> bool {
        self.type_size(ty).is_none_or(|sz| offset < sz)
    }

    /// Tells whether `cast` inside `(cast)expr->field` is an unparenthesized C
    /// prefix cast whose precedence is lower than `->` and `.`.
    ///
    /// # Arguments
    ///
    /// * `cast` - Tokens inside the leading `(...)`.
    /// * `at` - Enclosing line and scope.
    fn is_unparenthesized_cast(&self, cast: &[Tok<'_>], at: &At<'_>) -> bool {
        if !is_cast_type_tokens(cast) {
            return false;
        }
        if let [(Piece::Token(Lex::Name), single, _)] = cast {
            return self.scope_var_spec(single, at).is_none()
                && !self.declared.vars.contains(single)
                && !self.declared.functions.contains(single);
        }
        true
    }

    /// Resolves the type of an expression token slice before `->` or `.`.
    ///
    /// # Arguments
    ///
    /// * `expr` - Expression tokens ending immediately before `->` or `.`.
    /// * `at` - Enclosing line and scope.
    /// * `depth` - Current recursion depth.
    /// * `allow_prefix` - Whether outer parentheses allow unary prefix casts,
    ///   `*` and `&` to govern the whole slice.
    fn expr_type(
        &self,
        mut expr: &[Tok<'_>],
        at: &At<'_>,
        depth: usize,
        allow_prefix: bool,
    ) -> Option<TypeSpec> {
        if expr.is_empty() || depth > EXPR_DEPTH_MAX {
            return None;
        }
        if !allow_prefix {
            while let Some((cast, rest)) = split_leading_paren_group(expr) {
                if !self.is_unparenthesized_cast(cast, at) {
                    break;
                }
                expr = rest;
            }
        }
        if let Some(inner) = strip_outer_parens(expr) {
            return self.expr_type(inner, at, depth + 1, true);
        }
        if allow_prefix {
            if let Some((cast, inner)) = strip_leading_cast(expr)
                && is_cast_operand(inner)
                && let Some(spec) = spec_from_tokens(cast)
            {
                return Some(spec);
            }
            if let [(_, "*", _), rest @ ..] = expr {
                let mut inner = self.resolve_aliases(self.expr_type(rest, at, depth + 1, true)?);
                inner.ptrs = inner.ptrs.checked_sub(1)?;
                return Some(inner);
            }
            if let [(_, "&", _), rest @ ..] = expr {
                let mut inner = self.expr_type(rest, at, depth + 1, true)?;
                inner.ptrs += 1;
                return Some(inner);
            }
        }
        if let Some(prefix) = strip_trailing_subscript(expr) {
            let mut sub = self.resolve_aliases(self.expr_type(prefix, at, depth + 1, false)?);
            if sub.array {
                sub.array = false;
                return Some(sub);
            }
            sub.ptrs = sub.ptrs.checked_sub(1)?;
            return Some(sub);
        }
        if let Some(pointee) = smart_deref_call_type(expr) {
            return Some(TypeSpec {
                base: pointee.to_owned(),
                ptrs: 1,
                array: false,
            });
        }
        if let Some((op_pos, arrow)) = last_top_member_op(expr) {
            let left =
                self.resolve_aliases(self.expr_type(expr.get(..op_pos)?, at, depth + 1, false)?);
            let field_tok = expr.get(op_pos + 1)?;
            if expr.len() != op_pos + 2 || field_tok.0 != Piece::Token(Lex::Name) {
                return None;
            }
            if left.ptrs != usize::from(arrow) || left.array {
                return None;
            }
            return self.member_type(&left.base, field_tok.1);
        }
        let [(Piece::Token(Lex::Name), var, _)] = expr else {
            return None;
        };
        self.ident_type(var, at)
    }

    /// Resolves the aggregate or pointer type of a single identifier `var`.
    ///
    /// # Arguments
    ///
    /// * `var` - Identifier text.
    /// * `at` - Enclosing line and scope.
    fn ident_type(&self, var: &str, at: &At<'_>) -> Option<TypeSpec> {
        if let Some(raw) = self.scope_var_spec(var, at) {
            let resolved = self.resolve_aliases(raw);
            if self.is_named_aggregate(&resolved.base) {
                return Some(resolved);
            }
        }
        if let Some(owner) = at.scope.owner
            && let Some(f) = self.analysis.function(owner)
        {
            if var == "this"
                && let Some(cls) =
                    crate::analysis::stated::object_class(self.analysis, self.overlay, f)
            {
                return Some(TypeSpec {
                    base: cls,
                    ptrs: 1,
                    array: false,
                });
            }
            if let Some(idx) = var
                .strip_prefix('a')
                .and_then(|d| d.parse::<u8>().ok())
                .and_then(|k| k.checked_sub(1))
                && let Some(cls) = f.param_hints.get(&idx)
            {
                return Some(TypeSpec {
                    base: cls.clone(),
                    ptrs: 1,
                    array: false,
                });
            }
        }
        if let Some(tag) = self.inferred_ptr_tag(var, at) {
            return Some(TypeSpec {
                base: tag,
                ptrs: 1,
                array: false,
            });
        }
        if let Some(spec) = self.types.globals.get(var) {
            return Some(spec.clone());
        }
        if let Some(spelled) = typelib::data_type(var, self.program.format)
            && let Some(spec) = spec_from_str(spelled)
        {
            return Some(spec);
        }
        if let Some(spec) = self.applied_global_spec(var, at.scope.facts) {
            return Some(spec);
        }
        if let Some((prefix, tail)) = var.rsplit_once("::")
            && tail == self.analysis.packs.name_for("singleton")
            && self.is_named_aggregate(prefix)
        {
            return Some(TypeSpec {
                base: prefix.to_owned(),
                ptrs: 1,
                array: false,
            });
        }
        None
    }

    /// Looks up a user-applied global type for `var` without noting whole
    /// overlay tables.
    ///
    /// # Arguments
    ///
    /// * `var` - Global identifier text.
    /// * `facts` - Enclosing function's reference facts.
    fn applied_global_spec(&self, var: &str, facts: Option<&Facts<'_>>) -> Option<TypeSpec> {
        let facts = facts?;
        let va = global_addr(var)
            .filter(|a| facts.refs.contains(a))
            .or_else(|| {
                facts
                    .data_map(self.program, self.analysis, self.overlay)
                    .get(var)
                    .copied()
                    .flatten()
            })?;
        let expr = self.overlay.applied.get(&va)?;
        Some(spec_from_expr(expr))
    }

    /// Returns any SDK struct tag or smart-pointer class inferred from calls or
    /// assignments to `var` within `at`'s owning body.
    ///
    /// # Arguments
    ///
    /// * `var` - Variable identifier.
    /// * `at` - Enclosing line and scope.
    fn inferred_ptr_tag(&self, var: &str, at: &At<'_>) -> Option<String> {
        match at.role {
            Role::Body => self
                .types
                .inferred_ptrs
                .get_or_init(|| infer_body_ptrs(self.body, self.program.format))
                .get(var)
                .cloned(),
            Role::Inline => {
                let Ok(mut slot) = self.types.inline_ptrs.try_borrow_mut() else {
                    return None;
                };
                if slot.as_ref().is_none_or(|(idx, _)| *idx != at.i) {
                    let map = inline_body_lines(at.line, at.pieces)
                        .map(|src| infer_body_ptrs(&src, self.program.format))
                        .unwrap_or_default();
                    *slot = Some((at.i, map));
                }
                slot.as_ref().and_then(|(_, map)| map.get(var).cloned())
            }
            Role::Header
            | Role::Signature
            | Role::Prototype
            | Role::Macro
            | Role::Struct
            | Role::Item
            | Role::Declaration => None,
        }
    }

    /// Looks up the [`TypeSpec`] of member `field` inside aggregate `ty` for
    /// chained accesses (`a->b->c` or `a->b.c`).
    ///
    /// # Arguments
    ///
    /// * `ty` - Aggregate type name.
    /// * `field` - Intermediate member name.
    fn member_type(&self, ty: &str, field: &str) -> Option<TypeSpec> {
        if let Some(UserType::Struct(s)) = self.overlay.types.get(ty)
            && let Some((off, spec)) = unique_user_field_type(s, field)
        {
            return self.offset_fits(ty, off).then_some(spec);
        }
        if let Some(UserType::Struct(s)) = self.program.debug_types.get(ty)
            && let Some((off, spec)) = unique_user_field_type(s, field)
        {
            return self.offset_fits(ty, off).then_some(spec);
        }
        if let Some(u) = self.types.unit_structs.get(ty) {
            let mut hits = u.fields.iter().filter(|f| f.name == field);
            if let (Some(one), None) = (hits.next(), hits.next()) {
                return self.offset_fits(ty, one.offset).then(|| one.spec.clone());
            }
        }
        if let Some(s) = sdk::structure(ty) {
            let word_bytes = if self.word_bits == 64 { 8 } else { 4 };
            let mut hits = s
                .at(word_bytes)
                .into_iter()
                .filter(|(_, f)| f.name == field);
            if let (Some((off, one)), None) = (hits.next(), hits.next()) {
                return self.offset_fits(ty, off).then(|| spec_from_str(one.ty))?;
            }
        }
        if let Some(fields) = self.overlay.fields.get(ty) {
            let mut hits = fields.iter().filter(|(_, f)| f.name == field);
            if let (Some((&off, one)), None) = (hits.next(), hits.next()) {
                return self
                    .offset_fits(ty, off)
                    .then(|| one.ty.as_ref().map(spec_from_expr))?;
            }
        }
        None
    }

    /// Resolves a named field `field` on aggregate `ty` to its offset and checks
    /// [`Self::offset_fits`].
    ///
    /// # Arguments
    ///
    /// * `ty` - Aggregate type name.
    /// * `field` - Member identifier.
    /// * `tally` - Counts ambiguous and out-of-bounds members.
    fn lookup_named_field(
        &self,
        ty: &str,
        field: &str,
        tally: &mut Tally,
    ) -> (Kind, Option<Ref>, bool) {
        let mut offsets = BTreeSet::new();
        if let Some(UserType::Struct(s)) = self.overlay.types.get(ty) {
            for (&off, f) in &s.fields {
                if f.name == field {
                    offsets.insert(off);
                }
            }
        } else if let Some(UserType::Struct(s)) = self.program.debug_types.get(ty) {
            for (&off, f) in &s.fields {
                if f.name == field {
                    offsets.insert(off);
                }
            }
        }
        if offsets.is_empty()
            && let Some(u) = self.types.unit_structs.get(ty)
        {
            for f in &u.fields {
                if f.name == field {
                    offsets.insert(f.offset);
                }
            }
        }
        if offsets.is_empty()
            && let Some(s) = sdk::structure(ty)
        {
            let word_bytes = if self.word_bits == 64 { 8 } else { 4 };
            for (off, f) in s.at(word_bytes) {
                if f.name == field {
                    offsets.insert(off);
                }
            }
        }
        if offsets.is_empty() {
            let map = tally.class_fields.entry(ty.to_owned()).or_insert_with(|| {
                classes::field_names(self.program, self.analysis, self.overlay, ty)
            });
            for (&off, name) in map.iter() {
                if name == field {
                    offsets.insert(off);
                }
            }
        }
        match offsets.len() {
            0 => (Kind::Field, None, false),
            1 => {
                let off = offsets.into_iter().next().unwrap_or(0);
                if self.offset_fits(ty, off) {
                    (
                        Kind::Field,
                        Some(Ref::Field {
                            ty: Some(ty.into()),
                            offset: off,
                        }),
                        false,
                    )
                } else {
                    tally.unlinked.uncorroborated += 1;
                    (Kind::Field, None, false)
                }
            }
            _ => {
                tally.unlinked.ambiguous += 1;
                (Kind::Field, None, false)
            }
        }
    }

    /// Tells whether `w` is a `#define`d constant, enum member or platform
    /// constant.
    ///
    /// # Arguments
    ///
    /// * `w` - Candidate identifier text.
    /// * `call` - Whether `(` immediately follows `w`.
    /// * `facts` - Enclosing function's reference facts.
    pub(super) fn is_constant(&self, w: &str, call: bool, facts: Option<&Facts<'_>>) -> bool {
        if call {
            return w == "HRESULT_FROM_WIN32";
        }
        if self.declared.constants.contains(w)
            || crate::winconst::is_constant(w)
            || typelib::is_constant(w, self.program.format)
        {
            return true;
        }
        let members = self
            .types
            .enum_members
            .get_or_init(|| self.collect_enum_members(facts));
        members.contains(w)
    }

    /// Gathers enum member names active in [`Self::text`] without noting whole
    /// overlay maps.
    ///
    /// # Arguments
    ///
    /// * `facts` - Enclosing function's reference facts.
    fn collect_enum_members(&self, facts: Option<&Facts<'_>>) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        if let Some(listed) = enums::listed_enum(self.text) {
            for (_, name) in listed.members {
                out.insert(name);
            }
        }
        for spec in self.types.params.values().chain(self.types.locals.values()) {
            let resolved = self.resolve_aliases(spec.clone());
            self.push_named_enum_values(&resolved.base, &mut out);
        }
        if let Some(f) = facts {
            for &va in &f.refs {
                let Some(expr) = self.overlay.applied.get(&va) else {
                    continue;
                };
                let spec = self.resolve_aliases(spec_from_expr(expr));
                self.push_named_enum_values(&spec.base, &mut out);
                if let Some(UserType::Struct(s)) = self.overlay.types.get(&spec.base) {
                    for field in s.fields.values() {
                        let fspec = self.resolve_aliases(spec_from_expr(&field.ty));
                        self.push_named_enum_values(&fspec.base, &mut out);
                    }
                }
            }
        }
        match self.overlay.enum_source {
            EnumSource::Binary => {
                for table in
                    enums::called_tables(self.program, self.analysis, self.overlay, self.text)
                        .into_values()
                {
                    for (_, m) in table.members {
                        out.insert(m);
                    }
                }
            }
            EnumSource::Given => {
                for callee in called_names_in(self.text) {
                    if let Some(table) = self.overlay.enums.get(&callee) {
                        for (_, m) in &table.members {
                            out.insert(m.clone());
                        }
                    }
                }
            }
        }
        out
    }

    /// Appends member names when `name` resolves to a [`UserType::Enum`] in the
    /// overlay or debug information.
    ///
    /// # Arguments
    ///
    /// * `name` - Resolved base type name.
    /// * `out` - Destination set of enum member names.
    fn push_named_enum_values(&self, name: &str, out: &mut BTreeSet<String>) {
        if let Some(UserType::Enum(e)) = self
            .overlay
            .types
            .get(name)
            .or_else(|| self.program.debug_types.get(name))
        {
            for (_, m) in &e.values {
                out.insert(m.clone());
            }
        }
    }
}

/// Returns the unique `(offset, TypeSpec)` of `field` inside `s`, or `None`
/// when zero or multiple fields share that name.
///
/// # Arguments
///
/// * `s` - User or debug struct layout.
/// * `field` - Member identifier.
fn unique_user_field_type(s: &UserStruct, field: &str) -> Option<(u64, TypeSpec)> {
    let mut hits = s.fields.iter().filter(|(_, f)| f.name == field);
    let (&off, one) = hits.next()?;
    hits.next()
        .is_none()
        .then(|| (off, spec_from_expr(&one.ty)))
}

/// Extracts up to [`RECEIVER_TOKENS_MAX`] code tokens belonging to the postfix
/// operand immediately before `->` or `.` at `op_piece`.
///
/// # Arguments
///
/// * `line` - Source line.
/// * `pieces` - Scanned pieces of `line`.
/// * `op_piece` - Piece index of `->` or `.`.
fn code_before_op<'t>(line: &'t str, pieces: &[Spanned], op_piece: usize) -> Vec<Tok<'t>> {
    let Some(head) = pieces.get(..op_piece) else {
        return Vec::new();
    };
    let (mut parens, mut brackets) = (0usize, 0usize);
    let mut rev_toks = Vec::new();
    for (p, r) in head.iter().rev() {
        if matches!(p, Piece::Space | Piece::Comment) {
            continue;
        }
        let w = line.get(r.clone()).unwrap_or("");
        match w {
            ")" => parens += 1,
            "]" => brackets += 1,
            "(" => {
                if parens == 0 {
                    break;
                }
                parens -= 1;
            }
            "[" => {
                if brackets == 0 {
                    break;
                }
                brackets -= 1;
            }
            _ if parens == 0 && brackets == 0 && is_expr_boundary(w) => break,
            _ => {}
        }
        if rev_toks.len() >= RECEIVER_TOKENS_MAX {
            return Vec::new();
        }
        rev_toks.push((*p, w, r.clone()));
    }
    rev_toks.reverse();
    rev_toks
}

/// Tells whether `w` separates a member-access receiver from surrounding C
/// statements, binary operators or lower-precedence prefix unary operators.
///
/// # Arguments
///
/// * `w` - Punctuation or keyword token text.
fn is_expr_boundary(w: &str) -> bool {
    matches!(
        w,
        ";" | ","
            | "{"
            | "}"
            | "?"
            | ":"
            | "="
            | "+="
            | "-="
            | "*="
            | "/="
            | "%="
            | "&="
            | "|="
            | "^="
            | "<<="
            | ">>="
            | "=="
            | "!="
            | "<"
            | "<="
            | ">"
            | ">="
            | "&&"
            | "||"
            | "+"
            | "-"
            | "*"
            | "&"
            | "++"
            | "--"
            | "/"
            | "%"
            | "|"
            | "^"
            | "<<"
            | ">>"
            | "!"
            | "~"
            | "return"
            | "case"
            | "sizeof"
    )
}

/// Strips one balanced outer `(...)` pair when it wraps the whole slice.
///
/// # Arguments
///
/// * `expr` - Expression token slice.
fn strip_outer_parens<'a, 't>(expr: &'a [Tok<'t>]) -> Option<&'a [Tok<'t>]> {
    if expr.first()?.1 != "(" || expr.last()?.1 != ")" {
        return None;
    }
    let mut depth = 0usize;
    for (i, (_, w, _)) in expr.iter().enumerate() {
        match *w {
            "(" => depth += 1,
            ")" => {
                depth = depth.checked_sub(1)?;
                if depth == 0 && i + 1 < expr.len() {
                    return None;
                }
            }
            _ => {}
        }
    }
    (depth == 0).then(|| &expr[1..expr.len() - 1])
}

/// Splits a leading `(head)tail` group when `tail` is non-empty.
///
/// # Arguments
///
/// * `expr` - Expression token slice.
fn split_leading_paren_group<'a, 't>(
    expr: &'a [Tok<'t>],
) -> Option<(&'a [Tok<'t>], &'a [Tok<'t>])> {
    if expr.first()?.1 != "(" {
        return None;
    }
    let mut depth = 0usize;
    let mut close = None;
    for (i, (_, w, _)) in expr.iter().enumerate() {
        match *w {
            "(" => depth += 1,
            ")" => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    close = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close?;
    let cast = expr.get(1..close)?;
    let tail = expr.get(close + 1..)?;
    (!cast.is_empty() && !tail.is_empty()).then_some((cast, tail))
}

/// Tells whether `tokens` spell a C scalar or pointer cast type (`uint64_t`,
/// `const struct Foo *`).
///
/// # Arguments
///
/// * `tokens` - Tokens inside `(...)`.
fn is_cast_type_tokens(tokens: &[Tok<'_>]) -> bool {
    let mut has_base = false;
    for (p, w, _) in tokens {
        match *w {
            "*" | "&" => {}
            _ if is_qualifier_or_tag(w) => {}
            _ if *p == Piece::Token(Lex::Name) => has_base = true,
            _ => return false,
        }
    }
    has_base
}

/// Splits a leading C pointer cast `(Type *)inner` into `(cast_tokens, inner)`.
///
/// # Arguments
///
/// * `expr` - Expression token slice.
fn strip_leading_cast<'a, 't>(expr: &'a [Tok<'t>]) -> Option<(&'a [Tok<'t>], &'a [Tok<'t>])> {
    let (cast, tail) = split_leading_paren_group(expr)?;
    cast.iter()
        .any(|(_, w, _)| matches!(*w, "*" | "&"))
        .then_some((cast, tail))
}

/// Tells whether `expr` is a single C unary/postfix cast operand with no
/// top-level binary, ternary, assignment or comma operators.
///
/// # Arguments
///
/// * `expr` - Operand tokens following `(Type *)`.
fn is_cast_operand(mut expr: &[Tok<'_>]) -> bool {
    loop {
        if let Some((cast, rest)) = split_leading_paren_group(expr)
            && is_cast_type_tokens(cast)
        {
            expr = rest;
            continue;
        }
        if let [(_, op, _), rest @ ..] = expr
            && matches!(*op, "*" | "&" | "+" | "-" | "~" | "!" | "++" | "--")
        {
            expr = rest;
            continue;
        }
        break;
    }
    let Some((first_p, first_w, _)) = expr.first() else {
        return false;
    };
    let mut idx = if *first_w == "(" {
        let Some(end) = matching_delim(expr, 0, "(", ")") else {
            return false;
        };
        end + 1
    } else if matches!(
        first_p,
        Piece::Token(Lex::Name | Lex::Number | Lex::Literal)
    ) {
        1
    } else {
        return false;
    };
    while let Some((_, w, _)) = expr.get(idx) {
        match *w {
            "[" => match matching_delim(expr, idx, "[", "]") {
                Some(end) => idx = end + 1,
                None => return false,
            },
            "(" => match matching_delim(expr, idx, "(", ")") {
                Some(end) => idx = end + 1,
                None => return false,
            },
            "->" | "." => match expr.get(idx + 1) {
                Some((Piece::Token(Lex::Name), _, _)) => idx += 2,
                _ => return false,
            },
            "++" | "--" => idx += 1,
            _ => return false,
        }
    }
    true
}

/// Finds the index of the closing delimiter matching `open` at `start`.
///
/// # Arguments
///
/// * `expr` - Token slice.
/// * `start` - Index of `open`.
/// * `open` - Opening delimiter (`"("` or `"["`).
/// * `close` - Closing delimiter (`")"` or `"]"`).
fn matching_delim(expr: &[Tok<'_>], start: usize, open: &str, close: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (rel, (_, w, _)) in expr.get(start..)?.iter().enumerate() {
        if *w == open {
            depth += 1;
        } else if *w == close {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some(start + rel);
            }
        }
    }
    None
}

/// Parses a cast's inner tokens (`struct Foo *`) into a [`TypeSpec`].
///
/// # Arguments
///
/// * `tokens` - Tokens inside `(...)` of a cast.
fn spec_from_tokens(tokens: &[Tok<'_>]) -> Option<TypeSpec> {
    let mut base_words = Vec::new();
    let mut ptrs = 0usize;
    for (p, w, _) in tokens {
        match *w {
            "*" | "&" => ptrs += 1,
            _ if is_qualifier_or_tag(w) => {}
            _ if *p == Piece::Token(Lex::Name) => base_words.push(*w),
            _ => return None,
        }
    }
    (!base_words.is_empty() && ptrs > 0).then(|| TypeSpec {
        base: base_words.join(" "),
        ptrs,
        array: false,
    })
}

/// Strips a trailing `[...]` subscript from `expr`, returning the prefix.
///
/// # Arguments
///
/// * `expr` - Expression token slice.
fn strip_trailing_subscript<'a, 't>(expr: &'a [Tok<'t>]) -> Option<&'a [Tok<'t>]> {
    if expr.last()?.1 != "]" {
        return None;
    }
    let mut depth = 0usize;
    for (i, (_, w, _)) in expr.iter().enumerate().rev() {
        match *w {
            "]" => depth += 1,
            "[" => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return (i > 0).then_some(&expr[..i]);
                }
            }
            _ => {}
        }
    }
    None
}

/// Finds the last top-level `->` or `.` operator in `expr`.
///
/// # Arguments
///
/// * `expr` - Expression token slice.
fn last_top_member_op(expr: &[Tok<'_>]) -> Option<(usize, bool)> {
    let (mut parens, mut brackets) = (0usize, 0usize);
    for (i, (_, w, _)) in expr.iter().enumerate().rev() {
        match *w {
            ")" => parens += 1,
            "(" => parens = parens.saturating_sub(1),
            "]" => brackets += 1,
            "[" => brackets = brackets.saturating_sub(1),
            "->" if parens == 0 && brackets == 0 && i > 0 => return Some((i, true)),
            "." if parens == 0 && brackets == 0 && i > 0 => return Some((i, false)),
            _ => {}
        }
    }
    None
}

/// Extracts the pointee class from an inline `SmartPtr<T>::operator ->(...)`
/// call expression.
///
/// # Arguments
///
/// * `expr` - Expression token slice.
fn smart_deref_call_type<'t>(expr: &[Tok<'t>]) -> Option<&'t str> {
    if expr.last()?.1 != ")" {
        return None;
    }
    let mut depth = 0usize;
    let mut open = None;
    for (i, (_, w, _)) in expr.iter().enumerate().rev() {
        match *w {
            ")" => depth += 1,
            "(" => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    open = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let head = expr.get(..open?)?;
    if let [(_, op_name, _), (_, "->", _)] | [(_, "::", _), (_, op_name, _), (_, "->", _)] = head {
        let cls = op_name.strip_suffix("::operator")?;
        return classes::smart_pointee(cls);
    }
    None
}

/// Extracts the `{ ... }` body of a one-line `static inline` definition with
/// top-level `;` statement separators expanded onto separate lines.
///
/// # Arguments
///
/// * `line` - One-line `static inline` source line.
/// * `pieces` - Scanned pieces of `line`.
///
/// # Returns
///
/// Statement lines separated by `\n`, or `None` when no `{ ... }` block is found.
fn inline_body_lines(line: &str, pieces: &[Spanned]) -> Option<String> {
    let open = pieces
        .iter()
        .position(|(p, r)| *p == Piece::Token(Lex::Punct) && line.get(r.clone()) == Some("{"))?;
    let close = pieces
        .iter()
        .rposition(|(p, r)| *p == Piece::Token(Lex::Punct) && line.get(r.clone()) == Some("}"))?;
    if close <= open {
        return None;
    }
    let body_start = pieces.get(open)?.1.end;
    let body_end = pieces.get(close)?.1.start;
    let mut out = String::with_capacity(body_end.saturating_sub(body_start).saturating_add(8));
    let mut cursor = body_start;
    for (p, r) in &pieces[open + 1..close] {
        if *p == Piece::Token(Lex::Punct) && line.get(r.clone()) == Some(";") {
            out.push_str(line.get(cursor..r.end).unwrap_or(""));
            out.push('\n');
            cursor = r.end;
        }
    }
    if cursor < body_end {
        out.push_str(line.get(cursor..body_end).unwrap_or(""));
    }
    Some(out)
}

/// Scans body lines for single-assigned SDK structure pointers
/// ([`api_pointee_tags`]) and smart-pointer dereference assignments
/// (`x = Ptr<T>::operator ->(...)`).
///
/// # Arguments
///
/// * `text` - Full decompile text.
/// * `format` - Binary format for platform API declarations.
fn infer_body_ptrs(text: &str, format: BinaryFormat) -> BTreeMap<String, String> {
    let mut out: BTreeMap<String, String> = api_pointee_tags(text, format)
        .into_iter()
        .map(|(k, v)| (k.to_owned(), v.to_owned()))
        .collect();
    if !text.contains(">::operator ->(") {
        return out;
    }
    let mut assigned_counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut smart_found: BTreeMap<&str, Option<&str>> = BTreeMap::new();
    let mut pieces = Vec::new();
    let mut in_comment = false;
    for line in text.lines() {
        let Some(code_at) = super::super::fields::step_block_comment(line, &mut in_comment) else {
            continue;
        };
        let t = line.get(code_at..).unwrap_or("").trim();
        super::super::fields::note_line_writes(t, &mut assigned_counts);
        if !t.contains(" = ") {
            continue;
        }
        let stmt = if t.contains("//") || t.contains("/*") {
            super::split(t, 0, &mut pieces);
            let end = pieces
                .iter()
                .rposition(|(p, _)| !matches!(p, Piece::Space | Piece::Comment))
                .and_then(|k| pieces.get(k))
                .map_or(0, |(_, r)| r.end);
            t.get(..end).unwrap_or("")
        } else {
            t
        };
        if let Some((lhs, rhs)) = stmt.strip_suffix(';').and_then(|s| s.split_once(" = "))
            && is_ident(lhs)
            && !lhs.starts_with(|c: char| c.is_ascii_digit())
        {
            let cls = rhs.contains(">::operator ->(").then(|| {
                super::split(rhs, 0, &mut pieces);
                let rhs_toks = code(rhs, &pieces);
                let mut expr: &[Tok<'_>] = &rhs_toks;
                for _ in 0..EXPR_DEPTH_MAX {
                    let Some(inner) = strip_outer_parens(expr) else {
                        break;
                    };
                    expr = inner;
                }
                smart_deref_call_type(expr)
            });
            if let Some(Some(cls)) = cls {
                smart_found
                    .entry(lhs)
                    .and_modify(|prev| {
                        if *prev != Some(cls) {
                            *prev = None;
                        }
                    })
                    .or_insert(Some(cls));
            } else {
                smart_found.insert(lhs, None);
            }
        }
    }
    for (var, cls) in smart_found {
        if let Some(cls) = cls
            && assigned_counts.get(var).copied().unwrap_or(0) == 1
        {
            out.entry(var.to_owned()).or_insert_with(|| cls.to_owned());
        }
    }
    out
}

/// Collects distinct callee display names appearing immediately before `(` in
/// `text`.
///
/// # Arguments
///
/// * `text` - Full decompile text.
fn called_names_in(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut pieces = Vec::new();
    let mut in_comment = false;
    for line in text.lines() {
        let Some(code_at) = super::super::fields::step_block_comment(line, &mut in_comment) else {
            continue;
        };
        super::split(line, code_at, &mut pieces);
        let toks = code(line, &pieces);
        for pair in toks.windows(2) {
            if let [(Piece::Token(Lex::Name), callee, _), (_, "(", _)] = pair {
                out.insert((*callee).to_owned());
            }
        }
    }
    out
}
