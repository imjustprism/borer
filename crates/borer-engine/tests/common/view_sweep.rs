//! Outside link corroboration and token census for the `dogfood` view sweep.

use std::collections::{BTreeMap, BTreeSet};

use borer_engine::analysis::decompile::view::literal_at;
use borer_engine::analysis::decompile::{declarations_end, virtual_callees};
use borer_engine::analysis::utypes::UserType;
use borer_engine::analysis::{Analysis, Overlay, name_of, sdk};
use borer_engine::program::{BinaryFormat, Program, SymbolKind};
use borer_engine::view::{Kind, Ref, View};

/// Spells a function's or an import's name as a text does: without its module
/// prefix, the `.`, `$` and `@` of a C name turned to `_`, a qualified name
/// kept whole.
///
/// # Arguments
///
/// * `name` - Raw symbol or display name.
pub(super) fn spelled(name: &str) -> String {
    let name = borer_engine::analysis::bare_name(name);
    if name.contains("::") || name.contains('(') {
        name.to_owned()
    } else {
        name.replace(['.', '$', '@'], "_")
    }
}

/// Returns how many discovered functions and imports go by each spelling.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
pub(super) fn spellings(p: &Program, a: &Analysis) -> BTreeMap<String, usize> {
    let o = Overlay::default();
    let mut by = BTreeMap::new();
    let imports: BTreeSet<&str> = p
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| s.name.as_str())
        .collect();
    let functions = a
        .functions
        .iter()
        .filter(|f| f.thunk.is_none())
        .map(|f| spelled(&name_of(a, &o, f.entry)));
    let imports = imports
        .into_iter()
        .map(|n| spelled(&borer_engine::search::demangled_name(n)));
    for name in functions.chain(imports) {
        *by.entry(name).or_insert(0) += 1;
    }
    by
}

/// Parses `field_0x<hex>` into its byte offset.
///
/// # Arguments
///
/// * `word` - Candidate token spelling.
fn parse_field_hex(word: &str) -> Option<u64> {
    let hex = word.strip_prefix("field_0x")?;
    (!hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit()))
        .then(|| u64::from_str_radix(hex, 16).ok())
        .flatten()
}

/// Tells whether `offset` lies strictly below `ty`'s known debug or SDK size.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `ty` - Aggregate type name.
/// * `offset` - Linked byte offset.
fn field_offset_below_size(p: &Program, ty: &str, offset: u64) -> bool {
    if let Some(UserType::Struct(s)) = p.debug_types.get(ty)
        && s.size > 0
    {
        return offset < s.size;
    }
    if let Some(s) = sdk::structure(ty) {
        let sz = if p.is_64 { Some(s.size64) } else { s.size32 };
        if let Some(sz) = sz.filter(|&n| n > 0) {
            return offset < sz;
        }
    }
    true
}

/// Corroborates a named member token `tok` against `ty`'s declared debug, SDK
/// or recovered class layout at `offset`, falling back to `unit_defined` only
/// when none of those layouts governs `(ty, tok)`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its analysis.
/// * `ty` - Aggregate type name.
/// * `tok` - Member identifier text.
/// * `offset` - Linked byte offset.
/// * `unit_defined` - Whether the view's header defines `struct ty`.
fn named_field_matches(
    p: &Program,
    a: &Analysis,
    ty: &str,
    tok: &str,
    offset: u64,
    unit_defined: bool,
) -> bool {
    let debug_struct = match p.debug_types.get(ty) {
        Some(UserType::Struct(s)) if !s.fields.is_empty() => {
            if s.fields.values().any(|f| f.name == tok) {
                return s.fields.get(&offset).is_some_and(|f| f.name == tok);
            }
            true
        }
        _ => false,
    };
    let sdk_struct = if !p.debug_types.contains_key(ty)
        && let Some(s) = sdk::structure(ty)
    {
        let at = s.at(if p.is_64 { 8 } else { 4 });
        if at.iter().any(|(_, f)| f.name == tok) {
            return at.iter().any(|(off, f)| *off == offset && f.name == tok);
        }
        !at.is_empty()
    } else {
        false
    };
    let class_fields = borer_engine::analysis::classes::field_names(p, a, &Overlay::default(), ty);
    if class_fields.values().any(|n| n == tok) {
        return class_fields.get(&offset).is_some_and(|n| n == tok);
    }
    if debug_struct || sdk_struct {
        return false;
    }
    unit_defined
}

/// Resolves the function scope of line `line` inside `entry`'s view.
///
/// # Arguments
///
/// * `entry` - Enclosing function entry.
/// * `line` - Source line text.
/// * `tokens` - Tokens of `line`.
fn line_scope(
    entry: u64,
    line: &str,
    tokens: &[(std::ops::Range<usize>, Kind, Option<&Ref>)],
) -> Option<u64> {
    if !line.starts_with("static inline ") {
        return Some(entry);
    }
    let named = tokens.iter().find(|(_, kind, _)| *kind == Kind::Function);
    named.and_then(|(.., link)| match link {
        Some(Ref::Function(g)) => Some(*g),
        _ => None,
    })
}

/// Checks whether one linked token `(tok, r)` on line `i` is borne out by
/// facts outside the view.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `entry` - Function entry the view was built for.
/// * `scope` - Function scope of the current line.
/// * `decls` - Line index ending the header and declaration block.
/// * `v` - The view.
/// * `tok` - Exact token slice.
/// * `r` - Linked target.
/// * `referenced` - Reference-target predicate for `scope`.
/// * `virtuals` - Lazily populated virtual callees of `entry`.
#[expect(
    clippy::too_many_arguments,
    reason = "shares per-function caches across every token of the view"
)]
fn link_ok(
    p: &Program,
    a: &Analysis,
    entry: u64,
    scope: Option<u64>,
    decls: usize,
    v: &View,
    tok: &str,
    r: &Ref,
    referenced: &dyn Fn(u64) -> bool,
    virtuals: &mut Option<Vec<u64>>,
) -> bool {
    let f = scope.and_then(|s| a.function(s));
    match r {
        Ref::Function(e) => {
            Some(*e) == scope
                || f.is_some_and(|f| {
                    f.callees.contains(e)
                        || f.callees
                            .iter()
                            .any(|c| a.function(*c).and_then(|g| g.bound) == Some(*e))
                })
                || referenced(*e)
                || (scope == Some(entry)
                    && virtuals
                        .get_or_insert_with(|| virtual_callees(p, a, &Overlay::default(), entry))
                        .contains(e))
        }
        Ref::Import(s) => {
            let stub = f.is_some_and(|f| {
                f.callees
                    .iter()
                    .any(|c| a.function(*c).and_then(|g| g.thunk) == Some(*s))
            });
            (referenced(*s) || stub)
                && p.symbols
                    .iter()
                    .any(|y| y.kind == SymbolKind::Import && y.addr == *s)
        }
        Ref::Address(va) => f.is_some_and(|f| f.blocks.iter().any(|b| b.start == *va)),
        Ref::Global(va) => {
            let mapped = p.section_at(*va).is_some()
                || p.zero_fill_at(*va).is_some()
                || p.in_headers(*va)
                || (p.format == BinaryFormat::Pe && *va == p.image_base);
            mapped && referenced(*va)
        }
        Ref::String(va) => {
            let own = scope
                .map(|s| {
                    borer_engine::analysis::bare_name(&name_of(a, &Overlay::default(), s))
                        .to_owned()
                })
                .unwrap_or_default();
            p.section_at(*va).is_some()
                && referenced(*va)
                && literal_at(p, *va, &own).as_deref() == Some(tok)
        }
        Ref::Field { ty, offset } => {
            let size_ok = ty
                .as_deref()
                .is_none_or(|t| field_offset_below_size(p, t, *offset));
            let member_ok = if let Some(h) = parse_field_hex(tok) {
                h == *offset
            } else {
                ty.as_deref().is_none_or(|t| {
                    let unit_defined = (0..decls).any(|i| {
                        v.line(i)
                            .is_some_and(|l| l.starts_with(&format!("struct {t} ")))
                    });
                    named_field_matches(p, a, t, tok, *offset, unit_defined)
                })
            };
            size_ok && member_ok
        }
        Ref::Variable { function, name } => {
            Some(*function) == scope
                && v.definition(r).is_some_and(|d| {
                    v.line(d).is_some_and(|l| {
                        let declares = l.starts_with("// signature: ")
                            || l.starts_with("static inline ")
                            || d < decls;
                        declares
                            && l.split(|c: char| !c.is_alphanumeric() && c != '_')
                                .any(|w| w == &**name)
                    })
                })
        }
        Ref::Type(name) => v
            .definition(r)
            .is_some_and(|d| v.line(d).is_some_and(|l| l.contains(&**name))),
    }
}

/// Returns the ids `v` ships that outside facts of `entry` do not bear out.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `entry` - The function the view is of.
/// * `v` - The view.
/// * `text` - The text it read.
pub(super) fn unborne(p: &Program, a: &Analysis, entry: u64, v: &View, text: &str) -> Vec<String> {
    let decls = declarations_end(text).unwrap_or(0);
    let targets =
        |f: u64| -> BTreeSet<u64> { a.refs_from(f).into_iter().map(|(t, _)| t).collect() };
    let main = targets(entry);
    let mut virtuals: Option<Vec<u64>> = None;
    let mut bad = Vec::new();
    for i in 0..v.lines() {
        let line = v.line(i).unwrap_or_default();
        let tokens: Vec<_> = v.tokens(i).collect();
        let scope = line_scope(entry, line, &tokens);
        let inline = scope
            .filter(|s| *s != entry)
            .map(targets)
            .unwrap_or_default();
        let referenced = |at: u64| match scope {
            Some(s) if s == entry => main.contains(&at),
            Some(_) => inline.contains(&at),
            None => false,
        };
        for (span, _, link) in &tokens {
            let Some(r) = link else { continue };
            let tok = &line[span.clone()];
            if !link_ok(
                p,
                a,
                entry,
                scope,
                decls,
                v,
                tok,
                r,
                &referenced,
                &mut virtuals,
            ) {
                bad.push(format!("{entry:#x} line {i}: {tok} {r:?}"));
            }
        }
    }
    bad
}

/// Counts linked and unlinked tokens across all decompile views in a sweep.
#[derive(Debug, Default)]
pub(super) struct Census {
    /// Call tokens, and how many carry an id.
    pub(super) calls: (usize, usize),
    /// Call tokens whose spelling names exactly one discovered function or
    /// import, and how many carry an id.
    pub(super) resolvable: (usize, usize),
    /// Call tokens whose spelling names more than one.
    pub(super) ambiguous: usize,
    /// Variable, label, global, string-literal and field tokens `(total, linked)`.
    pub(super) kinds: [(usize, usize); 5],
    /// Non-ambiguous string-literal tokens and how many carry an id.
    pub(super) resolvable_strings: (usize, usize),
    /// `field_0x<hex>` member tokens `(total, linked_with_matching_offset)`.
    pub(super) field_hex: (usize, usize),
    /// Unlinked counts reported by `View::unlinked` `(uncorroborated, ambiguous)`.
    pub(super) counted: (usize, usize),
    /// First resolvable call tokens without an id.
    pub(super) examples: Vec<String>,
    /// Unlinked string-literal tokens tallied by cause.
    pub(super) string_causes: BTreeMap<&'static str, usize>,
    /// Sample unlinked string-literal tokens with their cause.
    pub(super) string_examples: Vec<String>,
}

impl Census {
    /// Adds one function's view to the census.
    ///
    /// # Arguments
    ///
    /// * `p` - The program.
    /// * `a` - Its analysis.
    /// * `entry` - Function entry.
    /// * `v` - Its view.
    /// * `by` - Function and import spelling counts ([`spellings`]).
    pub(super) fn add(
        &mut self,
        p: &Program,
        a: &Analysis,
        entry: u64,
        v: &View,
        by: &BTreeMap<String, usize>,
    ) {
        let mut ref_literals: BTreeMap<u64, BTreeMap<String, usize>> = BTreeMap::new();
        for i in 0..v.lines() {
            let line = v.line(i).unwrap_or_default();
            let tokens: Vec<_> = v.tokens(i).collect();
            let scope = line_scope(entry, line, &tokens);
            for (k, (span, kind, link)) in tokens.iter().enumerate() {
                let word = &line[span.clone()];
                let is_str_lit =
                    *kind == Kind::String && (word.starts_with('"') || word.starts_with("L\""));
                let slot = match kind {
                    Kind::Variable => Some(0),
                    Kind::Label => Some(1),
                    Kind::Global => Some(2),
                    Kind::String if is_str_lit => Some(3),
                    Kind::Field => Some(4),
                    Kind::Space
                    | Kind::Comment
                    | Kind::Keyword
                    | Kind::Constant
                    | Kind::Mnemonic
                    | Kind::Register
                    | Kind::Type
                    | Kind::Function
                    | Kind::Address
                    | Kind::String
                    | Kind::Number
                    | Kind::Punct
                    | Kind::Text => None,
                };
                if let Some(s) = slot {
                    self.kinds[s].0 += 1;
                    self.kinds[s].1 += usize::from(link.is_some());
                }
                if is_str_lit {
                    if link.is_some() {
                        self.resolvable_strings.0 += 1;
                        self.resolvable_strings.1 += 1;
                    } else {
                        let cause = classify_unlinked_string(p, a, scope, word, &mut ref_literals);
                        if cause != "ambiguous" {
                            self.resolvable_strings.0 += 1;
                        }
                        *self.string_causes.entry(cause).or_default() += 1;
                        if self.string_examples.len() < 10 {
                            self.string_examples
                                .push(format!("{entry:#x} line {i} ({cause}): {word}"));
                        }
                    }
                }
                if *kind == Kind::Field
                    && !line.starts_with("struct ")
                    && let Some(hex_off) = parse_field_hex(word)
                {
                    self.field_hex.0 += 1;
                    if matches!(link, Some(Ref::Field { offset, .. }) if *offset == hex_off) {
                        self.field_hex.1 += 1;
                    }
                }
                let opens = tokens
                    .get(k + 1)
                    .is_some_and(|(next, ..)| &line[next.clone()] == "(");
                if !opens || !matches!(kind, Kind::Function | Kind::Text) {
                    continue;
                }
                self.calls.0 += 1;
                self.calls.1 += usize::from(link.is_some());
                match by.get(word).copied().unwrap_or(0) {
                    0 => {}
                    1 => {
                        self.resolvable.0 += 1;
                        self.resolvable.1 += usize::from(link.is_some());
                        if link.is_none() && self.examples.len() < 10 {
                            self.examples.push(format!("{entry:#x} line {i}: {word}"));
                        }
                    }
                    _ => self.ambiguous += 1,
                }
            }
        }
        let counted = v.unlinked();
        self.counted.0 += counted.uncorroborated;
        self.counted.1 += counted.ambiguous;
    }
}

/// Classifies why string-literal token `word` in `scope` carried no link.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `scope` - Enclosing function entry, `None` for a helper line.
/// * `word` - Quoted string-literal token text.
/// * `cache` - Per-function map of referenced literal spellings to counts.
fn classify_unlinked_string(
    p: &Program,
    a: &Analysis,
    scope: Option<u64>,
    word: &str,
    cache: &mut BTreeMap<u64, BTreeMap<String, usize>>,
) -> &'static str {
    let Some(s) = scope else {
        return "helper_scope";
    };
    let counts = cache.entry(s).or_insert_with(|| {
        let own = borer_engine::analysis::bare_name(&name_of(a, &Overlay::default(), s)).to_owned();
        let refs: BTreeSet<u64> = a.refs_from(s).into_iter().map(|(t, _)| t).collect();
        let mut by = BTreeMap::new();
        for va in refs {
            if let Some(lit) = literal_at(p, va, &own) {
                *by.entry(lit).or_insert(0) += 1;
            }
        }
        by
    });
    if counts.get(word).copied().unwrap_or(0) >= 2 {
        "ambiguous"
    } else {
        "unreferenced"
    }
}

#[cfg(test)]
mod tests {
    use super::unborne;
    use borer_engine::analysis::decompile::view::view_of;
    use borer_engine::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
    use borer_engine::analysis::{Analysis, Overlay};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use std::collections::BTreeMap;

    /// Known debug and SDK field layouts reject wrong in-bounds member offsets even
    /// when the view's header also defines `struct T`, while keeping the fallback
    /// when no outside layout exists.
    #[test]
    fn header_defined_structs_still_check_known_debug_and_sdk_field_offsets() {
        const ENTRY: u64 = 0x1_4000_1000;
        let mut p = Program::raw(
            vec![0xc3],
            Arch::X86_64,
            0x1_4000_0000,
            Some(ENTRY),
            vec![Section::mapped(".text", ENTRY, 0, 1, false, true)],
        );
        p.format = BinaryFormat::Pe;
        let a = Analysis::compute(&p);

        let dbg_src = concat!(
            "// signature: uint32_t sub_140001000(struct Widget *a1)\n",
            "struct Widget { uint64_t pad; uint32_t count; };\n",
            "\n",
            "return a1->count;\n",
        );
        let v_dbg = view_of(&p, &a, &Overlay::default(), ENTRY, dbg_src).expect("view");
        assert!(unborne(&p, &a, ENTRY, &v_dbg, dbg_src).is_empty());

        let mut p_known = p.clone();
        p_known.debug_types.insert(
            "Widget".to_owned(),
            UserType::Struct(UserStruct {
                size: 0x10,
                fields: BTreeMap::from([(
                    0x4,
                    UserField {
                        name: "count".to_owned(),
                        ty: TypeExpr::U32,
                    },
                )]),
            }),
        );
        let bad_dbg = unborne(&p_known, &a, ENTRY, &v_dbg, dbg_src);
        assert_eq!(bad_dbg.len(), 1, "{bad_dbg:?}");

        let sdk_src = concat!(
            "// signature: int32_t sub_140001000(struct _RTL_CRITICAL_SECTION *a1)\n",
            "struct _RTL_CRITICAL_SECTION { int32_t LockCount; };\n",
            "\n",
            "return a1->LockCount;\n",
        );
        let v_sdk = view_of(&p, &a, &Overlay::default(), ENTRY, sdk_src).expect("sdk view");
        let bad_sdk = unborne(&p, &a, ENTRY, &v_sdk, sdk_src);
        assert_eq!(bad_sdk.len(), 1, "{bad_sdk:?}");

        const RDATA: u64 = 0x1_4000_2000;
        let expr_va = RDATA + 0x10;
        let sig_va = RDATA + 0x30;
        let mut code = vec![0x48, 0x83, 0xec, 0x28, 0x83, 0x79, 0x08, 0x00, 0x75, 0x14];
        for (op, target) in [
            (&[0x48u8, 0x8d, 0x0d][..], expr_va),
            (&[0x48u8, 0x8d, 0x15][..], sig_va),
            (&[0xffu8, 0x15][..], RDATA),
        ] {
            let next = ENTRY + u64::try_from(code.len() + op.len() + 4).expect("fits");
            let disp = i32::try_from(target.cast_signed() - next.cast_signed()).expect("near");
            code.extend_from_slice(op);
            code.extend_from_slice(&disp.to_le_bytes());
        }
        code.extend_from_slice(&[0x8b, 0x41, 0x08, 0x48, 0x83, 0xc4, 0x28, 0xc3]);
        let mut bytes = vec![0u8; 0x2000];
        bytes[..0x1000].fill(0xcc);
        bytes[..code.len()].copy_from_slice(&code);
        bytes[0x1010..0x1010 + 17].copy_from_slice(b"this->count != 0\0");
        bytes[0x1030..0x1030 + 30].copy_from_slice(b"void __cdecl Boxed::get(void)\0");
        let mut p_cls = Program::raw(
            bytes,
            Arch::X86_64,
            0x1_4000_0000,
            Some(ENTRY),
            vec![
                Section::mapped(".text", ENTRY, 0, 0x1000, false, true),
                Section::mapped(".rdata", RDATA, 0x1000, 0x1000, false, false),
            ],
        );
        p_cls.format = BinaryFormat::Pe;
        p_cls.symbols.push(borer_engine::program::Symbol {
            name: "TEST.dll!n_assert".to_owned(),
            addr: RDATA,
            kind: borer_engine::program::SymbolKind::Import,
        });
        let a_cls = Analysis::compute(&p_cls);
        assert!(!a_cls.classes.by_name.contains_key("Boxed"));
        let cls_src = "// signature: uint32_t Boxed::get(Boxed *this)\n\nreturn this->count;\n";
        let v_cls = view_of(&p_cls, &a_cls, &Overlay::default(), ENTRY, cls_src).expect("cls");
        assert!(unborne(&p_cls, &a_cls, ENTRY, &v_cls, cls_src).is_empty());
        let bad_cls_src = concat!(
            "// signature: uint32_t Boxed::get(struct Boxed *this)\n",
            "struct Boxed { uint32_t count; };\n\nreturn this->count;\n",
        );
        let v_bad_cls = view_of(&p, &a, &Overlay::default(), ENTRY, bad_cls_src).expect("bad cls");
        assert_eq!(
            unborne(&p_cls, &a_cls, ENTRY, &v_bad_cls, bad_cls_src).len(),
            1
        );
    }
}
