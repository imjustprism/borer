//! Definitions of the struct types and tables a finished text names.
//!
//! A text that reads `stdout->_IO_write_ptr` or `prec_table[i].prec_name`
//! names a struct's fields and a global array the debug information
//! states, and neither is C until the text defines them. Each struct whose
//! field the text names is defined on one line with the fields it names at
//! their offsets and padding between them, `struct _IO_FILE { uint8_t
//! pad_0[0x28]; char *_IO_write_ptr; ... };`, so the layout is the
//! binary's and the unit stays short; the typedef that names it (`FILE`)
//! is the translation-unit closure's ([`super::unit::close`]). Each table
//! the text indexes is declared `extern` at its stated length.

use std::collections::{BTreeMap, BTreeSet};

use crate::analysis::utypes::{TypeExpr, UserStruct, UserType, width_of};
use crate::program::Program;

use super::line::is_ident_char;

/// Most structs one text defines.
const STRUCTS_MAX: usize = 16;

/// Tells whether a line of a finished text is a struct definition
/// [`declare`] put there.
///
/// # Arguments
///
/// * `line` - The line.
pub(super) fn defines(line: &str) -> bool {
    line.starts_with("struct ") && line.ends_with("};") && line.contains(" { ")
}

/// Defines, after the header comments, each struct whose fields the text
/// names and declares each stated table it indexes.
///
/// A struct counts when the text names it (`FILE *`, `struct merge_node
/// *`, through a typedef or its tag) or a defined struct holds it, and the
/// text names one of its fields; one a defined struct or table holds by
/// value counts whatever it names. Its definition lists the named fields
/// only, each at its offset, with `uint8_t` padding for the bytes between
/// and after them, so the struct keeps its size. A table counts when the
/// text indexes it (`name[`) and declares it nowhere. A text that names
/// neither comes back unchanged.
///
/// # Arguments
///
/// * `text` - A finished decompilation.
/// * `program` - The image, with its debug information.
///
/// # Returns
///
/// The text with the definitions added.
pub(super) fn declare(text: &str, program: &Program) -> String {
    let types = &program.debug_types;
    if types.is_empty() && program.debug_globals.is_empty() {
        return text.to_owned();
    }
    let word = u64::from(program.arch.bitness().unwrap_or(64) / 8);
    let code: Vec<&str> = text
        .lines()
        .filter(|l| !l.trim_start().starts_with("//") || l.starts_with("// signature: "))
        .collect();
    let fields = member_names(&code);
    let words = words_of(&code);
    let mut tables: Vec<String> = Vec::new();
    let mut by_value: Vec<String> = Vec::new();
    for g in &program.debug_globals {
        let Some(t) = g
            .addr
            .and_then(|at| super::globals::table_holding(program, at))
            .filter(|t| Some(t.start) == g.addr)
        else {
            continue;
        };
        if !code.iter().any(|l| indexes(l, &g.name)) || tables.len() >= STRUCTS_MAX {
            continue;
        }
        let declaration = code.iter().find(|l| declares(l, &g.name));
        if let Some(tag) = t.declared.strip_prefix("struct ")
            && declaration.is_none_or(|l| l.contains(t.declared.as_str()))
        {
            by_value.push(tag.to_owned());
        }
        if declaration.is_none() {
            tables.push(format!("extern {} {}[{}];", t.declared, g.name, t.len));
        }
    }
    let mut roots: Vec<String> = Vec::new();
    for w in &words {
        let Some((tag, s)) = resolve(types, w) else {
            continue;
        };
        if s.fields.values().any(|f| fields.contains(f.name.as_str())) && !roots.contains(&tag) {
            roots.push(tag);
        }
    }
    let mut out = Defs {
        types,
        fields: &fields,
        word,
        done: BTreeSet::new(),
        lines: Vec::new(),
    };
    for tag in &by_value {
        out.define(tag, true, 0);
    }
    for tag in &roots {
        out.define(tag, false, 0);
    }
    if out.lines.is_empty() && tables.is_empty() {
        return text.to_owned();
    }
    let mut lines: Vec<&str> = text.lines().collect();
    let at = lines.iter().take_while(|l| l.starts_with("//")).count();
    let added: Vec<String> = out.lines.into_iter().chain(tables).collect();
    lines.splice(at..at, added.iter().map(String::as_str));
    let mut joined = lines.join("\n");
    joined.push('\n');
    joined
}

/// The struct definitions of one text under construction.
struct Defs<'t> {
    /// The debug information's types.
    types: &'t BTreeMap<String, UserType>,
    /// The field names the text uses.
    fields: &'t BTreeSet<&'t str>,
    /// The image's pointer width in bytes.
    word: u64,
    /// The struct tags already defined, or being defined.
    done: BTreeSet<String>,
    /// The definitions, each struct after the ones it holds by value.
    lines: Vec<String>,
}

impl Defs<'_> {
    /// Defines the struct `tag`, after the structs it holds by value and
    /// the ones its named pointer fields reach.
    ///
    /// # Arguments
    ///
    /// * `tag` - The struct's name in the debug information.
    /// * `whole` - The struct is held by value, so it is defined even
    ///   when the text names none of its fields.
    /// * `depth` - How many structs hold this one, against a cycle.
    fn define(&mut self, tag: &str, whole: bool, depth: usize) {
        if self.done.contains(tag) || self.done.len() >= STRUCTS_MAX || depth > STRUCTS_MAX {
            return;
        }
        let Some(UserType::Struct(s)) = self.types.get(tag) else {
            return;
        };
        let named: Vec<(u64, &str, &TypeExpr)> = s
            .fields
            .iter()
            .filter(|(_, f)| self.fields.contains(f.name.as_str()))
            .map(|(off, f)| (*off, f.name.as_str(), &f.ty))
            .collect();
        if named.is_empty() && !whole {
            return;
        }
        self.done.insert(tag.to_owned());
        for (_, _, ty) in &named {
            if let Some(held) = struct_tag(self.types, ty) {
                self.define(&held, true, depth + 1);
            } else if let Some(pointed) = pointee_tag(self.types, ty) {
                self.define(&pointed, false, depth + 1);
            }
        }
        let mut body = String::new();
        let mut at = 0u64;
        for (off, field, ty) in named {
            let (Some(width), Some(spelled)) = (
                width_of(self.types, ty, self.word),
                spell(self.types, ty, field),
            ) else {
                continue;
            };
            if off < at {
                continue;
            }
            if off > at {
                body.push_str(&format!("uint8_t pad_{at:x}[{:#x}]; ", off - at));
            }
            body.push_str(&format!("{spelled}; "));
            at = off + width;
        }
        if s.size > at {
            body.push_str(&format!("uint8_t pad_{at:x}[{:#x}]; ", s.size - at));
        }
        self.lines.push(format!("struct {tag} {{ {body}}};"));
    }
}

/// The struct a name stands for: a struct of that name, or one a typedef
/// of that name stands for.
///
/// # Arguments
///
/// * `types` - The debug information's types.
/// * `name` - A word of the text.
///
/// # Returns
///
/// The struct's tag and its layout, or `None` when the word names no
/// struct.
fn resolve<'t>(
    types: &'t BTreeMap<String, UserType>,
    name: &str,
) -> Option<(String, &'t UserStruct)> {
    match types.get(name)? {
        UserType::Struct(s) => Some((name.to_owned(), s)),
        UserType::Alias(TypeExpr::Named(tag)) => match types.get(tag)? {
            UserType::Struct(s) => Some((tag.clone(), s)),
            UserType::Enum(_) | UserType::Alias(_) => None,
        },
        UserType::Enum(_) | UserType::Alias(_) => None,
    }
}

/// The struct a type holds by value, through aliases.
///
/// # Arguments
///
/// * `types` - The debug information's types.
/// * `ty` - The type.
fn struct_tag(types: &BTreeMap<String, UserType>, ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Named(n) => resolve(types, n).map(|(tag, _)| tag),
        TypeExpr::Array(elem, _) => struct_tag(types, elem),
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
        | TypeExpr::Char
        | TypeExpr::Ptr(_) => None,
    }
}

/// The struct a pointer type points at, through aliases.
///
/// # Arguments
///
/// * `types` - The debug information's types.
/// * `ty` - The type.
fn pointee_tag(types: &BTreeMap<String, UserType>, ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Ptr(inner) => struct_tag(types, inner).or_else(|| pointee_tag(types, inner)),
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
        | TypeExpr::Char
        | TypeExpr::Array(..)
        | TypeExpr::Named(_) => None,
    }
}

/// Spells a declaration of `decl` at type `ty`, as C writes it.
///
/// A struct is spelled by its tag (`struct _IO_FILE *`), an enum as the
/// integer of its width, and a typedef as what it stands for.
///
/// # Arguments
///
/// * `types` - The debug information's types.
/// * `ty` - The type.
/// * `decl` - The declarator: a name, with any stars and bounds.
///
/// # Returns
///
/// The declaration, or `None` for a name the debug information does not
/// state.
fn spell(types: &BTreeMap<String, UserType>, ty: &TypeExpr, decl: &str) -> Option<String> {
    let base = match ty {
        TypeExpr::U8 => "uint8_t",
        TypeExpr::U16 => "uint16_t",
        TypeExpr::U32 => "uint32_t",
        TypeExpr::U64 => "uint64_t",
        TypeExpr::I8 => "int8_t",
        TypeExpr::I16 => "int16_t",
        TypeExpr::I32 => "int32_t",
        TypeExpr::I64 => "int64_t",
        TypeExpr::F32 => "float",
        TypeExpr::F64 => "double",
        TypeExpr::Char => "char",
        TypeExpr::Ptr(inner) => {
            let decl = if matches!(**inner, TypeExpr::Array(..)) {
                format!("(*{decl})")
            } else {
                format!("*{decl}")
            };
            return spell(types, inner, &decl)
                .or_else(|| matches!(**inner, TypeExpr::Named(_)).then(|| format!("void {decl}")));
        }
        TypeExpr::Array(elem, len) => return spell(types, elem, &format!("{decl}[{len}]")),
        TypeExpr::Named(n) => {
            return match types.get(n)? {
                UserType::Struct(_) => Some(format!("struct {n} {decl}")),
                UserType::Enum(e) => Some(format!(
                    "{} {decl}",
                    if e.size == 8 { "int64_t" } else { "int32_t" }
                )),
                UserType::Alias(t) => spell(types, t, decl),
            };
        }
    };
    Some(format!("{base} {decl}"))
}

/// The names the text reads as fields: each word after `->`, or after a
/// `.` that follows a name, a `]` or a `)`.
///
/// # Arguments
///
/// * `code` - The text's lines, comments left out.
fn member_names<'t>(code: &[&'t str]) -> BTreeSet<&'t str> {
    let mut out = BTreeSet::new();
    for line in code {
        let bytes = line.as_bytes();
        for (i, _) in line.match_indices("->").chain(line.match_indices('.')) {
            let start = if bytes.get(i) == Some(&b'-') {
                i + 2
            } else if i > 0
                && bytes
                    .get(i - 1)
                    .is_some_and(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b']' | b')'))
                && bytes.get(i + 1).is_some_and(|b| !b.is_ascii_digit())
            {
                i + 1
            } else {
                continue;
            };
            let rest = line.get(start..).unwrap_or("");
            let len = rest.find(|c: char| !is_ident_char(c)).unwrap_or(rest.len());
            if let Some(name) = rest.get(..len).filter(|n| !n.is_empty()) {
                out.insert(name);
            }
        }
    }
    out
}

/// The words of the text, each once.
///
/// # Arguments
///
/// * `code` - The text's lines, comments left out.
fn words_of<'t>(code: &[&'t str]) -> BTreeSet<&'t str> {
    code.iter()
        .flat_map(|l| l.split(|c: char| !is_ident_char(c)))
        .filter(|w| w.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_'))
        .collect()
}

/// Tells whether a line indexes `name`: the word followed by `[`.
///
/// # Arguments
///
/// * `line` - One line of the text.
/// * `name` - The table's name.
fn indexes(line: &str, name: &str) -> bool {
    super::line::word_positions(line, name)
        .into_iter()
        .any(|at| {
            line.get(at + name.len()..)
                .is_some_and(|t| t.starts_with('['))
        })
}

/// Tells whether a line declares `name`: a declaration whose last word,
/// past any stars and bounds, is the name.
///
/// # Arguments
///
/// * `line` - One line of the text.
/// * `name` - The name.
fn declares(line: &str, name: &str) -> bool {
    let decl = line.split(" //").next().unwrap_or(line).trim();
    let Some(decl) = decl.strip_suffix(';') else {
        return false;
    };
    if decl.contains(['(', '=']) {
        return false;
    }
    let decl = decl.split('[').next().unwrap_or(decl);
    decl.chars()
        .all(|c| is_ident_char(c) || matches!(c, ' ' | '*'))
        && !decl.starts_with("return ")
        && decl.rsplit(|c: char| !is_ident_char(c)).next() == Some(name)
        && decl.contains(' ')
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::declare;
    use crate::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
    use crate::dwarf::Global;
    use crate::program::{Arch, Program};

    /// Builds an image whose debug information states `struct pair { short
    /// key; char *name; }`, the typedef `PAIR` of it, `struct node` holding
    /// a `struct pair` by value, and `struct pair table[4]` at 0x4000.
    fn program() -> Program {
        let mut p = Program::raw(vec![0; 16], Arch::X86_64, 0, None, Vec::new());
        let field = |name: &str, ty: TypeExpr| UserField {
            name: name.to_owned(),
            ty,
        };
        p.debug_types.insert(
            "pair".to_owned(),
            UserType::Struct(UserStruct {
                size: 16,
                fields: [
                    (0, field("key", TypeExpr::I16)),
                    (8, field("name", TypeExpr::Ptr(Box::new(TypeExpr::Char)))),
                ]
                .into(),
            }),
        );
        p.debug_types.insert(
            "PAIR".to_owned(),
            UserType::Alias(TypeExpr::Named("pair".to_owned())),
        );
        p.debug_types.insert(
            "node".to_owned(),
            UserType::Struct(UserStruct {
                size: 32,
                fields: [
                    (
                        0,
                        field(
                            "next",
                            TypeExpr::Ptr(Box::new(TypeExpr::Named("node".to_owned()))),
                        ),
                    ),
                    (8, field("item", TypeExpr::Named("pair".to_owned()))),
                ]
                .into(),
            }),
        );
        p.debug_globals = vec![Global {
            name: "table".to_owned(),
            addr: Some(0x4000),
            type_name: Some("struct pair[]".to_owned()),
            ty: Some(TypeExpr::Array(
                Box::new(TypeExpr::Named("pair".to_owned())),
                4,
            )),
        }];
        p
    }

    /// A struct the text reaches through a typedef is defined with the
    /// fields it names, padded to its layout, before the body.
    #[test]
    fn a_named_field_defines_its_struct() {
        let text = "// signature: char *f(PAIR *p)\n\nreturn p->name;\n";
        let out = declare(text, &program());
        assert_eq!(
            out,
            "// signature: char *f(PAIR *p)\nstruct pair { uint8_t pad_0[0x8]; char *name; };\n\nreturn p->name;\n"
        );
    }

    /// A struct held by value is defined first, whole, and an indexed
    /// table is declared at its stated length.
    #[test]
    fn a_held_struct_and_an_indexed_table_are_declared() {
        let text = "// signature: int f(struct node *n, int i)\n\nreturn n->next->item.key + table[i].key;\n";
        let out = declare(text, &program());
        let pair = out
            .find("struct pair { int16_t key; uint8_t pad_2[0xe]; };")
            .expect("pair is defined");
        let node = out
            .find("struct node { struct node *next; struct pair item; uint8_t pad_18[0x8]; };")
            .expect("node is defined");
        assert!(pair < node, "{out}");
        assert!(out.contains("extern struct pair table[4];"), "{out}");
    }

    /// A text that names no stated field or table is left as it is, and a
    /// table it declares itself is not declared again.
    #[test]
    fn a_text_naming_nothing_is_unchanged() {
        let program = program();
        let plain = "// signature: int f(PAIR *p)\n\nreturn *(uint32_t*)p;\n";
        assert_eq!(declare(plain, &program), plain);
        let declared = "// signature: int f(int i)\nuint64_t table[4];\n\nreturn table[i];\n";
        assert_eq!(declare(declared, &program), declared);
        let indexed = "// signature: int f(int i)\n\nif (i != 0) {\n  return table[i].key;\n}\n";
        assert!(
            declare(indexed, &program).contains("extern struct pair table[4];"),
            "an indented return is no declaration"
        );
    }
}
