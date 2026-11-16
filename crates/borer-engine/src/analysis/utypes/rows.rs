//! Every type the engine knows, one row each with where it comes from.
//!
//! The user's types, the ones the debug information states, the SDK's and
//! the classes recovered from their constructors merge in one listing a
//! types browser pages through.

use std::collections::BTreeMap;

use super::{TypeExpr, UserType, width_of};
use crate::analysis::typelib::{base_of, pass_of};
use crate::analysis::{Analysis, Overlay, sdk};
use crate::program::{BinaryFormat, Program};

/// What a type is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeKind {
    /// A struct or union: fields at offsets.
    Struct,
    /// An enum: named values of one width.
    Enum,
    /// A name standing for another type.
    Typedef,
    /// A COM interface: methods by vtable slot.
    Interface,
    /// A class recovered from the constructors storing its vtable.
    Class,
}

/// Where a type comes from, in the order a listing ranks the same name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeSource {
    /// The overlay: a type the user or an agent stated.
    User,
    /// The program's DWARF ([`Program::debug_types`] and
    /// [`Program::debug_typedefs`]); a PDB's type records are not read.
    Dwarf,
    /// The Windows SDK library ([`sdk`]), listed for a PE only.
    Sdk,
    /// A class recovered from its constructors
    /// ([`crate::analysis::ClassFacts::by_name`]), but for the `class_<vtable>`
    /// names the engine makes up for a vtable no name states.
    Recovered,
}

/// One type as a listing shows it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeRow {
    /// The type's name: a user type's or a typedef's name, a struct's tag,
    /// a class's qualified name.
    pub name: Box<str>,
    /// What the type is.
    pub kind: TypeKind,
    /// Its size in bytes at the program's pointer width, `None` when the
    /// engine cannot size it (a recovered class, an interface, a typedef
    /// of a type it does not know). A debug typedef is sized as the debug
    /// type it names or, under a pointer, as a word; the storage of a C
    /// scalar the debug information names is not read, so it has none.
    pub size: Option<u64>,
    /// Its members: a struct's fields, an enum's values, an interface's
    /// methods, none for a typedef; `None` for a recovered class, whose
    /// fields only decompiling its methods shows
    /// ([`crate::analysis::classes::class_layout`]).
    pub fields: Option<usize>,
    /// The overlay's applications whose type names this one, under any
    /// pointers and arrays; only a user type is ever applied.
    pub applied: usize,
    /// Where the type comes from.
    pub source: TypeSource,
    /// For a user type, the debug or SDK type of the same name, the debug
    /// one when both exist: where the decompiler's field rendering looks a
    /// name up, it reads the user type first.
    pub shadows: Option<TypeSource>,
}

/// One page of the type listing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeRows {
    /// The rows shown, by name, then source, then kind.
    pub rows: Vec<TypeRow>,
    /// The rows the filter kept, before paging.
    pub total: usize,
}

/// Lists every type the engine knows, one row per name and source.
///
/// # Arguments
///
/// * `p` - The loaded image: its debug types, format and pointer width.
/// * `a` - The analysis, for the recovered classes.
/// * `o` - The overlay, for the user types and their applications.
/// * `filter` - Case-insensitive substring a row's name must contain.
/// * `offset` - Rows to skip first.
/// * `limit` - Most rows to show.
///
/// # Returns
///
/// The page of rows and how many the filter kept.
#[must_use]
pub fn type_rows(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    filter: Option<&str>,
    offset: usize,
    limit: usize,
) -> TypeRows {
    let q = filter.map(str::to_lowercase);
    let all = memo(p, a, o);
    let kept = all.iter().filter(|r| {
        q.as_deref()
            .is_none_or(|q| r.name.to_lowercase().contains(q))
    });
    let total = kept.clone().count();
    let rows = kept.skip(offset).take(limit).cloned().collect();
    TypeRows { rows, total }
}

/// Returns every row, built once per overlay and kept in
/// [`Analysis::derived`].
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
fn memo(p: &Program, a: &Analysis, o: &Overlay) -> std::sync::Arc<Vec<TypeRow>> {
    a.derived
        .get_or_build_named("type_rows", o.fingerprint(), (), || all_rows(p, a, o))
}

/// Collects every row, sorted by name, then source, then kind.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
fn all_rows(p: &Program, a: &Analysis, o: &Overlay) -> Vec<TypeRow> {
    let word = word_of(p);
    let mut applied = BTreeMap::new();
    for ty in o.applied.values() {
        if let Some(n) = base_name(ty) {
            *applied.entry(n).or_insert(0usize) += 1;
        }
    }
    let mut rows = Vec::new();
    for (name, ty) in &o.types {
        rows.push(TypeRow {
            applied: applied.get(name.as_str()).copied().unwrap_or(0),
            shadows: hidden(p, word, name),
            ..row_of(name, ty, &o.types, word, TypeSource::User)
        });
    }
    for (name, ty) in &p.debug_types {
        rows.push(row_of(name, ty, &p.debug_types, word, TypeSource::Dwarf));
    }
    for (name, spelled) in &p.debug_typedefs {
        let (base, stars) = base_of(spelled);
        if stars == 0 && base == *name && p.debug_types.contains_key(name) {
            continue;
        }
        let size = if stars > 0 {
            Some(word)
        } else {
            width_of(&p.debug_types, &TypeExpr::Named(base), word)
        };
        rows.push(row(
            name,
            TypeKind::Typedef,
            size,
            Some(0),
            TypeSource::Dwarf,
        ));
    }
    if p.format == BinaryFormat::Pe {
        for tag in sdk::structures().keys() {
            if let Some(s) = sdk_struct(tag, word) {
                let fields = Some(s.at(word).len());
                let size = s.size_at(word);
                rows.push(row(tag, TypeKind::Struct, size, fields, TypeSource::Sdk));
            }
        }
        for name in sdk::typedefs().keys() {
            let size = sdk_c_size(name, word);
            rows.push(row(name, TypeKind::Typedef, size, Some(0), TypeSource::Sdk));
        }
        for (name, i) in sdk::interfaces() {
            let methods = Some(i.methods.len());
            rows.push(row(
                name,
                TypeKind::Interface,
                None,
                methods,
                TypeSource::Sdk,
            ));
        }
    }
    for name in a
        .classes
        .by_name
        .keys()
        .filter(|n| !n.starts_with("class_"))
    {
        rows.push(row(
            name,
            TypeKind::Class,
            None,
            None,
            TypeSource::Recovered,
        ));
    }
    rows.sort_by(|x, y| (&*x.name, x.source, x.kind).cmp(&(&*y.name, y.source, y.kind)));
    rows.dedup_by(|x, y| (&x.name, x.source, x.kind) == (&y.name, y.source, y.kind));
    rows
}

/// Builds a row nothing applies and nothing shadows.
///
/// # Arguments
///
/// * `name` - The type's name.
/// * `kind` - What it is.
/// * `size` - Its size in bytes, when known.
/// * `fields` - Its members, when known.
/// * `source` - Where it comes from.
fn row(
    name: &str,
    kind: TypeKind,
    size: Option<u64>,
    fields: Option<usize>,
    source: TypeSource,
) -> TypeRow {
    TypeRow {
        name: name.into(),
        kind,
        size,
        fields,
        applied: 0,
        source,
        shadows: None,
    }
}

/// Builds the row of a type in the overlay's language, a user or a debug
/// one.
///
/// # Arguments
///
/// * `name` - The type's name.
/// * `ty` - The type.
/// * `known` - The types its names resolve against, for a typedef's size.
/// * `word` - The image's pointer width in bytes (4 or 8).
/// * `source` - Where it comes from.
fn row_of(
    name: &str,
    ty: &UserType,
    known: &BTreeMap<String, UserType>,
    word: u64,
    source: TypeSource,
) -> TypeRow {
    let (kind, size, fields) = match ty {
        UserType::Struct(s) => (TypeKind::Struct, Some(s.size), s.fields.len()),
        UserType::Enum(e) => (TypeKind::Enum, Some(e.size), e.values.len()),
        UserType::Alias(inner) => (TypeKind::Typedef, width_of(known, inner, word), 0),
    };
    row(name, kind, size, Some(fields), source)
}

/// Returns the debug or SDK type a user type of this name hides.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `word` - The image's pointer width in bytes (4 or 8).
/// * `name` - The user type's name.
fn hidden(p: &Program, word: u64, name: &str) -> Option<TypeSource> {
    if p.debug_types.contains_key(name) || p.debug_typedefs.contains_key(name) {
        return Some(TypeSource::Dwarf);
    }
    let sdk = p.format == BinaryFormat::Pe
        && (sdk_struct(name, word).is_some()
            || sdk::typedef(name).is_some()
            || sdk::interface(name).is_some());
    sdk.then_some(TypeSource::Sdk)
}

/// Returns the image's pointer width in bytes.
///
/// # Arguments
///
/// * `p` - The loaded image.
fn word_of(p: &Program) -> u64 {
    if p.is_64 { 8 } else { 4 }
}

/// Returns the SDK structure a tag names, when the machine of a pointer
/// width defines it.
///
/// # Arguments
///
/// * `tag` - The structure's tag.
/// * `word` - The pointer width in bytes (4 or 8).
fn sdk_struct(tag: &str, word: u64) -> Option<&'static sdk::Struct> {
    sdk::structure(tag).filter(|s| word == 8 || s.size32.is_some())
}

/// Returns the name a type ends at under its pointers and arrays.
///
/// # Arguments
///
/// * `ty` - The type.
fn base_name(ty: &TypeExpr) -> Option<&str> {
    let mut base = ty;
    while let TypeExpr::Ptr(inner) | TypeExpr::Array(inner, _) = base {
        base = inner;
    }
    base.name()
}

/// Sizes a type an SDK row spells, by what a PE passes it as
/// ([`pass_of`], which on Windows is its storage), counting trailing array
/// bounds, or as the SDK structure it names by value.
///
/// # Arguments
///
/// * `spelled` - The type as written (`DWORD`, `WCHAR[260]`, `char *`).
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Returns
///
/// The size in bytes, or `None` for `void` and for a type neither the
/// library nor the SDK knows.
fn sdk_c_size(spelled: &str, word: u64) -> Option<u64> {
    let mut count: u64 = 1;
    let mut elem = spelled.trim();
    while let Some((inner, bound)) = elem.strip_suffix(']').and_then(|s| s.rsplit_once('[')) {
        count = count.checked_mul(bound.trim().parse().ok()?)?;
        elem = inner.trim_end();
    }
    let bits = if word == 8 { 64 } else { 32 };
    let one = match pass_of(elem, bits, BinaryFormat::Pe) {
        Some(pass) => u64::from(pass.bits(bits) / 8),
        None => {
            let (base, stars) = base_of(elem);
            let tag = match sdk::typedef(&base) {
                Some(t) if t.stars == 0 && stars == 0 => t.tag?,
                Some(_) => return None,
                None => base.as_str(),
            };
            sdk_struct(tag, word)?.size_at(word)?
        }
    };
    (one > 0).then(|| one.checked_mul(count)).flatten()
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{TypeKind, TypeSource, type_rows};
    use crate::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{BinaryFormat, Program};
    use std::collections::BTreeMap;

    /// A struct of one `u32` at offset 0, `size` bytes long.
    ///
    /// # Arguments
    ///
    /// * `size` - The struct's size in bytes.
    fn one_field(size: u64) -> UserType {
        let field = UserField {
            name: "a".to_owned(),
            ty: TypeExpr::U32,
        };
        UserType::Struct(UserStruct {
            size,
            fields: BTreeMap::from([(0, field)]),
        })
    }

    /// A user struct, a debug struct of the same name, an SDK typedef and a
    /// recovered class each list with their source.
    ///
    /// The user struct says it shadows the debug one and counts where it is
    /// applied; a debug typedef of its own struct is no second row, one of a
    /// pointer is a word and one of a scalar is not sized; the listing pages,
    /// filters by name and follows the overlay.
    #[test]
    fn every_type_lists_with_its_source_and_what_it_shadows() {
        let mut p = Program::raw_x64(&[0xc3]);
        p.format = BinaryFormat::Pe;
        p.debug_types.insert("S".to_owned(), one_field(8));
        for (name, to) in [
            ("S", "struct S"),
            ("PS", "S *"),
            ("SAlias", "struct S"),
            ("uint", "unsigned int"),
        ] {
            p.debug_typedefs.insert(name.to_owned(), to.to_owned());
        }
        let mut a = Analysis::compute(&p);
        a.classes.by_name.insert(
            "Game::Actor".to_owned(),
            crate::analysis::vtables::ClassInfo::default(),
        );
        let mut o = Overlay::default();
        o.types.insert("S".to_owned(), one_field(16));
        let named = TypeExpr::Ptr(Box::new(TypeExpr::Named("S".to_owned())));
        o.applied.insert(0x2000, named);
        let all = type_rows(&p, &a, &o, None, 0, usize::MAX);
        let find = |name: &str, source| {
            all.rows
                .iter()
                .find(|r| &*r.name == name && r.source == source)
                .unwrap_or_else(|| panic!("{name} from {source:?}"))
        };
        let user = find("S", TypeSource::User);
        assert_eq!(user.shadows, Some(TypeSource::Dwarf));
        assert_eq!(
            (user.size, user.fields, user.applied),
            (Some(16), Some(1), 1)
        );
        let debug = find("S", TypeSource::Dwarf);
        assert_eq!(
            (debug.size, debug.shadows, debug.applied),
            (Some(8), None, 0)
        );
        let dword = find("DWORD", TypeSource::Sdk);
        assert_eq!((dword.kind, dword.size), (TypeKind::Typedef, Some(4)));
        let class = find("Game::Actor", TypeSource::Recovered);
        assert_eq!(
            (class.kind, class.size, class.fields),
            (TypeKind::Class, None, None)
        );
        let order: Vec<TypeSource> = all
            .rows
            .iter()
            .filter(|r| &*r.name == "S")
            .map(|r| r.source)
            .collect();
        assert_eq!(order, [TypeSource::User, TypeSource::Dwarf]);
        let sizes: Vec<Option<u64>> = ["PS", "SAlias", "uint"]
            .into_iter()
            .map(|n| find(n, TypeSource::Dwarf).size)
            .collect();
        assert_eq!(sizes, [Some(8), Some(8), None]);
        let page = type_rows(&p, &a, &o, Some("game::"), 0, 10);
        assert_eq!((page.total, page.rows.len()), (1, 1));
        let past = type_rows(&p, &a, &o, None, all.total, 10);
        assert_eq!((past.total, past.rows.len()), (all.total, 0));
        let before = type_rows(&p, &a, &o, Some("t"), 0, 0).total;
        o.types.insert("T".to_owned(), one_field(4));
        assert_eq!(type_rows(&p, &a, &o, Some("t"), 0, 0).total, before + 1);
        p.format = BinaryFormat::Elf;
        let a = Analysis::compute(&p);
        let elf = type_rows(&p, &a, &o, None, 0, usize::MAX);
        assert!(elf.rows.iter().all(|r| r.source != TypeSource::Sdk));
    }
}
