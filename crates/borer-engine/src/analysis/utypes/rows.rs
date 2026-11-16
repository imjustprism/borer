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

/// Most field pairs one detail lists as sharing bytes.
pub const OVERLAPS_MAX: usize = 256;

/// One field of a type's detail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldRow {
    /// The field's byte offset in the type.
    pub offset: u64,
    /// Its size in bytes, `None` when the engine cannot size its type.
    pub size: Option<u64>,
    /// Its name.
    pub name: Box<str>,
    /// Its type as its source spells it (`u32 *`, `WCHAR[260]`).
    pub ty: Box<str>,
}

/// A type opened: its row, its fields, and the bytes they leave or share.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDetail {
    /// The type's row, as [`type_rows`] lists it.
    pub row: TypeRow,
    /// Its fields by ascending offset; empty for anything but a struct.
    pub fields: Vec<FieldRow>,
    /// `(offset, length)` of each run of bytes below the size no field
    /// covers; none past a field the engine cannot size, whose end it
    /// does not know.
    pub holes: Vec<(u64, u64)>,
    /// Index pairs into `fields` of two sized fields sharing a byte (a
    /// union's members), lower index first, at most [`OVERLAPS_MAX`].
    pub overlaps: Vec<(usize, usize)>,
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

/// Opens one type: its fields with their sizes, the holes between them
/// and the fields that overlap.
///
/// A user or debug field is sized by [`width_of`] against the types its
/// own source holds, an SDK field by what the machine passes its type as
/// ([`pass_of`]); a field neither sizes keeps `None`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
/// * `name` - The type's name, as its row spells it.
/// * `source` - Where the type comes from.
/// * `kind` - What it is: with `name` and `source`, the row to open, as
///   two types of one name and source (a struct tag and a typedef) differ
///   only by it.
///
/// # Returns
///
/// The detail, or `None` when no row has that name, source and kind, or
/// the row is a recovered class, whose fields are
/// [`crate::analysis::classes::class_layout`]'s answer with its evidence.
#[must_use]
pub fn type_detail(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    name: &str,
    source: TypeSource,
    kind: TypeKind,
) -> Option<TypeDetail> {
    if source == TypeSource::Recovered {
        return None;
    }
    let all = memo(p, a, o);
    let at = all
        .binary_search_by(|r| (&*r.name, r.source, r.kind).cmp(&(name, source, kind)))
        .ok()?;
    let row = all.get(at)?.clone();
    let word = word_of(p);
    let mut fields = match source {
        TypeSource::User => o.types.get(name).map(|t| user_fields(t, &o.types, word)),
        TypeSource::Dwarf => p
            .debug_types
            .get(name)
            .map(|t| user_fields(t, &p.debug_types, word)),
        TypeSource::Sdk => sdk_struct(name, word).map(|s| {
            s.at(word)
                .into_iter()
                .map(|(offset, f)| FieldRow {
                    offset,
                    size: sdk_c_size(f.ty, word),
                    name: f.name.into(),
                    ty: f.ty.into(),
                })
                .collect()
        }),
        TypeSource::Recovered => None,
    }
    .filter(|_| kind == TypeKind::Struct)
    .unwrap_or_default();
    fields.sort_by_key(|f| f.offset);
    Some(TypeDetail {
        holes: holes(&fields, row.size),
        overlaps: overlaps(&fields),
        row,
        fields,
    })
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

/// Lists a struct's fields in the overlay's language, sized against the
/// types its names resolve in.
///
/// # Arguments
///
/// * `ty` - The type; anything but a struct has no fields.
/// * `known` - The types its fields' names resolve against.
/// * `word` - The image's pointer width in bytes (4 or 8).
fn user_fields(ty: &UserType, known: &BTreeMap<String, UserType>, word: u64) -> Vec<FieldRow> {
    let UserType::Struct(s) = ty else {
        return Vec::new();
    };
    s.fields
        .iter()
        .map(|(offset, f)| FieldRow {
            offset: *offset,
            size: width_of(known, &f.ty, word),
            name: f.name.as_str().into(),
            ty: f.ty.spell().into(),
        })
        .collect()
}

/// Finds the runs of bytes below `size` no field covers.
///
/// # Arguments
///
/// * `fields` - The fields, by ascending offset.
/// * `size` - The type's size in bytes; with none there is no hole.
///
/// # Returns
///
/// `(offset, length)` per run, in order; none past a field of unknown
/// size.
fn holes(fields: &[FieldRow], size: Option<u64>) -> Vec<(u64, u64)> {
    let Some(size) = size else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut end = Some(0u64);
    for f in fields {
        let start = f.offset.min(size);
        if let Some(e) = end
            && start > e
        {
            out.push((e, start - e));
        }
        end = end
            .zip(f.size)
            .map(|(e, len)| e.max(f.offset.saturating_add(len)));
    }
    if let Some(e) = end
        && e < size
    {
        out.push((e, size - e));
    }
    out
}

/// Finds the pairs of sized fields that share a byte.
///
/// # Arguments
///
/// * `fields` - The fields, by ascending offset.
///
/// # Returns
///
/// Index pairs, lower first, at most [`OVERLAPS_MAX`].
fn overlaps(fields: &[FieldRow]) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for (i, x) in fields.iter().enumerate() {
        let Some(end) = x
            .size
            .filter(|&n| n > 0)
            .map(|n| x.offset.saturating_add(n))
        else {
            continue;
        };
        for (j, y) in fields.iter().enumerate().skip(i + 1) {
            if y.offset >= end {
                break;
            }
            if y.size.is_some_and(|n| n > 0) {
                if out.len() == OVERLAPS_MAX {
                    return out;
                }
                out.push((i, j));
            }
        }
    }
    out
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
    use super::{TypeKind, TypeSource, type_detail, type_rows};
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

    /// A struct with `(offset, type)` fields, `size` bytes long.
    ///
    /// # Arguments
    ///
    /// * `size` - The struct's size in bytes.
    /// * `fields` - The fields' offsets and types.
    fn laid(size: u64, fields: &[(u64, TypeExpr)]) -> UserType {
        let fields = fields
            .iter()
            .map(|(off, ty)| {
                let name = format!("f{off}");
                (
                    *off,
                    UserField {
                        name,
                        ty: ty.clone(),
                    },
                )
            })
            .collect();
        UserType::Struct(UserStruct { size, fields })
    }

    /// A struct's holes are the bytes below its size no field covers, none
    /// counted past the size.
    ///
    /// Two fields sharing bytes are one overlap; a field the engine cannot size
    /// neither ends a hole nor overlaps; an SDK structure's fields are sized by
    /// their C types.
    #[test]
    fn a_detail_finds_the_holes_and_the_overlaps() {
        let mut p = Program::raw_x64(&[0xc3]);
        p.format = BinaryFormat::Pe;
        let a = Analysis::compute(&p);
        let mut o = Overlay::default();
        let unknown = TypeExpr::Named("Missing".to_owned());
        for (name, ty) in [
            ("Gaps", laid(24, &[(0, TypeExpr::U32), (8, TypeExpr::U64)])),
            ("Short", laid(8, &[(0, TypeExpr::U32), (12, TypeExpr::U32)])),
            ("Union", laid(8, &[(0, TypeExpr::U64), (4, TypeExpr::U32)])),
            ("Open", laid(32, &[(0, unknown), (16, TypeExpr::U32)])),
        ] {
            o.types.insert(name.to_owned(), ty);
        }
        let open = |name: &str, source| {
            type_detail(&p, &a, &o, name, source, TypeKind::Struct)
                .unwrap_or_else(|| panic!("{name} from {source:?} opens"))
        };
        let gaps = open("Gaps", TypeSource::User);
        assert_eq!(gaps.holes, [(4, 4), (16, 8)]);
        assert!(gaps.overlaps.is_empty());
        let sizes: Vec<Option<u64>> = gaps.fields.iter().map(|f| f.size).collect();
        assert_eq!(sizes, [Some(4), Some(8)]);
        assert_eq!(open("Short", TypeSource::User).holes, [(4, 4)]);
        let union = open("Union", TypeSource::User);
        assert_eq!((union.holes.len(), union.overlaps), (0, vec![(0, 1)]));
        let open_ended = open("Open", TypeSource::User);
        assert_eq!(open_ended.fields.first().map(|f| f.size), Some(None));
        assert!(open_ended.holes.is_empty() && open_ended.overlaps.is_empty());
        let startup = open("_STARTUPINFOW", TypeSource::Sdk);
        let sizes: Vec<Option<u64>> = startup.fields.iter().take(2).map(|f| f.size).collect();
        assert_eq!(sizes, [Some(4), Some(8)]);
        assert_eq!(startup.holes.first(), Some(&(4, 4)));
        let missing = [
            (TypeSource::Dwarf, TypeKind::Struct),
            (TypeSource::User, TypeKind::Enum),
        ];
        for (source, kind) in missing {
            assert!(type_detail(&p, &a, &o, "Gaps", source, kind).is_none());
        }
    }
}
