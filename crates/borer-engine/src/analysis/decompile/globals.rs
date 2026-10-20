//! The types of the globals a function reads, from what the binary states:
//! its debug information, and the C library's data objects.
//!
//! A global the lifter names (`stdout`, `optarg`, `g32_6010`) is declared at
//! the width it is read, `uint64_t stdout;`, and a pointer read through it
//! at bytes past it, `*(uint64_t*)(stdout + 0x28)`. Where the debug
//! information states the variable (by its address, or by its name for a
//! declaration of one another module defines), or the C library exports an
//! object of that name, the declaration takes the stated type, `FILE
//! *stdout;`, and a struct the pointer points at names its fields,
//! `stdout->_IO_write_ptr`.

use std::collections::BTreeSet;

use super::expr::{Key, Names, Ty};
use super::fields::{TypedFields, struct_fields};
use crate::analysis::utypes::{TypeExpr, UserType, pointee_struct, width_of};
use crate::dwarf::Global;
use crate::program::Program;

/// A global's stated type, as a declaration spells it and in the type
/// language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Stated {
    /// The C spelling a declaration gives it (`FILE *`, `int32_t`).
    pub(super) spelled: String,
    /// The type in the type language.
    pub(super) ty: TypeExpr,
}

/// Returns the type the binary states for the global at `addr`.
///
/// The debug information's variable at that address comes first, then its
/// declaration of a variable by the global's name (a copy-relocated
/// `stdout` is defined in the C library, and only declared in the
/// program's own units), then the C library's data object of that name
/// ([`crate::analysis::typelib::data_type`]).
///
/// # Arguments
///
/// * `program` - The loaded image, with its debug information.
/// * `addr` - The global's address.
/// * `name` - The name the text gives it.
///
/// # Returns
///
/// The type, or `None` when nothing states one the language spells: a
/// scalar, or a pointer to one, to a named type or to a pointer.
pub(super) fn stated(program: &Program, addr: u64, name: &str) -> Option<Stated> {
    let globals = &program.debug_globals;
    let declared = globals
        .get(..globals.partition_point(|g| g.addr.is_none()))
        .unwrap_or(&[]);
    let debug = globals
        .get(globals.partition_point(|g| g.addr < Some(addr)))
        .filter(|g| g.addr == Some(addr))
        .or_else(|| {
            declared
                .binary_search_by(|g| g.name.as_str().cmp(name))
                .ok()
                .and_then(|i| declared.get(i))
        });
    let word = u64::from(program.arch.bitness().unwrap_or(64) / 8);
    match debug {
        Some(g) => from_debug(g, word),
        None => {
            let spelled = crate::analysis::typelib::data_type(name, program.format)?;
            Some(Stated {
                spelled: spelled.to_owned(),
                ty: library_type(spelled, word)?,
            })
        }
    }
}

/// An array global the debug information states, as a text declares it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Table {
    /// The array's address.
    pub(super) start: u64,
    /// How many elements it holds.
    pub(super) len: u64,
    /// One element's size in bytes.
    pub(super) size: u64,
    /// The element type it is declared with: `struct prec_assoc`, or for
    /// a scalar element the unsigned integer of its width (`uint32_t` of
    /// an `int`), the type the lifter reads every unsigned load as.
    pub(super) declared: String,
}

/// One element of a [`Table`], as an access at some address reads it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Element {
    /// The array.
    pub(super) table: Table,
    /// The element the address lies in, counted from the array's start.
    pub(super) index: u64,
    /// The field the access reads, `.prec`, or empty for a whole scalar
    /// element.
    pub(super) field: String,
    /// The C type the access reads as: a field's own type, or the
    /// declared type of a scalar element.
    pub(super) reads: String,
}

/// Returns the array global the debug information states at `at`, with
/// its element type.
///
/// An array of integers, pointers or structs counts; one of floats or of
/// arrays does not, since a table is declared and read in integers.
///
/// # Arguments
///
/// * `program` - The loaded image, with its debug information.
/// * `at` - An address.
///
/// # Returns
///
/// The table and its element type, or `None` when no such array holds
/// `at`.
fn stated_table(program: &Program, at: u64) -> Option<(Table, &TypeExpr)> {
    let globals = &program.debug_globals;
    let defined = globals.get(globals.partition_point(|g| g.addr.is_none())..)?;
    let g = defined.get(
        defined
            .partition_point(|g| g.addr <= Some(at))
            .checked_sub(1)?,
    )?;
    let (Some(start), Some(TypeExpr::Array(elem, len))) = (g.addr, &g.ty) else {
        return None;
    };
    let word = u64::from(program.arch.bitness().unwrap_or(64) / 8);
    let types = &program.debug_types;
    let size = width_of(types, elem, word).filter(|s| *s > 0)?;
    if at - start >= size.checked_mul(*len)? {
        return None;
    }
    let declared = match pointee_struct(types, &TypeExpr::Ptr(elem.clone())) {
        Some(_) => {
            let TypeExpr::Named(tag) = elem.as_ref() else {
                return None;
            };
            match types.get(tag) {
                Some(UserType::Alias(TypeExpr::Named(t))) => format!("struct {t}"),
                Some(UserType::Struct(_) | UserType::Enum(_) | UserType::Alias(_)) | None => {
                    format!("struct {tag}")
                }
            }
        }
        None if matches!(**elem, TypeExpr::Array(..) | TypeExpr::F32 | TypeExpr::F64) => {
            return None;
        }
        None => match size {
            1 => "uint8_t",
            2 => "uint16_t",
            4 => "uint32_t",
            8 => "uint64_t",
            _ => return None,
        }
        .to_owned(),
    };
    Some((
        Table {
            start,
            len: *len,
            size,
            declared,
        },
        elem,
    ))
}

/// Returns the array global the debug information states at `at`
/// ([`stated_table`]), whatever an access there reads.
///
/// # Arguments
///
/// * `program` - The loaded image, with its debug information.
/// * `at` - An address.
///
/// # Returns
///
/// The table, or `None` when no stated array holds `at`.
pub(super) fn table_holding(program: &Program, at: u64) -> Option<Table> {
    stated_table(program, at).map(|(t, _)| t)
}

/// Returns the element of a stated array global an access of `bytes` at
/// `at` reads.
///
/// The access must be one whole integer or pointer: a scalar element, or
/// the field of a struct element the remaining offset lands on, at the
/// field's width. A scalar element reads as its table's declared type, so
/// a read needs no cast; a field keeps its stated type.
///
/// # Arguments
///
/// * `program` - The loaded image, with its debug information.
/// * `at` - The access's address.
/// * `bytes` - The access's width in bytes.
///
/// # Returns
///
/// The element, or `None` when no stated array holds `at` or the access is
/// not one whole scalar of it.
pub(super) fn table_at(program: &Program, at: u64, bytes: u64) -> Option<Element> {
    let (table, elem) = stated_table(program, at)?;
    let word = u64::from(program.arch.bitness().unwrap_or(64) / 8);
    let types = &program.debug_types;
    let off = at - table.start;
    let (index, within) = (off / table.size, off % table.size);
    let (field, reads) = match pointee_struct(types, &TypeExpr::Ptr(Box::new(elem.clone()))) {
        Some(s) => {
            let f = s.fields.get(&within)?;
            if width_of(types, &f.ty, word)? != bytes {
                return None;
            }
            let reads = match &f.ty {
                TypeExpr::Char => "int8_t".to_owned(),
                TypeExpr::Array(..) | TypeExpr::Named(_) | TypeExpr::F32 | TypeExpr::F64 => {
                    return None;
                }
                other => other.c_name(word)?,
            };
            (format!(".{}", f.name), reads)
        }
        None if within == 0 && table.size == bytes => (String::new(), table.declared.clone()),
        None => return None,
    };
    Some(Element {
        table,
        index,
        field,
        reads,
    })
}

/// Reads a debug-information variable's type as a declaration states it.
///
/// A scalar is spelled at its fixed width (`int32_t`); a pointer keeps the
/// source's spelling without its qualifiers (`FILE *`, `char *`), which
/// names a typedef the reader knows rather than the struct behind it.
///
/// # Arguments
///
/// * `g` - The variable.
/// * `word` - The image's pointer width in bytes.
///
/// # Returns
///
/// The type, or `None` for an aggregate, an array, a function pointer or a
/// chain that did not resolve.
fn from_debug(g: &Global, word: u64) -> Option<Stated> {
    let ty = g.ty.clone()?;
    let spelled = match &ty {
        TypeExpr::Ptr(_) => {
            let source = g.type_name.as_deref()?;
            let bare: Vec<&str> = source
                .split(' ')
                .filter(|w| !matches!(*w, "const" | "volatile" | ""))
                .collect();
            let bare = bare.join(" ").replace("* *", "**");
            if bare.contains(['(', '[']) || !bare.ends_with('*') {
                return None;
            }
            bare
        }
        TypeExpr::Char => "char".to_owned(),
        TypeExpr::U8
        | TypeExpr::U16
        | TypeExpr::U32
        | TypeExpr::U64
        | TypeExpr::I8
        | TypeExpr::I16
        | TypeExpr::I32
        | TypeExpr::I64
        | TypeExpr::F32
        | TypeExpr::F64 => ty.c_name(word)?,
        TypeExpr::Array(..) | TypeExpr::Named(_) => return None,
    };
    Some(Stated { spelled, ty })
}

/// Reads one of the C library's type spellings in the type language.
///
/// # Arguments
///
/// * `spelled` - The spelling: a base word (`int`, `long`, `char`, a
///   typedef such as `FILE`) and its stars.
/// * `word` - The image's pointer width in bytes, the width of `long`
///   on the platforms these objects come from.
///
/// # Returns
///
/// The type, or `None` for an empty spelling.
fn library_type(spelled: &str, word: u64) -> Option<TypeExpr> {
    let base = spelled.trim_end_matches(['*', ' ']);
    let stars = spelled.matches('*').count();
    let scalar = match base {
        "int" => TypeExpr::I32,
        "char" => TypeExpr::Char,
        "long" if word == 4 => TypeExpr::I32,
        "long" => TypeExpr::I64,
        "" => return None,
        other => TypeExpr::Named(other.to_owned()),
    };
    Some((0..stars).fold(scalar, |t, _| TypeExpr::Ptr(Box::new(t))))
}

impl Stated {
    /// Tells whether a declaration of this type reads as the global's
    /// access does: a pointer as an integer word, a scalar at its own
    /// width and kind.
    ///
    /// # Arguments
    ///
    /// * `access` - How the text reads the global.
    /// * `word` - The image's pointer width in bytes.
    pub(super) fn fits(&self, access: Ty, word: u64) -> bool {
        let int = matches!(access, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64);
        let bits = u64::from(access.bits());
        match &self.ty {
            TypeExpr::Ptr(_) => int && bits == word * 8,
            TypeExpr::U8 | TypeExpr::I8 | TypeExpr::Char => access == Ty::U8,
            TypeExpr::U16 | TypeExpr::I16 => access == Ty::U16,
            TypeExpr::U32 | TypeExpr::I32 => access == Ty::U32,
            TypeExpr::U64 | TypeExpr::I64 => access == Ty::U64,
            TypeExpr::F32 => access == Ty::F32,
            TypeExpr::F64 => access == Ty::F64,
            TypeExpr::Array(..) | TypeExpr::Named(_) => false,
        }
    }

    /// Tells whether the declaration is a pointer, the one change of type
    /// whose reads mean what the access's did: an unsigned read of the
    /// same width spells the same value as the address it holds.
    pub(super) fn is_pointer(&self) -> bool {
        matches!(self.ty, TypeExpr::Ptr(_))
    }
}

/// Returns the globals of a function whose stated type points at a struct
/// the debug information lays out, with that struct's fields.
///
/// # Arguments
///
/// * `program` - The loaded image, with its debug information.
/// * `globals` - The globals the function reads and writes.
/// * `names` - The name resolver, for each global's rendered variable.
/// * `word` - The image's pointer width in bytes.
///
/// # Returns
///
/// `(variable, fields)` per such global.
pub(super) fn debug_typed(
    program: &Program,
    globals: &BTreeSet<(u64, Ty)>,
    names: &Names<'_>,
    word: u64,
) -> Vec<(String, TypedFields)> {
    let mut out: Vec<(String, TypedFields)> = Vec::new();
    for &(addr, ty) in globals {
        let name = names.key(Key::Global(addr, ty.bits()));
        let Some(stated) = stated(program, addr, &name).filter(|s| s.fits(ty, word)) else {
            continue;
        };
        if !stated.is_pointer() || out.iter().any(|(v, _)| *v == name) {
            continue;
        }
        let Some(s) = pointee_struct(&program.debug_types, &stated.ty) else {
            continue;
        };
        let fields = struct_fields(&program.debug_types, s, word);
        if !fields.is_empty() {
            out.push((name, fields));
        }
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Stated, library_type};
    use crate::analysis::decompile::expr::Ty;
    use crate::analysis::utypes::TypeExpr;

    /// The library's spellings read as the types they name, `long` at the
    /// platform's word.
    #[test]
    fn library_spellings_read_as_types() {
        assert_eq!(
            library_type("FILE *", 8),
            Some(TypeExpr::Ptr(Box::new(TypeExpr::Named("FILE".to_owned()))))
        );
        assert_eq!(
            library_type("char **", 8),
            Some(TypeExpr::Ptr(Box::new(TypeExpr::Ptr(Box::new(
                TypeExpr::Char
            )))))
        );
        assert_eq!(library_type("long", 4), Some(TypeExpr::I32));
        assert_eq!(library_type("int", 8), Some(TypeExpr::I32));
    }

    /// A pointer fits a word-wide integer read and nothing else; a scalar
    /// fits a read of its own width.
    #[test]
    fn a_stated_type_fits_reads_of_its_width() {
        let file = Stated {
            spelled: "FILE *".to_owned(),
            ty: TypeExpr::Ptr(Box::new(TypeExpr::Named("FILE".to_owned()))),
        };
        assert!(file.fits(Ty::U64, 8));
        assert!(!file.fits(Ty::U32, 8));
        assert!(file.fits(Ty::U32, 4));
        let int = Stated {
            spelled: "int32_t".to_owned(),
            ty: TypeExpr::I32,
        };
        assert!(int.fits(Ty::U32, 8));
        assert!(!int.fits(Ty::U8, 8));
    }
}
