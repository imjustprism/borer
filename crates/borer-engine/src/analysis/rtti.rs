//! MSVC run-time type information: the class name and parent behind a
//! vtable, read from the complete object locator the compiler places one
//! word before it.
//!
//! Every polymorphic class an MSVC program defines carries this record
//! unless RTTI was turned off, and it is the one naming source that needs
//! no inference: the mangled name sits in the type descriptor and the bases
//! in the class hierarchy descriptor. On a 64-bit image the locator's
//! pointers are image-relative; on a 32-bit one they are absolute. Every
//! read is bounds-checked against the image, and a record whose signature
//! or self-pointer does not match is not a locator.

use super::{pointer_size, read_u32, read_word};
use crate::program::Program;
use crate::strings::cstr_at;

/// Longest mangled type name read from a type descriptor.
const NAME_MAX: usize = 512;
/// Most bases read from a class hierarchy descriptor.
const BASES_MAX: u32 = 64;

/// The complete object locator's two links and the subobject it serves.
struct Locator {
    /// Offset of the subobject this table is for: zero for the class's own
    /// (primary) table, the base's offset for a further base's table under
    /// multiple inheritance.
    offset: u32,
    /// The type descriptor: `type_info` object whose name is the class's.
    type_descriptor: u64,
    /// The class hierarchy descriptor: base count and base array.
    hierarchy: u64,
}

/// Returns the class name a vtable's locator carries.
///
/// Only a class's primary table (the one at subobject offset zero) is
/// named: a further base's table under multiple inheritance belongs to the
/// same class, which has one name and one entry.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `vtable` - Address of the vtable's first slot.
///
/// # Returns
///
/// The qualified class name (`Managers::CinemaManager`), or `None` when no
/// locator precedes the table, the table is not the primary one, or its
/// name does not decode.
pub(super) fn class_name(program: &Program, vtable: u64) -> Option<String> {
    let col = locator(program, vtable)?;
    if col.offset != 0 {
        return None;
    }
    type_name(program, col.type_descriptor)
}

/// Returns the class and base a further base's table belongs to.
///
/// Under multiple inheritance a class has one table per base subobject
/// past the first, each with a locator naming the class and the offset the
/// subobject sits at; the class's own table has offset zero and is named
/// by [`class_name`]. The base is the one in the hierarchy's array whose
/// member displacement is that offset, as the compiler's own
/// `vftable{for Base}` name has it, and the offset in hex when no base
/// states it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `vtable` - Address of the table's first slot.
///
/// # Returns
///
/// `(class, base)` for a further base's table, or `None` for the primary
/// table or anything that is not a table.
pub(super) fn secondary(program: &Program, vtable: u64) -> Option<(String, String)> {
    let col = locator(program, vtable)?;
    if col.offset == 0 {
        return None;
    }
    let class = type_name(program, col.type_descriptor)?;
    let base =
        base_at(program, col.hierarchy, col.offset).unwrap_or_else(|| format!("{:#x}", col.offset));
    Some((class, base))
}

/// Returns the name of the base placed at an offset in the object.
///
/// Each base class descriptor in the hierarchy's array carries the member
/// displacement of its subobject; the first past the class itself whose
/// displacement is `offset`, and which is not reached through a virtual
/// base pointer, is the base.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `hierarchy` - Address of the class hierarchy descriptor.
/// * `offset` - The subobject offset the locator states.
///
/// # Returns
///
/// The base's demangled name, or `None` when no base sits at that offset.
fn base_at(program: &Program, hierarchy: u64, offset: u32) -> Option<String> {
    let bases = read_u32(program, hierarchy.checked_add(8)?)?;
    if !(2..=BASES_MAX).contains(&bases) {
        return None;
    }
    let array = pointer(program, hierarchy.checked_add(12)?)?;
    (1..bases).find_map(|k| {
        let base = pointer(program, array.checked_add(u64::from(k) * 4)?)?;
        let mdisp = read_u32(program, base.checked_add(8)?)?;
        let pdisp = read_u32(program, base.checked_add(12)?)?;
        if mdisp != offset || pdisp != u32::MAX {
            return None;
        }
        type_name(program, pointer(program, base)?)
    })
}

/// Returns the name of the first base class of the class a vtable belongs to.
///
/// The hierarchy descriptor's base array lists the class itself first and
/// its bases after it in depth-first order, so the second entry is the
/// direct base a single-inheritance class derives from.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `vtable` - Address of the vtable's first slot.
///
/// # Returns
///
/// The base's qualified name, or `None` when the class has no base or the
/// records do not decode.
pub(super) fn parent(program: &Program, vtable: u64) -> Option<String> {
    let col = locator(program, vtable)?;
    let bases = read_u32(program, col.hierarchy.checked_add(8)?)?;
    if !(2..=BASES_MAX).contains(&bases) {
        return None;
    }
    let array = pointer(program, col.hierarchy.checked_add(12)?)?;
    let base = pointer(program, array.checked_add(4)?)?;
    let descriptor = pointer(program, base)?;
    type_name(program, descriptor)
}

/// Reads the complete object locator one word before a vtable.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `vtable` - Address of the vtable's first slot.
///
/// # Returns
///
/// The locator's links, or `None` when the word before the table is not a
/// locator: the signature is the wrong one for the image's width, or the
/// 64-bit self-pointer does not point back at the record.
fn locator(program: &Program, vtable: u64) -> Option<Locator> {
    let col = read_word(program, vtable.checked_sub(pointer_size(program))?)?;
    let signature = read_u32(program, col)?;
    let expected = u32::from(program.is_64);
    if signature != expected {
        return None;
    }
    let offset = read_u32(program, col.checked_add(4)?)?;
    let type_descriptor = pointer(program, col.checked_add(12)?)?;
    let hierarchy = pointer(program, col.checked_add(16)?)?;
    if program.is_64 && pointer(program, col.checked_add(20)?)? != col {
        return None;
    }
    Some(Locator {
        offset,
        type_descriptor,
        hierarchy,
    })
}

/// Reads the qualified class name out of a type descriptor.
///
/// The descriptor is a `type_info` object: a vtable pointer, a spare
/// pointer, then the mangled name, `.?AVName@Scope@@` for a class and
/// `.?AUName@@` for a struct. The components come out innermost first and
/// are reversed into `Scope::Name`; a name with a template or another
/// special component goes through the demangler.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `descriptor` - Address of the type descriptor.
///
/// # Returns
///
/// The qualified name, or `None` when nothing readable is there.
fn type_name(program: &Program, descriptor: u64) -> Option<String> {
    let word = pointer_size(program);
    let (_, raw) = cstr_at(program, descriptor.checked_add(2 * word)?, 5, NAME_MAX)?;
    let body = raw
        .strip_prefix(".?AV")
        .or_else(|| raw.strip_prefix(".?AU"))?
        .strip_suffix("@@")?;
    if body.contains('?') || body.is_empty() {
        let demangled = msvc_demangler::demangle(
            &format!("??_R0{}@8", raw.get(1..)?),
            msvc_demangler::DemangleFlags::NAME_ONLY,
        )
        .ok()?;
        return demangled
            .strip_suffix(" `RTTI Type Descriptor'")
            .map(str::to_owned);
    }
    let mut parts: Vec<&str> = body.split('@').collect();
    parts.reverse();
    Some(parts.join("::"))
}

/// Reads the C++ type a `catch` clause's type descriptor names.
///
/// A class or a struct reads as [`type_name`] reads it; any other type
/// (`.H` for `int`, `.PEAD` for `char *`) goes through the demangler as
/// the descriptor's own symbol would, and its `__ptr64` qualifiers are
/// dropped since every pointer of the image has that width.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `descriptor` - Address of the type descriptor.
///
/// # Returns
///
/// The type as C++ spells it, or `None` when nothing readable is there.
pub(crate) fn caught_type(program: &Program, descriptor: u64) -> Option<String> {
    if let Some(name) = type_name(program, descriptor) {
        return Some(name);
    }
    let word = pointer_size(program);
    let (_, raw) = cstr_at(program, descriptor.checked_add(2 * word)?, 2, NAME_MAX)?;
    let demangled = msvc_demangler::demangle(
        &format!("??_R0{}@8", raw.strip_prefix('.')?),
        msvc_demangler::DemangleFlags::NAME_ONLY,
    )
    .ok()?;
    let ty = demangled.strip_suffix(" `RTTI Type Descriptor'")?;
    Some(ty.replace(" __ptr64", ""))
}

/// Reads a locator-relative link: an absolute pointer on a 32-bit image,
/// an image-relative offset on a 64-bit one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - Address of the four-byte field.
///
/// # Returns
///
/// The resolved address, or `None` when the field is zero or unreadable.
fn pointer(program: &Program, at: u64) -> Option<u64> {
    let v = read_u32(program, at)?;
    if v == 0 {
        return None;
    }
    if program.is_64 {
        program.image_base.checked_add(u64::from(v))
    } else {
        Some(u64::from(v))
    }
}
