//! A recovered layout applied: the struct a pointer's accesses or a
//! class's methods show, defined as a user type, and the parameter it was
//! recovered through typed with it by a stated prototype.
//!
//! A proposal the agent has to transcribe into `set_type` calls is a
//! proposal it gets wrong; this turns one into the overlay entries that
//! make the decompiler name the fields (`a1->f_10`). Each field takes the
//! widest access seen at its offset (`u8`, `u16`, `u32` or `u64`; a class
//! field read as floating point is `f32` or `f64`), named `f_<offset>` or
//! by the member name the class's asserts give it. An offset that overlaps
//! the field before it, one below the pointer, one of no scalar width and
//! one only handed to calls is left out, and the plan says so. The
//! prototype is the one stated for the function, else the one its
//! decompiled signature prints, with the parameter's type replaced, so the
//! arity, the return and the other parameters stay what the text shows.

use std::collections::BTreeMap;

use super::classes::{ClassLayout, FieldLabel};
use super::protos::{CType, PROTOTYPES_MAX, Proto};
use super::utypes::{self, TypeExpr, UserType, build_struct};
use super::{Analysis, Overlay, bare_name, name_of};
use crate::program::Program;

/// A struct to define and the prototypes that type a pointer with it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    /// The struct's name.
    pub name: String,
    /// The struct.
    pub ty: UserType,
    /// The prototypes to state, by function entry, in address order.
    pub prototypes: Vec<(u64, Proto)>,
    /// One line per offset or function left out, and why.
    pub notes: Vec<String>,
}

impl Plan {
    /// Describes the plan, one line per entry: the struct with its fields,
    /// then each prototype, then the notes.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis, to name the functions.
    /// * `o` - User names.
    ///
    /// # Returns
    ///
    /// The lines, at most 40 prototypes and 20 notes named before the
    /// rest are counted.
    #[must_use]
    pub fn describe(&self, a: &Analysis, o: &Overlay) -> Vec<String> {
        /// Prototypes named before the rest are counted.
        const PROTOS_SHOWN: usize = 40;
        /// Notes named before the rest are counted.
        const NOTES_SHOWN: usize = 20;
        let mut out = Vec::new();
        if let UserType::Struct(s) = &self.ty {
            let fields = s
                .fields
                .iter()
                .map(|(off, f)| format!("{off:#x} {} {}", f.name, f.ty.spell()))
                .collect::<Vec<_>>()
                .join(", ");
            out.push(format!(
                "struct {} ({:#x} bytes): {fields}",
                self.name, s.size
            ));
        }
        for (entry, proto) in self.prototypes.iter().take(PROTOS_SHOWN) {
            out.push(format!(
                "prototype {} ({entry:#x}): {}",
                name_of(a, o, *entry),
                proto.spell()
            ));
        }
        if self.prototypes.len() > PROTOS_SHOWN {
            out.push(format!(
                "# {} more prototypes",
                self.prototypes.len() - PROTOS_SHOWN
            ));
        }
        for note in self.notes.iter().take(NOTES_SHOWN) {
            out.push(format!("# {note}"));
        }
        if self.notes.len() > NOTES_SHOWN {
            out.push(format!("# {} more notes", self.notes.len() - NOTES_SHOWN));
        }
        out
    }

    /// Writes the plan into an overlay: the struct, and each prototype in
    /// place of any stated before.
    ///
    /// # Arguments
    ///
    /// * `o` - The overlay.
    pub fn apply(self, o: &mut Overlay) {
        o.types.insert(self.name, self.ty);
        o.prototypes.extend(self.prototypes);
    }
}

/// Plans the struct a function's accesses through one pointer show, and the
/// prototype that types the parameter the pointer arrives in.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names, types and prototypes.
/// * `spec` - `<address>[,<register>]`, as `borer://layout` reads it; the
///   address must be the function's entry, where the register is a
///   parameter.
/// * `name` - The struct's name.
///
/// # Returns
///
/// The plan.
///
/// # Errors
///
/// When the spec is refused, the register is no parameter at the entry,
/// no field has a width, the struct does not build, or the prototype
/// cannot be read or holds no such parameter.
pub fn from_pointer(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    spec: &str,
    name: &str,
) -> Result<Plan, String> {
    let found = super::render::layout_fields(p, a, o, spec)?;
    let fname = name_of(a, o, found.entry);
    let param = found.param.ok_or_else(|| {
        format!(
            "{} carries no parameter of {fname} at its entry {:#x}; apply types a parameter, so give the entry and an argument register",
            found.register, found.entry
        )
    })?;
    let mut notes: Vec<String> = Vec::new();
    let mut stated: Vec<(u64, String, TypeExpr)> = Vec::new();
    let mut end = 0u64;
    for (&at, &width) in &found.widths {
        let Ok(off) = u64::try_from(at) else {
            notes.push(format!(
                "-{:#x} is below the pointer: a container's field, left out",
                at.unsigned_abs()
            ));
            continue;
        };
        let Some(ty) = scalar(width, false) else {
            notes.push(format!(
                "{off:#x} is accessed {width} bytes wide, which no scalar is; left out"
            ));
            continue;
        };
        if off < end {
            notes.push(format!("{off:#x} overlaps the field before it; left out"));
            continue;
        }
        end = off.saturating_add(u64::from(width));
        stated.push((off, format!("f_{off:x}"), ty));
    }
    for &at in &found.addressed {
        let sign = if at < 0 { "-" } else { "" };
        notes.push(format!(
            "{sign}{:#x} is only handed to calls, so it states no width; left out",
            at.unsigned_abs()
        ));
    }
    if stated.is_empty() {
        return Err(format!(
            "{fname} reads and writes nothing through {} at a width a field takes; no struct to apply",
            found.register
        ));
    }
    let word: u64 = if p.is_64 { 8 } else { 4 };
    let ty = build_struct(name, None, &stated, &o.types, word).map_err(|e| e.to_string())?;
    let proto = typed(p, a, o, found.entry, param, name)?;
    check_room(o, 1)?;
    Ok(Plan {
        name: name.to_owned(),
        ty,
        prototypes: vec![(found.entry, proto)],
        notes,
    })
}

/// Plans the struct a class's methods show, and the prototypes that type
/// each method's first parameter, its object, with it.
///
/// A method whose prototype cannot be read, or that takes no parameter, is
/// left out with a note; the struct is still defined.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names, types and prototypes.
/// * `layout` - The class's recovered layout.
/// * `name` - The struct's name.
///
/// # Returns
///
/// The plan.
///
/// # Errors
///
/// When no field has a width, or the struct does not build.
pub fn from_class(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    layout: &ClassLayout,
    name: &str,
) -> Result<Plan, String> {
    let (stated, mut notes) = scalar_fields(layout);
    if stated.is_empty() {
        return Err(format!(
            "class {}'s methods access no field at a width a field takes; no struct to apply",
            layout.name
        ));
    }
    let word: u64 = if p.is_64 { 8 } else { 4 };
    let ty = build_struct(name, None, &stated, &o.types, word).map_err(|e| e.to_string())?;
    let mut prototypes: Vec<(u64, Proto)> = Vec::new();
    for &entry in layout.methods.iter().take(super::classes::METHODS_MAX) {
        match typed(p, a, o, entry, 0, name) {
            Ok(proto) => prototypes.push((entry, proto)),
            Err(why) => notes.push(format!("{} left untyped: {why}", name_of(a, o, entry))),
        }
    }
    check_room(o, prototypes.len())?;
    Ok(Plan {
        name: name.to_owned(),
        ty,
        prototypes,
        notes,
    })
}

/// Returns the fields a class layout states as scalars, in offset order,
/// and a note for each offset left out.
///
/// Each field takes the widest access seen at its offset, named by the
/// member name the class's asserts give it or `f_<offset>`; an offset of
/// no scalar width, one only addressed, and one overlapping the field
/// before it are left out.
///
/// # Arguments
///
/// * `layout` - The class's recovered layout.
///
/// # Returns
///
/// The `(offset, name, type)` fields and the notes.
pub(crate) fn scalar_fields(layout: &ClassLayout) -> (Vec<(u64, String, TypeExpr)>, Vec<String>) {
    let mut notes: Vec<String> = Vec::new();
    let mut stated: Vec<(u64, String, TypeExpr)> = Vec::new();
    let mut taken: BTreeMap<String, u64> = BTreeMap::new();
    let mut end = 0u64;
    for (&off, f) in &layout.fields {
        let bits = f.widths.iter().copied().max().unwrap_or(0);
        let float = f.float_widths.contains(&bits);
        let Some(ty) = scalar(u32::from(bits / 8), float) else {
            if f.address_taken > 0 && bits == 0 {
                notes.push(format!(
                    "{off:#x} is only addressed (an embedded object), so it states no width; left out"
                ));
            } else {
                notes.push(format!(
                    "{off:#x} is accessed {bits} bits wide, which no scalar is; left out"
                ));
            }
            continue;
        };
        if off < end {
            notes.push(format!("{off:#x} overlaps the field before it; left out"));
            continue;
        }
        let label = match layout.labels.get(&off) {
            Some(FieldLabel::Member(m)) if utypes::is_ident(m) && !taken.contains_key(m) => {
                m.clone()
            }
            Some(FieldLabel::Member(_) | FieldLabel::ReadBy(_)) | None => format!("f_{off:x}"),
        };
        taken.insert(label.clone(), off);
        end = off.saturating_add(u64::from(bits / 8));
        stated.push((off, label, ty));
    }
    (stated, notes)
}

/// The scalar of a field's width.
///
/// # Arguments
///
/// * `bytes` - The width in bytes.
/// * `float` - The field is read as floating point.
///
/// # Returns
///
/// The type, or `None` for a width no scalar of the language has.
fn scalar(bytes: u32, float: bool) -> Option<TypeExpr> {
    Some(match (bytes, float) {
        (4, true) => TypeExpr::F32,
        (8, true) => TypeExpr::F64,
        (1, _) => TypeExpr::U8,
        (2, _) => TypeExpr::U16,
        (4, false) => TypeExpr::U32,
        (8, false) => TypeExpr::U64,
        _ => return None,
    })
}

/// Refuses a plan that would state more prototypes than an overlay holds.
///
/// # Arguments
///
/// * `o` - The overlay.
/// * `more` - Prototypes the plan adds, at most.
///
/// # Errors
///
/// When the overlay would pass [`PROTOTYPES_MAX`].
fn check_room(o: &Overlay, more: usize) -> Result<(), String> {
    if o.prototypes.len().saturating_add(more) > PROTOTYPES_MAX {
        return Err(format!(
            "the overlay states {} prototypes; {more} more would pass the {PROTOTYPES_MAX} it holds",
            o.prototypes.len()
        ));
    }
    Ok(())
}

/// The prototype that types one parameter of a function as a pointer to a
/// struct: the stated one, else the decompiled signature's, with that
/// parameter's type replaced.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names, types and prototypes.
/// * `entry` - The function.
/// * `param` - The parameter's position from zero.
/// * `name` - The struct.
///
/// # Errors
///
/// When the function does not decompile, its signature does not read as a
/// prototype, or it has no parameter at that position.
fn typed(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    param: usize,
    name: &str,
) -> Result<Proto, String> {
    let mut proto = match o.prototypes.get(&entry) {
        Some(stated) => stated.clone(),
        None => {
            let text = super::decompile::decompile_plain(p, a, o, entry)
                .ok_or_else(|| format!("{entry:#x} does not decompile"))?;
            let own = name_of(a, o, entry);
            signature_proto(&text, bare_name(&own))?
        }
    };
    let count = proto.params.len();
    let slot = proto.params.get_mut(param).ok_or_else(|| {
        format!(
            "its prototype lists {count} parameter(s), none at position {}",
            param + 1
        )
    })?;
    slot.ty = CType {
        base: name.to_owned(),
        stars: 1,
    };
    Ok(proto)
}

/// Reads the signature a decompiled text prints as a prototype, the names
/// it makes up for parameters (`a1`) dropped so the prototype keeps
/// rendering them so.
///
/// # Arguments
///
/// * `text` - The decompiled text, whose `// signature:` line is read.
/// * `name` - The function's name as the signature prints it.
///
/// # Errors
///
/// When the text has no signature line, the line does not hold the name,
/// or what it states does not parse as a prototype.
fn signature_proto(text: &str, name: &str) -> Result<Proto, String> {
    let line = text
        .lines()
        .find_map(|l| l.strip_prefix("// signature: "))
        .ok_or_else(|| "its text states no signature".to_owned())?;
    let open = format!("{name}(");
    let at = line.find(&open).ok_or_else(|| {
        format!(
            "its signature {} does not name it",
            crate::text::quoted(line)
        )
    })?;
    let ret = line.get(..at).unwrap_or("").trim_end();
    let rest = line.get(at + open.len()..).unwrap_or("");
    let rest = rest.strip_suffix(" const").unwrap_or(rest);
    let inner = rest.strip_suffix(')').ok_or_else(|| {
        format!(
            "its signature {} does not end with `)`",
            crate::text::quoted(line)
        )
    })?;
    let params: Vec<&str> = if inner.trim().is_empty() {
        Vec::new()
    } else {
        inner
            .split(',')
            .map(|piece| unnamed(piece.trim()))
            .collect()
    };
    Proto::parse(&format!("{ret} ({})", params.join(", "))).map_err(|e| e.to_string())
}

/// A parameter as a signature spells it, without a made-up `aN` name.
///
/// # Arguments
///
/// * `piece` - `uint64_t a1`, `Player *a2`, `Foo *this`.
fn unnamed(piece: &str) -> &str {
    let start = piece
        .char_indices()
        .rev()
        .take_while(|(_, c)| c.is_ascii_alphanumeric() || *c == '_')
        .last()
        .map_or(piece.len(), |(i, _)| i);
    let made_up = piece
        .get(start..)
        .and_then(|n| n.strip_prefix('a'))
        .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()));
    if made_up && start > 0 {
        piece.get(..start).unwrap_or(piece).trim_end()
    } else {
        piece
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{signature_proto, unnamed};

    /// A decompiled signature reads back as the prototype it prints, its
    /// made-up names dropped and its own names kept.
    #[test]
    fn a_signature_reads_back_as_a_prototype() {
        assert_eq!(unnamed("uint64_t a1"), "uint64_t");
        assert_eq!(unnamed("Player *a12"), "Player *");
        assert_eq!(unnamed("Foo *this"), "Foo *this");
        assert_eq!(unnamed("..."), "...");
        let text = "// sub_1 @ 0x1000: 3 instructions, 1 blocks\n// signature: uint32_t sub_1(uint64_t a1, char *name, ...)\n";
        let proto = signature_proto(text, "sub_1").unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(proto.spell(), "uint32_t (uint64_t, char *name, ...)");
        let none =
            signature_proto("// signature: void f()\n", "f").unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(none.spell(), "void (void)");
        assert!(signature_proto("no header\n", "f").is_err());
    }
}
