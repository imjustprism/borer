//! The fields an agent states of a class borer recovered, kept in
//! [`Overlay::fields`] beside the layout the class's methods show.
//!
//! A recovered layout is evidence, and an agent often knows one thing more
//! about one field: the member's name from an assert string, or its type.
//! Stating that must not cost the rest, so a statement holds only the
//! offsets it names and every other field stays as recovered. A stated
//! name is the first source of a class's field labels ([`labels`], which
//! [`super::classes::field_labels`] starts from), so every decompile of the
//! class's methods and every listing of its fields prints it, and a layout
//! marks the row it came from ([`notes`]).

use std::collections::BTreeMap;

use super::Overlay;
use super::classes::FieldLabel;
use super::utypes::TypeExpr;

/// One field an agent stated of a class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// The member's name, as the decompiler renders it (`this->name`).
    pub name: String,
    /// The type stated with the name; `None` leaves the field the width
    /// the class's code accesses it at.
    pub ty: Option<TypeExpr>,
}

impl Field {
    /// Spells the field as the listings write it after its offset.
    ///
    /// # Returns
    ///
    /// The name, then a space and the type when one was stated
    /// (`m_count u32`): a name holds no space, so the two read back apart.
    #[must_use]
    pub fn spell(&self) -> String {
        match &self.ty {
            Some(ty) => format!("{} {}", self.name, ty.spell()),
            None => self.name.clone(),
        }
    }
}

/// Returns the names the overlay states of a class's fields, as the labels
/// they take ahead of every name the class's code gives.
///
/// # Arguments
///
/// * `overlay` - The overlay.
/// * `class` - The class, as the method index spells it.
///
/// # Returns
///
/// A member label per stated offset, none when nothing is stated of the
/// class.
pub(crate) fn labels(overlay: &Overlay, class: &str) -> BTreeMap<u64, FieldLabel> {
    overlay
        .fields
        .get(class)
        .into_iter()
        .flatten()
        .map(|(off, field)| (*off, FieldLabel::Member(field.name.clone())))
        .collect()
}

/// Returns the notes a class layout's row opens with: where the row's name
/// came from, when the overlay states it.
///
/// # Arguments
///
/// * `overlay` - The overlay.
/// * `class` - The class, as the method index spells it.
/// * `off` - The field's byte offset.
///
/// # Returns
///
/// `stated`, followed by the type when one was stated with the name, or
/// nothing for a field the overlay does not state.
pub(crate) fn notes(overlay: &Overlay, class: &str, off: u64) -> Vec<String> {
    overlay
        .fields
        .get(class)
        .and_then(|fields| fields.get(&off))
        .map(|field| match &field.ty {
            Some(ty) => format!("stated {}", ty.spell()),
            None => "stated".to_owned(),
        })
        .into_iter()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::Field;
    use crate::analysis::Overlay;

    /// The overlay the binary's own name tables are read under keeps the
    /// stated fields, so what is read under it is keyed by them too.
    ///
    /// # Panics
    ///
    /// When the fields are left behind.
    #[test]
    fn the_overlay_without_tables_keeps_the_stated_fields() {
        let mut o = Overlay::default();
        let field = Field {
            name: "m_count".to_owned(),
            ty: None,
        };
        o.fields
            .entry("Cls".to_owned())
            .or_default()
            .insert(8, field);
        assert_eq!(o.without_tables().fields, o.fields);
        assert_ne!(
            o.without_tables().fingerprint(),
            Overlay::default().fingerprint()
        );
    }
}
