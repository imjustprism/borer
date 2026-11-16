//! Who stated each name a view links ([`Said`]), read from the fact the
//! engine spelled it with, never from the spelling's shape alone.
//!
//! A function says what its row of the function table says
//! ([`RowSource`]); an import is the file's, but for one whose name a
//! table of exports lends to its ordinal or the loader makes up
//! ([`OrdinalName`]);
//! a global is the overlay's or
//! a data symbol's where it is spelled as theirs, and a placeholder where
//! it is spelled from its address and nothing names it; a label is the
//! overlay's, or a placeholder spelled from its block's address where the
//! overlay names it nothing. A variable says what the edit path reads it
//! as ([`var_said`]); a field or a type is the overlay's or the debug
//! information's where they name it so, and a field spelled
//! `field_0x<hex>` at its own offset a placeholder. Each looks the overlay up by
//! the referent's own key, which the text that spelled it read already, so
//! a view reads what its answer read.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::super::expr_render::data_name;
use super::super::line::label_address;
use super::fields::field_hex_offset;
use crate::analysis::attributes::global_addr;
use crate::analysis::edit::var_said;
use crate::analysis::render::RowSource;
use crate::analysis::utypes::UserType;
use crate::analysis::{Analysis, NameSource, Overlay, bare_name};
use crate::headers::OrdinalName;
use crate::program::{Program, SymbolKind};
use crate::view::{Ref, Said};

impl From<RowSource> for Said {
    fn from(source: RowSource) -> Self {
        match source {
            RowSource::User => Self::User,
            RowSource::Found(NameSource::None) => Self::Placeholder,
            RowSource::Found(NameSource::Symbol) => Self::Stated,
            RowSource::Found(
                NameSource::Helper
                | NameSource::Signature
                | NameSource::Handler
                | NameSource::Slot
                | NameSource::Qt
                | NameSource::Funclet
                | NameSource::Pack
                | NameSource::Library
                | NameSource::ObjC
                | NameSource::Constants,
            ) => Self::Inferred,
        }
    }
}

/// Returns who stated the name one token of a view spells a referent by.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force, looked up by the referent's key only.
/// * `r` - The referent.
/// * `spelled` - The token's text.
///
/// # Returns
///
/// Who stated it, `None` when the fact the name was spelled from does not
/// say, or for a referent that is no name.
pub(crate) fn of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    r: &Ref,
    spelled: &str,
) -> Option<Said> {
    match r {
        Ref::Function(e) => {
            let f = analysis.function(*e)?;
            let said = Said::from(RowSource::of(overlay, f));
            (said == Said::User || (said == Said::Placeholder) == f.name.is_none()).then_some(said)
        }
        Ref::Import(id) => import(program, analysis, *id, spelled),
        Ref::Global(va) => global(program, analysis, overlay, *va, spelled),
        Ref::Address(va) => label(overlay, *va, spelled),
        Ref::Variable { function, name, .. } => var_said(program, overlay, *function, name),
        Ref::Field { ty, offset } => field(program, overlay, ty, *offset, spelled),
        Ref::Type(name) => type_said(program, Some(overlay), name),
        Ref::String(_) => None,
    }
}

/// Returns who stated the name a token spells an import by.
///
/// Every slot the loader lists the import at ([`super::import_slots`]) is
/// read off the one import symbol at the slot ([`import_symbols`]) and how
/// the loader named it ([`crate::headers::Headers::import_names`]).
/// The name after the module is the file's where the file states it, the
/// engine's finding where a table names an ordinal, and a placeholder where
/// the loader made it up. A token spelling the symbol whole, module and
/// all, is a placeholder too where the loader made the module's name up:
/// the listing's, and the decompile's where no `(unnamed)` module can be
/// cut from the name.
///
/// # Arguments
///
/// * `program` - The loaded image, for its symbols and how it named them.
/// * `analysis` - Its analysis, holding the import groups.
/// * `id` - The import's first slot.
/// * `spelled` - The token's text.
///
/// # Returns
///
/// Who stated it, as every slot that holds one import symbol says: a slot
/// two import symbols share says nothing of either. `None` when no import
/// is listed at `id`, when no slot holds it alone, when a symbol has two
/// entries, or when two of its slots say apart: a missed source, never a
/// false one.
fn import(program: &Program, analysis: &Analysis, id: u64, spelled: &str) -> Option<Said> {
    let slots = super::import_slots(program, analysis, id)?;
    let held = import_symbols(program, analysis);
    let mut said = slots.iter().filter_map(|&slot| {
        let k = match held.get(&slot).map(Vec::as_slice) {
            Some([k]) => k,
            Some([_, _, ..]) => return None,
            Some([]) | None => return Some(None),
        };
        let at = program.headers.import_names.at(slot);
        let mut named = at.iter().filter(|e| e.symbol == *k);
        let (entry, None) = (named.next(), named.next()) else {
            return Some(None);
        };
        let whole = program.symbols.get(*k).is_some_and(|s| s.name == spelled);
        if whole && entry.is_some_and(|e| e.module.is_some()) {
            return Some(Some(Said::Placeholder));
        }
        Some(Some(match entry.and_then(|e| e.origin) {
            None => Said::Stated,
            Some(OrdinalName::Listed) => Said::Inferred,
            Some(OrdinalName::Made) => Said::Placeholder,
        }))
    });
    let first = said.next()??;
    said.all(|s| s == Some(first)).then_some(first)
}

/// Returns each import slot's symbols, by their places in the symbol
/// table, read once per analysis.
///
/// # Arguments
///
/// * `program` - The loaded image, whose symbols list the imports.
/// * `analysis` - Its analysis, holding the memo.
fn import_symbols(program: &Program, analysis: &Analysis) -> Arc<BTreeMap<u64, Vec<usize>>> {
    analysis
        .derived
        .get_or_build("view_import_symbols", (), || {
            let mut by: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
            for (k, s) in program.symbols.iter().enumerate() {
                if s.kind == SymbolKind::Import {
                    by.entry(s.addr).or_default().push(k);
                }
            }
            by
        })
}

/// Returns who stated the name a global is spelled by: the overlay's
/// name, a data symbol's, or its `g<bits>_<hex>` address where neither
/// names it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis, for the symbol at the address.
/// * `overlay` - Names in force.
/// * `va` - The global's address.
/// * `spelled` - The token's text.
fn global(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    va: u64,
    spelled: &str,
) -> Option<Said> {
    let user = overlay.names.get(&va);
    let symbol = analysis.symbol_at(program, va).map(|s| data_name(&s.name));
    if user.is_some_and(|n| n == spelled) {
        Some(Said::User)
    } else if symbol.as_deref() == Some(spelled) {
        Some(Said::Stated)
    } else {
        (user.is_none() && symbol.is_none() && global_addr(spelled) == Some(va))
            .then_some(Said::Placeholder)
    }
}

/// Returns who stated the name an address is spelled by: the overlay's
/// name for it, or a placeholder for its block's `L_<hex>` label where the
/// overlay names it nothing.
///
/// # Arguments
///
/// * `overlay` - Names in force.
/// * `va` - The address.
/// * `spelled` - The token's text.
fn label(overlay: &Overlay, va: u64, spelled: &str) -> Option<Said> {
    match overlay.names.get(&va) {
        Some(n) => (n == spelled || bare_name(n) == spelled).then_some(Said::User),
        None => (label_address(spelled) == Some(va)).then_some(Said::Placeholder),
    }
}

/// Returns who stated a type's name: the overlay, else the debug
/// information.
///
/// # Arguments
///
/// * `program` - The loaded image, for its debug types.
/// * `overlay` - The types in force, `None` for a type the text declares,
///   whose name reads no user type, as the view's reading of it reads none.
/// * `name` - The type's name.
pub(super) fn type_said(program: &Program, overlay: Option<&Overlay>, name: &str) -> Option<Said> {
    if overlay.is_some_and(|o| o.types.contains_key(name)) {
        Some(Said::User)
    } else {
        program
            .debug_types
            .contains_key(name)
            .then_some(Said::Stated)
    }
}

/// Returns who stated the name a field is spelled by: the overlay's struct
/// or the debug information's naming it so at its offset, the overlay's
/// fields of its class, or its own `field_0x<hex>` offset.
///
/// # Arguments
///
/// * `program` - The loaded image, for its debug types.
/// * `overlay` - Names in force, looked up by the field's type.
/// * `ty` - The aggregate type.
/// * `offset` - The field's byte offset.
/// * `spelled` - The token's text.
fn field(
    program: &Program,
    overlay: &Overlay,
    ty: &str,
    offset: u64,
    spelled: &str,
) -> Option<Said> {
    let names = |t: Option<&UserType>| match t {
        Some(UserType::Struct(s)) => s.fields.get(&offset).is_some_and(|f| f.name == spelled),
        Some(UserType::Enum(_) | UserType::Alias(_)) | None => false,
    };
    let stated = || {
        overlay
            .fields
            .get(ty)
            .and_then(|fs| fs.get(&offset))
            .is_some_and(|f| f.name == spelled)
    };
    if names(overlay.types.get(ty)) || stated() {
        Some(Said::User)
    } else if names(program.debug_types.get(ty)) {
        Some(Said::Stated)
    } else {
        (field_hex_offset(spelled) == Some(offset)).then_some(Said::Placeholder)
    }
}
