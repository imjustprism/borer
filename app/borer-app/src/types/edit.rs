//! The edits a struct tab asks of the engine's edit path, built from what the tab shows and
//! the text typed; nothing here writes the overlay.

use borer_engine::analysis::edit::{Edit, Laid};
use borer_engine::analysis::fieldrefs::parse_unsigned;
use borer_engine::analysis::stated::{Field, Mode};
use borer_engine::analysis::utypes::{FieldRow, TypeDetail, TypeExpr, parse_type};

use super::{Line, Shown};

/// What the person asks of the line a struct tab has selected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ask {
    /// Gives the selected field a new name.
    Rename,
    /// Gives the selected field a new type.
    Retype,
    /// Adds a field at the selected hole's offset.
    Add,
    /// Takes the selected field out of the struct.
    Delete,
    /// Gives the struct a new size: decimal, or hex after `0x`.
    Size,
    /// Defines a user struct of the shown type's fields.
    Copy,
    /// Defines the struct a proposal shows and types the pointer it was read through.
    Accept,
}

impl Ask {
    /// Returns what the input says before anything is typed, empty for an ask that takes
    /// no text.
    #[must_use]
    pub const fn prompt(self) -> &'static str {
        match self {
            Self::Rename => "New name of the field",
            Self::Retype => "New type of the field: u32, S *, u8[16]",
            Self::Add => "Name and type of the new field: count u32",
            Self::Delete => "",
            Self::Size => "New size in bytes",
            Self::Copy => "Name of the user struct",
            Self::Accept => "Name of the struct to define",
        }
    }

    /// Returns whether the ask takes typed text before it is planned.
    #[must_use]
    pub const fn takes_text(self) -> bool {
        !self.prompt().is_empty()
    }
}

/// Returns the one word of `text`, or why it is not one.
///
/// # Arguments
///
/// * `text` - What was typed.
///
/// # Errors
///
/// Returns why the text is empty or more than one word.
fn word(text: &str) -> Result<String, String> {
    let text = text.trim();
    if text.is_empty() || text.contains(char::is_whitespace) {
        return Err(format!("type one name, not \"{text}\""));
    }
    Ok(text.to_owned())
}

/// Returns `text` read as a type, or the engine's words for why it does not read.
///
/// # Arguments
///
/// * `text` - The type's spelling.
///
/// # Errors
///
/// Returns the engine's words for a spelling that does not read as a type.
fn ty(text: &str) -> Result<TypeExpr, String> {
    parse_type(text.trim()).map_err(|e| format!("{e:#}"))
}

/// Returns `f` stated with its own name and type, or why its type does not read.
///
/// # Arguments
///
/// * `f` - The engine's field row.
///
/// # Errors
///
/// Returns the field and why its type's spelling does not read as a type.
fn restated(f: &FieldRow) -> Result<(u64, Field), String> {
    let ty = ty(&f.ty).map_err(|why| format!("field {} at {:#x}: {why}", f.name, f.offset))?;
    let field = Field {
        name: f.name.to_string(),
        ty: Some(ty),
    };
    Ok((f.offset, field))
}

/// Returns the edits `ask` on `line` of what `shown` shows is, with `text` typed.
///
/// # Arguments
///
/// * `ask` - What the person asks.
/// * `shown` - What the tab shows.
/// * `line` - The selected line, if any.
/// * `text` - What was typed, ignored by an ask that takes none.
///
/// # Errors
///
/// Returns why no edit is made: the ask does not fit the line or what is shown, or the
/// text does not read as a name, a type or a size.
pub(super) fn edits(
    ask: Ask,
    shown: &Shown,
    line: Option<Line>,
    text: &str,
) -> Result<Vec<Edit>, String> {
    if let (Ask::Accept, Shown::Proposal(proposal, _)) = (ask, shown) {
        let spec = format!("{:#x},{}", proposal.entry, proposal.register);
        let name = word(text)?;
        let from = Laid::Pointer(spec);
        return Ok(vec![Edit::Layout { from, name }]);
    }
    let Shown::Detail(detail, _) = shown else {
        return Err("nothing here to edit".to_owned());
    };
    struct_edits(ask, detail, line, text)
}

/// Returns the edits `ask` on `line` of the struct `detail` is, as [`edits`] does.
///
/// # Arguments
///
/// * `ask` - What the person asks.
/// * `detail` - The engine's detail of the struct.
/// * `line` - The selected line, if any.
/// * `text` - What was typed.
///
/// # Errors
///
/// As [`edits`].
fn struct_edits(
    ask: Ask,
    detail: &TypeDetail,
    line: Option<Line>,
    text: &str,
) -> Result<Vec<Edit>, String> {
    let name = detail.row.name.to_string();
    let field = match line {
        Some(Line::Field(at, _)) => detail.fields.get(at),
        Some(Line::Hole(..) | Line::Proposed(_)) | None => None,
    };
    let selected = || field.ok_or_else(|| "select a field first".to_owned());
    let merge = |offset: u64, field: Field| Edit::Fields {
        name: name.clone(),
        size: None,
        fields: vec![(offset, field)],
        mode: Mode::Merge,
    };
    let edit = match ask {
        Ask::Rename => {
            let f = selected()?;
            let renamed = Field {
                name: word(text)?,
                ty: None,
            };
            merge(f.offset, renamed)
        }
        Ask::Retype => {
            let f = selected()?;
            let retyped = Field {
                name: f.name.to_string(),
                ty: Some(ty(text)?),
            };
            merge(f.offset, retyped)
        }
        Ask::Add => {
            let Some(Line::Hole(offset, _)) = line else {
                return Err("select a hole to add a field in".to_owned());
            };
            let (field_name, field_ty) = text
                .trim()
                .split_once(char::is_whitespace)
                .ok_or_else(|| "type the field's name, then its type: count u32".to_owned())?;
            let added = Field {
                name: word(field_name)?,
                ty: Some(ty(field_ty)?),
            };
            merge(offset, added)
        }
        Ask::Delete => {
            let f = selected()?;
            let rest = detail.fields.iter().filter(|g| g.offset != f.offset);
            Edit::Fields {
                name,
                size: detail.row.size,
                fields: rest.map(restated).collect::<Result<_, _>>()?,
                mode: Mode::Replace,
            }
        }
        Ask::Size => {
            let size = parse_unsigned(text.trim())
                .ok_or_else(|| format!("\"{}\" is no size in bytes", text.trim()))?;
            Edit::Fields {
                name,
                size: Some(size),
                fields: Vec::new(),
                mode: Mode::Merge,
            }
        }
        Ask::Copy => Edit::Fields {
            name: word(text)?,
            size: detail.row.size,
            fields: detail
                .fields
                .iter()
                .map(restated)
                .collect::<Result<_, _>>()?,
            mode: Mode::Replace,
        },
        Ask::Accept => return Err("only a proposal is accepted".to_owned()),
    };
    Ok(vec![edit])
}
