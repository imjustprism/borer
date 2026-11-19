//! Which edit a referent a view holds takes: the form of [`Edit`] that
//! addresses it, its target filled and the value left to type, or the
//! sentence that says why none of that kind does.

use super::{Proto, resolve_var, var_said};
use crate::analysis::decompile::decompile_named;
use crate::analysis::protos::VarKey;
use crate::analysis::schema::{signature_line, signature_params};
use crate::analysis::utypes::{TypeExpr, UserType};
use crate::analysis::{Analysis, Overlay, name_of};
use crate::program::Program;
use crate::view::{Ref, Said};

#[cfg(doc)]
use super::Edit;

/// One form of edit with its target filled and its value left to type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Form {
    /// Names a function by its entry, or a data address ([`Edit::Name`]);
    /// the value is the name.
    Name {
        /// The entry or the address.
        at: u64,
    },
    /// Comments an address ([`Edit::Comment`]); the value is the comment.
    Comment {
        /// The address.
        at: u64,
    },
    /// Names and types a function's variable ([`Edit::Var`]).
    Var {
        /// The function's entry.
        entry: u64,
        /// The variable as the function's text spells it.
        var: String,
        /// What the value is, and what it keeps.
        value: VarValue,
    },
    /// States a function's prototype ([`Edit::Proto`]); the value is the
    /// prototype as C.
    Proto {
        /// The function's entry.
        entry: u64,
    },
    /// Applies a type at a data global ([`Edit::Apply`]); the value is the
    /// type as C.
    Apply {
        /// The global's address.
        at: u64,
    },
    /// Names a field of a struct or class, or types it under the name it
    /// keeps ([`Edit::Fields`], merged into what the type states).
    Field {
        /// The struct or class.
        ty: String,
        /// The field's byte offset.
        offset: u64,
        /// The name kept while the value types the field; `None` when the
        /// value is its new name.
        keep: Option<String>,
    },
    /// Defines the types C declarations state ([`Edit::Declare`]); the value
    /// is the declarations.
    Declare,
    /// Defines a 4-byte enum ([`Edit::Enum`]); the value is its name, a
    /// colon, then each value's name and number (`State: Run = 1, Stop`), a
    /// value with no number one past the one before.
    Enum,
    /// Defines a typedef ([`Edit::Alias`]); the value is its name, `=`, then
    /// the type it stands for (`Handle = u64`).
    Alias,
}

/// What the value of a [`Form::Var`] is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarValue {
    /// A declaration: a name alone, or a type and a name (`wchar_t *path`).
    Declaration {
        /// The type kept when the declaration states none, as C.
        kept_type: Option<String>,
    },
    /// The variable's type, under the name it keeps.
    Type {
        /// The name kept.
        kept_name: String,
    },
}

/// A form a referent takes and the value it holds now, which an editor
/// opens with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Offer {
    /// The form.
    pub form: Form,
    /// The name, type, prototype or comment the target holds now; empty
    /// when it holds none the engine states.
    pub now: String,
}

/// Which kind of edit a person asks of a referent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A new name.
    Rename,
    /// A type, or a function's prototype.
    Retype,
    /// A comment.
    Comment,
}

/// Says a referent takes no comment, having no address of its own.
const NO_ADDRESS: &str =
    "it has no address of its own to hold a comment; comment the line it is read on";

/// Says a string literal takes no name or type.
const LITERAL: &str = "a string literal is shown by its text, so a name or a type there would not show; comment it instead";

/// Says an import takes no name or type here.
const IMPORT: &str = "an import goes by the name its module exports it under, and its prototype is that module's; comment the call instead";

/// Returns the edit of `kind` that `r` takes over `o`, its form's target
/// filled, or the sentence that says why it takes none of that kind.
///
/// A call's function is named by [`Edit::Name`] at its entry and typed by
/// [`Edit::Proto`]; a variable by [`Edit::Var`]; a global by
/// [`Edit::Name`] and typed by [`Edit::Apply`]; a field by
/// [`Edit::Fields`]; anything at an address is commented by
/// [`Edit::Comment`]. A label inside a function takes no name of its own,
/// since [`Edit::Name`] names the function it is in. A variable the
/// function's text does not name is refused in [`super::plan`]'s words.
/// Only a function's prototype reads its text, so asking for a name or a
/// comment never decompiles.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its analysis.
/// * `o` - The overlay the edit would be planned over.
/// * `r` - The referent.
/// * `kind` - What is asked of it.
///
/// # Errors
///
/// The sentence that says why `r` takes no edit of `kind`.
pub fn offer(p: &Program, a: &Analysis, o: &Overlay, r: &Ref, kind: Kind) -> Result<Offer, String> {
    match r {
        Ref::Function(entry) => Ok(at_function(p, a, o, *entry, kind)),
        Ref::Address(at) => match a.function_at(*at) {
            Some(f) if f.entry == *at => Ok(at_function(p, a, o, *at, kind)),
            Some(f) => {
                let fname = name_of(a, o, f.entry);
                match kind {
                    Kind::Rename => Err(format!(
                        "{at:#x} is a label inside {fname}; a name there names {fname}, so a label takes no name of its own: comment it, or rename {fname} at its entry"
                    )),
                    Kind::Retype => Err(format!(
                        "{at:#x} is code inside {fname}; a type applies at a data global, and {fname}'s prototype is set at its entry"
                    )),
                    Kind::Comment => Ok(comment(o, *at)),
                }
            }
            None => Ok(global(p, o, *at, kind)),
        },
        Ref::Global(at) => Ok(global(p, o, *at, kind)),
        Ref::Import(slot) => commented_only(o, *slot, kind, IMPORT),
        Ref::String(at) => commented_only(o, *at, kind, LITERAL),
        Ref::Field { ty, offset } => field(p, o, ty, *offset, kind),
        Ref::Variable {
            function,
            name,
            key,
        } => variable(p, o, (*function, name, *key), kind),
        Ref::Type(name) => Err(match kind {
            Kind::Rename => format!(
                "borer has no edit that renames a type; declare {name} again under the new name"
            ),
            Kind::Retype => {
                format!("{name} is a type, not a value; declare it again to change what it is")
            }
            Kind::Comment => format!("{name} is a type: {NO_ADDRESS}"),
        }),
        Ref::Comment(at) => match kind {
            Kind::Rename => Err(format!("a comment takes no name; rename what {at:#x} is")),
            Kind::Retype => Err(format!("a comment takes no type; type what {at:#x} is")),
            Kind::Comment => Ok(comment(o, *at)),
        },
    }
}

/// Returns the comment form at `at`, holding the comment there now.
///
/// # Arguments
///
/// * `o` - The overlay.
/// * `at` - The address.
fn comment(o: &Overlay, at: u64) -> Offer {
    Offer {
        form: Form::Comment { at },
        now: o.comments.get(&at).cloned().unwrap_or_default(),
    }
}

/// Returns the comment at `at` for [`Kind::Comment`], else `why`.
///
/// # Arguments
///
/// * `o` - The overlay.
/// * `at` - The address.
/// * `kind` - What is asked.
/// * `why` - Why a name or a type is refused there.
///
/// # Errors
///
/// `why`, for a name or a type.
fn commented_only(o: &Overlay, at: u64, kind: Kind, why: &str) -> Result<Offer, String> {
    match kind {
        Kind::Comment => Ok(comment(o, at)),
        Kind::Rename | Kind::Retype => Err(why.to_owned()),
    }
}

/// Returns what a function takes at its entry: its name, its prototype,
/// stated or as its text's signature line spells it, or a comment.
///
/// # Arguments
///
/// * `(p, a, o)` - The image, its analysis and the overlay.
/// * `entry` - The function's entry.
/// * `kind` - What is asked; only a prototype reads the text.
fn at_function(p: &Program, a: &Analysis, o: &Overlay, entry: u64, kind: Kind) -> Offer {
    match kind {
        Kind::Rename => Offer {
            form: Form::Name { at: entry },
            now: name_of(a, o, entry),
        },
        Kind::Retype => {
            let proto = o.prototypes.get(&entry).map(Proto::spell).or_else(|| {
                let text = decompile_named(p, a, o, entry)?;
                signature_line(&text).map(stated)
            });
            Offer {
                form: Form::Proto { entry },
                now: proto.unwrap_or_default(),
            }
        }
        Kind::Comment => comment(o, entry),
    }
}

/// Returns a signature line as a prototype a person can state as it is.
///
/// That is the line itself when it parses, else the line with each parameter
/// name the text makes up (`a1`) left out, which a stated prototype refuses.
///
/// # Arguments
///
/// * `sig` - The signature as the text's line spells it.
fn stated(sig: &str) -> String {
    if Proto::parse(sig).is_ok() {
        return sig.to_owned();
    }
    let unnamed = |param: &str| {
        let param = param.trim();
        let word = param
            .rfind(|c: char| !(c.is_alphanumeric() || c == '_'))
            .map_or(param, |at| param.get(at + 1..).unwrap_or_default());
        if crate::dwarf::local_name_ok(word) {
            param.to_owned()
        } else {
            param
                .strip_suffix(word)
                .unwrap_or(param)
                .trim_end()
                .to_owned()
        }
    };
    let rebuilt = sig
        .find('(')
        .zip(signature_params(sig))
        .and_then(|(open, params)| {
            let head = sig.get(..open)?;
            let params: Vec<String> = params.iter().map(|p| unnamed(p)).collect();
            Proto::parse(&format!("{head}({})", params.join(", "))).ok()
        });
    rebuilt.map_or_else(|| sig.to_owned(), |proto| proto.spell())
}

/// Returns what a data address takes: a name, an applied type or a
/// comment, each holding what the overlay or the symbol table states.
///
/// # Arguments
///
/// * `p` - The image, for a symbol's name there.
/// * `o` - The overlay.
/// * `at` - The address.
/// * `kind` - What is asked.
fn global(p: &Program, o: &Overlay, at: u64, kind: Kind) -> Offer {
    match kind {
        Kind::Rename => {
            let symbol = || {
                p.symbols
                    .iter()
                    .find(|s| s.addr == at)
                    .map(|s| s.name.clone())
            };
            Offer {
                form: Form::Name { at },
                now: o
                    .names
                    .get(&at)
                    .cloned()
                    .or_else(symbol)
                    .unwrap_or_default(),
            }
        }
        Kind::Retype => Offer {
            form: Form::Apply { at },
            now: o.applied.get(&at).map(|t| t.spell()).unwrap_or_default(),
        },
        Kind::Comment => comment(o, at),
    }
}

/// Returns what a field takes: a name, or a type under the name it has,
/// as the overlay or the debug information states it, else as the text
/// spells an unnamed one (`field_0x8`).
///
/// # Arguments
///
/// * `p` - The image, for its debug types.
/// * `o` - The overlay.
/// * `ty` - The struct or class.
/// * `offset` - The field's byte offset.
/// * `kind` - What is asked.
///
/// # Errors
///
/// For a comment: a field has no address of its own.
fn field(p: &Program, o: &Overlay, ty: &str, offset: u64, kind: Kind) -> Result<Offer, String> {
    let named = |name: &str| o.types.get(name).or_else(|| p.debug_types.get(name));
    let typed = |t: Option<&UserType>| {
        let s = match t {
            Some(UserType::Struct(s)) => s,
            Some(UserType::Alias(TypeExpr::Named(target))) => match named(target) {
                Some(UserType::Struct(s)) => s,
                Some(UserType::Enum(_) | UserType::Alias(_)) | None => return None,
            },
            Some(UserType::Enum(_) | UserType::Alias(_)) | None => return None,
        };
        s.fields
            .get(&offset)
            .map(|f| (f.name.clone(), f.ty.spell()))
    };
    let stated = o.fields.get(ty).and_then(|fs| fs.get(&offset)).map(|f| {
        let spelled = f.ty.as_ref().map(|t| t.spell()).unwrap_or_default();
        (f.name.clone(), spelled)
    });
    let (name, now) = stated
        .or_else(|| typed(o.types.get(ty)))
        .or_else(|| typed(p.debug_types.get(ty)))
        .unwrap_or_else(|| (format!("field_0x{offset:x}"), String::new()));
    let form = |keep| Form::Field {
        ty: ty.to_owned(),
        offset,
        keep,
    };
    match kind {
        Kind::Rename => Ok(Offer {
            form: form(None),
            now: name,
        }),
        Kind::Retype => Ok(Offer {
            form: form(Some(name)),
            now,
        }),
        Kind::Comment => Err(format!("a field: {NO_ADDRESS}")),
    }
}

/// Returns what a function's variable takes, or [`super::plan`]'s refusal
/// when the name is no variable of the function's.
///
/// A name keeps its stated type. A type goes under the name the variable
/// has, or with a new name when the text spells it by its place
/// (`local_8`), since a type is stated with a name. A name that now reads
/// as another variable than the view's token named is refused: the view
/// was built before an edit renamed them.
///
/// # Arguments
///
/// * `p` - The image.
/// * `o` - The overlay.
/// * `(entry, name, seen)` - The function's entry, the variable as the
///   view's text spells it, and the variable the view read it as.
/// * `kind` - What is asked.
///
/// # Errors
///
/// The plan's refusal of the name, that the name names another variable
/// now, or for a comment that a variable has no address of its own.
fn variable(
    p: &Program,
    o: &Overlay,
    (entry, name, seen): (u64, &str, Option<VarKey>),
    kind: Kind,
) -> Result<Offer, String> {
    if kind == Kind::Comment {
        return Err(format!("a variable: {NO_ADDRESS}"));
    }
    let key = resolve_var(p, o, entry, name)?;
    if seen.is_some_and(|seen| seen != key) {
        return Err(format!(
            "{name} names another variable since this view was built; wait for it to show the edit, then ask again"
        ));
    }
    let typed = o
        .vars
        .get(&entry)
        .and_then(|vs| vs.get(&key))
        .and_then(|v| v.ty.as_ref())
        .map(|t| t.spell());
    let form = |value| Form::Var {
        entry,
        var: name.to_owned(),
        value,
    };
    let declared = |kept_type| VarValue::Declaration { kept_type };
    Ok(match kind {
        Kind::Retype if var_said(p, o, entry, (name, key)) == Some(Said::Placeholder) => Offer {
            form: form(declared(None)),
            now: name.to_owned(),
        },
        Kind::Retype => Offer {
            form: form(VarValue::Type {
                kept_name: name.to_owned(),
            }),
            now: typed.unwrap_or_default(),
        },
        Kind::Rename | Kind::Comment => Offer {
            form: form(declared(typed)),
            now: name.to_owned(),
        },
    })
}
