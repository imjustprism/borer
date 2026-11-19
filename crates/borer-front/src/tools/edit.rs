//! The tools that edit the names in force: `set_name`, `set_comment`,
//! `set_type` and `class_layout` given `apply`.
//!
//! Each builds its edits and hands them to the face ([`super::Snapshot::edit`]).
//! A dry run, the default, plans them, and every face answers the same plan
//! text. Applied, what happens is the face's: the MCP server commits the
//! plan, and a face that holds proposals for a person keeps it instead
//! ([`Held::edit`]).

use borer_engine::analysis::edit::{self, Edit, Force, Laid, Plan};
use borer_engine::analysis::protos::Proto;
use borer_engine::analysis::settable::{Annotation, must_be_in_a_section};
use borer_engine::analysis::utypes::parse_type;
use borer_engine::analysis::{Analysis, Overlay, apply, classes, name_of, stated};
use borer_engine::answer::Need;
use borer_engine::program::Feature;

use super::params::{
    ClassLayoutParams, SetCommentParams, SetNameParams, SetTypeParams, field_var, must_be_a_name,
    must_fit_a_row, stated_fields, stated_values,
};
use super::{Apply, Failure, Held, run};

/// Returns whether a call is a dry run, and what the face is asked to do
/// with its plan.
///
/// # Arguments
///
/// * `dry_run` - The call's `dry_run`; absent is a dry run.
fn asked(dry_run: Option<bool>) -> (bool, Apply) {
    let dry = dry_run.unwrap_or(true);
    (dry, if dry { Apply::Preview } else { Apply::Commit })
}

/// Renders a class layout recovered from its methods' field accesses, or
/// with `apply` plans it as a user struct that types each method's object
/// ([`borer_engine::analysis::apply::from_class`]).
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded, the address is not a class method, nothing
/// belongs to the class, or the struct to apply is refused.
pub fn class_layout(h: &dyn Held, p: &ClassLayoutParams) -> Result<String, Failure> {
    run(h, Need::Code(Feature::Decompile), |s| {
        let (a, o) = (s.analysis(), s.overlay());
        let name = match s.entry(&p.class) {
            Ok(entry) => {
                let n = name_of(a, o, entry);
                classes::class_of(&n)
                    .ok_or_else(|| format!("{n} is not a class method"))?
                    .to_owned()
            }
            Err(_) => p.class.clone(),
        };
        let Some(struct_name) = &p.apply else {
            let layout = apply::class_named(s.program(), a, o, &name)?;
            return Ok(classes::render_layout(&layout, a, o));
        };
        let (dry, apply) = asked(p.dry_run);
        let edits = [Edit::Layout {
            from: Laid::Class(name),
            name: struct_name.clone(),
        }];
        s.edit(&edits, Force::Refuse, apply)
            .map(|plan| listed(&plan, dry))
            .map_err(|e| e.to_string())
    })
}

/// Reads the renames a `set_name` call asks for: `address` and `name`, or
/// `names`, each `address=name`.
///
/// # Arguments
///
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When neither form or both are given, `names` is empty or holds more than
/// one call takes, or an entry is not `address=name`.
fn renames(p: &SetNameParams) -> Result<Vec<(String, String)>, Failure> {
    /// Most renames one call takes.
    const NAMES_MAX: usize = 500;
    /// What a call naming nothing, or naming both ways, is told.
    const ASKED: &str = "give address and name, or names=[\"address=name\", ...]";
    match (&p.names, &p.address, &p.name) {
        (Some(names), None, None) if !names.is_empty() => {
            if names.len() > NAMES_MAX {
                return Err(Failure::asked(format!(
                    "{} names; one call takes at most {NAMES_MAX}",
                    names.len()
                )));
            }
            names
                .iter()
                .map(|pair| {
                    pair.split_once('=')
                        .map(|(a, n)| (a.trim().to_owned(), n.trim().to_owned()))
                        .ok_or_else(|| {
                            Failure::asked(format!(
                                "{} is not address=name",
                                borer_engine::text::quoted(pair)
                            ))
                        })
                })
                .collect()
        }
        (None, Some(address), Some(name)) => Ok(vec![(address.clone(), name.clone())]),
        _ => Err(Failure::asked(ASKED)),
    }
}

/// Names a function or data address in the overlay, dry-run by default.
///
/// `names` renames many at once, each `address=name`, all checked before
/// any is applied. A name must be an identifier ([`must_be_a_name`]), and
/// one another address already answers to is refused unless `force`: two
/// places of one name make every later lookup of it ambiguous.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When neither `address` and `name` nor `names` is given, a name is not an
/// identifier or is taken, no binary is loaded, an address does not
/// resolve, no section holds it, or the session would hold more names than
/// a project file holds ([`borer_engine::analysis::project::NAMES_MAX`]).
pub fn set_name(h: &dyn Held, p: &SetNameParams) -> Result<String, Failure> {
    let (dry, apply) = asked(p.dry_run);
    let pairs = renames(p)?;
    for (_, name) in &pairs {
        must_fit_a_row(name, Annotation::Name)?;
        must_be_a_name(name)?;
    }
    let force = if p.force.unwrap_or(false) {
        Force::Take
    } else {
        Force::Refuse
    };
    let item = |i: usize, e: String| match pairs.get(i) {
        Some((address, name)) if pairs.len() > 1 => format!("{address}={name}: {e}"),
        Some(_) | None => e,
    };
    run(h, Need::Code(Feature::Discover), |s| {
        let edits = pairs
            .iter()
            .enumerate()
            .map(|(i, (address, name))| {
                let at = s.addr(address).map_err(|e| item(i, e))?;
                Ok(Edit::Name {
                    at,
                    name: name.clone(),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let plan =
            s.edit(&edits, force, apply)
                .map_err(|e| match e.downcast_ref::<edit::Refused>() {
                    Some(refused) => item(refused.edit, refused.why.clone()),
                    None => e.to_string(),
                })?;
        let lines: Vec<(String, String)> = plan.lines().iter().map(|l| l.said(dry)).collect();
        Ok(match lines.as_slice() {
            [_] => answered(&plan, dry),
            more if dry => format!(
                "dry-run: {} names\n{}\npass dry_run=false to apply.",
                more.len(),
                more.iter()
                    .map(|(line, numeric)| format!("would {line}{numeric}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            more => more
                .iter()
                .map(|(line, numeric)| format!("{line}{numeric}"))
                .collect::<Vec<_>>()
                .join("\n"),
        })
    })
}

/// Attaches a comment to an address in the overlay, dry-run by default.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When the comment cannot be a row, no binary is loaded, the address does
/// not resolve, no section holds it, or the session would hold more
/// comments than a project file holds
/// ([`borer_engine::analysis::project::COMMENTS_MAX`]).
pub fn set_comment(h: &dyn Held, p: &SetCommentParams) -> Result<String, Failure> {
    let (dry, apply) = asked(p.dry_run);
    must_fit_a_row(&p.comment, Annotation::Comment)?;
    run(h, Need::File, |s| {
        let edits = [Edit::Comment {
            at: s.addr(&p.address)?,
            text: p.comment.clone(),
        }];
        s.edit(&edits, Force::Refuse, apply)
            .map(|plan| answered(&plan, dry))
            .map_err(|e| e.to_string())
    })
}

/// Defines a user type, states fields of a struct or a class, applies a
/// type at an address, states a function's prototype or one of its
/// variables.
///
/// `name` with `fields` states fields by offset ([`stated::plan`]): of the
/// user struct of that name, else of the class of exactly that name borer
/// recovered, else of a struct it defines. The fields merge into what the
/// name states, a field without a type keeping the type or the width it
/// had, and the answer counts the fields kept, changed and new; `replace`
/// drops every field the call does not restate, which with no fields is
/// every field stated of a class. A type of a size the class's code never
/// reads the field at is refused ([`stated::plan_class`]). `name` with
/// `values` defines an enum; `name` with `type` alone defines a typedef.
/// `address` with `type` applies the type at that data global: the
/// decompiler types the variable it renders there, so a `Player *` names
/// every field read through it (`g->hp` at the width the field states) and
/// a `State` applied at a global names every constant compared with it. At
/// a function, `type` is its prototype as C ([`Proto`]), which its
/// signature, its body and every call to it follow; with `var` (`a1`,
/// `local_58`, a name the debug information gives, or a name stated
/// before), `name` and an optional `type` name and type that variable, and
/// a `var` spelling an unnamed field (`field_0x270`) states that field of
/// the function's class ([`Edit::Var`]). `type` alone is C declarations,
/// laid out by the binary's ABI ([`borer_engine::analysis::cdecl`]).
/// Everything is validated before anything is written: types the language
/// does not spell, references to names nothing defines, fields that
/// overlap, a size that does not cover the last field and an offset
/// assertion that fails are refused with a message naming the offender.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When `replace` comes without `name` and `fields`, the call names
/// nothing to define or apply, a text cannot be a row, no binary is
/// loaded, a definition, a field, an application, a prototype or a variable
/// is refused, the address does not resolve or no section holds it, or the
/// session would apply more types than a project file holds
/// ([`borer_engine::analysis::utypes::APPLIED_MAX`]).
pub fn set_type(h: &dyn Held, p: &SetTypeParams) -> Result<String, Failure> {
    let SetTypeParams {
        name,
        fields,
        replace,
        values,
        size,
        address,
        r#type: ty,
        var,
        dry_run,
    } = p;
    let (dry, apply) = asked(*dry_run);
    if *replace == Some(true) && (name.is_none() || fields.is_none() || var.is_some()) {
        return Err(Failure::asked(
            "`replace` drops the fields `fields` does not restate, so it goes with `name` and `fields`",
        ));
    }
    if let (None, None, None, None, None, None, Some(decl)) =
        (name, address, var, fields, values, size, ty)
    {
        let edits = [Edit::Declare { text: decl.clone() }];
        return run(h, Need::Best(Feature::Discover), |s| {
            s.edit(&edits, Force::Refuse, apply)
                .map(|plan| listed(&plan, dry))
                .map_err(|e| e.to_string())
        });
    }
    if name.is_none() && address.is_none() {
        return Err(Failure::asked(
            "set_type needs `name` (+ `fields`, `values` or `type`) to define a type, `address` + `type` to apply one, or `type` alone holding C declarations",
        ));
    }
    for text in name
        .iter()
        .chain(ty)
        .chain(var)
        .chain(fields.iter().flatten())
        .chain(values.iter().flatten())
    {
        must_fit_a_row(text, Annotation::Type)?;
    }
    run(h, Need::Code(Feature::Discover), |s| {
        let (pr, a, o) = (s.program(), s.analysis(), s.overlay());
        let (at, function) = match address {
            Some(text) => {
                let va = s.addr(text)?;
                must_be_in_a_section(pr, va, Annotation::Type)?;
                (Some(va), a.function_at(va).map(|f| f.entry))
            }
            None => (None, None),
        };
        let edits = match var {
            Some(var) => {
                let entry = function.ok_or_else(|| {
                    "`var` names a variable of a function: give the function's `address`".to_owned()
                })?;
                vec![Edit::Var {
                    entry,
                    var: var.clone(),
                    field: field_var(var),
                    name: name.clone(),
                    ty: ty.clone(),
                }]
            }
            None => type_edits(p, (a, o), at, function)?,
        };
        s.edit(&edits, Force::Refuse, apply)
            .map(|plan| answered(&plan, dry))
            .map_err(|e| e.to_string())
    })
}

/// Plans the edits a `set_type` call states that are not a variable's:
/// a struct's or a class's fields, an enum, a typedef, then a type
/// applied at a data global or a function's prototype.
///
/// # Arguments
///
/// * `asked` - The call's parameters.
/// * `(a, o)` - The analysis and the overlay, for the name of a function
///   whose prototype does not read.
/// * `at` - The address the call names, resolved.
/// * `function` - The entry of the function `at` is in, if it is in one.
///
/// # Errors
///
/// When the parameters state a type two ways, a definition names nothing
/// to define, a type, a field or a value does not parse, or a type to
/// apply or a prototype is missing or does not parse.
fn type_edits(
    asked: &SetTypeParams,
    (a, o): (&Analysis, &Overlay),
    at: Option<u64>,
    function: Option<u64>,
) -> Result<Vec<Edit>, String> {
    let SetTypeParams {
        name,
        fields,
        replace,
        values,
        size,
        r#type: ty,
        ..
    } = asked;
    let mut edits = Vec::new();
    match (name, fields, values) {
        (Some(n), Some(fs), vs) if !fs.is_empty() || *replace == Some(true) => {
            if vs.is_some() {
                return Err(format!(
                    "type {n} states both fields and values; a struct takes fields, an enum values"
                ));
            }
            edits.push(Edit::Fields {
                name: n.clone(),
                size: *size,
                fields: stated_fields(fs)?,
                mode: stated::Mode::asked(replace.unwrap_or(false)),
            });
        }
        (Some(n), Some(_), _) => {
            return Err(format!(
                "struct {n} states no fields; give fields, `values` for an enum, or a `type` for a typedef"
            ));
        }
        (Some(n), _, Some(vs)) if !vs.is_empty() => edits.push(Edit::Enum {
            name: n.clone(),
            size: size.unwrap_or(4),
            values: stated_values(vs)?,
        }),
        (Some(n), _, Some(_)) => {
            return Err(format!(
                "enum {n} states no values; give them as name:value"
            ));
        }
        (Some(n), None, None) if function.is_some() => {
            return Err(format!(
                "at a function `type` is its prototype; define typedef {n} in a call of its own"
            ));
        }
        (Some(n), None, None) => {
            let target = ty
                .as_deref()
                .ok_or_else(|| format!("typedef {n} needs the `type` it stands for"))?;
            edits.push(Edit::Alias {
                name: n.clone(),
                ty: parse_type(target).map_err(|e| e.to_string())?,
            });
        }
        (None, _, _) => {}
    }
    match (at, function) {
        (Some(at), None) => {
            let spelled = ty
                .as_deref()
                .ok_or_else(|| "applying a type needs the `type` to apply".to_owned())?;
            edits.push(Edit::Apply {
                at,
                ty: parse_type(spelled).map_err(|e| e.to_string())?,
            });
        }
        (Some(_) | None, Some(entry)) => {
            let decl = ty.as_deref().ok_or_else(|| {
                "at a function `type` is its prototype: `int f(Player *p, uint32_t n)`".to_owned()
            })?;
            let proto = Proto::parse(decl).map_err(|e| {
                if decl.contains('(') {
                    e.to_string()
                } else {
                    format!(
                        "{entry:#x} is inside {}; types apply to data globals, and at a function `type` is its prototype (`int f(Player *p)`)",
                        name_of(a, o, entry)
                    )
                }
            })?;
            edits.push(Edit::Proto { entry, proto });
        }
        (None, None) => {}
    }
    Ok(edits)
}

/// Answers a plan whose lines are blocks of their own (types from C, a
/// layout): the blocks, then, for a dry run, how to apply them.
///
/// # Arguments
///
/// * `plan` - The plan.
/// * `dry` - Whether the plan is a dry run's.
fn listed(plan: &Plan, dry: bool) -> String {
    let mut out: String = plan.lines().iter().map(|l| l.said(dry).0).collect();
    if dry {
        out.push_str("pass dry_run=false to apply.\n");
    }
    out
}

/// Answers a plan of one line or of lines joined by `; `: a dry run says
/// what it would do and how to apply it, then the notes.
///
/// # Arguments
///
/// * `plan` - The plan.
/// * `dry` - Whether the plan is a dry run's.
fn answered(plan: &Plan, dry: bool) -> String {
    let lines: Vec<(String, String)> = plan.lines().iter().map(|l| l.said(dry)).collect();
    let words: Vec<&str> = lines
        .iter()
        .map(|(line, _)| line.as_str())
        .filter(|line| !line.is_empty())
        .collect();
    let notes: String = lines.iter().map(|(_, note)| note.as_str()).collect();
    if dry {
        format!(
            "dry-run: would {}. pass dry_run=false to apply.{notes}",
            words.join("; ")
        )
    } else {
        format!("{}{notes}", words.join("; "))
    }
}
