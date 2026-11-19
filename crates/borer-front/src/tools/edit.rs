//! The tools that edit the names in force: `set_name`, `set_comment`,
//! `set_type`, `class_layout` given `apply`, and `script`'s proposals.
//!
//! Each builds its edits and hands them to the face ([`Snapshot::edit`]).
//! A dry run, the default, plans them, and every face answers the same plan
//! text. Applied, what happens is the face's: the MCP server commits the
//! plan, and a face that holds proposals for a person keeps it instead
//! ([`Held::edit`]).

use std::collections::HashSet;
use std::rc::Rc;
use std::sync::Arc;

use borer_engine::analysis::edit::{self, Edit, Force, Laid, Plan};
use borer_engine::analysis::protos::Proto;
use borer_engine::analysis::settable::{Annotation, must_be_in_a_section};
use borer_engine::analysis::utypes::parse_type;
use borer_engine::analysis::{Analysis, Overlay, apply, classes, name_of, stated};
use borer_engine::answer::{Need, percent_decode};
use borer_engine::program::Feature;
use borer_engine::script::Query;

use super::params::{
    ClassLayoutParams, ScriptParams, SetCommentParams, SetNameParams, SetTypeParams, field_var,
    must_be_a_name, must_fit_a_row, stated_fields, stated_values,
};
use super::{Apply, Failure, Held, Outcome, Snapshot, run};

/// What an answer opens with when the face held its plan as a proposal.
const PROPOSED: &str = "proposed, not applied: waits for the person to accept:";

/// Returns what a call asks the face to do with its plan.
///
/// # Arguments
///
/// * `dry_run` - The call's `dry_run`; absent is a dry run.
fn asked(dry_run: Option<bool>) -> Apply {
    if dry_run.unwrap_or(true) {
        Apply::Preview
    } else {
        Apply::Commit
    }
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
        let apply = asked(p.dry_run);
        let edits = [Edit::Layout {
            from: Laid::Class(name),
            name: struct_name.clone(),
        }];
        s.edit(&edits, Force::Refuse, apply)
            .map(|(plan, done)| listed(&plan, done))
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
    let apply = asked(p.dry_run);
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
        let (plan, done) =
            s.edit(&edits, force, apply)
                .map_err(|e| match e.downcast_ref::<edit::Refused>() {
                    Some(refused) => item(refused.edit, refused.why.clone()),
                    None => e.to_string(),
                })?;
        let lines: Vec<(String, String)> = plan
            .lines()
            .iter()
            .map(|l| l.said(done != Outcome::Committed))
            .collect();
        let would = |more: &[(String, String)]| {
            more.iter()
                .map(|(line, numeric)| format!("would {line}{numeric}"))
                .collect::<Vec<_>>()
                .join("\n")
        };
        Ok(match (lines.as_slice(), done) {
            ([_], _) => answered(&plan, done),
            (more, Outcome::Planned) => format!(
                "dry-run: {} names\n{}\npass dry_run=false to apply.",
                more.len(),
                would(more)
            ),
            (more, Outcome::Proposed) => {
                format!("{PROPOSED} {} names\n{}", more.len(), would(more))
            }
            (more, Outcome::Committed) => more
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
    let apply = asked(p.dry_run);
    must_fit_a_row(&p.comment, Annotation::Comment)?;
    run(h, Need::File, |s| {
        let edits = [Edit::Comment {
            at: s.addr(&p.address)?,
            text: p.comment.clone(),
        }];
        s.edit(&edits, Force::Refuse, apply)
            .map(|(plan, done)| answered(&plan, done))
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
    let apply = asked(*dry_run);
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
                .map(|(plan, done)| listed(&plan, done))
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
            .map(|(plan, done)| answered(&plan, done))
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

/// Runs a Rhai script against the program in borer's sandbox, answering
/// its `query` calls through the face ([`Held::querier`]).
///
/// The script runs on the snapshot and holds no lock while it runs. A
/// `query` of `borer://script/...` is refused, since a script that ran
/// scripts could recurse without end, and so is one saying
/// `dry_run=false`, which no read obeys, since a script only proposes and
/// `dry_run` here decides what is applied; the URI is read as the resource
/// reads it, percent-decoded, so an escaped `dry_run%3Dfalse` is refused
/// too. A failed script still answers what it printed and proposed before
/// its error, and applies nothing; applied, a proposal the listings could
/// not show, or at an address no section holds, is skipped and counted.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or borer does not disassemble its
/// architecture; a failing script, or one whose names or comments would
/// take the session past what a project file holds, is an answer that
/// applies nothing, not an error.
pub fn script(h: &dyn Held, p: &ScriptParams) -> Result<String, Failure> {
    run(h, Need::Best(Feature::Discover), |s| {
        if let Some(why) = s.program().refuses(Feature::Disasm) {
            return Err(why);
        }
        let face = h.querier();
        let query: Query = Rc::new(move |uri: &str| {
            if uri.starts_with("borer://script/") {
                return Err(
                    "a script cannot query borer://script/...: scripts do not run scripts"
                        .to_owned(),
                );
            }
            if percent_decode(uri).contains("dry_run=false") {
                return Err(
                    "a script proposes and applies nothing through query: drop dry_run=false"
                        .to_owned(),
                );
            }
            face(uri)
        });
        let ran = borer_engine::script::run_with(
            Arc::clone(s.program_arc()),
            Arc::clone(s.analysis_arc()),
            Arc::new(s.overlay().clone()),
            &p.code,
            &[],
            Some(query),
        );
        let mut text = borer_engine::script::run_tsv(&ran);
        if ran.names.is_empty() && ran.comments.is_empty() {
            return Ok(text);
        }
        if ran.error.is_some() {
            text.push_str("# nothing applied: the script failed\n");
        } else if p.dry_run.unwrap_or(true) {
            text.push_str("# dry-run: pass dry_run=false to apply these\n");
        } else {
            text.push_str(&proposed(s, &ran));
        }
        Ok(text)
    })
}

/// Applies the names and comments a script proposed, through the face, and
/// says what landed.
///
/// # Arguments
///
/// * `s` - The snapshot the script ran on.
/// * `ran` - The script's run.
///
/// # Returns
///
/// One line: what was applied and what skipped, or why nothing was.
fn proposed(s: &Snapshot<'_>, ran: &borer_engine::script::ScriptRun) -> String {
    let (program, analysis) = (s.program(), s.analysis());
    let (mut named, mut commented) = (HashSet::new(), HashSet::new());
    let mut skipped = 0usize;
    let mut edits = Vec::with_capacity(ran.names.len() + ran.comments.len());
    for (at, name) in &ran.names {
        if must_fit_a_row(name, Annotation::Name).is_ok()
            && must_be_a_name(name).is_ok()
            && must_be_in_a_section(program, *at, Annotation::Name).is_ok()
        {
            named.insert(analysis.function_at(*at).map_or(*at, |f| f.entry));
            edits.push(Edit::Name {
                at: *at,
                name: name.clone(),
            });
        } else {
            skipped += 1;
        }
    }
    for (at, comment) in &ran.comments {
        if must_fit_a_row(comment, Annotation::Comment).is_ok()
            && must_be_in_a_section(program, *at, Annotation::Comment).is_ok()
        {
            commented.insert(*at);
            edits.push(Edit::Comment {
                at: *at,
                text: comment.clone(),
            });
        } else {
            skipped += 1;
        }
    }
    let counted = format!(
        "names at {} addresses and comments at {}, the last proposal for an address winning; {skipped} skipped (empty, unprintable, no name set_name sets, or in no section)",
        named.len(),
        commented.len()
    );
    match s.edit(&edits, Force::Take, Apply::Commit) {
        Err(why) => format!("# nothing applied: {why}\n"),
        Ok((_, Outcome::Committed)) => format!("# applied {counted}\n"),
        Ok((_, Outcome::Planned | Outcome::Proposed)) => format!("# {PROPOSED} {counted}\n"),
    }
}

/// Answers a plan whose lines are blocks of their own (types from C, a
/// layout): the blocks, then, for a dry run, how to apply them; a proposal
/// says first that nothing was applied.
///
/// # Arguments
///
/// * `plan` - The plan.
/// * `done` - What the face did with it.
fn listed(plan: &Plan, done: Outcome) -> String {
    let said = |dry: bool| -> String { plan.lines().iter().map(|l| l.said(dry).0).collect() };
    match done {
        Outcome::Planned => format!("{}pass dry_run=false to apply.\n", said(true)),
        Outcome::Committed => said(false),
        Outcome::Proposed => format!("{PROPOSED}\n{}", said(true)),
    }
}

/// Answers a plan of one line or of lines joined by `; `: a dry run says
/// what it would do and how to apply it, a proposal that it was not
/// applied and what it would do, then the notes.
///
/// # Arguments
///
/// * `plan` - The plan.
/// * `done` - What the face did with it.
fn answered(plan: &Plan, done: Outcome) -> String {
    let lines: Vec<(String, String)> = plan
        .lines()
        .iter()
        .map(|l| l.said(done != Outcome::Committed))
        .collect();
    let words: Vec<&str> = lines
        .iter()
        .map(|(line, _)| line.as_str())
        .filter(|line| !line.is_empty())
        .collect();
    let words = words.join("; ");
    let notes: String = lines.iter().map(|(_, note)| note.as_str()).collect();
    match done {
        Outcome::Planned => format!("dry-run: would {words}. pass dry_run=false to apply.{notes}"),
        Outcome::Committed => format!("{words}{notes}"),
        Outcome::Proposed => format!("{PROPOSED} would {words}.{notes}"),
    }
}
