//! The tools that annotate: names, comments, types, and the listing of
//! every annotation the session holds.

use std::fmt::Write as _;

use borer_engine::analysis::edit::{self, Edit, Force, Line, Plan};
use borer_engine::analysis::protos::Proto;
use borer_engine::analysis::utypes::parse_type;
use borer_engine::analysis::{Analysis, Overlay, stated};
use borer_engine::program::Feature;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::errors::err_params;
use crate::params::{
    Annotation, AnnotationsParams, Filter, Page, SetCommentParams, SetNameParams, SetTypeParams,
    TypesParams, field_var, must_be_a_name, must_be_in_a_section, must_fit_a_row, stated_fields,
    stated_values,
};
use crate::safety::{Effect, effects};
use crate::state::read_lock;

impl BorerServer {
    /// Defines the types C declarations state, laid out by the loaded
    /// binary's ABI ([`borer_engine::analysis::cdecl`]): `set_type` with
    /// `type` alone.
    ///
    /// # Arguments
    ///
    /// * `text` - The declarations.
    /// * `dry` - Say what would be defined and write nothing.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the text is refused (a construct the
    /// subset does not read, an offset assertion that fails), or the types
    /// with the overlay's would not validate.
    fn declare_c(&self, text: &str, dry: bool) -> Result<String, ErrorData> {
        self.with_program(|p| {
            let edits = [Edit::Declare {
                text: text.to_owned(),
            }];
            let a = self.analysis_or_empty();
            self.edited((p, &a, &self.overlay()), &edits, Force::Refuse, dry)
                .map(|plan| listed(&plan, dry))
                .map_err(|e| e.to_string())
        })
    }
}

#[tool_router(router = annotate_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Names a function or data address in the overlay (dry-run by default).
    ///
    /// `names` renames many at once, each `address=name`, all checked
    /// before any is applied. A name must be an identifier
    /// ([`must_be_a_name`]), and one another address already answers to
    /// is refused unless `force`: two places of one name make every later
    /// lookup of it ambiguous.
    ///
    /// # Arguments
    ///
    /// * `SetNameParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, neither `address` and `name` nor `names`
    /// is given, a name is not an identifier or is taken, an address does
    /// not resolve, no section holds it, or the session would hold more
    /// names than a project file holds
    /// ([`borer_engine::analysis::project::NAMES_MAX`]).
    #[tool(
        description = "Name a function or data global in the session overlay, never the binary; names=[addr=name,...] renames many, checked first. A taken name needs force=true. Dry run until dry_run=false.",
        meta = effects(&[Effect::ChangesSession]),
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn set_name(
        &self,
        Parameters(SetNameParams {
            address,
            name,
            names,
            force,
            dry_run,
        }): Parameters<SetNameParams>,
    ) -> Result<String, ErrorData> {
        /// Most renames one call takes.
        const NAMES_MAX: usize = 500;
        /// What a call naming nothing, or naming both ways, is told.
        const ASKED: &str = "give address and name, or names=[\"address=name\", ...]";
        let dry = dry_run.unwrap_or(true);
        let pairs: Vec<(String, String)> = if let Some(names) = names {
            if address.is_some() || name.is_some() || names.is_empty() {
                return Err(err_params(ASKED));
            }
            if names.len() > NAMES_MAX {
                return Err(err_params(format!(
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
                            err_params(format!(
                                "{} is not address=name",
                                borer_engine::text::quoted(pair)
                            ))
                        })
                })
                .collect::<Result<_, _>>()?
        } else if let (Some(address), Some(name)) = (address, name) {
            vec![(address, name)]
        } else {
            return Err(err_params(ASKED));
        };
        for (_, name) in &pairs {
            must_fit_a_row(name, Annotation::Name)?;
            must_be_a_name(name)?;
        }
        let force = if force.unwrap_or(false) {
            Force::Take
        } else {
            Force::Refuse
        };
        let item = |i: usize, e: String| match pairs.get(i) {
            Some((address, name)) if pairs.len() > 1 => format!("{address}={name}: {e}"),
            Some(_) | None => e,
        };
        self.with_analysis(Feature::Discover, |p, a, o| {
            let edits = pairs
                .iter()
                .enumerate()
                .map(|(i, (address, name))| {
                    let at = self.addr(p, address).map_err(|e| item(i, e))?;
                    must_be_in_a_section(p, at, Annotation::Name).map_err(|e| item(i, e))?;
                    Ok(Edit::Name {
                        at,
                        name: name.clone(),
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            let plan = self
                .edited((p, a, o), &edits, force, dry)
                .map_err(|e| match e.downcast_ref::<edit::Refused>() {
                    Some(refused) => item(refused.edit, refused.why.clone()),
                    None => e.to_string(),
                })?;
            let lines: Vec<(String, String)> = plan.lines().iter().map(|l| said(l, dry)).collect();
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

    /// Attaches a comment to an address in the overlay (dry-run by default).
    ///
    /// # Arguments
    ///
    /// * `SetCommentParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address does not resolve, no section
    /// holds it, or the session would hold more comments than a project
    /// file holds ([`borer_engine::analysis::project::COMMENTS_MAX`]).
    #[tool(
        description = "Comment an address in the session overlay, never the binary; a comment opening with ? is an open question. To name it use set_name. Dry run until dry_run=false; save_project keeps it.",
        meta = effects(&[Effect::ChangesSession]),
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn set_comment(
        &self,
        Parameters(SetCommentParams {
            address,
            comment,
            dry_run,
        }): Parameters<SetCommentParams>,
    ) -> Result<String, ErrorData> {
        let dry = dry_run.unwrap_or(true);
        must_fit_a_row(&comment, Annotation::Comment)?;
        self.with_program(|p| {
            let va = self.addr(p, &address)?;
            must_be_in_a_section(p, va, Annotation::Comment)?;
            let edits = [Edit::Comment {
                at: va,
                text: comment.clone(),
            }];
            let a = self.analysis_held();
            self.edited((p, &a, &self.overlay()), &edits, Force::Refuse, dry)
                .map(|plan| answered(&plan, dry))
                .map_err(|e| e.to_string())
        })
    }

    /// Defines a user type, states fields of a struct or a class, applies a
    /// type at an address, states a function's prototype or one of its
    /// variables.
    ///
    /// `name` with `fields` states fields by offset ([`stated::plan`]): of
    /// the user struct of that name, else of the class of exactly that name
    /// borer recovered, else of a struct it defines. The fields merge into
    /// what the name states, a field without a type keeping the type or the
    /// width it had, and the answer counts the fields kept, changed and
    /// new; `replace` drops every field the call does not restate, which
    /// with no fields is every field stated of a class. A type
    /// of a size the class's code never reads the field at is refused
    /// ([`stated::plan_class`]). `name` with `values` defines
    /// an enum; `name` with `type` alone defines a typedef. `address` with
    /// `type` applies the type at that data global: the decompiler types the
    /// variable it renders there, so a `Player *` names every field read
    /// through it (`g->hp` at the width the field states) and a `State`
    /// applied at a global names every constant compared with it. At a
    /// function, `type` is its prototype as C
    /// ([`borer_engine::analysis::protos::Proto`]), which its signature,
    /// its body and every call to it follow; with `var` (`a1`, `local_58`,
    /// or a name stated before), `name` and an optional `type` name and
    /// type that variable, and a `var` spelling an unnamed field
    /// (`field_0x270`) states that field of the function's class
    /// ([`edit::Edit::Var`]). `type` alone is C declarations, laid
    /// out by the binary's ABI ([`BorerServer::declare_c`]). Everything is
    /// validated before anything is written: types the language does not
    /// spell, references to names nothing defines, fields that overlap, a
    /// size that does not cover the last field and an offset assertion
    /// that fails are refused with a message naming the offender.
    ///
    /// # Arguments
    ///
    /// * `SetTypeParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, `replace` comes without `name` and
    /// `fields`, a definition, a field, an application, a prototype or a
    /// variable is refused, the address does not resolve or no section
    /// holds it, or the session would apply more types than a project file
    /// holds ([`borer_engine::analysis::utypes::APPLIED_MAX`]).
    #[tool(
        description = "Define a struct, enum or typedef, name fields of a struct or class_layout class, or apply a type at an address so decompile names its fields; at a function, type sets the prototype. Checked first; dry run until dry_run=false.",
        meta = effects(&[Effect::ChangesSession]),
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]

    pub(crate) fn set_type(
        &self,
        Parameters(asked): Parameters<SetTypeParams>,
    ) -> Result<String, ErrorData> {
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
        } = &asked;
        let dry = dry_run.unwrap_or(true);
        if *replace == Some(true) && (name.is_none() || fields.is_none() || var.is_some()) {
            return Err(err_params(
                "`replace` drops the fields `fields` does not restate, so it goes with `name` and `fields`",
            ));
        }
        if let (None, None, None, None, None, None, Some(decl)) =
            (name, address, var, fields, values, size, ty)
        {
            return self.declare_c(decl, dry);
        }
        if name.is_none() && address.is_none() {
            return Err(err_params(
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
        self.with_analysis(Feature::Discover, |p, a, o| {
            let (at, function) = match address {
                Some(text) => {
                    let va = self.addr(p, text)?;
                    must_be_in_a_section(p, va, Annotation::Type)?;
                    (Some(va), a.function_at(va).map(|f| f.entry))
                }
                None => (None, None),
            };
            let edits = match var {
                Some(var) => {
                    let entry = function.ok_or_else(|| {
                        "`var` names a variable of a function: give the function's `address`"
                            .to_owned()
                    })?;
                    vec![Edit::Var {
                        entry,
                        var: var.clone(),
                        field: field_var(var),
                        name: name.clone(),
                        ty: ty.clone(),
                    }]
                }
                None => type_edits(&asked, (a, o), at, function)?,
            };
            self.edited((p, a, o), &edits, Force::Refuse, dry)
                .map(|plan| answered(&plan, dry))
                .map_err(|e| e.to_string())
        })
    }

    /// Lists the user types and where they are applied.
    ///
    /// # Arguments
    ///
    /// * `TypesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When `limit` is zero.
    #[tool(
        description = "List user-defined types and where each is applied, paged. Not for defining one (use set_type) or names and comments (use annotations).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn types(
        &self,
        Parameters(TypesParams {
            filter,
            offset,
            limit,
            count_only,
        }): Parameters<TypesParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(
            offset,
            limit,
            count_only,
            50,
            borer_engine::analysis::utypes::TYPES_ROWS_MAX,
        )?;
        let o = read_lock(&self.overlay);
        let rows = stated::rows(&o);
        let (_, total, table) = borer_engine::analysis::utypes::list_tsv(
            &o.types,
            &o.applied,
            &rows,
            filter.as_deref(),
            page.offset,
            page.limit.n,
        );
        let (types, applied) = (o.types.len(), o.applied.len());
        drop(o);
        if page.count_only {
            return Ok(format!(
                "# {total} rows ({types} type(s), {applied} applied)\n"
            ));
        }
        Ok(page.limit.noted(table))
    }

    /// Lists the overlay's entries: names, then the fields stated of
    /// classes, then findings, then open questions, a page at a time.
    ///
    /// A comment opening with a question mark is a hypothesis, not a
    /// finding. Separating the two is what makes the overlay a ledger an
    /// agent can return to: a conclusion it proved is worth building on,
    /// and one it guessed at is worth checking before it does. The ledger
    /// grows with the session, so it pages like every list: the header
    /// says `showing N of M` of the rows the filter keeps, and only the
    /// page asked for is held while the rows are counted.
    ///
    /// # Arguments
    ///
    /// * `AnnotationsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When `limit` is zero.
    #[tool(
        description = "List the names, findings and open questions (comments opening with ?) added this session, paged. Use it to resume work; not for binary symbols (use symbols) or user types (use types).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn annotations(
        &self,
        Parameters(AnnotationsParams {
            filter,
            offset,
            limit,
            count_only,
        }): Parameters<AnnotationsParams>,
    ) -> Result<String, ErrorData> {
        /// Rows a page holds when `limit` is absent.
        const ROWS_DEFAULT: usize = 200;
        /// Most rows a page holds.
        const ROWS_MAX: usize = 1000;
        let page = Page::new(offset, limit, count_only, ROWS_DEFAULT, ROWS_MAX)?;
        let filter = Filter::new(filter.as_deref());
        let o = read_lock(&self.overlay);
        let (open, settled): (Vec<_>, Vec<_>) = o
            .comments
            .iter()
            .partition(|(_, c)| c.trim_start().starts_with('?'));
        let fields = o.fields.iter().flat_map(|(class, fields)| {
            fields.iter().map(move |(off, field)| {
                let at = format!("{class}+{off:#x}");
                format!("{at:<12} field: {}", field.spell())
            })
        });
        let stated: usize = o.fields.values().map(std::collections::BTreeMap::len).sum();
        let rows = o
            .names
            .iter()
            .map(|(va, name)| format!("{:<12} name: {name}", format!("{va:#x}")))
            .chain(fields)
            .chain(
                settled
                    .iter()
                    .map(|(va, c)| format!("{:<12} found: {c}", format!("{va:#x}"))),
            )
            .chain(open.iter().map(|(va, c)| {
                let claim = c.trim_start().trim_start_matches('?').trim_start();
                format!("{:<12} open:  {claim}", format!("{va:#x}"))
            }))
            .filter(|row| filter.accepts(row));
        let (mut total, mut shown) = (0usize, Vec::new());
        for row in rows {
            if total >= page.offset && shown.len() < page.limit.n {
                shown.push(row);
            }
            total += 1;
        }
        let counts = format!(
            "{} names, {} findings, {} open question(s){}",
            o.names.len(),
            settled.len(),
            open.len(),
            match stated {
                0 => String::new(),
                n => format!(", {n} stated field(s)"),
            }
        );
        if page.count_only {
            return Ok(format!("# {total} annotations ({counts})\n"));
        }
        let mut out = format!(
            "# showing {} of {total} annotations ({counts})\n# addr annotation\n",
            shown.len()
        );
        for row in shown {
            let _ = writeln!(out, "{row}");
        }
        if !o.comments.is_empty() {
            out.push_str(
                "# a comment opening with ? is an open question; drop the ? once it is proved\n",
            );
        }
        Ok(page.limit.noted(out))
    }
}

/// Spells one line of a plan as the tools word it, without the `would`
/// a dry run opens with: the line, and the note that follows the answer.
///
/// # Arguments
///
/// * `line` - The line.
/// * `dry` - Whether the plan is a dry run's.
///
/// # Returns
///
/// The line's words, and its note, empty when it has none.
fn said(line: &Line, dry: bool) -> (String, String) {
    match line {
        Line::Named {
            target,
            function,
            old,
            new,
            number,
        } => {
            let what = if *function { "function" } else { "data" };
            let numeric = number.map_or_else(String::new, |n| {
                format!(
                    "
# note: '{new}' also reads as the number {n:#x}; an address argument finds the name first, and 0x-prefixed text is always an address"
                )
            });
            let line = if dry {
                format!("set name of {what} {target:#x} ({old}) to '{new}'")
            } else {
                format!("renamed {what} {target:#x}: {old} -> {new}")
            };
            (line, numeric)
        }
        Line::Commented { at } if dry => (format!("set comment at {at:#x}"), String::new()),
        Line::Commented { at } => (format!("comment set at {at:#x}"), String::new()),
        Line::Declared { types, abi, lines } => {
            /// Types a reply describes before it counts the rest.
            const SHOWN: usize = 64;
            let verb = if dry {
                "dry-run: would define"
            } else {
                "defined"
            };
            let mut out = format!("{verb} {types} type(s) from C, laid out for {abi}:\n");
            for line in lines.iter().take(SHOWN) {
                out.push_str(line);
                out.push('\n');
            }
            if lines.len() > SHOWN {
                out.push_str(&format!(
                    "# showing {SHOWN} of {} lines; `types` lists every type\n",
                    lines.len()
                ));
            }
            (out, String::new())
        }
        Line::Laid {
            name,
            prototypes,
            lines,
        } => {
            let (define, state) = if dry {
                ("dry-run: would define", "state")
            } else {
                ("defined", "stated")
            };
            let mut out = format!(
                "{define} struct {name} and {state} {prototypes} prototype(s); decompile then names the fields:\n"
            );
            for line in lines {
                out.push_str(line);
                out.push('\n');
            }
            (out, String::new())
        }
        Line::Stated { would, .. } if dry => (would.clone(), String::new()),
        Line::Stated { done, .. } => (done.clone(), String::new()),
        Line::Unknown(types) => (
            String::new(),
            format!(
                "\n# note: {} names no user type or C type word borer knows, so it passes as a word",
                types.join(", ")
            ),
        ),
    }
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
                        borer_engine::analysis::name_of(a, o, entry)
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
/// * `plan` - The plan, its lines spelled by [`said`].
/// * `dry` - Whether the plan is a dry run's.
pub(crate) fn listed(plan: &Plan, dry: bool) -> String {
    let mut out: String = plan.lines().iter().map(|l| said(l, dry).0).collect();
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
/// * `plan` - The plan, its lines spelled by [`said`].
/// * `dry` - Whether the plan is a dry run's.
fn answered(plan: &Plan, dry: bool) -> String {
    let lines: Vec<(String, String)> = plan.lines().iter().map(|l| said(l, dry)).collect();
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

#[cfg(test)]
mod tests;
