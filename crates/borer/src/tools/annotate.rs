//! The tools that annotate: names, comments, types, and the listing of
//! every annotation the session holds.

use std::fmt::Write as _;

use borer_engine::analysis::project::{COMMENTS_MAX, room};
use borer_engine::analysis::utypes::APPLIED_MAX;
use borer_engine::analysis::{Analysis, Overlay, parse_addr, stated};
use borer_engine::program::{Feature, Program};
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::errors::err_params;
use crate::params::{
    Annotation, AnnotationsParams, Filter, Page, SetCommentParams, SetNameParams, SetTypeParams,
    TypesParams, field_var, must_be_a_name, must_be_in_a_section, must_fit_a_row, plan_var,
    stated_fields, stated_key, stated_values,
};
use crate::safety::{Effect, effects};
use crate::state::read_lock;

/// Tells whether `text` holds `word` as a whole identifier, not inside a
/// longer one (`a1` is not in `a12` or `data1`).
///
/// # Arguments
///
/// * `text` - The text searched.
/// * `word` - The identifier.
pub(crate) fn names_word(text: &str, word: &str) -> bool {
    let ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    !word.is_empty()
        && text.match_indices(word).any(|(i, _)| {
            !text[..i].chars().next_back().is_some_and(ident)
                && !text[i + word.len()..].chars().next().is_some_and(ident)
        })
}

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
        /// Types a reply describes before it counts the rest.
        const SHOWN: usize = 64;
        self.with_program(|p| {
            let abi = borer_engine::analysis::cdecl::Abi::of(p);
            let o = self.overlay_plain();
            let declared = borer_engine::analysis::cdecl::parse(text, &o.types, abi)
                .map_err(|e| e.to_string())?;
            let mut types = o.types.clone();
            for (name, ty, _) in &declared.types {
                types.insert(name.clone(), ty.clone());
            }
            borer_engine::analysis::utypes::validate(&types, &o.applied)
                .map_err(|e| e.to_string())?;
            if declared
                .types
                .iter()
                .any(|(name, ..)| o.types.contains_key(name))
            {
                stated::standing(p, &self.analysis_or_empty(), &o, &types)?;
            }
            let lines = borer_engine::analysis::cdecl::describe(&declared);
            let mut out = format!(
                "{} {} type(s) from C, laid out for {}:\n",
                if dry {
                    "dry-run: would define"
                } else {
                    "defined"
                },
                declared.types.len(),
                abi.name()
            );
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
            if dry {
                out.push_str("pass dry_run=false to apply.\n");
                return Ok(out);
            }
            self.edit_overlay(|o| {
                o.types
                    .extend(declared.types.into_iter().map(|(name, ty, _)| (name, ty)));
            })?;
            Ok(out)
        })
    }

    /// States a variable of a function, or a field of the class the
    /// function's object is of: `set_type` with `var`.
    ///
    /// `var` is a parameter or a stack slot as the function's text shows
    /// it, or a name stated before ([`plan_var`]). Any other `var` that
    /// spells an unnamed field as the text prints one (`field_0x270`) is
    /// that field of the function's class, stated there as `name` and
    /// `fields` state it by the class's name ([`stated::plan_at`]).
    ///
    /// # Arguments
    ///
    /// * `(p, a, o)` - The loaded program, its analysis and the overlay.
    /// * `entry` - The function `address` is in, when it is in one.
    /// * `var` - The variable or the field.
    /// * `(name, ty)` - Its new name, and its type if one is stated.
    /// * `dry` - Say what would be stated and write nothing.
    ///
    /// # Errors
    ///
    /// When `address` is in no function, the variable, the field or the
    /// name is refused, or the function's text names no such variable.
    fn state_var(
        &self,
        (p, a, o): (&Program, &Analysis, &Overlay),
        entry: Option<u64>,
        var: &str,
        (name, ty): (Option<&str>, Option<&str>),
        dry: bool,
    ) -> Result<String, String> {
        let entry = entry.ok_or_else(|| {
            "`var` names a variable of a function: give the function's `address`".to_owned()
        })?;
        if let Some(off) = field_var(var).filter(|_| stated_key(o, entry, var).is_none()) {
            let name =
                name.ok_or("naming a field needs `name`, its new name (`type` is optional)")?;
            let ty = ty
                .map(borer_engine::analysis::utypes::parse_type)
                .transpose()
                .map_err(|e| e.to_string())?;
            let name = name.to_owned();
            let plan = stated::plan_at(p, a, o, entry, off, stated::Field { name, ty })?;
            if dry {
                return Ok(format!(
                    "dry-run: would {}. pass dry_run=false to apply.",
                    plan.would()
                ));
            }
            let said = plan.done();
            self.edit_overlay(|o| plan.apply(o))?;
            return Ok(said);
        }
        let (key, named) = plan_var(p, o, entry, var, name, ty)?;
        let (stack, shadow, frame) = borer_engine::analysis::protos::slot_words(p, entry);
        let spelled = key.spell(stack, shadow, frame);
        let fname = borer_engine::analysis::name_of(a, o, entry);
        let renamed = o.vars.get(&entry).is_some_and(|v| v.contains_key(&key));
        if !renamed
            && let Some(text) = borer_engine::analysis::decompile::decompile_named(p, a, o, entry)
            && !names_word(&text, var)
            && !names_word(&text, &spelled)
        {
            return Err(format!(
                "{fname} has no variable {spelled}: its text never names it, so a type there would invent a parameter the code does not take; decompile it for the variables it has"
            ));
        }
        let what = format!("{spelled} of {fname} ({entry:#x}) {}", named.spell());
        if dry {
            return Ok(format!(
                "dry-run: would name {what}; decompile then renders it so. pass dry_run=false to apply."
            ));
        }
        self.edit_overlay(|o| {
            o.vars.entry(entry).or_default().insert(key, named);
        })?;
        Ok(format!("named {what}"))
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
        let force = force.unwrap_or(false);
        let single = pairs.len() == 1;
        self.with_analysis(Feature::Discover, |p, a, o| {
            let mut working = o.clone();
            let mut renamed = Vec::with_capacity(pairs.len());
            let mut lines = Vec::with_capacity(pairs.len());
            for (address, name) in &pairs {
                let item = |e: String| {
                    if single {
                        e
                    } else {
                        format!("{address}={name}: {e}")
                    }
                };
                let va = self.addr(p, address).map_err(item)?;
                must_be_in_a_section(p, va, Annotation::Name).map_err(item)?;
                let target = a.function_at(va).map_or(va, |f| f.entry);
                let old = borer_engine::analysis::name_of(a, &working, target);
                working.names.insert(target, name.clone());
                if !force {
                    match borer_engine::analysis::resolve(p, a, &working, name) {
                        Ok(at) if at == target => {}
                        Ok(at) => {
                            return Err(item(format!(
                                "'{name}' already names {at:#x}; pick another name, or force=true to take it"
                            )));
                        }
                        Err(why) => {
                            return Err(item(format!(
                                "'{name}' is taken ({why}); pick another name, or force=true to take it"
                            )));
                        }
                    }
                }
                let what = if a.function(target).is_some() {
                    "function"
                } else {
                    "data"
                };
                let numeric = parse_addr(name).map_or_else(String::new, |n| {
                    format!(
                        "
# note: '{name}' also reads as the number {n:#x}; an address argument finds the name first, and 0x-prefixed text is always an address"
                    )
                });
                let line = if dry {
                    format!("would set name of {what} {target:#x} ({old}) to '{name}'")
                } else {
                    format!("renamed {what} {target:#x}: {old} -> {name}")
                };
                lines.push((line, numeric));
                renamed.push((target, name.clone()));
            }
            borer_engine::analysis::project::held(&working)?;
            let joined = || {
                lines
                    .iter()
                    .map(|(line, numeric)| format!("{line}{numeric}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            };
            if dry {
                return Ok(match lines.as_slice() {
                    [(line, numeric)] => {
                        format!("dry-run: {line}. pass dry_run=false to apply.{numeric}")
                    }
                    more => format!(
                        "dry-run: {} names\n{}\npass dry_run=false to apply.",
                        more.len(),
                        joined()
                    ),
                });
            }
            self.edit_overlay(|o| o.names.extend(renamed))?;
            Ok(joined())
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
            adding(
                &read_lock(&self.overlay).comments,
                Some(va),
                "comments",
                COMMENTS_MAX,
            )?;
            if dry {
                return Ok(format!(
                    "dry-run: would set comment at {va:#x}. pass dry_run=false to apply."
                ));
            }
            self.edit_overlay(|o| {
                o.comments.insert(va, comment.clone());
            })?;
            Ok(format!("comment set at {va:#x}"))
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
    /// ([`BorerServer::state_var`]). `type` alone is C declarations, laid
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
        Parameters(SetTypeParams {
            name,
            fields,
            replace,
            values,
            size,
            address,
            r#type: ty,
            var,
            dry_run,
        }): Parameters<SetTypeParams>,
    ) -> Result<String, ErrorData> {
        let dry = dry_run.unwrap_or(true);
        if replace == Some(true) && (name.is_none() || fields.is_none() || var.is_some()) {
            return Err(err_params(
                "`replace` drops the fields `fields` does not restate, so it goes with `name` and `fields`",
            ));
        }
        if let (None, None, None, None, None, None, Some(decl)) =
            (&name, &address, &var, &fields, &values, size, &ty)
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
            .chain(&ty)
            .chain(&var)
            .chain(fields.iter().flatten())
            .chain(values.iter().flatten())
        {
            must_fit_a_row(text, Annotation::Type)?;
        }
        self.with_analysis(Feature::Discover, |p, a, o| {
            let word: u64 = if p.is_64 { 8 } else { 4 };
            let function = match &address {
                Some(text) => {
                    let va = self.addr(p, text)?;
                    must_be_in_a_section(p, va, Annotation::Type)?;
                    a.function_at(va).map(|f| f.entry)
                }
                None => None,
            };
            if let Some(var) = &var {
                let named = (name.as_deref(), ty.as_deref());
                return self.state_var((p, a, o), function, var, named, dry);
            }
            let mut fielded = None;
            let defined = match (&name, &fields, &values) {
                (Some(n), Some(fs), vs) if !fs.is_empty() || replace == Some(true) => {
                    if vs.is_some() {
                        return Err(format!(
                            "type {n} states both fields and values; a struct takes fields, an enum values"
                        ));
                    }
                    let statement = stated::Statement {
                        name: n,
                        size,
                        fields: &stated_fields(fs)?,
                        mode: stated::Mode::asked(replace.unwrap_or(false)),
                    };
                    fielded = Some(stated::plan(p, a, o, &statement)?);
                    None
                }
                (Some(n), Some(_), _) => {
                    return Err(format!(
                        "struct {n} states no fields; give fields, `values` for an enum, or a `type` for a typedef"
                    ));
                }
                (Some(n), _, Some(vs)) if !vs.is_empty() => {
                    let stated = stated_values(vs)?;
                    Some((
                        n.clone(),
                        borer_engine::analysis::utypes::build_enum(
                            n,
                            size.unwrap_or(4),
                            &stated,
                        )
                        .map_err(|e| e.to_string())?,
                    ))
                }
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
                    let target = ty.as_deref().ok_or_else(|| {
                        format!("typedef {n} needs the `type` it stands for")
                    })?;
                    let parsed = borer_engine::analysis::utypes::parse_type(target)
                        .map_err(|e| e.to_string())?;
                    Some((
                        n.clone(),
                        borer_engine::analysis::utypes::build_alias(n, &parsed, &o.types, word)
                            .map_err(|e| e.to_string())?,
                    ))
                }
                (None, _, _) => None,
            };
            let applied = match &address {
                Some(text) if function.is_none() => {
                    let spelled = ty.as_deref().ok_or_else(|| {
                        "applying a type needs the `type` to apply".to_owned()
                    })?;
                    let parsed = borer_engine::analysis::utypes::parse_type(spelled)
                        .map_err(|e| e.to_string())?;
                    let va = self.addr(p, text)?;
                    Some((va, parsed))
                }
                Some(_) | None => None,
            };
            let stated = match function {
                Some(entry) => {
                    let decl = ty.as_deref().ok_or_else(|| {
                        "at a function `type` is its prototype: `int f(Player *p, uint32_t n)`"
                            .to_owned()
                    })?;
                    let proto =
                        borer_engine::analysis::protos::Proto::parse(decl).map_err(|e| {
                            if decl.contains('(') {
                                e.to_string()
                            } else {
                                format!(
                                    "{entry:#x} is inside {}; types apply to data globals, and at a function `type` is its prototype (`int f(Player *p)`)",
                                    borer_engine::analysis::name_of(a, o, entry)
                                )
                            }
                        })?;
                    if o.prototypes.len() >= borer_engine::analysis::protos::PROTOTYPES_MAX
                        && !o.prototypes.contains_key(&entry)
                    {
                        return Err(format!(
                            "the overlay states {} prototypes, the most it holds",
                            o.prototypes.len()
                        ));
                    }
                    Some((entry, proto))
                }
                None => None,
            };
            let fresh = fielded.as_ref().and_then(stated::Plan::defined);
            let fresh = fresh.or(defined.as_ref().map(|(n, ty)| (n.as_str(), ty)));
            let types = stated::retyped(p, a, o, fresh)?;
            let applied = applied
                .map(|(va, ty)| {
                    borer_engine::analysis::utypes::width_of(&types, &ty, word).ok_or_else(|| {
                        let first = "set_type(name=..., fields=[...]) first";
                        stated::undefined(Some(a), o, &ty, first)
                    }).map(|w| (va, ty, w))
                })
                .transpose()?;
            adding(&o.applied, applied.as_ref().map(|a| a.0), "applied types", APPLIED_MAX)?;
            let mut done: Vec<String> = Vec::new();
            let mut would: Vec<String> = Vec::new();
            if let Some(plan) = &fielded {
                done.push(plan.done());
                would.push(plan.would());
            }
            if let Some((n, ty)) = &defined {
                done.push(format!("defined {}", ty.describe(n)));
                would.push(format!("define {}", ty.describe(n)));
            }
            if let Some((va, ty, width)) = &applied {
                let renders = if borer_engine::analysis::utypes::named_enum(&types, ty).is_some() {
                    "names its values"
                } else {
                    "names its fields"
                };
                done.push(format!(
                    "applied {} at {va:#x} ({width} byte(s)); decompile {renders}",
                    ty.spell()
                ));
                would.push(format!(
                    "apply {} at {va:#x} ({width} byte(s)); decompile then {renders}",
                    ty.spell()
                ));
            }
            let mut note = String::new();
            if let Some((entry, proto)) = &stated {
                let fname = borer_engine::analysis::name_of(a, o, *entry);
                done.push(format!("stated {fname} ({entry:#x}) as {}", proto.spell()));
                would.push(format!(
                    "state {fname} ({entry:#x}) as {}; decompile then renders its signature, its body and every call to it by it",
                    proto.spell()
                ));
                let bits = u8::try_from(word * 8).unwrap_or(64);
                let unknown: Vec<String> = proto
                    .ret
                    .iter()
                    .chain(proto.params.iter().map(|q| &q.ty))
                    .filter(|t| t.pass(&types, bits, p.format).is_none())
                    .map(borer_engine::analysis::protos::CType::spell)
                    .collect();
                if !unknown.is_empty() {
                    note = format!(
                        "\n# note: {} names no user type or C type word borer knows, so it passes as a word",
                        unknown.join(", ")
                    );
                }
            }
            if dry {
                return Ok(format!(
                    "dry-run: would {}. pass dry_run=false to apply.{note}",
                    would.join("; ")
                ));
            }
            self.edit_overlay(|overlay| {
                if let Some(plan) = fielded {
                    plan.apply(overlay);
                }
                if let Some((n, ty)) = defined {
                    overlay.types.insert(n, ty);
                }
                if let Some((va, ty, _)) = applied {
                    overlay.applied.insert(va, ty);
                }
                if let Some((entry, proto)) = stated {
                    overlay.prototypes.insert(entry, proto);
                }
            })?;
            Ok(format!("{}{note}", done.join("; ")))
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

/// Refuses an edit that would add an entry at `va` to a table past what a
/// project file holds, by the count the edit would leave ([`room`]), so a
/// dry run answers as its apply will.
///
/// # Arguments
///
/// * `table` - The table as it is.
/// * `va` - Where the edit adds an entry, if it adds one.
/// * `what` - The table, for the message (`comments`).
/// * `most` - Its cap.
///
/// # Errors
///
/// When the entry would take the table past its cap.
fn adding<V>(
    table: &std::collections::BTreeMap<u64, V>,
    va: Option<u64>,
    what: &str,
    most: usize,
) -> Result<(), String> {
    let Some(va) = va else {
        return Ok(());
    };
    let count = table
        .len()
        .saturating_add(usize::from(!table.contains_key(&va)));
    room(what, count, most)
}

#[cfg(test)]
mod tests;
