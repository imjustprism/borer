//! The tools that annotate: names, comments, types, and the listing of
//! every annotation the session holds.

use std::fmt::Write as _;

use borer_engine::analysis::parse_addr;
use borer_engine::program::Feature;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::errors::err_params;
use crate::params::{
    Annotation, AnnotationsParams, Filter, Page, SetCommentParams, SetNameParams, SetTypeParams,
    TypesParams, frame_words, must_be_a_name, must_be_in_a_section, must_fit_a_row, plan_var,
};
use crate::state::{read_lock, write_lock};

/// Splits one `offset:name:type` field statement.
///
/// # Arguments
///
/// * `f` - The statement, colons separating its three parts.
///
/// # Errors
///
/// When the statement is not three parts.
pub(crate) fn field_of(f: &str) -> Result<(&str, &str, &str), String> {
    f.split_once(':')
        .and_then(|(off, rest)| rest.split_once(':').map(|(name, ty)| (off, name, ty)))
        .ok_or_else(|| format!("field {f} is not offset:name:type"))
}

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
            let before = self.overlay_plain();
            write_lock(&self.overlay)
                .types
                .extend(declared.types.into_iter().map(|(name, ty, _)| (name, ty)));
            self.names_changed(&before);
            Ok(out)
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
    /// not resolve, or no section holds it.
    #[tool(
        description = "Name a function or data global in the session overlay, never the binary; names=[addr=name,...] renames many, checked first. A taken name needs force=true. Dry run until dry_run=false.",
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
            let before = self.overlay_plain();
            write_lock(&self.overlay).names.extend(renamed);
            self.names_changed(&before);
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
    /// When no binary is loaded, the address does not resolve, or no section
    /// holds it.
    #[tool(
        description = "Comment an address in the session overlay, never the binary; a comment opening with ? is an open question. To name it use set_name. Dry run until dry_run=false; save_project keeps it.",
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
            if dry {
                return Ok(format!(
                    "dry-run: would set comment at {va:#x}. pass dry_run=false to apply."
                ));
            }
            let before = self.overlay_plain();
            write_lock(&self.overlay)
                .comments
                .insert(va, comment.clone());
            self.names_changed(&before);
            Ok(format!("comment set at {va:#x}"))
        })
    }

    /// Defines a user type, applies one at an address, states a function's
    /// prototype or one of its variables.
    ///
    /// `name` with `fields` defines a struct; `name` with `values` defines
    /// an enum; `name` with `type` alone defines a typedef. `address` with
    /// `type` applies the type at that data global: the decompiler types the
    /// variable it renders there, so a `Player *` names every field read
    /// through it (`g->hp` at the width the field states) and a `State`
    /// applied at a global names every constant compared with it. At a
    /// function, `type` is its prototype as C
    /// ([`borer_engine::analysis::protos::Proto`]), which its signature,
    /// its body and every call to it follow; with `var` (`a1`, `local_58`,
    /// or a name stated before), `name` and an optional `type` name and
    /// type that variable. `type` alone is C declarations, laid out by the
    /// binary's ABI ([`BorerServer::declare_c`]). Everything is validated
    /// before anything is written: types the language does not spell,
    /// references to names nothing defines, fields that overlap, a size
    /// that does not cover the last field and an offset assertion that
    /// fails are refused with a message naming the offender.
    ///
    /// # Arguments
    ///
    /// * `SetTypeParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, a definition, an application, a prototype
    /// or a variable is refused, or the address does not resolve or no
    /// section holds it.
    #[tool(
        description = "Define a struct, enum or typedef, or apply a type at an address so decompile names its fields; at a function, type sets the prototype. To infer a class use class_layout. Checked first; dry run until dry_run=false.",
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
            values,
            size,
            address,
            r#type: ty,
            var,
            dry_run,
        }): Parameters<SetTypeParams>,
    ) -> Result<String, ErrorData> {
        let dry = dry_run.unwrap_or(true);
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
                let entry = function.ok_or_else(|| {
                    "`var` names a variable of a function: give the function's `address`".to_owned()
                })?;
                let (key, stated) = plan_var(p, o, entry, var, name.as_deref(), ty.as_deref())?;
                let (stack, shadow) = frame_words(p);
                let spelled = key.spell(stack, shadow);
                let renamed = o.vars.get(&entry).is_some_and(|v| v.contains_key(&key));
                if !renamed
                    && let Some(text) =
                        borer_engine::analysis::decompile::decompile_named(p, a, o, entry)
                    && !names_word(&text, var)
                    && !names_word(&text, &spelled)
                {
                    return Err(format!(
                        "{} has no variable {spelled}: its text never names it, so a type there would invent a parameter the code does not take; decompile it for the variables it has",
                        borer_engine::analysis::name_of(a, o, entry)
                    ));
                }
                let what = format!(
                    "{} of {} ({entry:#x}) {}",
                    key.spell(stack, shadow),
                    borer_engine::analysis::name_of(a, o, entry),
                    stated.spell()
                );
                if dry {
                    return Ok(format!(
                        "dry-run: would name {what}; decompile then renders it so. pass dry_run=false to apply."
                    ));
                }
                let before = self.overlay_plain();
                write_lock(&self.overlay)
                    .vars
                    .entry(entry)
                    .or_default()
                    .insert(key, stated);
                self.names_changed(&before);
                return Ok(format!("named {what}"));
            }
            let defined = match (&name, &fields, &values) {
                (Some(n), Some(fs), vs) if !fs.is_empty() => {
                    if vs.is_some() {
                        return Err(format!(
                            "type {n} states both fields and values; a struct takes fields, an enum values"
                        ));
                    }
                    let mut stated: Vec<(u64, String, borer_engine::analysis::utypes::TypeExpr)> =
                        Vec::with_capacity(fs.len());
                    for f in fs {
                        let (off, stated_name, ty) = field_of(f)?;
                        let ty = borer_engine::analysis::utypes::parse_type(ty)
                            .map_err(|e| format!("field {stated_name}: {e}"))?;
                        let off = off
                            .strip_prefix("0x")
                            .map_or_else(
                                || off.parse::<u64>().ok(),
                                |h| u64::from_str_radix(h, 16).ok(),
                            )
                            .ok_or_else(|| {
                                format!("field {stated_name}: offset {off} is not a number")
                            })?;
                        stated.push((off, stated_name.to_owned(), ty));
                    }
                    Some((
                        n.clone(),
                        borer_engine::analysis::utypes::build_struct(n, size, &stated, &o.types, word)
                            .map_err(|e| e.to_string())?,
                    ))
                }
                (Some(n), Some(_), _) => {
                    return Err(format!(
                        "struct {n} states no fields; give fields, `values` for an enum, or a `type` for a typedef"
                    ));
                }
                (Some(n), _, Some(vs)) if !vs.is_empty() => {
                    let mut stated: Vec<(u64, String)> = Vec::with_capacity(vs.len());
                    for v in vs {
                        let Some((stated_name, value)) = v.split_once(':') else {
                            return Err(format!("value {v} is not name:value"));
                        };
                        let value = value
                            .strip_prefix("0x")
                            .map_or_else(
                                || value.parse::<u64>().ok(),
                                |h| u64::from_str_radix(h, 16).ok(),
                            )
                            .ok_or_else(|| {
                                format!("value {stated_name}: {value} is not a number")
                            })?;
                        stated.push((value, stated_name.to_owned()));
                    }
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
            let mut types = o.types.clone();
            if let Some((n, ty)) = &defined {
                types.insert(n.clone(), ty.clone());
            }
            let applied = applied
                .map(|(va, ty)| {
                    borer_engine::analysis::utypes::width_of(&types, &ty, word).ok_or_else(|| {
                        format!(
                            "the type {} names nothing defined; set_type(name=..., fields=[...]) first",
                            ty.spell()
                        )
                    }).map(|w| (va, ty, w))
                })
                .transpose()?;
            let mut done: Vec<String> = Vec::new();
            let mut would: Vec<String> = Vec::new();
            if let Some((n, ty)) = &defined {
                match ty {
                    borer_engine::analysis::utypes::UserType::Struct(s) => {
                        done.push(format!(
                            "defined struct {n}: {} field(s), {:#x} byte(s)",
                            s.fields.len(),
                            s.size
                        ));
                        would.push(format!(
                            "define struct {n}: {} field(s), {:#x} byte(s)",
                            s.fields.len(),
                            s.size
                        ));
                    }
                    borer_engine::analysis::utypes::UserType::Enum(e) => {
                        done.push(format!(
                            "defined enum {n}: {} value(s), {:#x} byte(s)",
                            e.values.len(),
                            e.size
                        ));
                        would.push(format!(
                            "define enum {n}: {} value(s), {:#x} byte(s)",
                            e.values.len(),
                            e.size
                        ));
                    }
                    borer_engine::analysis::utypes::UserType::Alias(inner) => {
                        done.push(format!("defined typedef {n}: {}", inner.spell()));
                        would.push(format!("define typedef {n}: {}", inner.spell()));
                    }
                }
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
            let before = self.overlay_plain();
            let mut overlay = write_lock(&self.overlay);
            if let Some((n, ty)) = defined {
                overlay.types.insert(n, ty);
            }
            if let Some((va, ty, _)) = applied {
                overlay.applied.insert(va, ty);
            }
            if let Some((entry, proto)) = stated {
                overlay.prototypes.insert(entry, proto);
            }
            drop(overlay);
            self.names_changed(&before);
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
        let stated = borer_engine::analysis::protos::rows(&o.prototypes, &o.vars);
        let (_, total, table) = borer_engine::analysis::utypes::list_tsv(
            &o.types,
            &o.applied,
            &stated,
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

    /// Lists the overlay's entries: names, then findings, then open
    /// questions, a page at a time.
    ///
    /// A comment opening with a question mark is a hypothesis, not a
    /// finding. Separating the two is what makes the overlay a ledger an
    /// agent can return to: a conclusion it proved is worth building on,
    /// and one it guessed at is worth checking before it does. The ledger
    /// grows with the session, so it pages like every list: the header
    /// says `showing N of M` of the rows the filter keeps.
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
        let rows: Vec<String> = o
            .names
            .iter()
            .map(|(va, name)| format!("{:<12} name: {name}", format!("{va:#x}")))
            .chain(
                settled
                    .iter()
                    .map(|(va, c)| format!("{:<12} found: {c}", format!("{va:#x}"))),
            )
            .chain(open.iter().map(|(va, c)| {
                let claim = c.trim_start().trim_start_matches('?').trim_start();
                format!("{:<12} open:  {claim}", format!("{va:#x}"))
            }))
            .filter(|row| filter.accepts(row))
            .collect();
        let counts = format!(
            "{} names, {} findings, {} open question(s)",
            o.names.len(),
            settled.len(),
            open.len()
        );
        let total = rows.len();
        if page.count_only {
            return Ok(format!("# {total} annotations ({counts})\n"));
        }
        let shown: Vec<&String> = rows.iter().skip(page.offset).take(page.limit.n).collect();
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

#[cfg(test)]
mod tests {
    use crate::testing::raw_server;

    /// A rename and a comment each let go of the text read under the names
    /// before them: the old text is not kept beside the new one, and the
    /// new one carries the name.
    ///
    /// # Panics
    ///
    /// When a text read under replaced names stays held, or the text read
    /// after the rename lacks the new name.
    #[test]
    fn a_rename_lets_go_of_the_text_read_under_the_old_names() {
        use crate::params::DecompileParams;
        use crate::params::SetCommentParams;
        use crate::params::SetNameParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        let decompile = || {
            server
                .decompile(Parameters(DecompileParams {
                    address: "0x1000".to_owned(),
                    detail: None,
                    filter: None,
                    offset: None,
                    limit: Some(u32::MAX),
                }))
                .expect("decompiles")
        };
        let held = || {
            server
                .analysis(borer_engine::program::Feature::Decompile)
                .expect("analyzed")
                .derived
                .held("plain_text")
        };
        assert!(!decompile().contains("renamed"));
        assert_eq!(held(), 1);
        server
            .set_name(Parameters(SetNameParams {
                address: Some("0x1000".to_owned()),
                name: Some("renamed".to_owned()),
                names: None,
                force: None,
                dry_run: Some(false),
            }))
            .expect("renames");
        assert_eq!(held(), 0, "the text under the old name is let go");
        assert!(decompile().contains("renamed"));
        assert_eq!(held(), 1);
        server
            .set_comment(Parameters(SetCommentParams {
                address: "0x1000".to_owned(),
                comment: "seen".to_owned(),
                dry_run: Some(false),
            }))
            .expect("comments");
        assert_eq!(held(), 0, "the text without the comment is let go");
    }

    /// A rename of an address a text did not read keeps the text, filed
    /// under the new names, so the next decompile builds nothing.
    ///
    /// # Panics
    ///
    /// When the text is let go, or the decompile after the rename builds
    /// a result or answers other bytes.
    #[test]
    fn a_rename_keeps_the_texts_that_did_not_read_the_name() {
        use crate::params::DecompileParams;
        use crate::params::SetNameParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        let decompile = || {
            server
                .decompile(Parameters(DecompileParams {
                    address: "0x1000".to_owned(),
                    detail: None,
                    filter: None,
                    offset: None,
                    limit: Some(u32::MAX),
                }))
                .expect("decompiles")
        };
        let derived = || {
            let a = server
                .analysis(borer_engine::program::Feature::Decompile)
                .expect("analyzed");
            (a.derived.held("plain_text"), a.derived.builds())
        };
        let text = decompile();
        assert_eq!(derived().0, 1);
        server
            .set_name(Parameters(SetNameParams {
                address: Some("0x1080".to_owned()),
                name: Some("elsewhere".to_owned()),
                names: None,
                force: None,
                dry_run: Some(false),
            }))
            .expect("renames");
        let (held, built) = derived();
        assert_eq!(held, 1, "the text is carried over");
        assert_eq!(decompile(), text);
        assert_eq!(derived(), (1, built), "the decompile built nothing");
    }

    /// `set_name` refuses a name that is not an identifier and one another
    /// address holds unless forced, and `names` renames many in one call,
    /// checking all before applying any.
    ///
    /// # Panics
    ///
    /// When a bad or taken name is accepted, or the batch applies in part.
    #[test]
    fn set_name_refuses_bad_and_taken_names_and_renames_in_batches() {
        use crate::params::SetNameParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        let set = |address: Option<&str>, name: Option<&str>, names: Option<&[&str]>, force| {
            server.set_name(Parameters(SetNameParams {
                address: address.map(str::to_owned),
                name: name.map(str::to_owned),
                names: names.map(|n| n.iter().map(|s| (*s).to_owned()).collect()),
                force,
                dry_run: Some(false),
            }))
        };
        let spaced = set(Some("0x1000"), Some("foo bar"), None, None).expect_err("a space");
        assert!(spaced.message.contains("holds ' '"), "{}", spaced.message);
        let digit = set(Some("0x1000"), Some("1st"), None, None).expect_err("a digit");
        assert!(
            digit.message.contains("opens with a digit"),
            "{}",
            digit.message
        );
        set(Some("0x1000"), Some("Foo::bar<int>"), None, None).expect("a C++ name");
        set(Some("0x1010"), Some("main"), None, None).expect("a free name");
        let taken = set(Some("0x1020"), Some("main"), None, None).expect_err("taken");
        assert!(
            taken.message.contains("0x1010") && taken.message.ends_with("force=true to take it"),
            "{}",
            taken.message
        );
        set(Some("0x1020"), Some("main"), None, Some(true)).expect("forced");
        assert!(set(None, None, None, None).is_err(), "nothing asked");
        let half = set(None, None, Some(&["0x1030=one", "0x1040=two words"]), None);
        assert!(half.is_err(), "one bad name refuses the batch");
        let bad_pair =
            set(None, None, Some(&["0x1030=one", "0x1040=one"]), None).expect_err("one name twice");
        assert!(
            bad_pair.message.starts_with("0x1040=one: 'one' ")
                && bad_pair.message.contains("0x1030"),
            "{}",
            bad_pair.message
        );
        assert!(
            !crate::state::read_lock(&server.overlay)
                .names
                .values()
                .any(|n| n == "one"),
            "a refused batch applies nothing"
        );
        let both = set(None, None, Some(&["0x1030=one", "0x1040 = two"]), None).expect("renames");
        assert_eq!(both.lines().count(), 2, "{both}");
        let names = &crate::state::read_lock(&server.overlay).names;
        assert_eq!(names.get(&0x1030).map(String::as_str), Some("one"));
        assert_eq!(names.get(&0x1040).map(String::as_str), Some("two"));
    }

    /// A name that reads as a number is noted when set and reaches its
    /// function afterwards.
    ///
    /// `0x` text stays the address, and bare digits naming nothing are
    /// decimal, with the hex spelling suggested when that is the function
    /// meant.
    ///
    /// # Panics
    ///
    /// When the note is missing, the name does not resolve, or the decimal
    /// reading is not explained.
    #[test]
    fn a_name_that_reads_as_a_number_is_noted_and_reachable() {
        use crate::params::FunctionDetailParams;
        use crate::params::SetNameParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        let set = server
            .set_name(Parameters(SetNameParams {
                address: Some("0x1000".to_owned()),
                name: Some("cafe".to_owned()),
                names: None,
                force: None,
                dry_run: Some(false),
            }))
            .expect("renames");
        assert!(set.contains("also reads as the number 0xcafe"), "{set}");
        let function = |address: &str| {
            server.function(Parameters(FunctionDetailParams {
                address: address.to_owned(),
                offset: None,
            }))
        };
        let by_name = function("cafe").expect("the name resolves");
        assert!(by_name.contains("cafe"), "{by_name}");
        assert!(function("0xcafe").is_err(), "0x text is the address");
        let decimal = function("1000").expect_err("decimal 1000 is 0x3e8");
        assert!(
            decimal
                .message
                .contains("bare digits are decimal, write 0x1000"),
            "{decimal:?}"
        );
    }

    /// `set_type` dry-runs by default, defines a struct and applies it at a
    /// data global, and `types` lists both.
    ///
    /// A type the language does not spell, a field naming nothing defined
    /// and a global inside a function are refused with a message naming
    /// the offender.
    ///
    /// # Panics
    ///
    /// When the dry run writes, the listing misses what was stated, or a
    /// refusal accepts.
    #[test]
    fn set_type_defines_applies_and_refuses() {
        use crate::params::SetTypeParams;
        use crate::params::TypesParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(
            vec![0xcc; 0x200],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text, data],
        );
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let fields = || vec!["0x18:hp:u32".to_owned(), "0x1c:mp:u32".to_owned()];
        let out = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Player".to_owned()),
                fields: Some(fields()),
                values: None,
                size: None,
                address: Some("0x2000".to_owned()),
                r#type: Some("Player *".to_owned()),
                var: None,
                dry_run: None,
            }))
            .expect("dry-runs");
        assert!(
            out.starts_with("dry-run: would define struct Player"),
            "{out}"
        );
        let listed = server
            .types(Parameters(TypesParams {
                filter: None,
                offset: None,
                limit: None,
                count_only: Some(true),
            }))
            .expect("lists");
        assert!(listed.contains("0 rows (0 type(s), 0 applied)"), "{listed}");
        let out = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Player".to_owned()),
                fields: Some(fields()),
                values: None,
                size: None,
                address: Some("0x2000".to_owned()),
                r#type: Some("Player *".to_owned()),
                var: None,
                dry_run: Some(false),
            }))
            .expect("defines and applies");
        assert!(
            out.contains("defined struct Player: 2 field(s), 0x20 byte(s)"),
            "{out}"
        );
        assert!(out.contains("applied Player * at 0x2000"), "{out}");
        let listed = server
            .types(Parameters(TypesParams {
                filter: Some("player".to_owned()),
                offset: None,
                limit: None,
                count_only: None,
            }))
            .expect("lists");
        assert!(
            listed.contains("struct\tPlayer\t0x20\t0x18 hp u32, 0x1c mp u32"),
            "{listed}"
        );
        assert!(listed.contains("applied\t0x2000\t-\tPlayer *"), "{listed}");
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: None,
                fields: None,
                values: None,
                size: None,
                address: Some("0x2000".to_owned()),
                r#type: Some("three of them".to_owned()),
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("garbage refused");
        assert!(bad.message.contains("'three of them'"), "{}", bad.message);
        let mut unknown = fields();
        unknown.push("0x20:next:Missing *".to_owned());
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Player".to_owned()),
                fields: Some(unknown),
                values: None,
                size: None,
                address: None,
                r#type: None,
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("unknown name refused");
        assert!(
            bad.message.contains("resolves to no size"),
            "{}",
            bad.message
        );
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: None,
                fields: None,
                values: None,
                size: None,
                address: Some("0x1000".to_owned()),
                r#type: Some("u32".to_owned()),
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("code refused");
        assert!(
            bad.message.contains("types apply to data globals"),
            "{}",
            bad.message
        );
    }

    /// `borer://layout/...,apply=Name` and `class_layout(apply=)` define a
    /// struct and type the parameter, dry-run by default.
    ///
    /// The dry run names the struct and the prototype and writes nothing;
    /// `dry_run=false` writes both and the re-decompiled function reads
    /// `a1->f_10`; a script cannot apply through `query`.
    ///
    /// # Panics
    ///
    /// When the dry run writes, the applied text misses a field, or a
    /// refusal accepts.
    #[test]
    fn a_layout_applies_as_a_struct_on_request() {
        use crate::params::ClassLayoutParams;
        use crate::params::DecompileParams;
        use crate::params::ScriptParams;
        use crate::params::TypesParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut bytes = vec![0xccu8; 0x1000];
        bytes[..12].copy_from_slice(&[
            0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
            0x48, 0x03, 0x41, 0x18, // ASM: add rax, [rcx+0x18]
            0xc6, 0x41, 0x20, 0x01, // ASM: mov byte [rcx+0x20], 1
            0xc3, // ASM: ret
        ]);
        let text = Section::mapped(".text", 0x401_000, 0, 0x1000, false, true);
        let program = Program::raw(bytes, Arch::X86_64, 0x400_000, Some(0x401_000), vec![text]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let types = || {
            server
                .types(Parameters(TypesParams {
                    filter: None,
                    offset: None,
                    limit: None,
                    count_only: Some(true),
                }))
                .expect("lists")
        };
        let dry = server
            .resource_text("borer://layout/0x401000,rcx,apply=Rec")
            .expect("a dry run");
        assert_eq!(
            dry,
            "dry-run: would define struct Rec and state 1 prototype(s); decompile then names the fields:\nstruct Rec (0x21 bytes): 0x10 f_10 u32, 0x18 f_18 u64, 0x20 f_20 u8\nprototype sub_401000 (0x401000): uint64_t (Rec *)\npass dry_run=false to apply.\n"
        );
        assert!(types().starts_with("# 0 rows"), "{}", types());
        let scripted = server
            .script(Parameters(ScriptParams {
                code: "print(query(\"borer://layout/0x401000,apply=Rec,dry_run=false\"));"
                    .to_owned(),
                dry_run: None,
            }))
            .expect("a script answers");
        assert!(
            scripted.contains("applies nothing through query"),
            "{scripted}"
        );
        assert!(types().starts_with("# 0 rows"), "{}", types());
        let done = server
            .resource_text("borer://layout/0x401000,apply=Rec,dry_run=false")
            .expect("applies");
        assert!(
            done.starts_with("defined struct Rec and stated 1 prototype(s)"),
            "{done}"
        );
        assert!(
            types().starts_with("# 2 rows (1 type(s), 0 applied)"),
            "{}",
            types()
        );
        let text = server
            .decompile(Parameters(DecompileParams {
                address: "0x401000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: None,
            }))
            .expect("decompiles");
        assert!(text.contains("a1->f_10"), "{text}");
        assert!(text.contains("a1->f_20 = 1;"), "{text}");
        let bad = server
            .resource_text("borer://layout/0x401003,apply=Rec")
            .expect_err("mid-function");
        assert!(
            bad.message.contains("carries no parameter"),
            "{}",
            bad.message
        );
        let no_class = server
            .class_layout(Parameters(ClassLayoutParams {
                class: "Nope".to_owned(),
                apply: Some("N".to_owned()),
                dry_run: None,
            }))
            .expect_err("no such class");
        assert!(
            no_class.message.contains("no function belongs"),
            "{}",
            no_class.message
        );
    }

    /// `set_type` with `type` alone reads C declarations by the binary's ABI.
    ///
    /// The dry run shows the offsets and writes nothing, the applied struct
    /// reads with `read type=`, and a failing offset assertion is refused
    /// with the field named.
    ///
    /// # Panics
    ///
    /// When a layout differs, the dry run writes, or a refusal accepts.
    #[test]
    fn set_type_reads_c_declarations() {
        use crate::params::ReadParams;
        use crate::params::SetTypeParams;
        use crate::params::TypesParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let decl = |server: &crate::BorerServer, text: &str, dry_run: Option<bool>| {
            server.set_type(Parameters(SetTypeParams {
                name: None,
                fields: None,
                values: None,
                size: None,
                address: None,
                r#type: Some(text.to_owned()),
                var: None,
                dry_run,
            }))
        };
        let server_for = |arch: Arch| {
            let mut bytes = vec![0u8; 0x200];
            bytes[0x100] = b'A';
            bytes[0x104..0x108].copy_from_slice(&7u32.to_le_bytes());
            let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
            let program = Program::raw(bytes, arch, 0, None, vec![data]);
            crate::BorerServer {
                program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                    program,
                )))),
                pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
                ..crate::BorerServer::default()
            }
        };
        let text = "#pragma pack(push, 8)\nstruct S {\n  char c;\n  int n;   // @0x4\n  char *p;\n};\n#pragma pack(pop)\nstatic_assert(sizeof(S) == 16);";
        let x64 = server_for(Arch::X86_64);
        let dry = decl(&x64, text, None).expect("dry-runs");
        assert_eq!(
            dry,
            "dry-run: would define 1 type(s) from C, laid out for x64 Windows:\nstruct S (0x10 bytes, align 8): 0x0 c char, 0x4 n i32, 0x8 p char *\npass dry_run=false to apply.\n"
        );
        let listed = x64
            .types(Parameters(TypesParams {
                filter: None,
                offset: None,
                limit: None,
                count_only: Some(true),
            }))
            .expect("lists");
        assert!(listed.contains("0 rows (0 type(s)"), "{listed}");
        let done = decl(&x64, text, Some(false)).expect("defines");
        assert!(done.starts_with("defined 1 type(s) from C"), "{done}");
        let read = x64
            .read(Parameters(ReadParams {
                address: "0x2000".to_owned(),
                kind: None,
                r#type: Some("S".to_owned()),
                count: None,
            }))
            .expect("reads");
        assert!(read.contains("0x2000       c char   'A'\n"), "{read}");
        assert!(read.contains("0x2004       n i32    7\n"), "{read}");
        let x86 = server_for(Arch::X86);
        let narrow = decl(&x86, "struct S { char c; int n; char *p; };", None).expect("x86");
        assert!(
            narrow.contains("laid out for x86 Windows:\nstruct S (0xc bytes, align 4)"),
            "{narrow}"
        );
        let wrong = decl(
            &x64,
            "struct T {\n  char c;\n  int n;   // @0x2\n};",
            Some(false),
        )
        .expect_err("a failing assertion");
        assert!(
            wrong.message.contains(
                "line 3: field n of struct T is at 0x4 under x64 Windows layout, not 0x2"
            ),
            "{}",
            wrong.message
        );
    }

    /// `read` with `type` lays a defined struct over the bytes: `count`
    /// records, each field a row with a `char` array quoted; a kind beside
    /// a type, and a file offset, are refused.
    ///
    /// # Panics
    ///
    /// When a row is missing or a refusal accepts.
    #[test]
    fn read_lays_a_user_type_over_the_bytes() {
        use crate::params::ReadKind;
        use crate::params::ReadParams;
        use crate::params::SetTypeParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut bytes = vec![0u8; 0x200];
        bytes[0x100..0x104].copy_from_slice(&7u32.to_le_bytes());
        bytes[0x104..0x108].copy_from_slice(b"hi\0\0");
        bytes[0x108..0x10c].copy_from_slice(&9u32.to_le_bytes());
        bytes[0x10c..0x110].copy_from_slice(b"yo\0\0");
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(bytes, Arch::X86_64, 0, None, vec![data]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        server
            .set_type(Parameters(SetTypeParams {
                name: Some("Item".to_owned()),
                fields: Some(vec!["0:id:u32".to_owned(), "4:tag:char[4]".to_owned()]),
                values: None,
                size: None,
                address: None,
                r#type: None,
                var: None,
                dry_run: Some(false),
            }))
            .expect("defines");
        let read = |kind: Option<ReadKind>, ty: &str, address: &str, count: Option<u32>| {
            server.read(Parameters(ReadParams {
                address: address.to_owned(),
                kind,
                r#type: Some(ty.to_owned()),
                count,
            }))
        };
        let text = read(None, "Item", "0x2000", Some(2)).expect("reads");
        assert!(
            text.starts_with("# showing 4 of 4 rows: Item[2] at 0x2000 in .data, 0x10 bytes\n"),
            "{text}"
        );
        assert!(
            text.contains("0x2004       [0].tag char[4] \"hi\"\n"),
            "{text}"
        );
        assert!(
            text.contains("0x2008       [1].id  u32     0x9\n"),
            "{text}"
        );
        let one = read(None, "Item", "0x2008", None).expect("reads one");
        assert!(one.contains("0x200c       tag char[4] \"yo\"\n"), "{one}");
        let both = read(Some(ReadKind::U8), "Item", "0x2000", None).expect_err("kind and type");
        assert!(both.message.contains("give one"), "{}", both.message);
        let off = read(None, "Item", "off:0x100", None).expect_err("an offset");
        assert!(off.message.contains("takes an address"), "{}", off.message);
        let bad = read(None, "Item[", "0x2000", None).expect_err("an open bracket");
        assert!(bad.message.contains("does not close"), "{}", bad.message);
    }

    /// `set_type` with `values` defines an enum, applies it at a data
    /// global, and `types` lists its values in value order.
    ///
    /// A value under two names, and fields stated beside values, are
    /// refused with a message naming the offender.
    ///
    /// # Panics
    ///
    /// When the listing misses the enum, or a refusal accepts.
    #[test]
    fn set_type_defines_enums_and_refuses() {
        use crate::params::SetTypeParams;
        use crate::params::TypesParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(
            vec![0xcc; 0x200],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text, data],
        );
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let out = server
            .set_type(Parameters(SetTypeParams {
                name: Some("State".to_owned()),
                fields: None,
                values: Some(vec!["Run:1".to_owned(), "Idle:0".to_owned()]),
                size: None,
                address: Some("0x2000".to_owned()),
                r#type: Some("State".to_owned()),
                var: None,
                dry_run: Some(false),
            }))
            .expect("defines and applies");
        assert!(
            out.contains("defined enum State: 2 value(s), 0x4 byte(s)"),
            "{out}"
        );
        assert!(
            out.contains("applied State at 0x2000 (4 byte(s)); decompile names its values"),
            "{out}"
        );
        let listed = server
            .types(Parameters(TypesParams {
                filter: Some("state".to_owned()),
                offset: None,
                limit: None,
                count_only: None,
            }))
            .expect("lists");
        assert!(
            listed.contains("enum\tState\t0x4\tIdle = 0, Run = 1"),
            "{listed}"
        );
        assert!(listed.contains("applied\t0x2000\t-\tState"), "{listed}");
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Bad".to_owned()),
                fields: None,
                values: Some(vec!["A:0".to_owned(), "B:0".to_owned()]),
                size: None,
                address: None,
                r#type: None,
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("a duplicate value refused");
        assert!(
            bad.message.contains("names value 0 twice"),
            "{}",
            bad.message
        );
        let bad = server
            .set_type(Parameters(SetTypeParams {
                name: Some("Bad".to_owned()),
                fields: Some(vec!["0x0:f:u32".to_owned()]),
                values: Some(vec!["A:0".to_owned()]),
                size: None,
                address: None,
                r#type: None,
                var: None,
                dry_run: Some(false),
            }))
            .expect_err("fields beside values refused");
        assert!(
            bad.message.contains("both fields and values"),
            "{}",
            bad.message
        );
    }

    /// `set_type` refuses a type with more pointers than the language
    /// holds, on a dry run too, rather than building a chain of boxes whose
    /// spelling and drop overflowed the stack and took the server down.
    ///
    /// # Panics
    ///
    /// When a deep type is accepted or the refusal does not say why.
    #[test]
    fn set_type_refuses_a_type_too_deep_to_walk() {
        use crate::params::SetTypeParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let data = Section::mapped(".data", 0x2000, 0, 0x100, true, false);
        let program = Program::raw(vec![0; 0x100], Arch::X86_64, 0, None, vec![data]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let refuse = |name: Option<&str>, address: Option<&str>, ty: &str| {
            server
                .set_type(Parameters(SetTypeParams {
                    name: name.map(str::to_owned),
                    fields: None,
                    values: None,
                    size: None,
                    address: address.map(str::to_owned),
                    r#type: Some(ty.to_owned()),
                    var: None,
                    dry_run: None,
                }))
                .expect_err("a type too deep to walk was accepted")
                .message
        };
        let deep = format!("u8 {}", "*".repeat(17));
        let long = format!("u8 {}", "*".repeat(20_000));
        for (name, address) in [(Some("Stars"), None), (None, Some("0x2000"))] {
            let refused = refuse(name, address, &deep);
            assert!(refused.contains("stacks 17 pointers"), "{refused}");
            let refused = refuse(name, address, &long);
            assert!(
                refused.contains("the type is 20003 characters"),
                "{refused}"
            );
        }
    }

    /// `set_type` at a function states its prototype, and with `var` one of
    /// its variables.
    ///
    /// Dry runs leave the overlay's fingerprint as it was; applying states
    /// the prototype, and a variable is then found by the name the
    /// prototype gave it; a register and a data address are refused.
    ///
    /// # Panics
    ///
    /// When a dry run writes, an application does not, or a refusal is
    /// accepted.
    #[test]
    fn set_type_states_prototypes_and_variables() {
        use crate::params::SetTypeParams;
        use borer_engine::analysis::protos::VarKey;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut bytes = vec![0xcc; 0x200];
        // ASM: lea eax, [rcx+1]; ret
        bytes[..4].copy_from_slice(&[0x8d, 0x41, 0x01, 0xc3]);
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text, data]);
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        };
        let call = |address: &str,
                    ty: Option<&str>,
                    var: Option<&str>,
                    name: Option<&str>,
                    dry: Option<bool>| {
            server.set_type(Parameters(SetTypeParams {
                name: name.map(str::to_owned),
                fields: None,
                values: None,
                size: None,
                address: Some(address.to_owned()),
                r#type: ty.map(str::to_owned),
                var: var.map(str::to_owned),
                dry_run: dry,
            }))
        };
        let before = server.overlay_plain().fingerprint();
        let out = call("0x1000", Some("int f(int n)"), None, None, None).expect("dry-runs");
        assert!(
            out.starts_with("dry-run: would state sub_1000 (0x1000) as int (int n)"),
            "{out}"
        );
        assert_eq!(server.overlay_plain().fingerprint(), before);
        let out = call("0x1002", Some("int f(int n)"), None, None, Some(false)).expect("states");
        assert!(
            out.contains("stated sub_1000 (0x1000) as int (int n)"),
            "{out}"
        );
        let stated = server.overlay_plain().fingerprint();
        assert_ne!(stated, before);
        let out = call("0x1000", Some("Mystery *"), Some("n"), Some("thing"), None)
            .expect("dry-runs the variable");
        assert!(
            out.starts_with("dry-run: would name a1 of sub_1000 (0x1000) Mystery *thing"),
            "{out}"
        );
        assert_eq!(server.overlay_plain().fingerprint(), stated);
        call("0x1000", None, Some("n"), Some("count"), Some(false)).expect("names");
        let o = server.overlay_plain();
        assert_eq!(
            o.vars
                .get(&0x1000)
                .and_then(|v| v.get(&VarKey::Param(0)))
                .map(|v| v.name.as_str()),
            Some("count")
        );
        let refused = call("0x1000", None, Some("rax"), Some("x"), None)
            .expect_err("a register was named")
            .message;
        assert!(refused.contains("register"), "{refused}");
        let refused = call("0x2000", None, Some("a1"), Some("x"), None)
            .expect_err("a variable outside any function was named")
            .message;
        assert!(refused.contains("function"), "{refused}");
        let refused = call("0x1000", None, Some("a3"), Some("x"), None)
            .expect_err("a parameter the function does not take was named")
            .message;
        assert!(
            refused.starts_with("sub_1000 has no variable a3"),
            "{refused}"
        );
        let refused = call("0x1000", Some("int f(int n"), None, None, None)
            .expect_err("a prototype with an open parameter list was stated")
            .message;
        assert!(refused.contains("parameter list"), "{refused}");
        let refused = call("0x1000", Some("u32"), None, None, None)
            .expect_err("a plain type was stated at a function")
            .message;
        assert!(refused.contains("types apply to data globals"), "{refused}");
    }

    /// `set_comment` refuses an address in no section as `set_name` does,
    /// dry run or not, and still previews one inside a section.
    ///
    /// # Panics
    ///
    /// When a comment outside the image is accepted, the two refusals
    /// differ beyond the annotation's name, or a mapped address is refused.
    #[test]
    fn a_comment_outside_every_section_is_refused_as_a_name_is() {
        use crate::params::SetCommentParams;
        use crate::params::SetNameParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        let comment = |address: &str, dry_run| {
            server.set_comment(Parameters(SetCommentParams {
                address: address.to_owned(),
                comment: "typo".to_owned(),
                dry_run,
            }))
        };
        let refused = comment("0x1", Some(false)).expect_err("outside the image");
        assert!(
            refused
                .message
                .starts_with("0x1 is in no section, so nothing there can take a comment; "),
            "{}",
            refused.message
        );
        assert!(comment("0x1", None).is_err(), "a dry run is refused too");
        let named = server
            .set_name(Parameters(SetNameParams {
                address: Some("0x1".to_owned()),
                name: Some("typo".to_owned()),
                names: None,
                force: None,
                dry_run: None,
            }))
            .expect_err("outside the image");
        assert_eq!(named.code, refused.code);
        assert_eq!(
            named.message,
            refused.message.replace("a comment", "a name")
        );
        let preview = comment("0x1010", None).expect("inside .text");
        assert!(
            preview.starts_with("dry-run: would set comment at 0x1010"),
            "{preview}"
        );
        assert!(crate::state::read_lock(&server.overlay).comments.is_empty());
    }
}
