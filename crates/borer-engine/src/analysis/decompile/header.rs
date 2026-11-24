//! The signature a decompiled function's text opens with: its name, its
//! result type and its parameters, as the `// signature:` line prints them.

use super::*;

/// The function's signature as the header prints it.
pub(super) struct Head {
    /// The function's name.
    pub(super) name: String,
    /// The result type, as a declaration spells it.
    pub(super) ret_ty: String,
    /// The parameters in the order printed, each as `type name`, `...` last
    /// for a variadic function.
    pub(super) params: Vec<String>,
    /// The places the code shows a whole word ([`wide_params`]).
    pub(super) wide: BTreeSet<usize>,
}

/// Returns the signature the header prints for a function.
///
/// The result type is the one the body returns at the width it returns
/// it, unless a stated, library or debug prototype says otherwise; each
/// parameter takes, in order, a type the user stated, the prototype's, a
/// class hint, the debug information's or what the body shows of it
/// (`typed`), and the machine word or `float` when nothing does.
///
/// # Arguments
///
/// * `ctx` - The function's state: its program, analysis, names in force,
///   convention and debug facts.
/// * `f` - The function.
/// * `shape` - What it takes ([`Shape`]).
/// * `names` - The names its text uses.
/// * `typed` - The types the body shows, by position ([`param_types`]).
/// * `value_return` - The body returns a value.
///
/// # Returns
///
/// The name, the result type, the parameters and the wide places.
pub(super) fn head(
    ctx: &Ctx<'_>,
    f: &Function,
    shape: &Shape,
    names: &Names<'_>,
    typed: &BTreeMap<usize, String>,
    value_return: bool,
) -> Head {
    let (analysis, overlay) = (ctx.analysis, ctx.overlay);
    let name = name_of(analysis, overlay, f.entry);
    let (ret_ty, declared) = prototype(ctx, f, shape, &name, value_return);
    let var_typed: BTreeSet<usize> = overlay
        .vars
        .get(&f.entry)
        .into_iter()
        .flatten()
        .filter_map(|(k, v)| match (k, &v.ty) {
            (VarKey::Param(i), Some(_)) => Some(usize::from(*i)),
            (VarKey::Param(_), None) | (VarKey::Slot(_), _) => None,
        })
        .collect();
    let class = classes::class_of(crate::analysis::bare_name(&name)).unwrap_or("");
    let result_at = ctx.result_param.map(usize::from);
    let lead = usize::from(ctx.this_param)
        + usize::from(result_at.is_some_and(|r| r <= usize::from(ctx.this_param)));
    let floats = shape.floats();
    let mut params: Vec<String> = (0..shape.count)
        .map(|i| {
            let unread = || {
                ctx.debug_params
                    .get(i)
                    .map(|p| p.name.clone())
                    .filter(|n| !n.is_empty())
                    .unwrap_or_else(|| format!("a{}", i + 1))
            };
            let key = u8::try_from(i)
                .ok()
                .filter(|_| {
                    ctx.conv
                        .arg_reg(i, floats)
                        .is_some_and(|r| ctx.params.contains(&r))
                })
                .map_or_else(unread, |p| names.key(Key::Param(p)));
            if ctx.this_param && i == 0 {
                let this_class = if class.is_empty() {
                    f.param_hints.get(&0).map_or("void", String::as_str)
                } else {
                    class
                };
                return format!("{this_class} *this");
            }
            if result_at == Some(i) {
                return format!("{ret_ty} *result");
            }
            let hint = u8::try_from(i).ok().and_then(|p| f.param_hints.get(&p));
            let float_only = floats & (1u8 << i.min(7)) != 0;
            let plain = if float_only {
                "float"
            } else {
                word_type(ctx.bitness)
            };
            let hint = hint.filter(|_| !float_only);
            let recorded = ctx
                .debug_params
                .get(i)
                .and_then(|p| p.type_name.clone())
                .or_else(|| typed.get(&i).cloned());
            let stated_ty = recorded.clone().filter(|_| var_typed.contains(&i));
            match (
                stated_ty
                    .as_ref()
                    .or_else(|| i.checked_sub(lead).and_then(|j| declared.get(j))),
                hint,
                recorded,
            ) {
                (Some(ty), _, _) if ty.ends_with('*') || ty.ends_with('&') => {
                    format!("{ty}{key}")
                }
                (Some(ty), _, _) => format!("{ty} {key}"),
                (None, Some(c), _) => format!("{c} *{key}"),
                (None, None, Some(ty)) if ty.ends_with(['*', '&']) => format!("{ty}{key}"),
                (None, None, Some(ty)) => format!("{ty} {key}"),
                (None, None, None) => format!("{plain} {key}"),
            }
        })
        .collect();
    let wide = wide_params(typed, &params, ctx.bitness);
    if let Some(r) = result_at.filter(|r| *r < params.len()) {
        let at = abi::indirect_result_position(ctx.this_param);
        let result = params.remove(r);
        params.insert(at.min(params.len()), result);
    }
    if ctx.variadic {
        params.push("...".to_owned());
    }
    Head {
        name,
        ret_ty,
        params,
        wide,
    }
}

/// Returns the result type and the declared parameter types a function's
/// header prints.
///
/// The result is the width the body returns, unless a stated, library,
/// debug or class-hint prototype says otherwise; the declared types come
/// from the debug information when a prototype is stated, else from the
/// function's signature or the type library's prototype of its name.
///
/// # Arguments
///
/// * `ctx` - The function's state.
/// * `f` - The function.
/// * `shape` - What it takes ([`Shape`]).
/// * `name` - Its name as the header prints it.
/// * `value_return` - The body returns a value.
///
/// # Returns
///
/// The result type and the declared types, from the first parameter after
/// `this` and the hidden result pointer.
fn prototype(
    ctx: &Ctx<'_>,
    f: &Function,
    shape: &Shape,
    name: &str,
    value_return: bool,
) -> (String, Vec<String>) {
    let program = ctx.program;
    let inferred = match (value_return, ctx.ret_bits) {
        (false, _) => "void",
        (true, _) if f.ret_float == Some(32) || ctx.x87_ret == 32 => "float",
        (true, _) if f.ret_float.is_some() => "double",
        (true, 32) if ctx.ret_sse => "float",
        (true, _) if ctx.ret_sse => "double",
        (true, 8) => "uint8_t",
        (true, 16) => "uint16_t",
        (true, 32) => "uint32_t",
        (true, _) => word_type(ctx.bitness),
    };
    let ret_ty = ctx.debug_ret.as_deref().unwrap_or(inferred);
    let library = (ctx.stated.is_none()
        && f.signature.is_none()
        && ctx.debug_ret.is_none()
        && ctx.debug_params.is_empty())
    .then(|| {
        signature::library_prototype(
            crate::analysis::bare_name(name),
            program.format,
            shape.count,
            ctx.variadic,
            value_return,
        )
    })
    .flatten();
    let declared: Vec<String> = match ctx.stated {
        Some(_) => ctx
            .debug_params
            .iter()
            .map(|p| p.type_name.clone().unwrap_or_default())
            .collect(),
        None => f.signature.as_ref().map_or_else(
            || {
                library.as_ref().map_or_else(Vec::new, |(_, params)| {
                    params.iter().map(|p| (*p).to_owned()).collect()
                })
            },
            |s| s.params.clone(),
        ),
    };
    let ret_ty = f.signature.as_ref().map_or_else(
        || match &library {
            Some((ret, _)) => (*ret).to_owned(),
            None => f
                .ret_hint
                .as_ref()
                .filter(|_| f.ret_float.is_none())
                .map_or(ret_ty.to_owned(), |c| format!("{c} *")),
        },
        |s| s.ret.clone(),
    );
    let ret_ty = match ctx.stated {
        Some(_) => ctx.debug_ret.clone().unwrap_or_else(|| "void".to_owned()),
        None => ret_ty,
    };
    (ret_ty, declared)
}
