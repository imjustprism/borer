//! The names a text gives things of the binary, resolved once per set of
//! names in force.

use super::*;

/// Every name a text may give something of the binary, with everything it
/// is.
///
/// The image base, the functions (in address order, where several share a
/// name), the vtables, the known tables and the symbols, in that order of
/// precedence; a data symbol under the name the text spells it
/// ([`data_name`](crate::analysis::decompile::expr_render::data_name): `f.tab` is `f_tab`), and
/// an import's slot also under its linker name `__imp_name`, which a
/// wrapper of the same name calls it by.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
fn names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
) -> FxHashMap<String, Vec<Known>> {
    let mut out: FxHashMap<String, Vec<Known>> = FxHashMap::default();
    out.insert(
        "__ImageBase".to_owned(),
        vec![Known::Address(program.image_base)],
    );
    for f in &analysis.functions {
        let full = name_of(analysis, overlay, f.entry);
        out.entry(bare_name(&full).to_owned())
            .or_default()
            .push(Known::Code(f.entry));
    }
    for (at, class) in &analysis.classes.vtables {
        out.entry(format!("{class}::vftable"))
            .or_default()
            .push(Known::Address(*at));
    }
    for (at, n) in &analysis.crypto {
        out.entry(crate::crypto::identifier(n))
            .or_default()
            .push(Known::Address(*at));
    }
    for s in program.symbols.iter().filter(|s| s.addr != 0) {
        let n = crate::search::demangled_name(&s.name);
        if s.kind == SymbolKind::Import {
            for name in [bare_name(&n).to_owned(), format!("__imp_{}", bare_name(&n))] {
                out.entry(name).or_default().push(Known::Slot(s.addr));
            }
        } else {
            let code = program.section_at(s.addr).is_some_and(|sec| sec.executable);
            out.entry(crate::analysis::decompile::expr_render::data_name(&s.name))
                .or_default()
                .push(if code {
                    Known::Address(s.addr)
                } else {
                    Known::Data(s.addr)
                });
        }
    }
    out
}

/// Resolves the names the text uses that it does not declare, through the
/// table of [`names()`] built once per set of names in force.
///
/// The table reads the names alone, so it is keyed without the passes and
/// choice points ([`Overlay::names_key`]): the texts a repair search builds
/// under other passes and choices share it, where each of them built the
/// whole table again.
///
/// Where several things share a name (overloads of one C++ name), the one
/// the function refers to is meant, else the first. A name the text also
/// gives an instruction (`memcpy` for a `rep movs`) is the function or the
/// import only where the function refers to it; elsewhere it is the
/// instruction, and left out to run as the builtin.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
/// * `entry` - The function whose text it is.
/// * `wanted` - The names.
///
/// # Returns
///
/// Each name that is a function, a known table or a symbol, with what it
/// is; a name left out is a parameter by position or an intrinsic.
pub(super) fn resolve_names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    wanted: &std::collections::BTreeSet<&str>,
) -> FxHashMap<String, Known> {
    if wanted.is_empty() {
        return FxHashMap::default();
    }
    let table = analysis
        .derived
        .get_or_build_named("text_names", overlay.names_key(), (), || {
            names(program, analysis, overlay)
        });
    let referred = |k: &Known| {
        let (Known::Code(at) | Known::Address(at) | Known::Data(at) | Known::Slot(at)) = *k;
        analysis
            .xrefs_to(at)
            .iter()
            .any(|r| r.from_entry == Some(entry))
    };
    wanted
        .iter()
        .filter_map(|n| {
            let all = table.get(*n)?;
            let mine = all.iter().copied().find(|k| referred(k));
            let known = if INTRINSICS.contains(n) {
                mine?
            } else {
                mine.or_else(|| all.first().copied())?
            };
            Some(((*n).to_owned(), known))
        })
        .collect()
}

impl Running<'_, '_> {
    /// Returns the address of a data symbol the text names bare
    /// ([`Known::Data`]), `None` for any other expression.
    ///
    /// An index into one takes its address, as an array's name decays to
    /// ([`Running::data_cast`] for a cast of one).
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    pub(super) fn data_symbol(&self, e: &Ast) -> Option<u64> {
        let Ast::Name(n) = e else {
            return None;
        };
        match self.s.known.get(n) {
            Some(Known::Data(at)) if !self.s.vars.contains_key(n) => Some(*at),
            Some(Known::Data(_) | Known::Code(_) | Known::Address(_) | Known::Slot(_)) | None => {
                None
            }
        }
    }

    /// Reads a cast of a data symbol at the cast's width: `(uint8_t)flag`
    /// loads the byte, as C's conversion keeps it, so a flag at the end of
    /// its section reads the byte the binary does.
    ///
    /// # Arguments
    ///
    /// * `ty` - The integer type cast to.
    /// * `e` - The expression cast.
    ///
    /// # Returns
    ///
    /// The read, or `None` when `e` is no data symbol or `ty` is no integer
    /// at most a word wide.
    pub(super) fn data_cast(&mut self, ty: CTy, e: &Ast) -> Option<Eval<Val>> {
        let word = self.word();
        let narrow =
            ty.ptr == 0 && ty.float().is_none() && ty.bits(word).is_some_and(|b| b <= word);
        let at = self.data_symbol(e).filter(|_| narrow)?;
        Some(self.read(Place::Mem(at, ty)))
    }
}
