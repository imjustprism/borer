//! The header of a decompiled function as a run reads it: the layout
//! lines and the declarations before the first blank line.

use super::*;

/// Returns a text's lines with each definition the header holds (a
/// struct, a helper) blanked to a comment, and where the body starts: past
/// the first blank line, the end of the header.
///
/// # Arguments
///
/// * `text` - A decompiled function.
pub(super) fn lines(text: &str) -> (Vec<&str>, usize) {
    let all: Vec<&str> = text
        .lines()
        .map(|l| if defines(l) { "//" } else { l })
        .collect();
    let base = all
        .iter()
        .position(|l| l.trim().is_empty())
        .map_or(0, |i| i + 1);
    (all, base)
}

/// The pieces of a decompiled function's header the run needs beside its
/// signature.
#[derive(Debug, Default)]
pub(super) struct Header {
    /// Declared names: type, and the address a global's `// @` gives.
    pub(super) declared: Vec<(String, CTy, Option<u64>)>,
    /// The declared names that are arrays (`uint32_t local_28[8]`), whose
    /// name reads as the address of their first element.
    pub(super) arrays: FxHashSet<String>,
    /// Field widths by base and offset.
    pub(super) layouts: FxHashMap<String, FxHashMap<u64, CTy>>,
}

/// Reads the header of a decompiled function beside its signature: its
/// layout lines and its declarations, the lines before the first blank.
///
/// A storage word (`static`, `extern`, `inline`) is no type, an
/// initializer declares nothing, and a function defined in the header
/// (`static inline uint64_t op_add(...) { ... }`) is no variable. A table
/// of function pointers (`static uint32_t (*const g64_2000[2])(uint64_t)
/// = {...}`) declares its name as an array of `void *`. A global named by
/// its address (`g32_d68`) is at that address when no `// @` comment
/// places it.
///
/// # Arguments
///
/// * `lines` - The header's lines.
/// * `word` - The machine word in bits.
///
/// # Errors
///
/// When a declaration does not tokenize.
pub(super) fn header(lines: &[&str], word: u8) -> Result<Header, String> {
    let mut h = Header::default();
    let mut layout_base: Option<String> = None;
    for raw in lines {
        let t = raw.trim();
        let layout = t
            .strip_prefix("// layout ")
            .and_then(|l| l.split_once(':'))
            .map(|(base, rest)| (Some(base.trim().to_owned()), rest))
            .or_else(|| {
                t.strip_prefix("//  ")
                    .filter(|_| layout_base.is_some())
                    .map(|rest| (None, rest))
            });
        if let Some((base, rest)) = layout {
            if let Some(b) = base {
                layout_base = Some(b);
            }
            let Some(b) = layout_base.clone() else {
                continue;
            };
            for item in rest.split(',') {
                let mut words = item.split_whitespace();
                let (Some(off), Some(letter)) = (words.next(), words.next()) else {
                    continue;
                };
                let Some(off) = crate::analysis::parse_addr(off) else {
                    continue;
                };
                if let Some(ty) = layout_letter(letter) {
                    h.layouts.entry(b.clone()).or_default().insert(off, ty);
                }
            }
            continue;
        }
        layout_base = None;
        if t.starts_with("//") || t.is_empty() {
            continue;
        }
        let at = t
            .split_once("// @ ")
            .and_then(|(_, a)| crate::analysis::parse_addr(a.trim()));
        let toks = tokens(t)?;
        let storage = toks
            .iter()
            .take_while(|t| matches!(t, Tok::Name(n) if matches!(n.as_str(), "static" | "extern" | "inline")))
            .count();
        let init = toks.iter().position(|t| *t == Tok::Punct("="));
        if init.is_none() && toks.contains(&Tok::Punct("{")) {
            continue;
        }
        let toks = toks.get(storage..init.unwrap_or(toks.len())).unwrap_or(&[]);
        let Some((base, used)) = crate::analysis::decompile::ctext::leading_type(toks, word) else {
            continue;
        };
        for decl in split_top(toks.get(used..).unwrap_or(&[]), ",") {
            let code = matches!(decl, [Tok::Punct("("), Tok::Punct("*"), ..]);
            let lead = if code {
                let consts = decl.iter().skip(2);
                2 + consts
                    .take_while(|t| matches!(t, Tok::Name(c) if c == "const"))
                    .count()
            } else {
                decl.iter()
                    .take_while(|t| matches!(t, Tok::Punct("*")))
                    .count()
            };
            if let Some(Tok::Name(n)) = decl.get(lead) {
                let ty = if code {
                    CTy::of(Base::Void).to()
                } else {
                    (0..lead).fold(base, |t, _| t.to())
                };
                if matches!(decl.get(lead + 1), Some(Tok::Punct("["))) {
                    h.arrays.insert(n.clone());
                }
                let at = at.or_else(|| global_name(n).map(|(addr, _)| addr));
                h.declared.push((n.clone(), ty, at));
            }
        }
    }
    Ok(h)
}

/// Returns where a table the header declares lies, when its name is a
/// data symbol of the binary.
///
/// A declaration with no `// @` and no address in its name (`ops`) is
/// placed nowhere else. A stack local (`local_8`, a stated or a
/// debug-named one) stays on the stack whatever symbol shares its name.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions and symbols.
/// * `overlay` - User names.
/// * `entry` - The function, for the names its code refers to.
/// * `head` - The header read.
/// * `name` - A declared name.
///
/// # Returns
///
/// The symbol's address, `None` for a name that is no array or no data
/// symbol.
pub(super) fn placed(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    head: &Header,
    name: &str,
) -> Option<u64> {
    let wbytes = u64::from(program.arch.bitness().unwrap_or(64) / 8);
    let local = slot_offset(name, wbytes, frame_base(program))
        .or_else(|| stated_local(overlay, entry, name))
        .or_else(|| debug_local(program, entry, name));
    if !head.arrays.contains(name) || local.is_some() {
        return None;
    }
    let wanted = std::collections::BTreeSet::from([name]);
    match resolve_names(program, analysis, overlay, entry, &wanted).get(name)? {
        Known::Address(addr) => Some(*addr),
        Known::Code(_) | Known::Slot(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{Arch, Section, Symbol, SymbolKind};

    /// A declared array is placed at the data symbol of its name, except a
    /// stack local, which keeps its slot whatever symbol shares its name.
    ///
    /// # Panics
    ///
    /// When either is placed otherwise.
    #[test]
    fn a_stack_local_is_not_placed_at_a_symbol_of_its_name() {
        let mut p = Program::raw(
            vec![0xc3; 0x2000],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![
                Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
                Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
            ],
        );
        p.symbols = [("local_8", 0x2000), ("ops", 0x2008)]
            .iter()
            .map(|(name, addr)| Symbol {
                name: (*name).to_owned(),
                addr: *addr,
                kind: SymbolKind::Data,
            })
            .collect();
        let a = Analysis::compute(&p);
        let mut head = Header::default();
        head.arrays.insert("local_8".to_owned());
        head.arrays.insert("ops".to_owned());
        let o = Overlay::default();
        assert_eq!(placed(&p, &a, &o, 0x1000, &head, "local_8"), None);
        assert_eq!(placed(&p, &a, &o, 0x1000, &head, "ops"), Some(0x2008));
    }
}
