//! The names and comments borer holds, written for another tool to apply:
//! an `IDAPython` script, a Ghidra script, a Binary Ninja script, or an
//! x64dbg database.
//!
//! The scripts take every address relative to the image base borer loaded
//! the file at, and add the base the tool loaded it at, so they apply to a
//! rebased database too; x64dbg keys its database by module and relative
//! address already.

use super::{Analysis, Overlay, name_of};
use crate::program::Program;
use std::fmt::Write as _;

/// The tools [`names_export`] writes for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tool {
    /// IDA Pro, through `IDAPython`.
    Ida,
    /// Ghidra, through its Python scripting (Jython or `PyGhidra`).
    Ghidra,
    /// Binary Ninja, through its Python API.
    BinaryNinja,
    /// x64dbg, as a `.dd64` or `.dd32` database to load.
    X64dbg,
}

impl Tool {
    /// The words [`Tool::parse`] reads.
    pub const NAMES: &'static str = "ida, ghidra, binja, x64dbg";

    /// Parses a tool's name.
    ///
    /// # Arguments
    ///
    /// * `word` - `ida`, `ghidra`, `binja` or `x64dbg`.
    #[must_use]
    pub fn parse(word: &str) -> Option<Self> {
        Some(match word.to_ascii_lowercase().as_str() {
            "ida" | "idapython" => Self::Ida,
            "ghidra" => Self::Ghidra,
            "binja" | "binaryninja" | "binary-ninja" => Self::BinaryNinja,
            "x64dbg" | "x32dbg" => Self::X64dbg,
            _ => return None,
        })
    }
}

/// A string as a double-quoted literal both Python and JSON read: `\`, `"`
/// and control characters escaped.
///
/// # Arguments
///
/// * `s` - The text.
fn quoted(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => {
                let _ = write!(out, "\\u{:04x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Every address borer names, with the name.
///
/// That is functions named by debug information, signatures, inference or
/// the user, and the globals the user named; `sub_` placeholders and names cut short for display (ending
/// `...`, which no tool should apply) left out.
///
/// # Arguments
///
/// * `a` - Discovery results.
/// * `o` - User names, which win.
fn named(a: &Analysis, o: &Overlay) -> Vec<(u64, String)> {
    let mut out: Vec<(u64, String)> = a
        .functions
        .iter()
        .map(|f| (f.entry, name_of(a, o, f.entry)))
        .filter(|(entry, n)| *n != format!("sub_{entry:x}") && !n.ends_with("..."))
        .collect();
    for (&va, n) in o.names.raw() {
        if a.function(va).is_none() {
            out.push((va, n.clone()));
        }
    }
    out.sort_unstable();
    out.dedup_by_key(|(va, _)| *va);
    out
}

/// Writes the names and comments borer holds for another tool to apply.
///
/// # Arguments
///
/// * `p` - The loaded image, for its base and file name.
/// * `a` - Discovery results.
/// * `o` - User names and comments.
/// * `tool` - The tool to write for.
///
/// # Returns
///
/// The script or database text.
#[must_use]
pub fn names_export(p: &Program, a: &Analysis, o: &Overlay, tool: Tool) -> String {
    let names = named(a, o);
    let comments: Vec<(u64, &String)> = o.comments.raw().iter().map(|(&va, c)| (va, c)).collect();
    let base = p.image_base;
    let file = p
        .path
        .file_name()
        .map_or_else(String::new, |f| f.to_string_lossy().into_owned());
    let head = format!(
        "borer: {} names and {} comments for {file}, loaded at {base:#x}",
        names.len(),
        comments.len()
    );
    let mut out = String::new();
    match tool {
        Tool::X64dbg => {
            let rva = |va: u64| format!("{:#x}", va.wrapping_sub(base));
            let module = quoted(&file);
            let rows = |items: &mut dyn Iterator<Item = (u64, &str)>| {
                items
                    .map(|(va, text)| {
                        format!(
                            "    {{\"module\": {module}, \"address\": \"{}\", \"manual\": true, \"text\": {}}}",
                            rva(va),
                            quoted(text)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(",\n")
            };
            let _ = write!(
                out,
                "{{\n  \"labels\": [\n{}\n  ],\n  \"comments\": [\n{}\n  ]\n}}\n",
                rows(&mut names.iter().map(|(va, n)| (*va, n.as_str()))),
                rows(&mut comments.iter().map(|(va, c)| (*va, c.as_str())))
            );
        }
        Tool::Ida | Tool::Ghidra | Tool::BinaryNinja => {
            let _ = writeln!(out, "# {head}");
            let prelude = match tool {
                Tool::Ida => {
                    "# File > Script file... with the database open.\nimport ida_name, idc\ndelta = idc.get_imagebase() - BASE\ndef n(ea, name):\n    ida_name.set_name(ea + delta, name, ida_name.SN_NOWARN | ida_name.SN_NOCHECK | ida_name.SN_FORCE)\ndef c(ea, text):\n    idc.set_cmt(ea + delta, text, 0)\n"
                }
                Tool::Ghidra => {
                    "# Run from the Script Manager with the program open.\n# @category borer\nfrom ghidra.program.model.symbol import SourceType\ndelta = currentProgram.getImageBase().getOffset() - BASE\ndef n(ea, name):\n    at = toAddr(ea + delta)\n    f = getFunctionAt(at)\n    if f is not None:\n        f.setName(name, SourceType.USER_DEFINED)\n    else:\n        createLabel(at, name, True, SourceType.USER_DEFINED)\ndef c(ea, text):\n    setEOLComment(toAddr(ea + delta), text)\n"
                }
                Tool::BinaryNinja | Tool::X64dbg => {
                    "# Run in the Python console (or as a snippet) with the view open.\nfrom binaryninja import Symbol, SymbolType\ndelta = bv.start - BASE\ndef n(ea, name):\n    at = ea + delta\n    kind = SymbolType.FunctionSymbol if bv.get_function_at(at) is not None else SymbolType.DataSymbol\n    bv.define_user_symbol(Symbol(kind, at, name))\ndef c(ea, text):\n    bv.set_comment_at(ea + delta, text)\n"
                }
            };
            let _ = writeln!(out, "BASE = {base:#x}");
            out.push_str(prelude);
            for (va, n) in &names {
                let _ = writeln!(out, "n({va:#x}, {})", quoted(n));
            }
            for (va, c) in &comments {
                let _ = writeln!(out, "c({va:#x}, {})", quoted(c));
            }
            let _ = writeln!(
                out,
                "print(\"borer: applied {} names and {} comments\")",
                names.len(),
                comments.len()
            );
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{Tool, quoted};

    /// Quotes, backslashes and control characters are escaped for Python
    /// and JSON alike.
    ///
    /// # Panics
    ///
    /// When the literal reads otherwise.
    #[test]
    fn names_are_quoted_for_python_and_json() {
        assert_eq!(quoted("a\"b\\c\nd\u{1}"), "\"a\\\"b\\\\c\\nd\\u0001\"");
    }

    /// Each tool parses by its usual names.
    ///
    /// # Panics
    ///
    /// When one does not.
    #[test]
    fn tools_parse_by_their_names() {
        assert_eq!(Tool::parse("IDA"), Some(Tool::Ida));
        assert_eq!(Tool::parse("binaryninja"), Some(Tool::BinaryNinja));
        assert_eq!(Tool::parse("x32dbg"), Some(Tool::X64dbg));
        assert_eq!(Tool::parse("radare"), None);
    }
}
