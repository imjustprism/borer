//! borer's code names no one family's classes or namespaces.
//!
//! borer's rules are general: what one engine or product does lives in a
//! pack (`packs/nebula.borer`), not in borer's code. This test reads the
//! engine's and the CLI's sources and fails on a string literal, outside
//! comments and test modules, that spells a known family's class or
//! namespace, so a convention that slips back in is caught by the gate.

use std::fs;
use std::path::{Path, PathBuf};

/// Spellings that belong to one family (Nebula3)
/// and so to its pack, never to engine code.
const FAMILY: &[&str] = &[
    "Game::",
    "Messaging::",
    "Commands::",
    "Properties::",
    "Core::Ptr",
    "Core::Rtti",
    "Network::",
    "Base::NetStream",
    "AttributeDefinitionBase",
    "UI::Widget",
    "StringAtom",
    "NEBULA",
];

/// Collects every `.rs` file under a directory.
///
/// # Arguments
///
/// * `dir` - The directory.
/// * `out` - The files found so far.
fn sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// The string literals on one line of code, up to a `//` comment.
///
/// # Arguments
///
/// * `line` - The line.
fn literals(line: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut current: Option<String> = None;
    let mut chars = line.chars().peekable();
    while let Some(c) = chars.next() {
        match (&mut current, c) {
            (Some(s), '\\') => {
                s.push(c);
                if let Some(next) = chars.next() {
                    s.push(next);
                }
            }
            (Some(s), '"') => {
                out.push(std::mem::take(s));
                current = None;
            }
            (Some(s), _) => s.push(c),
            (None, '"') => current = Some(String::new()),
            (None, '/') if chars.peek() == Some(&'/') => break,
            (None, '\'') => {
                let rest: String = chars.clone().take(2).collect();
                if rest == "\"'" {
                    chars.next();
                    chars.next();
                }
            }
            (None, _) => {}
        }
    }
    out
}

/// Tells whether the item after a `#[cfg(test)]` is a module: the first
/// line past its other attributes starts with `mod `.
///
/// # Arguments
///
/// * `after` - The lines after the `#[cfg(test)]`.
fn opens_test_module(after: &[&str]) -> bool {
    after
        .iter()
        .find(|l| !(l.starts_with("#[") || l.starts_with(' ') || l.starts_with(')')))
        .is_some_and(|l| l.starts_with("mod "))
}

/// No engine source spells a family's class or namespace in code.
///
/// # Panics
///
/// When one does, listing each file, line and spelling.
#[test]
fn engine_code_names_no_family() {
    let engine = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    sources(&engine.join("src"), &mut files);
    sources(&engine.join("../borer/src"), &mut files);
    assert!(files.len() > 20, "found only {} sources", files.len());
    let mut hits = Vec::new();
    for file in files {
        let text = fs::read_to_string(&file).unwrap_or_default();
        let lines: Vec<&str> = text.lines().collect();
        for (n, line) in lines.iter().enumerate() {
            if line.starts_with("#[cfg(test)]") && opens_test_module(&lines[n + 1..]) {
                break;
            }
            let code = line.trim_start();
            if code.starts_with("//") {
                continue;
            }
            for lit in literals(code) {
                if let Some(term) = FAMILY.iter().find(|t| lit.contains(**t)) {
                    hits.push(format!("{}:{}: {term} in \"{lit}\"", file.display(), n + 1));
                }
            }
        }
    }
    assert!(
        hits.is_empty(),
        "a family's convention in engine code; it belongs in a pack:\n{}",
        hits.join("\n")
    );
}

/// The literal reader finds strings, skips comments and a quote character.
///
/// # Panics
///
/// When a literal is misread.
#[test]
fn literals_are_read_from_code_only() {
    assert_eq!(literals(r#"let a = "x::y"; // "Game::""#), vec!["x::y"]);
    assert_eq!(literals(r#"f('"', "a\"b")"#), vec![r#"a\"b"#]);
    assert!(literals("let x = 1;").is_empty());
}
