//! Well-formedness of pseudo-C: the labels a `goto` names must exist.

use std::collections::BTreeSet;

/// Returns the text with every string literal's content removed.
///
/// A literal may hold `goto L_` or braces: borer's own cleanup code is data
/// inside `borer.exe`.
///
/// # Arguments
///
/// * `text` - Pseudo-C text.
pub(crate) fn without_strings(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut in_str = false;
    let mut escaped = false;
    for c in text.chars() {
        if in_str {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
                out.push('"');
            }
            continue;
        }
        if c == '"' {
            in_str = true;
        }
        out.push(c);
    }
    out
}

/// Lists the labels referenced by a goto but never defined in the text.
///
/// # Arguments
///
/// * `text` - Pseudo-C text.
///
/// # Returns
///
/// The missing labels in first-reference order, without duplicates.
pub(crate) fn dangling_gotos(text: &str) -> Vec<String> {
    let text = without_strings(text);
    let mut labels: BTreeSet<&str> = BTreeSet::new();
    for l in text.lines() {
        let t = l.trim();
        if let Some(name) = t.strip_suffix(':')
            && name.starts_with("L_")
        {
            labels.insert(name);
        }
    }
    let mut missing = Vec::new();
    for l in text.lines() {
        let mut rest = l;
        while let Some(pos) = rest.find("goto L_") {
            let after = &rest[pos + 5..];
            let end = after.find(';').unwrap_or(after.len());
            let name = &after[..end];
            if !labels.contains(name) && !missing.iter().any(|m| m == name) {
                missing.push(name.to_owned());
            }
            rest = &after[end..];
        }
    }
    missing
}
