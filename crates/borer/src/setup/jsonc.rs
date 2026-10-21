//! Editing a JSON or JSONC configuration's servers in its text, so
//! comments, trailing commas and key order stay byte for byte, and writing
//! an entry in the one-line form those files use.

use std::io;

use serde::Serialize;

use super::{Change, NAME};

/// Writes JSON on one line with a space after each `:` and `,`, as a
/// person would write an entry: `{"command": "/b", "args": []}`.
struct Inline;

impl serde_json::ser::Formatter for Inline {
    fn begin_object_key<W: ?Sized + io::Write>(
        &mut self,
        w: &mut W,
        first: bool,
    ) -> io::Result<()> {
        if first { Ok(()) } else { w.write_all(b", ") }
    }

    fn begin_object_value<W: ?Sized + io::Write>(&mut self, w: &mut W) -> io::Result<()> {
        w.write_all(b": ")
    }

    fn begin_array_value<W: ?Sized + io::Write>(
        &mut self,
        w: &mut W,
        first: bool,
    ) -> io::Result<()> {
        if first { Ok(()) } else { w.write_all(b", ") }
    }
}

/// An entry as one line of JSON, its fields in the order its type
/// declares them.
///
/// # Arguments
///
/// * `value` - The entry.
pub(super) fn inline<T: Serialize>(value: &T) -> String {
    let mut out = Vec::new();
    let mut ser = serde_json::Serializer::with_formatter(&mut out, Inline);
    let _ = value.serialize(&mut ser);
    String::from_utf8(out).unwrap_or_default()
}

/// Blanks what a JSON file may hold that strict JSON does not.
///
/// That is `//` and `/* */` comments and trailing commas (JSONC, as VS
/// Code and Zed read it) and a leading byte order mark. Each blanked byte
/// becomes a space, newlines excepted, so a position in the result is the
/// same position in the text.
///
/// # Arguments
///
/// * `text` - The file's text.
///
/// # Returns
///
/// The text as strict JSON, if the rest of it is.
pub(super) fn plain_json(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = bytes.to_vec();
    if let Some(bom) = out.get_mut(..3).filter(|b| *b == b"\xef\xbb\xbf") {
        bom.fill(b' ');
    }
    let mut blank = |from: usize, to: usize| {
        for b in out.iter_mut().take(to).skip(from) {
            if *b != b'\n' {
                *b = b' ';
            }
        }
    };
    let mut i = 0;
    let mut in_string = false;
    while let Some(&c) = bytes.get(i) {
        let next = bytes.get(i + 1).copied();
        if in_string {
            match c {
                b'\\' => i += 1,
                b'"' => in_string = false,
                _ => {}
            }
            i += 1;
        } else if c == b'"' {
            in_string = true;
            i += 1;
        } else if c == b'/' && next == Some(b'/') {
            let end = text[i..].find('\n').map_or(bytes.len(), |n| i + n);
            blank(i, end);
            i = end;
        } else if c == b'/' && next == Some(b'*') {
            let end = text[i + 2..]
                .find("*/")
                .map_or(bytes.len(), |n| i + 2 + n + 2);
            blank(i, end);
            i = end;
        } else {
            i += 1;
        }
    }
    let mut in_string = false;
    let mut i = 0;
    while let Some(&c) = out.get(i) {
        if in_string {
            match c {
                b'\\' => i += 1,
                b'"' => in_string = false,
                _ => {}
            }
        } else if c == b'"' {
            in_string = true;
        } else if c == b','
            && out
                .get(i + 1..)
                .and_then(|rest| rest.iter().find(|b| !b.is_ascii_whitespace()))
                .is_some_and(|b| matches!(b, b'}' | b']'))
            && let Some(comma) = out.get_mut(i)
        {
            *comma = b' ';
        }
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// Finds where the object a top-level member holds opens.
///
/// # Arguments
///
/// * `plain` - The file's text with comments and trailing commas blanked, already checked to
///   parse as a JSON object.
/// * `key` - The member's name, which holds no escapes.
///
/// # Returns
///
/// The position of the member's `{`, the last when the key repeats (as a
/// parser reads it), or `None` when no such member holds an object.
fn member_open(plain: &str, key: &str) -> Option<usize> {
    let bytes = plain.as_bytes();
    let after_space = |from: usize| {
        (from..bytes.len()).find(|&j| bytes.get(j).is_some_and(|b| !b.is_ascii_whitespace()))
    };
    let mut depth = 0usize;
    let mut found = None;
    let mut i = 0;
    while let Some(&c) = bytes.get(i) {
        match c {
            b'"' => {
                let start = i + 1;
                let mut j = start;
                while let Some(&s) = bytes.get(j) {
                    match s {
                        b'\\' => j += 2,
                        b'"' => break,
                        _ => j += 1,
                    }
                }
                if depth == 1
                    && plain.get(start..j) == Some(key)
                    && let Some(colon) = after_space(j + 1).filter(|&k| bytes.get(k) == Some(&b':'))
                    && let Some(open) =
                        after_space(colon + 1).filter(|&k| bytes.get(k) == Some(&b'{'))
                {
                    found = Some(open);
                }
                i = j + 1;
            }
            b'{' | b'[' => {
                depth += 1;
                i += 1;
            }
            b'}' | b']' => {
                depth = depth.saturating_sub(1);
                i += 1;
            }
            _ => i += 1,
        }
    }
    found
}

/// The leading whitespace of the line a position is on.
///
/// # Arguments
///
/// * `text` - The text.
/// * `at` - The position.
fn indent_at(text: &str, at: usize) -> &str {
    let line = text[..at].rfind('\n').map_or(0, |n| n + 1);
    let rest = &text[line..];
    &rest[..rest.len() - rest.trim_start_matches([' ', '\t']).len()]
}

/// Finds a member of a JSON object by name.
///
/// # Arguments
///
/// * `plain` - The text as strict JSON ([`plain_json`]).
/// * `open` - The position of the object's `{`.
/// * `name` - The member's key.
///
/// # Returns
///
/// Where the member's key opens and where its value ends, or `None` when
/// the object has no such member.
fn member_span(plain: &str, open: usize, name: &str) -> Option<(usize, usize)> {
    let bytes = plain.as_bytes();
    let string_end = |from: usize| {
        let mut j = from + 1;
        while let Some(&c) = bytes.get(j) {
            match c {
                b'\\' => j += 2,
                b'"' => return Some(j),
                _ => j += 1,
            }
        }
        None
    };
    let mut depth = 0usize;
    let mut key: Option<(usize, bool)> = None;
    let mut i = open + 1;
    while let Some(&c) = bytes.get(i) {
        match c {
            b'"' => {
                let end = string_end(i)?;
                if depth == 0 && key.is_none() {
                    key = Some((i, plain.get(i + 1..end) == Some(name)));
                }
                i = end + 1;
            }
            b'{' | b'[' => {
                depth += 1;
                i += 1;
            }
            b'}' | b']' if depth > 0 => {
                depth -= 1;
                i += 1;
            }
            b',' | b'}' | b']' if depth == 0 => {
                if let Some((at, true)) = key {
                    return Some((at, plain[..i].trim_end().len()));
                }
                if c != b',' {
                    return None;
                }
                key = None;
                i += 1;
            }
            _ => i += 1,
        }
    }
    None
}

/// Takes the server entry out of a JSON configuration's text.
///
/// The member goes with the comma that joined it to its neighbour;
/// nothing else in the text changes.
///
/// # Arguments
///
/// * `text` - The file's text, possibly with comments.
/// * `key` - The top-level key holding the servers.
///
/// # Returns
///
/// The text without the entry.
///
/// # Errors
///
/// When the text has no servers object naming `borer`, or the text left
/// is not JSON.
pub(super) fn remove_json(text: &str, key: &str) -> Result<String, String> {
    let plain = plain_json(text);
    let open = member_open(&plain, key).ok_or_else(|| format!("it has no {key} object"))?;
    let (start, end) =
        member_span(&plain, open, NAME).ok_or_else(|| format!("its {key} names no {NAME}"))?;
    let next = end + plain[end..].len() - plain[end..].trim_start().len();
    let before = plain[..start].trim_end().len();
    let (from, to) = if plain.as_bytes().get(next) == Some(&b',') {
        let after = next + 1;
        (
            start,
            after + plain[after..].len() - plain[after..].trim_start().len(),
        )
    } else if before > 0 && plain.as_bytes().get(before - 1) == Some(&b',') {
        (before - 1, end)
    } else {
        (open + 1, end)
    };
    let out = format!("{}{}", &text[..from], &text[to..]);
    let gone = serde_json::from_str::<serde_json::Value>(&plain_json(&out))
        .ok()
        .is_some_and(|v| v.get(key).is_some_and(|s| s.get(NAME).is_none()));
    if gone {
        Ok(out)
    } else {
        Err(format!("taking {NAME} out of {key} did not give JSON"))
    }
}

/// Adds a server entry to a JSON configuration's text.
///
/// The entry is inserted as the first member of the servers object, which
/// is made as the first member of the file when it is missing; nothing
/// else in the text changes. An empty text becomes a new file.
///
/// # Arguments
///
/// * `text` - The file's text, possibly with comments.
/// * `key` - The top-level key holding the servers.
/// * `entry` - The entry's value, as JSON.
///
/// # Returns
///
/// The new text, or that a server named `borer` is already there.
///
/// # Errors
///
/// When the text is not a JSON object once comments and trailing commas
/// are blanked, or its servers member is not an object; the message says
/// which.
pub(super) fn add_json(text: &str, key: &str, entry: &str) -> Result<Change, String> {
    let nl = if text.contains("\r\n") { "\r\n" } else { "\n" };
    let member = format!("\"{NAME}\": {entry}");
    if text.trim().is_empty() {
        return Ok(Change::Text(format!(
            "{{{nl}  \"{key}\": {{{nl}    {member}{nl}  }}{nl}}}{nl}"
        )));
    }
    let plain = plain_json(text);
    let root: serde_json::Value =
        serde_json::from_str(&plain).map_err(|e| format!("it is not plain JSON ({e})"))?;
    let root = root
        .as_object()
        .ok_or_else(|| "its top level is not an object".to_owned())?;
    let unit = text
        .lines()
        .find_map(|l| {
            let rest = l.trim_start_matches([' ', '\t']);
            (rest.starts_with('"') && rest.len() < l.len()).then(|| &l[..l.len() - rest.len()])
        })
        .unwrap_or("  ");
    let is_empty_after = |open: usize| plain[open + 1..].trim_start().starts_with('}');
    let (at, insert) = match root.get(key) {
        Some(serde_json::Value::Object(servers)) => {
            if let Some(present) = servers.get(NAME) {
                let command = present
                    .get("command")
                    .and_then(|c| c.as_str().or_else(|| c.as_array()?.first()?.as_str()));
                return Ok(Change::Present(command.map(str::to_owned)));
            }
            let open = member_open(&plain, key)
                .ok_or_else(|| format!("cannot find where its {key} object opens"))?;
            let outer = indent_at(text, open);
            let tail = if is_empty_after(open) {
                format!("{nl}{outer}")
            } else {
                ",".to_owned()
            };
            (open, format!("{nl}{outer}{unit}{member}{tail}"))
        }
        Some(_) => return Err(format!("its {key} member is not an object")),
        None => {
            let open = plain.len() - plain.trim_start().len();
            let outer = indent_at(text, open);
            let tail = if is_empty_after(open) {
                format!("{nl}{outer}")
            } else {
                ",".to_owned()
            };
            (
                open,
                format!(
                    "{nl}{outer}{unit}\"{key}\": {{{nl}{outer}{unit}{unit}{member}{nl}{outer}{unit}}}{tail}"
                ),
            )
        }
    };
    let mut out = String::with_capacity(text.len() + insert.len());
    out.push_str(&text[..=at]);
    out.push_str(&insert);
    out.push_str(&text[at + 1..]);
    let added = serde_json::from_str::<serde_json::Value>(&plain_json(&out))
        .ok()
        .is_some_and(|v| v.get(key).and_then(|s| s.get(NAME)).is_some());
    if !added {
        return Err(format!("adding the entry under {key} did not give JSON"));
    }
    Ok(Change::Text(out))
}

#[cfg(test)]
mod tests {
    use super::super::{Change, changed_text};
    use super::{add_json, inline, plain_json, remove_json};

    /// The entry the tests add.
    const ENTRY: &str = r#"{"command": "/opt/borer", "args": []}"#;

    /// An entry is written on one line, fields in declared order.
    ///
    /// # Panics
    ///
    /// When the line differs.
    #[test]
    fn an_entry_is_one_line_in_declared_order() {
        #[derive(serde::Serialize)]
        struct E<'a> {
            z: &'a str,
            a: [u8; 2],
            m: [&'a str; 0],
        }
        assert_eq!(
            inline(&E {
                z: "x\\y",
                a: [1, 2],
                m: []
            }),
            r#"{"z": "x\\y", "a": [1, 2], "m": []}"#
        );
    }

    /// An entry goes into an existing servers object as its first member,
    /// every other byte of the file (comments, other servers, other keys,
    /// their order) stays, and a second add finds it present.
    ///
    /// # Panics
    ///
    /// When a byte of the old file is lost, the result does not parse, or
    /// the second add adds again.
    #[test]
    fn an_entry_joins_the_servers_and_keeps_everything_else() {
        let old = "{\n  // keep me\n  \"zeta\": 1,\n  \"mcpServers\": {\n    \"other\": {\"command\": \"node\"}\n  },\n  \"alpha\": [1, 2] /* and me */\n}\n";
        let new = changed_text(add_json(old, "mcpServers", ENTRY));
        assert_eq!(
            new,
            "{\n  // keep me\n  \"zeta\": 1,\n  \"mcpServers\": {\n    \"borer\": {\"command\": \"/opt/borer\", \"args\": []},\n    \"other\": {\"command\": \"node\"}\n  },\n  \"alpha\": [1, 2] /* and me */\n}\n"
        );
        let parsed: serde_json::Value =
            serde_json::from_str(&plain_json(&new)).expect("the result parses");
        assert_eq!(parsed["mcpServers"]["other"]["command"], "node");
        assert_eq!(parsed["zeta"], 1);
        assert_eq!(
            add_json(&new, "mcpServers", ENTRY),
            Ok(Change::Present(Some("/opt/borer".to_owned())))
        );
    }

    /// A missing servers key is made, an empty object filled, and an empty
    /// file written whole; a `/` inside a string is not a comment.
    ///
    /// # Panics
    ///
    /// When a result differs or does not parse.
    #[test]
    fn a_missing_key_an_empty_object_and_an_empty_file_take_the_entry() {
        let made = changed_text(add_json("{\"url\": \"http://x//y\"}", "servers", ENTRY));
        assert_eq!(
            made,
            "{\n  \"servers\": {\n    \"borer\": {\"command\": \"/opt/borer\", \"args\": []}\n  },\"url\": \"http://x//y\"}"
        );
        let filled = changed_text(add_json(
            "{\r\n  \"context_servers\": {}\r\n}\r\n",
            "context_servers",
            ENTRY,
        ));
        assert_eq!(
            filled,
            "{\r\n  \"context_servers\": {\r\n    \"borer\": {\"command\": \"/opt/borer\", \"args\": []}\r\n  }\r\n}\r\n"
        );
        let fresh = changed_text(add_json("", "mcpServers", ENTRY));
        let parsed: serde_json::Value = serde_json::from_str(&fresh).expect("parses");
        assert_eq!(parsed["mcpServers"]["borer"]["command"], "/opt/borer");
        let empty_root = changed_text(add_json("{}", "mcpServers", ENTRY));
        assert!(
            serde_json::from_str::<serde_json::Value>(&empty_root).is_ok(),
            "{empty_root}"
        );
    }

    /// A file that is not a JSON object, has a servers member that is not
    /// an object, or does not parse even as JSONC is refused with the
    /// reason.
    ///
    /// # Panics
    ///
    /// When one is edited, or the reason is missing.
    #[test]
    fn what_is_not_a_json_object_is_refused() {
        let refused = |t: &str| add_json(t, "mcpServers", ENTRY).expect_err("refused");
        assert!(refused("[1]").contains("top level is not an object"));
        assert!(refused("{\"mcpServers\": []}").contains("mcpServers member is not an object"));
        assert!(refused("{a: 1}").contains("not plain JSON"));
    }

    /// Trailing commas, as Zed's settings carry them, are read past and
    /// kept; a comma inside a string is not one.
    ///
    /// # Panics
    ///
    /// When the entry is not added, or a byte of the old file is lost.
    #[test]
    fn trailing_commas_are_read_past_and_kept() {
        let old = "{\n  \"theme\": \"One, Dark\",\n  \"context_servers\": {\n    \"x\": {\"command\": \"y\",},\n  },\n  \"tabs\": [1, 2,],\n}\n";
        let new = changed_text(add_json(old, "context_servers", ENTRY));
        assert_eq!(
            new,
            "{\n  \"theme\": \"One, Dark\",\n  \"context_servers\": {\n    \"borer\": {\"command\": \"/opt/borer\", \"args\": []},\n    \"x\": {\"command\": \"y\",},\n  },\n  \"tabs\": [1, 2,],\n}\n"
        );
        let parsed: serde_json::Value = serde_json::from_str(&plain_json(&new)).expect("parses");
        assert_eq!(parsed["theme"], "One, Dark");
    }

    /// The entry comes out of a servers object with the comma that joined
    /// it, wherever it sits, and every other byte stays; a file naming no
    /// `borer` is refused.
    ///
    /// # Panics
    ///
    /// When a removal leaves a byte it should not, or takes one it should
    /// keep.
    #[test]
    fn an_entry_comes_out_with_its_comma_and_nothing_else() {
        let first = "{\n  \"mcpServers\": {\n    \"borer\": {\"command\": \"/b\"},\n    \"other\": {}\n  }\n}\n";
        assert_eq!(
            remove_json(first, "mcpServers").expect("removed"),
            "{\n  \"mcpServers\": {\n    \"other\": {}\n  }\n}\n"
        );
        let last =
            "{\"mcpServers\": {\"other\": {}, // keep\n \"borer\": {\"args\": [1, {}]}}, \"x\": 1}";
        assert_eq!(
            remove_json(last, "mcpServers").expect("removed"),
            "{\"mcpServers\": {\"other\": {}}, \"x\": 1}"
        );
        let only = "{\"servers\": {\"borer\": {\"type\": \"stdio\"}}}";
        assert_eq!(
            remove_json(only, "servers").expect("removed"),
            "{\"servers\": {}}"
        );
        assert!(remove_json("{\"mcpServers\": {\"other\": {}}}", "mcpServers").is_err());
        let added = add_json(first, "mcpServers", "{}").map(|c| matches!(c, Change::Present(_)));
        assert_eq!(added, Ok(true));
    }
}
