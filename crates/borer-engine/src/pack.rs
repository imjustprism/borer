//! Packs: what borer knows about a family of programs, kept out of its code.
//!
//! The engine's rules are generic: they read what a binary says about
//! itself (signature strings, registrations, tables, the code's own
//! arithmetic). What only one engine, framework or product does, and what a
//! user learned about one target, lives in a pack instead: a text file that
//! names a family's conventions (what its per-class static instance is
//! called, which templates are its serializer streams, which registrar
//! defines its attributes, which base classes play which role), so a Nebula
//! pack, a Qt pack or a pack for one product ships beside the engine and
//! anyone can write their own.
//!
//! The format is line-based, like the anchors manifest:
//!
//! ```text
//! # comments start with #
//! pack nebula 1
//! about Nebula Device 3 conventions
//!
//! [naming]
//! singleton Singleton
//!
//! [types]
//! stream Network::
//!
//! [roles]
//! class Game::Property property
//! prefix Commands:: command
//! ```
//!
//! A line is a key, a space and its value. Keys belong to the section above
//! them. A key the engine does not know is kept and reported as a warning,
//! so a pack written for a newer borer still loads. Several packs load
//! together: a list key gathers every pack's lines in load order, and a
//! single-valued key takes the last pack's value.
//!
//! A pack with a `[match]` section says which programs it is for: every
//! line there (`string`, `import`, `export`, `section`) must hold, and a
//! front end then loads the pack by itself for a program it fits (see
//! [`Pack::fit`]). A pack without one loads only when asked for.
//!
//! Every rule the engine runs works with no pack at all. A key's defaults
//! are general conventions (a stream class's name carries `Stream` or
//! `Writer`, a class deriving from a `...Widget` is a widget), and a pack
//! narrows or names them for its family. A list key either replaces its
//! defaults when a pack sets it, or adds to them (`list+` in
//! [`keys_tsv`]).

use std::fmt::Write as _;

use crate::program::{Program, SymbolKind};

/// A key the engine reads from packs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Key {
    /// The section it belongs to.
    pub section: &'static str,
    /// The key.
    pub key: &'static str,
    /// Whether every pack's lines add up (a list) or the last one wins.
    pub list: bool,
    /// Whether a list key's defaults still apply after a pack's lines
    /// (they add up) or only when no pack sets the key (a pack replaces
    /// them).
    pub extends: bool,
    /// What borer uses when no pack sets the key: at most one value for a
    /// single key, any number for a list.
    pub defaults: &'static [&'static str],
    /// What it means, for the key listing.
    pub meaning: &'static str,
}

/// Every key the engine reads, by section.
pub const KEYS: &[Key] = &[
    Key {
        section: "naming",
        key: "singleton",
        list: false,
        extends: false,
        defaults: &["instance"],
        meaning: "the name of the static holding a class's one instance (a thread-local slot the analysis ties to the class): Class::<name>",
    },
    Key {
        section: "naming",
        key: "class_id",
        list: false,
        extends: false,
        defaults: &["class_id"],
        meaning: "the name of the static a registered class's id accessor hands out: Class::<name>",
    },
    Key {
        section: "naming",
        key: "class_id_accessor",
        list: false,
        extends: false,
        defaults: &["get_class_id"],
        meaning: "the name given to a registered class's id accessor: Class::<name>",
    },
    Key {
        section: "naming",
        key: "class_info",
        list: false,
        extends: false,
        defaults: &["class_info"],
        meaning: "the name of a class's type descriptor, the object its registration names: Class::<name>",
    },
    Key {
        section: "naming",
        key: "class_info_accessor",
        list: false,
        extends: false,
        defaults: &["get_class_info"],
        meaning: "the name given to a function whose whole body hands out a class's descriptor: Class::<name>",
    },
    Key {
        section: "types",
        key: "stream",
        list: true,
        extends: false,
        defaults: &["Stream", "Writer", "Archive", "Serializer"],
        meaning: "text a serializer's stream class contains (a namespace such as `Net::`, or a word such as `BitStream`); a smart-pointer dereference of such a class opens the stream an encoder writes",
    },
    Key {
        section: "types",
        key: "wire",
        list: true,
        extends: false,
        defaults: &["Net", "Socket", "Packet", "BitStream", "Wire"],
        meaning: "text a stream's class contains when it is the network rather than a file; a class's wire reader outranks its file reader",
    },
    Key {
        section: "types",
        key: "kind",
        list: true,
        extends: true,
        defaults: &[
            "Guid guid",
            "Blob blob",
            "Atom atom",
            "String string",
            "Array< array",
        ],
        meaning: "`<word> <kind>`: a word a reader's helper text carries and the value kind it hints; the first word found wins, a pack's lines before the defaults",
    },
    Key {
        section: "attributes",
        key: "registrar",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "the qualified-name suffix of the function every typed attribute registrar calls (`AttrDefBase::Register`, say); the attribute catalog starts from its callers",
    },
    Key {
        section: "messages",
        key: "accept",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "the name of a helper a message port's declaring virtual calls with each message id it accepts; the port routes start from its callers",
    },
    Key {
        section: "roles",
        key: "class",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "`<base class> <role>`: classes deriving from the base play the role in the namespace map",
    },
    Key {
        section: "roles",
        key: "prefix",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "`<name prefix> <role>`: classes whose name starts with the prefix play the role in the namespace map",
    },
    Key {
        section: "roles",
        key: "word",
        list: true,
        extends: true,
        defaults: &[
            "Property property",
            "Component component",
            "Manager manager",
            "Widget widget",
            "Window window",
            "Message message",
            "Event event",
            "Command command",
            "Port port",
            "Handler handler",
            "Service service",
            "Controller controller",
            "Actor actor",
        ],
        meaning: "`<word> <role>`: a class whose own name or an ancestor's ends with the word, in any case, plays the role (the nearest wins), after the class and prefix lines",
    },
    Key {
        section: "names",
        key: "fn",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "`<signature> <name>`: the one function whose entry matches the signature (its first bytes in hex, `??` for any byte) takes the name; `export-pack` writes these",
    },
    Key {
        section: "names",
        key: "lib",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "`<signature> <symbol> [<offset>=<symbol>...]`: a library function as its object has it, the relocated bytes `??` and what each relocation names; a function whose bytes match and whose references agree takes the name; `sigmake` writes these from a library",
    },
    Key {
        section: "scripts",
        key: "run",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "a script file, relative to the pack's own file, that runs after the analysis; the names it proposes go on functions borer left unnamed or named by vtable slot",
    },
    Key {
        section: "match",
        key: "string",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "text the program's file holds, as ASCII or UTF-16; every `[match]` line must hold for the pack to load itself",
    },
    Key {
        section: "match",
        key: "import",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "`<module>` or `<module>!<function>`, in any case: the program imports it",
    },
    Key {
        section: "match",
        key: "export",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "a name the program exports",
    },
    Key {
        section: "match",
        key: "section",
        list: true,
        extends: false,
        defaults: &[],
        meaning: "the name of a section the program has",
    },
];

/// How a pack fits a program, by its `[match]` lines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fit {
    /// The pack has no `[match]` lines, so it loads only when asked for.
    Unconditional,
    /// Every `[match]` line holds: the pack is for this program.
    Holds,
    /// This line, as `key value`, does not hold.
    Fails(String),
}

/// One `key value` line of a pack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// The section the line sits in.
    pub section: String,
    /// The key.
    pub key: String,
    /// The rest of the line, trimmed.
    pub value: String,
    /// The line number, from 1.
    pub line: usize,
}

/// One pack as read.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Pack {
    /// The name its `pack` line gives.
    pub name: String,
    /// The version its `pack` line gives.
    pub version: String,
    /// What its `about` line says.
    pub about: String,
    /// Where it was read from, for messages.
    pub source: String,
    /// Its lines, in order.
    pub entries: Vec<Entry>,
    /// The scripts its `[scripts] run` lines name, as the file each came
    /// from and its text; a front end reads the files, since the engine
    /// opens none.
    pub scripts: Vec<(String, String)>,
}

impl Pack {
    /// Reads a pack's text.
    ///
    /// # Arguments
    ///
    /// * `text` - The file's contents.
    /// * `source` - Where it came from, for messages.
    ///
    /// # Returns
    ///
    /// The pack and the warnings about keys the engine does not read.
    ///
    /// # Errors
    ///
    /// When the text has no `pack <name> <version>` line before its first
    /// section, or a line outside every section.
    pub fn parse(text: &str, source: &str) -> Result<(Pack, Vec<String>), String> {
        let mut pack = Pack {
            source: source.to_owned(),
            ..Pack::default()
        };
        let mut warnings = Vec::new();
        let mut section: Option<String> = None;
        for (i, raw) in text.lines().enumerate() {
            let line = raw.trim();
            let n = i + 1;
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
                if pack.name.is_empty() {
                    return Err(format!(
                        "{source}:{n}: a section before the `pack <name> <version>` line"
                    ));
                }
                section = Some(name.trim().to_owned());
                continue;
            }
            let (key, value) = line
                .split_once(char::is_whitespace)
                .map_or((line, ""), |(k, v)| (k, v.trim()));
            let Some(current) = &section else {
                match key {
                    "pack" => {
                        let mut words = value.split_whitespace();
                        pack.name = words.next().unwrap_or("").to_owned();
                        pack.version = words.next().unwrap_or("").to_owned();
                        if pack.name.is_empty() {
                            return Err(format!("{source}:{n}: `pack` needs a name"));
                        }
                    }
                    "about" => value.clone_into(&mut pack.about),
                    _ => {
                        return Err(format!(
                            "{source}:{n}: `{key}` outside a section (only `pack` and `about` go above the first one)"
                        ));
                    }
                }
                continue;
            };
            if !KEYS.iter().any(|k| k.section == current && k.key == key) {
                warnings.push(format!(
                    "{source}:{n}: borer reads no `{key}` in [{current}]; kept"
                ));
            }
            pack.entries.push(Entry {
                section: current.clone(),
                key: key.to_owned(),
                value: value.to_owned(),
                line: n,
            });
        }
        if pack.name.is_empty() {
            return Err(format!("{source}: no `pack <name> <version>` line"));
        }
        Ok((pack, warnings))
    }

    /// How the pack fits a program: whether it has `[match]` lines and, if
    /// so, whether every one holds.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded program.
    #[must_use]
    pub fn fit(&self, program: &Program) -> Fit {
        let mut any = false;
        for e in self.entries.iter().filter(|e| e.section == "match") {
            any = true;
            let v = e.value.as_str();
            let holds = match e.key.as_str() {
                "string" => file_holds(&program.bytes, v),
                "import" => program.symbols.iter().any(|s| {
                    s.kind == SymbolKind::Import
                        && (s.name.eq_ignore_ascii_case(v)
                            || s.name
                                .split_once('!')
                                .is_some_and(|(module, _)| module.eq_ignore_ascii_case(v)))
                }),
                "export" => program.symbols.iter().any(|s| {
                    matches!(s.kind, SymbolKind::Export | SymbolKind::Forwarder) && s.name == v
                }),
                "section" => program.sections.iter().any(|s| s.name == v),
                _ => false,
            };
            if !holds {
                return Fit::Fails(format!("{} {v}", e.key));
            }
        }
        if any { Fit::Holds } else { Fit::Unconditional }
    }

    /// The script files the pack's `[scripts] run` lines name, relative to
    /// the pack's own file.
    #[must_use]
    pub fn script_files(&self) -> Vec<&str> {
        self.entries
            .iter()
            .filter(|e| e.section == "scripts" && e.key == "run")
            .map(|e| e.value.as_str())
            .collect()
    }

    /// The pack's `[match]` lines, as `key value`, for a report.
    #[must_use]
    pub fn match_lines(&self) -> Vec<String> {
        self.entries
            .iter()
            .filter(|e| e.section == "match")
            .map(|e| format!("{} {}", e.key, e.value))
            .collect()
    }
}

/// Tells whether a file holds a text as ASCII or as UTF-16LE.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `text` - The text.
fn file_holds(bytes: &[u8], text: &str) -> bool {
    let wide: Vec<u8> = text.encode_utf16().flat_map(u16::to_le_bytes).collect();
    !text.is_empty() && (holds(bytes, text.as_bytes()) || holds(bytes, &wide))
}

/// Tells whether `needle` occurs in `hay`.
///
/// # Arguments
///
/// * `hay` - Where to look.
/// * `needle` - What to find.
fn holds(hay: &[u8], needle: &[u8]) -> bool {
    let Some((&first, rest)) = needle.split_first() else {
        return false;
    };
    let mut at = 0;
    while let Some(i) = hay
        .get(at..)
        .and_then(|h| h.iter().position(|&b| b == first))
    {
        let start = at + i;
        if hay
            .get(start + 1..start + needle.len())
            .is_some_and(|w| w == rest)
        {
            return true;
        }
        at = start + 1;
    }
    false
}

/// The packs one analysis runs with, in load order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Packs {
    /// The packs, first loaded first.
    pub packs: Vec<Pack>,
}

impl Packs {
    /// Every value a list key has across the packs, in load order.
    ///
    /// # Arguments
    ///
    /// * `section` - The section.
    /// * `key` - The key.
    pub fn values<'a>(&'a self, section: &'a str, key: &'a str) -> impl Iterator<Item = &'a str> {
        self.packs
            .iter()
            .flat_map(|p| p.entries.iter())
            .filter(move |e| e.section == section && e.key == key)
            .map(|e| e.value.as_str())
    }

    /// A single-valued key's value: the last pack's, else the engine's
    /// default from [`KEYS`].
    ///
    /// # Arguments
    ///
    /// * `section` - The section.
    /// * `key` - The key.
    #[must_use]
    pub fn value<'a>(&'a self, section: &'a str, key: &'a str) -> Option<&'a str> {
        self.values(section, key)
            .last()
            .or_else(|| defaults(section, key).first().copied())
    }

    /// A list key's values as the engine reads them: every pack's lines in
    /// load order, then the key's defaults when it adds to them or no pack
    /// sets it.
    ///
    /// # Arguments
    ///
    /// * `section` - The section.
    /// * `key` - The key.
    #[must_use]
    pub fn list<'a>(&'a self, section: &'a str, key: &'a str) -> Vec<&'a str> {
        let mut out: Vec<&str> = self.values(section, key).collect();
        let extends = KEYS
            .iter()
            .any(|k| k.section == section && k.key == key && k.extends);
        if extends || out.is_empty() {
            out.extend(defaults(section, key).iter().copied());
        }
        out
    }

    /// [`Packs::list`]'s values split into their first word and the rest:
    /// `class Game::Property property` gives `("Game::Property",
    /// "property")`.
    ///
    /// # Arguments
    ///
    /// * `section` - The section.
    /// * `key` - The key.
    #[must_use]
    pub fn pairs<'a>(&'a self, section: &'a str, key: &'a str) -> Vec<(&'a str, &'a str)> {
        self.list(section, key)
            .into_iter()
            .filter_map(|v| {
                let (a, b) = v.split_once(char::is_whitespace)?;
                Some((a, b.trim()))
            })
            .collect()
    }

    /// A `[naming]` key's name: the last pack's, else the engine's default,
    /// else the key itself.
    ///
    /// # Arguments
    ///
    /// * `key` - The naming key (`singleton`, `class_id`, ...).
    #[must_use]
    pub fn name_for<'a>(&'a self, key: &'a str) -> &'a str {
        self.value("naming", key).unwrap_or(key)
    }

    /// The loaded packs as `name version` words, for headers.
    #[must_use]
    pub fn label(&self) -> String {
        let mut out = String::new();
        for p in &self.packs {
            if !out.is_empty() {
                out.push_str(", ");
            }
            out.push_str(&p.name);
            if !p.version.is_empty() {
                let _ = write!(out, " {}", p.version);
            }
        }
        out
    }
}

/// A key's defaults, or none when the engine reads no such key.
///
/// # Arguments
///
/// * `section` - The section.
/// * `key` - The key.
#[must_use]
pub fn defaults(section: &str, key: &str) -> &'static [&'static str] {
    KEYS.iter()
        .find(|k| k.section == section && k.key == key)
        .map_or(&[], |k| k.defaults)
}

/// Every key the engine reads, as a `#`-headed table: section, key, kind
/// (`single`, `list`, or `list+` for a list whose defaults still apply
/// after a pack's lines), defaults, meaning.
#[must_use]
pub fn keys_tsv() -> String {
    let mut out = format!(
        "# {} keys a pack can set; a list's defaults apply when no pack sets it, a list+'s always\n",
        KEYS.len()
    );
    out.push_str("section\tkey\tkind\tdefault\tmeaning\n");
    for k in KEYS {
        let kind = match (k.list, k.extends) {
            (false, _) => "single",
            (true, false) => "list",
            (true, true) => "list+",
        };
        let default = if k.defaults.is_empty() {
            "-".to_owned()
        } else {
            k.defaults.join(" | ")
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{kind}\t{default}\t{}",
            k.section, k.key, k.meaning
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A pack reads its header, sections and lines; an unknown key is kept
    /// and warned about; list keys gather across packs and a single key
    /// takes the last pack's value or the default.
    ///
    /// # Panics
    ///
    /// When a read value differs.
    #[test]
    fn packs_read_and_merge() {
        let text = "# a pack\npack one 2\nabout the first\n\n[naming]\nsingleton Only\n\n[roles]\nclass Base::Thing thing\nprefix Cmd:: command\nfuture later\n";
        let (one, warnings) = Pack::parse(text, "one.borer").expect("reads");
        assert_eq!((one.name.as_str(), one.version.as_str()), ("one", "2"));
        assert_eq!(one.about, "the first");
        assert_eq!(warnings.len(), 1, "{warnings:?}");
        assert!(warnings[0].contains("`future`"), "{warnings:?}");
        let (two, _) = Pack::parse(
            "pack two 1\n[roles]\nclass Other::Base other\n[naming]\nsingleton Last\n",
            "two.borer",
        )
        .expect("reads");
        let packs = Packs {
            packs: vec![one, two],
        };
        assert_eq!(packs.value("naming", "singleton"), Some("Last"));
        assert_eq!(packs.value("naming", "class_id"), Some("class_id"));
        let roles = packs.pairs("roles", "class");
        assert_eq!(
            roles,
            vec![("Base::Thing", "thing"), ("Other::Base", "other")]
        );
        assert_eq!(packs.list("types", "stream"), defaults("types", "stream"));
        let (three, _) = Pack::parse(
            "pack three 1\n[types]\nstream Net::\nkind Handle handle\n",
            "three.borer",
        )
        .expect("reads");
        let one_more = Packs { packs: vec![three] };
        assert_eq!(one_more.list("types", "stream"), vec!["Net::"]);
        let kinds = one_more.pairs("types", "kind");
        assert_eq!(kinds.first(), Some(&("Handle", "handle")));
        assert_eq!(kinds.len(), 1 + defaults("types", "kind").len());
        assert_eq!(packs.label(), "one 2, two 1");
        let program = Program::raw_x64(b"\x90\x90Some Engine v3\0\xc3");
        let (fits, _) =
            Pack::parse("pack e 1\n[match]\nstring Some Engine\n", "e.borer").expect("reads");
        assert_eq!(fits.fit(&program), Fit::Holds);
        assert_eq!(fits.match_lines(), vec!["string Some Engine"]);
        let (other, _) = Pack::parse(
            "pack o 1\n[match]\nstring Some Engine\nimport KERNEL32.dll\n",
            "o.borer",
        )
        .expect("reads");
        assert_eq!(
            other.fit(&program),
            Fit::Fails("import KERNEL32.dll".into())
        );
        assert_eq!(packs.packs[0].fit(&program), Fit::Unconditional);
        assert!(file_holds(b"a\0b\0c\0", "abc"));
        assert!(!file_holds(b"ab", "abc"));
        assert!(Pack::parse("[naming]\nsingleton x\n", "x").is_err());
        assert!(Pack::parse("singleton x\n", "x").is_err());
        assert!(Pack::parse("# nothing\n", "x").is_err());
    }
}
