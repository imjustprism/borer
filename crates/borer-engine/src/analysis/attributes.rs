//! Attributes: the typed attribute definitions a program registers at
//! start-up (Nebula3's `AttributeDefinitionBase`, say), with their codes,
//! types, defaults and the code using them.
//!
//! An entity's state is a set of attributes (`HitPoints`, `PlayTimeStart`,
//! `Transform`), each a global definition built once by a typed registrar:
//! a small function per attribute builds the name into a string, puts the
//! four-character code in a local, and hands both with the global, the
//! access mode and the default to the registrar for its type, which calls
//! `AttributeDefinitionBase::Register`. Each registrar stores a constant
//! type code at one offset of the definition, and the table accessors
//! guard that same offset against named types
//! (`GetColumnValueType(colIndex) == Matrix44Type`), which names the codes.
//! This module reads all of it back into one table. The function every
//! registrar calls is the framework's own, so a pack names it
//! (`[attributes] registrar`); with none named the catalog is empty.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::classes::{code_or_hex, four_chars};
use super::naming::in_data;
use super::render::Legend;
use super::schema::{ident_char, split_args};
use super::{Analysis, Overlay, RefKind, name_of, plain_text_cached};
use crate::program::Program;
use crate::strings::cstr_at;

/// Fewest registration sites worth a worker each.
const PAR_MIN: usize = 64;
/// Most users named on one row of the full table.
const USERS_MAX: usize = 4;
/// Most users listed under the row when the filter picks one attribute.
const USERS_ONE_MAX: usize = 200;
/// Rows one answer lists at most; a filter narrows a catalog beyond it.
const PAGE: usize = 200;
/// Longest default printed as the text passed; a longer one is `-`.
const DEFAULT_MAX: usize = 24;
/// Lines searched back from a type assert for the guard naming the code.
const GUARD_BACK: usize = 3;
/// Shortest and longest assert text read for a type name.
const ASSERT_LEN: (usize, usize) = (8, 256);

/// One registered attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttrDef {
    /// The four-character code.
    pub code: u32,
    /// The attribute's name.
    pub name: String,
    /// The type code its registrar stores, when one does.
    pub type_code: Option<u64>,
    /// Whether the registrar copies a whole value in at the type offset
    /// instead, so the attribute takes the type of its default.
    pub variant: bool,
    /// The access mode passed: `ro`, `rw`, or the value.
    pub access: String,
    /// The default passed, as text, or `-`.
    pub default: String,
    /// The definition global.
    pub definition: u64,
    /// The function registering it.
    pub site: u64,
    /// The registrar it went through.
    pub registrar: u64,
    /// Functions referencing the definition other than its registration
    /// and the exit-time destructor the registration hands over.
    pub users: Vec<u64>,
}

/// Every attribute with the type names the binary's asserts give the codes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AttrCatalog {
    /// The attributes, by name.
    pub attrs: Vec<AttrDef>,
    /// The registrars found.
    pub registrars: usize,
    /// Type code to name (`8` to `String`).
    pub type_names: BTreeMap<u64, String>,
}

/// The arguments of the first call to `callee` on `line`, read balanced.
///
/// # Arguments
///
/// * `line` - The line.
/// * `callee` - The callee's name as the text spells it.
pub(crate) fn call_args(line: &str, callee: &str) -> Option<Vec<String>> {
    let needle = format!("{callee}(");
    let mut from = 0;
    while let Some(at) = line[from..].find(&needle).map(|p| p + from) {
        let bounded = line[..at]
            .chars()
            .next_back()
            .is_none_or(|c| !ident_char(c));
        from = at + needle.len();
        if !bounded {
            continue;
        }
        let open = at + callee.len();
        let mut depth = 0i32;
        for (k, b) in line.bytes().enumerate().skip(open) {
            match b {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(split_args(&line[open + 1..k]));
                    }
                }
                _ => {}
            }
        }
        return None;
    }
    None
}

/// A constant as the text spells it: decimal, or hex after `0x`; an
/// identifier that happens to be hex digits (`a4`) is not one.
///
/// # Arguments
///
/// * `text` - The text.
fn constant(text: &str) -> Option<u64> {
    let t = text.trim();
    match t.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None if !t.is_empty() && t.bytes().all(|b| b.is_ascii_digit()) => t.parse().ok(),
        None => None,
    }
}

/// The address a global's text names: `&g64_1413bc1c0` is `0x1413bc1c0`.
///
/// # Arguments
///
/// * `arg` - The argument.
pub(crate) fn global_addr(arg: &str) -> Option<u64> {
    let name = arg.trim().trim_start_matches('&');
    let (width, hex) = name.strip_prefix('g')?.split_once('_')?;
    if width.is_empty() || !width.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    u64::from_str_radix(hex, 16).ok()
}

/// The string literal a call built into `local`: `S(&local_48, "Name")`.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `local` - The local, without its `&`.
fn literal_into(lines: &[&str], local: &str) -> Option<String> {
    let taken = format!("(&{local}, \"");
    lines.iter().find_map(|line| {
        let at = line.find(&taken)?;
        let rest = &line[at + taken.len()..];
        let end = rest.find("\")")?;
        Some(rest[..end].to_owned())
    })
}

/// The value assigned to `var` by the last plain assignment before `at`.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `at` - Index to search back from.
/// * `var` - The variable.
pub(crate) fn assigned_before<'l>(lines: &[&'l str], at: usize, var: &str) -> Option<&'l str> {
    let head = format!("{var} = ");
    lines[..at].iter().rev().find_map(|line| {
        let pos = line.find(&head)?;
        let before = line[..pos].trim();
        if !(before.is_empty() || before.ends_with('=')) {
            return None;
        }
        if pos > 0 && line[..pos].chars().next_back().is_some_and(ident_char) {
            return None;
        }
        let mut value = line[pos + head.len()..].trim().trim_end_matches(';');
        while let Some((target, rest)) = value.split_once(" = ")
            && !target.is_empty()
            && target.chars().all(ident_char)
        {
            value = rest.trim();
        }
        Some(value)
    })
}

/// The four-character code a local holds: `home_0 = 'AATa';`.
///
/// # Arguments
///
/// * `lines` - The function's lines, trimmed.
/// * `at` - Index of the registration call.
/// * `var` - The local.
fn code_in(lines: &[&str], at: usize, var: &str) -> Option<u32> {
    let value = assigned_before(lines, at, var)?;
    if let Some(chars) = value.strip_prefix('\'').and_then(|v| v.strip_suffix('\'')) {
        let bytes = chars.as_bytes();
        if bytes.len() == 4 {
            return Some(u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]));
        }
        return None;
    }
    constant(value).and_then(|v| u32::try_from(v).ok())
}

/// The constants a function stores through its first parameter, by
/// offset: `a1->field_0x50 = 8;` and `*(uint32_t*)(a1 + 0x50) = 8;`.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
fn constant_stores(text: &str) -> BTreeMap<u64, u64> {
    let mut out = BTreeMap::new();
    for line in text.lines().map(str::trim) {
        let Some((lhs, rhs)) = line.split_once(" = ") else {
            continue;
        };
        let Some(value) = constant(rhs.trim_end_matches(';').trim()) else {
            continue;
        };
        let off = if let Some(hex) = lhs.strip_prefix("a1->field_0x") {
            u64::from_str_radix(hex, 16).ok()
        } else if let Some(inner) = lhs.rsplit_once(")(a1 + ").map(|(_, r)| r) {
            constant(inner.trim_end_matches(')'))
        } else if lhs.ends_with(")a1") && lhs.starts_with("*(") {
            Some(0)
        } else {
            None
        };
        if let Some(off) = off {
            out.insert(off, value);
        }
    }
    out
}

/// The offset every registrar writes its type code at: the one holding
/// a constant in the most registrars, with the most distinct values.
///
/// # Arguments
///
/// * `stores` - Each registrar's constant stores.
fn type_offset(stores: &[BTreeMap<u64, u64>]) -> Option<u64> {
    let mut seen: BTreeMap<u64, (usize, BTreeSet<u64>)> = BTreeMap::new();
    for s in stores {
        for (&off, &value) in s {
            let e = seen.entry(off).or_default();
            e.0 += 1;
            e.1.insert(value);
        }
    }
    let wanted = if stores.len() > 1 { 2 } else { 1 };
    seen.into_iter()
        .filter(|(_, (_, values))| values.len() >= wanted)
        .max_by_key(|(off, (n, values))| (values.len(), *n, std::cmp::Reverse(*off)))
        .map(|(off, _)| off)
}

/// The names the binary's type asserts give the codes stored at `offset`:
/// `if (*(uint32_t*)(x + 0x50) != 10) { assert_failed("... ==
/// Matrix44Type", ...) }` names 10 `Matrix44`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the cross-references.
/// * `overlay` - Names in force.
/// * `overlay_key` - The overlay's fingerprint.
/// * `offset` - The type code's offset in a definition.
fn type_names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    overlay_key: u64,
    offset: u64,
) -> BTreeMap<u64, String> {
    let mut asserts: BTreeMap<u64, (String, String)> = BTreeMap::new();
    for (&target, sites) in &analysis.xrefs {
        if !in_data(program, target) {
            continue;
        }
        let Some((_, text)) = cstr_at(program, target, ASSERT_LEN.0, ASSERT_LEN.1) else {
            continue;
        };
        let Some(ident) = text.rsplit_once("== ").map(|(_, r)| r.trim()) else {
            continue;
        };
        let Some(name) = ident.strip_suffix("Type") else {
            continue;
        };
        if name.is_empty() || !ident.chars().all(ident_char) {
            continue;
        }
        for from in sites.iter().filter_map(|s| s.from_entry) {
            asserts
                .entry(from)
                .or_insert_with(|| (text.clone(), name.to_owned()));
        }
    }
    let guard = format!(" + {offset:#x}) != ");
    let mut out: BTreeMap<u64, String> = BTreeMap::new();
    for (entry, (literal, name)) in asserts {
        let Some(text) = plain_text_cached(program, analysis, overlay, overlay_key, entry) else {
            continue;
        };
        let lines: Vec<&str> = text.lines().map(str::trim).collect();
        let quoted = format!("\"{literal}\"");
        let Some(at) = lines.iter().position(|l| l.contains(&quoted)) else {
            continue;
        };
        let code = lines[at.saturating_sub(GUARD_BACK)..at]
            .iter()
            .rev()
            .find_map(|l| {
                let (_, rest) = l.split_once(&guard)?;
                constant(rest.split(')').next()?.trim())
            });
        if let Some(code) = code {
            out.entry(code).or_insert(name);
        }
    }
    out
}

/// One attribute as its registration site states it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SiteRow {
    /// The definition global.
    definition: u64,
    /// The four-character code.
    code: u32,
    /// The attribute's name.
    name: String,
    /// The access mode passed: `ro`, `rw`, or the value.
    access: String,
    /// The default passed, as text, or `-`.
    default: String,
    /// The registrar it went through.
    registrar: u64,
}

/// Reads one registration function for the attributes it registers.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
/// * `registrars` - Each registrar's entry and the name the text calls it.
fn parse_site(text: &str, registrars: &[(u64, String)]) -> Vec<SiteRow> {
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let mut out = Vec::new();
    for (at, line) in lines.iter().enumerate() {
        for (entry, name) in registrars {
            let Some(args) = call_args(line, name) else {
                continue;
            };
            let [definition, label, code, access, default, ..] = args.as_slice() else {
                continue;
            };
            let Some(definition) = global_addr(definition) else {
                continue;
            };
            let Some(label) = label
                .strip_prefix('&')
                .and_then(|local| literal_into(&lines, local))
            else {
                continue;
            };
            let Some(code) = code
                .strip_prefix('&')
                .and_then(|local| code_in(&lines, at, local))
            else {
                continue;
            };
            let access = match access.as_str() {
                "0" => "ro".to_owned(),
                "1" => "rw".to_owned(),
                other => other.to_owned(),
            };
            let default = match default.strip_prefix('&') {
                Some(local) => literal_into(&lines, local)
                    .map(|l| format!("\"{l}\""))
                    .or_else(|| {
                        let v = assigned_before(&lines, at, local)?;
                        constant(v).map(|_| v.to_owned())
                    })
                    .unwrap_or_else(|| "-".to_owned()),
                None if default.len() <= DEFAULT_MAX => default.clone(),
                None => "-".to_owned(),
            };
            out.push(SiteRow {
                definition,
                code,
                name: label,
                access,
                default,
                registrar: *entry,
            });
        }
    }
    out
}

/// Every attribute the binary registers, with its type and users.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
///
/// # Returns
///
/// The catalog; empty when no function is named after the registration
/// every registrar calls.
#[must_use]
pub fn catalog(program: &Program, analysis: &Analysis, overlay: &Overlay) -> AttrCatalog {
    let overlay_key = overlay.fingerprint();
    let registrars = analysis.packs.list("attributes", "registrar");
    let register: BTreeSet<u64> = analysis
        .functions
        .iter()
        .map(|f| f.entry)
        .filter(|&e| {
            let name = name_of(analysis, overlay, e);
            registrars.iter().any(|r| name.ends_with(r))
        })
        .collect();
    let callers = |targets: &BTreeSet<u64>| -> BTreeSet<u64> {
        targets
            .iter()
            .filter_map(|t| analysis.xrefs.get(t))
            .flatten()
            .filter(|s| s.kind == RefKind::Call)
            .filter_map(|s| s.from_entry)
            .collect()
    };
    let registrar_set = callers(&register);
    if registrar_set.is_empty() {
        return AttrCatalog::default();
    }
    let registrars: Vec<(u64, String)> = registrar_set
        .iter()
        .map(|&e| (e, name_of(analysis, overlay, e)))
        .collect();
    let stores: Vec<BTreeMap<u64, u64>> = registrars
        .iter()
        .map(|&(e, _)| {
            plain_text_cached(program, analysis, overlay, overlay_key, e)
                .map(|t| constant_stores(&t))
                .unwrap_or_default()
        })
        .collect();
    let offset = type_offset(&stores);
    let type_of: BTreeMap<u64, u64> = registrars
        .iter()
        .zip(&stores)
        .filter_map(|((e, _), s)| Some((*e, *s.get(&offset?)?)))
        .collect();
    let variants: BTreeSet<u64> = offset.map_or_else(BTreeSet::new, |off| {
        let handed = [
            format!("a1 + {off},"),
            format!("a1 + {off})"),
            format!("a1 + {off:#x},"),
            format!("a1 + {off:#x})"),
        ];
        registrars
            .iter()
            .filter(|(e, _)| !type_of.contains_key(e))
            .filter(|&&(e, _)| {
                plain_text_cached(program, analysis, overlay, overlay_key, e)
                    .is_some_and(|t| handed.iter().any(|h| t.contains(h.as_str())))
            })
            .map(|(e, _)| *e)
            .collect()
    });
    let type_names = offset.map_or_else(BTreeMap::new, |off| {
        type_names(program, analysis, overlay, overlay_key, off)
    });
    let sites: Vec<u64> = callers(&registrar_set).into_iter().collect();
    let parsed = super::striped_with(
        &sites,
        PAR_MIN,
        || (),
        |(), &site| {
            plain_text_cached(program, analysis, overlay, overlay_key, site)
                .map(|text| parse_site(&text, &registrars))
                .unwrap_or_default()
        },
    );
    let mut attrs: Vec<AttrDef> = Vec::new();
    for (&site, found) in sites.iter().zip(parsed) {
        for row in found.unwrap_or_default() {
            let users: Vec<u64> = analysis
                .xrefs
                .get(&row.definition)
                .into_iter()
                .flatten()
                .filter_map(|s| s.from_entry)
                .filter(|&from| from != site)
                .filter(|&from| !taken_by(analysis, from, site))
                .collect::<BTreeSet<u64>>()
                .into_iter()
                .collect();
            attrs.push(AttrDef {
                code: row.code,
                name: row.name,
                type_code: type_of.get(&row.registrar).copied(),
                variant: variants.contains(&row.registrar),
                access: row.access,
                default: row.default,
                definition: row.definition,
                site,
                registrar: row.registrar,
                users,
            });
        }
    }
    attrs.sort_by(|a, b| a.name.cmp(&b.name).then(a.code.cmp(&b.code)));
    AttrCatalog {
        attrs,
        registrars: registrars.len(),
        type_names,
    }
}

/// Whether `site` takes `function`'s address rather than calling it: the
/// exit-time destructor a registration hands to `atexit`.
///
/// # Arguments
///
/// * `analysis` - Discovery results with the cross-references.
/// * `function` - The candidate user.
/// * `site` - The registration function.
fn taken_by(analysis: &Analysis, function: u64, site: u64) -> bool {
    analysis.xrefs.get(&function).is_some_and(|refs| {
        refs.iter()
            .any(|r| r.from_entry == Some(site) && r.kind != RefKind::Call)
    })
}

/// Renders the attribute catalog as a `#`-headed table.
///
/// One row per attribute, tab-separated: the code (its four characters, or
/// its value when a byte is unprintable), the name, the type, the access
/// mode, the default and the users: up to [`USERS_MAX`] of the functions
/// referencing the definition with `+N more` for the rest, or `-`. A
/// function named in two or more cells of the page is numbered in a
/// `# users:` line and its number stands in the cells ([`Legend`]). A
/// filter matches the name or the code, case-insensitively; when it picks
/// one attribute exactly, the users cell is their count and a table under
/// the row names every one (up to [`USERS_ONE_MAX`]) with the definition
/// global and how each accesses the attribute. An answer lists [`PAGE`]
/// rows at most, whatever `limit` allows beyond, and the header says how
/// many attributes matched.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `filter` - Substring of the name or code; empty for all.
/// * `limit` - Rows shown at most, [`PAGE`] when it allows more.
#[must_use]
pub fn catalog_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    filter: &str,
    limit: usize,
) -> String {
    let cat = analysis
        .derived
        .get_or_build_named("attrs", overlay.fingerprint(), (), || {
            catalog(program, analysis, overlay)
        });
    let q = filter.to_lowercase();
    let picked: Vec<&AttrDef> = cat
        .attrs
        .iter()
        .filter(|a| {
            q.is_empty()
                || a.name.to_lowercase().contains(&q)
                || four_chars(a.code).to_lowercase() == q
        })
        .collect();
    let exact = picked.len() == 1
        || picked
            .iter()
            .filter(|a| a.name.to_lowercase() == q || four_chars(a.code).to_lowercase() == q)
            .count()
            == 1;
    let picked: Vec<&AttrDef> = if exact && picked.len() > 1 {
        picked
            .into_iter()
            .filter(|a| a.name.to_lowercase() == q || four_chars(a.code).to_lowercase() == q)
            .collect()
    } else {
        picked
    };
    let used = picked.iter().filter(|a| !a.users.is_empty()).count();
    let shown = picked.len().min(limit).min(PAGE);
    let one = match picked.as_slice() {
        [one] => Some(*one),
        _ => None,
    };
    let mut out = format!(
        "# {} attributes registered through {} typed registrars",
        cat.attrs.len(),
        cat.registrars
    );
    if !q.is_empty() {
        let _ = write!(
            out,
            ", {} match {}",
            picked.len(),
            crate::text::quoted(filter)
        );
    }
    let _ = write!(
        out,
        ", {used} used by code outside their registration, showing {shown}"
    );
    if shown < picked.len() {
        if shown == PAGE {
            let _ = write!(out, " ({PAGE} per answer)");
        }
        out.push_str("; borer://attrs/<filter> narrows");
    }
    if one.is_none() {
        out.push_str("; borer://attrs/<name> lists one attribute's users");
    }
    if analysis.packs.list("attributes", "registrar").is_empty() {
        out.push_str(
            "; no pack names the registrar (an `[attributes] registrar` line, as packs/nebula.borer has)",
        );
    }
    out.push('\n');
    if !cat.type_names.is_empty() {
        let names: Vec<String> = cat
            .type_names
            .iter()
            .map(|(code, name)| format!("{code}={name}"))
            .collect();
        let _ = writeln!(out, "# types: {}", names.join(" "));
    }
    let rows: Vec<(&AttrDef, Vec<String>)> = picked
        .iter()
        .take(shown)
        .map(|&a| {
            let users = if one.is_some() {
                Vec::new()
            } else {
                a.users
                    .iter()
                    .take(USERS_MAX)
                    .map(|&u| name_of(analysis, overlay, u))
                    .collect()
            };
            (a, users)
        })
        .collect();
    let legend = Legend::of(
        rows.iter()
            .flat_map(|(_, users)| users.iter())
            .map(String::as_str),
    );
    out.push_str(&legend.line("users"));
    out.push_str("code\tname\ttype\taccess\tdefault\tusers\n");
    for (a, users) in &rows {
        let ty = match a.type_code {
            Some(code) => cat
                .type_names
                .get(&code)
                .cloned()
                .unwrap_or_else(|| format!("type{code}")),
            None if a.variant => "Variant".to_owned(),
            None => "?".to_owned(),
        };
        let users = if one.is_some() {
            a.users.len().to_string()
        } else if users.is_empty() {
            "-".to_owned()
        } else {
            let mut parts: Vec<String> = users.iter().map(|u| legend.cell(u)).collect();
            if a.users.len() > USERS_MAX {
                parts.push(format!("+{} more", a.users.len() - USERS_MAX));
            }
            parts.join(" ")
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{ty}\t{}\t{}\t{users}",
            code_or_hex(a.code),
            a.name,
            a.access,
            a.default
        );
    }
    if let Some(one) = one {
        let overlay_key = overlay.fingerprint();
        let listed = &one.users[..one.users.len().min(USERS_ONE_MAX)];
        let accesses = super::striped_with(
            listed,
            PAR_MIN,
            || (),
            |(), &user| {
                plain_text_cached(program, analysis, overlay, overlay_key, user)
                    .map(|text| access_of(&text, one.definition))
            },
        );
        let _ = writeln!(
            out,
            "# {} users of {} ({:#x})",
            one.users.len(),
            one.name,
            one.definition
        );
        out.push_str("function\taccess\tcall\n");
        for (&user, found) in listed.iter().zip(accesses) {
            let (kind, call) = found
                .flatten()
                .flatten()
                .map_or(("ref", String::new()), |(a, call)| (a.word(), call));
            let _ = writeln!(out, "{}\t{kind}\t{call}", name_of(analysis, overlay, user));
        }
        if one.users.len() > USERS_ONE_MAX {
            let _ = writeln!(out, "# {} more users", one.users.len() - USERS_ONE_MAX);
        }
    }
    out
}

/// Lines searched after a function takes an attribute's definition for
/// the accessor call that reads or writes it.
const ACCESS_FORWARD: usize = 12;

/// How a function touches an attribute through its accessors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Access {
    /// Through a `Get...` accessor only.
    Read,
    /// Through a `Set...` accessor only.
    Write,
    /// Through both.
    ReadWrite,
}

impl Access {
    /// The access as the table prints it: `read`, `write` or `read/write`.
    fn word(self) -> &'static str {
        match self {
            Access::Read => "read",
            Access::Write => "write",
            Access::ReadWrite => "read/write",
        }
    }
}

/// How a function touches an attribute: through a table or entity
/// accessor called after it takes the definition, `Set...` writing and
/// `Get...` reading.
///
/// # Arguments
///
/// * `text` - The function's pseudo-C.
/// * `definition` - The attribute's definition global.
///
/// # Returns
///
/// The access with the first accessor call, or `None` when no accessor
/// follows a reference.
fn access_of(text: &str, definition: u64) -> Option<(Access, String)> {
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let (mut read, mut write) = (false, false);
    let mut first: Option<String> = None;
    for (at, line) in lines.iter().enumerate() {
        if line.starts_with("//")
            || !line
                .split(['&', ' ', '(', ')', ',', ';'])
                .any(|w| global_addr(w) == Some(definition))
        {
            continue;
        }
        for later in lines.iter().skip(at).take(ACCESS_FORWARD) {
            let Some(kind) = accessor_kind(later) else {
                continue;
            };
            match kind {
                Access::Write => write = true,
                Access::Read | Access::ReadWrite => read = true,
            }
            first.get_or_insert_with(|| (*later).to_owned());
            break;
        }
    }
    let kind = match (read, write) {
        (true, true) => Access::ReadWrite,
        (false, true) => Access::Write,
        (true, false) => Access::Read,
        (false, false) => return None,
    };
    Some((kind, first.unwrap_or_default()))
}

/// Whether a line calls an attribute accessor, and which way: a method of
/// an attribute table, value table or entity named `Set...` writes, one
/// named `Get...` reads.
///
/// # Arguments
///
/// * `line` - The line.
fn accessor_kind(line: &str) -> Option<Access> {
    let open = line.find('(')?;
    let callee = line[..open]
        .rsplit(|c: char| !(ident_char(c) || c == ':'))
        .next()?;
    let (class, method) = callee.rsplit_once("::")?;
    if !(class.contains("Attr") || class.contains("Table") || class.contains("Entity")) {
        return None;
    }
    if method.starts_with("Set") {
        Some(Access::Write)
    } else if method.starts_with("Get") {
        Some(Access::Read)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A registration as the game's decompile to: the name built into one
    /// local, the code in another, the string default in a third.
    const SITE: &str = "// sub_140001220 @ 0x140001220
uint64_t rdx, local_48, local_88;
uint32_t home_0;

local_48 = local_18 = local_10 = 0;
home_0 = 'AUEV';
sub_140ccfdf0(&local_48, \"AudioEvent\");
local_88 = local_58 = local_50 = 0;
sub_140ccfdf0(&local_88, \"\");
sub_140c81048(&g64_14135e820, &local_48, &home_0, 0, &local_88, 0);
return sub_140d73d38(sub_140df5f40);
";

    /// A registration site yields its definition, code, name, access and
    /// default.
    ///
    /// # Panics
    ///
    /// When a part disagrees with the text.
    #[test]
    fn a_registration_site_is_read_whole() {
        let registrars = vec![(0x1_40c8_1048, "sub_140c81048".to_owned())];
        let found = parse_site(SITE, &registrars);
        assert_eq!(
            found,
            vec![SiteRow {
                definition: 0x1_4135_e820,
                code: u32::from_be_bytes(*b"AUEV"),
                name: "AudioEvent".to_owned(),
                access: "ro".to_owned(),
                default: "\"\"".to_owned(),
                registrar: 0x1_40c8_1048,
            }]
        );
        assert_eq!(global_addr("&g64_14135e820"), Some(0x1_4135_e820));
        assert_eq!(global_addr("&local_48"), None);
        assert_eq!(four_chars(u32::from_be_bytes(*b"AUEV")), "AUEV");
    }

    /// The type offset is the one whose constants differ between
    /// registrars, and a store through a cast pointer counts too.
    ///
    /// # Panics
    ///
    /// When the offset or a store is read wrongly.
    #[test]
    fn the_type_offset_is_where_registrars_differ() {
        let a = constant_stores("a1->field_0x38 = 0;\na1->field_0x50 = 8;\n");
        let b = constant_stores("a1->field_0x38 = 0;\n*(uint32_t*)(a1 + 0x50) = 5;\n");
        let c = constant_stores("a1->field_0x38 = 0;\na1->field_0x50 = 1;\na1->field_0x4c = a4;\n");
        assert_eq!(b.get(&0x50), Some(&5));
        assert_eq!(
            c.get(&0x4c),
            None,
            "a store of a parameter is not a constant"
        );
        assert_eq!(type_offset(&[a, b, c]), Some(0x50));
        assert_eq!(type_offset(&[]), None);
    }

    /// A user that resolves the column and calls the table's setter writes
    /// the attribute; one that calls a getter reads it; one that only
    /// takes its address is neither.
    ///
    /// # Panics
    ///
    /// When an access is read wrongly.
    #[test]
    fn a_user_reads_or_writes_through_the_accessor_it_calls() {
        let writer = "home_0 = &g64_14139eda0;
rax = sub_14012cda4(rax + 48, &home_0);
Attr::AttributeTable::SetInt(rbx, *(uint32_t*)rax, rdi, rsi);
";
        assert_eq!(
            access_of(writer, 0x1_4139_eda0),
            Some((
                Access::Write,
                "Attr::AttributeTable::SetInt(rbx, *(uint32_t*)rax, rdi, rsi);".to_owned()
            ))
        );
        let reader = "local_398 = &g64_14139eda0;
rax = Attr::AttributeTable::GetInt(rax, rdx, 0);
";
        assert_eq!(
            access_of(reader, 0x1_4139_eda0).map(|(k, _)| k),
            Some(Access::Read)
        );
        assert_eq!(
            access_of(
                "x = &g64_14139eda0;
",
                0x1_4139_eda0
            ),
            None
        );
        assert_eq!(
            accessor_kind("Game::Entity::SetFloat(a1, v);"),
            Some(Access::Write)
        );
        assert_eq!(accessor_kind("Util::String::SetCharPtr(a1);"), None);
    }

    /// An image with no attribute registry has an empty catalog and the
    /// table header.
    ///
    /// # Panics
    ///
    /// When the header differs.
    #[test]
    fn an_image_without_a_registry_has_an_empty_table() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let text = catalog_tsv(&p, &a, &Overlay::default(), "", 10);
        assert!(
            text.starts_with("# 0 attributes registered through 0 typed registrars"),
            "{text}"
        );
        assert!(text.contains("code\tname\ttype\taccess\tdefault\tusers\n"));
    }
}
