//! .NET obfuscator markers, each with its evidence.
//!
//! The markers are an obfuscator's own type or attribute names, renamed
//! symbols, a module initializer, bodies that do not decode, call proxies, and the string decryptor's shape (a
//! static method taking integers or strings and returning a string, called
//! right after a constant at most of its many call sites).
//!
//! A marker is a hint, not a verdict: each row says what it rests on, and
//! a shape that holds only weakly is not reported, since a missed marker
//! beats a false one.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::managed::{LDSTR, Managed, Refs};
use super::meta::Meta;
use crate::analysis::Analysis;
use crate::program::Program;
use crate::text::one_line;

/// Names an obfuscator leaves in the types or attributes it adds, with the
/// obfuscator; matched as a part of a type's or attribute's full name.
const NAMED: [(&str, &str); 14] = [
    ("ConfusedByAttribute", "ConfuserEx"),
    ("SmartAssembly.", "SmartAssembly"),
    ("PoweredByAttribute", "SmartAssembly"),
    ("DotfuscatorAttribute", "Dotfuscator"),
    ("BabelObfuscatorAttribute", "Babel"),
    ("BabelAttribute", "Babel"),
    ("CryptoObfuscator", "Crypto Obfuscator"),
    ("ObfuscatedByGoliath", "Goliath"),
    ("Xenocode.", "Xenocode"),
    ("YanoAttribute", "Yano"),
    ("AgileDotNetRT", "Agile.NET"),
    ("NineRays.Obfuscator", "Spices.Net"),
    ("ZYXDNGuarder", "DNGuard"),
    ("__.NETReactor", ".NET Reactor"),
];

/// The attribute that asks `ildasm` to refuse the assembly.
const SUPPRESS_ILDASM: &str = "System.Runtime.CompilerServices.SuppressIldasmAttribute";

/// Fewest calls a string decryptor has.
const DECRYPTOR_CALLS: usize = 5;

/// Share of a decryptor's calls, in percent, that come right after a
/// constant.
const DECRYPTOR_CONSTANT_PCT: usize = 75;

/// Fewest renamed names, and their least share in percent, that make the
/// renaming marker.
const RENAMED: (usize, usize) = (5, 10);

/// Fewest call proxies that make the proxy marker.
const PROXIES: usize = 10;

/// Most samples one row's evidence names.
const SAMPLES: usize = 3;

/// Whether a simple name is not what a compiler emits.
///
/// Such a name has a character that is neither a letter or digit in any
/// script (C# and VB take Unicode identifiers) nor one of a compiler's
/// `<>`, `$`, `` ` `` and `.` names: an invisible or control character.
fn renamed(name: &str) -> bool {
    !name.chars().all(|c| {
        c.is_alphanumeric()
            || matches!(c, '_' | '<' | '>' | '$' | '`' | '.' | '-' | '=' | '|' | '@')
    })
}

/// The simple name after a full name's last `::`, `/` or `.`.
fn simple(full: &str) -> &str {
    let tail = full.rsplit_once("::").map_or(full, |(_, m)| m);
    let tail = tail.rsplit_once('/').map_or(tail, |(_, n)| n);
    if tail.starts_with('.') {
        tail
    } else {
        tail.rsplit_once('.').map_or(tail, |(_, n)| n)
    }
}

/// The obfuscators' own names among the types and attributes.
fn named(meta: &Meta<'_>, rows: &mut Vec<(String, &'static str, String)>) {
    let clr = meta.clr;
    let attrs = meta.attributes();
    let mut found: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    for (needle, who) in NAMED {
        let hits = found.entry(who).or_default();
        hits.extend(
            clr.types
                .iter()
                .filter(|t| t.name.contains(needle))
                .map(|t| format!("TypeDef {}", t.name)),
        );
        hits.extend(
            clr.type_refs
                .iter()
                .filter(|t| t.contains(needle))
                .map(|t| format!("TypeRef {t}")),
        );
        hits.extend(attrs.iter().filter(|a| a.class.contains(needle)).map(|a| {
            let arg = a
                .arg
                .as_ref()
                .map_or_else(String::new, |s| format!("(\"{s}\")"));
            format!("attribute {}{arg} on {:#010x}", a.class, a.parent)
        }));
    }
    for (who, mut hits) in found {
        hits.dedup();
        if !hits.is_empty() {
            rows.push((
                who.to_lowercase().replace([' ', '.'], ""),
                "strong",
                samples(&hits, hits.len()),
            ));
        }
    }
    if let Some(a) = attrs.iter().find(|a| a.class == SUPPRESS_ILDASM) {
        rows.push((
            "anti-ildasm".to_owned(),
            "medium",
            format!("attribute {} on {:#010x}, which obfuscators add and compilers emit only when asked", a.class, a.parent),
        ));
    }
}

/// At most [`SAMPLES`] items joined, and how many there were.
fn samples(items: &[String], total: usize) -> String {
    let shown: Vec<String> = items.iter().take(SAMPLES).map(|s| one_line(s)).collect();
    if total > SAMPLES {
        format!("{} (+{} more)", shown.join("; "), total - SAMPLES)
    } else {
        shown.join("; ")
    }
}

/// Renamed types and methods.
fn renaming(meta: &Meta<'_>, rows: &mut Vec<(String, &'static str, String)>) {
    let clr = meta.clr;
    let names: Vec<&str> = clr
        .types
        .iter()
        .map(|t| t.name.as_str())
        .chain(clr.methods.iter().map(|m| m.name.as_str()))
        .collect();
    let odd: Vec<String> = names
        .iter()
        .filter(|n| renamed(simple(n)))
        .map(|n| (*n).to_owned())
        .collect();
    if odd.len() >= RENAMED.0 && odd.len() * 100 >= names.len() * RENAMED.1 {
        rows.push((
            "renamed".to_owned(),
            "medium",
            format!(
                "{} of {} type and method names are not compiler identifiers, e.g. {}",
                odd.len(),
                names.len(),
                samples(&odd, odd.len())
            ),
        ));
    }
}

/// The module initializer, bodies that do not decode, and call proxies.
fn bodies(meta: &Meta<'_>, index: &Managed, rows: &mut Vec<(String, &'static str, String)>) {
    let clr = meta.clr;
    if let Some(init) = clr.methods.iter().find(|m| m.name == "<Module>::.cctor")
        && let Some(r) = index.method(init.token)
    {
        let calls: Vec<String> = r
            .sites
            .iter()
            .filter(|s| s.is_call())
            .filter_map(|s| meta.member_name(s.token))
            .collect();
        if !calls.is_empty() {
            rows.push((
                "module-initializer".to_owned(),
                "weak",
                format!(
                    "<Module>::.cctor {:#010x} runs before any other code and calls {}",
                    init.token,
                    samples(&calls, calls.len())
                ),
            ));
        }
    }
    let broken: Vec<String> = index
        .methods
        .iter()
        .filter_map(|r| {
            let why = r.stop.as_ref()?;
            Some(format!(
                "{:#010x} {}: {why}",
                r.token,
                meta.member_name(r.token).unwrap_or_default()
            ))
        })
        .collect();
    if !broken.is_empty() {
        rows.push((
            "invalid-il".to_owned(),
            "medium",
            format!(
                "{} of {} IL bodies do not decode (encrypted until run, or junk), e.g. {}",
                broken.len(),
                index.methods.len(),
                samples(&broken, broken.len())
            ),
        ));
    }
    let proxies: Vec<String> = index
        .methods
        .iter()
        .filter(|r| is_proxy(r))
        .filter_map(|r| r.sites.first().and_then(|s| meta.member_name(s.token)))
        .collect();
    if proxies.len() >= PROXIES {
        rows.push((
            "call-proxies".to_owned(),
            "medium",
            format!(
                "{} methods only forward their arguments to one call, hiding the callee from the caller, e.g. to {}",
                proxies.len(),
                samples(&proxies, proxies.len())
            ),
        ));
    }
}

/// Whether a method's body only forwards its arguments to one call: its
/// one site is a call and its instructions are argument loads, the call
/// and `ret`.
fn is_proxy(r: &Refs) -> bool {
    r.forwards && r.instrs <= 8
}

/// String decryptors: static methods returning a string from integer or
/// string parameters, called often and mostly right after a constant.
fn decryptors(meta: &Meta<'_>, index: &Managed, rows: &mut Vec<(String, &'static str, String)>) {
    let mut calls: BTreeMap<u32, (usize, usize, Vec<u32>)> = BTreeMap::new();
    let mut loads = 0usize;
    for r in &index.methods {
        for s in &r.sites {
            if s.op == LDSTR {
                loads += 1;
            } else if s.op == 0x28 {
                let e = calls.entry(s.token).or_default();
                e.0 += 1;
                e.1 += usize::from(s.after_constant());
                if e.2.last() != Some(&r.token) {
                    e.2.push(r.token);
                }
            }
        }
    }
    for (token, (n, constant, callers)) in calls {
        if n < DECRYPTOR_CALLS || constant * 100 < n * DECRYPTOR_CONSTANT_PCT {
            continue;
        }
        let Some(sig) = meta.sig(token) else {
            continue;
        };
        let text = meta.token(token);
        let returns_string =
            sig.ret == "string" || (sig.ret.starts_with("!!") && text.contains("<string>"));
        let keys = !sig.params.is_empty()
            && sig.params.len() <= 3
            && sig
                .params
                .iter()
                .all(|p| matches!(p.as_str(), "int" | "uint" | "long" | "ulong" | "string"));
        if sig.this || !returns_string || !keys {
            continue;
        }
        rows.push((
            "string-decryptor".to_owned(),
            if n >= 2 * DECRYPTOR_CALLS { "strong" } else { "medium" },
            format!(
                "{text} {token:#010x}: {n} calls from {} methods, {}% right after a constant; the code loads {loads} literal strings with ldstr",
                callers.len(),
                constant * 100 / n
            ),
        ));
    }
}

/// Lists the obfuscator markers of a .NET assembly, each with its
/// evidence.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis, which keeps the IL index.
///
/// # Returns
///
/// `marker strength evidence` rows under a header; a line saying none was
/// found when none was.
///
/// # Errors
///
/// When the program is no .NET assembly or its metadata was refused.
pub fn markers_tsv(p: &Program, a: &Analysis) -> Result<String, String> {
    let meta = Meta::open(p)?;
    let index = Managed::of(p, a);
    let mut rows = Vec::new();
    named(&meta, &mut rows);
    renaming(&meta, &mut rows);
    bodies(&meta, &index, &mut rows);
    decryptors(&meta, &index, &mut rows);
    let mut out = format!(
        "# .NET obfuscator markers: {} found over {} types and {} IL methods; a marker is a hint with its evidence, not a verdict\n",
        rows.len(),
        meta.clr.types.len(),
        index.methods.len()
    );
    if rows.is_empty() {
        out.push_str("# no marker: no obfuscator's names, renaming, undecodable bodies, proxies or string decryptor seen\n");
        return Ok(out);
    }
    out.push_str("marker\tstrength\tevidence\n");
    for (marker, strength, evidence) in rows {
        let _ = writeln!(out, "{marker}\t{strength}\t{evidence}");
    }
    Ok(out)
}
