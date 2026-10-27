//! Managed code: IL methods disassembled and their references indexed.
//!
//! Each IL method's body is disassembled with its tokens named, and the
//! references every body makes (calls, `ldstr`, fields, types) are indexed
//! once per analysis, so callers, callees, string loads and the APIs a
//! method uses answer as they do for native code.
//!
//! A method is named by its `MethodDef` token or by its IL body's address,
//! which carries the method's name as a data symbol. The index is built on
//! first use and memoized in [`crate::analysis::Derived`].

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::Arc;

use super::il::{self, Instr, Operand};
use super::meta::Meta;
use super::{Body, Clr};
use crate::analysis::Analysis;
use crate::program::Program;

/// Most reference sites the index keeps across every body; past it the
/// index says it is capped.
const SITES_MAX: usize = 1 << 21;

/// Bytes read for one body: the largest code [`il::CODE_MAX`] allows and
/// room for its header and clauses.
const BODY_READ: usize = il::CODE_MAX * 2;

/// Most bytes of code the index decodes across every body.
const CODE_TOTAL_MAX: usize = 1 << 26;

/// Why a body has no references: the index's caps were spent before it.
pub(crate) const NOT_INDEXED: &str =
    "not indexed: the index's caps on code and references were spent";

/// Rows one table of callers, callees or strings shows.
pub const ROWS_MAX: usize = 300;

/// `ldstr`.
pub const LDSTR: u16 = 0x72;

/// `ret`.
const RET: u16 = 0x2a;

/// No instruction before a site: the site is the body's first.
const NO_OP: u16 = u16::MAX;

/// The opcodes that call or name a method to call: `jmp`, `call`,
/// `callvirt`, `newobj`, `ldftn`, `ldvirtftn`.
const CALLS: [u16; 6] = [0x27, 0x28, 0x6f, 0x73, 0xfe06, 0xfe07];

/// One instruction that names a token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Site {
    /// Its offset in the code.
    pub off: u32,
    /// Its opcode.
    pub op: u16,
    /// The opcode of the instruction before it, [`NO_OP`] for none.
    pub prev: u16,
    /// The token it names.
    pub token: u32,
    /// The method it names: a `MethodSpec`'s generic method, else
    /// [`Site::token`].
    pub method: u32,
}

impl Site {
    /// Whether the site calls or names a method to call.
    #[must_use]
    pub fn is_call(&self) -> bool {
        CALLS.contains(&self.op)
    }

    /// Whether the instruction before it pushes a constant: an `ldc.*` or
    /// an `ldstr`.
    #[must_use]
    pub fn after_constant(&self) -> bool {
        matches!(self.prev, 0x15..=0x23 | LDSTR)
    }
}

/// One IL method's references.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refs {
    /// The method's `MethodDef` token.
    pub token: u32,
    /// Its IL body's address.
    pub va: u64,
    /// Bytes of code.
    pub code_len: usize,
    /// Instructions decoded.
    pub instrs: usize,
    /// Its sites, in code order.
    pub sites: Vec<Site>,
    /// Why the body did not read or decoding stopped early.
    pub stop: Option<String>,
    /// The body only loads arguments, makes one call (not `newobj`) and
    /// returns: a proxy forwarding to its callee.
    pub forwards: bool,
}

/// Every IL method's references, in table order.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Managed {
    /// The methods with IL bodies.
    pub methods: Vec<Refs>,
    /// More than [`SITES_MAX`] sites were there and the rest were not kept.
    pub capped: bool,
}

impl Managed {
    /// Reads every IL body of a program and indexes its references.
    ///
    /// Methods sharing a body share its entry, read once; past
    /// [`CODE_TOTAL_MAX`] bytes of code or [`SITES_MAX`] sites the rest is
    /// not indexed and the index says it is capped.
    ///
    /// # Arguments
    ///
    /// * `p` - The program.
    #[must_use]
    pub fn build(p: &Program) -> Self {
        let mut out = Managed::default();
        let Ok(meta) = Meta::open(p) else {
            return out;
        };
        let mut budget = (SITES_MAX, CODE_TOTAL_MAX);
        let mut seen: BTreeMap<u64, usize> = BTreeMap::new();
        for m in meta.clr.methods.iter().filter(|m| m.body == Body::Il) {
            let va = p.image_base.saturating_add(u64::from(m.rva));
            let shared = seen.get(&va).and_then(|i| out.methods.get(*i));
            let r = match shared {
                Some(first) if first.sites.len() <= budget.0 => {
                    budget.0 -= first.sites.len();
                    Refs {
                        token: m.token,
                        ..first.clone()
                    }
                }
                _ => {
                    seen.insert(va, out.methods.len());
                    index_body(p, &meta, m.token, va, &mut budget)
                }
            };
            out.capped |= r.stop.as_deref() == Some(NOT_INDEXED);
            out.methods.push(r);
        }
        out
    }

    /// Says when the index misses references: bodies that did not decode
    /// whole, or the caps spent.
    #[must_use]
    pub fn partial(&self) -> String {
        let broken = self.methods.iter().filter(|m| m.stop.is_some()).count();
        if broken == 0 {
            return String::new();
        }
        format!(
            "; partial: {broken} bodies did not decode whole{}, so references in them may be missing",
            if self.capped {
                " or were past the index's caps"
            } else {
                ""
            }
        )
    }

    /// The index of a program, built once per analysis.
    ///
    /// # Arguments
    ///
    /// * `p` - The program.
    /// * `a` - Its analysis, which keeps the index.
    #[must_use]
    pub fn of(p: &Program, a: &Analysis) -> Arc<Self> {
        a.derived.get_or_build("clr_managed", (), || Self::build(p))
    }

    /// One method's references, by its token.
    #[must_use]
    pub fn method(&self, token: u32) -> Option<&Refs> {
        self.methods
            .binary_search_by_key(&token, |m| m.token)
            .ok()
            .and_then(|i| self.methods.get(i))
    }

    /// Every site naming one of `targets`, by the method holding it.
    ///
    /// # Arguments
    ///
    /// * `targets` - The tokens.
    #[must_use]
    pub fn sites_of(&self, targets: &BTreeSet<u32>) -> Vec<(&Refs, Vec<Site>)> {
        self.methods
            .iter()
            .filter_map(|m| {
                let hits: Vec<Site> = m
                    .sites
                    .iter()
                    .filter(|s| targets.contains(&s.token) || targets.contains(&s.method))
                    .copied()
                    .collect();
                (!hits.is_empty()).then_some((m, hits))
            })
            .collect()
    }
}

/// Whether a body only loads arguments, makes one call that is not a
/// `newobj`, and returns.
///
/// # Arguments
///
/// * `instrs` - The body's instructions.
fn forwards(instrs: &[Instr]) -> bool {
    let Some((last, rest)) = instrs.split_last() else {
        return false;
    };
    let calls = rest
        .iter()
        .filter(|i| i.op != 0x73 && CALLS.contains(&i.op))
        .count();
    last.op == RET
        && calls == 1
        && rest
            .iter()
            .all(|i| CALLS.contains(&i.op) || matches!(i.op, 0x02..=0x05 | 0x0e | 0xfe09))
}

/// Reads one body and indexes its references within the budget left.
///
/// # Arguments
///
/// * `p` - The program.
/// * `meta` - The metadata, which names a `MethodSpec`'s generic method.
/// * `token` - The method's token.
/// * `va` - The body's address.
/// * `budget` - Sites and bytes of code the index may still take, lowered
///   by what this body takes.
fn index_body(
    p: &Program,
    meta: &Meta<'_>,
    token: u32,
    va: u64,
    budget: &mut (usize, usize),
) -> Refs {
    let mut r = Refs {
        token,
        va,
        code_len: 0,
        instrs: 0,
        sites: Vec::new(),
        stop: None,
        forwards: false,
    };
    let read = p
        .read_va_upto(va, BODY_READ)
        .ok_or_else(|| format!("the IL body at {va:#x} is not in the file"))
        .and_then(il::header);
    let (body, code) = match read {
        Ok(b) => b,
        Err(why) => {
            r.stop = Some(why);
            return r;
        }
    };
    r.code_len = body.code_len;
    let Some(left) = budget.1.checked_sub(code.len()) else {
        r.stop = Some(NOT_INDEXED.to_owned());
        return r;
    };
    budget.1 = left;
    let (instrs, stop) = il::decode(code);
    r.instrs = instrs.len();
    r.forwards = stop.is_none() && forwards(&instrs);
    r.stop = stop;
    let mut prev = NO_OP;
    for i in &instrs {
        if let Operand::Token(t) = i.operand {
            if budget.0 == 0 {
                r.stop = Some(NOT_INDEXED.to_owned());
                break;
            }
            budget.0 -= 1;
            r.sites.push(Site {
                off: i.off,
                op: i.op,
                prev,
                token: t,
                method: meta.generic_of(t).unwrap_or(t),
            });
        }
        prev = i.op;
    }
    r
}

/// Reads and decodes one body.
///
/// # Arguments
///
/// * `p` - The program.
/// * `va` - The body's address.
///
/// # Errors
///
/// When the body is not in the file or its header does not read.
fn read(p: &Program, va: u64) -> Result<(il::MethodBody, Vec<Instr>, Option<String>), String> {
    let bytes = p
        .read_va_upto(va, BODY_READ)
        .ok_or_else(|| format!("the IL body at {va:#x} is not in the file"))?;
    let (body, code) = il::body(bytes)?;
    let (instrs, stop) = il::decode(code);
    Ok((body, instrs, stop))
}

/// The IL method whose body starts at an address.
///
/// # Arguments
///
/// * `p` - The program.
/// * `va` - The address.
///
/// # Returns
///
/// The method's `MethodDef` token, `None` when no IL body starts there.
#[must_use]
pub fn il_method(p: &Program, va: u64) -> Option<u32> {
    p.clr()?
        .method_at(p.image_base, va)
        .filter(|m| m.body == Body::Il)
        .map(|m| m.token)
}

/// Returns the tokens a name or token text stands for.
///
/// The text is a token in hex whose table a CIL instruction names
/// (`0x0a00001c`), or a method's or field's full name
/// (`System.Reflection.Assembly::Load`) or its end after a dot
/// (`Assembly::Load`), every overload.
///
/// # Arguments
///
/// * `p` - The program.
/// * `text` - The name or token.
///
/// # Returns
///
/// The tokens in table order; `None` for no .NET assembly or no match.
#[must_use]
pub fn targets(p: &Program, text: &str) -> Option<BTreeSet<u32>> {
    let meta = Meta::open(p).ok()?;
    let text = text.trim();
    if let Some(token) = crate::analysis::parse_addr(text)
        .filter(|_| crate::analysis::hex_prefixed(text))
        .and_then(|v| u32::try_from(v).ok())
        .filter(|t| !meta.token(*t).ends_with('?'))
    {
        return Some(BTreeSet::from([token]));
    }
    let tail = format!(".{text}");
    let fits = |name: &str| name == text || (text.contains("::") && name.ends_with(&tail));
    let clr = meta.clr;
    let fields = if text.contains("::") {
        meta.fields()
    } else {
        Vec::new()
    };
    let found: BTreeSet<u32> = clr
        .methods
        .iter()
        .filter(|m| fits(&m.name))
        .map(|m| m.token)
        .chain(
            (1..=u32::try_from(clr.member_refs.len()).unwrap_or(0))
                .map(|r| 0x0a00_0000 | r)
                .filter(|t| meta.member_name(*t).is_some_and(|n| fits(&n))),
        )
        .chain(fields.into_iter().filter(|(_, n)| fits(n)).map(|(t, _)| t))
        .collect();
    (!found.is_empty()).then_some(found)
}

/// The .NET members an argument names, when it names managed code.
///
/// A method's or field's declared name comes first, every overload,
/// unless one of them is a native method ([`targets`]); else the address
/// the argument resolved to when an IL body starts there; else, when that
/// address is not mapped, a token or name.
///
/// # Arguments
///
/// * `p` - The program.
/// * `text` - The argument.
/// * `va` - The address the argument resolved to, `None` for none.
///
/// # Returns
///
/// The tokens, `None` for a program with no .NET metadata or an argument
/// naming native code or nothing managed.
#[must_use]
pub fn named(p: &Program, text: &str, va: Option<u64>) -> Option<BTreeSet<u32>> {
    let clr = p.clr()?;
    let native = |t: &BTreeSet<u32>| {
        t.iter().any(|token| {
            clr.methods
                .iter()
                .any(|m| m.token == *token && m.body == Body::Native)
        })
    };
    if !crate::analysis::hex_prefixed(text)
        && let Some(found) = targets(p, text).filter(|t| !native(t))
    {
        return Some(found);
    }
    if let Some(va) = va {
        if let Some(token) = il_method(p, va) {
            return Some(BTreeSet::from([token]));
        }
        if p.read_va(va, 1).is_some() {
            return None;
        }
    }
    targets(p, text)
}

/// The IL method an argument names ([`named`]): the first `MethodDef`
/// with an IL body among the names it stands for.
///
/// # Arguments
///
/// * `p` - The program.
/// * `text` - The argument.
/// * `va` - The address the argument resolved to, `None` for none.
#[must_use]
pub fn il_method_named(p: &Program, text: &str, va: Option<u64>) -> Option<u32> {
    let clr = p.clr()?;
    named(p, text, va)?.into_iter().find(|t| {
        clr.methods
            .iter()
            .any(|m| m.token == *t && m.body == Body::Il)
    })
}

/// A method's header lines: its name and signature, body header, locals
/// and exception clauses.
fn header(meta: &Meta<'_>, r: &Refs, body: &il::MethodBody) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "# .NET method {:#010x} {}, IL body at {:#x}",
        r.token,
        meta.token(r.token),
        r.va
    );
    let locals = if body.locals == 0 {
        "no locals".to_owned()
    } else {
        meta.token(body.locals)
    };
    let _ = writeln!(
        out,
        "# {} header, {} bytes of code, max stack {}, {locals}{}; {} exception clauses",
        if body.fat { "fat" } else { "tiny" },
        body.code_len,
        body.max_stack,
        if body.init_locals {
            ", init locals"
        } else {
            ""
        },
        body.clauses.len()
    );
    for c in &body.clauses {
        let extra = match c.kind {
            il::ClauseKind::Catch => format!(" {}", meta.token(c.extra)),
            il::ClauseKind::Filter => format!(" filter IL_{:04x}", c.extra),
            il::ClauseKind::Finally | il::ClauseKind::Fault => String::new(),
        };
        let _ = writeln!(
            out,
            "# .try IL_{:04x}..IL_{:04x} {}{extra} handler IL_{:04x}..IL_{:04x}",
            c.try_start,
            c.try_end,
            c.kind.word(),
            c.handler_start,
            c.handler_end
        );
    }
    out
}

/// A branch target as a label.
fn label(t: i64) -> String {
    if t >= 0 {
        format!("IL_{t:04x}")
    } else {
        format!("IL_-{:x}", t.unsigned_abs())
    }
}

/// One instruction's operand as a listing shows it.
fn operand_text(meta: &Meta<'_>, o: &Operand) -> String {
    match o {
        Operand::None => String::new(),
        Operand::Int(v) => v.to_string(),
        Operand::Var(v) => v.to_string(),
        Operand::Real(v) => v.to_string(),
        Operand::Token(t) => meta.token(*t),
        Operand::Target(t) => label(*t),
        Operand::Switch(ts) => {
            let shown: Vec<String> = ts.iter().take(64).map(|t| label(*t)).collect();
            let more = if ts.len() > 64 { ", ..." } else { "" };
            format!("({}{more})", shown.join(", "))
        }
    }
}

/// Disassembles one IL method, every token named.
///
/// # Arguments
///
/// * `p` - The program.
/// * `token` - The method's `MethodDef` token.
/// * `max` - Most instructions shown.
///
/// # Returns
///
/// Header lines (signature, body header, locals, exception clauses), then
/// `IL_<offset>: <op> <operand>` rows; a branch's operand is the label of
/// its target's row.
///
/// # Errors
///
/// When the program is no .NET assembly, the token names no IL method, or
/// its body does not read.
pub fn listing(p: &Program, token: u32, max: usize) -> Result<String, String> {
    let meta = Meta::open(p)?;
    let r = il_refs(meta.clr, p, token)?;
    let (body, instrs, stop) = read(p, r.va)?;
    let mut out = header(&meta, &r, &body);
    for i in instrs.iter().take(max) {
        let operand = operand_text(&meta, &i.operand);
        let _ = writeln!(
            out,
            "IL_{:04x}: {}{}{operand}",
            i.off,
            i.name(),
            if operand.is_empty() { "" } else { " " }
        );
    }
    if instrs.len() > max {
        let _ = writeln!(
            out,
            "# showing {max} of {} instructions; max_instrs shows more",
            instrs.len()
        );
    }
    if let Some(why) = stop {
        let _ = writeln!(out, "# decoding stopped: {why}");
    }
    Ok(out)
}

/// The index entry of an IL method, its references unread.
///
/// # Errors
///
/// When the token names no method with an IL body.
fn il_refs(clr: &Clr, p: &Program, token: u32) -> Result<Refs, String> {
    let m = clr
        .methods
        .iter()
        .find(|m| m.token == token)
        .ok_or_else(|| format!("{token:#010x} is no method of this assembly"))?;
    if m.body != Body::Il {
        return Err(format!(
            "{token:#010x} {} has no IL body: it is {}",
            m.name,
            m.body.word()
        ));
    }
    Ok(Refs {
        token,
        va: p.image_base.saturating_add(u64::from(m.rva)),
        code_len: 0,
        instrs: 0,
        sites: Vec::new(),
        stop: None,
        forwards: false,
    })
}

/// An IL method's index entry.
///
/// # Errors
///
/// When the token names no method with an IL body.
fn indexed<'i>(index: &'i Managed, clr: &Clr, p: &Program, token: u32) -> Result<&'i Refs, String> {
    if let Some(r) = index.method(token) {
        return Ok(r);
    }
    il_refs(clr, p, token)?;
    Err(format!("{token:#010x}: its IL body was not indexed"))
}

/// The user strings one IL method loads, as `site token text` rows.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis, which keeps the index.
/// * `token` - The method's `MethodDef` token.
///
/// # Errors
///
/// When the token names no IL method.
pub fn strings_tsv(p: &Program, a: &Analysis, token: u32) -> Result<String, String> {
    let meta = Meta::open(p)?;
    let index = Managed::of(p, a);
    let r = indexed(&index, meta.clr, p, token)?;
    let loads: Vec<&Site> = r.sites.iter().filter(|s| s.op == LDSTR).collect();
    let mut out = format!(
        "# {} user strings loaded by {:#010x} {} (ldstr), showing {} of {}{}\nsite\ttoken\ttext\n",
        loads.len(),
        token,
        meta.member_name(token).unwrap_or_default(),
        loads.len().min(ROWS_MAX),
        loads.len(),
        r.stop.as_ref().map_or_else(String::new, |why| format!(
            "; partial, the body stopped: {why}"
        ))
    );
    for s in loads.iter().take(ROWS_MAX) {
        let _ = writeln!(
            out,
            "IL_{:04x}\t{:#010x}\t{}",
            s.off,
            s.token,
            meta.token(s.token)
        );
    }
    Ok(out)
}

/// One IL method's facts: its body, and who calls it, what it calls and
/// what else it names, as `rel token sites name` rows.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis, which keeps the index.
/// * `token` - The method's `MethodDef` token.
/// * `offset` - Rows skipped.
///
/// # Errors
///
/// When the token names no IL method or its body does not read.
pub fn detail(p: &Program, a: &Analysis, token: u32, offset: usize) -> Result<String, String> {
    let meta = Meta::open(p)?;
    let index = Managed::of(p, a);
    let r = indexed(&index, meta.clr, p, token)?;
    let (body, _, _) = read(p, r.va)?;
    let mut out = header(&meta, r, &body);
    let mut rows: Vec<(&str, u32, usize)> = Vec::new();
    for (m, hits) in index.sites_of(&BTreeSet::from([token])) {
        rows.push(("caller", m.token, hits.len()));
    }
    let mut named: BTreeMap<(u8, u32), usize> = BTreeMap::new();
    for s in &r.sites {
        let rank = if s.is_call() {
            0
        } else if s.op == LDSTR {
            2
        } else {
            1
        };
        *named.entry((rank, s.token)).or_default() += 1;
    }
    for ((rank, t), n) in named {
        let rel = ["callee", "uses", "string"]
            .get(usize::from(rank))
            .copied()
            .unwrap_or("uses");
        rows.push((rel, t, n));
    }
    let start = offset.min(rows.len());
    let _ = writeln!(
        out,
        "# {} instructions, {} callers, tags {}; showing {} of {} rows from {start}{}",
        r.instrs,
        rows.iter().filter(|x| x.0 == "caller").count(),
        tags_text(&tags(&meta, r, &pinvoke_names(&meta))),
        rows.len().saturating_sub(start).min(ROWS_MAX),
        rows.len(),
        r.stop
            .as_ref()
            .map_or_else(String::new, |w| format!("; decoding stopped: {w}"))
    );
    out.push_str("rel\ttoken\tsites\tname\n");
    for (rel, t, n) in rows.iter().skip(start).take(ROWS_MAX) {
        let _ = writeln!(out, "{rel}\t{t:#010x}\t{n}\t{}", meta.token(*t));
    }
    Ok(out)
}

/// The methods referencing any of `targets`, one row per method, paged.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis, which keeps the index.
/// * `targets` - The tokens ([`targets`]).
/// * `offset` - Rows skipped.
/// * `limit` - Most rows shown.
/// * `count_only` - Only the header line.
///
/// # Errors
///
/// When the program is no .NET assembly.
pub fn xrefs_tsv(
    p: &Program,
    a: &Analysis,
    targets: &BTreeSet<u32>,
    offset: usize,
    limit: usize,
    count_only: bool,
) -> Result<String, String> {
    let meta = Meta::open(p)?;
    let index = Managed::of(p, a);
    let hits = index.sites_of(targets);
    let names: Vec<String> = targets.iter().take(4).map(|t| meta.token(*t)).collect();
    let total_sites: usize = hits.iter().map(|(_, s)| s.len()).sum();
    let start = offset.min(hits.len());
    let page = hits.iter().skip(start).take(limit);
    let mut out = format!(
        "# {total_sites} IL references to {}{} from {} methods{}; showing {} of {} from {start}\n",
        names.join(" | "),
        if targets.len() > 4 { " | ..." } else { "" },
        hits.len(),
        index.partial(),
        hits.len().saturating_sub(start).min(limit),
        hits.len()
    );
    if count_only || hits.is_empty() {
        return Ok(out);
    }
    out.push_str("method\tva\tsites\tname\n");
    for (m, sites) in page {
        let at: Vec<String> = sites
            .iter()
            .take(4)
            .map(|s| format!("IL_{:04x} {}", s.off, il::name(s.op).unwrap_or("?")))
            .collect();
        let more = if sites.len() > 4 { ", ..." } else { "" };
        let _ = writeln!(
            out,
            "{:#010x}\t{:#x}\t{}{more}\t{}",
            m.token,
            m.va,
            at.join(", "),
            meta.member_name(m.token).unwrap_or_default()
        );
    }
    Ok(out)
}

/// What a called API says about a method, by the prefix of the called
/// member's `Owner::Name`.
pub const API_TAGS: [(&str, &str); 27] = [
    ("load", "System.Reflection.Assembly::Load"),
    ("load", "System.Reflection.Assembly::UnsafeLoadFrom"),
    ("load", "System.AppDomain::Load"),
    ("reflect", "System.Reflection.MethodBase::Invoke"),
    ("reflect", "System.Type::InvokeMember"),
    ("reflect", "System.Type::GetMethod"),
    ("reflect", "System.Activator::CreateInstance"),
    ("reflect", "System.Delegate::DynamicInvoke"),
    ("emit", "System.Reflection.Emit."),
    ("process", "System.Diagnostics.Process::"),
    ("process", "System.Diagnostics.ProcessStartInfo::"),
    ("net", "System.Net."),
    ("registry", "Microsoft.Win32.Registry"),
    ("crypto", "System.Security.Cryptography."),
    ("file", "System.IO.File::"),
    ("file", "System.IO.Directory::"),
    ("file", "System.IO.FileStream::"),
    ("decode", "System.Convert::FromBase64"),
    ("compress", "System.IO.Compression."),
    (
        "resource",
        "System.Reflection.Assembly::GetManifestResource",
    ),
    ("resource", "System.Resources.ResourceManager::"),
    ("env", "System.Environment::GetFolderPath"),
    ("env", "System.Environment::GetEnvironmentVariable"),
    ("screen", "System.Drawing.Graphics::CopyFromScreen"),
    ("clipboard", "System.Windows.Forms.Clipboard::"),
    ("wmi", "System.Management."),
    ("marshal", "System.Runtime.InteropServices.Marshal::"),
];

/// The word tagging a call to a P/Invoke.
pub const PINVOKE_TAG: &str = "pinvoke";

/// The tags a method's calls earn, each with the APIs that earned it, in
/// tag order.
///
/// # Arguments
///
/// * `meta` - The metadata.
/// * `r` - The method's references.
fn tags(
    meta: &Meta<'_>,
    r: &Refs,
    pinvokes: &BTreeMap<u32, String>,
) -> BTreeMap<&'static str, BTreeSet<String>> {
    let mut out: BTreeMap<&'static str, BTreeSet<String>> = BTreeMap::new();
    let called: BTreeSet<u32> = r
        .sites
        .iter()
        .filter(|s| s.is_call())
        .map(|s| s.token)
        .collect();
    for t in called {
        if let Some(native) = pinvokes.get(&t) {
            out.entry(PINVOKE_TAG).or_default().insert(native.clone());
            continue;
        }
        let Some(name) = meta.member_name(t) else {
            continue;
        };
        for (tag, prefix) in API_TAGS {
            if name.starts_with(prefix) {
                out.entry(tag).or_default().insert(name.clone());
            }
        }
    }
    out
}

/// Each P/Invoke's `dll!export`, by its method's token.
fn pinvoke_names(meta: &Meta<'_>) -> BTreeMap<u32, String> {
    meta.clr
        .pinvokes
        .iter()
        .map(|pi| (pi.token, format!("{}!{}", pi.dll, pi.entry)))
        .collect()
}

/// Tags as a comma-separated list, `-` for none.
fn tags_text(tags: &BTreeMap<&'static str, BTreeSet<String>>) -> String {
    if tags.is_empty() {
        "-".to_owned()
    } else {
        tags.keys().copied().collect::<Vec<_>>().join(",")
    }
}

/// What earns a method its row: the APIs of the tags asked for, then its
/// other APIs; or, with texts, its APIs and loaded strings containing one.
///
/// # Arguments
///
/// * `meta` - The metadata.
/// * `r` - The method's references.
/// * `t` - Its tags ([`tags`]).
/// * `name` - Its name.
/// * `want_tags` - The tags asked for.
/// * `texts` - The texts asked for, lowercased.
///
/// # Returns
///
/// The evidence, `None` when a text is in neither the name, an API nor a
/// string.
fn evidence(
    meta: &Meta<'_>,
    r: &Refs,
    t: &BTreeMap<&'static str, BTreeSet<String>>,
    name: &str,
    want_tags: &[&str],
    texts: &[String],
) -> Option<Vec<String>> {
    let mut out: Vec<String> = Vec::new();
    if texts.is_empty() {
        for api in want_tags
            .iter()
            .filter_map(|w| t.get(w))
            .chain(t.values())
            .flatten()
        {
            if !out.contains(api) {
                out.push(api.clone());
            }
        }
        return Some(out);
    }
    let lower = name.to_lowercase();
    let called: BTreeSet<u32> = r
        .sites
        .iter()
        .filter(|s| s.is_call())
        .map(|s| s.token)
        .collect();
    let mut said: Vec<String> = called
        .into_iter()
        .filter_map(|c| meta.member_name(c))
        .collect();
    said.extend(t.get(PINVOKE_TAG).into_iter().flatten().cloned());
    said.extend(
        r.sites
            .iter()
            .filter(|s| s.op == LDSTR)
            .map(|s| meta.token(s.token)),
    );
    let all_hit = texts.iter().all(|x| {
        lower.contains(x.as_str()) || said.iter().any(|s| s.to_lowercase().contains(x.as_str()))
    });
    all_hit.then(|| {
        said.into_iter()
            .filter(|s| texts.iter().any(|x| s.to_lowercase().contains(x.as_str())))
            .collect()
    })
}

/// Lists IL methods with what they call and load: `token va code tags
/// name evidence` rows, narrowed by tags and texts.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis, which keeps the index.
/// * `spec` - Comma-separated tags ([`API_TAGS`], `pinvoke`), which a
///   method must all have, texts its name, a string it loads or an API it
///   calls contains, `offset=<n>` and `limit=<n>`.
///
/// # Errors
///
/// When the program is no .NET assembly or the page does not read.
pub fn methods_tsv(p: &Program, a: &Analysis, spec: &str) -> Result<String, String> {
    let meta = Meta::open(p)?;
    let index = Managed::of(p, a);
    let (mut want_tags, mut texts, mut offset, mut limit) =
        (Vec::new(), Vec::new(), 0, super::CLR_PAGE);
    for word in spec.split(',').map(str::trim).filter(|w| !w.is_empty()) {
        if let Some(n) = word.strip_prefix("offset=") {
            offset = crate::table::row_offset(n)?;
        } else if let Some(n) = word.strip_prefix("limit=") {
            limit = crate::table::row_limit(n)?.min(super::CLR_PAGE);
        } else if word == PINVOKE_TAG || API_TAGS.iter().any(|(t, _)| *t == word) {
            want_tags.push(word);
        } else {
            texts.push(word.to_lowercase());
        }
    }
    let pinvokes = pinvoke_names(&meta);
    let mut rows = Vec::new();
    for r in &index.methods {
        let t = tags(&meta, r, &pinvokes);
        if !want_tags.iter().all(|w| t.contains_key(w)) {
            continue;
        }
        let name = meta.member_name(r.token).unwrap_or_default();
        let Some(evidence) = evidence(&meta, r, &t, &name, &want_tags, &texts) else {
            continue;
        };
        let shown: Vec<String> = evidence.iter().take(3).cloned().collect();
        let more = if evidence.len() > 3 {
            format!("; +{}", evidence.len() - 3)
        } else {
            String::new()
        };
        rows.push(format!(
            "{:#010x}\t{:#x}\t{}\t{}\t{name}\t{}{more}",
            r.token,
            r.va,
            r.code_len,
            tags_text(&t),
            if shown.is_empty() {
                "-".to_owned()
            } else {
                shown.join("; ")
            }
        ));
    }
    let start = offset.min(rows.len());
    let page: Vec<&String> = rows.iter().skip(start).take(limit).collect();
    let mut out = format!(
        "# IL methods by what they call and load: tags {} {PINVOKE_TAG}; {} of {} methods match{}\n# showing {} of {} from {start}; borer://clr/methods,<tag or text> narrows, offset=<n> pages; disassemble_function <token or name> lists a method's IL\n",
        API_TAGS
            .iter()
            .map(|(t, _)| *t)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .join(" "),
        rows.len(),
        index.methods.len(),
        if index.capped {
            "; capped: more references than were indexed"
        } else {
            ""
        },
        page.len(),
        rows.len()
    );
    if !page.is_empty() {
        out.push_str("token\tva\tcode\ttags\tname\tevidence\n");
        for row in page {
            out.push_str(row);
            out.push('\n');
        }
    }
    Ok(out)
}
