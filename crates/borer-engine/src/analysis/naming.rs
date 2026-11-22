//! Function names inferred from the signature strings asserts and logs carry.
//!
//! `__FUNCSIG__` and `__PRETTY_FUNCTION__` literals name the function that
//! contains them: `sub_140a9b9bc` becomes `UI::WindowManager::Instance` at
//! analysis time, so every tool, listing and call site shows the real name
//! without a script pass. The same string declares the return type and the
//! parameter types, which the decompiler puts in the signature line.
//!
//! A function's candidates are the signature strings its code references. A
//! candidate no other function references names the function outright. One
//! referenced from several functions belongs to a helper inlined into them;
//! once every other referrer has a name of its own, the remaining one is the
//! helper itself and takes it. When that never happens (the other referrers
//! carry no signature of their own), the helper is the one referrer that
//! mentions no other signature and reads exactly the argument registers the
//! signature declares (`this` included). A name goes to one function only:
//! the other referrers inlined it and stay `sub_`, as does anything still
//! ambiguous.
//!
//! A trace string (`Class::Method()`, no return type) reads the same as an
//! assert's condition, so it names a function only as a weaker fallback on
//! evidence outside the text ([`choose_traces`]), and declares no types.
//!
//! The template signatures GCC and Clang write (`void Box<T>::Grow() [with
//! T = int]`) name nothing; they say what code a function holds
//! ([`templates`]).

use std::collections::{BTreeMap, BTreeSet};

use crate::isa::x86::{InstructionInfoFactory, OpAccess, Register};

use super::classes::class_of;
use super::functions::decode_block;
use super::schema::ident_char;
use super::{Analysis, Function, NameSource, Signature, data_referrers, single};
use crate::program::{BinaryFormat, Program};
use crate::strings::cstr_at;

pub(crate) mod templates;

/// Longest signature string read.
pub(crate) const SIG_MAX: usize = 512;
/// Shortest text considered.
const SIG_MIN: usize = 8;
/// Longest inferred name kept.
const NAME_MAX: usize = 120;
/// Calling-convention keywords MSVC's `__FUNCSIG__` places before the name.
const CONVENTIONS: [&str; 6] = [
    "__cdecl ",
    "__thiscall ",
    "__fastcall ",
    "__stdcall ",
    "__vectorcall ",
    "__clrcall ",
];
/// Elaborated-type keywords dropped from types and template arguments.
const KEYWORDS: [&str; 4] = ["class ", "struct ", "enum ", "union "];
/// First words that make a convention-less, namespace-less head a signature
/// (`int main(int, char **)`) rather than prose.
const TYPE_WORDS: [&str; 16] = [
    "void", "int", "bool", "char", "unsigned", "signed", "long", "short", "float", "double",
    "static", "const", "size_t", "auto", "virtual", "inline",
];

/// Keywords a return type may spell beside its name, past [`TYPE_WORDS`].
const SPECIFIERS: [&str; 10] = [
    "volatile",
    "constexpr",
    "extern",
    "explicit",
    "typename",
    "mutable",
    "wchar_t",
    "char8_t",
    "char16_t",
    "char32_t",
];

/// Steps [`choose_own`] may take per reference from a function to a name.
///
/// Each function is decided in at most two visits that read its
/// references, and each name's referrers are read once: three steps per
/// reference.
const FUEL_PER_REFERENCE: usize = 4;

/// The signature strings the code references.
struct Found {
    /// Each signature read, one per string, in address order.
    sigs: Vec<Signature>,
    /// Each referring function's candidates: a name, by its index in
    /// `referrers`, to the index in `sigs` of the first string the
    /// function references under it.
    candidates: BTreeMap<u64, BTreeMap<usize, usize>>,
    /// The functions referencing each name, names in the order met.
    referrers: Vec<BTreeSet<u64>>,
}

/// What a string the code references reads as.
enum Read {
    /// A full signature: a return type or a constructor, destructor or
    /// conversion ([`parse_signature`]).
    Full(Signature),
    /// A trace: a qualified name and `()` ([`trace_name`]).
    Trace(String),
    /// A bare qualified name, a `__FUNCTION__` spelling ([`qualified_word`]),
    /// with its text.
    Bare(String),
    /// None of these.
    Nothing,
}

/// The strings that name a function without declaring it.
#[derive(Default)]
struct Traces {
    /// Each trace name ([`trace_name`]) with the functions referencing it.
    calls: BTreeMap<String, BTreeSet<u64>>,
    /// Each function's bare qualified-name strings, by address.
    bare: BTreeMap<u64, BTreeSet<u64>>,
    /// The text of each bare qualified-name string, by address.
    texts: BTreeMap<u64, String>,
}

/// Fills the name and signature of every unnamed function that references a
/// signature string only it can be, and marks those names inferred.
///
/// # Arguments
///
/// * `program` - The image the strings are read from.
/// * `analysis` - Functions and cross-references; names are written in place.
pub(crate) fn infer(program: &Program, analysis: &mut Analysis) {
    let (found, traces) = signatures(program, analysis);
    let mut named: BTreeSet<u64> = analysis
        .functions
        .iter()
        .filter(|f| f.name.is_some())
        .map(|f| f.entry)
        .collect();
    let mut assigned = vec![false; found.referrers.len()];
    let (mut chosen, _) = choose_own(&found, &mut named, &mut assigned);
    chosen.extend(choose_helpers(program, analysis, &found, &named, &assigned));
    let traced = choose_traces(&found, &traces, &named);
    let mut seen: BTreeMap<String, u32> = BTreeMap::new();
    for f in &mut analysis.functions {
        let sig = chosen.get(&f.entry).and_then(|&s| found.sigs.get(s));
        let Some(name) = sig
            .map(|s| &s.name)
            .or_else(|| traced.get(&f.entry).copied())
        else {
            continue;
        };
        let n = seen.entry(name.clone()).or_insert(0);
        *n += 1;
        f.name = Some(if *n == 1 {
            name.clone()
        } else {
            format!("{name}_{n}")
        });
        f.name_inferred = true;
        f.name_source = sig.map_or(NameSource::Trace, |_| NameSource::Signature);
        f.signature = sig.cloned();
    }
}

/// Names each function by the one trace string it references
/// ([`trace_name`]) when the evidence outside the text holds.
///
/// Text alone cannot tell `"CVdsVolumePlex::QueryExtents()"`, a trace of
/// the method's own name, from `"thread_util::IsMainThread()"`, an assert's
/// condition. So the function must reference no accepted full signature
/// (one always wins), no other function may reference the trace (a
/// condition is shared by every site that checks it, a trace sits in its
/// one method), and the function must reference no second trace and no bare
/// qualified name (a `__FUNCTION__` spelling, `ns::Cls::Run`) that differs from it:
/// that one is the function's own name and the trace a call it checks. A
/// bare name that agrees supports it. The name is a weaker claim
/// ([`NameSource::Trace`]) and gives no types.
///
/// # Arguments
///
/// * `found` - The full signatures and the functions referencing them.
/// * `traces` - The trace and bare qualified-name strings.
/// * `named` - The functions already holding a name.
///
/// # Returns
///
/// Each named function's entry and its name.
fn choose_traces<'t>(
    found: &Found,
    traces: &'t Traces,
    named: &BTreeSet<u64>,
) -> BTreeMap<u64, &'t String> {
    let mut per: BTreeMap<u64, Vec<&String>> = BTreeMap::new();
    for (name, refs) in &traces.calls {
        for &r in refs {
            per.entry(r).or_default().push(name);
        }
    }
    per.into_iter()
        .filter_map(|(entry, names)| {
            let [name] = names.as_slice() else {
                return None;
            };
            let alone = traces.calls.get(*name).is_some_and(|r| r.len() == 1);
            let disputed = traces.bare.get(&entry).is_some_and(|b| {
                b.iter()
                    .any(|at| traces.texts.get(at).is_some_and(|t| t != *name))
            });
            (alone
                && !disputed
                && !named.contains(&entry)
                && !found.candidates.contains_key(&entry))
            .then_some((entry, *name))
        })
        .collect()
}

/// Reads the signature and trace strings the code references, each once,
/// and records the setters among the signatures in
/// `analysis.classes.setters`.
///
/// # Arguments
///
/// * `program` - The image the strings are read from.
/// * `analysis` - Cross-references; the setters are written in place.
///
/// # Returns
///
/// The full signatures and the trace strings.
fn signatures(program: &Program, analysis: &mut Analysis) -> (Found, Traces) {
    let mut found = Found {
        sigs: Vec::new(),
        candidates: BTreeMap::new(),
        referrers: Vec::new(),
    };
    let mut ids: BTreeMap<String, usize> = BTreeMap::new();
    let targets: Vec<u64> = analysis
        .xrefs
        .keys()
        .copied()
        .filter(|&t| in_data(program, t))
        .collect();
    let parsed = super::striped(&targets, |&target| {
        cstr_at(program, target, SIG_MIN, SIG_MAX).map_or(Read::Nothing, |(_, text)| {
            if let Some(sig) = parse_signature(&text) {
                Read::Full(sig)
            } else if let Some(name) = trace_name(&text) {
                Read::Trace(name)
            } else if qualified_word(&text) {
                Read::Bare(text)
            } else {
                Read::Nothing
            }
        })
    });
    let mut setters: BTreeMap<String, Vec<(u64, String)>> = BTreeMap::new();
    let mut traces = Traces::default();
    for (target, read) in targets.iter().zip(parsed) {
        let Some(sites) = analysis.xrefs.get(target) else {
            continue;
        };
        let sig = match read {
            Read::Full(sig) => sig,
            Read::Trace(name) => {
                let refs = traces.calls.entry(name).or_default();
                refs.extend(data_referrers(sites));
                continue;
            }
            Read::Bare(text) => {
                for from in data_referrers(sites) {
                    traces.bare.entry(from).or_default().insert(*target);
                }
                traces.texts.insert(*target, text);
                continue;
            }
            Read::Nothing => continue,
        };
        if let Some(class) = class_of(&sig.name)
            && let Some(member) = setter_member(&sig.name)
        {
            setters
                .entry(class.to_owned())
                .or_default()
                .push((*target, member.to_owned()));
        }
        let n = *ids.entry(sig.name.clone()).or_insert_with(|| {
            found.referrers.push(BTreeSet::new());
            found.referrers.len() - 1
        });
        let s = found.sigs.len();
        for from in data_referrers(sites) {
            found
                .candidates
                .entry(from)
                .or_default()
                .entry(n)
                .or_insert(s);
            if let Some(refs) = found.referrers.get_mut(n) {
                refs.insert(from);
            }
        }
        found.sigs.push(sig);
    }
    analysis.classes.setters = setters;
    (found, traces)
}

/// Reads a trace string: a qualified name and empty parentheses, no return
/// type (`CVdsVolumePlex::QueryExtents()`), which [`parse_signature`]
/// refuses as a call.
///
/// # Arguments
///
/// * `text` - The string as read.
///
/// # Returns
///
/// The name, or `None` when the text is not one qualified name followed
/// by `()`.
fn trace_name(text: &str) -> Option<String> {
    let name = text.strip_suffix("()")?;
    qualified_word(name).then(|| name.to_owned())
}

/// Tells whether a text is one qualified name and nothing else
/// (`ns::Cls::Run`, `Box<int, T *>::Get`): no parentheses, no space outside
/// template arguments, at most [`NAME_MAX`] bytes.
///
/// # Arguments
///
/// * `name` - The text.
fn qualified_word(name: &str) -> bool {
    last_token(name).len() == name.len()
        && name.len() <= NAME_MAX
        && class_of(name).is_some()
        && name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        && name.chars().all(|c| ident_char(c) || ":<>,*& ".contains(c))
}

/// Names each function by the one candidate only it still references.
///
/// A candidate is a function's own once every other function referencing
/// its name has a name. Functions are decided in rounds, each against the
/// names the rounds before it gave, so the answer does not hang on the
/// order they are visited in: one with a single own candidate takes it,
/// and one with two never takes any, since naming more functions only
/// adds own candidates. A function is visited again only when a name it
/// references is left with it as its one unnamed referrer, so the work is
/// linear in the references, and [`FUEL_PER_REFERENCE`] holds it there.
///
/// # Arguments
///
/// * `found` - The candidates and referrers.
/// * `named` - The functions holding a name; those named here are added.
/// * `assigned` - Whether each name is taken; those taken here are set.
///
/// # Returns
///
/// The index in `found.sigs` of each newly named function's signature,
/// and the steps spent.
fn choose_own(
    found: &Found,
    named: &mut BTreeSet<u64>,
    assigned: &mut [bool],
) -> (BTreeMap<u64, usize>, usize) {
    let mut unnamed: Vec<usize> = found
        .referrers
        .iter()
        .map(|r| r.iter().filter(|f| !named.contains(f)).count())
        .collect();
    let references: usize = found.referrers.iter().map(BTreeSet::len).sum();
    let budget = references.saturating_mul(FUEL_PER_REFERENCE);
    let mut fuel = budget;
    let mut chosen = BTreeMap::new();
    let mut undecidable = BTreeSet::new();
    let mut queue: BTreeSet<u64> = found
        .candidates
        .keys()
        .copied()
        .filter(|e| !named.contains(e))
        .collect();
    while !queue.is_empty() {
        let mut picks = Vec::new();
        for (&entry, cands) in queue
            .iter()
            .filter_map(|e| found.candidates.get_key_value(e))
        {
            let Some(left) = fuel.checked_sub(cands.len()) else {
                return (chosen, budget);
            };
            fuel = left;
            let mut own = cands
                .iter()
                .filter(|&(&n, _)| assigned.get(n) == Some(&false) && unnamed.get(n) == Some(&1));
            match (own.next(), own.next()) {
                (Some((&n, &s)), None) => picks.push((entry, n, s)),
                (Some(_), Some(_)) => {
                    undecidable.insert(entry);
                }
                (None, _) => {}
            }
        }
        for &(entry, n, s) in &picks {
            chosen.insert(entry, s);
            named.insert(entry);
            if let Some(taken) = assigned.get_mut(n) {
                *taken = true;
            }
        }
        let mut next = BTreeSet::new();
        for (entry, _, _) in picks {
            for &m in found
                .candidates
                .get(&entry)
                .into_iter()
                .flat_map(BTreeMap::keys)
            {
                let (Some(count), Some(refs)) = (unnamed.get_mut(m), found.referrers.get(m)) else {
                    continue;
                };
                *count = count.saturating_sub(1);
                if *count == 1 {
                    let Some(left) = fuel.checked_sub(refs.len()) else {
                        return (chosen, budget);
                    };
                    fuel = left;
                    next.extend(refs.iter().find(|f| !named.contains(f)));
                }
            }
        }
        queue = next.difference(&undecidable).copied().collect();
    }
    (chosen, budget.saturating_sub(fuel))
}

/// Names the helper behind each signature several unnamed functions still
/// reference.
///
/// It is the one of them that mentions no other signature and reads
/// exactly the argument registers the signature declares (`this`
/// included).
///
/// Such a helper references its own name only, so naming it changes no
/// other name's referrers, and one pass decides them all.
///
/// # Arguments
///
/// * `program` - Bytes, format and bitness.
/// * `analysis` - The functions.
/// * `found` - The candidates and referrers.
/// * `named` - The functions holding a name.
/// * `assigned` - Whether each name is taken.
///
/// # Returns
///
/// Each helper's entry and the index in `found.sigs` of its signature.
fn choose_helpers(
    program: &Program,
    analysis: &Analysis,
    found: &Found,
    named: &BTreeSet<u64>,
    assigned: &[bool],
) -> Vec<(u64, usize)> {
    let mut picks = Vec::new();
    for (n, refs) in found.referrers.iter().enumerate() {
        if assigned.get(n) != Some(&false) {
            continue;
        }
        let unnamed: Vec<u64> = refs
            .iter()
            .copied()
            .filter(|r| !named.contains(r))
            .collect();
        if unnamed.len() < 2 {
            continue;
        }
        let Some((s, sig)) = unnamed.iter().find_map(|r| {
            let s = *found.candidates.get(r)?.get(&n)?;
            Some((s, found.sigs.get(s)?))
        }) else {
            continue;
        };
        let expected = sig.params.len() + usize::from(sig.by_pointer);
        let fits = unnamed.iter().copied().filter(|r| {
            found.candidates.get(r).is_some_and(|c| c.len() == 1)
                && analysis.function(*r).is_some_and(|f| {
                    let k = args_read(program, f);
                    k == expected || k == expected + 1
                })
        });
        if let Some(only) = single(fits) {
            picks.push((only, s));
        }
    }
    picks
}

/// The opening of a command dispatcher's wrong-type message, up to the type.
///
/// The whole text reads `Command handler for type 'X' called with command of
/// wrong type ...`, and the function carrying it is X's handler.
const HANDLER_PREFIX: &str = "Command handler for type '";

/// Derives a handler's name from the type check it prints on a mismatch.
///
/// `Command handler for type 'Cmd::Exit' called with ...`
/// gives `HandleExit`: the type's last segment behind `Handle`,
/// the spelling the source gives the handlers it does name.
///
/// # Arguments
///
/// * `text` - The string literal.
///
/// # Returns
///
/// The name, or `None` when the text is not a handler's type check.
fn handler_name(text: &str) -> Option<String> {
    let rest = text.strip_prefix(HANDLER_PREFIX)?;
    let ty = rest.split('\'').next()?;
    let short = ty.rsplit("::").next()?;
    (!short.is_empty()
        && short
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || c == b'_'))
    .then(|| format!("Handle{short}"))
}

/// Names the functions that carry a handler's type check after the type they
/// handle.
///
/// A dispatcher's handlers are registered from tables, not named by a
/// signature literal, so [`infer`] leaves them as `sub_`; each begins by
/// checking that the command it was handed is the type it handles, and the
/// message it prints on a mismatch names that type. A second unnamed carrier
/// of the same message is numbered, in address order.
///
/// # Arguments
///
/// * `program` - The image the strings are read from.
/// * `analysis` - Functions and cross-references; names are written in place.
pub(crate) fn infer_handlers(program: &Program, analysis: &mut Analysis) {
    let mut chosen: BTreeMap<u64, String> = BTreeMap::new();
    for (&target, sites) in &analysis.xrefs {
        if !in_data(program, target) {
            continue;
        }
        let Some(name) =
            cstr_at(program, target, SIG_MIN, SIG_MAX).and_then(|(_, text)| handler_name(&text))
        else {
            continue;
        };
        for from in data_referrers(sites) {
            if analysis.function(from).is_some_and(|f| f.name.is_none()) {
                chosen.entry(from).or_insert_with(|| name.clone());
            }
        }
    }
    let mut seen: BTreeMap<String, u32> = BTreeMap::new();
    for f in &mut analysis.functions {
        let Some(name) = chosen.get(&f.entry) else {
            continue;
        };
        let n = seen.entry(name.clone()).or_insert(0);
        *n += 1;
        f.name = Some(if *n == 1 {
            name.clone()
        } else {
            format!("{name}_{n}")
        });
        f.name_inferred = true;
        f.name_source = NameSource::Handler;
    }
}

/// The member a setter's qualified name sets: `Type::SetField` sets `Field`.
///
/// # Arguments
///
/// * `name` - The qualified method name.
///
/// # Returns
///
/// The member, or `None` when the method is not a `SetX` with a capitalized
/// `X`.
pub(crate) fn setter_member(name: &str) -> Option<&str> {
    let method = name.rsplit("::").next()?;
    let member = method.strip_prefix("Set")?;
    (member.chars().next().is_some_and(char::is_uppercase)
        && member
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_'))
    .then_some(member)
}

/// Counts the argument registers a function reads before writing them:
/// one past the highest convention position read.
///
/// # Arguments
///
/// * `program` - Bytes, format and bitness.
/// * `f` - The function; its blocks are decoded in address order.
fn args_read(program: &Program, f: &Function) -> usize {
    const MS: [Register; 4] = [Register::RCX, Register::RDX, Register::R8, Register::R9];
    const SYSV: [Register; 6] = [
        Register::RDI,
        Register::RSI,
        Register::RDX,
        Register::RCX,
        Register::R8,
        Register::R9,
    ];
    let Some(bitness) = program.arch.bitness() else {
        return 0;
    };
    if bitness != 64 {
        return 0;
    }
    let args: &[Register] = match program.format {
        BinaryFormat::Elf | BinaryFormat::MachO => &SYSV,
        BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => &MS,
    };
    let mut factory = InstructionInfoFactory::new();
    let mut written: BTreeSet<Register> = BTreeSet::new();
    let mut read = 0usize;
    for instr in f
        .blocks
        .iter()
        .flat_map(|b| decode_block(program, bitness, b))
    {
        let mut writes: Vec<Register> = Vec::new();
        for ur in factory.info(&instr).used_registers() {
            let r = ur.register().full_register();
            let Some(pos) = args.iter().position(|a| *a == r) else {
                continue;
            };
            if matches!(
                ur.access(),
                OpAccess::Read | OpAccess::CondRead | OpAccess::ReadWrite | OpAccess::ReadCondWrite
            ) && !written.contains(&r)
            {
                read = read.max(pos + 1);
            }
            if matches!(
                ur.access(),
                OpAccess::Write
                    | OpAccess::ReadWrite
                    | OpAccess::CondWrite
                    | OpAccess::ReadCondWrite
            ) {
                writes.push(r);
            }
        }
        written.extend(writes);
    }
    read
}

/// Tells whether `va` lies in readable, non-executable memory.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The address.
pub(super) fn in_data(program: &Program, va: u64) -> bool {
    program
        .section_at(va)
        .is_some_and(|s| s.readable && !s.executable)
}

/// Parses a signature string into its return type, name and parameters.
///
/// MSVC's `__FUNCSIG__` (`class A *__cdecl A::Instance(void)`) names the
/// function right after its calling convention and puts the return type
/// before it; GCC's `__PRETTY_FUNCTION__` (`void Foo::bar(int) const`) names
/// it in the last word before the parameter list, template arguments
/// included. Elaborated-type keywords are dropped everywhere
/// (`Util::Array<Util::String>::Copy`, `const Util::String &`), `(void)` is
/// no parameter, and a trailing `const` is kept as a flag. A head without a
/// convention or a `::` must start with a type word and carry a type-like
/// parameter list, so `Failed to open file (%s)` never becomes a name. A
/// class returned by value (elaborated `class`/`struct`/`union`, or a
/// qualified or template type in the convention-less form) is returned
/// through a hidden pointer argument, which `by_pointer` records.
///
/// # Arguments
///
/// * `text` - The string as read (a capped read ending in `...` is rejected).
///   An operator function's symbol (`operator ->`, `operator []`,
///   `operator >=`, `operator ()`) is no template or parameter delimiter.
///
/// # Returns
///
/// The signature, or `None` when the text is not a function signature or
/// names one by more than [`NAME_MAX`] bytes.
pub(crate) fn parse_signature(text: &str) -> Option<Signature> {
    read_signature(text).filter(|sig| sig.name.len() <= NAME_MAX)
}

/// Parses a signature string as [`parse_signature`] does, a name of any
/// length included.
///
/// # Arguments
///
/// * `text` - The string as read.
///
/// # Returns
///
/// The signature, or `None` when the text is not a function signature.
fn read_signature(text: &str) -> Option<Signature> {
    if text.ends_with("...") {
        return None;
    }
    let (head, params, after) = split_signature(text)?;
    if !(after.is_empty() || after == "const" || after == "const noexcept" || after == "noexcept") {
        return None;
    }
    let conv = CONVENTIONS.iter().find_map(|k| head.rsplit_once(k));
    let (ret_raw, raw) = match conv {
        Some((pre, rest)) => (pre, rest.trim()),
        None => {
            let head = head.trim_end();
            let name = last_token(head).trim_start_matches(['*', '&']);
            (head.get(..head.len() - name.len()).unwrap_or(""), name)
        }
    };
    let name = strip_keywords(raw);
    if name.is_empty()
        || !name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_' || c == '<')
    {
        return None;
    }
    if conv.is_none() && (!declares(head, &name, params, |_| false) || expression(ret_raw, &name)) {
        return None;
    }
    let ret_core = ret_raw.trim().trim_start_matches("const ").trim_start();
    let elaborated = ["class ", "struct ", "union "]
        .iter()
        .any(|k| ret_core.starts_with(k));
    let ret = strip_keywords(ret_raw.trim_end());
    let ret = if ret.is_empty() {
        conversion_type(&name).map_or(ret, str::to_owned)
    } else {
        ret
    };
    if hand_written(&ret, &[params]) {
        return None;
    }
    let by_pointer = !ret.is_empty()
        && !ret.ends_with('*')
        && !ret.ends_with('&')
        && (elaborated
            || (conv.is_none()
                && !ret_core.starts_with("enum ")
                && (ret.contains("::") || ret.contains('<'))));
    let params: Vec<String> = split_params(params)
        .into_iter()
        .map(strip_keywords)
        .filter(|p| !p.is_empty() && p != "void")
        .collect();
    Some(Signature {
        ret: if ret.is_empty() {
            "void".to_owned()
        } else {
            ret
        },
        name,
        params,
        is_const: after.starts_with("const"),
        by_pointer,
    })
}

/// Tells whether a signature-shaped text is one no compiler writes: a log
/// line spelled like a declaration.
///
/// Its return type is prose ([`prose`]: `Error in Net::open()`), or ends
/// in `:`, a sentence's label (`Retrying: Net::open(...)`), or one of its
/// parts holds a printf conversion (`%s`, `%zu`, `%-8d`), which no
/// declaration and no template binding spells.
///
/// # Arguments
///
/// * `ret` - The return type, elaborated-type keywords dropped.
/// * `parts` - The parameter list, and a template's bindings.
fn hand_written(ret: &str, parts: &[&str]) -> bool {
    let conversion = |text: &&str| {
        text.match_indices('%').any(|(i, _)| {
            let spec = text
                .get(i + 1..)
                .unwrap_or("")
                .trim_start_matches(|c: char| "-+ #0123456789.*hlLqjzt".contains(c));
            spec.starts_with(|c: char| "diouxXfFeEgGaAcspn".contains(c))
        })
    };
    prose(ret) || ret.trim_end().ends_with(':') || parts.iter().any(conversion)
}

/// Tells whether a head with no calling convention declares a function
/// rather than reads as prose (`Failed to open file (%s)`).
///
/// A qualified name declares one. An unqualified name needs two to four
/// words before the parameter list, the first a type word (`int main(int,
/// char **)`), and a parameter list of type characters only.
///
/// # Arguments
///
/// * `head` - The text before the parameter list.
/// * `name` - The name read from it.
/// * `params` - The text inside the parameter list.
/// * `bound` - Whether a word names a type of its own: a template's bound
///   parameter (`T Twice(T) [with T = int]`).
fn declares(head: &str, name: &str, params: &str, bound: impl Fn(&str) -> bool) -> bool {
    if name.contains("::") {
        return true;
    }
    let words: Vec<&str> = head.split_whitespace().collect();
    let typed = words
        .first()
        .is_some_and(|w| TYPE_WORDS.contains(w) || bound(w));
    let type_like = params
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || " _*&,:<>[]".contains(c));
    (2..=4).contains(&words.len()) && typed && type_like
}

/// Tells whether a convention-less head reads as an expression around a
/// call, an assert's condition text, rather than a declaration.
///
/// GCC and Clang write a return type before every name but a
/// constructor's, a destructor's and a conversion operator's, so
/// `thread_util::IsMainThread()` is a call; and a return type spells no
/// operator, so `ok && ns::Ready()` and `n == ns::Count()` are
/// comparisons. A reference or pointer return keeps its `&` or `*` beside
/// the type or the name (`Foo &ns::Get()`, `Foo&& ns::Take()`), never with a
/// space on both sides.
///
/// # Arguments
///
/// * `ret` - The text before the name, as the head spells it.
/// * `name` - The name, elaborated-type keywords dropped.
fn expression(ret: &str, name: &str) -> bool {
    if ret.trim().is_empty() {
        let special = class_of(name).is_some_and(|class| {
            let method = name.get(class.len() + 2..).unwrap_or("");
            let stem = |s: &str| {
                let s = s.split('<').next().unwrap_or(s);
                s.rsplit("::").next().unwrap_or(s).to_owned()
            };
            method.starts_with('~') || stem(method) == stem(class)
        });
        return !special && conversion_type(name).is_none();
    }
    ret.contains(['=', '!', '|', '?', '+', '"', '\''])
        || [" && ", " & ", " * "].iter().any(|op| ret.contains(op))
}

/// Splits a signature at its parameter list.
///
/// The list opens at the first `(` outside template arguments, an operator
/// function's symbol skipped, and closes at the first `)` after it.
///
/// # Arguments
///
/// * `text` - The signature.
///
/// # Returns
///
/// The text before the list, the text inside it and the trimmed text after
/// it, or `None` when there is no list.
fn split_signature(text: &str) -> Option<(&str, &str, &str)> {
    let symbol_end = operator_symbol_end(text);
    let mut depth = 0i32;
    let mut paren = None;
    let mut prev = ' ';
    for (i, c) in text.char_indices() {
        if symbol_end.is_some_and(|end| i < end) {
            prev = c;
            continue;
        }
        match c {
            '<' => depth += 1,
            '>' if prev != '-' => depth -= 1,
            '(' if depth == 0 => {
                paren = Some(i);
                break;
            }
            _ => {}
        }
        prev = c;
    }
    let paren = paren?;
    let head = text.get(..paren)?;
    let tail = text.get(paren..)?;
    let close = tail.find(')')?;
    let params = tail.get(1..close)?;
    let after = tail.get(close + 1..)?.trim();
    Some((head, params, after))
}

/// Tells whether a string is a function signature, one [`parse_signature`]
/// takes or not.
///
/// A name longer than [`NAME_MAX`] is no bar, and neither is the
/// `[with T = int; U = float]` GCC appends to the signature of a
/// template's instantiation, Clang's `[T = int, U = float]`, when the text
/// before it reads as a signature.
///
/// A return type spelling two plain words side by side, neither a
/// keyword (`Fatal error in Net::Session::Open(...)`), is prose: C++
/// spells a type by one name among keywords.
///
/// # Arguments
///
/// * `text` - The string as read.
pub(crate) fn is_signature(text: &str) -> bool {
    if read_signature(text).is_some() {
        return true;
    }
    let Some((body, open)) = bindings_open(text) else {
        return false;
    };
    let inner = body.get(open + 1..).unwrap_or("");
    inner.strip_prefix("with ").unwrap_or(inner).contains(" = ")
        && body
            .get(..open)
            .is_some_and(|head| read_signature(head.trim_end()).is_some())
}

/// Finds the `[` that opens the bindings a template signature ends with.
///
/// # Arguments
///
/// * `text` - The string as read.
///
/// # Returns
///
/// The text without its final `]` and the index in it of the `[` that
/// matches that `]`, or `None` when the text does not end in a bracketed
/// list.
fn bindings_open(text: &str) -> Option<(&str, usize)> {
    let body = text.strip_suffix(']')?;
    let mut depth = 1usize;
    let open = body.bytes().rposition(|b| {
        match b {
            b']' => depth += 1,
            b'[' => depth = depth.saturating_sub(1),
            _ => {}
        }
        depth == 0
    })?;
    Some((body, open))
}

/// Tells whether a return type spells two plain words side by side,
/// neither a keyword: prose, since C++ spells a type by one name among
/// keywords.
///
/// # Arguments
///
/// * `ret` - The return type as a signature spells it.
fn prose(ret: &str) -> bool {
    let plain = |w: &str| {
        w.chars().all(ident_char)
            && !w.starts_with("__")
            && !TYPE_WORDS.contains(&w)
            && !SPECIFIERS.contains(&w)
    };
    let words = ret.split_whitespace();
    words
        .clone()
        .zip(words.skip(1))
        .any(|(a, b)| plain(a) && plain(b))
}

/// The type a conversion operator converts to: `Base::NetStreamBase *` for
/// `Core::Ptr<Base::NetStreamBase>::operator Base::NetStreamBase *`.
///
/// `operator new` and `operator delete` allocate and free rather than
/// convert, and a symbol operator (`operator ->`) converts nothing.
///
/// # Arguments
///
/// * `name` - A function's qualified name.
fn conversion_type(name: &str) -> Option<&str> {
    let at = name.find("::operator ").map_or_else(
        || name.strip_prefix("operator ").map(|_| 0),
        |i| Some(i + 2),
    )?;
    let ty = name.get(at + "operator ".len()..)?.trim();
    let named = ty.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_' || c == ':');
    let allocates = ["new", "delete", "new[]", "delete[]"].contains(&ty);
    (named && !allocates).then_some(ty)
}

/// Splits a parameter list at the commas outside template and function-type
/// brackets.
///
/// # Arguments
///
/// * `params` - The text between the outer parentheses.
fn split_params(params: &str) -> Vec<&str> {
    split_outside(params, ',')
}

/// Splits a list at each `sep` outside template and function-type
/// brackets, trimming each part.
///
/// # Arguments
///
/// * `params` - The list.
/// * `sep` - The separator.
fn split_outside(params: &str, sep: char) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in params.char_indices() {
        match c {
            '<' | '(' => depth += 1,
            '>' | ')' => depth -= 1,
            c if c == sep && depth == 0 => {
                out.push(params.get(start..i).unwrap_or("").trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(params.get(start..).unwrap_or("").trim());
    out
}

/// Finds where the symbol of an operator function's name ends.
///
/// MSVC spells `operator ->`, `operator []`, `operator ()`, `operator >=`
/// and the like with a space before the symbol, whose brackets are neither
/// template nor parameter delimiters.
///
/// # Arguments
///
/// * `text` - A signature string.
///
/// # Returns
///
/// The byte index just past the symbol, or `None` for a conversion
/// operator (`operator Foo *`), a named one (`operator new`) or no operator.
fn operator_symbol_end(text: &str) -> Option<usize> {
    let at = text.find("operator ")? + "operator ".len();
    let rest = text.get(at..)?;
    let first = rest.chars().next()?;
    if first.is_alphanumeric() || first == '_' || first == ':' {
        return None;
    }
    if rest.starts_with("()") {
        return Some(at + 2);
    }
    Some(at + rest.find('(').unwrap_or(rest.len()))
}

/// Returns the last space-separated token of `head`, keeping spaces inside
/// template arguments and after `operator`, and the qualifier before it.
///
/// # Arguments
///
/// * `head` - The text before the parameter list.
fn last_token(head: &str) -> &str {
    let trimmed = head.trim_end();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in trimmed.char_indices().rev() {
        match c {
            '>' if trimmed.as_bytes().get(i.wrapping_sub(1)) != Some(&b'-') => depth += 1,
            '<' => depth -= 1,
            ' ' if depth == 0 => {
                start = i + 1;
                break;
            }
            _ => {}
        }
    }
    let token = trimmed.get(start..).unwrap_or(trimmed);
    let before = trimmed.get(..start).unwrap_or("").trim_end();
    if before.ends_with("operator") {
        let op_start = before.len() - "operator".len();
        let scope = trimmed.get(..op_start).unwrap_or("");
        let start = if scope.ends_with("::") {
            op_start - last_token(scope).len()
        } else {
            op_start
        };
        return trimmed.get(start..).unwrap_or(token);
    }
    token
}

/// Removes elaborated-type keywords and collapses whitespace runs.
///
/// A keyword is removed only as a whole word, at the start or after a byte
/// that is no identifier byte (`$` is one, as MSVC, GCC and Clang take it),
/// so `my_class *` and `my$class *` keep their names.
///
/// # Arguments
///
/// * `name` - The raw type or qualified name.
fn strip_keywords(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut rest = name;
    while let Some(c) = rest.chars().next() {
        let word_start = !out.ends_with(|p: char| ident_char(p) || p == '$');
        if let Some(after) = KEYWORDS
            .iter()
            .find_map(|k| rest.strip_prefix(k))
            .filter(|_| word_start)
        {
            rest = after;
            continue;
        }
        out.push(c);
        rest = rest.get(c.len_utf8()..).unwrap_or("");
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::{
        BTreeMap, BTreeSet, Found, choose_own, handler_name, parse_signature, setter_member,
    };

    /// A handler's type check names the handler; prose and other asserts do not.
    ///
    /// # Panics
    ///
    /// When a name disagrees with its expectation.
    #[test]
    fn handler_names_come_from_the_type_check() {
        assert_eq!(
            handler_name(
                "Command handler for type 'Cmd::Exit' called with command of \
                 wrong type. Command is of type '%s' but 'Cmd::Exit' is expected."
            )
            .as_deref(),
            Some("HandleExit")
        );
        assert_eq!(
            handler_name("Command handler for type 'Mode::Flag' called").as_deref(),
            Some("HandleFlag")
        );
        assert!(handler_name("Command handler for type '' called").is_none());
        assert!(handler_name("no config for map '%s' found").is_none());
        assert_eq!(setter_member("Type::SetField"), Some("Field"));
        assert_eq!(setter_member("Util::String::Set"), None);
        assert_eq!(setter_member("Settings::Load"), None);
    }

    /// MSVC, GCC and operator forms yield the qualified name, return type and
    /// parameters; prose does not.
    ///
    /// # Panics
    ///
    /// When a parse disagrees with its expectation.
    #[test]
    fn signatures_parse_and_prose_does_not() {
        let s = parse_signature("class UI::Manager *__cdecl UI::Manager::Instance(void)")
            .expect("msvc signature");
        assert_eq!(s.name, "UI::Manager::Instance");
        assert_eq!(s.ret, "UI::Manager *");
        assert!(s.params.is_empty() && !s.is_const && !s.by_pointer);
        let s = parse_signature("class Util::String __cdecl Util::String::AsUpper(void) const")
            .expect("by-value class return");
        assert!(s.by_pointer && s.is_const);
        let s = parse_signature("enum Foo::Kind __cdecl Foo::KindOf(int)").expect("enum return");
        assert!(!s.by_pointer);
        let s = parse_signature("Util::String Foo::Name() const").expect("gcc class return");
        assert!(s.by_pointer);
        let s = parse_signature(
            "void __cdecl Util::Array<class Util::String>::operator =(const class Util::Array<class Util::String> &)",
        )
        .expect("operator signature");
        assert_eq!(s.name, "Util::Array<Util::String>::operator =");
        assert_eq!(s.params, vec!["const Util::Array<Util::String> &"]);
        let s = parse_signature(
            "class UI::TextEntry *__cdecl Core::Ptr<class UI::TextEntry>::operator ->(void) const",
        )
        .expect("arrow operator");
        assert_eq!(s.name, "Core::Ptr<UI::TextEntry>::operator ->");
        assert_eq!(s.ret, "UI::TextEntry *");
        assert!(s.params.is_empty() && s.is_const);
        let s = parse_signature(
            "bool __cdecl Util::String::operator >=(const class Util::String &) const",
        )
        .expect("greater-equal operator");
        assert_eq!(s.name, "Util::String::operator >=");
        assert_eq!(s.params, vec!["const Util::String &"]);
        let s = parse_signature(
            "__cdecl Core::Ptr<class Base::NetStreamBase>::operator class Base::NetStreamBase *(void) const",
        )
        .expect("conversion operator");
        assert_eq!(
            s.name,
            "Core::Ptr<Base::NetStreamBase>::operator Base::NetStreamBase *"
        );
        assert_eq!(s.ret, "Base::NetStreamBase *");
        assert_eq!(
            super::class_of(&s.name),
            Some("Core::Ptr<Base::NetStreamBase>")
        );
        let s = parse_signature("int __cdecl Fn::operator ()(int) const").expect("call operator");
        assert_eq!(s.name, "Fn::operator ()");
        assert_eq!(s.params, vec!["int"]);
        let s = parse_signature("bool Foo::bar(int, char *) const").expect("gcc signature");
        assert_eq!((s.name.as_str(), s.ret.as_str()), ("Foo::bar", "bool"));
        assert_eq!(s.params, vec!["int", "char *"]);
        assert!(s.is_const);
        let s = parse_signature("int main(int, char **)").expect("main");
        assert_eq!(s.name, "main");
        assert!(parse_signature("Failed to open file (%s)").is_none());
        assert!(parse_signature("Error in function main(int)").is_none());
        assert!(parse_signature("call foo() now").is_none());
    }

    /// An elaborated-type keyword is dropped only as a whole word, never
    /// from the tail of an identifier that ends in one.
    ///
    /// # Panics
    ///
    /// When a name, return type or parameter loses part of an identifier.
    #[test]
    fn keywords_drop_only_as_whole_words() {
        let s = parse_signature(
            "class UI::Subclass *__cdecl Box<class my_class *>::Get(const struct my_struct &)",
        )
        .expect("msvc signature");
        assert_eq!(s.name, "Box<my_class *>::Get");
        assert_eq!(s.ret, "UI::Subclass *");
        assert_eq!(s.params, vec!["const my_struct &"]);
        let s = parse_signature("union my_union __cdecl Kind::Of(enum my_enum, int)")
            .expect("by-value union return");
        assert_eq!(s.ret, "my_union");
        assert_eq!(s.params, vec!["my_enum", "int"]);
        let s =
            parse_signature("void __cdecl Kind::Set(enum my_enum *, int)").expect("enum pointer");
        assert_eq!(s.params, vec!["my_enum *", "int"]);
        let s = parse_signature(
            "void __cdecl Text::Put(class std::basic_string<char,struct std::char_traits<char> >)",
        )
        .expect("keyword after a comma");
        assert_eq!(
            s.params,
            vec!["std::basic_string<char,std::char_traits<char> >"]
        );
        let s = parse_signature("void __cdecl Kind::Use(enum class Foo)").expect("enum class");
        assert_eq!(s.params, vec!["Foo"]);
        let s = parse_signature("void __cdecl Kind::Take(class my$class *)").expect("dollar");
        assert_eq!(s.params, vec!["my$class *"]);
    }

    /// An operator keeps its class however it is spaced, and a log line
    /// spelled like a qualified declaration names nothing.
    ///
    /// # Panics
    ///
    /// When an operator loses its class or a log line parses.
    #[test]
    fn operators_keep_their_class_and_log_lines_name_nothing() {
        let s = parse_signature("Foo::operator bool() const").expect("conversion operator");
        assert_eq!(
            (s.name.as_str(), s.ret.as_str()),
            ("Foo::operator bool", "bool")
        );
        let s = parse_signature("static void* Foo::operator new(std::size_t)")
            .expect("allocation operator");
        assert_eq!(s.name, "Foo::operator new");
        assert_eq!(s.params, vec!["std::size_t"]);
        for text in [
            "Retrying: Net::open(%s)",
            "Retrying: Net::open()",
            "Error in Net::open()",
            "Calling Net::Connect(%d)",
            "Net::Send(%zu bytes)",
        ] {
            assert!(parse_signature(text).is_none(), "{text}");
        }
    }

    /// Clang's pointer and reference returns parse, a constructor,
    /// destructor or conversion needs no return type, and assert condition
    /// text, a call or an operator around one, names nothing.
    ///
    /// # Panics
    ///
    /// When a parse disagrees with its expectation.
    #[test]
    fn condition_text_is_no_signature() {
        let s =
            parse_signature("audio::SourceArray &audio::GetDefaultSourceArray(audio::SourceType)")
                .expect("clang reference return");
        assert_eq!(s.name, "audio::GetDefaultSourceArray");
        assert_eq!(s.ret, "audio::SourceArray &");
        assert!(!s.by_pointer);
        let s = parse_signature("const char *Foo::Name() const").expect("clang pointer return");
        assert_eq!(
            (s.name.as_str(), s.ret.as_str()),
            ("Foo::Name", "const char *")
        );
        let s = parse_signature("Foo&& ns::Take(Foo&&)").expect("gcc rvalue return");
        assert_eq!(s.ret, "Foo&&");
        for ctor in ["Foo::Foo(int)", "ns::Box<T>::Box()", "Foo::~Foo()"] {
            assert!(parse_signature(ctor).is_some(), "{ctor}");
        }
        for text in [
            "thread_util::IsMainThread()",
            "ns::Find(key)",
            "p->ns::Get()",
            "ok && ns::Ready()",
            "n == ns::Count()",
            "!ns::Done()",
            "a & ns::Mask()",
        ] {
            assert!(parse_signature(text).is_none(), "{text}");
        }
    }

    /// A trace string is one qualified name and `()`; prose, arguments,
    /// members and unqualified calls are not.
    ///
    /// # Panics
    ///
    /// When a reading disagrees with its expectation.
    #[test]
    fn trace_strings_are_one_qualified_name_and_empty_parentheses() {
        assert_eq!(
            super::trace_name("CVdsVolumePlex::QueryExtents()").as_deref(),
            Some("CVdsVolumePlex::QueryExtents")
        );
        assert_eq!(
            super::trace_name("CComObject<CFoo, int>::CreateInstance()").as_deref(),
            Some("CComObject<CFoo, int>::CreateInstance")
        );
        for text in [
            "Error in Foo::Bar()",
            "Foo::Bar(&p)",
            "p->Foo::Bar()",
            "x.Foo::Bar()",
            "Refresh()",
            "Foo::Bar() failed",
        ] {
            assert!(super::trace_name(text).is_none(), "{text}");
        }
    }

    /// A space between the name and its parameter list leaves the return
    /// type whole.
    ///
    /// # Panics
    ///
    /// When the return type keeps a piece of the name.
    #[test]
    fn a_space_before_the_list_keeps_the_return_type() {
        let s = parse_signature("void Foo::Init (int)").expect("gcc signature");
        assert_eq!((s.name.as_str(), s.ret.as_str()), ("Foo::Init", "void"));
        assert_eq!(s.params, vec!["int"]);
    }

    /// A chain of functions, each referencing its own name and the one
    /// before it, is named whole in at most three steps per reference.
    ///
    /// Only the last function's name has one referrer; naming it leaves
    /// the one before it the last referrer of its own, and so on down, one
    /// function per round. A loop that rescanned every function each round
    /// spent steps quadratic in the chain.
    ///
    /// # Panics
    ///
    /// When the chain is not named whole or the steps pass the bound.
    #[test]
    fn a_chain_is_chosen_in_linear_steps() {
        const N: usize = 1000;
        let entry = |k: usize| 0x1000 + crate::num::from_usize(k);
        let found = Found {
            sigs: Vec::new(),
            candidates: (0..N)
                .map(|k| {
                    let names = [(k, k), (k.saturating_sub(1), k.saturating_sub(1))];
                    (entry(k), names.into_iter().collect())
                })
                .collect(),
            referrers: (0..N)
                .map(|n| [entry(n), entry((n + 1).min(N - 1))].into_iter().collect())
                .collect(),
        };
        let references: usize = found.referrers.iter().map(BTreeSet::len).sum();
        let (chosen, steps) = choose_own(&found, &mut BTreeSet::new(), &mut vec![false; N]);
        let whole = (0..N).map(|k| (entry(k), k)).collect::<BTreeMap<_, _>>();
        assert!(chosen == whole, "{} of {N} named", chosen.len());
        assert!(
            steps <= 3 * references,
            "{steps} steps for {references} references"
        );
    }
}
