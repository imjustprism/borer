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

use std::collections::{BTreeMap, BTreeSet};

use crate::isa::x86::{InstructionInfoFactory, OpAccess, Register};

use super::classes::class_of;
use super::functions::decode_block;
use super::{Analysis, Function, NameSource, Signature, data_referrers, single};
use crate::program::{BinaryFormat, Program};
use crate::strings::cstr_at;

/// Longest signature string read.
const SIG_MAX: usize = 512;
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

/// Fills the name and signature of every unnamed function that references a
/// signature string only it can be, and marks those names inferred.
///
/// # Arguments
///
/// * `program` - The image the strings are read from.
/// * `analysis` - Functions and cross-references; names are written in place.
pub(crate) fn infer(program: &Program, analysis: &mut Analysis) {
    let mut candidates: BTreeMap<u64, BTreeMap<String, Signature>> = BTreeMap::new();
    let mut referrers: BTreeMap<String, BTreeSet<u64>> = BTreeMap::new();
    let targets: Vec<u64> = analysis
        .xrefs
        .keys()
        .copied()
        .filter(|&t| in_data(program, t))
        .collect();
    let parsed = super::striped(&targets, |&target| {
        cstr_at(program, target, SIG_MIN, SIG_MAX).and_then(|(_, text)| parse_signature(&text))
    });
    let mut setters: BTreeMap<String, Vec<(u64, String)>> = BTreeMap::new();
    for (target, sig) in targets.iter().zip(parsed) {
        let (Some(sig), Some(sites)) = (sig.flatten(), analysis.xrefs.get(target)) else {
            continue;
        };
        if let Some(class) = class_of(&sig.name)
            && let Some(member) = setter_member(&sig.name)
        {
            setters
                .entry(class.to_owned())
                .or_default()
                .push((*target, member.to_owned()));
        }
        for from in data_referrers(sites) {
            candidates
                .entry(from)
                .or_default()
                .entry(sig.name.clone())
                .or_insert_with(|| sig.clone());
            referrers.entry(sig.name.clone()).or_default().insert(from);
        }
    }
    analysis.classes.setters = setters;
    let mut named: BTreeSet<u64> = analysis
        .functions
        .iter()
        .filter(|f| f.name.is_some())
        .map(|f| f.entry)
        .collect();
    let mut chosen: BTreeMap<u64, Signature> = BTreeMap::new();
    let mut assigned: BTreeSet<String> = BTreeSet::new();
    let mut arity: BTreeMap<u64, usize> = BTreeMap::new();
    loop {
        loop {
            let mut changed = false;
            for (&entry, cands) in &candidates {
                if named.contains(&entry) {
                    continue;
                }
                let own = cands.iter().filter(|(n, _)| {
                    !assigned.contains(*n)
                        && referrers
                            .get(*n)
                            .is_some_and(|r| r.iter().all(|f| *f == entry || named.contains(f)))
                });
                let Some((n, sig)) = single(own) else {
                    continue;
                };
                chosen.insert(entry, sig.clone());
                assigned.insert(n.clone());
                named.insert(entry);
                changed = true;
            }
            if !changed {
                break;
            }
        }
        let mut progressed = false;
        for (name, refs) in &referrers {
            if assigned.contains(name) {
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
            let Some(sig) = unnamed
                .iter()
                .find_map(|r| candidates.get(r).and_then(|c| c.get(name)))
            else {
                continue;
            };
            let expected = sig.params.len() + usize::from(sig.by_pointer);
            let fits = unnamed.iter().copied().filter(|r| {
                candidates.get(r).is_some_and(|c| c.len() == 1)
                    && analysis.function(*r).is_some_and(|f| {
                        let n = *arity.entry(*r).or_insert_with(|| args_read(program, f));
                        n == expected || n == expected + 1
                    })
            });
            let Some(only) = single(fits) else {
                continue;
            };
            chosen.insert(only, sig.clone());
            assigned.insert(name.clone());
            named.insert(only);
            progressed = true;
        }
        if !progressed {
            break;
        }
    }
    let mut seen: BTreeMap<String, u32> = BTreeMap::new();
    for f in &mut analysis.functions {
        let Some(sig) = chosen.get(&f.entry) else {
            continue;
        };
        let n = seen.entry(sig.name.clone()).or_insert(0);
        *n += 1;
        f.name = Some(if *n == 1 {
            sig.name.clone()
        } else {
            format!("{}_{n}", sig.name)
        });
        f.name_inferred = true;
        f.name_source = NameSource::Signature;
        f.signature = Some(sig.clone());
    }
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
/// The signature, or `None` when the text is not a function signature.
pub(crate) fn parse_signature(text: &str) -> Option<Signature> {
    if text.ends_with("...") {
        return None;
    }
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
    if !(after.is_empty() || after == "const" || after == "const noexcept" || after == "noexcept") {
        return None;
    }
    let conv = CONVENTIONS.iter().find_map(|k| head.rsplit_once(k));
    let (ret_raw, raw) = match conv {
        Some((pre, rest)) => (pre, rest.trim()),
        None => {
            let name = last_token(head);
            (head.get(..head.len() - name.len()).unwrap_or(""), name)
        }
    };
    let name = strip_keywords(raw);
    if name.is_empty()
        || name.len() > NAME_MAX
        || !name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_' || c == '<')
    {
        return None;
    }
    if conv.is_none() && !name.contains("::") {
        let words: Vec<&str> = head.split_whitespace().collect();
        let typed = words.first().is_some_and(|w| TYPE_WORDS.contains(w));
        let type_like = params
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || " _*&,:<>[]".contains(c));
        if words.len() < 2 || words.len() > 4 || !typed || !type_like {
            return None;
        }
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
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in params.char_indices() {
        match c {
            '<' | '(' => depth += 1,
            '>' | ')' => depth -= 1,
            ',' if depth == 0 => {
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
/// template arguments and after `operator`.
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
    if before.ends_with("operator") || before.ends_with("::operator") {
        let op_start = before.len() - "operator".len();
        return trimmed.get(op_start..).unwrap_or(token);
    }
    token
}

/// Removes elaborated-type keywords and collapses whitespace runs.
///
/// # Arguments
///
/// * `name` - The raw type or qualified name.
fn strip_keywords(name: &str) -> String {
    let mut out = name.to_owned();
    for k in KEYWORDS {
        out = out.replace(k, "");
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::{handler_name, parse_signature, setter_member};

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
}
