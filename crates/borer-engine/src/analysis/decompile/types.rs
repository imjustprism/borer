//! Types read back from the text: the classes calls return, parameter and local
//! declarations, and value widths.

use super::*;

mod infer;

pub(super) use infer::{Casts, inferred_type_on, scalar_width, signature_result, type_parameters};

/// Most singletons whose fields [`decompile_named`] names in one function.
pub(super) const SINGLETONS_MAX: usize = 8;

/// The classes whose static instance a function reads, in the order it
/// first does.
///
/// The analysis ties a thread-local slot to the class whose one instance it
/// holds, and the text names it `Class::<name>` with the name a pack gives
/// ([`crate::pack`], `[naming] singleton`). The text reads its fields as
/// `*(uint32_t*)(Class::instance + 0x70)`, and the static is a `Class *`,
/// so its fields take the class's names.
///
/// # Arguments
///
/// * `lines` - The function's lines.
/// * `suffix` - `::` and the static's name.
pub(super) fn singleton_classes(lines: &[String], suffix: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for line in lines.iter().filter(|l| !l.trim_start().starts_with("//")) {
        for (i, _) in line.match_indices(suffix) {
            if line
                .get(i + suffix.len()..)
                .is_some_and(|r| r.starts_with(is_ident_char))
            {
                continue;
            }
            let head = line.get(..i).unwrap_or("");
            let start = head
                .rfind(|c: char| !(is_ident_char(c) || c == ':'))
                .map_or(0, |k| k + 1);
            let class = head.get(start..).unwrap_or("");
            if class.starts_with(|c: char| c.is_ascii_alphabetic())
                && !out.iter().any(|c| c == class)
            {
                out.push(class.to_owned());
            }
        }
    }
    out
}

/// Most distinct classes whose call results [`decompile_named`] names the
/// fields of in one function; each costs one pass over its methods.
pub(super) const RESULT_CLASSES_MAX: usize = 8;

/// Most variables [`result_bindings`] binds in one function, copies
/// included.
pub(super) const RESULT_BINDINGS_MAX: usize = 512;

/// A variable that holds a pointer to a known class over a run of lines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Binding {
    /// The variable, a register or a local.
    pub(super) var: String,
    /// The class it points at.
    pub(super) class: String,
    /// First line it holds the pointer on.
    pub(super) from: usize,
    /// First line past the run: the end, a block or label that lets another
    /// value in, or the line that writes the variable again.
    pub(super) to: usize,
    /// Whether line `to` writes the variable again, so its right-hand side
    /// still reads the pointer.
    pub(super) rewritten: bool,
}

/// The class each callee of `f` returns a pointer to, by the name the
/// text calls it by.
///
/// A callee returning `Foo *` counts, and so does one returning a class by
/// value: it builds the object where its hidden result pointer says and
/// hands that pointer back, so the register holds a `Foo *` either way.
/// A callee with no declared signature still counts when its name says
/// what it returns: the accessor of a smart pointer or a container
/// (`Core::Ptr<Foo>::operator ->`, `std::unique_ptr<Foo>::get`,
/// `Util::Array<Foo>::operator []`) hands back the template argument
/// ([`accessor_class`]). Only a qualified or recovered class counts:
/// `char *` or `uint8_t *` has no fields to name.
///
/// # Arguments
///
/// * `analysis` - Discovery results with the callees' signatures.
/// * `overlay` - Names in force.
/// * `f` - The function being decompiled.
pub(super) fn result_classes(
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for &callee in &f.callees {
        let Some(sig) = analysis.function(callee).and_then(|g| g.signature.as_ref()) else {
            let name = name_of(analysis, overlay, callee);
            if let Some(class) = accessor_class(&name)
                .filter(|c| c.contains("::") || analysis.classes.by_name.contains_key(*c))
            {
                out.insert(name.clone(), class.to_owned());
            }
            continue;
        };
        let by_value = sig.by_pointer.then(|| {
            let ty = sig.ret.trim();
            ty.strip_prefix("const ").unwrap_or(ty).trim()
        });
        if let Some(class) = pointee_class(&sig.ret)
            .or(by_value)
            .filter(|c| c.contains("::") || analysis.classes.by_name.contains_key(*c))
        {
            out.insert(name_of(analysis, overlay, callee), class.to_owned());
        }
    }
    out
}

/// The method names that hand back the template argument of their class:
/// a smart pointer's dereference and getter, a container's element access.
const ACCESSORS: &[&str] = &[
    "operator ->",
    "operator->",
    "operator *",
    "operator*",
    "operator []",
    "operator[]",
    "get",
    "Get",
    "GetPtr",
    "get_ptr",
    "ptr",
    "Ptr",
    "At",
    "at",
    "Front",
    "front",
    "Back",
    "back",
];

/// The class an accessor of a template class returns a pointer or
/// reference to: the class's first template argument.
///
/// `Core::Ptr<Game::OfferGroup>::operator ->` returns a `Game::OfferGroup *`,
/// `std::unique_ptr<Foo,std::default_delete<Foo> >::get` a `Foo *`, and
/// `Util::Array<Core::Ptr<Game::Offer> >::operator []` a reference to a
/// `Core::Ptr<Game::Offer>`. Qualifiers and pointer marks on the argument
/// are dropped; an argument that is not a class (`unsigned int`, `float`)
/// is no class.
///
/// # Arguments
///
/// * `name` - The callee's qualified name.
pub(super) fn accessor_class(name: &str) -> Option<&str> {
    let class = classes::class_of(name)?;
    let method = name.get(class.len() + 2..)?.trim();
    if !ACCESSORS.contains(&method) {
        return None;
    }
    let inner = class.strip_suffix('>')?;
    let mut depth = 0usize;
    let mut open = None;
    for (i, ch) in inner.char_indices().rev() {
        match ch {
            '>' => depth += 1,
            '<' if depth == 0 => {
                open = Some(i);
                break;
            }
            '<' => depth -= 1,
            _ => {}
        }
    }
    let args = inner.get(open? + 1..)?;
    let mut depth = 0usize;
    let mut end = args.len();
    for (i, ch) in args.char_indices() {
        match ch {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                end = i;
                break;
            }
            _ => {}
        }
    }
    let arg = args.get(..end)?.trim();
    let arg = arg.strip_prefix("const ").unwrap_or(arg);
    let arg = arg.trim_end_matches(['*', '&', ' ']).trim();
    let plain = [
        "int",
        "unsigned int",
        "unsigned",
        "float",
        "double",
        "bool",
        "char",
        "unsigned char",
        "short",
        "unsigned short",
        "long",
        "unsigned long",
        "long long",
        "unsigned long long",
        "void",
        "signed char",
        "wchar_t",
    ];
    (!arg.is_empty() && !plain.contains(&arg) && !arg.starts_with(|c: char| c.is_ascii_digit()))
        .then_some(arg)
}

/// The function an expression calls last, when the whole expression is a
/// call: `Core::Ptr<A::B>::operator ->(a1 + 80)` calls
/// `Core::Ptr<A::B>::operator ->`.
///
/// # Arguments
///
/// * `rhs` - The expression.
pub(super) fn callee_of(rhs: &str) -> Option<&str> {
    let body = rhs.strip_suffix(')')?;
    let mut depth = 1usize;
    for (i, ch) in body.char_indices().rev() {
        match ch {
            ')' => depth += 1,
            '(' => {
                depth -= 1;
                if depth == 0 {
                    let callee = body.get(..i)?.trim_end();
                    return (!callee.is_empty()).then_some(callee);
                }
            }
            _ => {}
        }
    }
    None
}

/// Where each variable assigned a call's class-pointer result, or a copy of
/// one, holds it.
///
/// `rax = Core::Ptr<Game::Entity>::operator ->(a1 + 80);` binds `rax` to
/// `Game::Entity` from the next line until `rax` is written again, the
/// block it was assigned in closes, or a label lets another path in; a
/// `rbx = rax;` inside that run binds `rbx` the same way. A write inside a
/// loop that opened after the assignment ends the run before that loop,
/// which would read the new value on its second pass; a write anywhere
/// else, an `if` included, ends the run at itself. A variable whose address
/// is taken anywhere is not bound.
///
/// # Arguments
///
/// * `lines` - The function's lines.
/// * `class_of` - The class a right-hand side returns a pointer to.
pub(super) fn result_bindings(
    lines: &[String],
    class_of: impl Fn(&str) -> Option<String>,
) -> Vec<Binding> {
    let mut work: Vec<(String, String, usize)> = lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| {
            let (lhs, rhs) = plain_assignment(line)?;
            Some((lhs.to_owned(), class_of(rhs)?, i))
        })
        .collect();
    work.reverse();
    let mut out: Vec<Binding> = Vec::new();
    while let Some((var, class, def)) = work.pop() {
        if out.len() >= RESULT_BINDINGS_MAX {
            break;
        }
        if lines.iter().any(|l| takes_address(l, &var)) {
            continue;
        }
        let ind = lines.get(def).map_or(0, |l| indent_of(l));
        let mut to = lines.len();
        let mut rewritten = false;
        let mut loops: Vec<(usize, usize)> = Vec::new();
        for (j, line) in lines.iter().enumerate().skip(def + 1) {
            let t = line.trim();
            if t.is_empty() {
                continue;
            }
            let at = indent_of(line);
            if at < ind || t.ends_with(':') {
                to = j;
                break;
            }
            while let Some(&(open, _)) = loops.last() {
                if at < open || (at == open && t.starts_with('}')) {
                    loops.pop();
                } else {
                    break;
                }
            }
            if writes_var(t, &var) {
                if let Some(&(_, opener)) = loops.first() {
                    to = opener;
                } else {
                    to = j;
                    rewritten = true;
                }
                break;
            }
            if opens_loop(t) {
                loops.push((at, j));
            }
        }
        for (j, line) in lines.iter().enumerate().take(to).skip(def + 1) {
            if let Some((lhs, rhs)) = plain_assignment(line)
                && rhs == var
                && lhs != var
            {
                work.push((lhs.to_owned(), class.clone(), j));
            }
        }
        out.push(Binding {
            var,
            class,
            from: def + 1,
            to,
            rewritten,
        });
    }
    out
}

/// The scalar pointees a load casts to by one name.
///
/// Each holds the C spellings a declared type may use, the cast's name and
/// the size in bytes; `long` is left out, as its size is the platform's.
const SCALARS: [(&[&str], &str, u64); 10] = [
    (&["uint16_t", "unsigned short", "wchar_t"], "uint16_t", 2),
    (&["int16_t", "short"], "int16_t", 2),
    (&["uint32_t", "unsigned int", "unsigned"], "uint32_t", 4),
    (&["int32_t", "int"], "int32_t", 4),
    (
        &["uint64_t", "unsigned __int64", "unsigned long long"],
        "uint64_t",
        8,
    ),
    (&["int64_t", "__int64", "long long"], "int64_t", 8),
    (&["uint128_t"], "uint128_t", 16),
    (&["float"], "float", 4),
    (&["double"], "double", 8),
    (&["long double"], "long double", 10),
];

/// The pointees whose arithmetic C already counts in bytes, as GNU C does
/// for `void`.
const BYTE_POINTEES: [&str; 7] = [
    "void",
    "uint8_t",
    "int8_t",
    "char",
    "signed char",
    "unsigned char",
    "bool",
];

/// Rewrites the byte arithmetic on each typed pointer so that it still
/// counts bytes.
///
/// The text computes every address in bytes, as the instructions do:
/// `*(uint32_t*)(a2 + 0x14)` reads byte 0x14. That is what C means while
/// `a2` is a number or a `void *`, but C scales arithmetic on a `uint32_t *`
/// by four, so the same text read against a typed pointer names byte 0x50.
/// Each place a parameter declared `T *` meets `+`, `-` or a compound update,
/// `this` and class pointers included and bytes and `void` left out, is
/// rewritten to mean the bytes again: a load of the pointee's own type at a
/// multiple of its size is that element, `a2[5]`; an update by such a
/// multiple steps by elements, `a2 += 1`; any other operand reads the
/// pointer as its address, `(uintptr_t)a2 + 0x14`, which stays valid C on
/// either side of a minus and between two pointers. The address of a local
/// or a global is a typed pointer too, `&local_28` a `uint32_t *` when the
/// local is a `uint32_t`, and takes the same cast unless it is declared a
/// byte: `(uintptr_t)&local_28 + eax`.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `word` - The machine word type, `uint32_t` or `uint64_t`, the size of
///   a pointer a pointer points at.
///
/// # Returns
///
/// The text with the typed pointers' arithmetic in bytes.
pub(super) fn byte_arithmetic(text: &str, word: &str) -> String {
    let typed = typed_pointers(text);
    let bytes = byte_variables(text);
    let word = if word == "uint32_t" { 4 } else { 8 };
    let mut out: Vec<String> = text.lines().map(str::to_owned).collect();
    for line in out.iter_mut().filter(|l| !l.trim_start().starts_with("//")) {
        for (var, ty) in &typed {
            *line = bytes_of(line, var, ty, word);
        }
        *line = addresses_in(line, &bytes);
    }
    out.join("\n") + "\n"
}

/// The parameters the signature declares as pointers to something wider
/// than a byte, with their declared types.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
fn typed_pointers(text: &str) -> Vec<(String, String)> {
    signature_params(text)
        .into_iter()
        .filter(|(_, ty)| pointee_of(ty).is_some_and(|p| !BYTE_POINTEES.contains(&p)))
        .collect()
}

/// The parameters the signature declares, by name, with their declared
/// types.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
///
/// # Returns
///
/// `(name, type)` per parameter, in order; empty without a signature.
pub(super) fn signature_params(text: &str) -> Vec<(String, String)> {
    let Some(sig) = text.lines().find_map(|l| l.strip_prefix("// signature: ")) else {
        return Vec::new();
    };
    let sig = sig.strip_suffix(" const").unwrap_or(sig);
    let Some(body) = sig.strip_suffix(')') else {
        return Vec::new();
    };
    let mut depth = 0usize;
    let open = body.char_indices().rev().find_map(|(i, c)| {
        match c {
            ')' | '>' => depth += 1,
            '(' if depth == 0 => return Some(i),
            '(' | '<' => depth = depth.saturating_sub(1),
            _ => {}
        }
        None
    });
    let Some(params) = open.and_then(|i| body.get(i + 1..)) else {
        return Vec::new();
    };
    let mut parts: Vec<&str> = Vec::new();
    let (mut depth, mut start) = (0usize, 0);
    for (i, c) in params.char_indices() {
        match c {
            '(' | '<' => depth += 1,
            ')' | '>' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(&params[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(&params[start..]);
    parts
        .into_iter()
        .filter_map(|p| {
            let p = p.trim();
            let name_at = p.rfind(|c: char| !is_ident_char(c))? + 1;
            let (ty, name) = (p.get(..name_at)?.trim(), p.get(name_at..)?);
            is_ident(name).then(|| (name.to_owned(), ty.to_owned()))
        })
        .collect()
}

/// The variables a declaration line types as a byte, whose address counts
/// bytes already.
///
/// # Arguments
///
/// * `text` - A decompiled function, declarations included.
fn byte_variables(text: &str) -> BTreeSet<&str> {
    let mut out = BTreeSet::new();
    for line in text.lines() {
        let code = line.split(" //").next().unwrap_or(line).trim_end();
        let Some(names) = BYTE_POINTEES[1..]
            .iter()
            .find_map(|ty| code.strip_prefix(ty)?.strip_prefix(' ')?.strip_suffix(';'))
        else {
            continue;
        };
        if names.split(", ").all(is_ident) {
            out.extend(names.split(", "));
        }
    }
    out
}

/// Tells whether the operand between `head` and `tail` is a term of a sum
/// or a difference, a compound one or a negation included, where C scales
/// a typed pointer.
///
/// # Arguments
///
/// * `head` - The line before the operand.
/// * `tail` - The line after it.
fn summed(head: &str, tail: &str) -> bool {
    [" + ", " - ", " += ", " -= "]
        .iter()
        .any(|op| head.ends_with(op))
        || (head.ends_with('-') && !head.ends_with("--"))
        || [" + ", " - "].iter().any(|op| tail.starts_with(op))
}

/// Casts each `&name` a line sums to its address, unless `name` is a byte
/// ([`byte_arithmetic`]).
///
/// # Arguments
///
/// * `line` - One emitted line, not a comment.
/// * `bytes` - The variables declared as bytes.
fn addresses_in(line: &str, bytes: &BTreeSet<&str>) -> String {
    /// The cast that reads an address as a number.
    const CAST: &str = "(uintptr_t)";
    let mut s = line.to_owned();
    let mut from = 0;
    while let Some(at) = s.get(from..).and_then(|t| t.find('&')).map(|i| from + i) {
        from = at + 1;
        let rest = s.get(at + 1..).unwrap_or("");
        let name = &rest[..rest.find(|c: char| !is_ident_char(c)).unwrap_or(rest.len())];
        let (head, tail) = (&s[..at], &rest[name.len()..]);
        if !name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
            || bytes.contains(name)
            || head.ends_with([')', '&'])
            || tail.starts_with(['-', '.', '['])
            || in_literal(head)
            || !summed(head, tail)
        {
            continue;
        }
        from = at + CAST.len() + 1 + name.len();
        s.insert_str(at, CAST);
    }
    s
}

/// Rewrites one typed pointer's byte arithmetic in one line
/// ([`byte_arithmetic`]).
///
/// # Arguments
///
/// * `line` - One emitted line, not a comment.
/// * `var` - The pointer.
/// * `ty` - Its declared type, `T *`.
/// * `word` - Size in bytes of a pointer.
fn bytes_of(line: &str, var: &str, ty: &str, word: u64) -> String {
    let pointee = pointee_of(ty).unwrap_or(ty);
    let element = if pointee.ends_with('*') {
        Some((word, None))
    } else {
        SCALARS
            .iter()
            .find(|(names, _, _)| names.contains(&pointee))
            .map(|(_, cast, size)| (*size, Some(*cast)))
    };
    let mut s = line.to_owned();
    let mut from = 0;
    while let Some(at) = word_positions(&s, var).into_iter().find(|&p| p >= from) {
        from = at + var.len();
        let (head, tail) = (&s[..at], &s[at + var.len()..]);
        if in_literal(head)
            || head.ends_with(['>', '.', '&', ')', '*', '!', '~'])
            || tail.starts_with(['-', '.', '['])
        {
            continue;
        }
        if head.trim().is_empty()
            && let Some((op, step)) = [" += ", " -= "]
                .iter()
                .find_map(|op| Some((op.trim(), tail.strip_prefix(op)?.strip_suffix(';')?)))
        {
            let counted = element.and_then(|(size, _)| elements(step, size));
            let new = counted.map_or_else(
                || format!("{var} = ({ty})((uintptr_t){var} {} {step});", &op[..1]),
                |n| format!("{var} {op} {n};"),
            );
            s.replace_range(at.., &new);
            break;
        }
        if let Some((size, Some(cast))) = element
            && let Some(start) = head.strip_suffix(&format!("*({cast}*)(")).map(str::len)
            && let Some((sign, rest)) = tail
                .strip_prefix(" + ")
                .map(|r| ("", r))
                .or_else(|| tail.strip_prefix(" - ").map(|r| ("-", r)))
            && let Some(close) = rest.find(')')
            && let Some(n) = rest.get(..close).and_then(|k| elements(k, size))
        {
            let element = format!("{var}[{sign}{n}]");
            let end = s.len() - rest.len() + close + 1;
            s.replace_range(start..end, &element);
            from = start + element.len();
            continue;
        }
        if summed(head, tail) {
            let address = format!("(uintptr_t){var}");
            s.replace_range(at..at + var.len(), &address);
            from = at + address.len();
        }
    }
    s
}

/// The count of `size`-byte elements a byte step spells, when it spells a
/// whole number of them: a constant multiple of the size, or a variable
/// times the size.
///
/// # Arguments
///
/// * `step` - The byte step as the text writes it.
/// * `size` - The element size in bytes.
fn elements(step: &str, size: u64) -> Option<String> {
    if let Some(k) = parse_const(step) {
        return (k % size == 0).then(|| offset_text(k / size));
    }
    let shift = size
        .is_power_of_two()
        .then(|| format!(" << {}", size.trailing_zeros()));
    let times = step
        .strip_suffix(&format!(" * {size}"))
        .or_else(|| step.strip_suffix(shift.as_deref()?))?;
    is_ident(times).then(|| times.to_owned())
}

/// The type a declared pointer type points at, without its `const`.
///
/// # Arguments
///
/// * `ty` - The declared type, `T *`.
///
/// # Returns
///
/// `T`, or `None` when `ty` is no pointer.
fn pointee_of(ty: &str) -> Option<&str> {
    let pointee = ty.strip_suffix('*')?.trim();
    let pointee = pointee.strip_prefix("const ").unwrap_or(pointee);
    Some(pointee.strip_suffix(" const").unwrap_or(pointee))
}

/// Writes `((T*)base)[i]` as `base[i]` when `base` is already a `T *`.
///
/// The cast stays for a different pointee, a byte or `void` pointer, and
/// the machine word. A parenthesized base is not a declared name, so it
/// stays too. No field is invented: an array field already printed as
/// `base->field` is not this cast.
///
/// # Arguments
///
/// * `text` - A decompilation, parameter types already applied.
pub(super) fn spell_index(text: &str) -> String {
    let pointees = index_pointees(text);
    let chars = char_pointers(text);
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        if line.trim_start().starts_with("//") {
            out.push_str(line);
        } else {
            out.push_str(&char_indexes(&rewrite_indexes(line, &pointees), &chars));
        }
        out.push('\n');
    }
    out
}

/// The names a function declares as pointers to `char`, with the type a
/// load of one of their elements reads as.
///
/// Its parameters and its locals count; an element of a `char` or `signed
/// char` reads as `int8_t`, one of an `unsigned char` as `uint8_t`.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
fn char_pointers(text: &str) -> BTreeMap<String, &'static str> {
    let reads = |pointee: &str| match pointee {
        "char" | "signed char" => Some("int8_t"),
        "unsigned char" => Some("uint8_t"),
        _ => None,
    };
    let mut out = BTreeMap::new();
    for (name, ty) in signature_params(text) {
        if let Some(r) = pointee_of(&ty).and_then(reads) {
            out.insert(name, r);
        }
    }
    for line in text.lines() {
        let Some((ty, items)) = vars::declaration(line) else {
            continue;
        };
        let ty = ty.trim();
        let ty = ty.strip_prefix("const ").unwrap_or(ty);
        for (stars, name) in items {
            let p = if stars == "*" {
                Some(ty)
            } else {
                stars.is_empty().then(|| pointee_of(ty)).flatten()
            };
            if let Some(r) = p.and_then(reads) {
                out.insert(name.to_owned(), r);
            }
        }
    }
    out
}

/// Writes a byte load through a `char` pointer as the element it reads:
/// `*(int8_t*)(str + i)` as `str[i]` and `*(int8_t*)str` as `*str`.
///
/// A read of the other sign keeps it as a cast, `(uint8_t)str[i]`, so the
/// value is the one the machine read; a store needs none, since C
/// converts what it stores to the element's type and keeps the same low
/// byte, and neither does a test against zero, which either sign passes
/// alike. The index is all that follows `str + ` inside the parentheses,
/// and only sums, differences and products of terms qualify, which group
/// the same way in both spellings.
///
/// # Arguments
///
/// * `line` - One line of pseudo-C.
/// * `chars` - The `char` pointers and their element reads
///   ([`char_pointers`]).
fn char_indexes(line: &str, chars: &BTreeMap<String, &'static str>) -> String {
    if chars.is_empty() || !line.contains("int8_t*)") {
        return line.to_owned();
    }
    let mut out = String::with_capacity(line.len());
    let mut from = 0;
    let mut search = 0;
    while let Some(at) = line
        .get(search..)
        .and_then(|t| t.find("*("))
        .map(|k| k + search)
    {
        search = at + 2;
        let after = line.get(at + 2..).unwrap_or("");
        let Some(read) = ["int8_t", "uint8_t"]
            .into_iter()
            .find(|r| after.starts_with(&format!("{r}*)")))
        else {
            continue;
        };
        if in_literal(line.get(..at).unwrap_or("")) {
            continue;
        }
        let address = at + 2 + read.len() + 2;
        let Some((element, reads, used)) = element_of(line.get(address..).unwrap_or(""), chars)
        else {
            continue;
        };
        let end = address + used;
        let tail = line.get(end..).unwrap_or("");
        let stored = [" = ", " += ", " -= ", " |= ", " &= ", " ^= "]
            .iter()
            .any(|op| tail.starts_with(op));
        let zero_test = [" != 0", " == 0"].iter().any(|op| {
            tail.strip_prefix(op)
                .is_some_and(|r| !r.starts_with(|c: char| c.is_ascii_alphanumeric()))
        });
        out.push_str(line.get(from..at).unwrap_or(""));
        if reads == read || stored || zero_test {
            out.push_str(&element);
        } else {
            out.push_str(&format!("({read}){element}"));
        }
        from = end;
        search = end;
    }
    out.push_str(line.get(from..).unwrap_or(""));
    out
}

/// Reads `(name + index)` or `name` at the start of `text`, `name` a
/// `char` pointer.
///
/// # Arguments
///
/// * `text` - The text after a load's cast.
/// * `chars` - The `char` pointers and their element reads.
///
/// # Returns
///
/// The element (`name[index]` or `*name`), the type its load reads, and
/// how many bytes of `text` it spans; `None` when `text` starts with no
/// such address.
fn element_of(
    text: &str,
    chars: &BTreeMap<String, &'static str>,
) -> Option<(String, &'static str, usize)> {
    let span = ident_span(text);
    if span > 0 {
        let name = text.get(..span)?;
        let read = chars.get(name)?;
        let next = text.get(span..)?;
        return (!next.starts_with(['[', '(', '.']) && !next.starts_with("->"))
            .then(|| (format!("*{name}"), *read, span));
    }
    let inner = text.strip_prefix('(')?;
    let name = inner.get(..ident_span(inner))?;
    let read = chars.get(name)?;
    inner.get(name.len()..)?.strip_prefix(" + ")?;
    let close = matching_paren(text, 0)?;
    let index = text.get(1 + name.len() + 3..close)?;
    let mut depth = 0i32;
    for c in index.chars() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            c if depth == 0 && !(is_ident_char(c) || matches!(c, ' ' | '+' | '-' | '*')) => {
                return None;
            }
            _ => {}
        }
    }
    let index = match index.strip_prefix('(').and_then(|i| i.strip_suffix(')')) {
        Some(inner) if matching_paren(index, 0) == Some(index.len() - 1) => inner,
        Some(_) | None => index,
    };
    (!index.is_empty()).then(|| (format!("{name}[{index}]"), *read, close + 1))
}

/// Pointer names and the type they point at, bytes and `void` left out.
///
/// Those two already count bytes, so an element cast on them is the width
/// the declaration does not give.
///
/// # Arguments
///
/// * `text` - The function.
fn index_pointees(text: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for (name, ty) in typed_pointers(text) {
        if let Some(pointee) = pointee_of(&ty) {
            out.insert(name, pointee.to_owned());
        }
    }
    for line in text.lines() {
        let Some((ty, items)) = vars::declaration(line) else {
            continue;
        };
        for (stars, name) in items {
            let pointee = if !stars.is_empty() {
                ty.trim()
            } else if let Some(p) = pointee_of(ty.trim()) {
                p
            } else {
                continue;
            };
            if !pointee.is_empty() && !BYTE_POINTEES.contains(&pointee) {
                out.insert(name.to_owned(), pointee.to_owned());
            }
        }
    }
    out
}

/// Drops an element cast whose base is already that pointer.
///
/// # Arguments
///
/// * `line` - One line of pseudo-C.
/// * `pointees` - Declared pointer names and their pointees.
fn rewrite_indexes(line: &str, pointees: &BTreeMap<String, String>) -> String {
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    let mut quote = false;
    let mut escaped = false;
    while !rest.is_empty() {
        if quote {
            let c = rest.chars().next().unwrap_or('"');
            out.push(c);
            rest = rest.get(c.len_utf8()..).unwrap_or("");
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                quote = false;
            }
            continue;
        }
        if rest.starts_with('"') {
            quote = true;
            out.push('"');
            rest = rest.get(1..).unwrap_or("");
            continue;
        }
        let Some(at) = rest.find("((") else {
            out.push_str(rest);
            break;
        };
        if rest.get(..at).is_some_and(in_literal) {
            out.push_str(rest.get(..at + 2).unwrap_or(rest));
            rest = rest.get(at + 2..).unwrap_or("");
            continue;
        }
        let after = rest.get(at + 2..).unwrap_or("");
        let Some(cast) = element_cast(after, pointees) else {
            out.push_str(rest.get(..at + 2).unwrap_or(rest));
            rest = rest.get(at + 2..).unwrap_or("");
            continue;
        };
        out.push_str(rest.get(..at).unwrap_or(""));
        out.push_str(&cast);
        rest = rest
            .get(at + 2 + cast_len(after).unwrap_or(0)..)
            .unwrap_or("");
    }
    out
}

/// `base[index]` when `after` is `T*)base)[index]...` and `base` is a `T *`.
///
/// # Arguments
///
/// * `after` - The text after `((`.
/// * `pointees` - Declared pointer names and their pointees.
fn element_cast(after: &str, pointees: &BTreeMap<String, String>) -> Option<String> {
    let star = after.find("*)")?;
    let ty = after.get(..star)?.trim();
    if ty.is_empty() || ty.contains('(') {
        return None;
    }
    let name_at = star + 2;
    let name = after
        .get(name_at..)?
        .get(..ident_span(after.get(name_at..)?))?;
    if !is_ident(name) || pointees.get(name).is_none_or(|p| p != ty) {
        return None;
    }
    let bracket = after.get(name_at + name.len()..)?;
    let bracket = bracket.strip_prefix(")[")?;
    let end = close_bracket(bracket)?;
    let index = bracket.get(..end)?;
    Some(format!("{name}[{index}]"))
}

/// How many bytes of `after` an [`element_cast`] consumes, including the
/// `T*)base)[index]` it read.
///
/// # Arguments
///
/// * `after` - The text after `((`.
fn cast_len(after: &str) -> Option<usize> {
    let star = after.find("*)")?;
    let name_at = star + 2;
    let name_len = ident_span(after.get(name_at..)?);
    let tail = after.get(name_at + name_len..)?;
    let bracket = tail.strip_prefix(")[")?;
    let end = close_bracket(bracket)?;
    Some(name_at + name_len + 2 + end + 1)
}

/// The identifier length at the start of `text`.
///
/// # Arguments
///
/// * `text` - Text that may start with a name.
fn ident_span(text: &str) -> usize {
    text.chars()
        .take_while(|c| is_ident_char(*c))
        .map(char::len_utf8)
        .sum()
}

/// The index of the `]` that closes a `[` at the start of `text`'s caller.
///
/// `text` begins just after `[`.
///
/// # Arguments
///
/// * `text` - The index expression and the rest of the line.
fn close_bracket(text: &str) -> Option<usize> {
    let mut depth = 1i32;
    let mut quote = false;
    let mut escaped = false;
    for (i, c) in text.char_indices() {
        if quote {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                quote = false;
            }
            continue;
        }
        match c {
            '"' => quote = true,
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Tells whether the end of `head` lies inside a string literal.
///
/// # Arguments
///
/// * `head` - The line up to some position.
fn in_literal(head: &str) -> bool {
    let (mut inside, mut escaped) = (false, false);
    for c in head.chars() {
        match (inside, c) {
            (true, '\\') if !escaped => escaped = true,
            (_, '"') if !escaped => inside = !inside,
            _ => escaped = false,
        }
    }
    inside
}

/// Moves the typed locals off the `uint64_t` declaration onto their own.
///
/// # Arguments
///
/// * `lines` - The function, rewritten in place.
/// * `typed` - Each local and the type it gained.
pub(super) fn redeclare(lines: &mut Vec<String>, typed: &[(String, &'static str)]) {
    let taken: BTreeSet<&str> = typed.iter().map(|(n, _)| n.as_str()).collect();
    let mut extra: BTreeMap<&'static str, Vec<String>> = BTreeMap::new();
    for (name, ty) in typed {
        extra.entry(*ty).or_default().push(name.clone());
    }
    let mut at = None;
    for (i, line) in lines.iter_mut().enumerate() {
        let Some(kept) = line
            .strip_prefix("uint64_t ")
            .and_then(|rest| rest.strip_suffix(';'))
            .map(|names| {
                names
                    .split(", ")
                    .map(str::trim)
                    .filter(|n| !taken.contains(n))
                    .collect::<Vec<&str>>()
            })
        else {
            continue;
        };
        *line = if kept.is_empty() {
            String::from("\u{0}")
        } else {
            format!("uint64_t {};", kept.join(", "))
        };
        at = Some(i);
    }
    if let Some(i) = at {
        let added: Vec<String> = extra
            .iter()
            .map(|(ty, names)| format!("{ty} {};", names.join(", ")))
            .collect();
        lines.splice(i + 1..i + 1, added);
    }
    lines.retain(|l| l != "\u{0}");
}

/// Declares the stack slots a computed index runs across as one array.
///
/// `local_N` names the slot `N` bytes below the frame base, so
/// `local_48`, `local_38`, `local_28` and `local_18`, all `uint128_t`, lie
/// one after another upward from `local_48`. When the text reads through
/// `&local_48` at an offset it computes (`((uint32_t*)&local_48)[i]`),
/// the read can land in any of them, which C allows only inside one
/// object. The run of same-typed slots that starts at the indexed one and
/// steps by the type's size, with no gap, becomes `uint128_t local_48[4]`,
/// and each member reads as its element (`local_38` is `local_48[1]`).
/// The first slot's address is the array itself, `local_48`, which C
/// reads as the same address.
///
/// An indexed slot no other slot of its type follows is the frame object
/// it starts: the bytes up to the next slot the text names, or to the
/// frame's top. One `uint64_t local_58` that `((uint32_t*)&local_58)[i]`
/// indexes sixteen times over would let C's object rules write the slots
/// above it; it is `uint64_t local_58[10]`, its elements running up to
/// `local_c`.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
///
/// # Returns
///
/// The text with those slots declared as arrays.
pub(super) fn stack_arrays(text: &str) -> String {
    if !text.contains("&local_") {
        return text.to_owned();
    }
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let declared: BTreeMap<String, &'static str> = lines
        .iter()
        .filter(|l| is_declaration(l))
        .flat_map(|l| {
            let (ty, names) = l.trim_end_matches(';').split_once(' ').unwrap_or(("", ""));
            let ty = slot_type(ty);
            names
                .split(", ")
                .filter_map(move |n| ty.map(|t| (n.trim().to_owned(), t)))
                .collect::<Vec<_>>()
        })
        .collect();
    let named: Vec<u64> = lines
        .iter()
        .filter(|l| is_declaration(l))
        .flat_map(|l| {
            l.trim_end_matches(';')
                .split_once(' ')
                .map_or("", |(_, names)| names)
                .split(", ")
                .filter_map(|n| slot_offset(n.trim().trim_start_matches('*')))
                .collect::<Vec<_>>()
        })
        .collect();
    let indexed = indexed_through(&lines);
    let mut arrays: Vec<(String, &'static str, Vec<String>, u64)> = Vec::new();
    for (name, ty) in &declared {
        let Some(base) = slot_offset(name) else {
            continue;
        };
        if !indexed.contains(name.as_str()) {
            continue;
        }
        let size = slot_size(ty);
        let mut members = vec![name.clone()];
        let mut at = base;
        while let Some(next) = at.checked_sub(size).filter(|&n| n > 0) {
            let next_name = format!("local_{next:x}");
            if declared.get(&next_name) != Some(ty) {
                break;
            }
            members.push(next_name);
            at = next;
        }
        let len = if members.len() > 1 {
            u64::try_from(members.len()).unwrap_or(0)
        } else {
            let top = named
                .iter()
                .copied()
                .filter(|&d| d < base)
                .max()
                .unwrap_or(0);
            (base - top).div_ceil(size)
        };
        if len > 1 {
            arrays.push((name.clone(), ty, members, len));
        }
    }
    let runs: BTreeSet<String> = arrays
        .iter()
        .filter(|(_, _, m, _)| m.len() > 1)
        .flat_map(|(_, _, m, _)| m.iter().cloned())
        .collect();
    arrays.retain(|(name, _, m, _)| m.len() > 1 || !runs.contains(name));
    if arrays.is_empty() {
        return text.to_owned();
    }
    let gone: BTreeSet<&str> = arrays
        .iter()
        .flat_map(|(_, _, m, _)| m.iter().map(String::as_str))
        .collect();
    let mut at = None;
    for (k, line) in lines.iter_mut().enumerate() {
        if !is_declaration(line) {
            continue;
        }
        let Some((ty, names)) = line.trim_end_matches(';').split_once(' ') else {
            continue;
        };
        let kept: Vec<&str> = names
            .split(", ")
            .filter(|n| !gone.contains(n.trim()))
            .collect();
        if kept.len() != names.split(", ").count() {
            *line = if kept.is_empty() {
                String::from("\u{0}")
            } else {
                format!("{ty} {};", kept.join(", "))
            };
            at = Some(k);
        }
    }
    if let Some(k) = at {
        let decls: Vec<String> = arrays
            .iter()
            .map(|(name, ty, _, len)| format!("{ty} {name}[{len}];"))
            .collect();
        lines.splice(k + 1..k + 1, decls);
    }
    lines.retain(|l| l != "\u{0}");
    for (name, _, members, _) in &arrays {
        for line in lines
            .iter_mut()
            .filter(|l| !l.starts_with("//") && !is_declaration(l))
        {
            for (k, member) in members.iter().enumerate() {
                for pos in word_positions(line, member).into_iter().rev() {
                    let head = line.get(..pos).unwrap_or("");
                    if k == 0 && head.ends_with('&') {
                        line.replace_range(pos - 1..pos + member.len(), name);
                        continue;
                    }
                    line.replace_range(pos..pos + member.len(), &format!("{name}[{k}]"));
                }
            }
        }
    }
    lines.join("\n") + "\n"
}

/// A slot's declared type, when it is one an array of slots is made of.
///
/// # Arguments
///
/// * `ty` - The declared type.
fn slot_type(ty: &str) -> Option<&'static str> {
    [
        "uint8_t",
        "uint16_t",
        "uint32_t",
        "uint64_t",
        "uint128_t",
        "int8_t",
        "int16_t",
        "int32_t",
        "int64_t",
    ]
    .into_iter()
    .find(|t| *t == ty)
}

/// Bytes a slot of type `ty` takes.
///
/// # Arguments
///
/// * `ty` - One of [`slot_type`]'s types.
fn slot_size(ty: &str) -> u64 {
    match ty {
        "uint8_t" | "int8_t" => 1,
        "uint16_t" | "int16_t" => 2,
        "uint32_t" | "int32_t" => 4,
        "uint128_t" => 16,
        _ => 8,
    }
}

/// The frame offset `local_N` names.
///
/// # Arguments
///
/// * `name` - A variable name.
fn slot_offset(name: &str) -> Option<u64> {
    let base = name.split('[').next()?;
    u64::from_str_radix(base.strip_prefix("local_")?, 16).ok()
}

/// The names the text reads through `&name` at an offset it computes: an
/// index or a sum that is not a constant.
///
/// # Arguments
///
/// * `lines` - The function.
///
/// # Returns
///
/// Every name some code line reads through that way.
fn indexed_through(lines: &[String]) -> BTreeSet<&str> {
    let computed = |rest: &str| {
        let rest = rest.trim_start();
        !rest.starts_with(|c: char| c.is_ascii_digit())
    };
    let mut out = BTreeSet::new();
    for l in lines.iter().filter(|l| !l.starts_with("//")) {
        for after in l.split('&').skip(1) {
            let end = after
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(after.len());
            let (name, tail) = after.split_at(end);
            if name.is_empty() {
                continue;
            }
            let tail = tail.trim_start_matches(')');
            let through = match tail.strip_prefix('[') {
                Some(rest) => computed(rest),
                None => tail.trim_start().strip_prefix("+ ").is_some_and(computed),
            };
            if through {
                out.insert(name);
            }
        }
    }
    out
}

/// A line without its trailing `//` comment.
///
/// # Arguments
///
/// * `line` - One line.
fn uncommented(line: &str) -> &str {
    line.split_once(" //").map_or(line, |(code, _)| code)
}

/// The calls through a computed pointer in one line.
///
/// Each is where `(*` opens, the callee expression, and how many arguments
/// the call passes. A `(*)` with nothing inside is a function pointer type,
/// as a demangled template argument spells one, not a call.
///
/// # Arguments
///
/// * `line` - One line.
///
/// # Returns
///
/// Per call, the byte index of `(*`, the index one past the callee's
/// closing parenthesis, the callee text, and the argument count.
fn pointer_calls(line: &str) -> Vec<(usize, usize, String, usize)> {
    let mut out = Vec::new();
    let mut from = 0;
    while let Some(at) = line
        .get(from..)
        .and_then(|t| t.find("(*"))
        .map(|k| k + from)
    {
        from = at + 2;
        let Some(close) = matching_close(line, at) else {
            continue;
        };
        if line.get(close + 1..close + 2) != Some("(") {
            continue;
        }
        let Some(args_close) = matching_close(line, close + 1) else {
            continue;
        };
        let callee = line.get(at + 2..close).unwrap_or("");
        let callee = callee
            .strip_prefix('(')
            .and_then(|c| c.strip_suffix(')'))
            .filter(|c| balanced(c))
            .unwrap_or(callee)
            .to_owned();
        if callee.trim().is_empty() {
            continue;
        }
        let args = line.get(close + 2..args_close).unwrap_or("");
        let count = if args.trim().is_empty() {
            0
        } else {
            1 + top_level_commas(args)
        };
        out.push((at, close + 1, callee, count));
    }
    out
}

/// The index of the parenthesis that closes the one at `open`.
///
/// # Arguments
///
/// * `line` - The text.
/// * `open` - Index of a `(`.
fn matching_close(line: &str, open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (k, c) in line.char_indices().skip_while(|(k, _)| *k < open) {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(k);
                }
            }
            _ => {}
        }
    }
    None
}

/// How many commas separate arguments at the outermost level of `args`.
///
/// # Arguments
///
/// * `args` - An argument list without its parentheses.
fn top_level_commas(args: &str) -> usize {
    let mut depth = 0i32;
    let mut n = 0;
    for c in args.chars() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => n += 1,
            _ => {}
        }
    }
    n
}

/// A function pointer type returning a word and taking `count` words.
///
/// # Arguments
///
/// * `count` - The arguments.
/// * `name` - The declarator inside the `(*)`, empty for a cast.
fn word_function(count: usize, name: &str) -> String {
    let params = if count == 0 {
        "void".to_owned()
    } else {
        vec!["uint64_t"; count].join(", ")
    };
    format!("uint64_t (*{name})({params})")
}

/// Writes every call through a computed pointer as C can call it.
///
/// The lifter writes `(*p)(x)` for a call through a register or a loaded
/// word, and `p` is declared an integer or `void *`, which C cannot call.
/// A parameter that is only ever called, the same number of arguments
/// each time, is declared the function pointer it is and called by name:
/// `uint64_t (*a1)(uint64_t)` and `a1(x)`. Any other callee is cast to a
/// function pointer taking as many words as the call passes:
/// `((uint64_t (*)(uint64_t))rax)(x)`.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
///
/// # Returns
///
/// The text with its pointer calls typed.
pub(super) fn callable_pointers(text: &str) -> String {
    if !text.contains("(*") {
        return text.to_owned();
    }
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let mut arity: BTreeMap<String, Option<usize>> = BTreeMap::new();
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for (_, _, callee, count) in pointer_calls(line) {
            if is_ident(&callee) {
                let seen = arity.entry(callee).or_insert(Some(count));
                if *seen != Some(count) {
                    *seen = None;
                }
            }
        }
    }
    let uses = word_lines(&lines);
    let called: BTreeMap<String, usize> = arity
        .into_iter()
        .filter_map(|(name, count)| count.map(|c| (name, c)))
        .filter(|(name, _)| {
            uses.get(name.as_str())
                .map_or(&[][..], Vec::as_slice)
                .iter()
                .filter_map(|k| lines.get(*k))
                .filter(|l| !l.starts_with("//") && !is_declaration(uncommented(l)))
                .all(|l| {
                    let calls = pointer_calls(l)
                        .iter()
                        .filter(|(_, _, c, _)| c == name)
                        .count();
                    word_positions(l, name).len() == calls
                })
        })
        .collect();
    drop(uses);
    let mut changed = false;
    let mut declared: Vec<(usize, String)> = Vec::new();
    for (k, line) in lines.iter_mut().enumerate() {
        if line.starts_with("//") || !is_declaration(uncommented(line)) {
            continue;
        }
        let (body, comment) = match line.split_once(" //") {
            Some((b, c)) => (b.to_owned(), format!(" //{c}")),
            None => (line.clone(), String::new()),
        };
        let Some((ty, names)) = body.strip_suffix(';').and_then(|b| b.split_once(' ')) else {
            continue;
        };
        if !matches!(ty, "uint64_t" | "uint32_t" | "int64_t") {
            continue;
        }
        let mut kept: Vec<&str> = Vec::new();
        for n in names.split(", ").map(str::trim) {
            match called.get(n) {
                Some(&count) => {
                    declared.push((k, format!("{};{comment}", word_function(count, n))));
                }
                None => kept.push(n),
            }
        }
        if kept.len() != names.split(", ").count() {
            *line = if kept.is_empty() {
                String::from("\u{0}")
            } else {
                format!("{ty} {};{comment}", kept.join(", "))
            };
            changed = true;
        }
    }
    for (k, decl) in declared.into_iter().rev() {
        lines.insert(k + 1, decl);
    }
    lines.retain(|l| l != "\u{0}");
    for line in &mut lines {
        if let Some(rest) = line.strip_prefix("// signature: ") {
            let mut sig = rest.to_owned();
            for (name, count) in &called {
                for ty in ["uint64_t ", "void *", "uint32_t "] {
                    let decl = format!("{ty}{name}");
                    if let Some(at) = sig.find(&decl)
                        && sig
                            .get(at + decl.len()..)
                            .is_some_and(|t| t.starts_with([',', ')']))
                    {
                        sig.replace_range(at..at + decl.len(), &word_function(*count, name));
                        changed = true;
                        break;
                    }
                }
            }
            *line = format!("// signature: {sig}");
            continue;
        }
        if line.starts_with("//") || uncommented(line).starts_with("uint64_t (*") {
            continue;
        }
        for (at, end, callee, count) in pointer_calls(line).into_iter().rev() {
            let with = if called.contains_key(&callee) {
                callee.clone()
            } else if is_ident(&callee) {
                format!("(({}){callee})", word_function(count, ""))
            } else {
                format!("(({})({callee}))", word_function(count, ""))
            };
            line.replace_range(at..end, &with);
            changed = true;
        }
    }
    if !changed {
        return text.to_owned();
    }
    lines.join("\n") + "\n"
}

/// Writes a bitwise operation on a float parameter as an operation on its
/// bits.
///
/// `movd eax, xmm0` and the sign and magnitude masks read a float's
/// encoding, and the text says `a1 & 0xffffffff` with `a1` a `float`:
/// C has no bitwise operators on floats. An operand of `&`, `|`, `^`,
/// `<<` or `>>` that is a `float` parameter is `*(uint32_t*)&a1`, a
/// `double` one `*(uint64_t*)&a1`: the bits the instruction read.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
///
/// # Returns
///
/// The text with those reads spelled as bit reads.
pub(super) fn float_bit_reads(text: &str) -> String {
    let Some(sig) = text.lines().find_map(|l| l.strip_prefix("// signature: ")) else {
        return text.to_owned();
    };
    let floats: Vec<(String, &'static str)> = sig
        .split(['(', ',', ')'])
        .filter_map(|p| {
            let p = p.trim();
            let (ty, name) = p.rsplit_once(' ')?;
            let bits = match ty {
                "float" => "uint32_t",
                "double" => "uint64_t",
                _ => return None,
            };
            is_param_name(name).then(|| (name.to_owned(), bits))
        })
        .collect();
    if floats.is_empty() {
        return text.to_owned();
    }
    const BITWISE: [&str; 5] = [" & ", " | ", " ^ ", " << ", " >> "];
    let mut changed = false;
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    for line in lines.iter_mut().filter(|l| !l.starts_with("//")) {
        for (name, bits) in &floats {
            for at in word_positions(line, name).into_iter().rev() {
                let head = line.get(..at).unwrap_or("");
                let tail = line.get(at + name.len()..).unwrap_or("");
                let operand = BITWISE
                    .iter()
                    .any(|op| tail.starts_with(op) || head.ends_with(op));
                if operand && !head.ends_with('&') && !head.ends_with('*') {
                    line.replace_range(at..at + name.len(), &format!("*({bits}*)&{name}"));
                    changed = true;
                }
            }
        }
    }
    if !changed {
        return text.to_owned();
    }
    lines.join("\n") + "\n"
}

/// What joins the kept half of a scalar single's merge to its new low
/// lane ([`single_merge`]); a text without it holds no merge.
const MERGE_KEEP: &str = " & 0xffffffff00000000) | (";

/// The kept half and the new low lane of a scalar single's merge,
/// `(a & 0xffffffff00000000) | (e & 0xffffffff)`.
///
/// # Arguments
///
/// * `rhs` - An expression, without its `;`.
fn single_merge(rhs: &str) -> Option<(&str, &str)> {
    let rest = rhs.strip_prefix('(')?;
    let (kept, rest) = rest.split_once(MERGE_KEEP)?;
    let lane = rest.strip_suffix(" & 0xffffffff)")?;
    if !(balanced(kept) && balanced(lane)) {
        return None;
    }
    let inner = lane
        .strip_prefix('(')
        .and_then(|l| l.strip_suffix(')'))
        .filter(|l| balanced(l));
    Some((kept, inner.unwrap_or(lane)))
}

/// Declares a register a scalar single only ever replaces the low lane
/// of as a `float`, and writes each of those replacements as plain
/// assignments.
///
/// `addss` and its kin keep bits 63:32 of their register, which the
/// lifter spells `v = (v & 0xffffffff00000000) | (e & 0xffffffff)`. When
/// every write of `v` is such a merge or a zero, and every read of `v` is
/// another merge's lane or kept half or a `return` of a `float`
/// function, nothing reads the kept bits: `v` is the single `e`, and
/// `float v; v = e;` says the same in C. A `return` of a merge in a
/// function returning `float` returns its lane. Any other read (a cast, an
/// integer operation, a copy) keeps the variable as it was.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines included.
///
/// # Returns
///
/// The text with those registers declared `float`.
pub(super) fn float_lanes(text: &str) -> String {
    if !text.contains(MERGE_KEEP) {
        return text.to_owned();
    }
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let returns_float = lines.iter().any(|l| l.starts_with("// signature: float "));
    let mut changed = false;
    if returns_float {
        for line in &mut lines {
            let indent = line.len() - line.trim_start().len();
            let lane = line
                .trim()
                .strip_prefix("return ")
                .and_then(|r| r.strip_suffix(';'))
                .and_then(single_merge)
                .map(|(_, lane)| lane.to_owned());
            if let Some(lane) = lane {
                *line = format!("{}return {lane};", " ".repeat(indent));
                changed = true;
            }
        }
    }
    let names = uint64_names(&lines);
    let mut typed: Vec<(String, &'static str)> = Vec::new();
    for name in names {
        let mut merges = 0usize;
        let fits = lines.iter().all(|line| {
            if line.starts_with("//")
                || is_declaration(line)
                || word_positions(line, &name).is_empty()
            {
                return true;
            }
            let t = line.trim();
            let body = t.strip_suffix(';').unwrap_or(t);
            if let Some((lhs, rhs)) = body.split_once(" = ")
                && is_ident(lhs)
                && let Some((kept, lane)) = single_merge(rhs)
            {
                merges += usize::from(lhs == name);
                return !float_cast_of(kept, &name) && !float_cast_of(lane, &name);
            }
            if const_chain(t).is_some_and(|chain| chain.contains(&name.as_str())) {
                return body.ends_with(" = 0");
            }
            returns_float && body == format!("return {name}")
        });
        if fits && merges > 0 {
            typed.push((name, "float"));
        }
    }
    if typed.is_empty() && !changed {
        return text.to_owned();
    }
    let floats: BTreeSet<&str> = typed.iter().map(|(n, _)| n.as_str()).collect();
    for line in &mut lines {
        let indent = line.len() - line.trim_start().len();
        let t = line.trim();
        let Some((lhs, rhs)) = t.strip_suffix(';').and_then(|b| b.split_once(" = ")) else {
            continue;
        };
        if !floats.contains(lhs) {
            continue;
        }
        if let Some((_, lane)) = single_merge(rhs) {
            *line = format!("{}{lhs} = {lane};", " ".repeat(indent));
        }
    }
    redeclare(&mut lines, &typed);
    lines.join("\n") + "\n"
}

/// Tells whether `name` appears in `expr` right after an integer cast,
/// which reads its bits rather than its value.
///
/// # Arguments
///
/// * `expr` - An expression.
/// * `name` - The variable.
fn float_cast_of(expr: &str, name: &str) -> bool {
    word_positions(expr, name).into_iter().any(|at| {
        let head = expr.get(..at).unwrap_or("");
        head.ends_with("_t)") || head.ends_with("_t)(") || head.ends_with('&')
    })
}

/// Pulls a counter's initializer up to the `while` when another pure
/// assignment sits between them, and makes the `for` the emitter would
/// have made from a `+= 1` it can now see.
///
/// # Arguments
///
/// * `lines` - The body, after lane writes read as compound updates.
pub(super) fn sugar_gap(lines: &mut Vec<String>) {
    let mut k = 0;
    while k < lines.len() {
        if !gap_for(lines, k) {
            k += 1;
        }
    }
}

/// Rewrites `v = init; <pure>; while (C) { B; v += 1; }` at `k` as a `for`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of `v`'s initializer.
///
/// # Returns
///
/// Whether the `while` became a `for`.
fn gap_for(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(init) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(init);
    let Some((v, value)) = plain_assignment(init).filter(|(_, r)| !impure(r)) else {
        return false;
    };
    let mut head = None;
    let mut between = Vec::new();
    for j in (k + 1)..lines.len().min(k + 6) {
        let Some(line) = lines.get(j) else {
            break;
        };
        if line.trim().is_empty() {
            continue;
        }
        if indent_of(line) != pad {
            return false;
        }
        if let Some(cond) = line
            .trim()
            .strip_prefix("while (")
            .and_then(|r| r.strip_suffix(") {"))
        {
            if !mentions_ident(cond, v) {
                return false;
            }
            head = Some((j, cond.to_owned()));
            break;
        }
        let Some((other, rhs)) = plain_assignment(line).filter(|(_, r)| !impure(r)) else {
            return false;
        };
        if other == v || mentions_ident(rhs, v) || mentions_ident(value, other) {
            return false;
        }
        between.push(line.clone());
    }
    let Some((head, cond)) = head else {
        return false;
    };
    if between.is_empty() {
        return false;
    }
    let Some(close) = loops::closing(lines, head, pad) else {
        return false;
    };
    if lines.get(close).is_none_or(|l| l.trim() != "}") {
        return false;
    }
    let body = lines.get(head + 1..close).unwrap_or(&[]);
    if body.iter().any(|l| is_label(l)) {
        return false;
    }
    let Some(step) = body.last().map(|l| l.trim().to_owned()) else {
        return false;
    };
    let Some(step) = step.strip_suffix(';') else {
        return false;
    };
    if step != format!("{v} += 1") && step != format!("{v} -= 1") {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let mut rewritten = between;
    rewritten.push(format!("{pad_s}for ({v} = {value}; {cond}; {step}) {{"));
    rewritten.extend(body.get(..body.len() - 1).unwrap_or(&[]).iter().cloned());
    rewritten.push(format!("{pad_s}}}"));
    lines.splice(k..=close, rewritten);
    true
}

/// Mask a 32-bit write leaves on a value the text holds in 64 bits.
const MASK32: &str = " & 0xffffffff";

/// Declares a register variable at the width its uses show, and drops the
/// casts that width makes redundant.
///
/// The same evidence as [`type_parameters`], applied to the locals the
/// emitter declares: a register every use sign-extends from 32 bits was an
/// `int32_t`, one every use masks to a byte was a `uint8_t`. The name moves
/// off the `uint64_t` line onto one of its own type, dropping that line
/// when nothing is left on it, and its casts and
/// masks go, since C promotes the declared type the same way. A local the
/// text already declares at a narrow width drops that same cast, including
/// one written `(uint32_t)(name)`, and keeps a cast of a different width.
/// A mask over arithmetic C already does in `unsigned int` goes too
/// ([`drop_unsigned_masks`]). Only register
/// names and the variables a register's webs became
/// ([`super::vars::split_webs`]) move; a stack slot keeps the width its
/// accesses gave it, which the overlap notes depend on.
///
/// # Arguments
///
/// * `text` - A decompiled function, headers and declarations included.
///
/// # Returns
///
/// The text with the locals typed.
pub(super) fn type_locals(text: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let body: Vec<String> = lines
        .iter()
        .filter(|l| !is_declaration(l))
        .cloned()
        .collect();
    let uses = word_lines(&body);
    let casts = Casts::of(&body);
    let mut narrowed: Vec<(String, &'static str)> = Vec::new();
    for line in &lines {
        let Some(names) = line
            .strip_prefix("uint64_t ")
            .and_then(|r| r.strip_suffix(';'))
            .map(|r| {
                r.split(", ")
                    .map(str::trim)
                    .filter(|n| is_register_name(n) || vars::is_var_name(n))
                    .map(str::to_owned)
                    .collect::<Vec<String>>()
            })
        else {
            continue;
        };
        for name in names {
            let rows = uses.get(name.as_str()).map_or(&[][..], Vec::as_slice);
            let on = rows.iter().filter_map(|k| body.get(*k));
            if let Some(ty) = inferred_type_on(&body, &casts, on, &name) {
                narrowed.push((name, ty));
            }
        }
    }
    drop(uses);
    let signed = sign_signed_reads(&mut lines);
    let declared_narrow = narrow_declarations(&lines);
    if narrowed.is_empty() && declared_narrow.is_empty() && !signed {
        return if infer::refine_locals(&mut lines) {
            lines.join("\n") + "\n"
        } else {
            text.to_owned()
        };
    }
    strip_widths(&mut lines, &narrowed, |l| {
        !l.starts_with("//") && !l.starts_with("uint64_t ")
    });
    redeclare(&mut lines, &narrowed);
    strip_widths(&mut lines, &declared_narrow, |l| {
        !l.starts_with("//") && !is_declaration(l)
    });
    let widths: BTreeMap<&str, u8> = declared_narrow
        .iter()
        .chain(&narrowed)
        .filter_map(|(n, ty)| Some((n.as_str(), integer_bits(ty)?)))
        .collect();
    let unmasked: Vec<Option<String>> = lines.iter().map(|l| unmask_write(l, &widths)).collect();
    for (line, next) in lines.iter_mut().zip(unmasked) {
        if let Some(next) = next {
            *line = next;
        }
    }
    let unsigned32: BTreeSet<String> = lines
        .iter()
        .filter_map(|l| l.strip_prefix("uint32_t ")?.strip_suffix(';'))
        .flat_map(|names| names.split(", ").map(str::trim))
        .filter(|n| is_ident(n))
        .map(str::to_owned)
        .collect();
    if !unsigned32.is_empty() {
        for line in &mut lines {
            if line.contains(MASK32) && !line.starts_with("//") && !is_declaration(line) {
                *line = drop_unsigned_masks(line, &unsigned32);
            }
        }
    }
    infer::refine_locals(&mut lines);
    lines.join("\n") + "\n"
}

/// Declares a `uint32_t` local or global `int32_t` when the text reads it
/// only as one.
///
/// Every occurrence is cast `(int32_t)` or `(int64_t)(int32_t)`, is the
/// target of an assignment, an increment or a decrement, or is what a
/// function returning 32 bits returns.
///
/// The casts are the sign extensions the machine applied (`movsxd`), so
/// the variable was an `int`; [`narrow_declarations`] then drops them,
/// since C converts an `int` the same way. A write stores the same 32
/// bits in either type. A local the text reads any other way (its
/// address, a partial read, an unsigned operation) keeps its type.
///
/// PERF: each local's occurrences are read on the lines that hold it as a
/// word ([`word_lines`]), not on every line: a function of thousands of
/// lines declares hundreds of these locals, and the scan of every line for
/// each was a sixth of its decompile.
///
/// # Arguments
///
/// * `lines` - The function, header and declaration lines included.
///
/// # Returns
///
/// Whether any declaration changed.
fn sign_signed_reads(lines: &mut Vec<String>) -> bool {
    const CASTS: [&str; 2] = ["(int64_t)(int32_t)", "(int32_t)"];
    const WRITES: [&str; 5] = [" = ", " += ", " -= ", "++", "--"];
    let returns32 = signature_result(lines)
        .and_then(scalar_width)
        .is_some_and(|w| matches!(w, "int32_t" | "uint32_t"));
    let uses = std::cell::OnceCell::new();
    let signed_only = |name: &str| {
        let mut read = false;
        let rows = uses
            .get_or_init(|| word_lines(lines))
            .get(name)
            .map_or(&[][..], Vec::as_slice);
        for line in rows
            .iter()
            .filter_map(|&k| lines.get(k))
            .filter(|l| !l.starts_with("//") && !declares(l))
        {
            for at in word_positions(line, name) {
                let head = line.get(..at).unwrap_or("");
                let tail = line.get(at + name.len()..).unwrap_or("");
                let returned = returns32 && head.trim() == "return" && tail.starts_with(';');
                let written =
                    WRITES.iter().any(|w| tail.starts_with(w)) && !head.ends_with(['*', '&']);
                if CASTS.iter().any(|c| head.ends_with(c)) {
                    read = true;
                } else if !returned && !written {
                    return false;
                }
            }
        }
        read
    };
    let mut out: Vec<String> = Vec::with_capacity(lines.len() + 1);
    let mut retyped: Vec<String> = Vec::new();
    for line in lines.iter() {
        let (decl, note) = line.split_once("; //").unwrap_or((line.as_str(), ""));
        let names: Vec<&str> = decl
            .strip_prefix("uint32_t ")
            .map(|r| r.strip_suffix(';').unwrap_or(r))
            .filter(|_| note.is_empty() == decl.ends_with(';'))
            .map(|r| r.split(", ").map(str::trim).collect())
            .unwrap_or_default();
        let (signed, kept): (Vec<&str>, Vec<&str>) = names
            .iter()
            .filter(|n| is_ident(n))
            .partition(|n| signed_only(n));
        if signed.is_empty() || signed.len() + kept.len() != names.len() {
            out.push(line.clone());
            continue;
        }
        let note = if note.is_empty() {
            String::new()
        } else {
            format!(" //{note}")
        };
        if !kept.is_empty() {
            out.push(format!("uint32_t {};{note}", kept.join(", ")));
        }
        out.push(format!("int32_t {};{note}", signed.join(", ")));
        retyped.extend(signed.iter().map(|n| (*n).to_owned()));
    }
    *lines = out;
    let Some((casts, mask)) = narrow_type("int32_t") else {
        return false;
    };
    for line in lines
        .iter_mut()
        .filter(|l| !l.starts_with("//") && !declares(l))
    {
        for name in &retyped {
            if line.contains(name.as_str()) {
                *line = strip_width(line, name, casts, mask);
            }
        }
    }
    !retyped.is_empty()
}

/// Tells whether a line declares variables: a [`is_declaration`] line, or
/// one of a global with its `// @ address` note.
///
/// # Arguments
///
/// * `line` - One line of the text.
fn declares(line: &str) -> bool {
    match line.split_once("; //") {
        Some((decl, _)) => is_declaration(&format!("{decl};")),
        None => is_declaration(line),
    }
}

/// Tells whether C evaluates an expression as an `unsigned int`, so its
/// value already fits 32 bits.
///
/// Every leaf is a `uint32_t` variable or a constant below 2^31, at least
/// one is a variable, and the operators keep the type: arithmetic, bitwise
/// and shift operators. The usual conversions turn the `int` constants
/// beside an `unsigned int` into it, so the whole is computed modulo 2^32
/// and a 32-bit mask on it changes nothing. A call, a dereference, an index,
/// a field or a cast names something else, so it says no.
///
/// # Arguments
///
/// * `expr` - The expression inside the mask's parentheses.
/// * `unsigned32` - The variables declared `uint32_t`.
fn is_unsigned32(expr: &str, unsigned32: &BTreeSet<String>) -> bool {
    let mut vars = 0usize;
    let mut rest = expr.trim();
    while let Some(c) = rest.chars().next() {
        if is_ident_char(c) && !c.is_ascii_digit() {
            let n = rest.find(|c: char| !is_ident_char(c)).unwrap_or(rest.len());
            if !unsigned32.contains(rest.get(..n).unwrap_or("")) {
                return false;
            }
            rest = rest.get(n..).unwrap_or("").trim_start();
            if rest.starts_with(['(', '[', '.']) || rest.starts_with("->") {
                return false;
            }
            vars += 1;
        } else if c.is_ascii_digit() {
            let n = rest
                .find(|c: char| !c.is_ascii_alphanumeric())
                .unwrap_or(rest.len());
            if parse_const(rest.get(..n).unwrap_or("")).is_none_or(|k| k > 0x7fff_ffff) {
                return false;
            }
            rest = rest.get(n..).unwrap_or("").trim_start();
        } else {
            let Some(op) = ["<<", ">>", "+", "-", "*", "&", "|", "^", "~", "(", ")"]
                .iter()
                .find(|op| rest.starts_with(**op))
            else {
                return false;
            };
            rest = rest.get(op.len()..).unwrap_or("").trim_start();
        }
    }
    vars > 0
}

/// The width in bits of a narrow integer type a declaration gives, when
/// it does not depend on the data model (`long` does).
///
/// # Arguments
///
/// * `ty` - The declared type.
///
/// # Returns
///
/// 8, 16 or 32, or `None` for any other type.
pub(super) fn integer_bits(ty: &str) -> Option<u8> {
    match ty {
        "int32_t" | "int" | "INT" | "HRESULT" | "uint32_t" | "unsigned int" | "unsigned"
        | "DWORD" | "UINT" => Some(32),
        "int16_t" | "short" | "SHORT" | "uint16_t" | "unsigned short" | "WORD" | "wchar_t" => {
            Some(16)
        }
        "int8_t" | "char" | "signed char" | "uint8_t" | "unsigned char" | "BYTE" => Some(8),
        _ => None,
    }
}

/// Drops the mask from a write of a masked value to a narrow local that
/// the mask covers: `local_dc = v & 0xffffffff;` is `local_dc = v;` when
/// `local_dc` is a `uint32_t`.
///
/// Converting a value to an integer type of `n` bits keeps its low `n`
/// bits, and a mask at least that wide leaves those alone, so the mask
/// changes nothing the store keeps. The mask must cover the whole value:
/// one under a `|`, `^`, `&&`, `||` or `?:` at the top binds only to the
/// operand beside it.
///
/// # Arguments
///
/// * `line` - One line.
/// * `widths` - The narrow locals, with their widths in bits.
///
/// # Returns
///
/// The line without the mask, or `None` when it is no such write.
fn unmask_write(line: &str, widths: &BTreeMap<&str, u8>) -> Option<String> {
    let indent = line.len() - line.trim_start().len();
    let (pad, trimmed) = line.split_at(indent);
    let (lhs, rhs) = trimmed.strip_suffix(';')?.split_once(" = ")?;
    let bits = *widths.get(lhs)?;
    let expr = [32u8, 16, 8]
        .into_iter()
        .filter(|m| *m >= bits)
        .find_map(|m| rhs.strip_suffix(mask_text(m)))?
        .trim();
    let mut depth = 0i32;
    for (i, c) in expr.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ' ' if depth == 0 => {
                let rest = expr.get(i..).unwrap_or("");
                if [" | ", " ^ ", " && ", " || ", " ? ", " = ", " & "]
                    .iter()
                    .any(|op| rest.starts_with(op))
                {
                    return None;
                }
            }
            _ => {}
        }
    }
    (balanced(expr) && depth == 0).then(|| format!("{pad}{lhs} = {};", peel(expr)))
}

/// Drops each `(E) & 0xffffffff` whose `E` is already an `unsigned int`
/// ([`is_unsigned32`]), and the parentheses that only held it together:
/// a pair around it, an index's, or an assigned value's.
///
/// # Arguments
///
/// * `line` - One line of the text.
/// * `unsigned32` - The variables declared `uint32_t`.
fn drop_unsigned_masks(line: &str, unsigned32: &BTreeSet<String>) -> String {
    let needle = format!("){MASK32}");
    let mut out = line.to_owned();
    let mut from = 0;
    while let Some(at) = out
        .get(from..)
        .and_then(|t| t.find(&needle))
        .map(|k| k + from)
    {
        from = at + 1;
        let after = at + needle.len();
        if out
            .get(after..)
            .is_some_and(|t| t.starts_with(|c: char| c.is_ascii_hexdigit()))
        {
            continue;
        }
        let Some(open) = opening_paren(&out, at) else {
            continue;
        };
        if !is_unsigned32(out.get(open + 1..at).unwrap_or(""), unsigned32) {
            continue;
        }
        out.replace_range(at + 1..after, "");
        let (mut o, mut c) = (open, at);
        while o > 0 {
            match (out.get(o - 1..o), out.get(c + 1..c + 2)) {
                (Some("("), Some(")")) => {
                    out.replace_range(c + 1..c + 2, "");
                    out.replace_range(o - 1..o, "");
                    o -= 1;
                    c -= 1;
                }
                (Some("["), Some("]")) => {
                    out.replace_range(c..=c, "");
                    out.replace_range(o..=o, "");
                    break;
                }
                (Some(" "), Some(";" | ")" | ",")) if o >= 2 && out.get(o - 2..o) == Some("= ") => {
                    out.replace_range(c..=c, "");
                    out.replace_range(o..=o, "");
                    break;
                }
                _ => break,
            }
        }
        from = o;
    }
    out
}

/// Tells whether a line declares variables rather than doing anything.
///
/// A declaration names a type, then names, then a semicolon, with no
/// assignment and no call; the names in it say nothing about their width.
///
/// # Arguments
///
/// * `line` - One emitted line.
pub(super) fn is_declaration(line: &str) -> bool {
    let t = line.trim();
    t.ends_with(';')
        && !t.contains('=')
        && !t.contains('(')
        && t.split_once(' ').is_some_and(|(head, _)| {
            narrow_type(head).is_some()
                || matches!(head, "uint64_t" | "uint128_t" | "float" | "double")
        })
}

/// Names a declaration already gives a narrow integer type, with that type.
///
/// A `uint64_t` line is not one of these: [`type_locals`] retypes those
/// from their uses. A pointer declaration is not one either.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
pub(super) fn narrow_declarations(lines: &[String]) -> Vec<(String, &'static str)> {
    /// Longest first, so `unsigned int` is not read as `unsigned`.
    const DECLS: &[&str] = &[
        "unsigned char",
        "unsigned short",
        "unsigned int",
        "unsigned long",
        "signed char",
        "int32_t",
        "int16_t",
        "int8_t",
        "uint32_t",
        "uint16_t",
        "uint8_t",
        "HRESULT",
        "BOOLEAN",
        "wchar_t",
        "unsigned",
        "DWORD",
        "ULONG",
        "SHORT",
        "UINT",
        "WORD",
        "BYTE",
        "LONG",
        "INT",
        "short",
        "bool",
        "char",
        "long",
        "int",
    ];
    let mut out = Vec::new();
    for line in lines {
        let t = line.trim();
        if t.starts_with("//") || t.contains('=') || t.contains('(') || !t.ends_with(';') {
            continue;
        }
        let Some(ty) = DECLS
            .iter()
            .copied()
            .find(|ty| t.starts_with(ty) && t.as_bytes().get(ty.len()).is_some_and(|c| *c == b' '))
        else {
            continue;
        };
        if narrow_type(ty).is_none() {
            continue;
        }
        let Some(names) = t[ty.len()..].trim().strip_suffix(';') else {
            continue;
        };
        if names.is_empty() || !names.split(", ").all(is_ident) {
            continue;
        }
        for name in names.split(", ") {
            out.push((name.to_owned(), ty));
        }
    }
    out
}

/// Removes one variable's redundant casts and masks from a line of a 64-bit
/// function's text.
///
/// # Arguments
///
/// * `line` - The line.
/// * `name` - The variable.
/// * `casts` - Cast prefixes the declared type makes redundant.
/// * `mask` - Mask width the declared type makes redundant.
pub(super) fn strip_width(line: &str, name: &str, casts: &[&str], mask: Option<u8>) -> String {
    unwrap_parens(&strip_casts(line, name, casts, mask, true), name)
}

/// Removes one variable's redundant casts and masks from a line.
///
/// A mask's own grouping parentheses go with it when the character before
/// them is not a name and they are not the parentheses of `if`, `while`,
/// or `switch`. `(float)(a1 & 0xffffffff)` becomes `(float)a1`.
/// `foo(a1 & 0xffffffff)` and `switch (a1 & 0xffff)` keep their parentheses.
/// Any other parentheses stay for [`unwrap_parens`].
///
/// A narrow type computes in `int` or `unsigned int` where the masked or
/// extended value computed in the machine's 64 bits: `(a2 & 0xffffffff) <<
/// 0xa` keeps the bits shifted past 32, `a2 << 0xa` of a `uint32_t` loses
/// them. Where a shift or a product by a constant would lose bits
/// ([`loses_bits`]), the variable is cast to the machine's word instead.
/// Equality with a constant other than zero keeps its width cast: that
/// cast is the partial register the compare read, and a zero test is the
/// comparison the declared width already is.
///
/// # Arguments
///
/// * `line` - The line.
/// * `name` - The variable.
/// * `casts` - Cast prefixes the declared type makes redundant.
/// * `mask` - Mask width the declared type makes redundant.
/// * `wide` - The machine's word is 64 bits.
fn strip_casts(line: &str, name: &str, casts: &[&str], mask: Option<u8>, wide: bool) -> String {
    let mut out = String::with_capacity(line.len());
    let mut from = 0;
    for at in word_positions(line, name) {
        if at < from {
            continue;
        }
        let head = line.get(..at).unwrap_or("");
        let tail = line.get(at + name.len()..).unwrap_or("");
        let wrapped = casts.iter().find(|cast| {
            tail.starts_with(')')
                && head.len() > cast.len()
                && head.as_bytes().get(head.len() - 1) == Some(&b'(')
                && head
                    .get(..head.len() - 1)
                    .is_some_and(|h| h.ends_with(*cast))
        });
        let found = wrapped.or_else(|| casts.iter().find(|cast| head.ends_with(*cast)));
        let start = match (found, wrapped.is_some()) {
            (Some(cast), true) => at - cast.len() - 1,
            (Some(cast), false) => at - cast.len(),
            (None, _) => at,
        };
        let mut end = at + name.len() + usize::from(wrapped.is_some());
        let mut masked = false;
        if let Some(bits) = mask_width(line.get(end..).unwrap_or(""))
            && mask == Some(bits)
        {
            end += mask_text(bits).len();
            masked = true;
        }
        let wrapped_mask = masked
            && line.get(..start).is_some_and(|h| h.ends_with('('))
            && line.get(end..).is_some_and(|t| t.starts_with(')'));
        let (lo, hi) = if wrapped_mask {
            (start - 1, end + 1)
        } else {
            (start, end)
        };
        let before = line.get(..start - usize::from(wrapped_mask)).unwrap_or("");
        let call = wrapped_mask && before.ends_with(is_ident_char);
        let control = wrapped_mask
            && ["if", "while", "switch"].iter().any(|kw| {
                before
                    .strip_suffix(' ')
                    .and_then(|h| h.strip_suffix(kw))
                    .is_some_and(|h| !h.ends_with(is_ident_char))
            });
        let compared = line
            .get(end..)
            .and_then(|t| t.strip_prefix(" == ").or_else(|| t.strip_prefix(" != ")));
        let keep_eq = !masked
            && found.is_some()
            && compared.is_some_and(|rest| {
                let token: String = rest
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric())
                    .collect();
                !token.is_empty() && token != "0" && token != "0x0"
            });
        if keep_eq {
            out.push_str(line.get(from..end).unwrap_or(""));
            from = end;
            continue;
        }
        let (bits, limit, cast) = match mask {
            Some(32) => (32, 32, "(uint64_t)"),
            Some(b) => (u32::from(b), 31, "(uint64_t)"),
            None => (32, 31, "(int64_t)"),
        };
        let stripped = masked || found.is_some_and(|c| c.starts_with("(int64_t)"));
        if wide
            && stripped
            && loses_bits(
                line.get(..lo).unwrap_or(""),
                line.get(hi..).unwrap_or(""),
                bits,
                limit,
            )
        {
            out.push_str(line.get(from..lo).unwrap_or(""));
            out.push_str(cast);
            out.push_str(name);
            from = hi;
            continue;
        }
        let (keep_from, keep_to) = if wrapped_mask && !call && !control {
            (lo, hi)
        } else {
            (start, end)
        };
        out.push_str(line.get(from..keep_from).unwrap_or(""));
        out.push_str(name);
        from = keep_to;
    }
    out.push_str(line.get(from..).unwrap_or(""));
    out
}

/// Tells whether a narrow operand computes in C other than in the machine.
///
/// An operand of `bits` bits that C computes in a type whose values stop
/// at `limit` bits loses bits where the text shifts it left (after any
/// constant shifts right) or multiplies it by a constant, turns negative
/// where the text compares a difference of it, and wraps, when it is 32
/// bits wide, where the text adds to it or subtracts from it.
///
/// The count of a shift is read when it is a constant (`<< 0x20` of a word
/// does, `<< 8` of a byte does not); any other count may. A product by a
/// constant loses bits when the two lengths add up past the limit. One by
/// anything else may: it computes in the wider of the two types, and the
/// other factor may be narrowed too (`(a2 & 0xffffffff) *
/// (int64_t)(int32_t)a1` would be `a2 * a1`, a 32-bit product).
///
/// # Arguments
///
/// * `before` - The text before the operand.
/// * `after` - The text after it.
/// * `bits` - The operand's width.
/// * `limit` - The bits its C type holds: 31 for `int`, 32 for `unsigned
///   int`.
fn loses_bits(before: &str, after: &str, bits: u32, limit: u32) -> bool {
    let constant = |t: &str| -> Option<u64> {
        let token: String = t
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric())
            .collect();
        match token.strip_prefix("0x") {
            Some(hex) => u64::from_str_radix(hex, 16).ok(),
            None => token.parse().ok(),
        }
    };
    let length = |k: u64| 64 - k.leading_zeros();
    if let Some(rest) = after.strip_prefix(" - ") {
        let rest = rest.trim_start_matches(|c: char| c.is_ascii_alphanumeric() || c == '_');
        if [" < ", " <= ", " > ", " >= "]
            .iter()
            .any(|rel| rest.starts_with(rel))
        {
            return true;
        }
    }
    if bits >= 32
        && [" + ", " - "].iter().any(|op| {
            after
                .strip_prefix(op)
                .is_some_and(|t| narrow_operand(t, true))
                || before
                    .strip_suffix(op)
                    .is_some_and(|t| narrow_operand(t, false))
        })
    {
        return true;
    }
    let mut shifted = u64::from(bits);
    let mut rest = after;
    loop {
        let (count, left) = match (rest.strip_prefix(" >> "), rest.strip_prefix(" << ")) {
            (Some(c), _) => (c, false),
            (None, Some(c)) => (c, true),
            (None, None) => break,
        };
        let Some(k) = constant(count) else {
            return left;
        };
        shifted = if left {
            shifted.saturating_add(k)
        } else {
            shifted.saturating_sub(k)
        };
        if left && shifted > u64::from(limit) {
            return true;
        }
        rest = count.trim_start_matches(|c: char| c.is_ascii_alphanumeric());
    }
    let after_factor = after.strip_prefix(" * ");
    let before_factor = before
        .strip_suffix(" * ")
        .and_then(|head| head.rsplit(|c: char| !c.is_ascii_alphanumeric()).next());
    if after_factor
        .into_iter()
        .chain(before_factor)
        .any(|t| constant(t).is_none())
    {
        return true;
    }
    let factor = after_factor
        .and_then(constant)
        .or_else(|| before_factor.and_then(constant));
    factor.is_some_and(|k| bits + length(k) > limit)
}

/// Tells whether the operand next to a `+` or `-` computes in C no wider
/// than 32 bits.
///
/// A constant that fits 32 bits is, and so is a parenthesized operand a
/// narrow mask or cast makes narrow (`(a2 & 0xffffffff)`, `(uint32_t)x`).
/// A name is taken as wide: its declaration is not on the line.
///
/// # Arguments
///
/// * `text` - The line's text after the operator, or before it.
/// * `forward` - The operand starts `text` (it follows the operator);
///   otherwise it ends `text`.
fn narrow_operand(text: &str, forward: bool) -> bool {
    let operand = if forward {
        match text.strip_prefix('(') {
            Some(_) => text
                .char_indices()
                .scan(0i32, |depth, (k, c)| {
                    *depth += match c {
                        '(' => 1,
                        ')' => -1,
                        _ => 0,
                    };
                    Some((k, *depth))
                })
                .find(|&(_, depth)| depth == 0)
                .and_then(|(k, _)| text.get(..=k)),
            None => text.split([' ', ')', ';', ',']).next(),
        }
    } else if text.ends_with(')') {
        let mut depth = 0i32;
        text.char_indices().rev().find_map(|(k, c)| {
            depth += match c {
                ')' => 1,
                '(' => -1,
                _ => 0,
            };
            (depth == 0).then(|| text.get(k..)).flatten()
        })
    } else {
        text.rsplit([' ', '(', ',']).next()
    };
    let Some(operand) = operand.filter(|o| !o.is_empty()) else {
        return false;
    };
    let constant = match operand.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None => operand.parse::<u64>().ok(),
    };
    if let Some(c) = constant {
        return c <= 0xffff_ffff;
    }
    operand.starts_with('(')
        && ([" & 0xffffffff)", " & 0xffff)", " & 0xff)"]
            .iter()
            .any(|m| operand.ends_with(m))
            || [
                "(uint32_t)",
                "(int32_t)",
                "(uint16_t)",
                "(int16_t)",
                "(uint8_t)",
                "(int8_t)",
            ]
            .iter()
            .any(|c| operand.starts_with(c)))
}

/// Drops the parentheses left around a bare `name` once its cast or mask
/// is gone.
///
/// A call's or a cast's stay, an operator's call among them, and so do
/// those an `if`, a `while` or a `switch` takes: `sub_1020(rax)`,
/// `Ptr<T>::operator ->(a2)` and `switch (a3) {` keep them, where
/// `(rax) + 1` loses them.
///
/// # Arguments
///
/// * `line` - The line.
/// * `name` - The variable.
pub(super) fn unwrap_parens(line: &str, name: &str) -> String {
    let wrapped = format!("({name})");
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(i) = rest.find(&wrapped) {
        let head = rest.get(..i).unwrap_or("");
        out.push_str(head);
        let bound = out
            .chars()
            .next_back()
            .is_some_and(|c| is_ident_char(c) || matches!(c, ')' | ']'));
        let control = ["if", "while", "switch"].iter().any(|kw| {
            out.strip_suffix(' ')
                .and_then(|h| h.strip_suffix(kw))
                .is_some_and(|h| !h.ends_with(is_ident_char))
        });
        let kept = bound || control || ends_in_operator(&out);
        out.push_str(if kept { &wrapped } else { name });
        rest = rest.get(i + wrapped.len()..).unwrap_or("");
    }
    out.push_str(rest);
    out
}

/// Drops a width cast from a zero test when the declaration already says it.
///
/// `test eax, eax` after a call prints `(uint32_t)f() == 0`. The cast is
/// the register the test read, and it hides the call: a zero test of a
/// call, of a pointer, or of a name declared no wider than the cast reads
/// the same without it. A `uint64_t` or `int64_t` that nothing narrowed
/// keeps the cast, because its high half can be set where the low half is
/// zero.
///
/// # Arguments
///
/// * `text` - A decompiled function, types already applied.
pub(super) fn quiet_zero_tests(text: &str) -> String {
    let wide = wide_names(text);
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        if line.starts_with("//") {
            out.push_str(line);
        } else {
            out.push_str(&strip_zero_casts(line, &wide));
        }
        out.push('\n');
    }
    out
}

/// The names a 64-bit integer declaration still lists.
///
/// # Arguments
///
/// * `text` - The function.
fn wide_names(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed
            .strip_prefix("uint64_t ")
            .or_else(|| trimmed.strip_prefix("int64_t "))
            .and_then(|r| r.strip_suffix(';'))
        {
            for name in rest.split(", ") {
                let name = name.trim();
                if is_ident(name) {
                    out.insert(name.to_owned());
                }
            }
        }
        let Some(sig) = trimmed.strip_prefix("// signature: ") else {
            continue;
        };
        let Some(params) = sig
            .rsplit_once('(')
            .and_then(|(_, rest)| rest.rsplit_once(')').map(|(inner, _)| inner))
        else {
            continue;
        };
        for param in params.split(',') {
            let Some((ty, name)) = param.trim().rsplit_once(' ') else {
                continue;
            };
            if matches!(ty.trim(), "uint64_t" | "int64_t") && is_ident(name.trim()) {
                out.insert(name.trim().to_owned());
            }
        }
    }
    out
}

/// Removes width casts on zero tests from one line.
///
/// # Arguments
///
/// * `line` - One line.
/// * `wide` - Names still declared as a 64-bit integer.
fn strip_zero_casts(line: &str, wide: &BTreeSet<String>) -> String {
    const CASTS: [&str; 6] = [
        "(uint32_t)",
        "(int32_t)",
        "(uint16_t)",
        "(int16_t)",
        "(uint8_t)",
        "(int8_t)",
    ];
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some((at, cast)) = CASTS
        .iter()
        .filter_map(|cast| rest.find(cast).map(|at| (at, *cast)))
        .min_by_key(|(at, _)| *at)
    {
        let after = rest.get(at + cast.len()..).unwrap_or("");
        let Some(end) = operand_end(after) else {
            out.push_str(rest.get(..at + 1).unwrap_or(rest));
            rest = rest.get(at + 1..).unwrap_or("");
            continue;
        };
        let operand = after.get(..end).unwrap_or("");
        let following = after.get(end..).unwrap_or("").trim_start();
        let zero = following.starts_with("== 0") || following.starts_with("!= 0");
        let call = operand.contains('(') && !operand.starts_with('(');
        let bare = is_ident(operand);
        let drop_cast = zero && (call || (bare && !wide.contains(operand)));
        out.push_str(rest.get(..at).unwrap_or(""));
        if !drop_cast {
            out.push_str(cast);
        }
        out.push_str(operand);
        rest = after.get(end..).unwrap_or("");
    }
    out.push_str(rest);
    out
}

/// The end of a name, a call, or a parenthesized expression at the start of
/// `text`.
///
/// # Arguments
///
/// * `text` - The text after a cast.
fn operand_end(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    if bytes.first() == Some(&b'(') {
        return balanced_end(text);
    }
    let mut i = 0;
    if bytes
        .first()
        .is_none_or(|c| !c.is_ascii_alphabetic() && *c != b'_')
    {
        return None;
    }
    while bytes
        .get(i)
        .is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_' || *c == b':')
    {
        i += 1;
    }
    if bytes.get(i) == Some(&b'(') {
        i += balanced_end(text.get(i..)?)?;
    }
    Some(i)
}

/// The index just past the `)` that closes a `(` at the start of `text`.
///
/// # Arguments
///
/// * `text` - An expression starting with `(`.
fn balanced_end(text: &str) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i + c.len_utf8());
                }
            }
            _ => {}
        }
    }
    None
}

/// The casts and mask a declared parameter type makes redundant.
///
/// # Arguments
///
/// * `ty` - The type as the header spells it.
///
/// # Returns
///
/// The cast prefixes to drop and the mask width to drop, or `None` for a
/// type that is not a narrow integer (pointers, references, classes).
pub(super) fn narrow_type(ty: &str) -> Option<(&'static [&'static str], Option<u8>)> {
    Some(match ty {
        "int32_t" | "int" | "long" | "INT" | "LONG" | "HRESULT" => {
            (&["(int64_t)(int32_t)", "(int32_t)"][..], None)
        }
        "int16_t" | "short" | "SHORT" => (&["(int64_t)(int16_t)", "(int16_t)"][..], None),
        "int8_t" | "char" | "signed char" => (&["(int64_t)(int8_t)", "(int8_t)"][..], None),
        "uint8_t" | "bool" | "unsigned char" | "BYTE" | "BOOLEAN" => (&["(uint8_t)"][..], Some(8)),
        "uint16_t" | "unsigned short" | "WORD" | "wchar_t" => (&["(uint16_t)"][..], Some(16)),
        "uint32_t" | "unsigned int" | "unsigned" | "DWORD" | "unsigned long" | "ULONG" | "UINT" => {
            (&["(uint32_t)"][..], Some(32))
        }
        _ => return None,
    })
}

/// The mask text for a width, as the renderer spells it.
///
/// # Arguments
///
/// * `bits` - 8, 16 or 32.
pub(super) fn mask_text(bits: u8) -> &'static str {
    match bits {
        8 => " & 0xff",
        16 => " & 0xffff",
        _ => " & 0xffffffff",
    }
}

/// The width a trailing ` & 0xff`, ` & 0xffff` or ` & 0xffffffff` masks
/// to, if `tail` starts with one and nothing wider.
///
/// # Arguments
///
/// * `tail` - The text after an operand.
pub(super) fn mask_width(tail: &str) -> Option<u8> {
    for bits in [32, 16, 8] {
        if let Some(rest) = tail.strip_prefix(mask_text(bits))
            && !rest.starts_with(|c: char| c.is_ascii_hexdigit())
        {
            return Some(bits);
        }
    }
    None
}

#[cfg(test)]
mod paren_tests {
    use super::type_parameters;

    /// A `double` on a 32-bit stack owns the word after it: the signature
    /// drops that word unless the body reads it by itself.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_double_takes_the_word_after_it_on_a_32_bit_stack() {
        let text = concat!(
            "// signature: uint32_t f(void *this, double a2, uint32_t a3, double a4, uint32_t a5)\n",
            "return a2 > a4 && (a5 & 0x80000000) == 0;\n",
        );
        let typed = type_parameters(text, "uint32_t");
        let sig = typed.lines().next().unwrap_or("");
        assert!(
            sig.ends_with("(void *this, double a2, double a4, uint32_t a5)"),
            "{sig}"
        );
    }

    /// A cast in front of a field read casts the field, not the pointer.
    ///
    /// `(int32_t)a1->field_0x0` compares the field signed; `a1` stays the
    /// pointer the layout pass named the field on.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_cast_before_a_field_read_types_the_field() {
        let text = concat!(
            "// signature: uint32_t f(uint64_t a1, int32_t a2)\n",
            "// layout a1: 0x0 u32, 0x8 u32\n",
            "if (a2 >= (int32_t)a1->field_0x0) {\n",
            "  return a2 < (int32_t)a1->field_0x8;\n",
            "}\n",
            "return 0;\n",
        );
        let typed = type_parameters(text, "uint64_t");
        let sig = typed.lines().next().unwrap_or("");
        assert!(sig.contains("(void *a1, int32_t a2)"), "{sig}");
    }

    /// A parameter the body loads or stores through is a pointer, one on
    /// the stack included.
    ///
    /// It is typed by what it points at only when it is read at its start.
    /// An index into an absolute address, a parameter the body reassigns
    /// and one it uses only as a number are no pointers.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_parameter_loaded_through_is_a_pointer() {
        let text = concat!(
            "// signature: uint32_t f(uint32_t a1, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5, uint32_t a6, uint32_t a7)\n",
            "edx = *(uint32_t*)(a1 + 0x3c);\n",
            "*(uint32_t*)a2 = edx;\n",
            "*(uint32_t*)(a2 + 4) = 0;\n",
            "eax = *(uint8_t*)(a3 + 0x4d1234);\n",
            "a4 = sub_1(a4);\n",
            "*(uint32_t*)a4 = 0;\n",
            "*(uint16_t*)a7 = 0;\n",
            "return a5 + a6->field_0x8;\n",
        );
        let typed = type_parameters(text, "uint32_t");
        let sig = typed.lines().next().unwrap_or("");
        assert!(sig.contains("(void *a1, void *a2, uint32_t a3,"), "{sig}");
        assert!(
            sig.contains("uint32_t a4, uint32_t a5, void *a6, uint16_t *a7)"),
            "{sig}"
        );
    }

    /// A switch on a narrowed parameter keeps the parentheses C requires
    /// around the value, and an operator's call those of its argument: the
    /// mask or cast the type makes redundant goes, and they stay.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_narrowed_parameter_keeps_the_parentheses_c_requires() {
        let text = "// signature: void f(uint16_t a1)
switch (a1 & 0xffff) {
case 5: {
  return;
}
}
if (a1 & 0xffff) {
  return;
}
";
        let typed = type_parameters(text, "uint64_t");
        assert!(typed.contains("switch (a1) {"), "{typed}");
        assert!(typed.contains("if (a1) {"), "{typed}");
        assert_eq!(
            super::unwrap_parens("rax = Ptr<Item>::operator ->(a2);", "a2"),
            "rax = Ptr<Item>::operator ->(a2);"
        );
    }

    /// Two parameters the text widens before multiplying keep a 64-bit
    /// product once both are narrowed.
    ///
    /// `(a2 & 0xffffffff) * (int64_t)(int32_t)a1` multiplies in 64 bits;
    /// `a2 * a1` of a `uint32_t` and an `int32_t` would multiply in 32 and
    /// lose the high half, so each factor keeps a cast to the word.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_product_of_narrowed_parameters_stays_wide() {
        let text = "// signature: uint64_t f(uint64_t a1, uint64_t a2, uint64_t a3)\nreturn (a2 & 0xffffffff) * (int64_t)(int32_t)a1 + a3 * 3;\n";
        let typed = type_parameters(text, "uint64_t");
        assert!(
            typed.contains("f(int32_t a1, uint32_t a2, uint64_t a3)"),
            "{typed}"
        );
        assert!(
            typed.contains("return (uint64_t)a2 * (int64_t)a1 + a3 * 3;"),
            "{typed}"
        );
    }

    /// Narrowing a parameter drops the parentheses of a cast around it,
    /// never the parentheses of a call it is the one argument of.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_narrowed_parameter_keeps_its_call_parentheses() {
        let text = "// signature: uint64_t f(uint64_t a1)\nrax = sub_1(a1);\nif ((uint32_t)a1 == 0) {\n  return (a1);\n}\n";
        let typed = type_parameters(text, "uint64_t");
        assert!(typed.contains("sub_1(a1)"), "{typed}");
        assert!(!typed.contains("sub_1a1"), "{typed}");
    }
}

#[cfg(test)]
mod pointer_tests {
    use crate::analysis::decompile::polish;
    use crate::pack::Packs;

    /// The text's offsets count bytes, as the instructions do, also through
    /// a parameter typed as a pointer to something wider.
    ///
    /// C scales a typed pointer's arithmetic by its pointee, so a load of
    /// the pointee's own type at a multiple of its size is that element, a
    /// step by such a multiple counts elements, and every other operand
    /// reads the pointer as its address, a class's `this` and a local's
    /// address included. A byte pointer, a `void *`, a byte's address and a
    /// loaded value keep their arithmetic.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_typed_pointer_keeps_its_byte_offsets() {
        let text = concat!(
            "// f @ 0x1000: 9 instructions, 1 blocks\n",
            "// signature: uint64_t Game::Item::f(Game::Item *this, uint32_t *a2, uint16_t *a3, uint8_t *a4, void *a5, uint64_t *a6)\n",
            "uint32_t local_28;\n",
            "uint8_t local_8;\n",
            "uint64_t rax, rcx;\n",
            "\n",
            "if (*(uint32_t*)(a2 + 0x14) != 0) {\n",
            "  return *(uint16_t*)(a2 + 6);\n",
            "}\n",
            "a3 += 2;\n",
            "a6 += rcx;\n",
            "rax = sub_1(this + 0x48, rcx - a3, a2 - a3 + rcx, *(uint64_t*)a6 + 1);\n",
            "rax = sub_2(\"a2 + 1\", *(uint64_t*)(a6 + rcx * 8));\n",
            "a3 -= a6;\n",
            "local_8 = -a3 + *(uint8_t*)(&local_28 + rcx) + *(uint8_t*)(&local_8 + rcx);\n",
            "return *(uint8_t*)(a4 + 3) + *(uint32_t*)(a5 + 8) + this->field_0x10;\n",
        );
        let out = polish(text, 64, &Packs::default());
        for want in [
            "if (a2[5] != 0) {",
            "  return *(uint16_t*)((uintptr_t)a2 + 6);",
            "a3 += 1;",
            "a6 = (uint64_t *)((uintptr_t)a6 + rcx);",
            "sub_1((uintptr_t)this + 0x48, rcx - (uintptr_t)a3, (uintptr_t)a2 - (uintptr_t)a3 + rcx, *(uint64_t*)a6 + 1);",
            "sub_2(\"a2 + 1\", a6[rcx]);",
            "a3 = (uint16_t *)((uintptr_t)a3 - (uintptr_t)a6);",
            "local_8[0] = -(uintptr_t)a3 + *(uint8_t*)((uintptr_t)local_28 + rcx) + *(uint8_t*)(local_8 + rcx);",
            "return *(uint8_t*)(a4 + 3) + *(uint32_t*)(a5 + 8) + this->field_0x10;",
        ] {
            assert!(out.lines().any(|l| l == want), "{want}\n{out}");
        }
    }
}

#[cfg(test)]
mod accessor_tests {
    use super::accessor_class;

    /// A smart pointer's dereference or getter returns its template
    /// argument; a container's element access returns the element class;
    /// a plain element or a method that is no accessor returns nothing.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn accessors_return_the_template_argument() {
        assert_eq!(
            accessor_class("Core::Ptr<Game::OfferGroup>::operator ->"),
            Some("Game::OfferGroup")
        );
        assert_eq!(
            accessor_class("std::unique_ptr<Foo,std::default_delete<Foo> >::get"),
            Some("Foo")
        );
        assert_eq!(
            accessor_class("Util::Array<Core::Ptr<Game::Offer> >::operator []"),
            Some("Core::Ptr<Game::Offer>")
        );
        assert_eq!(
            accessor_class("Util::Array<unsigned int>::operator []"),
            None
        );
        assert_eq!(accessor_class("Core::Ptr<Game::OfferGroup>::Release"), None);
        assert_eq!(accessor_class("Game::OfferGroup::get"), None);
    }
}

#[cfg(test)]
mod declared_cast_tests {
    use super::type_locals;

    /// A masked value written to a narrow local the mask covers loses the
    /// mask; a narrower mask, a mask under `|`, and a wider local keep it.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_narrow_local_drops_the_mask_of_what_it_stores() {
        let text = concat!(
            "uint32_t local_dc, local_d0;
",
            "uint8_t local_8a;
",
            "uint64_t local_c0;
",
            "
",
            "local_dc = a1 & 0xffffffff;
",
            "local_d0 = (a2 + a1) & 0xffffffff;
",
            "local_8a = (a2 >> 3) & 0xffff;
",
            "local_dc = a2 & 0xffff;
",
            "local_d0 = a1 | a2 & 0xffffffff;
",
            "local_c0 = a1 & 0xffffffff;
",
            "return local_dc + local_d0 + local_8a + local_c0;
",
        );
        let out = type_locals(text);
        assert!(out.contains("local_dc = a1;"), "{out}");
        assert!(out.contains("local_d0 = a2 + a1;"), "{out}");
        assert!(out.contains("local_8a = a2 >> 3;"), "{out}");
        assert!(out.contains("local_dc = a2 & 0xffff;"), "{out}");
        assert!(out.contains("local_d0 = a1 | a2 & 0xffffffff;"), "{out}");
        assert!(out.contains("local_c0 = a1 & 0xffffffff;"), "{out}");
    }

    /// A local already declared at the cast's width does not need the cast.
    /// A different width, a cast of a sum, a nonzero equality, and a zero
    /// test of a `uint64_t` stay.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_name_declared_at_the_cast_width_drops_the_cast() {
        let text = concat!(
            "uint32_t var1;\n",
            "int32_t var2;\n",
            "uint64_t var3;\n",
            "\n",
            "if ((uint32_t)var1 < 5) {\n",
            "  return var1;\n",
            "}\n",
            "if ((uint32_t)(var1) != 0) {\n",
            "  return 1;\n",
            "}\n",
            "if ((uint32_t)var2 == 6) {\n",
            "  return 2;\n",
            "}\n",
            "if ((int32_t)(var2 + 1) < 0) {\n",
            "  return 3;\n",
            "}\n",
            "var3 = var3 << 4;\n",
            "if ((uint32_t)var3 != 0) {\n",
            "  return 4;\n",
            "}\n",
        );
        let out = type_locals(text);
        assert!(out.contains("if (var1 < 5) {"), "{out}");
        assert!(out.contains("if (var1 != 0) {"), "{out}");
        assert!(!out.contains("(uint32_t)var1"), "{out}");
        assert!(!out.contains("(uint32_t)(var1)"), "{out}");
        assert!(out.contains("if ((uint32_t)var2 == 6) {"), "{out}");
        assert!(out.contains("if ((int32_t)(var2 + 1) < 0) {"), "{out}");
        assert!(out.contains("if ((uint32_t)var3 != 0) {"), "{out}");
        assert!(out.contains("uint64_t var3;"), "{out}");
    }

    /// A 32-bit mask over arithmetic C already does in `unsigned int`
    /// changes nothing, so it goes, with the parentheses it needed.
    ///
    /// `var1` and `var2` are `uint32_t`, so `(var2 - var1) & 0xffffffff`
    /// is `var2 - var1`; `a2` is wider and a constant past `INT_MAX` is not
    /// an `int`, so those masks stay.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_mask_over_unsigned_int_arithmetic_goes() {
        let text = concat!(
            "uint32_t var1, var2;\n",
            "\n",
            "var1 = ((var2 - var1) & 0xffffffff) >> 1;\n",
            "var2 = a1[((var1 + 1) & 0xffffffff)];\n",
            "var1 = ((var2 + var1) & 0xffffffff);\n",
            "return ((a2 - var1) & 0xffffffff) + ((var1 ^ 0x80000000) & 0xffffffff);\n",
        );
        let out = type_locals(text);
        assert!(out.contains("var1 = (var2 - var1) >> 1;"), "{out}");
        assert!(out.contains("var2 = a1[var1 + 1];"), "{out}");
        assert!(out.contains("var1 = var2 + var1;"), "{out}");
        assert!(out.contains("((a2 - var1) & 0xffffffff)"), "{out}");
        assert!(out.contains("((var1 ^ 0x80000000) & 0xffffffff)"), "{out}");
    }
}

#[cfg(test)]
mod zero_tests {
    use super::quiet_zero_tests;

    /// A zero test of a call drops the register cast. A `uint64_t` the
    /// function also uses whole keeps it, and a store of a parameter at 32
    /// bits declares the parameter at that width.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_zero_test_of_a_call_drops_its_cast() {
        let text = concat!(
            "// signature: uint32_t f(uint64_t a1, uint64_t a2)\n",
            "uint64_t var1;\n",
            "\n",
            "if ((uint32_t)sub_1() != 0) {\n",
            "  *(uint32_t*)a2 = a1;\n",
            "}\n",
            "var1 = var1 + a2;\n",
            "if ((uint32_t)var1 != 0) {\n",
            "  return a1;\n",
            "}\n",
            "return 0;\n",
        );
        let out = super::type_parameters(text, "uint64_t");
        let out = quiet_zero_tests(&super::type_locals(&out));
        assert!(out.contains("if (sub_1() != 0)"), "{out}");
        assert!(!out.contains("(uint32_t)sub_1"), "{out}");
        assert!(out.contains("uint32_t a1"), "{out}");
        assert!(out.contains("*(uint32_t*)a2 = a1;"), "{out}");
        assert!(out.contains("(uint32_t)var1 != 0"), "{out}");
    }
}

/// The variables a function holds only declared results in, with the type
/// the declarations give them.
///
/// A variable every write of which is `v = f(...);`, where each `f` is a
/// callee whose declaration returns the same type (`HANDLE` from
/// `CreateFileW`), holds a value of that type wherever the text names it,
/// so it is declared of that type: the declaration says what the value
/// is, where `uint64_t` says only how wide. A variable written any other
/// way (a compound assignment, an increment, a `for` header, a second
/// type), or whose address is taken, keeps the type the lifting gave it.
///
/// # Arguments
///
/// * `body` - The function's body text.
/// * `returns` - Declared callee text to the type it returns, for the
///   callees whose results the text binds.
///
/// # Returns
///
/// Variable name to type, for the variables that qualify.
pub(super) fn typed_results(
    body: &str,
    returns: &BTreeMap<String, String>,
) -> BTreeMap<String, String> {
    /// Operators that write the variable before them.
    const WRITES: [&str; 12] = [
        "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "++", "--",
    ];
    if returns.is_empty() {
        return BTreeMap::new();
    }
    let mut typed: BTreeMap<String, Option<&str>> = BTreeMap::new();
    let code = || body.lines().filter(|l| !l.trim_start().starts_with("//"));
    for line in code() {
        let t = line.trim();
        let Some((lhs, rhs)) = t.split_once(" = ") else {
            continue;
        };
        if !is_ident(lhs) {
            continue;
        }
        let ty = rhs
            .split_once('(')
            .and_then(|(callee, _)| returns.get(callee))
            .filter(|_| rhs.ends_with(");"))
            .map(String::as_str);
        let entry = typed.entry(lhs.to_owned()).or_insert(ty);
        if *entry != ty {
            *entry = None;
        }
    }
    typed.retain(|_, ty| ty.is_some());
    for line in code() {
        let t = line.trim();
        for (var, ty) in &mut typed {
            for (i, _) in t.match_indices(var.as_str()) {
                let before = t.get(..i).unwrap_or("");
                let after = t.get(i + var.len()..).unwrap_or("");
                if before.ends_with(is_ident_char) || after.starts_with(is_ident_char) {
                    continue;
                }
                let plain_write = before.is_empty() && after.starts_with(" = ");
                let other_write = (!before.is_empty() && after.trim_start().starts_with("= "))
                    || WRITES.iter().any(|w| after.trim_start().starts_with(w))
                    || before.ends_with("++")
                    || before.ends_with("--")
                    || before.ends_with('&');
                if other_write && !plain_write {
                    *ty = None;
                }
            }
        }
    }
    typed
        .into_iter()
        .filter_map(|(var, ty)| Some((var, ty?.to_owned())))
        .collect()
}

#[cfg(test)]
mod float_lane_tests {
    use super::float_lanes;

    /// A register only scalar singles replace the low lane of is a `float`,
    /// and a `float` function's merged `return` returns the lane.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_register_only_singles_write_is_a_float() {
        let text = [
            "// signature: float f(float *a1, uint64_t a2, float a3)",
            "uint64_t var1, var2;",
            "",
            "var2 = 0;",
            "do {",
            "  var2 = (var2 & 0xffffffff00000000) | ((var2 * a3 + a1[var1]) & 0xffffffff);",
            "  var1 += 1;",
            "} while (var1 != a2);",
            "return var2;",
        ]
        .join("\n");
        let out = float_lanes(&text);
        assert!(out.contains("float var2;"), "{out}");
        assert!(out.contains("uint64_t var1;"), "{out}");
        assert!(out.contains("  var2 = var2 * a3 + a1[var1];"), "{out}");
        let ret = "// signature: float g(float a1, float a2)\n\nreturn (a2 & 0xffffffff00000000) | ((a2 - a1) & 0xffffffff);\n";
        assert!(
            float_lanes(ret).contains("return a2 - a1;"),
            "{}",
            float_lanes(ret)
        );
    }

    /// A read of the bits (an integer cast) keeps the register as it was.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_bit_read_keeps_the_merge() {
        let text = [
            "// signature: uint32_t f(float a1)",
            "uint64_t var2;",
            "",
            "var2 = (var2 & 0xffffffff00000000) | ((var2 + a1) & 0xffffffff);",
            "return (uint32_t)var2;",
        ]
        .join("\n");
        let out = float_lanes(&text);
        assert!(out.contains("uint64_t var2;"), "{out}");
        assert!(out.contains("0xffffffff00000000"), "{out}");
    }
}

#[cfg(test)]
mod pointer_call_tests {
    use super::{callable_pointers, float_bit_reads};

    /// A parameter only ever called is a function pointer parameter, and
    /// any other callee is cast to one taking the call's arguments.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn calls_through_pointers_are_typed() {
        let text = [
            "// signature: uint64_t f(uint64_t a1, uint64_t a2)",
            "uint64_t var1;",
            "",
            "var1 = (*a1)(a2);",
            "return (*(*(uint64_t*)(a2 + 8)))(var1, 3);",
        ]
        .join("\n");
        let out = callable_pointers(&text);
        assert!(
            out.contains("uint64_t f(uint64_t (*a1)(uint64_t), uint64_t a2)"),
            "{out}"
        );
        assert!(out.contains("var1 = a1(a2);"), "{out}");
        assert!(
            out.contains(
                "return ((uint64_t (*)(uint64_t, uint64_t))(*(uint64_t*)(a2 + 8)))(var1, 3);"
            ),
            "{out}"
        );
        let global = [
            "// signature: void f(uint64_t a1)",
            "uint64_t var1, var2;",
            "uint64_t g64_1008; // @ 0x1008",
            "",
            "var1 = (*g64_1008)(a1, 1);",
            "var2 = (*g64_1008)(var1, 2);",
        ]
        .join("\n");
        let out = callable_pointers(&global);
        assert!(
            out.contains("uint64_t (*g64_1008)(uint64_t, uint64_t); // @ 0x1008"),
            "{out}"
        );
        assert!(out.contains("var2 = g64_1008(var1, 2);"), "{out}");
        let named = "// signature: void f(uint64_t a1)\n\nmap_err<u8, u8 (*)(u32)>(a1);\n";
        assert_eq!(callable_pointers(named), named);
        assert!(out.contains("uint64_t var1, var2;"), "{out}");
    }

    /// A bitwise operation on a float parameter reads its bits; an
    /// arithmetic one keeps the value.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn bitwise_reads_of_a_float_read_its_bits() {
        let text = "// signature: uint32_t f(float a1, double a2)\nreturn (a1 & 0x7fffffff) + (a2 >> 52) + (uint32_t)(a1 * 2);\n";
        let out = float_bit_reads(text);
        assert!(out.contains("(*(uint32_t*)&a1 & 0x7fffffff)"), "{out}");
        assert!(out.contains("(*(uint64_t*)&a2 >> 52)"), "{out}");
        assert!(out.contains("(uint32_t)(a1 * 2)"), "{out}");
    }
}

#[cfg(test)]
mod stack_array_tests {
    use super::stack_arrays;

    /// Slots a computed index reads through the first one's address are
    /// one array; slots only named directly stay apart.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn an_indexed_run_of_slots_is_an_array() {
        let text = [
            "// signature: uint32_t f(uint64_t a1)",
            "uint64_t local_28, local_20, local_18, local_8;",
            "",
            "local_28 = 1;",
            "local_20 = 2;",
            "local_18 = 3;",
            "local_8 = 4;",
            "return ((uint32_t*)&local_28)[a1 & 3] + local_8;",
        ]
        .join("\n");
        let out = stack_arrays(&text);
        assert!(out.contains("uint64_t local_28[3];"), "{out}");
        assert!(out.contains("uint64_t local_8;"), "{out}");
        assert!(out.contains("local_28[1] = 2;"), "{out}");
        assert!(out.contains("local_28[2] = 3;"), "{out}");
        assert!(out.contains("((uint32_t*)local_28)[a1 & 3]"), "{out}");
        let direct = "uint64_t local_28, local_20;\n\nreturn local_28 + local_20;\n";
        assert_eq!(stack_arrays(direct), direct);
    }

    /// A lone indexed slot is the object up to the next slot the text
    /// names, and a member of an indexed run is no object of its own.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_lone_indexed_slot_runs_up_to_the_next_named_one() {
        let text = [
            "// signature: uint32_t f(uint64_t a1)",
            "uint32_t local_5c, local_c;",
            "uint64_t local_58;",
            "",
            "local_c = a1;",
            "((uint32_t*)&local_58)[local_5c] = 1;",
            "return ((uint32_t*)&local_58)[local_c & 0xf];",
        ]
        .join("\n");
        let out = stack_arrays(&text);
        assert!(out.contains("uint64_t local_58[10];"), "{out}");
        assert!(
            out.contains("return ((uint32_t*)local_58)[local_c & 0xf];"),
            "{out}"
        );
        let run = [
            "uint64_t local_28, local_20;",
            "",
            "((uint32_t*)&local_28)[a1] = 1;",
            "return ((uint8_t*)&local_20)[a1];",
        ]
        .join("\n");
        let out = stack_arrays(&run);
        assert!(out.contains("uint64_t local_28[2];"), "{out}");
        assert!(out.contains("((uint8_t*)&local_28[1])[a1]"), "{out}");
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod char_index_tests {
    use super::spell_index;

    /// A byte load through a `char` pointer is the element it reads.
    ///
    /// The signed read stays as it is, the unsigned one is cast, a store
    /// and a zero test take no cast, an index's own parentheses go, and a
    /// pointer to something else is untouched.
    #[test]
    fn a_byte_load_through_a_char_pointer_is_an_element() {
        let text = [
            "// signature: int f(const char *str, int *n, char *out)",
            "uint64_t var1;",
            "",
            "if (*(int8_t*)(str + var1 + 1) > 127) {",
            "  *(uint8_t*)(out + var1) = 32;",
            "}",
            "if (*(uint8_t*)(str + var1) != 0 && *(uint8_t*)n == 1) {",
            "  return *(uint8_t*)(str + (var1 & 3));",
            "}",
            "return *(int8_t*)str + *(uint8_t*)(str + var1);",
        ]
        .join("\n");
        let out = spell_index(&text);
        assert!(out.contains("if (str[var1 + 1] > 127) {"), "{out}");
        assert!(out.contains("  out[var1] = 32;"), "{out}");
        assert!(
            out.contains("if (str[var1] != 0 && *(uint8_t*)n == 1) {"),
            "{out}"
        );
        assert!(out.contains("return (uint8_t)str[var1 & 3];"), "{out}");
        assert!(out.contains("return *str + (uint8_t)str[var1];"), "{out}");
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod signed_read_tests {
    use super::type_locals;

    /// A `uint32_t` local or global the text only reads sign-extended is
    /// an `int32_t`, and its casts go; one read any other way keeps its
    /// type.
    #[test]
    fn a_name_read_only_signed_is_declared_signed() {
        let text = [
            "// signature: uint32_t f(const char *str)",
            "uint32_t local_10, local_c;",
            "uint32_t limit; // @ 0x4010",
            "",
            "for (local_10 = 0; str[(int64_t)(int32_t)local_10] != 0; local_10 += 1) {",
            "  if ((int32_t)local_10 > (int32_t)limit) {",
            "    return local_c >> 1;",
            "  }",
            "}",
            "return limit;",
        ]
        .join("\n");
        let out = type_locals(&text);
        assert!(out.contains("uint32_t local_c;"), "{out}");
        assert!(out.contains("int32_t local_10;"), "{out}");
        assert!(out.contains("int32_t limit; // @ 0x4010"), "{out}");
        assert!(out.contains("str[local_10] != 0"), "{out}");
        assert!(out.contains("if (local_10 > limit) {"), "{out}");
        let unsigned = text.replace("return local_c >> 1;", "return local_10 >> 1;");
        let out = type_locals(&unsigned);
        assert!(out.contains("uint32_t local_10, local_c;"), "{out}");
        assert!(out.contains("(int64_t)(int32_t)local_10"), "{out}");
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod named_parameter_tests {
    use super::type_parameters;

    /// A parameter the debug information names with a signed type drops
    /// the casts that type makes redundant, as an `aN` one does.
    #[test]
    fn a_named_signed_parameter_drops_its_casts() {
        let text = [
            "// signature: uint32_t f(int total, unsigned int mask)",
            "",
            "return ((int64_t)(int32_t)total >> 5) + (int32_t)total / 3 + (mask & 0xffffffff);",
        ]
        .join("\n");
        let out = type_parameters(&text, "uint64_t");
        assert!(
            out.contains("return (total >> 5) + total / 3 + (mask & 0xffffffff);"),
            "{out}"
        );
    }
}
