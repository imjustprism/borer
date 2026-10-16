//! Types read back from the text: the classes calls return, parameter and local
//! declarations, and value widths.

use super::*;

/// Most singletons whose fields [`decompile_named`] names in one function.
pub(super) const SINGLETONS_MAX: usize = 8;

/// Largest offset from a parameter that reads as a field of what it points
/// at; a load at a larger one indexes an absolute address by the parameter.
const FIELD_OFFSET_MAX: u64 = 0x1_0000;

/// The value types a load through an address is cast to, with their widths
/// in bytes.
const LOAD_TYPES: [(&str, usize); 11] = [
    ("uint8_t", 1),
    ("uint16_t", 2),
    ("uint32_t", 4),
    ("uint64_t", 8),
    ("uint128_t", 16),
    ("int8_t", 1),
    ("int16_t", 2),
    ("int32_t", 4),
    ("int64_t", 8),
    ("float", 4),
    ("double", 8),
];

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

/// Types a parameter by how the body uses it, and drops the casts a
/// declared type makes redundant.
///
/// A parameter the header declares `uint64_t` whose every use is a
/// sign-extension from one width (`(int64_t)(int32_t)a2`, `(int32_t)a2`)
/// or a mask to one width (`a3 & 0xff`) was that narrower type in the
/// source: the header says so (`int32_t a2`, `uint8_t a3`) and the casts
/// and masks go, as C promotes the declared type the same way. A parameter
/// the header already declares narrow (`int a2` from an assert, `bool a3`)
/// keeps its type and loses the casts and masks that agree with it
/// ([`narrow_type`]). One the body loads or stores through is a pointer
/// ([`pointed_at`]). On a 32-bit target the word after a `double` is the
/// double's high half, not a parameter ([`drop_high_halves`]).
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `word` - The type a parameter has when nothing declared one, the
///   machine word (`uint32_t` on a 32-bit target): the one type that means
///   "unknown" rather than "declared this wide".
///
/// # Returns
///
/// The text with the parameters typed.
pub(super) fn type_parameters(text: &str, word: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let Some(sig) = lines.iter().position(|l| l.starts_with("// signature: ")) else {
        return text.to_owned();
    };
    if word == "uint32_t" {
        drop_high_halves(&mut lines, sig);
    }
    let params: Vec<(String, String)> = lines[sig]
        .split(['(', ',', ')'])
        .filter_map(|p| {
            let (ty, name) = p.trim().rsplit_once(' ')?;
            is_param_name(name).then(|| (ty.trim().to_owned(), name.to_owned()))
        })
        .collect();
    for (declared, param) in params {
        let ty = if declared != word {
            declared.as_str()
        } else if let Some(found) = inferred_type(&lines, &param) {
            found
        } else if let Some(pointer) = pointed_at(&lines, &param) {
            retype(&mut lines[sig], word, &param, pointer);
            continue;
        } else {
            continue;
        };
        let Some((casts, mask)) = narrow_type(ty) else {
            continue;
        };
        for line in lines.iter_mut().filter(|l| !l.starts_with("//")) {
            *line = unwrap_parens(
                &strip_casts(line, &param, casts, mask, word == "uint64_t"),
                &param,
            );
        }
        if declared == word {
            retype(&mut lines[sig], word, &param, ty);
        }
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Drops from a 32-bit signature the word after each `double` parameter
/// when the body never names it.
///
/// A `double` on a 32-bit stack is two words, and the second is its high
/// half, which every caller pushes as part of it: listed on its own, the
/// header claims an argument no caller passes. A body that reads the half
/// by itself (to test the sign or the exponent) keeps it.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `sig` - Index of the `// signature:` line.
fn drop_high_halves(lines: &mut [String], sig: usize) {
    let number = |name: &str| name.strip_prefix('a')?.parse::<u32>().ok();
    let params: Vec<(String, String)> = lines[sig]
        .split(['(', ',', ')'])
        .filter_map(|p| {
            let (ty, name) = p.trim().rsplit_once(' ')?;
            is_param_name(name).then(|| (ty.trim().to_owned(), name.to_owned()))
        })
        .collect();
    for pair in params.windows(2) {
        let [(ty, name), (next_ty, next)] = pair else {
            continue;
        };
        let follows = number(name)
            .zip(number(next))
            .is_some_and(|(n, m)| n.checked_add(1) == Some(m));
        let named = lines
            .iter()
            .any(|l| !l.starts_with("//") && !word_positions(l, next).is_empty());
        if ty != "double" || next_ty != "uint32_t" || !follows || named {
            continue;
        }
        for end in [",", ")"] {
            lines[sig] = lines[sig].replace(&format!(", uint32_t {next}{end}"), end);
        }
    }
}

/// Rewrites a parameter's type in the signature line from the machine word
/// to `ty`.
///
/// # Arguments
///
/// * `sig` - The `// signature:` line.
/// * `word` - The machine word type the parameter is declared with.
/// * `param` - The parameter name.
/// * `ty` - Its type; a pointer type takes the name without a space.
fn retype(sig: &mut String, word: &str, param: &str, ty: &str) {
    let sep = if ty.ends_with('*') { "" } else { " " };
    for suffix in [",", ")"] {
        let old = format!("{word} {param}{suffix}");
        if sig.contains(&old) {
            *sig = sig.replace(&old, &format!("{ty}{sep}{param}{suffix}"));
        }
    }
}

/// The pointer type the body shows a parameter to be, when it loads or
/// stores through it and never assigns it.
///
/// A load or store through the parameter, `*(T*)a2` or `*(T*)(a2 + 0x10)`,
/// an element read `((T*)a2)[i]`, or a field the layout pass named on it,
/// `a2->field_0x10`, uses its value as an address, which only a pointer
/// is. The pointee follows the register scan's rule ([`pointee_type`]):
/// one width at offset zero is a pointer to that width, anything else
/// `void *`. Reading it off the text sees what the register scan cannot: an
/// argument that arrives on the stack, as every 32-bit `cdecl` and
/// `stdcall` one does. An offset past [`FIELD_OFFSET_MAX`] makes the
/// parameter the index of an absolute address, not a pointer, and a
/// parameter the body assigns, or casts to a narrow integer, is left as
/// it is.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
///
/// # Returns
///
/// The pointer type, or `None` when nothing in the body shows one.
fn pointed_at(lines: &[String], param: &str) -> Option<&'static str> {
    if assigned_values(lines, param) > 0 {
        return None;
    }
    let mut widths: BTreeSet<usize> = BTreeSet::new();
    let mut offsets: BTreeSet<i64> = BTreeSet::new();
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for at in word_positions(line, param) {
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + param.len()..).unwrap_or("");
            if ["(int8_t)", "(int16_t)", "(int32_t)"]
                .iter()
                .any(|c| head.ends_with(c))
            {
                return None;
            }
            if tail.starts_with("->") {
                offsets.extend([0, 1]);
                continue;
            }
            for (ty, width) in LOAD_TYPES {
                let field = head.strip_suffix(&format!("*({ty}*)(")).and_then(|_| {
                    let (sign, rest) = if let Some(r) = tail.strip_prefix(" + ") {
                        (1, r)
                    } else {
                        (-1, tail.strip_prefix(" - ")?)
                    };
                    let k = parse_const(rest.get(..rest.find(')')?)?)?;
                    (k < FIELD_OFFSET_MAX).then(|| sign * i64::try_from(k).unwrap_or(i64::MAX))
                });
                if head.ends_with(&format!("*({ty}*)")) {
                    widths.insert(width);
                    offsets.insert(0);
                } else if let Some(k) = field {
                    widths.insert(width);
                    offsets.insert(k);
                } else if head.ends_with(&format!("(({ty}*)")) && tail.starts_with(")[") {
                    widths.insert(width);
                    offsets.extend([0, 1]);
                }
            }
        }
    }
    (!offsets.is_empty()).then(|| pointee_type(&widths, &offsets))
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
    let mut joined = out.join("\n");
    joined.push('\n');
    joined
}

/// The parameters the signature declares as pointers to something wider
/// than a byte, with their declared types.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
fn typed_pointers(text: &str) -> Vec<(String, String)> {
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
            let pointee = pointee_of(ty)?;
            (is_ident(name) && !BYTE_POINTEES.contains(&pointee))
                .then(|| (name.to_owned(), ty.to_owned()))
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

/// Declares a register variable at the width its uses show, and drops the
/// casts that width makes redundant.
///
/// The same evidence as [`type_parameters`], applied to the locals the
/// emitter declares: a register every use sign-extends from 32 bits was an
/// `int32_t`, one every use masks to a byte was a `uint8_t`. The name moves
/// off the `uint64_t` line onto one of its own type, dropping that line
/// when nothing is left on it, and its casts and
/// masks go, since C promotes the declared type the same way. Only register
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
            if let Some(ty) = inferred_type(&body, &name) {
                narrowed.push((name, ty));
            }
        }
    }
    if narrowed.is_empty() {
        return text.to_owned();
    }
    for (name, ty) in &narrowed {
        let Some((casts, mask)) = narrow_type(ty) else {
            continue;
        };
        for line in &mut lines {
            if line.starts_with("//") || line.starts_with("uint64_t ") {
                continue;
            }
            *line = strip_width(line, name, casts, mask);
        }
    }
    let mut extra: BTreeMap<&'static str, Vec<String>> = BTreeMap::new();
    for (name, ty) in &narrowed {
        extra.entry(*ty).or_default().push(name.clone());
    }
    let taken: BTreeSet<&str> = narrowed.iter().map(|(n, _)| n.as_str()).collect();
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
    let mut out: String = lines
        .into_iter()
        .filter(|l| l != "\u{0}")
        .collect::<Vec<String>>()
        .join("\n");
    out.push('\n');
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

/// Removes one variable's redundant casts and masks from a line, leaving
/// any parentheses that held them.
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
        let found = casts
            .iter()
            .find(|cast| line.get(..at).is_some_and(|h| h.ends_with(*cast)));
        let start = found.map_or(at, |cast| at - cast.len());
        let mut end = at + name.len();
        let mut masked = false;
        if let Some(bits) = mask_width(line.get(end..).unwrap_or(""))
            && mask == Some(bits)
        {
            end += mask_text(bits).len();
            masked = true;
        }
        let (lo, hi) = if masked
            && line.get(..start).is_some_and(|h| h.ends_with('('))
            && line.get(end..).is_some_and(|t| t.starts_with(')'))
        {
            (start - 1, end + 1)
        } else {
            (start, end)
        };
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
        out.push_str(line.get(from..start).unwrap_or(""));
        out.push_str(name);
        from = end;
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
/// constant loses bits when the two lengths add up past the limit; one by
/// a variable is the variable's type's, which the text does not say here.
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
    let factor = after.strip_prefix(" * ").and_then(constant).or_else(|| {
        let head = before.strip_suffix(" * ")?;
        let token = head.rsplit(|c: char| !c.is_ascii_alphanumeric()).next()?;
        constant(token)
    });
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

/// The narrow type every use of a `uint64_t` variable agrees on, if any.
///
/// A variable's own assignment says nothing about its width, since the value
/// is truncated to whatever the variable is declared as, so it is skipped;
/// a parameter never has one.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
pub(super) fn inferred_type(lines: &[String], param: &str) -> Option<&'static str> {
    let mut ty: Option<&'static str> = None;
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for at in word_positions(line, param) {
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + param.len()..).unwrap_or("");
            if head.trim().is_empty() && tail.starts_with(" = ") {
                continue;
            }
            let t = if head.ends_with("(int32_t)") {
                "int32_t"
            } else if head.ends_with("(int16_t)") {
                "int16_t"
            } else if head.ends_with("(int8_t)") {
                "int8_t"
            } else if head.ends_with("(uint32_t)") {
                "uint32_t"
            } else if head.ends_with("(uint16_t)") {
                "uint16_t"
            } else if head.ends_with("(uint8_t)") {
                "uint8_t"
            } else {
                match mask_width(tail)? {
                    8 => "uint8_t",
                    16 => "uint16_t",
                    _ => "uint32_t",
                }
            };
            if ty.is_some_and(|prev| prev != t) {
                return None;
            }
            ty = Some(t);
        }
    }
    ty
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
            "// signature: uint32_t f(void *this, double a2, uint32_t a3, double a4, uint32_t a5)
",
            "return a2 > a4 && (a5 & 0x80000000) == 0;
",
        );
        let typed = type_parameters(text, "uint32_t");
        let sig = typed.lines().next().unwrap_or("");
        assert!(
            sig.ends_with("(void *this, double a2, double a4, uint32_t a5)"),
            "{sig}"
        );
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
            "local_8 = -(uintptr_t)a3 + *(uint8_t*)((uintptr_t)&local_28 + rcx) + *(uint8_t*)(&local_8 + rcx);",
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
