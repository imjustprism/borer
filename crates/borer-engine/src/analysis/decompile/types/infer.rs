//! What the uses of a variable show its type to be: the casts and masks
//! the text applies to it, the stores and returns it fills, and the
//! declared parameters of the calls it is passed to whole.

use super::super::evidence::{argument_of, whole_read};
use super::super::lexer::{Lex, Line, lex};
use super::*;
use crate::analysis::typelib::{self, Pass};
use crate::program::BinaryFormat;

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
/// ([`narrow_type`]), and so does one the debug information names
/// (`int total_stored`) when the type is a signed one, whose casts are
/// all it drops. One the declared calls it is passed to agree is a pointer
/// to a named type is that ([`api_pointer`]): `strlen(a1)` makes a word
/// or a byte pointer a `char *`. An operand whose format, or the
/// `gettext` call that format was assigned from, reads as a string is
/// one too. A `gettext` of a parameter takes the type the callers' string
/// literals agree on for that operand, and says nothing when they do not.
/// One the body loads or stores through is
/// a pointer ([`pointed_at`]), and a `void *` the body reads only bytes
/// through is a byte pointer. On a 32-bit target the word after a `double` is the
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
pub(in crate::analysis::decompile) fn type_parameters(text: &str, word: &str) -> String {
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
            let (ty, name) = match name.strip_prefix('*') {
                Some(n) => (format!("{} *", ty.trim()), n),
                None => (ty.trim().to_owned(), name),
            };
            let named_signed =
                is_ident(name) && narrow_type(&ty).is_some_and(|(_, mask)| mask.is_none());
            (is_param_name(name) || named_signed).then(|| (ty, name.to_owned()))
        })
        .collect();
    for (declared, param) in params {
        let bytes = matches!(declared.as_str(), "void *" | "uint8_t *");
        if (bytes || declared == word)
            && let Some(pointer) = api_pointer(&lines, &param)
            && (!bytes || pointer == "char *")
        {
            retype(&mut lines[sig], &declared, &param, &pointer);
            continue;
        }
        if declared == "void *" && pointed_at(&lines, &param) == Some("uint8_t *") {
            retype(&mut lines[sig], &declared, &param, "uint8_t *");
            continue;
        }
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
    lines.retain(|l| !l.starts_with("// formats "));
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

/// Rewrites a parameter's type in the signature line from the one it is
/// declared with to `ty`.
///
/// # Arguments
///
/// * `sig` - The `// signature:` line.
/// * `word` - The type the parameter is declared with, the machine word
///   or a pointer.
/// * `param` - The parameter name.
/// * `ty` - Its type; a pointer type takes the name without a space.
fn retype(sig: &mut String, word: &str, param: &str, ty: &str) {
    let spaced = |t: &str| if t.ends_with('*') { "" } else { " " };
    let sep = spaced(ty);
    for suffix in [",", ")"] {
        let old = format!("{word}{}{param}{suffix}", spaced(word));
        if sig.contains(&old) {
            *sig = sig.replace(&old, &format!("{ty}{sep}{param}{suffix}"));
        }
    }
}

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
/// it is; a cast in front of `a2->field_0x10` casts the field, not `a2`.
/// A load at the parameter plus a narrow integer, `*(T*)(a2 + local_10)`
/// ([`indexed_by_int`]), indexes from it.
/// The loads through a variable the parameter is copied into and that
/// only steps from there ([`copies`]) count too, at offsets that say only
/// that the pointer moved: bytes read through it make a byte pointer.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
///
/// # Returns
///
/// The pointer type, or `None` when nothing in the body shows one.
pub(in crate::analysis::decompile) fn pointed_at(
    lines: &[String],
    param: &str,
) -> Option<&'static str> {
    if assigned_values(lines, param) > 0 {
        return None;
    }
    let mut widths: BTreeSet<usize> = BTreeSet::new();
    let mut offsets: BTreeSet<i64> = BTreeSet::new();
    accesses(lines, param, &mut widths, &mut offsets)?;
    for copy in copies(lines, param) {
        let mut moved: BTreeSet<i64> = BTreeSet::new();
        accesses(lines, &copy, &mut widths, &mut moved)?;
        if !moved.is_empty() {
            offsets.extend([0, 1]);
        }
    }
    (!offsets.is_empty()).then(|| pointee_type(&widths, &offsets))
}

/// Collects the widths and offsets of the loads and stores through one
/// name, for [`pointed_at`].
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `name` - The name.
/// * `widths` - Access widths in bytes, added to.
/// * `offsets` - Offsets from the name, added to.
///
/// # Returns
///
/// `None` when a use casts the name to a narrow signed integer, which no
/// pointer is.
fn accesses(
    lines: &[String],
    name: &str,
    widths: &mut BTreeSet<usize>,
    offsets: &mut BTreeSet<i64>,
) -> Option<()> {
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for at in word_positions(line, name) {
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + name.len()..).unwrap_or("");
            if tail.starts_with("->") {
                offsets.extend([0, 1]);
                continue;
            }
            if ["(int8_t)", "(int16_t)", "(int32_t)"]
                .iter()
                .any(|c| head.ends_with(c))
            {
                return None;
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
                } else if (head.ends_with(&format!("(({ty}*)")) && tail.starts_with(")["))
                    || (head.ends_with(&format!("*({ty}*)(")) && indexed_by_int(lines, tail))
                {
                    widths.insert(width);
                    offsets.extend([0, 1]);
                }
            }
        }
    }
    Some(())
}

/// Tells whether the text after a name adds a narrow integer to it.
///
/// ` + local_10)` with `local_10` declared an `int32_t`, or ` +
/// (int64_t)(int32_t)i)`, adds an index no pointer is, so the name is the
/// base of the address.
///
/// # Arguments
///
/// * `lines` - The function, declarations included.
/// * `tail` - The text after the name.
fn indexed_by_int(lines: &[String], tail: &str) -> bool {
    let Some(rest) = tail.strip_prefix(" + ") else {
        return false;
    };
    let index = rest.split(')').next().unwrap_or("");
    rest.starts_with("(int64_t)")
        || (is_ident(index)
            && rest.get(index.len()..).is_some_and(|r| r.starts_with(')'))
            && declared_scalar(lines, index).is_some())
}

/// The variables a parameter is copied into whole and that only step
/// from there: `local_10 = a1;` then `local_10 += 2;`, the home an
/// unoptimized build keeps a parameter in.
///
/// A copy assigned anything else as well holds more than the parameter,
/// so it is left out.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
fn copies(lines: &[String], param: &str) -> Vec<String> {
    let whole = format!(" = {param};");
    let mut out: Vec<String> = Vec::new();
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        let Some(dest) = line.trim().strip_suffix(whole.as_str()) else {
            continue;
        };
        if !is_ident(dest) || dest == param || out.iter().any(|c| c == dest) {
            continue;
        }
        let writes = lines
            .iter()
            .filter(|l| {
                l.trim()
                    .strip_prefix(dest)
                    .is_some_and(|r| r.starts_with(" = "))
            })
            .count();
        if writes == 1 {
            out.push(dest.to_owned());
        }
    }
    out
}

/// The narrow type every use of a `uint64_t` variable agrees on, if any.
///
/// A variable's own assignment says nothing about its width, since the value
/// is truncated to whatever the variable is declared as, so it is skipped.
/// Storing it through a typed pointer, or assigning it whole to a variable
/// declared narrow, is that width; returning it from a function whose
/// result is a narrow integer is that result's width; passing it whole as
/// a declared API's narrow integer parameter, or as the value a `printf`
/// conversion reads, is that parameter's type ([`slot_at`]). A postfix use
/// (`a1->field_0x8`, `a1[i]`) binds before any cast in front of it, so it
/// says the variable is no narrow integer.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
pub(in crate::analysis::decompile) fn inferred_type(
    lines: &[String],
    param: &str,
) -> Option<&'static str> {
    inferred_type_on(lines, lines.iter(), param)
}

/// [`inferred_type`] over only the lines that can name the variable.
///
/// Uses of one width that disagree on the sign agree on the signed type:
/// every cast and mask of the other sign stays where it is, and says the
/// same of the low bits.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `uses` - The lines of `lines` to read, in order: every line that
///   names `param` must be among them.
/// * `param` - The variable's name.
///
/// # Returns
///
/// The type every use agrees on, `None` when they disagree or say none.
pub(in crate::analysis::decompile) fn inferred_type_on<'a>(
    lines: &[String],
    uses: impl Iterator<Item = &'a String>,
    param: &str,
) -> Option<&'static str> {
    let mut ty: Option<&'static str> = None;
    for line in uses.filter(|l| !l.starts_with("//")) {
        for at in word_positions(line, param) {
            let head = line.get(..at).unwrap_or("");
            let tail = line.get(at + param.len()..).unwrap_or("");
            if head.trim().is_empty() && tail.starts_with(" = ") {
                continue;
            }
            if tail.starts_with("->") || tail.starts_with(['[', '.']) {
                return None;
            }
            let t = if let Some(cast) = cast_before(head) {
                cast
            } else if let Some(stored) = stored_width(head, tail) {
                stored
            } else if head.trim() == "return" && tail.trim_start().starts_with(';') {
                scalar_width(signature_result(lines)?)?
            } else if let Some(bits) = mask_width(tail) {
                match bits {
                    8 => "uint8_t",
                    16 => "uint16_t",
                    _ => "uint32_t",
                }
            } else if let Some(width) = assigned_width(lines, head, tail) {
                width
            } else {
                match slot_at(line, at)? {
                    Slot::Narrow(t) => t,
                    Slot::Pointer(_) | Slot::Other => return None,
                }
            };
            ty = match ty {
                Some(prev) if prev != t => Some(same_width(prev, t)?),
                _ => Some(t),
            };
        }
    }
    ty
}

/// The narrow integer cast the text ends with, as [`inferred_type`] spells
/// it.
///
/// # Arguments
///
/// * `head` - The line up to a name.
fn cast_before(head: &str) -> Option<&'static str> {
    const CASTS: [(&str, &str); 6] = [
        ("(int32_t)", "int32_t"),
        ("(int16_t)", "int16_t"),
        ("(int8_t)", "int8_t"),
        ("(uint32_t)", "uint32_t"),
        ("(uint16_t)", "uint16_t"),
        ("(uint8_t)", "uint8_t"),
    ];
    CASTS
        .into_iter()
        .find_map(|(cast, ty)| head.ends_with(cast).then_some(ty))
}

/// The one of two integer types of the same width that is signed.
///
/// # Arguments
///
/// * `a` - One type, as [`inferred_type`] spells it.
/// * `b` - The other.
///
/// # Returns
///
/// The signed type, or `None` when the widths differ.
fn same_width(a: &'static str, b: &'static str) -> Option<&'static str> {
    (integer_bits(a)? == integer_bits(b)?).then(|| if a.starts_with('u') { b } else { a })
}

/// The integer width a store of exactly one name writes.
///
/// `*(uint32_t*)p = name` uses the low 32 bits and nothing above them.
/// A store of a sum does not: the sum may have been computed at 64 bits.
///
/// # Arguments
///
/// * `head` - The line up to the name.
/// * `tail` - The line after the name.
fn stored_width(head: &str, tail: &str) -> Option<&'static str> {
    if !tail.trim_start().starts_with(';') {
        return None;
    }
    let dest = head.trim_end().strip_suffix(" =")?.trim();
    let after = dest.strip_prefix("*(")?;
    let ty = after.split_once("*)")?.0.trim();
    scalar_width(ty)
}

/// The integer width an assignment of exactly one name to a variable the
/// text declares narrow keeps: `g32_c72c = a1;` stores the low 32 bits.
///
/// # Arguments
///
/// * `lines` - The function, declarations included.
/// * `head` - The line up to the name.
/// * `tail` - The line after the name.
fn assigned_width(lines: &[String], head: &str, tail: &str) -> Option<&'static str> {
    if !tail.trim_start().starts_with(';') {
        return None;
    }
    let dest = head.trim().strip_suffix(" =")?;
    is_ident(dest)
        .then(|| declared_scalar(lines, dest))
        .flatten()
}

/// The narrow integer a declaration line gives a variable, as
/// [`inferred_type`] spells it.
///
/// # Arguments
///
/// * `lines` - The function, declarations included.
/// * `name` - The variable.
fn declared_scalar(lines: &[String], name: &str) -> Option<&'static str> {
    lines.iter().find_map(|l| {
        let code = l
            .split(" //")
            .next()
            .unwrap_or(l)
            .trim()
            .strip_suffix(';')?;
        if code.contains(['=', '(', '*']) {
            return None;
        }
        let mut names = code.split(", ");
        let (ty, first) = names.next()?.rsplit_once(' ')?;
        (first == name || names.any(|n| n == name))
            .then(|| scalar_width(ty.trim()))
            .flatten()
    })
}

/// The narrow integer a C type name denotes, as [`inferred_type`] spells it.
///
/// # Arguments
///
/// * `ty` - A type as a signature or a cast spells it.
pub(in crate::analysis::decompile) fn scalar_width(ty: &str) -> Option<&'static str> {
    match ty {
        "int32_t" | "int" | "long" | "INT" | "LONG" | "HRESULT" => Some("int32_t"),
        "int16_t" | "short" | "SHORT" => Some("int16_t"),
        "int8_t" | "char" | "signed char" => Some("int8_t"),
        "uint8_t" | "bool" | "unsigned char" | "BYTE" | "BOOLEAN" => Some("uint8_t"),
        "uint16_t" | "unsigned short" | "WORD" | "wchar_t" => Some("uint16_t"),
        "uint32_t" | "unsigned int" | "unsigned" | "DWORD" | "unsigned long" | "ULONG" | "UINT" => {
            Some("uint32_t")
        }
        _ => None,
    }
}

/// The result type on the `// signature:` line.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
pub(in crate::analysis::decompile) fn signature_result(lines: &[String]) -> Option<&str> {
    let sig = lines.iter().find(|l| l.starts_with("// signature: "))?;
    let rest = sig.get("// signature: ".len()..)?.trim();
    let head = rest.split_once('(')?.0.trim();
    let ty = head.rsplit_once(' ')?.0.trim();
    (!ty.is_empty()).then_some(ty)
}

/// What the declared parameter a whole argument fills says of the value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::analysis::decompile) enum Slot {
    /// An integer of 32 bits or fewer, spelled as [`inferred_type`] spells
    /// it.
    Narrow(&'static str),
    /// A pointer to a named type, spelled as a declaration writes it
    /// (`char *`, `FILE *`), its qualifiers dropped.
    Pointer(String),
    /// Anything else: a wider integer, a float, a pointer to `void`, or a
    /// type only one platform's rows size.
    Other,
}

/// Returns what the declared parameter the name at byte `at` of `line` is
/// passed as says of it.
///
/// The callee is a function the type library declares, a POSIX row before
/// a Windows one, and the name its whole argument. A fixed parameter says
/// its type; a variadic argument of a `printf`-like function (one whose
/// last fixed parameter is its `format`) says what the conversion the
/// format literal gives it reads ([`conversion_slot`]). An integer type
/// that the two platforms size differently (`long`) says nothing, and so
/// does a parameter the two declare with different types (`connect`
/// takes an `int` socket on POSIX and a pointer-wide `SOCKET` on
/// Windows): the text does not say which platform it is.
///
/// # Arguments
///
/// * `line` - The line.
/// * `at` - The byte the name starts at.
///
/// # Returns
///
/// The slot, or `None` when the name is no whole argument of a declared
/// call.
pub(in crate::analysis::decompile) fn slot_at(line: &str, at: usize) -> Option<Slot> {
    let l = Line {
        text: line,
        toks: lex(line),
    };
    let k = l.toks.iter().position(|t| t.at == at)?;
    let (callee, index, open) = argument_of(&l, k)?;
    let posix = typelib::declared(callee, BinaryFormat::Elf);
    let windows = typelib::declared(callee, BinaryFormat::Pe);
    let decl = posix.or(windows)?;
    if let Some(p) = decl.params.get(index) {
        let other = posix.and(windows).and_then(|w| w.params.get(index));
        return other.is_none_or(|o| o.ty == p.ty).then(|| slot_of(p.ty));
    }
    let format = decl.params.len().checked_sub(1)?;
    if !decl.variadic || decl.params.get(format)?.name != "format" || callee.contains("scanf") {
        return None;
    }
    let literal = argument_token(&l, open, format)?;
    conversion_slot(l.word(literal), index - decl.params.len())
}

/// What a declared parameter's C type says of the value passed as it.
///
/// # Arguments
///
/// * `ty` - The type as the library spells it (`const char *`, `int`).
fn slot_of(ty: &str) -> Slot {
    let words: Vec<&str> = ty
        .split(|c: char| c == '*' || c.is_whitespace())
        .filter(|w| !w.is_empty() && !matches!(*w, "const" | "volatile" | "restrict"))
        .collect();
    let stars = ty.matches('*').count();
    if ty.contains('(') || words.is_empty() {
        return Slot::Other;
    }
    if stars > 0 {
        if words == ["void"] && stars == 1 {
            return Slot::Other;
        }
        return Slot::Pointer(format!("{} {}", words.join(" "), "*".repeat(stars)));
    }
    let passes = [BinaryFormat::Elf, BinaryFormat::Pe].map(|f| typelib::pass_of(ty, 64, f));
    match passes {
        [Some(Pass::Int { bits, signed }), other] if bits <= 32 && other == passes[0] => {
            Slot::Narrow(int_name(bits, signed))
        }
        _ => Slot::Other,
    }
}

/// The fixed-width name of an integer type, as [`inferred_type`] spells
/// it.
///
/// # Arguments
///
/// * `bits` - 8, 16 or 32.
/// * `signed` - Whether it is signed.
fn int_name(bits: u8, signed: bool) -> &'static str {
    match (bits, signed) {
        (8, true) => "int8_t",
        (8, false) => "uint8_t",
        (16, true) => "int16_t",
        (16, false) => "uint16_t",
        (_, true) => "int32_t",
        (_, false) => "uint32_t",
    }
}

/// The token of argument `index` of the call whose `(` is token `open`,
/// when that argument is exactly one string literal.
///
/// # Arguments
///
/// * `l` - The line.
/// * `open` - The call's `(` token.
/// * `index` - The argument, from zero.
fn argument_token(l: &Line<'_>, open: usize, index: usize) -> Option<usize> {
    let (mut depth, mut commas) = (0usize, 0usize);
    let mut start = Some(open + 1);
    for k in open + 1..l.toks.len() {
        if l.is(k, "(") || l.is(k, "[") {
            depth += 1;
        } else if l.is(k, ")") || l.is(k, "]") {
            if depth == 0 {
                break;
            }
            depth -= 1;
        } else if depth == 0 && l.is(k, ",") {
            commas += 1;
            start = Some(k + 1);
            continue;
        }
        if commas == index && start == Some(k) {
            let single = l.is(k + 1, ",") || l.is(k + 1, ")");
            return (single && l.toks.get(k)?.lex == Lex::Literal).then_some(k);
        }
    }
    None
}

/// What the conversion that reads variadic argument `index` of a `printf`
/// format says of it.
///
/// A `*` width or precision reads an `int` of its own. Without a length
/// modifier an integer conversion reads 32 bits (`%d` an `int`, `%u`,
/// `%x` and `%c` an `unsigned int`), `hh` a `char` and `h` a `short`; `%s`
/// reads a `char *`. Any other conversion (`%p`, `%f`, one with `l`, `z`
/// or `j`) reads a word, a float or something this does not size. glibc's
/// `%m` reads none. A positional argument (`%2$s`) or a conversion this
/// does not know says nothing, since the arguments after it can no longer
/// be counted.
///
/// # Arguments
///
/// * `literal` - The format, as the text spells the literal.
/// * `index` - The variadic argument, from zero.
///
/// # Returns
///
/// The slot, or `None` when the format has no conversion for it.
fn conversion_slot(literal: &str, index: usize) -> Option<Slot> {
    let body = literal.strip_prefix('"')?.strip_suffix('"')?;
    let mut chars = body.chars().peekable();
    let mut n = 0usize;
    let mut take = |slot: Slot| {
        let hit = (n == index).then_some(slot);
        n += 1;
        hit
    };
    while let Some(c) = chars.next() {
        if c != '%' {
            continue;
        }
        if chars.peek() == Some(&'%') {
            chars.next();
            continue;
        }
        let mut length = String::new();
        while let Some(&c) = chars.peek() {
            if c == '*' {
                if let Some(hit) = take(Slot::Narrow("int32_t")) {
                    return Some(hit);
                }
            } else if "hlLqjzt".contains(c) {
                length.push(c);
            } else if c == '$' {
                return None;
            } else if !"-+ #0123456789.'".contains(c) {
                break;
            }
            chars.next();
        }
        let conv = chars.next()?;
        if conv == 'm' {
            continue;
        }
        if !"diouxXcsfFeEgGaApn".contains(conv) {
            return None;
        }
        let signed = matches!(conv, 'd' | 'i');
        let slot = match (conv, length.as_str()) {
            ('d' | 'i' | 'u' | 'x' | 'X' | 'o' | 'c', "") => Slot::Narrow(int_name(32, signed)),
            ('d' | 'i' | 'u' | 'x' | 'X' | 'o', "h") => Slot::Narrow(int_name(16, signed)),
            ('d' | 'i' | 'u' | 'x' | 'X' | 'o', "hh") => Slot::Narrow(int_name(8, signed)),
            ('s', "") => Slot::Pointer("char *".to_owned()),
            _ => Slot::Other,
        };
        if let Some(hit) = take(slot) {
            return Some(hit);
        }
    }
    None
}

/// Tells whether token `k` is an operand of an operator C allows only of
/// an integer: `|`, `^`, `<<`, `>>`, `/`, `%` or `~` on either side, or a
/// binary `&` or `*` after it.
///
/// # Arguments
///
/// * `l` - The line.
/// * `k` - The token.
fn bit_operand(l: &Line<'_>, k: usize) -> bool {
    let text = |j: usize| {
        l.toks
            .get(j)
            .and_then(|t| l.text.get(t.at..t.end))
            .unwrap_or("")
    };
    let integer = |op: &str| {
        matches!(
            op.trim_end_matches('='),
            "|" | "^" | "<<" | ">>" | "/" | "%"
        )
    };
    let before = k.checked_sub(1).map_or("", text);
    let after = text(k + 1);
    integer(before)
        || before == "~"
        || integer(after)
        || matches!(after.trim_end_matches('='), "&" | "*")
}

/// A printf format recovered from the call, or from the `gettext` the
/// format variable was assigned.
enum Resolved {
    /// A string literal, quotes included, as [`conversion_slot`] reads it.
    Literal(String),
    /// `gettext` of a value. The message text is the expression it was called on.
    Message(String),
}

/// The source of argument `index` of the call whose `(` is token `open`.
///
/// # Arguments
///
/// * `l` - The line.
/// * `open` - The call's `(` token.
/// * `index` - The argument, from zero.
///
/// # Returns
///
/// The argument text, or `None` when the call has no such argument.
fn argument_text<'a>(l: &Line<'a>, open: usize, index: usize) -> Option<&'a str> {
    let (mut depth, mut commas) = (0usize, 0usize);
    let mut start = None;
    for k in open + 1..l.toks.len() {
        if l.is(k, "(") || l.is(k, "[") {
            depth += 1;
        } else if l.is(k, ")") || l.is(k, "]") {
            if depth == 0 {
                return (commas == index).then(|| {
                    let end = l.toks.get(k).map_or(l.text.len(), |t| t.at);
                    l.text.get(start.unwrap_or(end)..end).unwrap_or("").trim()
                });
            }
            depth -= 1;
        } else if depth == 0 && l.is(k, ",") {
            if commas == index {
                let end = l.toks.get(k).map_or(l.text.len(), |t| t.at);
                return Some(l.text.get(start.unwrap_or(end)..end).unwrap_or("").trim());
            }
            commas += 1;
            start = None;
            continue;
        }
        if depth == 0 && commas == index && start.is_none() {
            start = Some(l.toks.get(k)?.at);
        }
    }
    None
}

/// The message a `gettext`, `dgettext`, `dcgettext` or `_` call formats.
///
/// # Arguments
///
/// * `expr` - The call, as the text spells it.
///
/// # Returns
///
/// The literal message, [`Resolved::Message`] carrying the message
/// expression when it is a value, or `None` when `expr` is not one of
/// those calls. The call has to be the whole expression: `gettext("%s") + 3`
/// starts at a different conversion, so it says nothing.
fn message_format(expr: &str) -> Option<Resolved> {
    let l = Line {
        text: expr,
        toks: lex(expr),
    };
    if l.toks.len() < 3 || !l.is(1, "(") || l.toks.first()?.lex != Lex::Name {
        return None;
    }
    let name = l.word(0);
    let index = match name {
        "gettext" | "_" => 0,
        "dgettext" | "dcgettext" => 1,
        _ => return None,
    };
    if !call_is_whole(&l) {
        return None;
    }
    let msgid = argument_text(&l, 1, index)?;
    if msgid.starts_with('"') {
        Some(Resolved::Literal(msgid.to_owned()))
    } else {
        Some(Resolved::Message(msgid.to_owned()))
    }
}

/// Tells whether `l` is a call and nothing follows it.
///
/// # Arguments
///
/// * `l` - An expression whose second token is `(`.
///
/// # Returns
///
/// Whether the `)` that closes that call is the last token.
fn call_is_whole(l: &Line<'_>) -> bool {
    let mut depth = 0usize;
    for k in 1..l.toks.len() {
        if l.is(k, "(") {
            depth += 1;
        } else if l.is(k, ")") {
            let Some(next) = depth.checked_sub(1) else {
                return false;
            };
            depth = next;
            if depth == 0 {
                return k + 1 == l.toks.len();
            }
        }
    }
    false
}

/// The one right-hand side assigned to `name` before line `before`.
///
/// An assignment after the call does not reach it. A global (`// @`)
/// can change between the assignment and the call, so it is not followed.
/// A compound assignment or an increment before the use (`format += 3`)
/// moves the text, so that name is not followed either.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `name` - The variable.
/// * `before` - The line index of the use. Earlier lines are the only ones read.
///
/// # Returns
///
/// The right-hand side, or `None` when `name` is a global, is written
/// more than once before the use, or is not assigned before it.
fn sole_rhs<'a>(lines: &'a [String], name: &str, before: usize) -> Option<&'a str> {
    if global_name(lines, name) || assigned_values(&lines[..before], name) != 1 {
        return None;
    }
    let mut found = None;
    for line in lines.iter().take(before).filter(|l| !l.starts_with("//")) {
        let code = line.split("//").next().unwrap_or("").trim();
        let Some(stmt) = code.strip_suffix(';') else {
            continue;
        };
        let Some((lhs, rhs)) = stmt.split_once(" = ") else {
            continue;
        };
        if lhs.trim() != name {
            continue;
        }
        if found.is_some() {
            return None;
        }
        found = Some(rhs.trim());
    }
    found
}

/// Tells whether `name` is a global the text locates with `// @`.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `name` - The variable.
///
/// # Returns
///
/// Whether a declaration of `name` carries an address comment.
fn global_name(lines: &[String], name: &str) -> bool {
    lines.iter().any(|l| {
        let Some((code, note)) = l.split_once("//") else {
            return false;
        };
        note.contains('@')
            && code
                .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .any(|w| w == name)
    })
}

/// The format string `expr` prints, following one assignment of a name.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `expr` - A format argument: a literal, a `gettext` call, or a name.
/// * `depth` - Assignments already followed. Stops at 4.
/// * `before` - The line index of the use. Only an earlier assignment counts.
///
/// # Returns
///
/// The format, or `None` when `expr` is not one of those.
fn resolved_format(lines: &[String], expr: &str, depth: u8, before: usize) -> Option<Resolved> {
    if depth == 4 {
        return None;
    }
    let expr = expr.trim();
    if expr.starts_with('"') && expr.ends_with('"') {
        return Some(Resolved::Literal(expr.to_owned()));
    }
    if let Some(got) = message_format(expr) {
        return Some(got);
    }
    if !is_ident(expr) {
        return None;
    }
    resolved_format(lines, sole_rhs(lines, expr, before)?, depth + 1, before)
}

/// What a variadic format argument is, when the format is not itself a
/// literal on the call.
///
/// The format may be a `gettext` of a literal, or a variable assigned
/// once from one: the conversion then says the operand's type, as
/// [`slot_at`] does for a literal written on the call. A `gettext` of a
/// parameter takes the type the callers' literals agree on
/// ([`agreed_slot`]) and says nothing when that message is unknown.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `line` - The line.
/// * `at` - The byte the operand starts at.
/// * `before` - The index of `line`. Only an earlier assignment of the format counts.
///
/// # Returns
///
/// The slot, or `None` when the call shows none.
fn format_slot(lines: &[String], line: &str, at: usize, before: usize) -> Option<Slot> {
    let l = Line {
        text: line,
        toks: lex(line),
    };
    let k = l.toks.iter().position(|t| t.at == at)?;
    let (callee, index, open) = argument_of(&l, k)?;
    if callee.contains("scanf") {
        return None;
    }
    let posix = typelib::declared(callee, BinaryFormat::Elf);
    let windows = typelib::declared(callee, BinaryFormat::Pe);
    let decl = posix.or(windows)?;
    if posix
        .zip(windows)
        .is_some_and(|(p, w)| p.variadic != w.variadic || p.params.len() != w.params.len())
    {
        return None;
    }
    let format = decl.params.len().checked_sub(1)?;
    if !decl.variadic || decl.params.get(format)?.name != "format" || index < decl.params.len() {
        return None;
    }
    let expr = argument_text(&l, open, format)?;
    let variadic = index - decl.params.len();
    match resolved_format(lines, expr, 0, before)? {
        Resolved::Literal(lit) => conversion_slot(&lit, variadic),
        Resolved::Message(msgid) => agreed_slot(lines, msgid.trim(), variadic),
    }
}

/// The pointer type the caller literals of `msgid` agree on for variadic
/// argument `index`.
///
/// A literal with no conversion at `index` says nothing. A positional
/// conversion (`%2$s`), a conversion this cannot read (`%I64u`), an
/// integer conversion, two pointers that disagree, or a message the body
/// assigns refuses the operand: an unknown message is not guessed. An
/// assignment moves the text the callers passed (`a1 += 3` makes
/// `"%s %lu"` read `%lu`).
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `msgid` - The message expression, a parameter name when the callers
///   are what shows the text.
/// * `index` - The variadic argument, from zero.
///
/// # Returns
///
/// The pointer slot, or `None` when the notes do not agree on one.
fn agreed_slot(lines: &[String], msgid: &str, index: usize) -> Option<Slot> {
    if !is_ident(msgid) || assigned_values(lines, msgid) > 0 {
        return None;
    }
    let prefix = format!("// formats {msgid}:");
    let line = lines.iter().find(|l| l.starts_with(&prefix))?;
    let mut found = None;
    for lit in quoted(line.get(prefix.len()..)?)? {
        if lit.contains('$') || !caller_format_readable(&lit) {
            return None;
        }
        match conversion_slot(&lit, index) {
            None => {}
            Some(Slot::Pointer(ty)) => {
                if found.as_ref().is_some_and(|have| have != &ty) {
                    return None;
                }
                found = Some(ty);
            }
            Some(Slot::Narrow(_) | Slot::Other) => return None,
        }
    }
    found.map(Slot::Pointer)
}

/// Whether every conversion in `literal` is one [`conversion_slot`] can count.
///
/// A caller note is evidence only when the whole format can be read. An
/// unknown conversion (`%I64u`) is not "no argument": the arguments after
/// it cannot be counted, so one readable sibling must not type the operand.
///
/// # Arguments
///
/// * `literal` - The format, quotes included, as the note spells it.
///
/// # Returns
///
/// `false` when a conversion is positional, truncated, or not in the set
/// [`conversion_slot`] sizes. A format with no conversion is readable.
fn caller_format_readable(literal: &str) -> bool {
    let Some(body) = literal.strip_prefix('"').and_then(|s| s.strip_suffix('"')) else {
        return false;
    };
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '%' {
            continue;
        }
        if chars.peek() == Some(&'%') {
            chars.next();
            continue;
        }
        while let Some(&c) = chars.peek() {
            if c == '*' || "hlLqjzt".contains(c) || "-+ #0123456789.'".contains(c) {
                chars.next();
                continue;
            }
            if c == '$' {
                return false;
            }
            break;
        }
        let Some(conv) = chars.next() else {
            return false;
        };
        if conv == 'm' {
            continue;
        }
        if !"diouxXcsfFeEgGaApn".contains(conv) {
            return false;
        }
    }
    true
}

/// The quoted literals on a `// formats` note.
///
/// # Arguments
///
/// * `rest` - The note after its prefix, quotes included.
///
/// # Returns
///
/// The literals as [`conversion_slot`] reads them, or `None` when a quote
/// does not close.
fn quoted(rest: &str) -> Option<Vec<String>> {
    let bytes = rest.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b' ' {
            i += 1;
            continue;
        }
        if bytes[i] != b'"' {
            return None;
        }
        let start = i;
        let before = out.len();
        i += 1;
        while i < bytes.len() {
            if bytes[i] == b'\\' {
                i = i.checked_add(2)?;
                continue;
            }
            if bytes[i] == b'"' {
                i += 1;
                out.push(rest.get(start..i)?.to_owned());
                break;
            }
            i += 1;
        }
        if out.len() == before {
            return None;
        }
    }
    Some(out)
}

/// [`slot_at`], and the format a `gettext` hides from it.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `line` - The line.
/// * `at` - The byte the name starts at.
/// * `before` - The index of `line`.
///
/// # Returns
///
/// The slot, or `None` when the name is not a whole argument of a
/// declared call.
fn known_slot(lines: &[String], line: &str, at: usize, before: usize) -> Option<Slot> {
    slot_at(line, at).or_else(|| format_slot(lines, line, at, before))
}

/// The pointer type the declared calls a parameter is passed to whole
/// agree it is, when nothing else in the body says otherwise.
///
/// Every call that passes the parameter whole as a pointer must name the
/// same type ([`slot_at`], or [`format_slot`] when a `gettext` holds the
/// format), none as an integer, and the parameter is never
/// assigned or cast to a narrow integer. A `char *` takes any other use,
/// since its arithmetic counts bytes as the text's does; any other type
/// takes it only when every use hands the value on whole ([`whole_read`]),
/// so no arithmetic or load reads it as something it is not. No type takes
/// a value some use masks, shifts, multiplies or divides ([`bit_operand`]),
/// which C allows of no pointer. A call
/// passing a copy of the parameter that only steps from it ([`copies`])
/// says the same of the parameter.
///
/// # Arguments
///
/// * `lines` - The function, header lines included.
/// * `param` - The parameter name.
///
/// # Returns
///
/// The type as a declaration spells it (`char *`), or `None`.
pub(in crate::analysis::decompile) fn api_pointer(lines: &[String], param: &str) -> Option<String> {
    if assigned_values(lines, param) > 0 {
        return None;
    }
    let mut found: Option<String> = None;
    let mut whole = true;
    for (before, line) in lines
        .iter()
        .enumerate()
        .filter(|(_, l)| !l.starts_with("//"))
    {
        for at in word_positions(line, param) {
            if cast_before(line.get(..at).unwrap_or("")).is_some() {
                return None;
            }
            match known_slot(lines, line, at, before) {
                Some(Slot::Narrow(_)) => return None,
                Some(Slot::Pointer(t)) => {
                    if found.as_ref().is_some_and(|f| *f != t) {
                        return None;
                    }
                    found = Some(t);
                }
                Some(Slot::Other) | None => {
                    let l = Line {
                        text: line,
                        toks: lex(line),
                    };
                    let k = l.toks.iter().position(|t| t.at == at);
                    if k.is_some_and(|k| bit_operand(&l, k)) {
                        return None;
                    }
                    whole &= k.is_some_and(|k| whole_read(&l, k));
                }
            }
        }
    }
    for copy in copies(lines, param) {
        for (before, line) in lines
            .iter()
            .enumerate()
            .filter(|(_, l)| !l.starts_with("//"))
        {
            for at in word_positions(line, &copy) {
                match known_slot(lines, line, at, before) {
                    Some(Slot::Narrow(_)) => return None,
                    Some(Slot::Pointer(t)) if found.as_ref().is_some_and(|f| *f != t) => {
                        return None;
                    }
                    Some(Slot::Pointer(t)) => found = Some(t),
                    Some(Slot::Other) | None => {}
                }
            }
        }
    }
    found.filter(|t| t == "char *" || whole)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Slot, api_pointer, inferred_type, pointed_at, slot_at};

    /// Splits a text into owned lines.
    ///
    /// # Arguments
    ///
    /// * `text` - The text.
    fn lines(text: &str) -> Vec<String> {
        text.lines().map(str::to_owned).collect()
    }

    /// A whole argument takes the declared parameter's type, and a
    /// `printf` argument the conversion's; a parameter the two platforms
    /// declare differently (`connect`'s socket) says nothing.
    #[test]
    fn declared_parameters_type_their_arguments() {
        assert_eq!(slot_at("exit(a1);", 5), Some(Slot::Narrow("int32_t")));
        assert_eq!(
            slot_at("strlen(a1);", 7),
            Some(Slot::Pointer("char *".to_owned()))
        );
        let line = "fprintf(stderr, \"%s: %*d %lu %u\", a1, a2, a3, a4, a5);";
        let at = |w: &str| line.find(w).unwrap_or(0);
        assert_eq!(
            slot_at(line, at("a1")),
            Some(Slot::Pointer("char *".to_owned()))
        );
        assert_eq!(slot_at(line, at("a2")), Some(Slot::Narrow("int32_t")));
        assert_eq!(slot_at(line, at("a3")), Some(Slot::Narrow("int32_t")));
        assert_eq!(slot_at(line, at("a4")), Some(Slot::Other));
        assert_eq!(slot_at(line, at("a5")), Some(Slot::Narrow("uint32_t")));
        assert_eq!(slot_at("strlen(a1 + 1);", 7), None);
        assert_eq!(slot_at("connect(a1, a2, a3);", 8), None);
        let line = "printf(\"%m %s %d\", a1, a2);";
        let at = |w: &str| line.find(w).unwrap_or(0);
        assert_eq!(
            slot_at(line, at("a1")),
            Some(Slot::Pointer("char *".to_owned()))
        );
        assert_eq!(slot_at(line, at("a2")), Some(Slot::Narrow("int32_t")));
        let masked = lines(
            "uint64_t var1;

var1 = strlen(a1);
if ((a1 & 7) == 0) {
  return var1;
}",
        );
        assert_eq!(api_pointer(&masked, "a1"), None);
        let positional = "printf(\"%1$s\", a1);";
        assert_eq!(
            slot_at(positional, positional.find("a1").unwrap_or(0)),
            None
        );
    }

    /// A format hidden in `gettext` types its operands from the literal.
    /// An unknown message stays a word, and the callers' literals type the
    /// operand only when every one of them agrees.
    #[test]
    fn a_translated_format_types_its_operand() {
        let text = lines(
            "format = dcgettext(NULL, a1, 5);
error(0, 0, format, a2);",
        );
        assert_eq!(api_pointer(&text, "a2"), None);
        let text = lines(
            "// formats a1: \"%lu\"
format = gettext(a1);
error(0, 0, format, a2);",
        );
        assert_eq!(api_pointer(&text, "a2"), None);
        let text = lines(
            "// formats a1: \"%s\" \"%d\"
format = gettext(a1);
error(0, 0, format, a2);",
        );
        assert_eq!(api_pointer(&text, "a2"), None);
        let text = lines(
            "// formats a1: \"%s\" \"%I64u\"
format = gettext(a1);
error(0, 0, format, a2);",
        );
        assert_eq!(api_pointer(&text, "a2"), None);
        let text = lines(
            "// formats a1: \"missing operand after '%s'\" \"too many file label options\"
format = dcgettext(NULL, a1, 5);
error(0, 0, format, a2);",
        );
        assert_eq!(api_pointer(&text, "a2"), Some("char *".to_owned()));
        let text = lines(
            "format = dcgettext(NULL, \"%s: pass %lu/%lu (%s)...\", 5);
error(0, 0, format, a3, a7, a8, name);",
        );
        assert_eq!(api_pointer(&text, "a3"), Some("char *".to_owned()));
        assert_eq!(api_pointer(&text, "a7"), None);
        assert_eq!(api_pointer(&text, "a8"), None);
        let text = lines(
            "format = gettext(\"%d\");
error(0, 0, format, a1);",
        );
        assert_eq!(api_pointer(&text, "a1"), None);
        let text = lines(
            "format = gettext(a1);
error(0, 0, format, a2, a3);",
        );
        assert_eq!(api_pointer(&text, "a2"), None);
        let text = lines(
            "format = dcgettext(NULL, a1, 5);
error(0, 0, format, a2);
a2 = 0;",
        );
        assert_eq!(api_pointer(&text, "a2"), None);
        let text = lines(
            "format = gettext(\"%s %lu\") + 3;
printf(format, a1);",
        );
        assert_eq!(api_pointer(&text, "a1"), None);
        let text = lines(
            "// formats a1: \"%s %lu\"
a1 += 3;
format = gettext(a1);
error(0, 0, format, a2);",
        );
        assert_eq!(api_pointer(&text, "a2"), None);
        let text = lines(
            "uint64_t g64_1000; // @ 0x1000
printf(g64_1000, a1);
g64_1000 = gettext(\"%s\");",
        );
        assert_eq!(api_pointer(&text, "a1"), None);
        let text = lines(
            "printf(format, a1);
format = gettext(\"%s\");",
        );
        assert_eq!(api_pointer(&text, "a1"), None);
        let text = lines(
            "format = gettext(\"%s %lu\");
format += 3;
printf(format, a1);",
        );
        assert_eq!(api_pointer(&text, "a1"), None);
        let text = lines(
            "format = gettext(\"%s\");
format++;
printf(format, a1);",
        );
        assert_eq!(api_pointer(&text, "a1"), None);
        let typed = super::type_parameters(
            "// signature: void f(char *a1, uint64_t a2)\nformat = gettext(a1);\nerror(0, 0, format, a2);\n",
            "uint64_t",
        );
        assert!(typed.contains("f(char *a1, uint64_t a2)"), "{typed}");
        let typed = super::type_parameters(
            "// signature: void f(char *a1, uint64_t a2)\n// formats a1: \"missing operand after '%s'\" \"too many file label options\"\nformat = gettext(a1);\nerror(0, 0, format, a2);\n",
            "uint64_t",
        );
        assert!(typed.contains("f(char *a1, char *a2)"), "{typed}");
        assert!(!typed.contains("// formats"), "{typed}");
    }

    /// A parameter only passed to `exit` and stored to a 32-bit global is
    /// an `int`; one compared unsigned and closed as a descriptor is too.
    #[test]
    fn narrow_uses_agree_on_an_int() {
        let text = lines("uint32_t g32_10; // @ 0x10\n\ng32_10 = a1;\nexit(a1);");
        assert_eq!(inferred_type(&text, "a1"), Some("int32_t"));
        let text = lines("if ((uint32_t)a1 != 5) {\n  close(a1);\n}");
        assert_eq!(inferred_type(&text, "a1"), Some("int32_t"));
        let text = lines("exit(a1);\nfree(a1);");
        assert_eq!(inferred_type(&text, "a1"), None);
    }

    /// A string the calls agree on is a `char *`, whatever else reads it;
    /// a stream is a `FILE *` only while every use passes it on whole.
    #[test]
    fn declared_pointers_type_parameters() {
        let text = lines("if (strlen(a1) > 4) {\n  *(uint8_t*)(a1 + 4) = 0;\n}");
        assert_eq!(api_pointer(&text, "a1"), Some("char *".to_owned()));
        let text = lines("fputs(\"x\", a1);\nfclose(a1);");
        assert_eq!(api_pointer(&text, "a1"), Some("FILE *".to_owned()));
        let text = lines("fputs(\"x\", a1);\nv = *(uint32_t*)(a1 + 8);");
        assert_eq!(api_pointer(&text, "a1"), None);
        let text = lines("strlen(a1);\nexit(a1);");
        assert_eq!(api_pointer(&text, "a1"), None);
    }

    /// A parameter copied into the home an unoptimized build keeps it in
    /// takes what the copy shows: bytes walked through it, or a string
    /// passed on.
    #[test]
    fn copies_type_the_parameter_they_hold() {
        let text = lines("local_10 = a1;\nwhile (*(uint8_t*)local_10 != 0) {\n  local_10 += 1;\n}");
        assert_eq!(pointed_at(&text, "a1"), Some("uint8_t *"));
        let text = lines("local_10 = a1;\nputs(local_10);");
        assert_eq!(api_pointer(&text, "a1"), Some("char *".to_owned()));
        let text = lines("local_10 = a1;\nlocal_10 = 0;\nputs(local_10);");
        assert_eq!(api_pointer(&text, "a1"), None);
        let text = "// signature: uint32_t f(void *a1)\nvar2 = a1;\nwhile (*(uint8_t*)var2 != 0) {\n  var2 += 1;\n}\n";
        let typed = super::type_parameters(text, "uint64_t");
        assert!(typed.contains("f(uint8_t *a1)"), "{typed}");
    }
}
