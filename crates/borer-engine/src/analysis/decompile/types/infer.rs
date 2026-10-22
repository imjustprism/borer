//! What the uses of a variable show its type to be: the casts and masks
//! the text applies to it, the stores and returns it fills, and the
//! declared parameters of the calls it is passed to whole.

use super::super::evidence::{argument_of, whole_read};
use super::super::lexer::{Lex, Line, lex};
use super::*;
use crate::analysis::typelib::{self, Pass};
use crate::program::BinaryFormat;

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
    if !is_ident(dest) {
        return None;
    }
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
        (first == dest || names.any(|n| n == dest))
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
/// that the two platforms size differently (`long`) says nothing.
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
    let decl = typelib::declared(callee, BinaryFormat::Elf)
        .or_else(|| typelib::declared(callee, BinaryFormat::Pe))?;
    if let Some(p) = decl.params.get(index) {
        return Some(slot_of(p.ty));
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
/// or `j`) reads a word, a float or something this does not size.
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
            } else if !"-+ #0123456789.'".contains(c) {
                break;
            }
            chars.next();
        }
        let conv = chars.next()?;
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

/// The pointer type the declared calls a parameter is passed to whole
/// agree it is, when nothing else in the body says otherwise.
///
/// Every call that passes the parameter whole as a pointer must name the
/// same type ([`slot_at`]), none as an integer, and the parameter is never
/// assigned or cast to a narrow integer. A `char *` takes any other use,
/// since its arithmetic counts bytes as the text's does; any other type
/// takes it only when every use hands the value on whole ([`whole_read`]),
/// so no arithmetic or load reads it as something it is not.
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
    for line in lines.iter().filter(|l| !l.starts_with("//")) {
        for at in word_positions(line, param) {
            if cast_before(line.get(..at).unwrap_or("")).is_some() {
                return None;
            }
            match slot_at(line, at) {
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
                    whole &= k.is_some_and(|k| whole_read(&l, k));
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
    use super::{Slot, api_pointer, inferred_type, slot_at};

    /// Splits a text into owned lines.
    ///
    /// # Arguments
    ///
    /// * `text` - The text.
    fn lines(text: &str) -> Vec<String> {
        text.lines().map(str::to_owned).collect()
    }

    /// A whole argument takes the declared parameter's type, and a
    /// `printf` argument the conversion's.
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
}
