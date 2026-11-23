//! The layout fields of a text spelled back as the loads they name, for a
//! C file that defines no struct for them.

use std::borrow::Cow;
use std::collections::BTreeSet;

use super::{Layouts, Width, offset_text, read_layouts};
use crate::analysis::decompile::interp::header;
use crate::analysis::decompile::lexer::{Lex, Tok, lex};
use crate::analysis::decompile::line::rejoin;
use crate::analysis::decompile::{Dialect, signature_params, steps_bytes, vars};

/// The tokens after a member access that bind tighter than a dereference:
/// a load followed by one is parenthesized.
const POSTFIX: [&str; 6] = ["(", "[", "++", "--", "->", "."];

/// Returns a text with every field [`super::apply_layouts`] named spelled
/// as the load it names, the inverse of that pass.
///
/// `base->field_0x8` becomes `*(uint32_t*)(base + 8)` at the width the
/// base's layout line gives the offset, `base->field_0x0` becomes
/// `*(uint32_t*)base`, `base->field_neg0x10` becomes `*(uint32_t*)(base -
/// 0x10)`, and the address `&base->field_0x8` becomes `base + 8`,
/// parenthesized unless it stands alone (`f(&base->field_0x8)`). That is
/// what the text check reads a layout field as: the bytes that far past the
/// base's value ([`crate::analysis::decompile::interp`]). The layouts are
/// the header's, the lines the text check reads them from, so a comment in
/// the body that reads as one sizes nothing. The sum is the base's own
/// where that steps bytes in standard C ([`steps_bytes`]: an integer, in
/// its own type, or a pointer to a byte); any other base, and one whose type the
/// signature and the declarations do not give, is summed as
/// `(uintptr_t)base + 8`, as the byte arithmetic pass writes it, never as
/// GNU C's `void *` arithmetic. A field a struct of the user's or the
/// debug information names, a field no layout line sizes, and every
/// literal and comment stay as they are; so does each line, the layout
/// lines included, so no line moves.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
///
/// # Returns
///
/// The text with its layout fields lowered.
pub(in crate::analysis::decompile) fn lower_layouts(text: &str) -> String {
    let (head, end) = header::lines(text);
    let head = head.get(..end).unwrap_or_default();
    let layouts = read_layouts(head);
    if layouts.is_empty() {
        return text.to_owned();
    }
    let params = signature_params(text);
    let declared = |base: &str| {
        let param = params.iter().find(|(n, _)| n == base);
        param.map(|(_, t)| t.clone()).or_else(|| {
            head.iter().find_map(|l| {
                let (ty, items) = vars::declaration(l.trim())?;
                let (stars, _) = items.into_iter().find(|(_, n)| *n == base)?;
                Some(format!("{ty} {stars}"))
            })
        })
    };
    let bytes: BTreeSet<&str> = layouts
        .keys()
        .map(String::as_str)
        .filter(|b| declared(b).is_some_and(|t| steps_bytes(&t, Dialect::Iso)))
        .collect();
    let lowered: Vec<Cow<'_, str>> = text
        .lines()
        .map(|l| {
            if l.trim_start().starts_with("//") {
                Cow::Borrowed(l)
            } else {
                lower_line(l, &layouts, &bytes)
            }
        })
        .collect();
    rejoin(&lowered, text)
}

/// Reads the offset a field name [`super::apply_layouts`] writes spells:
/// `field_0x18` is 0x18, `field_neg0x40` is -0x40, each in its one
/// spelling.
///
/// # Arguments
///
/// * `name` - The member name.
fn field_offset(name: &str) -> Option<i64> {
    let (neg, hex) = match name.strip_prefix("field_neg0x") {
        Some(h) => (true, h),
        None => (false, name.strip_prefix("field_0x")?),
    };
    let off = i64::try_from(u64::from_str_radix(hex, 16).ok()?).ok()?;
    let canonical = format!("{off:x}") == hex && (!neg || off > 0);
    canonical.then_some(if neg { -off } else { off })
}

/// Returns one line with its layout fields lowered ([`lower_layouts`]).
///
/// # Arguments
///
/// * `line` - A line of code.
/// * `layouts` - The text's layouts.
/// * `bytes` - The bases whose sum with an offset steps bytes.
fn lower_line<'l>(line: &'l str, layouts: &Layouts, bytes: &BTreeSet<&str>) -> Cow<'l, str> {
    if !line.contains("->field_") {
        return Cow::Borrowed(line);
    }
    let toks = lex(line);
    let word = |k: usize| {
        toks.get(k)
            .and_then(|t| line.get(t.at..t.end))
            .unwrap_or("")
    };
    let is = |k: usize, lex: Lex| toks.get(k).is_some_and(|t| t.lex == lex);
    let punct = |k: usize, p: &str| is(k, Lex::Punct) && word(k) == p;
    let mut out = String::with_capacity(line.len() + 32);
    let (mut cursor, mut k) = (0, 0);
    while k < toks.len() {
        let member = k
            .checked_sub(1)
            .is_some_and(|j| punct(j, ".") || punct(j, "->"));
        let access = is(k, Lex::Name) && punct(k + 1, "->") && is(k + 2, Lex::Name) && !member;
        let base = word(k);
        let found = access
            .then(|| field_offset(word(k + 2)))
            .flatten()
            .and_then(|off| Some((off, *layouts.get(base)?.get(&off)?)));
        let (Some((off, width)), Some(first), Some(last)) = (found, toks.get(k), toks.get(k + 2))
        else {
            k += 1;
            continue;
        };
        let postfix = POSTFIX.iter().any(|p| punct(k + 3, p));
        let amp = k
            .checked_sub(1)
            .filter(|&j| !postfix && punct(j, "&") && unary(&toks, line, j));
        let start = amp.and_then(|j| toks.get(j)).unwrap_or(first);
        out.push_str(line.get(cursor..start.at).unwrap_or_default());
        if out.ends_with('/') {
            out.push(' ');
        }
        let alone = amp.is_some_and(|j| {
            let before = j.checked_sub(1);
            let opens = before
                .is_none_or(|i| ["(", ",", "="].iter().any(|p| punct(i, p)) || word(i) == "return");
            opens && [")", ",", ";"].iter().any(|p| punct(k + 3, p))
        });
        let wrap = if amp.is_some() { !alone } else { postfix };
        let field = Field {
            base,
            off,
            width,
            bytes: bytes.contains(base),
        };
        out.push_str(&field.lowered(amp.is_some(), wrap));
        cursor = last.end;
        k += 3;
    }
    out.push_str(line.get(cursor..).unwrap_or_default());
    Cow::Owned(out)
}

/// Tells whether the `&` at token `j` takes an address rather than an `and`
/// of two values: no value ends right before it.
///
/// A cast's `)` reads as a value's end, so `(T)&p->field_0x8` keeps its `&`
/// and its field becomes the load, `&*(U*)(p + 8)`, the same address.
///
/// # Arguments
///
/// * `toks` - The line's tokens.
/// * `line` - The line.
/// * `j` - The index of the `&`.
fn unary(toks: &[Tok], line: &str, j: usize) -> bool {
    let Some(prev) = j.checked_sub(1).and_then(|i| toks.get(i)) else {
        return true;
    };
    let text = line.get(prev.at..prev.end).unwrap_or_default();
    match prev.lex {
        Lex::Punct => !matches!(text, ")" | "]" | "++" | "--"),
        Lex::Name => text == "return",
        Lex::Number | Lex::Literal => false,
    }
}

/// One layout field an access names.
struct Field<'a> {
    /// The base it is read through.
    base: &'a str,
    /// Its offset from the base, negative below it.
    off: i64,
    /// Its width.
    width: &'static Width,
    /// Whether the base's own sum with the offset steps bytes
    /// ([`steps_bytes`]).
    bytes: bool,
}

impl Field<'_> {
    /// Returns the C for the field: its load, or its address.
    ///
    /// The text never begins with `/`, so it opens no comment after a `/`
    /// that [`lower_line`] has spaced off.
    ///
    /// # Arguments
    ///
    /// * `address` - Whether the text takes the field's address.
    /// * `wrap` - Whether the result is parenthesized: a load a postfix
    ///   operator follows, an address that does not stand alone.
    fn lowered(&self, address: bool, wrap: bool) -> String {
        let (base, ty) = (self.base, self.width.c);
        let stepped = if self.bytes {
            Cow::Borrowed(base)
        } else {
            Cow::Owned(format!("(uintptr_t){base}"))
        };
        let sign = if self.off < 0 { '-' } else { '+' };
        let at = format!("{stepped} {sign} {}", offset_text(self.off.unsigned_abs()));
        let c = match (address, self.off == 0) {
            (true, true) => base.to_owned(),
            (true, false) => at,
            (false, true) => format!("*({ty}*){base}"),
            (false, false) => format!("*({ty}*)({at})"),
        };
        if wrap { format!("({c})") } else { c }
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::super::apply_layouts;
    use super::lower_layouts;
    use crate::analysis::decompile::interp::{End, Script};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::Program;

    /// Returns a text without its layout lines.
    ///
    /// # Arguments
    ///
    /// * `text` - The text.
    fn unlaid(text: &str) -> String {
        let lines: Vec<&str> = text
            .lines()
            .filter(|l| !l.starts_with("// layout ") && !l.starts_with("//  "))
            .collect();
        format!("{}\n", lines.join("\n"))
    }

    /// Lowering undoes the layout pass.
    ///
    /// Each field becomes the load or the address it was, at the width the
    /// layout line gives, for a field at zero, above and below its base,
    /// two bases one of whose names begins the other's, an address taken,
    /// a field spelled in a string literal and an offset read at two
    /// widths, which neither pass touches. No line moves.
    #[test]
    fn lowering_gives_the_loads_the_layout_pass_named_back() {
        let text = "// signature: uint64_t f(uint64_t a1, uint64_t a10)
uint64_t var1;

var1 = *(uint64_t*)a1 + *(uint32_t*)(a1 + 8) + *(uint64_t*)(a1 + 0x18);
*(uint8_t*)(a1 + 0x10) = 1;
g((a1 + 0x18));
var1 += *(uint32_t*)(a10 - 0x40) + *(uint64_t*)(a10 + 8) + *(uint16_t*)(a10 + 0x20);
puts(\"a1->field_0x8\");
var1 += *(uint16_t*)(a1 + 0x30) + *(uint32_t*)(a1 + 0x30);
return var1;
";
        let laid = apply_layouts(text);
        assert!(laid.contains("// layout a1: 0x0 u64, 0x8 u32"), "{laid}");
        assert!(laid.contains("a10->field_neg0x40"), "{laid}");
        assert!(laid.contains("g((&a1->field_0x18));"), "{laid}");
        let lowered = lower_layouts(&laid);
        assert_eq!(lowered.lines().count(), laid.lines().count(), "{lowered}");
        assert_eq!(unlaid(&lowered), text, "{lowered}");
    }

    /// A base whose own sum does not step bytes is summed as an address.
    ///
    /// The sum is the base's own for an integer, of any width, and a
    /// pointer to a byte; a pointer to a wider type, `void *`, an array and
    /// a base no declaration types are summed through `(uintptr_t)`.
    #[test]
    fn a_base_whose_sum_does_not_step_bytes_is_summed_as_an_address() {
        let lowered = |params: &str, decl: &str| {
            let text = format!(
                "// signature: uint32_t f({params})\n// layout a1: 0x8 u32\n{decl}\nreturn a1->field_0x8;\n"
            );
            let out = lower_layouts(&text);
            out.lines().last().unwrap_or_default().to_owned()
        };
        let cast = "return *(uint32_t*)((uintptr_t)a1 + 8);";
        let plain = "return *(uint32_t*)(a1 + 8);";
        assert_eq!(lowered("uint64_t *a1", ""), cast);
        assert_eq!(lowered("void *a1", ""), cast);
        assert_eq!(lowered("void", "uint64_t a1[4];\n"), cast);
        assert_eq!(lowered("void", ""), cast);
        assert_eq!(lowered("uint64_t a1", ""), plain);
        assert_eq!(lowered("uint32_t a1", ""), plain);
        assert_eq!(lowered("uint8_t *a1", ""), plain);
        assert_eq!(lowered("void", "int64_t a1;\n"), plain);
        assert_eq!(lowered("void", "uint8_t *a1;\n"), plain);
        assert_eq!(lowered("void", "uint32_t *a1;\n"), cast);
    }

    /// Only the header's layout lines size a field: a comment in the body
    /// that reads as one, as a user's comment on an instruction prints,
    /// sizes nothing.
    #[test]
    fn a_layout_comment_in_the_body_sizes_nothing() {
        let text = "// signature: uint32_t f(uint64_t a1)
// layout a1: 0x8 u32

// layout a1: 0x8 u8
return a1->field_0x8;
";
        let out = lower_layouts(text);
        assert!(
            out.ends_with(
                "return *(uint32_t*)(a1 + 8);
"
            ),
            "{out}"
        );
    }

    /// A load after a `/` is spaced off it, so the two open no comment.
    #[test]
    fn a_load_after_a_slash_opens_no_comment() {
        let text = "// signature: uint32_t f(uint64_t a1)
// layout a1: 0x8 u32

return y/a1->field_0x8;
";
        let out = lower_layouts(text);
        assert!(
            out.ends_with(
                "return y/ *(uint32_t*)(a1 + 8);
"
            ),
            "{out}"
        );
    }

    /// Runs a text and its lowered form through the text check and returns
    /// both answers.
    ///
    /// # Arguments
    ///
    /// * `p` - The image the texts run on.
    /// * `text` - The text with its layout lines.
    /// * `args` - The arguments.
    /// * `pokes` - The memory the run starts with.
    fn runs(p: &Program, text: &str, args: &[u64], pokes: &[(u64, Vec<u8>)]) -> (End, End) {
        let a = Analysis::compute(p);
        let o = Overlay::default();
        let lowered = unlaid(&lower_layouts(text));
        assert!(!lowered.contains("->"), "{lowered}");
        let run = |t: &str| {
            let s = Script::read(p, &a, &o, 0x1000, t).expect("reads");
            s.run(args, pokes, 100).expect("runs").end
        };
        (run(text), run(&lowered))
    }

    /// The lowered text reads what the layout text reads through every
    /// kind of base: a pointer to a wider type, a `void *`, an array and a
    /// pointer on a 32-bit target, each summed as an address.
    #[test]
    fn the_lowered_text_runs_as_the_layout_text_does_on_every_base() {
        let x64 = Program::raw_x64(&[0xc3]);
        let mem = vec![(0x5000, (1..=0x20).collect::<Vec<u8>>())];
        let want = End::Returned(Some(u64::from(u32::from_le_bytes([9, 10, 11, 12]))));
        for param in ["uint64_t *a1", "void *a1"] {
            let text = format!(
                "// signature: uint64_t f({param})
// layout a1: 0x0 u64, 0x8 u32

return a1->field_0x8;
"
            );
            assert_eq!(
                runs(&x64, &text, &[0x5000], &mem),
                (want.clone(), want.clone()),
                "{text}"
            );
        }
        let array = "// signature: uint64_t f(uint64_t a1)
// layout local_28: 0x8 u64
uint64_t local_28[4];

local_28[1] = a1;
return local_28->field_0x8;
";
        let got = End::Returned(Some(0x77));
        assert_eq!(runs(&x64, array, &[0x77], &[]), (got.clone(), got));
        let text = crate::program::Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let x86 = Program::raw(
            vec![0xc3; 0x100],
            crate::program::Arch::X86,
            0,
            Some(0x1000),
            vec![text],
        );
        let narrow = "// signature: uint32_t f(uint32_t *a1)
// layout a1: 0x8 u32

return a1->field_0x8;
";
        assert_eq!(runs(&x86, narrow, &[0x5000], &mem), (want.clone(), want));
    }

    /// An integer base narrower than the word keeps its own arithmetic: the
    /// lowered text wraps at 32 bits where the text the layout pass read
    /// did, so both read the same bytes at the top of the range.
    #[test]
    fn a_narrow_integer_base_wraps_as_its_own_sum_does() {
        let x64 = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&x64);
        let o = Overlay::default();
        let text = "// signature: uint64_t f(uint32_t a1)

return *(uint32_t*)(a1 + 8) + *(uint32_t*)(a1 + 0x10) + *(uint32_t*)(a1 + 0x14);
";
        let laid = apply_layouts(text);
        assert!(laid.contains("// layout a1:"), "{laid}");
        let lowered = unlaid(&lower_layouts(&laid));
        let pokes = [(0, vec![1u8; 0x20]), (0x1_0000_0000, vec![2u8; 0x20])];
        let run = |t: &str| {
            let s = Script::read(&x64, &a, &o, 0x1000, t).expect("reads");
            s.run(&[0xffff_fff8], &pokes, 100).expect("runs").end
        };
        assert!(matches!(run(text), End::Returned(Some(_))), "{text}");
        assert_eq!(run(&lowered), run(text), "{lowered}");
    }

    /// A member no layout sizes stays a member: a name a struct gives, an
    /// offset the layout does not list, a spelling the layout pass never
    /// writes, a member of a member, and a field in a comment.
    #[test]
    fn a_field_no_layout_sizes_stays() {
        let text = "// signature: uint64_t f(uint64_t a1)
// layout a1: 0x8 u32

x = a1->count + a1->field_0x10 + a1->field_0x08 + b->a1->field_0x8;
x = 1; // a1->field_0x8
";
        assert_eq!(lower_layouts(text), text);
    }

    /// A load a postfix operator follows is parenthesized, an address is
    /// one only where no value ends before the `&`, and a cast's `&` keeps
    /// the address of the load.
    #[test]
    fn a_load_keeps_its_precedence() {
        let text = "// signature: uint64_t f(uint64_t a1)
// layout a1: 0x0 u64, 0x8 u32

x = a1->field_0x8[2] + (*a1->field_0x0)(1);
p = &a1->field_0x8[1];
x = y & a1->field_0x8;
p = (uint64_t)&a1->field_0x8;
p = &a1->field_0x8;
x = y + &a1->field_0x8 - z;
return &a1->field_0x0;
";
        let want = "// signature: uint64_t f(uint64_t a1)
// layout a1: 0x0 u64, 0x8 u32

x = (*(uint32_t*)(a1 + 8))[2] + (**(uint64_t*)a1)(1);
p = &(*(uint32_t*)(a1 + 8))[1];
x = y & *(uint32_t*)(a1 + 8);
p = (uint64_t)&*(uint32_t*)(a1 + 8);
p = a1 + 8;
x = y + (a1 + 8) - z;
return a1;
";
        assert_eq!(lower_layouts(text), want);
    }

    /// The lowered text means what the layout text means: the text check
    /// runs both, the layout lines dropped from the lowered one, to the
    /// same answer, the sum of the four fields the code reads.
    #[test]
    fn the_lowered_text_runs_as_the_layout_text_does() {
        let code = [
            0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
            0x8b, 0x51, 0x08, // ASM: mov edx, [rcx+8]
            0x48, 0x01, 0xd0, // ASM: add rax, rdx
            0x0f, 0xb6, 0x51, 0x10, // ASM: movzx edx, byte [rcx+0x10]
            0x48, 0x01, 0xd0, // ASM: add rax, rdx
            0x48, 0x03, 0x41, 0x18, // ASM: add rax, [rcx+0x18]
            0xc3, // ASM: ret
        ];
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let text = crate::analysis::decompile::decompile(&p, &a, &o, 0x1000).expect("decompiles");
        assert!(text.contains("// layout "), "{text}");
        let lowered = unlaid(&lower_layouts(&text));
        assert!(!lowered.contains("->"), "{lowered}");
        let mem: Vec<u8> = (1..=0x20).collect();
        let want = u64::from_le_bytes([1, 2, 3, 4, 5, 6, 7, 8])
            + u64::from(u32::from_le_bytes([9, 10, 11, 12]))
            + 17
            + u64::from_le_bytes([25, 26, 27, 28, 29, 30, 31, 32]);
        for t in [&text, &lowered] {
            let s = Script::read(&p, &a, &o, 0x1000, t).expect("reads");
            let r = s
                .run(&[0x5000], &[(0x5000, mem.clone())], 100)
                .expect("runs");
            assert_eq!(r.end, End::Returned(Some(want)), "{t}");
        }
    }
}
