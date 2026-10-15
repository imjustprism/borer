//! Rendering the symbolic expressions as C text: name resolution
//! ([`Names`]), precedence-aware expression and condition rendering, and
//! the literal spellings (constants, four-ccs, paths) the text prints.
//!
//! The expressions themselves, their construction and their constant
//! folding live in [`super::expr`]; this module only turns finished
//! expressions into the text [`super::emit`] prints.

use super::expr::{
    ATOM, Cc, Cond, Expr, Flags, Key, LOGICAL, Op, Ty, UNARY, UnOp, fold, indexed, low_bits_read,
    mask_bits, opaque_note, sext, signed_ty, tls_slot,
};
use crate::analysis::Overlay;
use crate::isa::a64;
use crate::isa::x86::{ConditionCode, Register};
use crate::num::lo32;
use crate::program::{BinaryFormat, Program, SymbolKind};

/// Name resolution for rendering: overlay names beat symbol names beat
/// debug-recorded locals beat synthesized `g{bits}_{addr}` / `local_N` /
/// register names.
pub(super) struct Names<'a> {
    /// Supplies the symbol table.
    pub program: &'a Program,
    /// Supplies function entries and the symbol index.
    pub analysis: &'a crate::analysis::Analysis,
    /// Supplies user names.
    pub overlay: &'a Overlay,
    /// The first parameter is the `this` object of a member function.
    pub this_param: bool,
    /// Index of the hidden return-pointer parameter, named `result`.
    pub result_param: Option<u8>,
    /// The function being rendered, so its own `__FUNCSIG__` literal reads
    /// as that macro.
    pub own_name: std::sync::Arc<str>,
    /// Parameters the debug information recorded, in order.
    pub debug_params: std::sync::Arc<[crate::dwarf::Parameter]>,
    /// The frame-relative locals the debug information recorded, as slot
    /// offset to name; a slot one names renders that name where the
    /// synthesized `local_N` would.
    pub debug_locals: std::sync::Arc<std::collections::BTreeMap<i64, String>>,
    /// Frame offset of the first stack-passed argument, above the return
    /// address and the shadow space.
    pub first_stack: i64,
    /// How many stack-passed arguments the function reads.
    pub stack_params: u32,
    /// How many arguments the convention passes in registers, which is
    /// where the stack ones continue counting from.
    pub reg_params: u32,
    /// Stack word size in bytes: the width of the return address and the
    /// distance between two stack-passed arguments.
    pub word: i64,
    /// The type each stack slot the text names is declared with, by its
    /// frame offset: what its name reads and writes.
    pub slot_types: std::sync::Arc<std::collections::BTreeMap<i64, Ty>>,
}

impl Names<'_> {
    /// Names a constant that is the address of a function, a data symbol or
    /// a string literal.
    ///
    /// # Arguments
    ///
    /// * `v` - The constant.
    /// * `literal` - Whether the string at the address may name it: true
    ///   where the constant is a value passed, stored, returned or loaded
    ///   through, false where it is an operand of arithmetic or a
    ///   comparison, which a number lands on as often as an address does.
    ///
    /// # Returns
    ///
    /// The function's name, `&symbol` for an export/local data symbol (also
    /// in `.bss`), `&Class::vftable` for a recovered vtable,
    /// `&Class::staticMetaObject` for a `moc` meta-object, `&Class::RTTI` for
    /// a class's type descriptor, `&Class::Id` for a registered message
    /// class's id, the name of a
    /// known algorithm's table (`crc_32_table`), `&__ImageBase` for a PE's
    /// own image base, a mapped overlay-named address, the quoted literal
    /// for a string in non-code memory when `literal` allows it, `&gN_addr`
    /// for an address in
    /// writable data that holds no literal, or `None` when the value names
    /// nothing.
    pub(super) fn const_name(&self, v: u64, literal: bool) -> Option<String> {
        if let Some(f) = self.analysis.function(v) {
            return Some(
                bare(&crate::analysis::name_of(
                    self.analysis,
                    self.overlay,
                    f.entry,
                ))
                .to_owned(),
            );
        }
        if let Some(s) = self
            .analysis
            .symbol_at(self.program, v)
            .filter(|s| s.kind != SymbolKind::Import)
        {
            return Some(format!("&{}", crate::search::demangled_name(&s.name)));
        }
        if let Some(class) = self.analysis.classes.vtables.get(&v) {
            return Some(format!("&{class}::vftable"));
        }
        if let Some(name) = self.analysis.classes.secondary_vtables.get(&v) {
            return Some(format!("&{name}"));
        }
        if let Some(class) = self.analysis.qt.iter().find(|c| c.meta_object == v) {
            return Some(format!("&{}::staticMetaObject", class.name));
        }
        if let Some(name) = self.analysis.crypto.get(&v) {
            return Some(crate::crypto::identifier(name));
        }
        // INVARIANT: a PE reads its own headers through the image base, which
        // the linker names `__ImageBase`; `*(uint16_t*)&__ImageBase == 0x5a4d`
        // is the DOS signature check it is.
        if v == self.program.image_base && self.program.format == BinaryFormat::Pe {
            return Some("&__ImageBase".to_owned());
        }
        let mapped = self
            .program
            .sections
            .iter()
            .any(|s| v >= s.va.0 && v < s.va.0 + s.vsize.max(s.file_size));
        if mapped && let Some(n) = self.overlay.names.get(&v) {
            return Some(format!("&{n}"));
        }
        if let Some(class) = self.analysis.classes.descriptors.get(&v) {
            return Some(format!(
                "&{class}::{}",
                self.analysis.packs.name_for("class_info")
            ));
        }
        if mapped {
            let homes = self.analysis.derived.get_or_build("id_homes", (), || {
                crate::analysis::messages::id_homes(self.program, self.analysis)
            });
            if let Some(class) = homes.get(&v) {
                return Some(format!(
                    "&{class}::{}",
                    self.analysis.packs.name_for("class_id")
                ));
            }
        }
        // INVARIANT: a status code is looked up only off the image, so a
        // 32-bit program large enough to map 0x406d1388 keeps it an address.
        if !mapped && let Some(n) = crate::winconst::name(v) {
            return Some(n.to_owned());
        }
        if literal && let Some(text) = super::literal_at(self.program, v, &self.own_name) {
            return Some(text);
        }
        // INVARIANT: an address in writable data is a variable's, and the
        // variable is named by the word as a read of it would be, so the
        // object passed to one call and read by another has one name.
        self.program
            .section_at(v)
            .filter(|s| s.writable && !s.executable)
            .map(|_| format!("&g{}_{v:x}", self.word * 8))
    }

    /// Tells whether a constant is the address of a string's first
    /// character.
    ///
    /// A literal of at least one character starts there, and the byte before
    /// it ends whatever came before (a terminator), or the section starts
    /// there. An address inside a string, where an unrelated number lands as
    /// often as not, is no start, and neither is a lone terminator, which
    /// no sum indexes as text.
    ///
    /// # Arguments
    ///
    /// * `v` - The constant.
    fn starts_string(&self, v: u64) -> bool {
        let first = self.program.section_at(v).is_some_and(|s| s.va.0 == v)
            || v.checked_sub(1)
                .and_then(|b| self.program.read_va(b, 1))
                .is_some_and(|b| b == [0]);
        first
            && super::literal_at(self.program, v, &self.own_name)
                .is_some_and(|l| !matches!(l.as_str(), "\"\"" | "L\"\""))
    }

    /// Tells whether the literal at a constant is the empty string.
    ///
    /// # Arguments
    ///
    /// * `v` - The constant.
    fn empty_literal(&self, v: u64) -> bool {
        super::literal_at(self.program, v, &self.own_name)
            .is_some_and(|l| matches!(l.as_str(), "\"\"" | "L\"\""))
    }

    /// Returns the bare import name whose IAT slot is `addr`: demangled,
    /// without the `dll!` prefix, so a call through the slot reads as
    /// `QString::QString` and not `??0QString@@QAE@PBD@Z`.
    ///
    /// A wrapper exporting the name of the import it forwards to (kernel32's
    /// `Beep` calling KERNELBASE's) would read as calling itself, so an
    /// import of the function's own name keeps the linker's name for its
    /// slot, `__imp_Beep`.
    ///
    /// # Arguments
    ///
    /// * `addr` - A candidate IAT slot address.
    pub(super) fn import_at(&self, addr: u64) -> Option<String> {
        let name = self
            .program
            .symbols
            .iter()
            .find(|s| s.kind == SymbolKind::Import && s.addr == addr && s.addr != 0)
            .map(|s| bare(&crate::search::demangled_name(&s.name)).to_owned())?;
        Some(if name == *self.own_name {
            format!("__imp_{name}")
        } else {
            name
        })
    }

    /// Names an Objective-C reference ([`crate::analysis::objc`]):
    /// `@selector(sel)` for a selector reference, the class's name for a
    /// class reference.
    ///
    /// # Arguments
    ///
    /// * `addr` - A candidate reference's address.
    fn objc_ref(&self, addr: u64) -> Option<String> {
        let objc = &self.analysis.objc;
        objc.selrefs
            .get(&addr)
            .map(|sel| format!("@selector({sel})"))
            .or_else(|| objc.classrefs.get(&addr).cloned())
    }

    /// Renders the text name of a variable.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    ///
    /// # Returns
    ///
    /// The lowercase register name, `local_N`/`arg_N`, the overlay, import or
    /// data-symbol name of a global, `@selector(sel)` or the class for an
    /// Objective-C reference, `Class::Id` for the id a registered
    /// message class hands out, `Class::RTTI` for a class's type descriptor
    /// (else `g{bits}_{addr}`), `tmp_N`, or `aN` for an incoming argument.
    pub(super) fn key(&self, k: Key) -> String {
        match k {
            Key::Reg(r) => format!("{r:?}").to_lowercase(),
            Key::Slot(off) => self.slot(off),
            Key::Global(addr, bits) => {
                if let Some(off) = tls_slot(addr) {
                    return match self.analysis.classes.tls_slots.get(&off) {
                        Some(c) => format!("{c}::{}", self.analysis.packs.name_for("singleton")),
                        None => format!("tls_{off:#x}"),
                    };
                }
                if let Some(n) = self.overlay.names.get(&addr) {
                    return n.clone();
                }
                if let Some(n) = self.objc_ref(addr) {
                    return n;
                }
                if let Some(n) = self.import_at(addr) {
                    return n;
                }
                if let Some(s) = self.analysis.symbol_at(self.program, addr) {
                    return crate::search::demangled_name(&s.name);
                }
                let homes = self.analysis.derived.get_or_build("id_homes", (), || {
                    crate::analysis::messages::id_homes(self.program, self.analysis)
                });
                if let Some(class) = homes.get(&addr) {
                    return format!("{class}::{}", self.analysis.packs.name_for("class_id"));
                }
                if let Some(class) = self.analysis.classes.descriptors.get(&addr) {
                    return format!("{class}::{}", self.analysis.packs.name_for("class_info"));
                }
                format!("g{bits}_{addr:x}")
            }
            Key::Tmp(n) => format!("tmp_{n}"),
            Key::A64(r) => a64_name(r),
            Key::Param(0) if self.this_param => "this".to_owned(),
            Key::Param(i) if Some(i) == self.result_param => "result".to_owned(),
            // The compiler's own name for the parameter, when it left one.
            Key::Param(i) => self
                .debug_params
                .get(usize::from(i))
                .map(|p| p.name.clone())
                .filter(|n| !n.is_empty())
                .unwrap_or_else(|| format!("a{}", u32::from(i) + 1)),
        }
    }
}

/// The code of the stack pointer in [`a64_code`], after `x30`.
const A64_SP: u8 = 31;

/// The code of the zero register in [`a64_code`].
const A64_ZR: u8 = 32;

/// The code of `v0` in [`a64_code`], with `v1`..`v31` after it.
const A64_V: u8 = 64;

/// The highest `v` register number.
const A64_V_LAST: u8 = 31;

/// Returns the one-byte code of an arm64 register.
///
/// Packed effects and the replay's variable addresses spell a register by
/// it: `x0`..`x30` as their numbers, then [`A64_SP`], [`A64_ZR`], and
/// `v0`..`v31` from [`A64_V`].
///
/// # Arguments
///
/// * `r` - The register.
pub(super) fn a64_code(r: a64::Reg) -> u8 {
    match r {
        a64::Reg::X(n) => n,
        a64::Reg::Sp => A64_SP,
        a64::Reg::Zr => A64_ZR,
        a64::Reg::V(n) => A64_V.saturating_add(n),
    }
}

/// The arm64 register an [`a64_code`] names.
///
/// # Arguments
///
/// * `code` - The code.
///
/// # Returns
///
/// The register, or `None` for a code that names none.
pub(super) fn a64_reg(code: u8) -> Option<a64::Reg> {
    Some(match code {
        A64_SP => a64::Reg::Sp,
        A64_ZR => a64::Reg::Zr,
        n if n < A64_SP => a64::Reg::X(n),
        n => a64::Reg::V(n.checked_sub(A64_V).filter(|v| *v <= A64_V_LAST)?),
    })
}

/// Names an arm64 register as the text names its variable: `x0`, `sp`,
/// `xzr`, `v0`.
///
/// # Arguments
///
/// * `r` - The register.
fn a64_name(r: a64::Reg) -> String {
    match r {
        a64::Reg::X(n) => format!("x{n}"),
        a64::Reg::Sp => "sp".to_owned(),
        a64::Reg::Zr => "xzr".to_owned(),
        a64::Reg::V(n) => format!("v{n}"),
    }
}

/// Strips the `dll!` prefix from an import name.
///
/// # Arguments
///
/// * `name` - A symbol name, possibly `DLL!name`.
pub(super) fn bare(name: &str) -> &str {
    crate::analysis::bare_name(name)
}

/// Renders the text name of a stack slot.
///
/// # Arguments
///
/// * `off` - Byte offset from the entry stack pointer.
/// * `word` - Stack word size in bytes, which is the width of the return
///   address the arguments sit above.
/// * `shadow` - Bytes of callee-owned home space above the return address:
///   32 under the Microsoft x64 convention, 0 elsewhere.
///
/// # Returns
///
/// `local_N` below the return address, `retaddr` at it, `home_N` in the
/// shadow space above it and `arg_N` past that, where N counts from the
/// first slot past the return address: the home slots
/// are the callee's own, where it spills or keeps a local, so a write
/// there is no write to an argument.
pub(super) fn slot_name(off: i64, word: i64, shadow: i64) -> String {
    if off < 0 {
        format!("local_{:x}", -off)
    } else if off == 0 {
        "retaddr".to_owned()
    } else if off < word + shadow {
        format!("home_{:x}", off - word)
    } else {
        format!("arg_{:x}", off - word)
    }
}

impl Names<'_> {
    /// Names a stack slot: an incoming argument by its parameter name, a
    /// slot the debug information named by that name, and anything else by
    /// [`slot_name`].
    ///
    /// The arguments a convention passes on the stack sit above the return
    /// address and the shadow space, one word apart, and continue the
    /// numbering the register arguments start. A local the debug
    /// information states for the slot is the compiler's own name for it,
    /// so it beats the synthesis the way any debug name does; it names the
    /// slot alone, never its width, which the lifting's own declaration
    /// keeps stating.
    ///
    /// # Arguments
    ///
    /// * `off` - The frame offset.
    pub(super) fn slot(&self, off: i64) -> String {
        if let Some(i) = self.stack_param(off) {
            return self.key(Key::Param(i));
        }
        if let Some(name) = self.debug_locals.get(&off) {
            return name.clone();
        }
        // INVARIANT: a convention whose stack arguments start at the stack
        // pointer the function is entered with (arm64) leaves no return
        // address there: every slot from it up is the caller's.
        if self.first_stack == 0 && off >= 0 {
            return format!("arg_{off:x}");
        }
        slot_name(off, self.word, self.first_stack - self.word)
    }

    /// Names an access of `ty` to the stack slot at `off`: the slot's name
    /// where the access is as wide as its declaration, else a load or a
    /// store of that width through its address.
    ///
    /// A C variable reads and writes as wide as it is declared, where the
    /// machine reads `mov edx, [rsp+4]` over a byte slot and the three
    /// bytes above it: `*(uint32_t*)&local_c`, not `local_c`. A stack
    /// parameter read narrower than the word is its low bytes, `(uint16_t)
    /// a1`, and an access to bytes past its first reaches them through its
    /// address, `*(uint16_t*)((uint8_t*)&a2 + 2)`.
    ///
    /// # Arguments
    ///
    /// * `off` - The frame offset.
    /// * `ty` - The access type.
    ///
    /// # Returns
    ///
    /// `(text, precedence)`.
    pub(super) fn slot_at(&self, off: i64, ty: Ty) -> (String, u8) {
        // INVARIANT: an access inside a stack parameter's word, past its
        // first byte, reaches those bytes of the parameter: `movzx ecx,
        // word [ebp+0xe]` reads the high half of `_finite`'s double, which
        // read as a variable of its own was never set.
        let past = off - self.first_stack;
        let within = past.rem_euclid(self.word.max(1));
        if past > 0
            && within > 0
            && within + i64::from(ty.bits() / 8) <= self.word
            && let Some(i) = self.stack_param(off - within)
        {
            let param = self.key(Key::Param(i));
            return (
                format!("*({}*)((uint8_t*)&{param} + {within})", ty.name()),
                UNARY,
            );
        }
        let name = self.slot(off);
        // INVARIANT: a stack parameter is a value of the machine's word; a
        // narrower read of it is its low bytes (`mov cx, [ebp+8]`).
        if self.stack_param(off).is_some() {
            return if matches!(ty, Ty::U8 | Ty::U16 | Ty::U32)
                && i64::from(ty.bits()) < self.word * 8
            {
                (format!("({}){name}", ty.name()), UNARY)
            } else {
                (name, ATOM)
            };
        }
        match self.slot_types.get(&off) {
            Some(declared)
                if declared.bits() != ty.bits()
                    && !matches!(ty, Ty::U128)
                    && !matches!(declared, Ty::U128) =>
            {
                (format!("*({}*)&{name}", ty.name()), UNARY)
            }
            _ => (name, ATOM),
        }
    }

    /// The parameter index of an incoming stack-argument slot.
    ///
    /// # Arguments
    ///
    /// * `off` - The frame offset.
    ///
    /// # Returns
    ///
    /// The index, or `None` when the slot is a local or beyond the count.
    pub(super) fn stack_param(&self, off: i64) -> Option<u8> {
        let past = off.checked_sub(self.first_stack)?;
        if past < 0 || past % self.word != 0 {
            return None;
        }
        let nth = u32::try_from(past / self.word).ok()?;
        (nth < self.stack_params)
            .then(|| u8::try_from(self.reg_params + nth).ok())
            .flatten()
    }
}

/// Renders an IEEE-754 constant as a C literal (`0.5f`, `2.0`, `NAN`, `-INFINITY`).
///
/// A value whose decimal digits run long is written with an exponent
/// (`6.02e23`). One far outside any quantity a program computes with, a
/// subnormal or an exponent of 2 past +-256 for a `double` (+-64 for a
/// `float`), is almost always other bytes moved through a float register
/// (eight bytes of a wide string copied with `movsd`), so it is written as
/// the C99 hexadecimal literal of its exact bits, `0x1.0074006e0065p-1016`,
/// where the bytes still show.
///
/// # Arguments
///
/// * `bits` - The bit pattern (low 32 bits for a `float`).
/// * `ty` - [`Ty::F32`] or [`Ty::F64`]; anything else renders the bits in hex.
pub(super) fn render_fconst(bits: u64, ty: Ty) -> String {
    /// Longest decimal spelling kept without an exponent.
    const DECIMAL_MAX: usize = 24;
    let (value, text, sci, suffix) = match ty {
        Ty::F32 => {
            let f = f32::from_bits(lo32(bits));
            (f64::from(f), format!("{f}"), format!("{f:e}"), "f")
        }
        Ty::F64 => {
            let f = f64::from_bits(bits);
            (f, format!("{f}"), format!("{f:e}"), "")
        }
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => return format!("{bits:#x}"),
    };
    if value.is_nan() {
        return "NAN".to_owned();
    }
    if value.is_infinite() {
        return if value > 0.0 { "INFINITY" } else { "-INFINITY" }.to_owned();
    }
    let mut s = match wild_float(bits, ty) {
        Some(hex) => hex,
        None if text.len() > DECIMAL_MAX => sci,
        None => text,
    };
    if !s.contains(['.', 'e', 'p']) {
        s.push_str(".0");
    }
    s.push_str(suffix);
    s
}

/// The C99 hexadecimal literal of a finite float far outside any quantity
/// a program computes with ([`render_fconst`]).
///
/// # Arguments
///
/// * `bits` - The bit pattern (low 32 bits for a `float`).
/// * `ty` - [`Ty::F32`] or [`Ty::F64`].
///
/// # Returns
///
/// `0x1.<fraction>p<exponent>`, or `0x0.<fraction>p<exponent>` for a
/// subnormal; `None` for zero, a value within reach of 1, or an integer
/// type.
fn wild_float(bits: u64, ty: Ty) -> Option<String> {
    let (negative, exp, frac, digits, bias, reach) = match ty {
        Ty::F32 => {
            let b = u64::from(lo32(bits));
            (
                b >> 31 != 0,
                (b >> 23) & 0xff,
                (b & 0x7f_ffff) << 1,
                6,
                127,
                64,
            )
        }
        Ty::F64 => (
            bits >> 63 != 0,
            (bits >> 52) & 0x7ff,
            bits & 0xf_ffff_ffff_ffff,
            13,
            1023,
            256,
        ),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => return None,
    };
    if (exp == 0 && frac == 0) || (exp != 0 && exp.abs_diff(bias) <= reach) {
        return None;
    }
    let (lead, power) = if exp == 0 {
        (0, 1 - bias.cast_signed())
    } else {
        (1, exp.cast_signed() - bias.cast_signed())
    };
    let fraction = format!("{frac:0digits$x}");
    let fraction = fraction.trim_end_matches('0');
    let dot = if fraction.is_empty() { "" } else { "." };
    let sign = if negative { "-" } else { "" };
    Some(format!("{sign}0x{lead}{dot}{fraction}p{power}"))
}

/// Returns the C type a cast to `ty` spells: floats by name, integers as
/// their signed form (the conversions that produce them are signed).
///
/// # Arguments
///
/// * `ty` - The target type.
fn cast_name(ty: Ty) -> &'static str {
    match ty {
        Ty::F32 | Ty::F64 | Ty::U128 => ty.name(),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 => signed_ty(ty.bits()),
    }
}

/// The low bits an `and` mask clears, when it clears only those.
///
/// A mask with its top bit set and fewer than twelve low bits off is a
/// clearing mask: `x & 0xffffffffffffff00` reads better as `x & ~0xff`.
///
/// # Arguments
///
/// * `mask` - The right operand of the `and`.
fn low_clear(mask: &Expr) -> Option<u64> {
    match mask {
        Expr::Const(c) if *c >= 1 << 63 && !*c < 0x1000 => Some(!*c),
        _ => None,
    }
}

/// Renders a constant: small values as decimal, small negatives as `-N`, the rest as hex.
///
/// # Arguments
///
/// * `v` - The constant.
/// * `hex` - The context prefers hex (bitwise masks, address arithmetic):
///   values of ten and up render as hex and negatives stay hex.
pub(super) fn render_const(v: u64, hex: bool) -> String {
    render_const_in(v, hex, 8)
}

/// Renders a constant as [`render_const`] does, reading it as a value of
/// the machine word: on a 32-bit target `0xffffffff` is `-1`.
///
/// A value that spells four characters reads as the code it spells
/// ([`fourcc_literal`]).
///
/// # Arguments
///
/// * `v` - The constant.
/// * `hex` - Render in hex (inside bitwise operators).
/// * `word` - The machine word in bytes.
pub(super) fn render_const_in(v: u64, hex: bool, word: i64) -> String {
    if !hex
        && v >= 256
        && let Some(code) = fourcc_literal(v)
    {
        return code;
    }
    render_number(v, hex, word)
}

/// Renders a constant as a number of the machine word, never as the
/// characters it might spell.
///
/// # Arguments
///
/// * `v` - The constant.
/// * `hex` - Render in hex (inside bitwise operators).
/// * `word` - The machine word in bytes.
fn render_number(v: u64, hex: bool, word: i64) -> String {
    if hex && v >= 10 {
        return format!("{v:#x}");
    }
    if v < 256 {
        return v.to_string();
    }
    if !hex && let Some(m) = negative_magnitude(v, word) {
        return format!("-{m}");
    }
    format!("{v:#x}")
}

/// Renders a constant that spells four printable characters as the
/// multi-character literal the source wrote, `'AUEV'`.
///
/// Nebula3 registers every class and attribute under such a code and a
/// DDS header names its pixel format by one; the number is the code read
/// with its first character in the high byte, as MSVC evaluates the
/// literal, so `MAKEFOURCC('D','X','T','5')` reads `'5TXD'`. Four
/// printable bytes with at least three letters or digits among them are
/// taken as a code: a mask or a size nearly always has a byte below a
/// space or above a tilde.
///
/// # Arguments
///
/// * `v` - The constant.
///
/// # Returns
///
/// The literal, or `None` for a number.
pub(super) fn fourcc_literal(v: u64) -> Option<String> {
    let bytes = u32::try_from(v).ok()?.to_be_bytes();
    if !bytes.iter().all(|b| (0x20..0x7f).contains(b))
        || bytes.iter().filter(|b| b.is_ascii_alphanumeric()).count() < 3
    {
        return None;
    }
    let text: String = bytes
        .iter()
        .flat_map(|&b| match b {
            b'\\' => vec!['\\', '\\'],
            b'\'' => vec!['\\', '\''],
            _ => vec![char::from(b)],
        })
        .collect();
    Some(format!("'{text}'"))
}

/// Reads a constant as a negative number of the machine word.
///
/// A value with the sign bit of the word set whose magnitude fits in
/// thirty-two bits (sixteen on a 32-bit word, so `0x80000000` stays the
/// flag it usually is) is the negative number the source wrote.
///
/// # Arguments
///
/// * `v` - The constant.
/// * `word` - The machine word in bytes.
///
/// # Returns
///
/// The magnitude, or `None` when the value reads better unsigned.
pub(super) fn negative_magnitude(v: u64, word: i64) -> Option<u64> {
    let wide = (v >= 1 << 63 && v.wrapping_neg() <= 0xffff_ffff).then(|| v.wrapping_neg());
    if word != 4 {
        return wide;
    }
    // INVARIANT: a 32-bit immediate arrives zero-extended when the decoder
    // read a 32-bit operand and sign-extended to 64 bits when it read an
    // 8-bit one; both spell the same number.
    if v > 0x7fff_ffff && v <= 0xffff_ffff {
        let m = (1u64 << 32) - v;
        return (m <= 0xffff).then_some(m);
    }
    wide.filter(|m| *m <= 0xffff)
}

impl Expr {
    /// Renders the expression as C text.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution for variables and globals.
    pub(super) fn render(&self, n: &Names<'_>) -> String {
        self.render_prec(n, false, false).0
    }

    /// Renders the expression with its outermost precedence.
    ///
    /// Operands are parenthesized when their precedence is lower, when they
    /// share the precedence of a non-commutative operator on the right, or
    /// when they belong to another operator family. `x + (-c)` renders as
    /// `x - c`.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `hex` - Render constants in hex (inside bitwise operators).
    /// * `address` - The expression is the address a load or store goes
    ///   through, or a term of its sum, where a constant may be the string
    ///   literal read from (`"0123456789abcdef"[i]`).
    ///
    /// # Returns
    ///
    /// `(text, precedence of the outermost operator)`.
    fn render_prec(&self, n: &Names<'_>, hex: bool, address: bool) -> (String, u8) {
        self.render_in(n, hex, address, true)
    }

    /// Renders the expression as [`Expr::render_prec`] does, knowing
    /// whether the bits above the low 32 of its value are read.
    ///
    /// The machine's arithmetic is 64 bits wide where C computes a narrow
    /// operand in `int` or `unsigned int`: `*(uint16_t*)p << 0x20` shifts
    /// the word out of an `int` where `shl rax, 0x20` keeps it. Where the
    /// upper bits are read and the text's shift or product would lose them
    /// ([`computes_narrow`]), its left operand is cast to `uint64_t`; under
    /// a mask to 32 bits or fewer they are not read, and the text stays as
    /// it is. C's `>>`, `/` and `%` on a signed operand are the signed
    /// ones, so a logical shift, quotient or remainder whose operand's text
    /// is signed ([`signed_text`]) casts it to the unsigned word first:
    /// `(uint64_t)(int64_t)(int32_t)x >> 1`.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `hex` - Render constants in hex (inside bitwise operators).
    /// * `address` - The expression is an address or a term of its sum
    ///   ([`Expr::render_prec`]).
    /// * `wide` - The bits above the low 32 of the value are read.
    ///
    /// # Returns
    ///
    /// `(text, precedence of the outermost operator)`.
    fn render_in(&self, n: &Names<'_>, hex: bool, address: bool, wide: bool) -> (String, u8) {
        match self {
            Expr::Const(v) => (
                n.const_name(*v, true)
                    .unwrap_or_else(|| render_const_in(*v, hex, n.word)),
                ATOM,
            ),
            Expr::Var(k) => (n.key(*k), ATOM),
            Expr::Str(s) => (s.clone(), ATOM),
            Expr::Sp(k) => (format!("&{}", n.slot(*k)), UNARY),
            Expr::FConst(bits, ty) => (render_fconst(*bits, *ty), ATOM),
            Expr::Call(f, args) => {
                let args: Vec<String> = args
                    .iter()
                    .map(|a| a.render_prec(n, true, false).0)
                    .collect();
                (format!("{f}({})", args.join(", ")), ATOM)
            }
            Expr::Cast(e, ty) => {
                let (es, ep) = match &**e {
                    Expr::Sext(inner, bits) => {
                        let (s, p) = inner.render_prec(n, false, false);
                        let s = if p < UNARY { format!("({s})") } else { s };
                        (format!("({}){s}", signed_ty(*bits)), UNARY)
                    }
                    other => other.render_prec(n, false, false),
                };
                let es = if ep < UNARY { format!("({es})") } else { es };
                (format!("({}){es}", cast_name(*ty)), UNARY)
            }
            Expr::Bin(op, l, r) => {
                if let Op::FMin | Op::FMax = op {
                    let name = if *op == Op::FMin { "fmin" } else { "fmax" };
                    return (format!("{name}({}, {})", l.render(n), r.render(n)), ATOM);
                }
                // INVARIANT: a rotate of 16 bits by 8 swaps its two bytes,
                // which `bswap` of the half word says as C's readers know it.
                if let (Op::Rol(16) | Op::Ror(16), Expr::Const(8)) = (op, r.as_ref()) {
                    let half = match l.as_ref() {
                        Expr::Deref(_, Ty::U16) | Expr::Cast(_, Ty::U16) => l.render(n),
                        other => Expr::Cast(Box::new(low_bits_read(other.clone(), 16)), Ty::U16)
                            .render(n),
                    };
                    return (format!("bswap({half})"), ATOM);
                }
                if let Op::Rol(w)
                | Op::Ror(w)
                | Op::MulHi(w)
                | Op::SMulHi(w)
                | Op::SMulO(w)
                | Op::UAddO(w)
                | Op::USubO(w) = op
                {
                    let name = match op {
                        Op::Rol(_) => "rotl",
                        Op::Ror(_) => "rotr",
                        Op::MulHi(_) => "mulhi",
                        Op::SMulHi(_) => "smulhi",
                        Op::UAddO(_) => "uaddo",
                        Op::USubO(_) => "usubo",
                        _ => "smulo",
                    };
                    return (
                        format!(
                            "{name}{w}({}, {})",
                            number(l, n, false).0,
                            number(r, n, false).0
                        ),
                        ATOM,
                    );
                }
                let p = op.prec();
                let hexo = hex || op.hex_operands();
                let sum = address && matches!(op, Op::Add | Op::Sub);
                // INVARIANT: the low bits of a sum, a difference, a product,
                // a left shift or a bitwise operation are read from the low
                // bits of its operands alone; a mask to 32 bits reads no more,
                // and any other operation reads them all.
                let inner = match (op, &**r) {
                    (Op::And, Expr::Const(m)) if *m <= 0xffff_ffff => false,
                    (Op::Add | Op::Sub | Op::Mul | Op::Shl | Op::And | Op::Or | Op::Xor, _) => wide,
                    _ => true,
                };
                let widen = wide && !address && n.word == 8 && computes_narrow(*op, l, r);
                let widened = |(s, sp): (String, u8)| {
                    if widen {
                        let s = if sp < UNARY { format!("({s})") } else { s };
                        (format!("(uint64_t){s}"), UNARY)
                    } else {
                        (s, sp)
                    }
                };
                if *op == Op::Add
                    && let Expr::Const(c) = **r
                    && let Some(m) = negative_magnitude(c, n.word)
                {
                    let (ls, lp) = widened(l.render_in(n, hexo, sum, inner));
                    let ls = if lp < p { format!("({ls})") } else { ls };
                    return (format!("{ls} - {m}"), p);
                }
                // INVARIANT: a constant a bitwise operator applies is a mask,
                // never an address, even when its value lands in the image
                // (`and edi, 0xff00ff` is not `edi & "some literal"`); one
                // any other operator applies is no string literal unless it
                // is a term of an address loaded through, or the first
                // character of a string a sum indexes (`i * 3 +
                // "SunMonTue"`); the empty string is a lone terminator no
                // sum indexes, so a term landing on one keeps its address.
                let indexes = |v: u64| matches!(op, Op::Add | Op::Sub) && n.starts_string(v);
                let operand = |e: &Expr| match e {
                    Expr::Const(v) if op.hex_operands() => {
                        (render_const_in(*v, true, n.word), ATOM)
                    }
                    Expr::Const(v) if !sum && !indexes(*v) => number(e, n, hexo),
                    Expr::Const(v) if sum && n.empty_literal(*v) => number(e, n, hexo),
                    _ => e.render_in(n, hexo, sum, inner),
                };
                let (ls, lp) = match (op, &**l) {
                    // INVARIANT: a logical shift shifts the constant's
                    // unsigned bits, which only its hex spelling has: `-1 >>
                    // n` shifts an `int` and keeps its sign.
                    (Op::Shr, Expr::Const(v)) if negative_magnitude(*v, n.word).is_some() => {
                        (render_const_in(*v, true, n.word), ATOM)
                    }
                    _ => widened(operand(l)),
                };
                let (rs, rp) = operand(r);
                let other_family = |e: &Expr| match e {
                    Expr::Bin(o, ..) => {
                        o.family() != op.family() || (*o != *op && op.family() == 2)
                    }
                    _ => false,
                };
                let wrapped = lp < p || other_family(l);
                let ls = if wrapped { format!("({ls})") } else { ls };
                let cast = |ty: &str, ls: String| {
                    if wrapped || lp >= UNARY {
                        format!("({ty}){ls}")
                    } else {
                        format!("({ty})({ls})")
                    }
                };
                let rs = if rp < p || (rp == p && !op.commutative()) || other_family(r) {
                    format!("({rs})")
                } else {
                    rs
                };
                match op {
                    Op::SDiv | Op::SRem => {
                        // INVARIANT: a narrow signed quotient converts back
                        // to 64 bits by sign extension, so dividing the
                        // narrow value is dividing its extension.
                        let signed = |side: &Expr, text: String| {
                            if let Expr::Sext(inner, from) = side {
                                let (s, p) = inner.render_prec(n, hex, false);
                                let s = if p < UNARY { format!("({s})") } else { s };
                                format!("({}){s}", signed_ty(*from))
                            } else if text.starts_with("(int64_t)")
                                || matches!(side, Expr::Const(_))
                            {
                                text
                            } else {
                                format!("(int64_t){text}")
                            }
                        };
                        let rs = match **r {
                            Expr::Const(c) => c.to_string(),
                            _ => rs,
                        };
                        (
                            format!("{} {} {}", signed(l, ls), op.sym(), signed(r, rs)),
                            p,
                        )
                    }
                    Op::Shr | Op::Div | Op::Rem
                        if signed_text(l) || (*op != Op::Shr && signed_text(r)) =>
                    {
                        let rs = match **r {
                            Expr::Const(c) if *op != Op::Shr => c.to_string(),
                            _ => rs,
                        };
                        let unsigned = if n.word == 4 { "uint32_t" } else { "uint64_t" };
                        (format!("{} {} {rs}", cast(unsigned, ls), op.sym()), p)
                    }
                    Op::Div | Op::Rem if matches!(**r, Expr::Const(_)) => {
                        let rs = match **r {
                            Expr::Const(c) => c.to_string(),
                            _ => rs,
                        };
                        (format!("{ls} {} {rs}", op.sym()), p)
                    }
                    Op::And if low_clear(r).is_some() => {
                        let cleared = low_clear(r).map_or(0, |c| c);
                        (format!("{ls} & ~{}", render_const(cleared, true)), p)
                    }
                    Op::Sar => {
                        let ls = if ls.starts_with("(int64_t)") {
                            ls
                        } else {
                            cast("int64_t", ls)
                        };
                        (format!("{ls} >> {rs}"), p)
                    }
                    _ => (format!("{ls} {} {rs}", op.sym()), p),
                }
            }
            Expr::Un(op, e) => match op.func_name() {
                Some(f) => (format!("{f}({})", e.render(n)), ATOM),
                None => {
                    let (es, ep) = number(e, n, hex);
                    let es = if ep < UNARY { format!("({es})") } else { es };
                    let sym = if *op == UnOp::Neg { "-" } else { "~" };
                    (format!("{sym}{es}"), UNARY)
                }
            },
            Expr::Deref(a, ty) => {
                if let Expr::Sp(k) = **a {
                    return n.slot_at(k, *ty);
                }
                if let Some(field) = teb_field(a, n.word) {
                    return (format!("NtCurrentTeb()->{field}"), ATOM);
                }
                render_load(a, *ty, ty.name(), n)
            }
            Expr::Cond(c) => match &c.flags {
                Flags::Truth(e, tcc) if c.cc == *tcc => e.render_prec(n, hex, false),
                flags => {
                    let text = c.render(n, false);
                    let prec = if super::structure::logical_operands(&text).is_some() {
                        LOGICAL
                    } else if matches!(flags, Flags::Truth(e, tcc)
                        if c.cc == tcc.invert() && equality(e).is_none())
                    {
                        UNARY
                    } else {
                        6
                    };
                    (text, prec)
                }
            },
            Expr::Ternary(c, a, b) => (
                format!(
                    "({} ? {} : {})",
                    c.render(n, false),
                    a.render(n),
                    b.render(n)
                ),
                ATOM,
            ),
            Expr::Sext(e, bits) => {
                if let Expr::Deref(a, ty) = e.as_ref()
                    && matches!(ty, Ty::U8 | Ty::U16 | Ty::U32)
                    && ty.bits() == *bits
                    && !matches!(**a, Expr::Sp(_))
                {
                    return render_load(a, *ty, signed_ty(*bits), n);
                }
                let (es, ep) = e.render_prec(n, false, false);
                let es = if ep < UNARY { format!("({es})") } else { es };
                (format!("(int64_t)({}){es}", signed_ty(*bits)), UNARY)
            }
        }
    }
}

/// Returns the condition a truth value is when it is an equality test,
/// whose negation is the inequality, NaN operands included: `!(a == b)` is
/// `a != b`, where `!(a < b)` is not `a >= b` for floats.
///
/// # Arguments
///
/// * `e` - The truth value.
fn equality(e: &Expr) -> Option<&Cond> {
    match e {
        Expr::Cond(c) if matches!(c.cc.0, ConditionCode::e | ConditionCode::ne) => Some(c),
        _ => None,
    }
}

/// Renders a sign test of a value at a width: `(int32_t)x < 0`.
///
/// The value is parenthesized only when its own operator binds looser than
/// the cast, so a variable or a load reads bare.
///
/// # Arguments
///
/// * `n` - Names for the rendering.
/// * `bits` - The width the sign is read at.
/// * `e` - The value.
/// * `rel` - The relation to zero: `<`, `>=`, `<=` or `>`.
fn signed_sign(n: &Names<'_>, bits: u8, e: &Expr, rel: &str) -> String {
    let (s, p) = number(e, n, false);
    let s = if p < UNARY { format!("({s})") } else { s };
    format!("({}){s} {rel} 0", signed_ty(bits))
}

impl Cond {
    /// Renders the condition as a C boolean expression.
    ///
    /// Flags set in another block or by an unmodeled instruction render as
    /// the obviously symbolic `FLAGS_UNKNOWN`, never as a fake constant. A
    /// `test` can never set CF, so `b`/`ae` after it are the constants `0`
    /// and `1` with a comment. A test of `setcc` results joined by `|` or
    /// `&` reads as the `||` or `&&` chain it is ([`render_truth_chain`]).
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `inverted` - Render the negated condition.
    pub(super) fn render(&self, n: &Names<'_>, inverted: bool) -> String {
        let text = self.render_plain(n, inverted);
        if self.eval().is_none()
            && let Some((outcome, evidence)) = super::opaque::constant_outcome(self)
        {
            return format!("{text} {}", opaque_note(outcome, inverted, evidence));
        }
        text
    }

    /// Renders the condition without judging whether its outcome can vary.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `inverted` - Render the negated condition.
    fn render_plain(&self, n: &Names<'_>, inverted: bool) -> String {
        if let Some(s) = self.simplify() {
            return s.render(n, inverted);
        }
        let cc = if inverted { self.cc.invert() } else { self.cc };
        use ConditionCode as C;
        if let Some(inner) = self.bool_operand() {
            match cc.0 {
                C::e => return inner.render(n, true),
                C::ne => return inner.render(n, false),
                _ => {}
            }
        }
        if let Some(chain) = self.tested().filter(|e| is_truth_chain(e)) {
            match cc.0 {
                C::e => return render_truth_chain(chain, n, true),
                C::ne => return render_truth_chain(chain, n, false),
                _ => {}
            }
        }
        match &self.flags {
            Flags::Unknown => {
                if inverted {
                    "!FLAGS_UNKNOWN".to_owned()
                } else {
                    "FLAGS_UNKNOWN".to_owned()
                }
            }
            Flags::Carry(e) => match cc.0 {
                C::b | C::o => format!("{} != 0", paren_if_lower(e, n, 6)),
                C::ae | C::no => format!("{} == 0", paren_if_lower(e, n, 6)),
                _ => undecided(n, self.cc, inverted, &[e]),
            },
            Flags::Shift(e, bits, c) => {
                let flags = match cc.0 {
                    C::be | C::a => {
                        let (bit, zero, join) = if cc.0 == C::be {
                            ("!=", "==", "||")
                        } else {
                            ("==", "!=", "&&")
                        };
                        return format!(
                            "({} {bit} 0 {join} {} {zero} 0)",
                            paren_if_lower(c, n, 6),
                            paren_if_lower(e, n, 6)
                        );
                    }
                    C::b | C::ae => Flags::Carry(c.clone()),
                    // The overflow of a shift is not its carry: `shl x, 1`
                    // sets it to the top bit of the result against CF, and
                    // a longer shift leaves it undefined.
                    C::o | C::no => return undecided(n, self.cc, inverted, &[e, c]),
                    _ => Flags::Result(e.clone(), *bits),
                };
                Cond { cc: self.cc, flags }.render(n, inverted)
            }
            Flags::Truth(e, tcc) if is_truth_chain(e) && (cc == *tcc || cc == tcc.invert()) => {
                render_truth_chain(e, n, cc != *tcc)
            }
            Flags::Truth(e, tcc) if cc == *tcc => e.render(n),
            Flags::Truth(e, tcc) if cc == tcc.invert() => match equality(e) {
                Some(inner) => inner.render(n, true),
                None => format!("!{}", paren_if_lower(e, n, UNARY)),
            },
            Flags::Truth(e, _) => undecided(n, self.cc, inverted, &[e]),
            Flags::Cmp(l, r, bits) if matches!(cc.0, C::p | C::np) => {
                let unordered = l.is_float()
                    || r.is_float()
                    || super::line::float_like(&l.render(n))
                    || super::line::float_like(&r.render(n));
                let not = if cc.0 == C::np { "!" } else { "" };
                if unordered {
                    format!("{not}isunordered({}, {})", l.render(n), r.render(n))
                } else {
                    parity(n, cc, &fold(Op::Sub, l.clone(), r.clone(), *bits))
                }
            }
            Flags::Cmp(l, r, _)
                if (l.is_float() || r.is_float())
                    && matches!(cc.0, C::a | C::ae | C::b | C::be) =>
            {
                float_relation(n, cc, l, r)
            }
            Flags::Cmp(l, r, bits) if matches!(cc.0, C::s | C::ns) => signed_sign(
                n,
                *bits,
                &fold(Op::Sub, l.clone(), r.clone(), *bits),
                if cc.0 == C::s { "<" } else { ">=" },
            ),
            Flags::Cmp(l, r, bits) => match cc.rel() {
                Some(rel @ ("==" | "!=")) => match vector_equality(l, r) {
                    Some((a, b)) => compare(
                        n,
                        &packed_literal(n, a).unwrap_or_else(|| a.clone()),
                        &packed_literal(n, b).unwrap_or_else(|| b.clone()),
                        rel,
                        false,
                        128,
                    ),
                    None => compare(n, l, r, rel, cc.signed(), *bits),
                },
                Some(rel) => compare(n, l, r, rel, cc.signed(), *bits),
                None => match cc.0 {
                    C::o => format!(
                        "ssubo{bits}({}, {}) != 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::no => format!(
                        "ssubo{bits}({}, {}) == 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    _ => undecided(n, self.cc, inverted, &[l, r]),
                },
            },
            Flags::Add(l, r, bits) => {
                let sum = fold(Op::Add, l.clone(), r.clone(), *bits);
                match cc.0 {
                    C::e => format!("{} == 0", paren_if_lower(&sum, n, 6)),
                    C::ne => format!("{} != 0", paren_if_lower(&sum, n, 6)),
                    C::s => signed_sign(n, *bits, &sum, "<"),
                    C::ns => signed_sign(n, *bits, &sum, ">="),
                    C::l => sum_relation(n, l, r, *bits, "<"),
                    C::ge => sum_relation(n, l, r, *bits, ">="),
                    C::le => sum_relation(n, l, r, *bits, "<="),
                    C::g => sum_relation(n, l, r, *bits, ">"),
                    C::b => format!(
                        "uaddo{bits}({}, {}) != 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::ae => format!(
                        "uaddo{bits}({}, {}) == 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::o => format!(
                        "saddo{bits}({}, {}) != 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::no => format!(
                        "saddo{bits}({}, {}) == 0",
                        number(l, n, false).0,
                        number(r, n, false).0
                    ),
                    C::be => format!(
                        "(uaddo{bits}({}, {}) != 0 || {} == 0)",
                        number(l, n, false).0,
                        number(r, n, false).0,
                        paren_if_lower(&sum, n, 6)
                    ),
                    C::a => format!(
                        "(uaddo{bits}({}, {}) == 0 && {} != 0)",
                        number(l, n, false).0,
                        number(r, n, false).0,
                        paren_if_lower(&sum, n, 6)
                    ),
                    C::p | C::np => parity(n, cc, &sum),
                    C::None => undecided(n, self.cc, inverted, &[l, r]),
                }
            }
            Flags::Test(l, r, bits) => {
                let single = l == r;
                let and = if single {
                    l.clone()
                } else {
                    fold(Op::And, l.clone(), r.clone(), *bits)
                };
                match cc.0 {
                    C::e | C::ne => format!(
                        "{} {} 0",
                        paren_if_lower(&and, n, 6),
                        if cc.0 == C::e { "==" } else { "!=" }
                    ),
                    C::s | C::l => signed_sign(n, *bits, &and, "<"),
                    C::ns | C::ge => signed_sign(n, *bits, &and, ">="),
                    C::le => signed_sign(n, *bits, &and, "<="),
                    C::g => signed_sign(n, *bits, &and, ">"),
                    C::b => "0 /*CF=0 after test*/".to_owned(),
                    C::ae => "1 /*CF=0 after test*/".to_owned(),
                    C::o => "0 /*OF=0 after test*/".to_owned(),
                    C::no => "1 /*OF=0 after test*/".to_owned(),
                    C::be => format!("{} == 0", paren_if_lower(&and, n, 6)),
                    C::a => format!("{} != 0", paren_if_lower(&and, n, 6)),
                    C::p | C::np => parity(n, cc, &and),
                    C::None => undecided(n, self.cc, inverted, &[l, r]),
                }
            }
            Flags::Result(e, bits) => match cc.0 {
                C::e => format!("{} == 0", paren_if_lower(e, n, 6)),
                C::ne => format!("{} != 0", paren_if_lower(e, n, 6)),
                C::s | C::l => signed_sign(n, *bits, e, "<"),
                C::ns | C::ge => signed_sign(n, *bits, e, ">="),
                C::le => signed_sign(n, *bits, e, "<="),
                C::g => signed_sign(n, *bits, e, ">"),
                C::p | C::np => parity(n, cc, e),
                C::b | C::ae | C::be | C::a | C::None | C::o | C::no => {
                    undecided(n, self.cc, inverted, &[e])
                }
            },
        }
    }
}

/// Tells whether a value is truth values joined by `|` and `&`: what
/// `setcc` results combined before one test leave (`sete al; setle cl; or
/// al, cl`), each leaf a condition's 0 or 1.
///
/// # Arguments
///
/// * `e` - The value.
fn is_truth_chain(e: &Expr) -> bool {
    match e {
        Expr::Bin(Op::Or | Op::And, a, b) => [a.as_ref(), b.as_ref()]
            .into_iter()
            .all(|x| matches!(x, Expr::Cond(_)) || is_truth_chain(x)),
        _ => false,
    }
}

/// Renders truth values joined by `|` and `&` ([`is_truth_chain`]) as the
/// `||` and `&&` they mean, or their negation by De Morgan.
///
/// Both sides of `|` are 0 or 1, so the value is nonzero exactly when
/// either condition holds; `||` reads that way, and the operand it may now
/// skip is a condition, which computes nothing the text needs. A nested
/// chain of the other operator keeps its parentheses.
///
/// # Arguments
///
/// * `e` - The chain.
/// * `n` - Name resolution.
/// * `negate` - Render the chain being zero instead.
fn render_truth_chain(e: &Expr, n: &Names<'_>, negate: bool) -> String {
    match e {
        Expr::Bin(op @ (Op::Or | Op::And), a, b) => {
            let joint = if (*op == Op::Or) == negate {
                "&&"
            } else {
                "||"
            };
            let side = |x: &Expr| {
                let text = render_truth_chain(x, n, negate);
                match super::structure::logical_operands(&text) {
                    Some((o, _)) if o != joint => format!("({text})"),
                    Some(_) | None => text,
                }
            };
            format!("{} {joint} {}", side(a), side(b))
        }
        Expr::Cond(c) => c.render(n, negate),
        other => format!(
            "{} {} 0",
            paren_if_lower(other, n, 6),
            if negate { "==" } else { "!=" }
        ),
    }
}

/// Renders a condition the recorded flags cannot decide as the opaque test
/// `flags_b(x)`: condition code `b` of the flags an operation on `x` left.
///
/// The carry an arithmetic result leaves depends on the operation, which
/// [`Flags::Result`] does not keep, and so on for the other undecided
/// shapes. Spelled as a call the condition is still C, and negated it is
/// the same call under `!`, so a condition and its inversion stay each
/// other's negation; a bare value with a comment would read as the value's
/// truth both ways.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `cc` - The condition code as recorded, before any inversion.
/// * `inverted` - Render the negation.
/// * `operands` - What the flags were computed from.
fn undecided(n: &Names<'_>, cc: Cc, inverted: bool, operands: &[&Expr]) -> String {
    let args: Vec<String> = operands.iter().map(|e| number(e, n, false).0).collect();
    let not = if inverted { "!" } else { "" };
    format!("{not}flags_{:?}({})", cc.0, args.join(", "))
}

/// Renders the parity flag of a value: `p` holds when the low byte has an
/// even number of set bits, `parity8(x)`, and `np` is its negation.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `cc` - `p` or `np`.
/// * `e` - The value the flags were set from.
fn parity(n: &Names<'_>, cc: Cc, e: &Expr) -> String {
    let not = if cc.0 == ConditionCode::np { "!" } else { "" };
    format!("{not}parity8({})", e.render(n))
}

/// Renders `e`, parenthesized when its precedence is below `prec`.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `n` - Name resolution.
/// * `prec` - Precedence of the operator `e` becomes an operand of.
fn paren_if_lower(e: &Expr, n: &Names<'_>, prec: u8) -> String {
    let (s, p) = e.render_prec(n, false, false);
    if p < prec { format!("({s})") } else { s }
}

/// Renders an operand of arithmetic.
///
/// A constant there is a number, a bound or a multiplier: it may still
/// name the function, symbol or variable at its value (a pointer to a
/// table's end), but not the string literal that happens to sit there, nor
/// the characters its bytes happen to spell. In a 32-bit image every
/// constant from the image base up lands somewhere in it, and `imul eax,
/// 0x1010101` is not `a2 * "void) const"`; the magic multiplier of a
/// division by three is `0x55555556`, not `'UUUV'`.
///
/// # Arguments
///
/// * `e` - The operand.
/// * `n` - Name resolution.
/// * `hex` - Render a constant in hex.
///
/// # Returns
///
/// `(text, precedence of the outermost operator)`.
fn number(e: &Expr, n: &Names<'_>, hex: bool) -> (String, u8) {
    match e {
        Expr::Const(v) => (
            n.const_name(*v, false)
                .unwrap_or_else(|| render_number(*v, hex, n.word)),
            ATOM,
        ),
        _ => e.render_prec(n, hex, false),
    }
}

/// Renders an operand of a comparison, parenthesized when its precedence
/// is below `prec`.
///
/// A constant there is a bound or a tag the value is tested against: it
/// reads as the code it spells (`id == 'MESH'`, a switch over tags lowered
/// to `id > '3TXD'`), but as for [`number`] never as a string literal.
///
/// # Arguments
///
/// * `e` - The operand.
/// * `n` - Name resolution.
/// * `prec` - Precedence of the operator `e` becomes an operand of.
fn paren_compared(e: &Expr, n: &Names<'_>, prec: u8) -> String {
    let (s, p) = match e {
        Expr::Const(v) => (
            n.const_name(*v, false)
                .unwrap_or_else(|| render_const_in(*v, false, n.word)),
            ATOM,
        ),
        _ => e.render_prec(n, false, false),
    };
    if p < prec { format!("({s})") } else { s }
}

/// Names a read through the thread environment block's segment.
///
/// `fs:[K]` on a 32-bit target and `gs:[K]` on a 64-bit one address the
/// current thread's TEB, and the fields a program reads there are a
/// short, fixed list: the exception chain, the stack bounds, the TEB's
/// own address, the process and thread ids, the thread-local storage
/// pointer, the PEB and the last error.
///
/// # Arguments
///
/// * `addr` - The address expression: the segment register, alone or
///   plus a constant.
/// * `word` - Machine word in bytes, which decides the layout.
///
/// # Returns
///
/// The field's name, or `None` when the read is not through the segment
/// or lands on no known field.
fn teb_field(addr: &Expr, word: i64) -> Option<&'static str> {
    let (seg, off) = match addr {
        Expr::Var(Key::Reg(r)) => (*r, 0),
        Expr::Bin(Op::Add, a, b) => match (&**a, &**b) {
            (Expr::Var(Key::Reg(r)), Expr::Const(k)) | (Expr::Const(k), Expr::Var(Key::Reg(r))) => {
                (*r, *k)
            }
            _ => return None,
        },
        _ => return None,
    };
    let wide = match (seg, word) {
        (Register::FS, 4) => false,
        (Register::GS, 8) => true,
        _ => return None,
    };
    TEB_FIELDS
        .iter()
        .find(|&&(_, at32, at64)| off == if wide { at64 } else { at32 })
        .map(|&(name, ..)| name)
}

/// The thread block fields the text names, with their offsets.
///
/// Each one's offset in a 32-bit block and in a 64-bit one: the exception
/// chain, the stack bounds, the block's own address, the process and
/// thread ids, the thread-local storage pointer, the PEB and the last
/// error. Every one is a machine word but `LastErrorValue`, 32 bits.
pub(super) const TEB_FIELDS: [(&str, u64, u64); 9] = [
    ("NtTib.ExceptionList", 0x00, 0x00),
    ("NtTib.StackBase", 0x04, 0x08),
    ("NtTib.StackLimit", 0x08, 0x10),
    ("NtTib.Self", 0x18, 0x30),
    ("ClientId.UniqueProcess", 0x20, 0x40),
    ("ClientId.UniqueThread", 0x24, 0x48),
    ("ThreadLocalStoragePointer", 0x2c, 0x58),
    ("ProcessEnvironmentBlock", 0x30, 0x60),
    ("LastErrorValue", 0x34, 0x68),
];

/// The C type a text expression computes in where it is narrower than the
/// machine's 64 bits ([`c_narrow`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Narrow {
    /// `int`: a promoted byte or word, a constant up to `INT_MAX`, a truth
    /// value.
    Int,
    /// `unsigned int`: a 32-bit load, a constant past `INT_MAX` that fits
    /// 32 bits.
    UInt,
}

/// The type C computes two operands in, by the usual conversions: `None`
/// when either is 64 bits wide.
///
/// # Arguments
///
/// * `a` - One operand's type.
/// * `b` - The other's.
fn converted(a: Option<Narrow>, b: Option<Narrow>) -> Option<Narrow> {
    match (a?, b?) {
        (Narrow::Int, Narrow::Int) => Some(Narrow::Int),
        _ => Some(Narrow::UInt),
    }
}

/// The narrow C type the text of an expression computes in.
///
/// `None` when it is 64 bits wide or its type is not known (a variable, a
/// call). A `uint8_t` or `uint16_t` load promotes to `int` and a `uint32_t` one
/// is `unsigned int`; a constant is the type its literal is (a negative one
/// renders as `-m`, an `int`, except in a bitwise operation, which spells
/// it in hex); a cast to a narrow type is that signed type, and `bswap` and
/// the bit counts are their operand's; an operation that would lose bits
/// is widened when it renders ([`computes_narrow`]), so it is 64 bits wide.
///
/// # Arguments
///
/// * `e` - The expression.
fn c_narrow(e: &Expr) -> Option<Narrow> {
    let hexed = |e: &Expr| match e {
        Expr::Const(v) if *v > 0xffff_ffff => None,
        other => c_narrow(other),
    };
    match e {
        Expr::Const(v) => match *v {
            0..=0x7fff_ffff => Some(Narrow::Int),
            0x8000_0000..=0xffff_ffff => Some(Narrow::UInt),
            v => negative_magnitude(v, 8).map(|_| Narrow::Int),
        },
        Expr::Deref(_, Ty::U8 | Ty::U16) | Expr::Cond(_) => Some(Narrow::Int),
        Expr::Deref(_, Ty::U32) => Some(Narrow::UInt),
        Expr::Cast(_, Ty::U8 | Ty::U16 | Ty::U32) => Some(Narrow::Int),
        Expr::Un(
            UnOp::Neg
            | UnOp::Not
            | UnOp::Bswap
            | UnOp::Tzcnt
            | UnOp::Lzcnt
            | UnOp::Popcnt
            | UnOp::Bsf
            | UnOp::Bsr,
            x,
        ) => c_narrow(x),
        Expr::Bin(op @ (Op::Shl | Op::Mul), l, r) => {
            if computes_narrow(*op, l, r) {
                None
            } else if *op == Op::Shl {
                c_narrow(l)
            } else {
                converted(c_narrow(l), c_narrow(r))
            }
        }
        Expr::Bin(Op::Add | Op::Sub, l, r) => converted(c_narrow(l), c_narrow(r)),
        Expr::Bin(Op::Shr, l, _) => c_narrow(l),
        Expr::Bin(Op::Div | Op::Rem, l, r) => converted(c_narrow(l), c_narrow(r)),
        Expr::Bin(Op::And | Op::Or | Op::Xor, l, r) => converted(hexed(l), hexed(r)),
        Expr::Ternary(_, a, b) => converted(c_narrow(a), c_narrow(b)),
        _ => None,
    }
}

/// The most bits the machine's value of an expression occupies: a load its
/// width, a constant its length, a product the sum of its operands'.
///
/// # Arguments
///
/// * `e` - The expression.
fn value_bits(e: &Expr) -> u64 {
    match e {
        Expr::Const(v) => u64::from(64 - v.leading_zeros()),
        Expr::Deref(_, ty) => u64::from(ty.bits()).min(64),
        Expr::Cond(_) => 1,
        Expr::Bin(op, l, r) => {
            let (a, b) = (value_bits(l), value_bits(r));
            match (op, &**r) {
                (Op::And, _) => a.min(b),
                (Op::Or | Op::Xor, _) => a.max(b),
                (Op::Add, _) => (a.max(b) + 1).min(64),
                (Op::Mul, _) => (a + b).min(64),
                (Op::Shl, Expr::Const(c)) => a.saturating_add(*c).min(64),
                (Op::Shr, Expr::Const(c)) => a.saturating_sub(*c),
                (Op::Shr | Op::Div | Op::Rem, _) => a,
                _ => 64,
            }
        }
        Expr::Ternary(_, a, b) => value_bits(a).max(value_bits(b)),
        _ => 64,
    }
}

/// Tells whether C computes a 64-bit left shift or product of the machine
/// narrower than it is, so that its text loses bits the machine keeps.
///
/// In `int` a result loses bits past 31, in `unsigned int` past 32. A sum
/// or a difference is left as it is: the lifter keeps a 32-bit one unmasked
/// where nothing reads its upper half, and C's narrow sum is then the
/// machine's.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `l` - The left operand: the value shifted, for a shift.
/// * `r` - The right operand.
fn computes_narrow(op: Op, l: &Expr, r: &Expr) -> bool {
    let (ty, bits) = match (op, r) {
        (Op::Shl, Expr::Const(c)) => (c_narrow(l), value_bits(l).saturating_add(*c)),
        (Op::Shl, _) => (c_narrow(l), 64),
        (Op::Mul, _) => (
            converted(c_narrow(l), c_narrow(r)),
            value_bits(l) + value_bits(r),
        ),
        _ => return false,
    };
    match ty {
        None => false,
        Some(Narrow::Int) => bits > 31,
        Some(Narrow::UInt) => bits > 32,
    }
}

/// Renders a load of `ty` at `a` as `*(name*)a`, or as the array element
/// `((name*)base)[index]` when the address is one ([`indexed`]).
///
/// An unsigned integer read at a constant address in the image's data is
/// the global there (`g64_2f64f0`, the name [`Names::key`] gives it), and a
/// byte read at a data symbol plus a variable is the symbol's table indexed
/// (`sqlite3UpperToLower[c]`, `(int8_t)yyRuleInfoNRhs[r]` for a signed
/// one).
///
/// # Arguments
///
/// * `a` - The address.
/// * `ty` - The access type, for its width.
/// * `name` - The type name to print, signed or unsigned.
/// * `n` - Name resolution.
fn render_load(a: &Expr, ty: Ty, name: &str, n: &Names<'_>) -> (String, u8) {
    // INVARIANT: an integer read at a constant address in the image's data
    // is a global, named as one the lifter keys (`g64_2f64f0`, or the data
    // symbol there), which the text's readers resolve to that address and
    // width; `*(uint64_t*)0x2f64f0` said the same in more words.
    if let Expr::Const(at) = a
        && matches!(ty, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64)
        && n.program
            .section_at(*at)
            .is_some_and(|s| !s.executable && s.file_size > 0)
        && name.starts_with('u')
    {
        return (n.key(Key::Global(*at, ty.bits())), ATOM);
    }
    // INVARIANT: a byte read at a data symbol plus a variable is an entry of
    // the table the symbol names, where base and index are otherwise
    // ambiguous for one-byte elements: `sqlite3UpperToLower[c]`. The table
    // holds bytes, so a signed read converts the entry it reads.
    if ty == Ty::U8
        && matches!(name, "uint8_t" | "int8_t")
        && let Expr::Bin(Op::Add, p, q) = a
    {
        for (base, index) in [(p, q), (q, p)] {
            if let Expr::Const(at) = **base
                && !matches!(**index, Expr::Const(_))
                && let Some(s) = n
                    .analysis
                    .symbol_at(n.program, at)
                    .filter(|s| s.kind == SymbolKind::Data)
            {
                let table = crate::search::demangled_name(&s.name);
                let entry = format!("{table}[{}]", index.render(n));
                return match name {
                    "int8_t" => (format!("(int8_t){entry}"), UNARY),
                    _ => (entry, ATOM),
                };
            }
        }
    }
    if let Some((base, index)) = indexed(a, ty) {
        let (bs, bp) = base.render_prec(n, true, true);
        let bs = if bp < UNARY { format!("({bs})") } else { bs };
        let is = match &index {
            Expr::Ternary(c, x, y) => {
                format!("{} ? {} : {}", c.render(n, false), x.render(n), y.render(n))
            }
            other => other.render(n),
        };
        return (format!("(({name}*){bs})[{is}]"), ATOM);
    }
    let (as_, ap) = a.render_prec(n, true, true);
    let as_ = if ap < UNARY { format!("({as_})") } else { as_ };
    (format!("*({name}*){as_}"), UNARY)
}

/// Renders a comparison, casting both sides to the signed type when the
/// condition is signed.
///
/// A cast binds tighter than any binary operator, so non-atomic operands
/// are parenthesized; an operand already carrying an `(int64_t)` cast
/// takes no second one. An unsigned ordering of a sign-extended value
/// casts it to the unsigned type of the compared width: `ja` after `movsxd
/// rbx, ecx; cmp ebx, 0x40f` finds `-1` above `0x40f`, which C's signed
/// `(int64_t)(int32_t)a1 <= 0x40f` does not. So does an ordering of a
/// difference C computes in `int` ([`int_difference`]), and a compare
/// narrower than the machine's word of an operand that may be wider: `cmp
/// edx, eax` compares the low halves of two 64-bit variables.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `l` - Left operand.
/// * `r` - Right operand.
/// * `rel` - The relational operator text.
/// * `signed` - The compare is signed.
/// * `bits` - Operand width, selecting the signed type.
fn compare(n: &Names<'_>, l: &Expr, r: &Expr, rel: &str, signed: bool, bits: u8) -> String {
    let cast = |e: &Expr| -> String {
        if signed && !matches!(e, Expr::Const(c) if *c < 1 << 31) {
            let text = paren_compared(e, n, UNARY);
            if bits == 64 && text.starts_with("(int64_t)") {
                text
            } else {
                format!("({}){text}", signed_ty(bits))
            }
        } else if (!signed
            && !matches!(rel, "==" | "!=")
            && (matches!(e, Expr::Sext(..)) || int_difference(e)))
            || (i64::from(bits) < n.word * 8 && value_bits(e) > u64::from(bits))
        {
            format!(
                "({}){}",
                Ty::from_bits(bits).name(),
                paren_compared(e, n, UNARY)
            )
        } else {
            paren_compared(e, n, 7)
        }
    };
    format!("{} {rel} {}", cast(l), cast(r))
}

/// Tells whether an expression is a difference C computes in `int`, which
/// goes below zero where the machine's unsigned value wraps:
/// `*(uint8_t*)p - 12` of a byte below 12.
///
/// # Arguments
///
/// * `e` - The expression.
fn int_difference(e: &Expr) -> bool {
    let differs = match e {
        Expr::Bin(Op::Sub, ..) | Expr::Un(UnOp::Neg | UnOp::Not, _) => true,
        Expr::Bin(Op::Add, _, r) => {
            matches!(**r, Expr::Const(c) if negative_magnitude(c, 8).is_some() || negative_magnitude(c, 4).is_some())
        }
        _ => false,
    };
    differs && (c_narrow(e) == Some(Narrow::Int) || widened_difference(e))
}

/// Tells whether the text of an expression is of a signed C type and may
/// be negative, so that C's `>>`, `/` and `%` on it are the signed ones.
///
/// A sign extension renders as `(int64_t)(intN_t)x`, an arithmetic shift
/// and a signed quotient or remainder as an `int64_t` operation, and an
/// `int` difference goes below zero ([`int_difference`]); a sum, product
/// or bitwise operation keeps the sign when its other operand is no
/// unsigned 64-bit value, by the usual conversions.
///
/// # Arguments
///
/// * `e` - The expression.
fn signed_text(e: &Expr) -> bool {
    match e {
        Expr::Sext(..) | Expr::Bin(Op::Sar | Op::SDiv | Op::SRem, ..) => true,
        Expr::Bin(op @ (Op::Add | Op::Sub | Op::Mul | Op::And | Op::Or | Op::Xor), l, r) => {
            let keeps = |e: &Expr| match e {
                Expr::Const(c) => !op.hex_operands() || *c >> 63 == 0,
                other => signed_text(other) || c_narrow(other).is_some(),
            };
            (signed_text(l) && keeps(r)) || (signed_text(r) && keeps(l)) || int_difference(e)
        }
        Expr::Bin(Op::Shl, l, _) => signed_text(l),
        Expr::Un(UnOp::Neg | UnOp::Not, x) => signed_text(x) || int_difference(e),
        _ => false,
    }
}

/// Tells whether a difference widens a value a 32-bit write zero-extended.
///
/// Its left side casts one to 64 bits, so below the subtrahend it goes
/// negative the same way an `int` difference does, where the machine's
/// zero-extended value wraps.
///
/// # Arguments
///
/// * `e` - The difference.
fn widened_difference(e: &Expr) -> bool {
    let Expr::Bin(Op::Sub | Op::Add, l, _) = e else {
        return false;
    };
    matches!(&**l, Expr::Cast(inner, ty) if ty.bits() == 64 && c_narrow(inner).is_some())
}

/// Renders an ordered floating-point comparison exactly, NaN included.
///
/// `comiss`/`ucomiss` and `fcomi` set ZF, PF and CF all three on an
/// unordered outcome, so `ja` and `jae` hold on ordered operands only, as
/// C's `>` and `>=` do, while `jb` and `jbe` also hold on a NaN: they are
/// `!(a >= b)` and `!(a > b)`, never `a < b` and `a <= b`. When neither
/// operand's text shows it is a float ([`super::line::float_like`]), the
/// C99 comparison macros spell it instead, so a text pass that negates a
/// condition can always tell a float comparison from an integer one.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `cc` - `a`, `ae`, `b` or `be`.
/// * `l` - Left operand.
/// * `r` - Right operand.
fn float_relation(n: &Names<'_>, cc: Cc, l: &Expr, r: &Expr) -> String {
    use ConditionCode as C;
    let (rel, call, negated) = match cc.0 {
        C::a => (">", "isgreater", false),
        C::ae => (">=", "isgreaterequal", false),
        C::b => (">=", "isgreaterequal", true),
        _ => (">", "isgreater", true),
    };
    let (ls, rs) = (paren_if_lower(l, n, 7), paren_if_lower(r, n, 7));
    let not = if negated { "!" } else { "" };
    if super::line::float_like(&ls) || super::line::float_like(&rs) {
        let relation = format!("{ls} {rel} {rs}");
        return if negated {
            format!("!({relation})")
        } else {
            relation
        };
    }
    format!("{not}{call}({}, {})", l.render(n), r.render(n))
}

/// Renders the signed relation to zero of a sum taken without wrapping.
///
/// After `add`, `jl` tests SF != OF, which is the true sum being negative
/// even where the machine sum overflowed, and `jle`, `jge` and `jg` alike.
/// A constant addend `c` moves across: `x + c < 0` is `x < -c`, exact when
/// `-c` fits the width, and `x + x` relates to zero as `x` does. Otherwise
/// the sign is the machine sum's unless the signed sum overflowed, when it
/// is either addend's (both have it, and the true sum is never zero then):
/// `(saddo32(x, y) ? (int32_t)x : (int32_t)(x + y)) < 0`, which needs no
/// wider type and no cast a parameter's declared type would drop.
///
/// # Arguments
///
/// * `n` - Name resolution.
/// * `l` - One addend.
/// * `r` - The other.
/// * `bits` - The width of the addition.
/// * `rel` - `<`, `>=`, `<=` or `>`.
fn sum_relation(n: &Names<'_>, l: &Expr, r: &Expr, bits: u8, rel: &str) -> String {
    let m = mask_bits(bits);
    let min = 1u64 << (bits.clamp(1, 64) - 1);
    let moved = match (l, r) {
        (x, Expr::Const(c)) | (Expr::Const(c), x) if c & m != min => Some((x, c)),
        _ => None,
    };
    if let Some((x, c)) = moved {
        let negated = Expr::Const(sext(c.wrapping_neg() & m, bits));
        return compare(n, x, &negated, rel, true, bits);
    }
    // `x + x` (`shl x, 1`) has the sign of `x` and is zero with it.
    if l == r {
        return compare(n, l, &Expr::Const(0), rel, true, bits);
    }
    let ty = signed_ty(bits);
    let sum = fold(Op::Add, l.clone(), r.clone(), bits);
    format!(
        "(saddo{bits}({}, {}) ? ({ty}){} : ({ty}){}) {rel} 0",
        number(l, n, false).0,
        number(r, n, false).0,
        paren_if_lower(l, n, UNARY),
        paren_if_lower(&sum, n, UNARY)
    )
}

/// Reads a whole-vector global as the text it holds, when that is text.
///
/// A 16-byte compare against a global is how a compiler inlines a fixed
/// string comparison, and the global is the string. Rendered as `g128_...`
/// the reader is told an address and has to look it up; rendered as the
/// literal, the comparison says what it tests.
///
/// # Arguments
///
/// * `n` - Name resolution, which carries the loaded image.
/// * `e` - The compared operand.
///
/// # Returns
///
/// The quoted literal, or `None` unless `e` is a 16-byte read of a global
/// whose bytes are all printable text. Widths are held in a `u8`, so 128
/// bits is the widest a global read can name.
fn packed_literal(n: &Names<'_>, e: &Expr) -> Option<Expr> {
    let Expr::Var(Key::Global(addr, bits)) = e else {
        return None;
    };
    if *bits != 128 {
        return None;
    }
    let len = usize::from(*bits) / 8;
    let raw = n.program.read_va(*addr, len)?;
    if raw.iter().all(|&b| crate::strings::printable(b)) {
        let text = String::from_utf8(raw.to_vec()).ok()?;
        return Some(Expr::Str(format!(
            "\"{}\"",
            text.replace('\\', "\\\\").replace('"', "\\\"")
        )));
    }
    if raw
        .chunks_exact(2)
        .all(|c| c[1] == 0 && crate::strings::printable(c[0]))
    {
        let units: Vec<u8> = raw.chunks_exact(2).map(|c| c[0]).collect();
        let text = String::from_utf8(units).ok()?;
        return Some(Expr::Str(format!(
            "L\"{}\"",
            text.replace('\\', "\\\\").replace('"', "\\\"")
        )));
    }
    None
}

/// Reads the two vectors an all-lanes-equal test compares, if that is the test.
///
/// `pcmpeqb` fills each byte lane with ones where its operands agree and
/// `pmovmskb` gathers the lanes' top bits, so testing the mask against all
/// ones asks whether every lane matched, which is the two vectors being
/// equal. Left as written it reads as bit arithmetic against an unexplained
/// constant, and the literal being compared against hides inside a `g128_`
/// global.
///
/// # Arguments
///
/// * `l` - The compared value, expected to be the gathered mask.
/// * `r` - The constant it is compared against, all ones over the lanes.
///
/// # Returns
///
/// The two compared vectors, or `None` when this is some other comparison.
pub(super) fn vector_equality<'a>(l: &'a Expr, r: &Expr) -> Option<(&'a Expr, &'a Expr)> {
    let Expr::Call(gather, gathered) = l else {
        return None;
    };
    if !matches!(gather.as_str(), "pmovmskb" | "vpmovmskb") {
        return None;
    }
    let Some(Expr::Call(lanes, args)) = gathered.first() else {
        return None;
    };
    if !matches!(lanes.as_str(), "pcmpeqb" | "vpcmpeqb") || args.len() != 2 {
        return None;
    }
    // One mask bit per byte lane: 16 for an xmm gather, 32 for a ymm one.
    if !matches!(r, Expr::Const(0xffff | 0xffff_ffff)) {
        return None;
    }
    Some((args.first()?, args.get(1)?))
}

/// Shortens the literals asserts and logs carry, keeping what they say.
///
/// A signature string is the compiler's `__FUNCSIG__`: it renders as that
/// macro when it names the function being rendered and as
/// `__FUNCSIG__(Qualified::Name)` when it names another (an inlined helper's
/// assert). A source path (a separator-bearing, space-free literal ending in
/// a C or C++ file extension) keeps its last two components. Anything else
/// is returned as is.
///
/// # Arguments
///
/// * `quoted` - The literal as rendered, quotes and escapes included.
/// * `own_name` - The bare name of the function being rendered.
pub(super) fn compact_literal(quoted: &str, own_name: &str) -> String {
    const EXTENSIONS: [&str; 10] = [
        ".h", ".hpp", ".hh", ".hxx", ".inl", ".c", ".cc", ".cpp", ".cxx", ".inc",
    ];
    let Some(inner) = quoted.strip_prefix('"').and_then(|q| q.strip_suffix('"')) else {
        return quoted.to_owned();
    };
    if let Some(sig) = crate::analysis::naming::parse_signature(inner) {
        return if sig.name == own_name {
            "__FUNCSIG__".to_owned()
        } else {
            format!("__FUNCSIG__({})", sig.name)
        };
    }
    let path_like = !inner.contains(' ')
        && inner.contains(['/', '\\'])
        && EXTENSIONS.iter().any(|e| inner.ends_with(e));
    if path_like {
        let parts: Vec<&str> = inner.split(['/', '\\']).filter(|p| !p.is_empty()).collect();
        if parts.len() > 2 {
            let n = parts.len();
            return format!("\"{}/{}\"", parts[n - 2], parts[n - 1]);
        }
    }
    quoted.to_owned()
}
