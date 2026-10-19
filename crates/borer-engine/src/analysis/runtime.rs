//! Compiler runtime helpers and their prototypes.
//!
//! compiler-rt, libgcc and the MSVC runtime supply them for arithmetic
//! the target has no instruction for (128-bit division, 64-bit division
//! on a 32-bit target, conversions between wide integers and floats).
//!
//! A compiler calls them on its own, so no header a program includes
//! declares them, and the code that calls them passes their arguments the
//! way the platform passes the wide types they take: a 128-bit integer in
//! two registers on System V x64, by pointer on Windows x64 (compiler-rt
//! built by clang for Windows), and a 64-bit one in two stack words on a
//! 32-bit target. Once a helper is named (its symbol, its import, or a
//! library signature), the decompiler takes its arity from here rather
//! than guessing it from the registers the call happens to set
//! ([`prototype`]), types what it returns ([`returns`]), and declares it
//! in the function's header with what it computes.
//!
//! The prototypes are the ones compiler-rt's `lib/builtins` sources and
//! libgcc's documentation (GCC internals, "The GCC low-level runtime
//! library") state; the MSVC 32-bit helpers (`_alldiv` and its kin) are
//! `__stdcall` and pop their stack arguments.

use super::prototypes::Prototype;
use crate::program::BinaryFormat;

/// What a parameter or a result is to the machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Arg {
    /// A 32-bit integer.
    I32,
    /// A 64-bit integer.
    I64,
    /// A 128-bit integer.
    I128,
    /// A pointer.
    Ptr,
    /// A `float`.
    F32,
    /// A `double`.
    F64,
}

/// One runtime helper.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Helper {
    /// The name as compiler-rt, libgcc or the MSVC runtime spells it.
    pub name: &'static str,
    /// Its C prototype.
    pub proto: &'static str,
    /// What it computes, in C.
    pub means: &'static str,
    /// Its parameters as the machine sees them.
    params: &'static [Arg],
    /// Its result as the machine sees it.
    ret: Arg,
    /// Whether it pops its stack arguments (`__stdcall`) on a 32-bit
    /// target.
    stdcall: bool,
}

/// Builds a [`Helper`] row.
macro_rules! helper {
    ($name:literal, $proto:literal, $means:literal, [$($p:ident),*], $ret:ident) => {
        Helper {
            name: $name,
            proto: $proto,
            means: $means,
            params: &[$(Arg::$p),*],
            ret: Arg::$ret,
            stdcall: false,
        }
    };
    ($name:literal, $proto:literal, $means:literal, [$($p:ident),*], $ret:ident, stdcall) => {
        Helper {
            name: $name,
            proto: $proto,
            means: $means,
            params: &[$(Arg::$p),*],
            ret: Arg::$ret,
            stdcall: true,
        }
    };
}

/// Every helper, sorted by name.
const HELPERS: &[Helper] = &[
    helper!(
        "__ashldi3",
        "int64_t __ashldi3(int64_t a, int b)",
        "a << b",
        [I64, I32],
        I64
    ),
    helper!(
        "__ashlti3",
        "__int128 __ashlti3(__int128 a, int b)",
        "a << b",
        [I128, I32],
        I128
    ),
    helper!(
        "__ashrdi3",
        "int64_t __ashrdi3(int64_t a, int b)",
        "a >> b, arithmetic",
        [I64, I32],
        I64
    ),
    helper!(
        "__ashrti3",
        "__int128 __ashrti3(__int128 a, int b)",
        "a >> b, arithmetic",
        [I128, I32],
        I128
    ),
    helper!(
        "__bswapdi2",
        "uint64_t __bswapdi2(uint64_t a)",
        "a with its bytes reversed",
        [I64],
        I64
    ),
    helper!(
        "__bswapsi2",
        "uint32_t __bswapsi2(uint32_t a)",
        "a with its bytes reversed",
        [I32],
        I32
    ),
    helper!(
        "__clzdi2",
        "int __clzdi2(uint64_t a)",
        "leading zero bits of a",
        [I64],
        I32
    ),
    helper!(
        "__clzsi2",
        "int __clzsi2(uint32_t a)",
        "leading zero bits of a",
        [I32],
        I32
    ),
    helper!(
        "__clzti2",
        "int __clzti2(unsigned __int128 a)",
        "leading zero bits of a",
        [I128],
        I32
    ),
    helper!(
        "__cmpdi2",
        "int __cmpdi2(int64_t a, int64_t b)",
        "a < b ? 0 : a == b ? 1 : 2",
        [I64, I64],
        I32
    ),
    helper!(
        "__cmpti2",
        "int __cmpti2(__int128 a, __int128 b)",
        "a < b ? 0 : a == b ? 1 : 2",
        [I128, I128],
        I32
    ),
    helper!(
        "__ctzdi2",
        "int __ctzdi2(uint64_t a)",
        "trailing zero bits of a",
        [I64],
        I32
    ),
    helper!(
        "__ctzsi2",
        "int __ctzsi2(uint32_t a)",
        "trailing zero bits of a",
        [I32],
        I32
    ),
    helper!(
        "__ctzti2",
        "int __ctzti2(unsigned __int128 a)",
        "trailing zero bits of a",
        [I128],
        I32
    ),
    helper!(
        "__divdi3",
        "int64_t __divdi3(int64_t a, int64_t b)",
        "a / b, signed",
        [I64, I64],
        I64
    ),
    helper!(
        "__divmoddi4",
        "int64_t __divmoddi4(int64_t a, int64_t b, int64_t *rem)",
        "a / b, signed, with *rem = a % b",
        [I64, I64, Ptr],
        I64
    ),
    helper!(
        "__divmodti4",
        "__int128 __divmodti4(__int128 a, __int128 b, __int128 *rem)",
        "a / b, signed, with *rem = a % b",
        [I128, I128, Ptr],
        I128
    ),
    helper!(
        "__divsi3",
        "int32_t __divsi3(int32_t a, int32_t b)",
        "a / b, signed",
        [I32, I32],
        I32
    ),
    helper!(
        "__divti3",
        "__int128 __divti3(__int128 a, __int128 b)",
        "a / b, signed",
        [I128, I128],
        I128
    ),
    helper!(
        "__ffsdi2",
        "int __ffsdi2(int64_t a)",
        "one plus the index of a's lowest set bit, 0 for 0",
        [I64],
        I32
    ),
    helper!(
        "__ffsti2",
        "int __ffsti2(__int128 a)",
        "one plus the index of a's lowest set bit, 0 for 0",
        [I128],
        I32
    ),
    helper!(
        "__fixdfdi",
        "int64_t __fixdfdi(double a)",
        "(int64_t)a",
        [F64],
        I64
    ),
    helper!(
        "__fixdfti",
        "__int128 __fixdfti(double a)",
        "(__int128)a",
        [F64],
        I128
    ),
    helper!(
        "__fixsfdi",
        "int64_t __fixsfdi(float a)",
        "(int64_t)a",
        [F32],
        I64
    ),
    helper!(
        "__fixsfti",
        "__int128 __fixsfti(float a)",
        "(__int128)a",
        [F32],
        I128
    ),
    helper!(
        "__fixunsdfdi",
        "uint64_t __fixunsdfdi(double a)",
        "(uint64_t)a",
        [F64],
        I64
    ),
    helper!(
        "__fixunsdfsi",
        "uint32_t __fixunsdfsi(double a)",
        "(uint32_t)a",
        [F64],
        I32
    ),
    helper!(
        "__fixunsdfti",
        "unsigned __int128 __fixunsdfti(double a)",
        "(unsigned __int128)a",
        [F64],
        I128
    ),
    helper!(
        "__fixunssfdi",
        "uint64_t __fixunssfdi(float a)",
        "(uint64_t)a",
        [F32],
        I64
    ),
    helper!(
        "__fixunssfti",
        "unsigned __int128 __fixunssfti(float a)",
        "(unsigned __int128)a",
        [F32],
        I128
    ),
    helper!(
        "__floatdidf",
        "double __floatdidf(int64_t a)",
        "(double)a",
        [I64],
        F64
    ),
    helper!(
        "__floatdisf",
        "float __floatdisf(int64_t a)",
        "(float)a",
        [I64],
        F32
    ),
    helper!(
        "__floattidf",
        "double __floattidf(__int128 a)",
        "(double)a",
        [I128],
        F64
    ),
    helper!(
        "__floattisf",
        "float __floattisf(__int128 a)",
        "(float)a",
        [I128],
        F32
    ),
    helper!(
        "__floatundidf",
        "double __floatundidf(uint64_t a)",
        "(double)a",
        [I64],
        F64
    ),
    helper!(
        "__floatundisf",
        "float __floatundisf(uint64_t a)",
        "(float)a",
        [I64],
        F32
    ),
    helper!(
        "__floatuntidf",
        "double __floatuntidf(unsigned __int128 a)",
        "(double)a",
        [I128],
        F64
    ),
    helper!(
        "__floatuntisf",
        "float __floatuntisf(unsigned __int128 a)",
        "(float)a",
        [I128],
        F32
    ),
    helper!(
        "__lshrdi3",
        "uint64_t __lshrdi3(uint64_t a, int b)",
        "a >> b, logical",
        [I64, I32],
        I64
    ),
    helper!(
        "__lshrti3",
        "unsigned __int128 __lshrti3(unsigned __int128 a, int b)",
        "a >> b, logical",
        [I128, I32],
        I128
    ),
    helper!(
        "__moddi3",
        "int64_t __moddi3(int64_t a, int64_t b)",
        "a % b, signed",
        [I64, I64],
        I64
    ),
    helper!(
        "__modsi3",
        "int32_t __modsi3(int32_t a, int32_t b)",
        "a % b, signed",
        [I32, I32],
        I32
    ),
    helper!(
        "__modti3",
        "__int128 __modti3(__int128 a, __int128 b)",
        "a % b, signed",
        [I128, I128],
        I128
    ),
    helper!(
        "__muldi3",
        "int64_t __muldi3(int64_t a, int64_t b)",
        "a * b",
        [I64, I64],
        I64
    ),
    helper!(
        "__mulodi4",
        "int64_t __mulodi4(int64_t a, int64_t b, int *overflow)",
        "a * b, with *overflow set when it does not fit",
        [I64, I64, Ptr],
        I64
    ),
    helper!(
        "__muloti4",
        "__int128 __muloti4(__int128 a, __int128 b, int *overflow)",
        "a * b, with *overflow set when it does not fit",
        [I128, I128, Ptr],
        I128
    ),
    helper!(
        "__multi3",
        "__int128 __multi3(__int128 a, __int128 b)",
        "a * b",
        [I128, I128],
        I128
    ),
    helper!("__negdi2", "int64_t __negdi2(int64_t a)", "-a", [I64], I64),
    helper!(
        "__negti2",
        "__int128 __negti2(__int128 a)",
        "-a",
        [I128],
        I128
    ),
    helper!(
        "__paritydi2",
        "int __paritydi2(uint64_t a)",
        "1 when a has an odd number of set bits",
        [I64],
        I32
    ),
    helper!(
        "__paritysi2",
        "int __paritysi2(uint32_t a)",
        "1 when a has an odd number of set bits",
        [I32],
        I32
    ),
    helper!(
        "__parityti2",
        "int __parityti2(unsigned __int128 a)",
        "1 when a has an odd number of set bits",
        [I128],
        I32
    ),
    helper!(
        "__popcountdi2",
        "int __popcountdi2(uint64_t a)",
        "set bits of a",
        [I64],
        I32
    ),
    helper!(
        "__popcountsi2",
        "int __popcountsi2(uint32_t a)",
        "set bits of a",
        [I32],
        I32
    ),
    helper!(
        "__popcountti2",
        "int __popcountti2(unsigned __int128 a)",
        "set bits of a",
        [I128],
        I32
    ),
    helper!(
        "__powidf2",
        "double __powidf2(double a, int b)",
        "a raised to the integer power b",
        [F64, I32],
        F64
    ),
    helper!(
        "__powisf2",
        "float __powisf2(float a, int b)",
        "a raised to the integer power b",
        [F32, I32],
        F32
    ),
    helper!(
        "__ucmpdi2",
        "int __ucmpdi2(uint64_t a, uint64_t b)",
        "a < b ? 0 : a == b ? 1 : 2, unsigned",
        [I64, I64],
        I32
    ),
    helper!(
        "__ucmpti2",
        "int __ucmpti2(unsigned __int128 a, unsigned __int128 b)",
        "a < b ? 0 : a == b ? 1 : 2, unsigned",
        [I128, I128],
        I32
    ),
    helper!(
        "__udivdi3",
        "uint64_t __udivdi3(uint64_t a, uint64_t b)",
        "a / b, unsigned",
        [I64, I64],
        I64
    ),
    helper!(
        "__udivmoddi4",
        "uint64_t __udivmoddi4(uint64_t a, uint64_t b, uint64_t *rem)",
        "a / b, unsigned, with *rem = a % b",
        [I64, I64, Ptr],
        I64
    ),
    helper!(
        "__udivmodti4",
        "unsigned __int128 __udivmodti4(unsigned __int128 a, unsigned __int128 b, unsigned __int128 *rem)",
        "a / b, unsigned, with *rem = a % b",
        [I128, I128, Ptr],
        I128
    ),
    helper!(
        "__udivsi3",
        "uint32_t __udivsi3(uint32_t a, uint32_t b)",
        "a / b, unsigned",
        [I32, I32],
        I32
    ),
    helper!(
        "__udivti3",
        "unsigned __int128 __udivti3(unsigned __int128 a, unsigned __int128 b)",
        "a / b, unsigned",
        [I128, I128],
        I128
    ),
    helper!(
        "__umoddi3",
        "uint64_t __umoddi3(uint64_t a, uint64_t b)",
        "a % b, unsigned",
        [I64, I64],
        I64
    ),
    helper!(
        "__umodsi3",
        "uint32_t __umodsi3(uint32_t a, uint32_t b)",
        "a % b, unsigned",
        [I32, I32],
        I32
    ),
    helper!(
        "__umodti3",
        "unsigned __int128 __umodti3(unsigned __int128 a, unsigned __int128 b)",
        "a % b, unsigned",
        [I128, I128],
        I128
    ),
    helper!(
        "_alldiv",
        "int64_t __stdcall _alldiv(int64_t a, int64_t b)",
        "a / b, signed",
        [I64, I64],
        I64,
        stdcall
    ),
    helper!(
        "_allmul",
        "int64_t __stdcall _allmul(int64_t a, int64_t b)",
        "a * b",
        [I64, I64],
        I64,
        stdcall
    ),
    helper!(
        "_allrem",
        "int64_t __stdcall _allrem(int64_t a, int64_t b)",
        "a % b, signed",
        [I64, I64],
        I64,
        stdcall
    ),
    helper!(
        "_aulldiv",
        "uint64_t __stdcall _aulldiv(uint64_t a, uint64_t b)",
        "a / b, unsigned",
        [I64, I64],
        I64,
        stdcall
    ),
    helper!(
        "_aullrem",
        "uint64_t __stdcall _aullrem(uint64_t a, uint64_t b)",
        "a % b, unsigned",
        [I64, I64],
        I64,
        stdcall
    ),
];

/// Returns the helper a function name names.
///
/// A 32-bit COFF name carries one more leading underscore than the C name
/// (`___udivdi3` for `__udivdi3`), and an import is named `module!name`;
/// both are read as the C name.
///
/// # Arguments
///
/// * `name` - The function's or import's name.
///
/// # Returns
///
/// The helper, or `None` when the name is no runtime helper's.
#[must_use]
pub fn helper(name: &str) -> Option<&'static Helper> {
    let name = super::bare_name(name);
    let find = |n: &str| {
        HELPERS
            .binary_search_by(|h| h.name.cmp(n))
            .ok()
            .and_then(|i| HELPERS.get(i))
    };
    find(name).or_else(|| find(name.strip_prefix('_')?))
}

/// Whether a format's 64-bit code takes the Microsoft x64 convention, as
/// the decompiler reads it: a PE, and the raw code and archives it reads
/// as one.
///
/// # Arguments
///
/// * `format` - The binary's format.
fn microsoft(format: BinaryFormat) -> bool {
    match format {
        BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => true,
        BinaryFormat::Elf | BinaryFormat::MachO => false,
    }
}

/// Returns what a call to a helper must supply, as the decompiler's
/// convention reads it.
///
/// On a 64-bit target a parameter is one argument position, a float one
/// in a vector register, and a 128-bit integer two positions on System V
/// and one pointer under the Microsoft convention ([`microsoft`]). On a
/// 32-bit target the count is the stack words the parameters take: two
/// for a 64-bit integer or a `double`.
///
/// # Arguments
///
/// * `h` - The helper.
/// * `bitness` - 32 or 64.
/// * `format` - The calling binary's format.
///
/// # Returns
///
/// The prototype.
#[must_use]
pub fn prototype(h: &Helper, bitness: u32, format: BinaryFormat) -> Prototype {
    let mut params = 0u8;
    let mut floats = 0u8;
    for a in h.params {
        let (width, float) = match (bitness, a) {
            (32, Arg::I64 | Arg::F64 | Arg::I128) => (2, false),
            (32, Arg::I32 | Arg::Ptr | Arg::F32) => (1, false),
            (_, Arg::I128) if !microsoft(format) => (2, false),
            (_, Arg::F32 | Arg::F64) => (1, true),
            (_, Arg::I32 | Arg::I64 | Arg::I128 | Arg::Ptr) => (1, false),
        };
        if float && bitness != 32 {
            floats |= 1u8.checked_shl(u32::from(params)).unwrap_or(0);
        }
        params = params.saturating_add(width);
    }
    Prototype {
        params,
        this: false,
        callee_pops: h.stdcall && bitness == 32,
        hidden_return: false,
        variadic: false,
        floats,
    }
}

/// Returns what a helper hands back: its width in bits and whether it is
/// a float.
///
/// # Arguments
///
/// * `h` - The helper.
/// * `bitness` - 32 or 64.
/// * `format` - The calling binary's format.
///
/// # Returns
///
/// `(bits, float)`, or `None` for a 128-bit result under the Microsoft
/// x64 convention, which comes back in `xmm0` as no integer the
/// decompiler reads there.
#[must_use]
pub fn returns(h: &Helper, bitness: u32, format: BinaryFormat) -> Option<(u8, bool)> {
    match h.ret {
        Arg::I32 => Some((32, false)),
        Arg::I64 => Some((64, false)),
        Arg::Ptr => Some((if bitness == 32 { 32 } else { 64 }, false)),
        Arg::I128 if microsoft(format) && bitness == 64 => None,
        Arg::I128 => Some((64, false)),
        Arg::F32 => Some((32, true)),
        Arg::F64 => Some((64, true)),
    }
}

#[cfg(test)]
mod tests {
    use super::{HELPERS, helper, prototype, returns};
    use crate::program::BinaryFormat;

    /// The table is sorted, so the lookup finds every row, and the names a
    /// binary spells a helper with all find it.
    ///
    /// # Panics
    ///
    /// When a row is out of order or a spelling is not found.
    #[test]
    fn every_helper_is_found_by_its_spellings() {
        assert!(HELPERS.windows(2).all(|w| w[0].name < w[1].name));
        for h in HELPERS {
            assert_eq!(helper(h.name).map(|f| f.name), Some(h.name));
            assert!(h.proto.contains(h.name), "{}", h.name);
        }
        assert_eq!(helper("___udivdi3").map(|h| h.name), Some("__udivdi3"));
        assert_eq!(
            helper("libgcc_s.so.1!__umodti3").map(|h| h.name),
            Some("__umodti3")
        );
        assert!(helper("memcpy").is_none());
        assert!(helper("_umodti3").is_none());
    }

    /// A 128-bit argument takes two registers on System V and one pointer
    /// on Windows; a 64-bit one two stack words on a 32-bit target, popped
    /// by an MSVC helper; a float a vector register.
    ///
    /// # Panics
    ///
    /// When a prototype is read wrongly.
    #[test]
    fn arguments_take_what_the_platform_passes() {
        let umod = helper("__umodti3").expect("a helper");
        assert_eq!(prototype(umod, 64, BinaryFormat::Elf).params, 4);
        assert_eq!(prototype(umod, 64, BinaryFormat::Pe).params, 2);
        assert_eq!(returns(umod, 64, BinaryFormat::Elf), Some((64, false)));
        assert_eq!(returns(umod, 64, BinaryFormat::Pe), None);
        let udiv = helper("__udivdi3").expect("a helper");
        let p = prototype(udiv, 32, BinaryFormat::Elf);
        assert_eq!((p.params, p.callee_pops), (4, false));
        let alldiv = helper("_alldiv").expect("a helper");
        let p = prototype(alldiv, 32, BinaryFormat::Pe);
        assert_eq!((p.params, p.callee_pops), (4, true));
        let powi = helper("__powidf2").expect("a helper");
        let p = prototype(powi, 64, BinaryFormat::Elf);
        assert_eq!((p.params, p.floats), (2, 1));
        assert_eq!(returns(powi, 64, BinaryFormat::Elf), Some((64, true)));
    }
}
