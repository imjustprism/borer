//! Declared prototypes for imports whose arity the code cannot show.
//!
//! A call to an import reaches a thunk or an address table, never a body, so
//! the scan that counts the argument registers a callee reads has nothing to
//! read. Without a declaration the renderer can pass only the registers the
//! caller set, which drops a parameter the caller passes on untouched, every
//! stack argument (`BCryptCreateHash` takes seven, `CreateFileW` seven) and
//! the `double` `sin` takes in `xmm0`.
//!
//! The table ([`TABLE`], `prototypes.tsv`) holds facts about the published
//! prototypes and nothing of their text: per function, what each declared
//! parameter is to the 64-bit convention (a pointer, an integer, a float),
//! the stack words the parameters take on a 32-bit target, whether the
//! 32-bit convention is `__stdcall`, and whether the list is variadic. It
//! was extracted with clang from the Windows SDK 10.0.26100 and UCRT headers
//! (`windows.h`, `winternl.h`, the shell, COM, Winsock, `d3d9.h` and the C
//! runtime), compiler intrinsics left out, plus the `WinINet` calls those
//! headers do not declare.
//!
//! It is a passive reference covering the whole surface a target might call
//! so any binary decompiles cleanly: the entries name APIs, nothing here
//! invokes them. Sensitive-looking names (`CreateRemoteThread`,
//! `CreateProcessW`) sit beside `CreateFileW` for that reason.
//!
//! A C++ import needs no table: its mangled name states the parameter list
//! and the calling convention, and [`msvc_prototype`] reads both.

use std::sync::LazyLock;

use msvc_demangler::{CallingConv, FuncClass, StorageClass, Type};

/// What a call must supply, and who cleans up after it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Prototype {
    /// Declared parameters, `this` excluded; a variadic tail is not counted.
    /// From the table on a 32-bit target, the stack words they take: a
    /// `double` or a `LARGE_INTEGER` passed by value takes two.
    pub params: u8,
    /// The callee takes `this` first: in `ecx` on a 32-bit `__thiscall`, in
    /// the first argument register of a 64-bit method.
    pub this: bool,
    /// The callee pops its stack arguments on return (`__stdcall`,
    /// `__thiscall`, `__fastcall`); a `__cdecl` caller pops them itself.
    pub callee_pops: bool,
    /// The callee returns a class by value, through a pointer the caller
    /// passes as a hidden first stack argument on a 32-bit target and the
    /// callee pops with the rest: `QString QVariant::toString()` takes one
    /// word its mangled name does not list.
    pub hidden_return: bool,
    /// The callee takes a variable argument list past the declared ones.
    pub variadic: bool,
    /// A bit per declared parameter, `this` not counted, of the first eight,
    /// that a 64-bit call passes in a vector register: a `float` or a
    /// `double`.
    pub floats: u8,
}

impl Prototype {
    /// Words the call passes on a 32-bit stack: the declared parameters and
    /// the hidden return pointer.
    #[must_use]
    pub fn stack_params(&self) -> u8 {
        self.params.saturating_add(u8::from(self.hidden_return))
    }
}

/// Reads an import's prototype from its MSVC-mangled name.
///
/// # Arguments
///
/// * `name` - The bare import name, without its `dll!` prefix.
///
/// # Returns
///
/// The prototype, or `None` when the name is not an MSVC-mangled function.
pub fn msvc_prototype(name: &str) -> Option<Prototype> {
    if !name.starts_with('?') {
        return None;
    }
    let parsed = msvc_demangler::parse(name).ok()?;
    let (conv, params, ret, this) = match parsed.symbol_type {
        Type::MemberFunction(class, conv, params, this, ret) => {
            let own = !class.contains(FuncClass::STATIC);
            let this = conv == CallingConv::Thiscall || (own && this.contains(StorageClass::PTR64));
            (conv, params, ret, this)
        }
        Type::NonMemberFunction(conv, params, _, ret) => (conv, params, ret, false),
        _ => return None,
    };
    let hidden_return = matches!(*ret, Type::Class(..) | Type::Struct(..) | Type::Union(..));
    let fixed: Vec<&Type<'_>> = params
        .types
        .iter()
        .filter(|t| !matches!(t, Type::Void(_) | Type::VarArgs | Type::EmptyParameterPack))
        .collect();
    let floats = fixed
        .iter()
        .enumerate()
        .filter(|(_, t)| matches!(t, Type::Float(_) | Type::Double(_) | Type::Ldouble(_)))
        .filter_map(|(i, _)| 1u8.checked_shl(u32::try_from(i).ok()?))
        .fold(0u8, |m, bit| m | bit);
    Some(Prototype {
        params: u8::try_from(fixed.len()).unwrap_or(u8::MAX),
        this,
        callee_pops: matches!(
            conv,
            CallingConv::Thiscall
                | CallingConv::Stdcall
                | CallingConv::Fastcall
                | CallingConv::Pascal
        ),
        hidden_return,
        variadic: params.types.iter().any(|t| matches!(t, Type::VarArgs)),
        floats,
    })
}

/// Tells whether a library is a C runtime, whose exports are `__cdecl`.
///
/// Every other library a 32-bit Windows program imports from is taken as
/// `__stdcall`, which is what `WINAPI` means and what the Win32 surface is
/// declared as without exception.
///
/// # Arguments
///
/// * `dll` - The library name as the import table spells it.
pub fn is_c_runtime(dll: &str) -> bool {
    /// Prefixes of the runtimes whose exports the caller cleans up after.
    const RUNTIMES: [&str; 7] = [
        "msvcr",
        "msvcrt",
        "ucrtbase",
        "api-ms-win-crt",
        "vcruntime",
        "cygwin",
        "msys",
    ];
    let lower = dll.to_ascii_lowercase();
    RUNTIMES.iter().any(|p| lower.starts_with(p))
}

/// Returns the stack words a 32-bit call to an import leaves for the
/// callee to pop: the declared parameters of a `__stdcall` function.
///
/// # Arguments
///
/// * `name` - The import name without its `dll!` prefix, case-sensitive as
///   the export table spells it. An `A`/`W` suffix is matched as written.
///
/// # Returns
///
/// The words, or `None` when the import is not in the table, is `__cdecl`
/// (its caller pops) or takes a structure of unknown size by value.
pub fn arity(name: &str) -> Option<u8> {
    declared(name, 32)
        .filter(|p| p.callee_pops)
        .map(|p| p.params)
}

/// Returns the prototype the Windows SDK or the C runtime declares for a
/// function, by its bare name, as a call on a target of `bitness` passes it.
///
/// # Arguments
///
/// * `name` - The function name without its `dll!` prefix, matched exactly.
/// * `bitness` - 32 or 64: a 32-bit prototype counts the stack words the
///   parameters take and says whether the callee pops them; a 64-bit one
///   counts the parameters and marks the ones passed in vector registers.
///
/// # Returns
///
/// The prototype, or `None` when the table has no such function, or none
/// for that target.
pub fn declared(name: &str, bitness: u32) -> Option<Prototype> {
    let i = TABLE.binary_search_by_key(&name, |row| row.0).ok()?;
    let &(_, kinds, words, flags) = TABLE.get(i)?;
    let variadic = flags.ends_with('v');
    let (params, callee_pops) = if bitness == 32 {
        let pops = match flags.chars().next()? {
            's' => true,
            'c' => false,
            _ => return None,
        };
        (words.parse::<u8>().ok()?, pops && !variadic)
    } else {
        (
            u8::try_from(kinds.len()).ok().filter(|_| kinds != "-")?,
            false,
        )
    };
    let floats = kinds
        .bytes()
        .take(8)
        .enumerate()
        .filter(|(_, k)| *k == b'f')
        .fold(0u8, |m, (i, _)| m | (1 << i));
    Some(Prototype {
        params,
        this: false,
        callee_pops,
        hidden_return: false,
        variadic,
        floats,
    })
}

/// The SDK prototype table, sorted by name.
///
/// Per function: one letter per
/// declared parameter as the 64-bit convention passes it (`p` a pointer,
/// `i` an integer or a small structure in a general register, `f` a float
/// or a double in a vector register; `-` when the 64-bit headers do not
/// declare it), the stack words the parameters take on a 32-bit target
/// (`-` when a structure of unknown size is passed by value or the 32-bit
/// headers do not declare it), and the flags: the 32-bit convention (`s`
/// `__stdcall`, `c` `__cdecl`, `f` `__fastcall`, `-` undeclared), then `v`
/// for a variadic list.
static TABLE: LazyLock<Vec<(&str, &str, &str, &str)>> = LazyLock::new(|| {
    include_str!("prototypes.tsv")
        .lines()
        .filter_map(|line| {
            let mut cols = line.split('\t');
            Some((cols.next()?, cols.next()?, cols.next()?, cols.next()?))
        })
        .collect()
});

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Prototype, TABLE, arity, declared, is_c_runtime, msvc_prototype};

    /// The table is sorted and every row is well formed: a name, the 64-bit
    /// kinds, the 32-bit words and the flags.
    #[test]
    fn the_table_is_sorted_and_well_formed() {
        assert!(TABLE.len() > 8000, "{}", TABLE.len());
        assert!(
            TABLE.windows(2).all(|w| w[0].0 < w[1].0),
            "prototype table is not sorted by name"
        );
        for (name, kinds, words, flags) in TABLE.iter() {
            assert!(!name.is_empty(), "{name}");
            assert!(
                *kinds == "-" || kinds.bytes().all(|k| b"pif".contains(&k)),
                "{name}"
            );
            assert!(*words == "-" || words.parse::<u8>().is_ok(), "{name}");
            assert!(
                ["s", "c", "f", "-"].contains(&flags.trim_end_matches('v')),
                "{name}"
            );
        }
    }

    /// The binary search answers what a scan of the table would.
    ///
    /// Every entry is found by its own name, and each decorated spelling of
    /// it is matched no more than the scan matches it: a name is matched
    /// exactly as the export table spells it, and stripping a `dll!` prefix
    /// is the caller's job.
    #[test]
    fn the_lookup_agrees_with_a_scan_of_the_table() {
        let scan = |name: &str| TABLE.iter().any(|row| row.0 == name);
        for (name, kinds, ..) in TABLE.iter().step_by(7) {
            assert_eq!(declared(name, 64).is_some(), *kinds != "-", "{name}");
            let decorated = [
                format!("_{name}@{}", kinds.len() * 4),
                format!("__imp_{name}"),
                format!("KERNEL32.dll!{name}"),
                name.to_ascii_lowercase(),
                name.to_ascii_uppercase(),
                format!("{name}A"),
                format!("{name}W"),
                name.trim_end_matches(['A', 'W']).to_owned(),
                format!(" {name}"),
            ];
            for d in &decorated {
                if !scan(d) {
                    assert_eq!(declared(d, 64), None, "{d}");
                }
            }
        }
    }

    /// Known imports report what each target passes; unknown ones nothing.
    ///
    /// A `LARGE_INTEGER` by value is one 64-bit argument and two 32-bit
    /// words, `sin` takes its `double` in a vector register, a `__cdecl`
    /// function leaves its words to the caller, and a variadic one says so.
    #[test]
    fn prototypes_are_looked_up_by_bare_name() {
        let params = |name, bits| declared(name, bits).map(|p| p.params);
        assert_eq!(params("BCryptCreateHash", 64), Some(7));
        assert_eq!(params("BCryptDecrypt", 64), Some(10));
        assert_eq!(params("memset", 64), Some(3));
        assert_eq!(params("SetFilePointerEx", 64), Some(4));
        assert_eq!(params("SetFilePointerEx", 32), Some(5));
        assert_eq!(arity("SetFilePointerEx"), Some(5));
        assert_eq!(arity("ExitProcess"), Some(1));
        assert_eq!(arity("memset"), None);
        assert_eq!(declared("sin", 64).map(|p| p.floats), Some(1));
        assert_eq!(declared("CreateFileW", 64).map(|p| p.floats), Some(0));
        let printf = declared("wsprintfA", 32);
        assert_eq!(
            printf.map(|p| (p.params, p.variadic, p.callee_pops)),
            Some((2, true, false))
        );
        assert_eq!(declared("NotAnImport", 64), None);
        assert_eq!(declared("bcrypt.dll!BCryptDecrypt", 64), None);
    }

    /// A mangled name states its parameters, who pops them, and whether a
    /// class comes back by value through a hidden pointer; a 64-bit method
    /// takes `this` first though its convention is `__cdecl`.
    #[test]
    fn mangled_names_state_their_prototype() {
        let proto = |p, t, c, h| {
            Some(Prototype {
                params: p,
                this: t,
                callee_pops: c,
                hidden_return: h,
                variadic: false,
                floats: 0,
            })
        };
        assert_eq!(
            msvc_prototype("?m@C@@QEAAXN@Z").map(|p| (p.params, p.this, p.floats)),
            Some((1, true, 1))
        );
        assert_eq!(
            msvc_prototype("?f@@YAXHZZ").map(|p| (p.params, p.variadic)),
            Some((1, true))
        );
        assert_eq!(
            msvc_prototype("?bar@@YGXHH@Z"),
            proto(2, false, true, false)
        );
        assert_eq!(
            msvc_prototype("?bar@@YAXHH@Z"),
            proto(2, false, false, false)
        );
        assert_eq!(msvc_prototype("?m@C@@QAEXH@Z"), proto(1, true, true, false));
        assert_eq!(
            msvc_prototype("??0QString@@QAE@XZ"),
            proto(0, true, true, false)
        );
        assert_eq!(
            msvc_prototype("?toString@QVariant@@QBE?AVQString@@XZ"),
            proto(0, true, true, true)
        );
        assert_eq!(
            msvc_prototype("?data@QString@@QAEPAVQChar@@XZ"),
            proto(0, true, true, false)
        );
        assert_eq!(
            msvc_prototype("?toString@QVariant@@QBE?AVQString@@XZ").map(|p| p.stack_params()),
            Some(1)
        );
        assert_eq!(msvc_prototype("?x@@3HA"), None);
        assert_eq!(msvc_prototype("CreateFileW"), None);
    }

    /// The C runtimes are `__cdecl`; the rest of Windows is not.
    #[test]
    fn runtimes_are_told_from_the_win32_surface() {
        assert!(is_c_runtime("MSVCR100.dll"));
        assert!(is_c_runtime("api-ms-win-crt-string-l1-1-0.dll"));
        assert!(!is_c_runtime("KERNEL32.dll"));
        assert!(!is_c_runtime("Qt5Core.dll"));
    }
}
