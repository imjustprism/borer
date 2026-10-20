//! The SDK type library: full prototypes of the Windows API, the kernel
//! and the C runtime, the typedefs they spell and the structures they
//! point at.
//!
//! [`typelib`](super::typelib) holds the curated rows an agent reads most,
//! with their constant groups. This is the wide layer under it: what
//! `scripts/dev/sdklib.py` restates from the Windows SDK headers with
//! clang, as facts (a name, a calling convention, parameter types and
//! names, a typedef's representation, a structure's field names, types and
//! offsets on x64 and x86) and no header text. `sdk/manifest.tsv` records
//! the SDK and clang versions, the headers each unit includes and the row
//! counts; every declaration was compiled beside the headers it came from,
//! and the few clang rejected are named there and left out.
//!
//! The tables are interned to stay small: `words.tsv` and `names.tsv` list
//! each spelled type and each parameter or field name once, most used
//! first, and the rows cite them by a base-36 index.
//!
//! * `functions.tsv` - name, convention and origin, the return type's
//!   word, then `type.name` per parameter and `...` for a variable list.
//! * `types.tsv` - a typedef, what the machine passes it as (`-` for a
//!   structure by value), the structure under it and the pointers over it.
//! * `structs.tsv` - a tag, its size on x64 and on x86, then
//!   `name.type.off64.off32` per field.

use std::collections::BTreeMap;
use std::sync::{LazyLock, OnceLock};

use super::typelib::{Conv, Decl, Os, Param};

/// Where a declaration's header sits in the SDK.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Origin {
    /// A user-mode Windows API (`um`, `shared`).
    User,
    /// A kernel-mode API (`km`).
    Kernel,
    /// The C runtime's own functions (`ucrt`, `vcruntime`).
    Runtime,
    /// A C standard function whose types mean the same on every platform.
    Standard,
}

impl Origin {
    /// Reads the table's letter for an origin.
    ///
    /// # Arguments
    ///
    /// * `c` - `u`, `k`, `r` or `c`.
    fn of(c: char) -> Option<Self> {
        match c {
            'u' => Some(Self::User),
            'k' => Some(Self::Kernel),
            'r' => Some(Self::Runtime),
            'c' => Some(Self::Standard),
            _ => None,
        }
    }

    /// The platform whose binaries call a declaration of this origin.
    fn os(self) -> Os {
        match self {
            Self::User | Self::Kernel | Self::Runtime => Os::Win,
            Self::Standard => Os::C,
        }
    }
}

/// One field of a structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Field {
    /// The field's name.
    pub name: &'static str,
    /// Its C type as the header spells it (`DWORD`, `WCHAR[260]`).
    pub ty: &'static str,
    /// Its offset in bytes on x64.
    pub off64: u64,
    /// Its offset in bytes on x86, `None` when the x86 layout lacks it.
    pub off32: Option<u64>,
}

/// One structure or union the declarations point at.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Struct {
    /// Its tag (`_STARTUPINFOW`).
    pub tag: &'static str,
    /// Its size in bytes on x64.
    pub size64: u64,
    /// Its size in bytes on x86, `None` when x86 does not define it.
    pub size32: Option<u64>,
    /// Its named fields by ascending x64 offset; an anonymous member's
    /// fields stand in for it, bit fields are left out.
    pub fields: Vec<Field>,
}

impl Struct {
    /// Returns the fields at their offsets for a machine word.
    ///
    /// # Arguments
    ///
    /// * `word` - The pointer width in bytes, 4 or 8.
    ///
    /// # Returns
    ///
    /// `(offset, field)` pairs, empty on x86 when the structure has no x86
    /// layout.
    #[must_use]
    pub fn at(&self, word: u64) -> Vec<(u64, Field)> {
        if word == 8 {
            return self.fields.iter().map(|f| (f.off64, *f)).collect();
        }
        if self.size32.is_none() {
            return Vec::new();
        }
        self.fields
            .iter()
            .filter_map(|f| Some((f.off32?, *f)))
            .collect()
    }
}

/// What a typedef stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Typedef {
    /// What the machine passes it as, a `ctypes.tsv` word; `None` for a
    /// structure by value.
    pub pass: Option<&'static str>,
    /// The structure under it, if any.
    pub tag: Option<&'static str>,
    /// The pointers over that structure (1 for `LPSTARTUPINFOW`).
    pub stars: usize,
}

/// Reads a base-36 index.
///
/// # Arguments
///
/// * `text` - The index's digits.
fn index(text: &str) -> Option<usize> {
    usize::from_str_radix(text, 36).ok()
}

/// The spelled types, by index (`words.tsv`).
static WORDS: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| include_str!("sdk/words.tsv").lines().collect());

/// The parameter and field names, by index (`names.tsv`); `-` is none.
static NAMES: LazyLock<Vec<&'static str>> =
    LazyLock::new(|| include_str!("sdk/names.tsv").lines().collect());

/// Returns the spelled type at an index.
///
/// # Arguments
///
/// * `text` - The base-36 index.
fn word(text: &str) -> Option<&'static str> {
    WORDS.get(index(text)?).copied()
}

/// Returns the name at an index, empty for none.
///
/// # Arguments
///
/// * `text` - The base-36 index.
fn name(text: &str) -> Option<&'static str> {
    NAMES
        .get(index(text)?)
        .map(|n| if *n == "-" { "" } else { *n })
}

/// Reads one row of `functions.tsv`.
///
/// # Arguments
///
/// * `line` - The row.
fn decl_of(line: &'static str) -> Option<Decl> {
    let mut cols = line.split('\t');
    let fn_name = cols.next()?;
    let mut flags = cols.next()?.chars();
    let conv = match flags.next()? {
        's' => Conv::Stdcall,
        'f' => Conv::Fastcall,
        'c' => Conv::Cdecl,
        _ => return None,
    };
    let origin = Origin::of(flags.next()?)?;
    let ret = word(cols.next()?)?;
    let mut params = Vec::new();
    let mut variadic = false;
    for col in cols {
        if col == "..." {
            variadic = true;
            continue;
        }
        let (ty, pname) = col.split_once('.')?;
        params.push(Param {
            ty: word(ty)?,
            name: name(pname)?,
            group: None,
        });
    }
    Some(Decl {
        name: fn_name,
        os: origin.os(),
        ret,
        ret_group: None,
        params,
        variadic,
        conv,
    })
}

/// One row of `functions.tsv`: the function's name, the row, and the
/// declaration the row reads as, read the first time it is asked for.
type Row = (&'static str, &'static str, OnceLock<Option<Decl>>);

/// The declarations' rows, sorted by name (`functions.tsv`).
///
/// Reading every row into a [`Decl`] up front cost the first decompile
/// of a process milliseconds for the few declarations it reads, so only
/// the names are split out here and a row is read when it is first asked
/// for ([`decl`]).
static DECLS: LazyLock<Vec<Row>> = LazyLock::new(|| {
    include_str!("sdk/functions.tsv")
        .lines()
        .map(|line| {
            let name = line.split_once('\t').map_or(line, |(n, _)| n);
            (name, line, OnceLock::new())
        })
        .collect()
});

/// Returns the declaration a row of [`DECLS`] reads as, reading it the
/// first time.
///
/// # Arguments
///
/// * `row` - The row.
///
/// # Returns
///
/// The declaration, or `None` when the row does not read as one.
fn decl(row: &'static Row) -> Option<&'static Decl> {
    row.2.get_or_init(|| decl_of(row.1)).as_ref()
}

/// The typedefs the declarations and fields spell (`types.tsv`).
static TYPES: LazyLock<BTreeMap<&'static str, Typedef>> = LazyLock::new(|| {
    include_str!("sdk/types.tsv")
        .lines()
        .filter_map(|line| {
            let mut cols = line.split('\t');
            let (n, pass, tag, stars) = (cols.next()?, cols.next()?, cols.next()?, cols.next()?);
            Some((
                n,
                Typedef {
                    pass: (pass != "-").then_some(pass),
                    tag: (tag != "-").then_some(tag),
                    stars: stars.parse().ok()?,
                },
            ))
        })
        .collect()
});

/// The structures, by tag (`structs.tsv`).
static STRUCTS: LazyLock<BTreeMap<&'static str, Struct>> = LazyLock::new(|| {
    include_str!("sdk/structs.tsv")
        .lines()
        .filter_map(|line| {
            let mut cols = line.split('\t');
            let tag = cols.next()?;
            let size64 = cols.next()?.parse().ok()?;
            let size32 = cols.next()?.parse().ok();
            let fields = cols
                .filter_map(|col| {
                    let mut parts = col.split('.');
                    Some(Field {
                        name: name(parts.next()?)?,
                        ty: word(parts.next()?)?,
                        off64: parts.next()?.parse().ok()?,
                        off32: parts.next()?.parse().ok(),
                    })
                })
                .collect();
            Some((
                tag,
                Struct {
                    tag,
                    size64,
                    size32,
                    fields,
                },
            ))
        })
        .collect()
});

/// Returns the SDK declaration of a function a binary of a platform calls.
///
/// # Arguments
///
/// * `fn_name` - The function's bare name, matched exactly.
/// * `serves` - Tells whether a declaration's platform is the caller's.
///
/// # Returns
///
/// The declaration, or `None` when the SDK declares none the caller's
/// platform calls.
pub fn declared(fn_name: &str, serves: impl Fn(Os) -> bool) -> Option<&'static Decl> {
    let at = DECLS.partition_point(|row| row.0 < fn_name);
    DECLS
        .get(at)
        .filter(|row| row.0 == fn_name)
        .and_then(decl)
        .filter(|d| serves(d.os))
}

/// Returns what a typedef the SDK spells stands for.
///
/// # Arguments
///
/// * `type_name` - The typedef's name (`DWORD`, `LPSTARTUPINFOW`).
#[must_use]
pub fn typedef(type_name: &str) -> Option<&'static Typedef> {
    TYPES.get(type_name)
}

/// Returns a structure by its tag.
///
/// # Arguments
///
/// * `tag` - The tag (`_STARTUPINFOW`).
#[must_use]
pub fn structure(tag: &str) -> Option<&'static Struct> {
    STRUCTS.get(tag)
}

/// Returns the structure a pointer type points at.
///
/// # Arguments
///
/// * `spelled` - The type as a declaration spells it (`LPSTARTUPINFOW`,
///   `STARTUPINFOW *`, `struct _STARTUPINFOW *`).
///
/// # Returns
///
/// The structure, or `None` when the type is not one pointer to an SDK
/// structure.
#[must_use]
pub fn pointee(spelled: &str) -> Option<&'static Struct> {
    let (base, stars) = super::typelib::base_of(spelled);
    let (tag, under) = match TYPES.get(base.as_str()) {
        Some(t) => (t.tag?, t.stars),
        None => (*STRUCTS.get_key_value(base.as_str())?.0, 0),
    };
    (stars + under == 1).then(|| STRUCTS.get(tag)).flatten()
}

/// Spells a declaration as C that compiles beside the SDK headers.
///
/// The name is parenthesized so a function-like macro of the same name
/// (`__isascii`) does not expand, a function pointer parameter carries its
/// name inside its declarator, and an unnamed parameter is `aN`. Only a
/// convention other than the default `__cdecl` is spelled, so a C library
/// row compiles beside a compiler that has no `__cdecl` keyword.
///
/// # Arguments
///
/// * `decl` - The declaration.
///
/// # Returns
///
/// One line, `RET (CONV NAME)(PARAMS);`, `RET (NAME)(PARAMS);` for
/// `__cdecl`.
#[must_use]
pub fn spell(decl: &Decl) -> String {
    let conv = match decl.conv {
        Conv::Cdecl => "",
        Conv::Stdcall => "__stdcall ",
        Conv::Fastcall => "__fastcall ",
    };
    let mut params: Vec<String> = decl
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let n = if p.name.is_empty() {
                format!("a{}", i + 1)
            } else {
                p.name.to_owned()
            };
            declarator(p.ty, &n)
        })
        .collect();
    if decl.variadic {
        params.push("...".to_owned());
    }
    let list = if params.is_empty() {
        "void".to_owned()
    } else {
        params.join(", ")
    };
    format!("{} ({conv}{})({list});", decl.ret, decl.name)
}

/// Spells `ty name` as a C declarator.
///
/// # Arguments
///
/// * `ty` - The type as spelled.
/// * `n` - The declared name.
fn declarator(ty: &str, n: &str) -> String {
    if ty.contains("(*)") {
        ty.replacen("(*)", &format!("(*{n})"), 1)
    } else if ty.ends_with('*') {
        format!("{ty}{n}")
    } else {
        format!("{ty} {n}")
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{
        DECLS, NAMES, STRUCTS, TYPES, WORDS, decl, declared, pointee, spell, structure, typedef,
    };
    use crate::analysis::typelib::{Conv, Os};

    /// Every row of the tables parses, the declarations are sorted and
    /// unique for the search, and every index resolves.
    #[test]
    fn the_tables_parse_whole() {
        let lines = |t: &str| t.lines().count();
        assert_eq!(
            DECLS.iter().filter_map(decl).count(),
            lines(include_str!("sdk/functions.tsv"))
        );
        assert_eq!(TYPES.len(), lines(include_str!("sdk/types.tsv")));
        assert_eq!(STRUCTS.len(), lines(include_str!("sdk/structs.tsv")));
        assert_eq!(WORDS.len(), lines(include_str!("sdk/words.tsv")));
        assert_eq!(NAMES.len(), lines(include_str!("sdk/names.tsv")));
        assert!(DECLS.windows(2).all(|w| w[0].0 < w[1].0));
        assert!(DECLS.len() > 10_000, "{}", DECLS.len());
        for s in STRUCTS.values() {
            assert!(
                s.fields.windows(2).all(|w| w[0].off64 <= w[1].off64),
                "{}",
                s.tag
            );
            assert!(s.fields.iter().all(|f| f.off64 <= s.size64), "{}", s.tag);
        }
    }

    /// A user-mode, a kernel and a runtime declaration carry their
    /// parameter names, types and convention.
    #[test]
    fn declarations_carry_names_types_and_convention() {
        let win = |o: Os| o == Os::Win;
        let create = declared("CreateProcessW", win).expect("CreateProcessW");
        assert_eq!(create.conv, Conv::Stdcall);
        assert_eq!(create.ret, "BOOL");
        let names: Vec<&str> = create.params.iter().map(|p| p.name).collect();
        assert_eq!(names.len(), 10);
        assert_eq!(names.get(8), Some(&"lpStartupInfo"));
        let nt = declared("ZwClose", win).expect("km");
        assert_eq!(
            (nt.conv, nt.params.first().map(|p| p.ty)),
            (Conv::Stdcall, Some("HANDLE"))
        );
        let fast = declared("IofCallDriver", win).expect("km");
        assert_eq!(fast.conv, Conv::Fastcall);
        let fopen = declared("_wfopen", win).expect("crt");
        assert_eq!(fopen.conv, Conv::Cdecl);
        assert_eq!(fopen.params.first().map(|p| p.name), Some("FileName"));
        let printf = declared("printf", |o| o == Os::C).expect("standard");
        assert!(printf.variadic);
        assert!(declared("CreateProcessW", |o| o == Os::C).is_none());
    }

    /// Pointer types reach their structure through a typedef or a tag, and
    /// the layout differs by word.
    #[test]
    fn pointers_reach_their_structures() {
        let si = pointee("LPSTARTUPINFOW").expect("LPSTARTUPINFOW");
        assert_eq!(
            (si.tag, si.size64, si.size32),
            ("_STARTUPINFOW", 104, Some(68))
        );
        assert_eq!(
            pointee("struct _STARTUPINFOW *").map(|s| s.tag),
            Some("_STARTUPINFOW")
        );
        assert!(pointee("LPCRITICAL_SECTION").is_some());
        assert!(pointee("LPSTARTUPINFOW *").is_none());
        let at64 = si.at(8);
        let at32 = si.at(4);
        let find = |v: &[(u64, super::Field)], n: &str| {
            v.iter().find(|(_, f)| f.name == n).map(|(o, _)| *o)
        };
        assert_eq!(find(&at64, "hStdError"), Some(96));
        assert_eq!(find(&at32, "hStdError"), Some(64));
        assert_eq!(typedef("SIZE_T").and_then(|t| t.pass), Some("word"));
        assert!(structure("_RTL_CRITICAL_SECTION").is_some());
    }

    /// A declaration spells as C with the name shielded from macros and a
    /// function pointer's name inside its declarator.
    #[test]
    fn declarations_spell_as_c() {
        let win = |o: Os| o == Os::Win;
        let create = declared("CreateFileW", win).expect("CreateFileW");
        assert_eq!(
            spell(create),
            "HANDLE (__stdcall CreateFileW)(LPCWSTR lpFileName, DWORD dwDesiredAccess, \
             DWORD dwShareMode, LPSECURITY_ATTRIBUTES lpSecurityAttributes, \
             DWORD dwCreationDisposition, DWORD dwFlagsAndAttributes, HANDLE hTemplateFile);"
        );
        let atexit = declared("atexit", win).expect("atexit");
        assert_eq!(spell(atexit), "int (atexit)(void (*a1)(void));");
    }
}
