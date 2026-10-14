//! The Itanium C++ ABI's language-specific data areas: the call-site tables
//! a GCC or Clang toolchain keeps in `.gcc_except_table`, one per function
//! that can unwind through a call.
//!
//! An `.eh_frame` FDE whose CIE's augmentation names an `L` encoding carries
//! the address of its function's LSDA ([`crate::eh_frame::fdes`]). The LSDA
//! opens with the landing-pad base and the call-site table's encoding, then
//! holds one record per region of the function a call may throw through:
//! where the region is, where the unwinder resumes inside the function when
//! something throws, and which action names what it catches. The landing
//! pads are labels of the function itself that no instruction of it
//! reaches, so discovery walks them as extra roots of their parent, the way
//! an MSVC `__except` body is walked ([`crate::unwind::continuations`]).
//!
//! The action table after the call sites is walked to what each landing pad
//! catches: a positive filter indexes the type table the header's `T`
//! encoding names, whose entries are Itanium `type_info` objects, and a
//! zero filter is a cleanup that runs for everything. A negative filter is
//! an exception specification, not a clause, and contributes nothing. The
//! base-class and virtual hierarchies the type descriptors carry are left
//! to a later reader: the name is what a clause shows.

use std::collections::BTreeMap;

use crate::analysis::ThrowSite;
use crate::eh_frame::Cursor;
use crate::program::Program;

/// `DW_EH_PE_omit`: no value present.
const OMIT: u8 = 0xff;
/// Most call-site records read from one LSDA.
const SITES_MAX: usize = 16384;
/// Most action entries one call site's catch chain walks.
const ACTIONS_MAX: usize = 16;
/// Longest mangled type name read from a type descriptor.
const NAME_MAX: usize = 512;

/// Reads every function's LSDA call sites out of the `.eh_frame` FDEs and
/// the LSDAs they name.
///
/// A function whose FDE carries no LSDA pointer, one whose LSDA lies in no
/// file-backed section, and one whose table does not hold together (an
/// encoding this does not read, a table past its section, a site or landing
/// pad outside code, more sites than [`SITES_MAX`]) all contribute nothing:
/// the file is hostile by definition, and a lie is answered by the absence
/// of facts, never by a guess.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// The call sites of each function that carries a readable LSDA, by the
/// function's entry, each list sorted by site start.
pub(crate) fn throw_sites(program: &Program) -> BTreeMap<u64, Vec<ThrowSite>> {
    let mut out: BTreeMap<u64, Vec<ThrowSite>> = BTreeMap::new();
    let Some(sec) = program.sections.iter().find(|s| s.name == ".eh_frame") else {
        return out;
    };
    let Some(bytes) = program.section_bytes(sec) else {
        return out;
    };
    for fde in crate::eh_frame::fdes(bytes, sec.va.0, program.is_64) {
        let Some(at) = fde.lsda else {
            continue;
        };
        if let Some(sites) = sites_of(program, fde.start, at)
            && !sites.is_empty()
        {
            out.insert(fde.start, sites);
        }
    }
    out
}

/// Parses one function's LSDA into call sites.
///
/// The header is read the way the personality routines read it: a
/// landing-pad encoding (or `omit`, leaving the base at the function's
/// start), a type-table encoding whose offset gives the table's base, then
/// the call-site table under its own encoding and length. Every record's
/// range and landing pad must land in executable code, or the whole table
/// is refused - the same discipline the MSVC scope-table reader holds
/// ([`crate::unwind`]). The action chains are resolved after the records
/// hold together, and a chain that stops mid-way keeps what it walked: the
/// range and its pad are facts of their own, and the catches are the
/// addition a broken tail cannot lie about, only shorten.
///
/// # Arguments
///
/// * `program` - The loaded image, for the section bounds and the check
///   that sites hold together.
/// * `func` - The function's entry, the base call-site offsets count from.
/// * `at` - The LSDA's address.
///
/// # Returns
///
/// The call sites sorted by start, or `None` when the LSDA is malformed or
/// lives in no file-backed section.
fn sites_of(program: &Program, func: u64, at: u64) -> Option<Vec<ThrowSite>> {
    let sec = program.section_at(at)?;
    let bytes = program.section_bytes(sec)?;
    let off = usize::try_from(at.checked_sub(sec.va.0)?).ok()?;
    let mut c = Cursor {
        bytes,
        pos: off,
        base: sec.va.0,
        ptr64: program.is_64,
    };
    let lpstart_enc = c.u8()?;
    let lpstart = if lpstart_enc == OMIT {
        func
    } else {
        c.pointer(lpstart_enc)?
    };
    let ttype_enc = c.u8()?;
    let ttype = if ttype_enc == OMIT {
        None
    } else {
        // SPEC: Itanium C++ ABI, LSDA header: the type table's base is the
        // uleb offset's own field position plus the offset, and the entry a
        // filter names sits that many entry widths below the base.
        let field = sec.va.0.checked_add(u64::try_from(c.pos).ok()?)?;
        let base = field.wrapping_add(c.uleb()?);
        Some((ttype_enc, base))
    };
    let cs_enc = c.u8()?;
    let table_len = usize::try_from(c.uleb()?).ok()?;
    let table = c.take(table_len)?;
    let base = sec
        .va
        .0
        .checked_add(u64::try_from(c.pos - table.len()).ok()?)?;
    let actions = base.checked_add(u64::try_from(table.len()).ok()?)?;
    let mut t = Cursor {
        bytes: table,
        pos: 0,
        base,
        ptr64: program.is_64,
    };
    let code = |va: u64| crate::analysis::is_executable_va(program, va);
    let mut out = Vec::new();
    while t.pos < table.len() {
        if out.len() >= SITES_MAX {
            return None;
        }
        let start = t.offset(cs_enc)?;
        let len = t.offset(cs_enc)?;
        let lp = t.offset(cs_enc)?;
        let action = u32::try_from(t.uleb()?).ok()?;
        let start_va = func.checked_add(start)?;
        let end_va = start_va.checked_add(len)?;
        if len == 0 || !code(start_va) || !code(end_va - 1) {
            return None;
        }
        let landing_pad = if lp == 0 {
            None
        } else {
            let pad = lpstart.checked_add(lp)?;
            if !code(pad) {
                return None;
            }
            Some(pad)
        };
        let (catches, cleanup) = if action == 0 {
            (Vec::new(), false)
        } else {
            chain(program, sec, bytes, ttype, actions, action)
        };
        out.push(ThrowSite {
            start: start_va,
            end: end_va,
            landing_pad,
            catches,
            cleanup,
        });
    }
    out.sort_unstable_by_key(|s| s.start);
    Some(out)
}

/// Walks one call site's action chain to what its landing pad catches.
///
/// A call site's action field is one past the byte offset of its first
/// action entry into the action table, so zero can mean no entry at all.
/// Each entry is a type filter and the offset of the next entry from this
/// one's start, and the chain ends at a non-positive next offset. A
/// positive filter indexes the type table; a zero filter is a cleanup,
/// which runs for whatever passes through, caught or not; a negative one
/// is an exception specification, which says what a function throws, not
/// what a clause catches.
///
/// # Arguments
///
/// * `program` - The loaded image, for the entry widths the type table
///   indexes with.
/// * `sec` - The section the LSDA lives in, the same bytes `bytes` hold.
/// * `bytes` - That section's bytes, where the chain and its type entries
///   are read.
/// * `ttype` - The type-table encoding and base from the LSDA header, or
///   `None` when the header omits the table.
/// * `actions` - The action table's address, where the chain begins.
/// * `action` - The call site's action field, one past its first entry's
///   offset.
///
/// # Returns
///
/// The demangled types the chain catches in clause order, and whether it
/// holds a cleanup; whatever a broken tail leaves unread is simply not
/// claimed.
fn chain(
    program: &Program,
    sec: &crate::program::Section,
    bytes: &[u8],
    ttype: Option<(u8, u64)>,
    actions: u64,
    action: u32,
) -> (Vec<String>, bool) {
    let Some(first) = action
        .checked_sub(1)
        .map(u64::from)
        .and_then(|a| actions.checked_add(a))
        .and_then(|a| a.checked_sub(sec.va.0))
        .and_then(|a| usize::try_from(a).ok())
        .filter(|p| *p < bytes.len())
    else {
        return (Vec::new(), false);
    };
    let mut c = Cursor {
        bytes,
        pos: first,
        base: sec.va.0,
        ptr64: program.is_64,
    };
    let mut catches = Vec::new();
    let mut cleanup = false;
    let mut at = first;
    for _ in 0..ACTIONS_MAX {
        c.pos = at;
        let Some(filter) = c.sleb() else {
            break;
        };
        let Some(next) = c.sleb() else {
            break;
        };
        if filter == 0 {
            cleanup = true;
        } else if filter > 0
            && let Some((enc, base)) = ttype
            && let Some(name) = entry(program, sec, bytes, enc, base, filter)
        {
            catches.push(name);
        }
        if next <= 0 {
            break;
        }
        let Some(step) = usize::try_from(next).ok() else {
            break;
        };
        let Some(after) = at.checked_add(step).filter(|p| *p < bytes.len()) else {
            break;
        };
        at = after;
    }
    (catches, cleanup)
}

/// Reads the type a filter names out of the type table.
///
/// The entry sits that many entry widths below the table's base and holds
/// the `type_info` object's address in the header's `T` encoding; the name
/// is the string the object carries after its vtable pointer.
///
/// # Arguments
///
/// * `program` - The loaded image, for the bounds the descriptor reads.
/// * `sec` - The section the LSDA lives in, the same bytes `bytes` hold.
/// * `bytes` - That section's bytes, where the entry is read.
/// * `enc` - The type-table's `DW_EH_PE` encoding.
/// * `base` - The type table's base address.
/// * `filter` - The positive filter the action entry carries.
///
/// # Returns
///
/// The demangled type name, or `None` when the entry or the descriptor it
/// names does not hold together.
fn entry(
    program: &Program,
    sec: &crate::program::Section,
    bytes: &[u8],
    enc: u8,
    base: u64,
    filter: i64,
) -> Option<String> {
    let size = entry_size(enc, program)?;
    let at = base.checked_sub(u64::try_from(filter).ok()?.checked_mul(size)?)?;
    let pos = usize::try_from(at.checked_sub(sec.va.0)?).ok()?;
    let mut c = Cursor {
        bytes,
        pos,
        base: sec.va.0,
        ptr64: program.is_64,
    };
    let descriptor = c.pointer(enc)?;
    let word = crate::analysis::pointer_size(program);
    let (_, raw) = crate::strings::cstr_at(program, descriptor.checked_add(word)?, 1, NAME_MAX)?;
    Some(name_of(&raw))
}

/// The width one type-table entry takes under its encoding.
///
/// A `uleb` or `sleb` entry has no fixed width to index with, and the
/// widths below are the ones a producer keeps entries for.
///
/// # Arguments
///
/// * `enc` - The type-table's `DW_EH_PE` encoding.
/// * `program` - The loaded image, for the pointer width an absolute
///   entry takes.
///
/// # Returns
///
/// The width in bytes, or `None` for an encoding whose entries cannot be
/// indexed.
fn entry_size(enc: u8, program: &Program) -> Option<u64> {
    Some(match enc & 0x0f {
        0x00 => crate::analysis::pointer_size(program),
        0x02 | 0x0a => 2,
        0x03 | 0x0b => 4,
        0x04 | 0x0c => 8,
        _ => return None,
    })
}

/// Decodes an Itanium `type_info` name into the C it spells.
///
/// A builtin is a single letter or one of the `D` codes; a class name is a
/// mangled name (`N3foo3BarE`, `5Error`) the demangler reads behind the
/// `_Z` a symbol would carry; anything else - a pointer or reference type,
/// whose `type_info` names only its target - is shown as it sits.
///
/// # Arguments
///
/// * `raw` - The name the type descriptor carries.
///
/// # Returns
///
/// The name as C writes it.
fn name_of(raw: &str) -> String {
    let builtin = match raw {
        "v" => "void",
        "w" => "wchar_t",
        "b" => "bool",
        "c" => "char",
        "a" => "signed char",
        "h" => "unsigned char",
        "s" => "short",
        "t" => "unsigned short",
        "i" => "int",
        "j" => "unsigned int",
        "l" => "long",
        "m" => "unsigned long",
        "x" => "long long",
        "y" => "unsigned long long",
        "n" => "__int128",
        "o" => "unsigned __int128",
        "f" => "float",
        "d" => "double",
        "e" => "long double",
        "z" => "...",
        "Dn" => "nullptr_t",
        "Ds" => "char16_t",
        "Di" => "char32_t",
        _ => "",
    };
    if !builtin.is_empty() {
        return builtin.to_owned();
    }
    let tried = format!("_Z{raw}");
    let demangled = crate::search::demangled_name(&tried);
    if demangled == tried {
        raw.to_owned()
    } else {
        demangled
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::name_of;

    /// The type-table names decode as C writes them: builtins by their
    /// letter, classes through the demangler behind the `_Z` a symbol
    /// would carry, and anything the demangler refuses stays as it sits.
    #[test]
    fn type_names_decode_as_c_writes_them() {
        assert_eq!(name_of("i"), "int");
        assert_eq!(name_of("d"), "double");
        assert_eq!(name_of("y"), "unsigned long long");
        assert_eq!(name_of("Dn"), "nullptr_t");
        assert_eq!(name_of("N3foo3BarE"), "foo::Bar");
        assert_eq!(name_of("5Error"), "Error");
        assert_eq!(name_of("Pi"), "Pi", "a pointer type keeps its raw name");
    }
}
