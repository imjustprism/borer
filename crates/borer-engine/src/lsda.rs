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
/// `DW_EH_PE_indirect`: the value is the address of a slot holding the
/// pointer.
const INDIRECT: u8 = 0x80;
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
    let mut lsdas = compact_lsdas(program);
    if let Some(sec) = program
        .sections
        .iter()
        .find(|s| s.name == ".eh_frame" || s.name == "__TEXT,__eh_frame")
        && let Some(bytes) = program.section_bytes(sec)
    {
        lsdas.extend(
            crate::eh_frame::fdes(bytes, sec.va.0, program.is_64)
                .into_iter()
                .filter_map(|fde| Some((fde.start, fde.lsda?))),
        );
    }
    for (func, at) in lsdas {
        if let Some(sites) = sites_of(program, func, at)
            && !sites.is_empty()
        {
            out.entry(func).or_insert(sites);
        }
    }
    out
}

/// Reads the LSDA index of a Mach-O's compact unwind table.
///
/// ld64 and lld keep a function's LSDA pointer out of `__eh_frame` when
/// its unwind fits a compact encoding: each first-level index entry of
/// `__unwind_info` names where its run of `{function offset, LSDA offset}`
/// pairs begins, and the next entry where it ends, both offsets from
/// `__TEXT`. Past [`SITES_MAX`] pairs the rest is not read.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// `(function, LSDA)` addresses in table order; none without the section.
fn compact_lsdas(program: &Program) -> Vec<(u64, u64)> {
    /// The one `__unwind_info` version there is.
    const VERSION: u32 = 1;
    /// Bytes in one first-level index entry.
    const INDEX_ENTRY: u64 = 12;
    let mut out = Vec::new();
    let Some(sec) = program
        .sections
        .iter()
        .find(|s| s.name == "__TEXT,__unwind_info")
    else {
        return out;
    };
    let base = sec.va.0;
    let word = |off: u64| crate::analysis::read_u32(program, base.checked_add(off)?);
    let (Some(VERSION), Some(index), Some(count)) = (word(0), word(20), word(24)) else {
        return out;
    };
    let lsda_at = |k: u32| word(u64::from(index) + u64::from(k) * INDEX_ENTRY + 8);
    let (Some(first), Some(last)) = (lsda_at(0), count.checked_sub(1).and_then(lsda_at)) else {
        return out;
    };
    let text = program.image_base;
    let mut at = u64::from(first);
    while at + 8 <= u64::from(last) && out.len() < SITES_MAX {
        let (Some(func), Some(lsda)) = (word(at), word(at + 4)) else {
            break;
        };
        out.push((
            text.wrapping_add(u64::from(func)),
            text.wrapping_add(u64::from(lsda)),
        ));
        at += 8;
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
        let offset = c.uleb()?;
        let after = sec.va.0.checked_add(u64::try_from(c.pos).ok()?)?;
        Some((ttype_enc, after.wrapping_add(offset)))
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
        let (clauses, cleanup) = if action == 0 {
            (Vec::new(), false)
        } else {
            chain(program, sec, bytes, ttype, actions, action)
        };
        let (filters, catches) = clauses.into_iter().unzip();
        out.push(ThrowSite {
            start: start_va,
            end: end_va,
            landing_pad,
            catches,
            filters,
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
/// Each entry is a type filter and the offset of the next entry from the
/// offset field itself, backward as often as forward since chains share
/// their tails, and the chain ends at a zero offset. A
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
/// The filter and demangled type of each clause the chain catches, in
/// clause order (`type_<filter>` for a type whose descriptor does not
/// read, so the clause still counts), and whether it holds a cleanup;
/// whatever a broken tail leaves unread is simply not claimed.
fn chain(
    program: &Program,
    sec: &crate::program::Section,
    bytes: &[u8],
    ttype: Option<(u8, u64)>,
    actions: u64,
    action: u32,
) -> (Vec<(i64, String)>, bool) {
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
        let field = c.pos;
        let Some(next) = c.sleb() else {
            break;
        };
        if filter == 0 {
            cleanup = true;
        } else if filter > 0 {
            let name = ttype
                .and_then(|(enc, base)| entry(program, sec, bytes, enc, base, filter))
                .unwrap_or_else(|| format!("type_{filter}"));
            catches.push((filter, name));
        }
        let Some(after) = i64::try_from(field)
            .ok()
            .and_then(|f| f.checked_add(next))
            .and_then(|p| usize::try_from(p).ok())
            .filter(|p| next != 0 && *p < bytes.len())
        else {
            break;
        };
        at = after;
    }
    (catches, cleanup)
}

/// Reads the type a filter names out of the type table.
///
/// The entry sits that many entry widths below the table's base and holds
/// the `type_info` object's address in the header's `T` encoding, or the
/// address of a slot holding it when the encoding is `indirect`, as
/// position-independent code writes it; a zero entry is `catch (...)`.
/// The object is a vtable pointer then a pointer to the mangled name.
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
    let mut raw = Cursor {
        bytes,
        pos,
        base: sec.va.0,
        ptr64: program.is_64,
    };
    if raw.pointer(enc & 0x0f)? == 0 {
        return Some("...".to_owned());
    }
    let mut descriptor = c.pointer(enc & 0x7f)?;
    if enc & INDIRECT != 0 {
        if let Some(name) = import_at(program, descriptor) {
            return Some(name);
        }
        descriptor = crate::analysis::read_word(program, descriptor)?;
    }
    let word = crate::analysis::pointer_size(program);
    let name = crate::analysis::read_word(program, descriptor.checked_add(word)?)?;
    let (_, raw) = crate::strings::cstr_at(program, name, 1, NAME_MAX)?;
    Some(name_of(&raw))
}

/// Names the type a GOT slot bound to an imported `type_info` stands for.
///
/// A type the image does not define - `std::exception` out of the C++
/// runtime - is reached through a slot the loader binds to the import
/// `_ZTI<type>`, so the import's name is the type's: mangled, or as the
/// loader names it once demangled (`typeinfo for std::exception`).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `slot` - The slot the type-table entry points at.
///
/// # Returns
///
/// The demangled type, or `None` when no `type_info` import is bound
/// there.
fn import_at(program: &Program, slot: u64) -> Option<String> {
    let s = program
        .symbols
        .iter()
        .find(|s| s.kind == crate::program::SymbolKind::Import && s.addr == slot)?;
    let bare = s.name.rsplit('!').next()?;
    if let Some(ty) = bare.strip_prefix("typeinfo for ") {
        return Some(ty.to_owned());
    }
    let mangled = bare.strip_prefix('_').unwrap_or(bare).strip_prefix("ZTI")?;
    Some(name_of(mangled))
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
    use super::{chain, name_of};
    use crate::program::{Arch, Program, Section};

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

    /// An action chain steps from each entry's offset field, back as
    /// often as forward, and a null type entry is `catch (...)`; a zero
    /// filter is a cleanup.
    #[test]
    fn a_chain_steps_back_from_its_offset_fields() {
        let mut bytes = vec![0u8; 0x60];
        bytes[..6].copy_from_slice(&[0x00, 0x00, 0x01, 0x7d, 0x02, 0x7d]);
        bytes[0x18..0x20].copy_from_slice(&0x3040u64.to_le_bytes());
        bytes[0x48..0x50].copy_from_slice(&0x3050u64.to_le_bytes());
        bytes[0x50..0x57].copy_from_slice(b"5Error\0");
        let sec = Section::mapped(".gcc_except_table", 0x3000, 0, 0x60, false, false);
        let p = Program::raw(bytes.clone(), Arch::X86_64, 0, None, vec![sec.clone()]);
        let (clauses, cleanup) = chain(&p, &sec, &bytes, Some((0x00, 0x3020)), 0x3000, 5);
        assert_eq!(
            clauses,
            vec![(2, "...".to_owned()), (1, "Error".to_owned())]
        );
        assert!(cleanup);
    }

    /// A clause whose type entry does not read still counts as a clause,
    /// named by its filter, so a landing pad's selectors stay matched to
    /// its clauses.
    #[test]
    fn an_unread_type_keeps_its_clause() {
        let bytes = vec![0x01u8, 0x00];
        let sec = Section::mapped(".gcc_except_table", 0x3000, 0, 2, false, false);
        let p = Program::raw(bytes.clone(), Arch::X86_64, 0, None, vec![sec.clone()]);
        let (clauses, cleanup) = chain(&p, &sec, &bytes, None, 0x3000, 1);
        assert_eq!(clauses, vec![(1, "type_1".to_owned())]);
        assert!(!cleanup);
    }
}
