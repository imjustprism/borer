//! DWARF debug information: the function names a compiler left behind.
//!
//! A binary built with debug information carries the name, and often the
//! parameter names, of every function the compiler saw. Reading them turns
//! `sub_1400b9150` into `_pei386_runtime_relocator` with no signature
//! database, heuristic or guess involved, because the compiler wrote it down.
//!
//! This reads the subset that answers "what is this function called, and
//! what did it name": the abbreviation tables, the unit headers, the
//! `DW_TAG_subprogram` entries carrying a name and an address, the
//! frame-relative `DW_TAG_variable` entries under them, placed by the
//! subprogram's own frame base, and the struct layouts and enum constants
//! the types state. Every other attribute is skipped by its form, which is
//! what makes a partial reader safe: a form this does not interpret still
//! has a known length.
//!
//! DWARF 2 through 5 are read. On a stripped image the section names are
//! gone, so the sections are found by the shape of their bytes
//! ([`crate::headers::sniff_section`]) rather than by name.

use crate::analysis::utypes::{
    ENUM_VALUES_MAX, FIELDS_MAX, TypeExpr, UserField, UserStruct, UserType, build_enum,
    check_type_name, is_ident,
};
use crate::program::Section;
use std::collections::BTreeMap;

/// `DW_TAG_subprogram`: a function.
const TAG_SUBPROGRAM: u64 = 0x2e;
/// `DW_TAG_formal_parameter`: one declared parameter.
const TAG_FORMAL_PARAMETER: u64 = 0x05;
/// `DW_AT_name`.
const AT_NAME: u64 = 0x03;
/// `DW_AT_low_pc`: the entry address.
const AT_LOW_PC: u64 = 0x11;
/// `DW_AT_abstract_origin`: this entry is a copy of another, which holds the
/// name. Inlined and cloned bodies are emitted this way.
const AT_ABSTRACT_ORIGIN: u64 = 0x31;
/// `DW_AT_specification`: the declaration an out-of-line definition completes.
const AT_SPECIFICATION: u64 = 0x47;
/// `DW_FORM_implicit_const`, whose value lives in the abbreviation.
const FORM_IMPLICIT_CONST: u64 = 0x21;
/// `DW_AT_type`: the entry describing this one's type.
const AT_TYPE: u64 = 0x49;
/// `DW_FORM_ref_addr`, the one reference form that is section-relative; every
/// other is relative to its own unit.
const FORM_REF_ADDR: u64 = 0x10;
/// `DW_TAG_pointer_type`.
const TAG_POINTER: u64 = 0x0f;
/// `DW_TAG_reference_type`.
const TAG_REFERENCE: u64 = 0x10;
/// `DW_TAG_rvalue_reference_type`.
const TAG_RVALUE_REFERENCE: u64 = 0x42;
/// `DW_TAG_const_type`.
const TAG_CONST: u64 = 0x26;
/// `DW_TAG_volatile_type`.
const TAG_VOLATILE: u64 = 0x35;
/// `DW_TAG_array_type`.
const TAG_ARRAY: u64 = 0x01;
/// `DW_TAG_structure_type`.
const TAG_STRUCTURE: u64 = 0x13;
/// `DW_TAG_union_type`.
const TAG_UNION: u64 = 0x17;
/// `DW_TAG_class_type`.
const TAG_CLASS: u64 = 0x02;
/// `DW_TAG_enumeration_type`.
const TAG_ENUMERATION: u64 = 0x04;
/// `DW_TAG_subroutine_type`: a function type, reached through a pointer.
const TAG_SUBROUTINE: u64 = 0x15;
/// How far a type chain is followed before it is called circular.
const TYPE_DEPTH: u32 = 16;
/// `DW_TAG_variable`: a local or global variable's own entry.
const TAG_VARIABLE: u64 = 0x34;
/// `DW_TAG_member`: one field of a struct, class or union.
const TAG_MEMBER: u64 = 0x0d;
/// `DW_TAG_enumerator`: one named value of an enumeration.
const TAG_ENUMERATOR: u64 = 0x28;
/// `DW_TAG_typedef`: a name standing for another type.
const TAG_TYPEDEF: u64 = 0x16;
/// `DW_AT_location`: where a variable lives at run time.
const AT_LOCATION: u64 = 0x02;
/// `DW_AT_byte_size`: a type's width in bytes.
const AT_BYTE_SIZE: u64 = 0x0b;
/// `DW_AT_const_value`: an enumerator's value.
const AT_CONST_VALUE: u64 = 0x1c;
/// `DW_AT_data_member_location`: a member's offset in its struct.
const AT_MEMBER_LOCATION: u64 = 0x38;
/// `DW_AT_encoding`: how a base type's bits are read.
const AT_ENCODING: u64 = 0x3e;
/// `DW_AT_frame_base`: the base a subprogram's `DW_OP_fbreg` offsets
/// count from.
const AT_FRAME_BASE: u64 = 0x70;
/// `DW_OP_fbreg`, the one location opcode that places a variable in its
/// function's frame: a signed offset from the frame base.
const OP_FBREG: u8 = 0x91;
/// `DW_OP_call_frame_cfa`, naming the caller's stack pointer just above
/// the pushed return address as the frame base.
const OP_CALL_FRAME_CFA: u8 = 0x9c;
/// `DW_OP_reg0`: `DW_OP_regN` is `OP_REG0 + N`, naming register `N` alone.
const OP_REG0: u8 = 0x50;
/// `DW_OP_reg31`, the last of the one-byte register opcodes.
const OP_REG_LAST: u8 = 0x6f;
/// `DW_OP_regx`, naming a register by a `ULEB128` that follows it.
const OP_REGX: u8 = 0x9e;
/// Most locals one function states, whatever its debug information.
///
/// No real function declares more than a few dozen named locals; past this
/// the reader stops taking them, the same discipline every capped walk
/// keeps against debug information that states more than a frame can hold.
pub(crate) const LOCALS_MAX: usize = 64;
/// Most types one program's debug information states.
///
/// No real program declares more; past this the reader stops taking them,
/// the same discipline every capped walk keeps against debug information
/// larger than any type table holds.
const TYPES_MAX: usize = 1 << 13;
/// Furthest from the entry stack pointer a local's slot may sit, in bytes.
///
/// A frame larger than this holds no local a compiler lays out for a
/// function a decompiler reads; debug information stating one further out
/// is a shifted or hostile stream and is refused rather than named onto a
/// slot the text may declare far from where the record means.
pub(crate) const FRAME_SPAN: i64 = 0x1_0000;

/// One declared parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    /// The name the compiler recorded.
    pub name: String,
    /// Its type as C source, when the type chain resolved.
    pub type_name: Option<String>,
}

/// One function the debug information names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subprogram {
    /// Entry address, as linked.
    pub low_pc: u64,
    /// The name the compiler recorded.
    pub name: String,
    /// Declared parameters in order; empty when none were recorded.
    pub parameters: Vec<Parameter>,
    /// The return type as C source, `None` for `void` or when unresolved.
    pub return_type: Option<String>,
    /// The frame-relative locals the debug information states for the
    /// function, by their slot offset: bytes from the stack pointer at
    /// entry, negative for a local of the frame. Empty where none were
    /// stated; every reader inserts through [`take_local`], which keeps
    /// one slot and one name for one local.
    pub locals: BTreeMap<i64, String>,
}

/// Whether a local's name can stand as a variable in the decompiled text.
///
/// The name renders verbatim where `local_N` otherwise would, so one that
/// is not a bare identifier, that spells a word the text's own grammar
/// reads, or that collides with a name the text synthesizes for a slot,
/// a temporary, a parameter or a global (`local_8`, `tmp_1`, `a3`,
/// `g64_...`) would make the text say or mean something else than the
/// variable it names. Both debug readers hold their names to this.
///
/// # Arguments
///
/// * `name` - The name the debug information states.
pub(crate) fn local_name_ok(name: &str) -> bool {
    let mut chars = name.chars();
    let first = chars.next().unwrap_or('0');
    let digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !matches!(
            name,
            "retaddr"
                | "if"
                | "else"
                | "while"
                | "for"
                | "return"
                | "do"
                | "switch"
                | "case"
                | "break"
                | "continue"
                | "goto"
                | "default"
                | "true"
                | "false"
                | "sizeof"
        )
        && !name.starts_with("local_")
        && !name.starts_with("home_")
        && !name.starts_with("arg_")
        && !name.starts_with("tmp_")
        && !name.strip_prefix('a').is_some_and(digits)
        && !name
            .strip_prefix('g')
            .is_some_and(|rest| rest.split_once('_').is_some_and(|(bits, _)| digits(bits)))
}

/// Converts a debug-stated frame offset to the slot the decompiler's text
/// names it by, with the frame-pointer-relative form both readers state.
///
/// The decompiler numbers slots from the stack pointer at entry, the
/// return address at zero. A record relative to the frame pointer names an
/// address a word under it, the pushed register itself; one relative to
/// the stack pointer - the frame-pointer-less frame a modern build lays
/// out - names an address the prologue's whole frame below entry, which
/// the PDB's procedure frame record states. Callee-saved pushes that
/// record leaves out of its size shift a stack-relative offset by their
/// bytes: such a local lands past the slot the text declares and is left
/// unused, never named onto the wrong slot by a guess.
///
/// # Arguments
///
/// * `off` - The offset the debug information states, from its base.
/// * `base_bp` - Whether the base is the frame pointer register; `false`
///   for the stack pointer one, a form only the PDB reader states.
/// * `word` - The stack word in bytes.
/// * `frame` - The frame's size in bytes as the PDB's frame record states
///   it, the bottom for a stack-pointer-relative offset.
///
/// # Returns
///
/// The slot offset, or `None` when the offset states no local a frame
/// holds: outside [`FRAME_SPAN`], or the return address's own slot.
pub(crate) fn frame_slot(off: i32, base_bp: bool, word: i64, frame: i64) -> Option<i64> {
    let slot = if base_bp {
        i64::from(off) - word
    } else {
        i64::from(off) - frame
    };
    slot_held(slot)
}

/// Whether a converted slot is one a frame holds: not the return
/// address's own slot, and within [`FRAME_SPAN`] of the entry stack
/// pointer.
///
/// # Arguments
///
/// * `slot` - The converted slot offset.
///
/// # Returns
///
/// The slot, or `None` when no frame holds it.
fn slot_held(slot: i64) -> Option<i64> {
    (slot != 0 && slot.abs() <= FRAME_SPAN).then_some(slot)
}

/// Takes one frame-relative local for a function the debug information
/// names, into its [`Subprogram::locals`] map.
///
/// The name joins the map unless another local already holds its slot or
/// its name: two locals of one frame never share either, so a record that
/// does is a shifted or hostile stream and is left out rather than split
/// across two slots, which would name the wrong one in the text. The cap
/// counts locals as both readers' walks count them, but silently. Both
/// debug readers insert through this, so one contract governs the map.
///
/// # Arguments
///
/// * `map` - The function's locals map, by slot offset.
/// * `slot` - The converted slot offset; `None` refuses the record.
/// * `name` - The local's name, already checked by [`local_name_ok`].
pub(crate) fn take_local(map: &mut BTreeMap<i64, String>, slot: Option<i64>, name: &str) {
    let Some(slot) = slot else {
        return;
    };
    if map.len() >= LOCALS_MAX || map.contains_key(&slot) || map.values().any(|n| n == name) {
        return;
    }
    map.insert(slot, name.to_owned());
}

/// One read position in one section.
struct Cursor<'a> {
    /// The bytes being read.
    bytes: &'a [u8],
    /// The next byte to read.
    at: usize,
}

impl<'a> Cursor<'a> {
    /// Starts a cursor at `at`.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The section.
    /// * `at` - Where to start.
    fn new(bytes: &'a [u8], at: usize) -> Self {
        Self { bytes, at }
    }

    /// Whether the cursor has reached `end` or the end of the section.
    ///
    /// # Arguments
    ///
    /// * `end` - The unit's end offset.
    fn done(&self, end: usize) -> bool {
        self.at >= end || self.at >= self.bytes.len()
    }

    /// Reads one byte.
    fn u8(&mut self) -> Option<u8> {
        let b = *self.bytes.get(self.at)?;
        self.at += 1;
        Some(b)
    }

    /// Reads `n` little-endian bytes as an unsigned value.
    ///
    /// # Arguments
    ///
    /// * `n` - Byte count, at most eight.
    fn uint(&mut self, n: usize) -> Option<u64> {
        let end = self.at.checked_add(n)?;
        let slice = self.bytes.get(self.at..end)?;
        self.at = end;
        let mut v = 0u64;
        for (k, b) in slice.iter().enumerate().take(8) {
            v |= u64::from(*b) << (k * 8);
        }
        Some(v)
    }

    /// Skips `n` bytes, failing when they are not there.
    ///
    /// # Arguments
    ///
    /// * `n` - How many bytes to pass over.
    fn skip(&mut self, n: usize) -> Option<()> {
        let end = self.at.checked_add(n)?;
        if end > self.bytes.len() {
            return None;
        }
        self.at = end;
        Some(())
    }

    /// Reads an unsigned LEB128.
    fn uleb(&mut self) -> Option<u64> {
        let mut v = 0u64;
        let mut shift = 0u32;
        loop {
            let b = self.u8()?;
            if shift < 64 {
                v |= u64::from(b & 0x7f) << shift;
            }
            shift += 7;
            if b & 0x80 == 0 {
                return Some(v);
            }
            if shift > 128 {
                return None;
            }
        }
    }

    /// Reads a signed LEB128.
    fn sleb(&mut self) -> Option<i64> {
        let mut v = 0i64;
        let mut shift = 0u32;
        loop {
            let b = self.u8()?;
            if shift < 64 {
                v |= i64::from(b & 0x7f) << shift;
            }
            shift += 7;
            if b & 0x80 == 0 {
                if shift < 64 && b & 0x40 != 0 {
                    v -= 1i64 << shift;
                }
                return Some(v);
            }
            if shift > 128 {
                return None;
            }
        }
    }

    /// Reads a NUL-terminated string.
    fn cstr(&mut self) -> Option<String> {
        let rest = self.bytes.get(self.at..)?;
        let len = rest.iter().position(|b| *b == 0)?;
        let s = String::from_utf8_lossy(rest.get(..len)?).into_owned();
        self.at += len + 1;
        Some(s)
    }
}

/// Reads a NUL-terminated string at `at` in a string section.
///
/// # Arguments
///
/// * `section` - The string section.
/// * `at` - Offset of the string.
///
/// # Returns
///
/// The string, or `None` when the offset is outside the section.
fn string_at(section: &[u8], at: usize) -> Option<String> {
    let rest = section.get(at..)?;
    let len = rest.iter().position(|b| *b == 0)?;
    Some(String::from_utf8_lossy(rest.get(..len)?).into_owned())
}

/// One attribute of an abbreviation: what it is and how it is encoded.
#[derive(Clone, Copy)]
struct Attribute {
    /// `DW_AT_*`.
    at: u64,
    /// `DW_FORM_*`.
    form: u64,
    /// The value itself, for `DW_FORM_implicit_const`.
    implicit: i64,
}

/// One abbreviation: the shape shared by every entry declaring its code.
struct Abbreviation {
    /// `DW_TAG_*`.
    tag: u64,
    /// Whether entries of this shape are followed by their children.
    children: bool,
    /// The attributes, in the order an entry carries them.
    attributes: Vec<Attribute>,
}

/// Reads the abbreviation table at `offset`.
///
/// # Arguments
///
/// * `abbrev` - The `.debug_abbrev` section.
/// * `offset` - Offset of this unit's table.
///
/// # Returns
///
/// The abbreviations by code, or `None` when the table does not parse.
fn abbreviations(abbrev: &[u8], offset: usize) -> Option<BTreeMap<u64, Abbreviation>> {
    let mut c = Cursor::new(abbrev, offset);
    let mut out = BTreeMap::new();
    loop {
        let code = c.uleb()?;
        if code == 0 {
            return Some(out);
        }
        let tag = c.uleb()?;
        let children = c.u8()? != 0;
        let mut attributes = Vec::new();
        loop {
            let at = c.uleb()?;
            let form = c.uleb()?;
            let implicit = if form == FORM_IMPLICIT_CONST {
                c.sleb()?
            } else {
                0
            };
            if at == 0 && form == 0 {
                break;
            }
            attributes.push(Attribute { at, form, implicit });
        }
        out.insert(
            code,
            Abbreviation {
                tag,
                children,
                attributes,
            },
        );
    }
}

/// A value read from an attribute, kept only when it could name or place a
/// function.
enum Value {
    /// An integer: an address, a constant or a reference.
    Int(u64),
    /// A string, resolved out of its section.
    Text(String),
    /// The bytes of an expression, for the attributes whose opcodes place
    /// a variable.
    Expr(Vec<u8>),
    /// A value whose form was understood well enough to pass over.
    Skipped,
}

/// The string sections a unit resolves its names against.
struct Strings<'a> {
    /// `.debug_str`, for `DW_FORM_strp`.
    text: &'a [u8],
    /// `.debug_line_str`, for `DW_FORM_line_strp`.
    lines: &'a [u8],
}

/// Reads one attribute's value, or passes over it by form.
///
/// A form this does not interpret still has a known length, which is what
/// lets a reader that understands four attributes walk the whole tree without
/// losing its place. An unknown form is the one case it cannot recover from,
/// and it ends the unit rather than guessing a length.
///
/// # Arguments
///
/// * `c` - The cursor, at the value.
/// * `form` - `DW_FORM_*`.
/// * `implicit` - The value for `DW_FORM_implicit_const`.
/// * `address_size` - The unit's address size in bytes.
/// * `offset_size` - Four for 32-bit DWARF, eight for 64-bit.
/// * `strings` - The string sections.
///
/// # Returns
///
/// The value, or `None` when the form is unknown or the bytes run out.
fn value(
    c: &mut Cursor<'_>,
    form: u64,
    implicit: i64,
    address_size: usize,
    offset_size: usize,
    strings: &Strings<'_>,
) -> Option<Value> {
    Some(match form {
        // DW_FORM_addr
        0x01 => Value::Int(c.uint(address_size)?),
        // block forms: a length, then that many bytes; the expression
        // form is kept, for a location is read out of its opcodes
        0x09 => {
            let n = usize::try_from(c.uleb()?).ok()?;
            let end = c.at.checked_add(n)?;
            let bytes = c.bytes.get(c.at..end)?.to_vec();
            c.at = end;
            Value::Expr(bytes)
        }
        0x03 => {
            let n = c.uint(2)?;
            c.skip(usize::try_from(n).ok()?)?;
            Value::Skipped
        }
        0x04 => {
            let n = c.uint(4)?;
            c.skip(usize::try_from(n).ok()?)?;
            Value::Skipped
        }
        0x18 => {
            let n = c.uleb()?;
            c.skip(usize::try_from(n).ok()?)?;
            Value::Skipped
        }
        0x0a => {
            let n = c.u8()?;
            c.skip(usize::from(n))?;
            Value::Skipped
        }
        // fixed-width integers, flags and references
        0x0b | 0x0c | 0x11 | 0x25 | 0x29 => Value::Int(c.uint(1)?),
        0x05 | 0x12 | 0x26 | 0x2a => Value::Int(c.uint(2)?),
        0x27 | 0x2b => Value::Int(c.uint(3)?),
        0x06 | 0x13 | 0x1c | 0x28 | 0x2c => Value::Int(c.uint(4)?),
        0x07 | 0x14 | 0x20 | 0x24 => Value::Int(c.uint(8)?),
        0x1e => {
            c.skip(16)?;
            Value::Skipped
        }
        // offsets into another section, sized by the unit's DWARF width
        0x10 | 0x17 | 0x1d => Value::Int(c.uint(offset_size)?),
        // LEB-encoded integers and indices
        0x0d => Value::Int(c.sleb()?.cast_unsigned()),
        0x0f | 0x15 | 0x1a | 0x1b | 0x22 | 0x23 => Value::Int(c.uleb()?),
        // strings
        0x08 => Value::Text(c.cstr()?),
        0x0e => {
            let at = c.uint(offset_size)?;
            string_at(strings.text, usize::try_from(at).ok()?).map_or(Value::Skipped, Value::Text)
        }
        0x1f => {
            let at = c.uint(offset_size)?;
            string_at(strings.lines, usize::try_from(at).ok()?).map_or(Value::Skipped, Value::Text)
        }
        // present by its own existence, and constant in the abbreviation
        0x19 => Value::Int(1),
        FORM_IMPLICIT_CONST => Value::Int(implicit.cast_unsigned()),
        _ => return None,
    })
}

/// One entry's attributes, as far as naming a function needs them.
#[derive(Default)]
struct Entry {
    /// `DW_AT_name`.
    name: Option<String>,
    /// `DW_AT_low_pc`.
    low_pc: Option<u64>,
    /// `DW_AT_abstract_origin` or `DW_AT_specification`: where the name is.
    origin: Option<u64>,
    /// `DW_AT_type`: the entry describing this one's type, and whether the
    /// reference was relative to its unit.
    type_ref: Option<(u64, bool)>,
    /// `DW_AT_frame_base`: where a subprogram's locals count from.
    frame_base: Option<Vec<u8>>,
    /// `DW_AT_location`: where a variable lives.
    location: Option<Vec<u8>>,
    /// `DW_AT_byte_size`: a type's width in bytes.
    byte_size: Option<u64>,
    /// `DW_AT_encoding`: how a base type's bits are read.
    encoding: Option<u64>,
    /// `DW_AT_data_member_location`: a member's offset in its struct.
    member_off: Option<u64>,
    /// `DW_AT_const_value`: an enumerator's value.
    const_value: Option<u64>,
}

/// What one entry contributes to reading a type: its kind, its name, and
/// the entry it is built from.
struct TypeNode {
    /// `DW_TAG_*`.
    tag: u64,
    /// `DW_AT_name`, for the tags that carry one.
    name: Option<String>,
    /// `DW_AT_type`, absolute in the section.
    inner: Option<u64>,
    /// `DW_AT_encoding` with `DW_AT_byte_size`: the base type's own facts,
    /// which name the scalar it is.
    scalar: Option<(u64, u64)>,
}

/// Renders a type as C source by following the chain from `at`.
///
/// A type is a chain of entries: a parameter points at a `const`, which
/// points at a pointer, which points at a base type. Following it is what
/// turns `uint64_t` into `const char *`. A typedef keeps its own name,
/// because `HANDLE` is what the source said and what a reader recognizes.
///
/// # Arguments
///
/// * `nodes` - Every type entry of the unit, by section offset.
/// * `at` - Where to start, or `None` for `void`.
/// * `depth` - Remaining links to follow, against a circular chain.
///
/// # Returns
///
/// The type as C source, or `None` when the chain does not resolve.
fn type_name(nodes: &BTreeMap<u64, TypeNode>, at: Option<u64>, depth: u32) -> Option<String> {
    let Some(at) = at else {
        return Some(String::from("void"));
    };
    if depth == 0 {
        return None;
    }
    let node = nodes.get(&at)?;
    let inner = || type_name(nodes, node.inner, depth - 1);
    match node.tag {
        TAG_POINTER => {
            let to = inner().unwrap_or_else(|| String::from("void"));
            Some(if to.ends_with('*') {
                format!("{to}*")
            } else {
                format!("{to} *")
            })
        }
        TAG_REFERENCE => Some(format!("{} &", inner()?)),
        TAG_RVALUE_REFERENCE => Some(format!("{} &&", inner()?)),
        TAG_CONST => {
            let to = inner()?;
            // `const` binds to the pointer, not the pointee, when it follows
            // one: `char * const`, not `const char *`.
            Some(if to.ends_with('*') {
                format!("{to} const")
            } else {
                format!("const {to}")
            })
        }
        TAG_VOLATILE => Some(format!("volatile {}", inner()?)),
        TAG_ARRAY => Some(format!("{}[]", inner()?)),
        TAG_SUBROUTINE => Some(format!(
            "{} ()",
            inner().unwrap_or_else(|| String::from("void"))
        )),
        TAG_STRUCTURE | TAG_CLASS => node
            .name
            .clone()
            .map(|n| format!("struct {n}"))
            .or_else(|| Some(String::from("struct"))),
        TAG_UNION => node
            .name
            .clone()
            .map(|n| format!("union {n}"))
            .or_else(|| Some(String::from("union"))),
        TAG_ENUMERATION => node
            .name
            .clone()
            .map(|n| format!("enum {n}"))
            .or_else(|| Some(String::from("enum"))),
        // A base type or a typedef is named outright, and the typedef's own
        // name is the one the source used.
        _ => node.name.clone().or_else(inner),
    }
}

/// The base a subprogram's `DW_OP_fbreg` offsets count from, when the
/// expression it states names one the decompiler's own slots cross to.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FrameBase {
    /// `DW_OP_call_frame_cfa`: the caller's stack pointer just above the
    /// pushed return address, a word above the entry slot zero.
    Caller,
    /// `DW_OP_regN` naming the frame pointer register: `rbp` on the 64-bit
    /// targets, `ebp` on the 32-bit ones, a word below the entry slot
    /// zero once the prologue pushes it.
    FramePointer,
}

/// Reads the frame base a subprogram states.
///
/// A compiler states one of two shapes: the canonical frame address, or
/// the frame pointer register a frame that keeps one. Anything else - a
/// register plus an offset, a memory dereference, more than one opcode -
/// names a base this reader cannot place against the entry stack pointer,
/// and the subprogram's locals contribute nothing rather than land on
/// slots guessed at.
///
/// # Arguments
///
/// * `expr` - The expression's bytes.
/// * `word` - The stack word in bytes, which picks the frame pointer's
///   register number.
///
/// # Returns
///
/// The base, or `None` when the expression names none this reads.
fn frame_base(expr: &[u8], word: i64) -> Option<FrameBase> {
    match expr {
        [OP_CALL_FRAME_CFA] => Some(FrameBase::Caller),
        [reg] if matches!(reg, OP_REG0..=OP_REG_LAST) => {
            frame_pointer(u64::from(*reg - OP_REG0), word)
        }
        [OP_REGX, reg] => frame_pointer(u64::from(*reg), word),
        _ => None,
    }
}

/// Whether a DWARF register number names the frame pointer.
///
/// # Arguments
///
/// * `reg` - The register number the expression states.
/// * `word` - The stack word in bytes, which picks the target's mapping.
///
/// # Returns
///
/// [`FrameBase::FramePointer`] when the register is `rbp` (6) on a 64-bit
/// target or `ebp` (5) on a 32-bit one, else `None`.
fn frame_pointer(reg: u64, word: i64) -> Option<FrameBase> {
    let fp = match word {
        8 => 6,
        4 => 5,
        _ => return None,
    };
    (reg == fp).then_some(FrameBase::FramePointer)
}

/// Reads the frame offset a variable's location states.
///
/// Only a whole-expression `DW_OP_fbreg` places a variable in its frame;
/// one padded with further opcodes, or built from any other opcode, states
/// a location this reader does not reduce to a slot and contributes
/// nothing.
///
/// # Arguments
///
/// * `expr` - The expression's bytes.
///
/// # Returns
/// The signed offset from the subprogram's frame base, or `None` when the
/// expression states no plain frame-relative location.
fn fbreg(expr: &[u8]) -> Option<i64> {
    let mut c = Cursor::new(expr, 0);
    (c.u8()? == OP_FBREG)
        .then(|| c.sleb())
        .flatten()
        .filter(|_| c.done(expr.len()))
}

/// The scalar a base type states, in the language the user types spell.
///
/// # Arguments
///
/// * `encoding` - `DW_ATE_*`.
/// * `size` - The width in bytes.
///
/// # Returns
///
/// The scalar, or `None` for an encoding or width the language does not
/// spell.
fn scalar(encoding: u64, size: u64) -> Option<TypeExpr> {
    Some(match (encoding, size) {
        // DW_ATE_signed
        (0x05, 1) => TypeExpr::I8,
        (0x05, 2) => TypeExpr::I16,
        (0x05, 4) => TypeExpr::I32,
        (0x05, 8) => TypeExpr::I64,
        // DW_ATE_unsigned
        (0x07, 1) => TypeExpr::U8,
        (0x07, 2) => TypeExpr::U16,
        (0x07, 4) => TypeExpr::U32,
        (0x07, 8) => TypeExpr::U64,
        // DW_ATE_float
        (0x04, 4) => TypeExpr::F32,
        (0x04, 8) => TypeExpr::F64,
        // DW_ATE_signed_char: the one byte of text `char` is.
        (0x06, 1) => TypeExpr::Char,
        // DW_ATE_boolean: a byte that holds true or false.
        (0x02, 1) => TypeExpr::U8,
        _ => return None,
    })
}

/// Renders a type in the language the user types spell, by following the
/// chain from `at`.
///
/// The C source [`type_name`] spells serves a signature; a struct layout
/// proposal must be a type an agent can state back, so the chain resolves
/// to the language's scalars and pointers, a named struct or enum by its
/// name, and a typedef to what it stands for. An array, a function type
/// or an encoding the language does not spell resolves to nothing, and a
/// member it types contributes none of itself.
///
/// # Arguments
///
/// * `nodes` - Every type entry of the unit, by section offset.
/// * `at` - Where to start, or `None` for `void`.
/// * `depth` - Remaining links to follow, against a circular chain.
///
/// # Returns
///
/// The type, or `None` when the chain does not resolve into the language.
fn type_expr(nodes: &BTreeMap<u64, TypeNode>, at: Option<u64>, depth: u32) -> Option<TypeExpr> {
    let at = at?;
    if depth == 0 {
        return None;
    }
    let node = nodes.get(&at)?;
    let inner = || type_expr(nodes, node.inner, depth - 1);
    match node.tag {
        TAG_POINTER => Some(TypeExpr::Ptr(Box::new(inner().unwrap_or(TypeExpr::U8)))),
        // The qualifiers the language does not spell fall away.
        TAG_CONST | TAG_VOLATILE => inner(),
        TAG_TYPEDEF => inner(),
        TAG_STRUCTURE | TAG_CLASS | TAG_UNION | TAG_ENUMERATION => {
            node.name.clone().map(TypeExpr::Named)
        }
        _ => node
            .scalar
            .and_then(|(encoding, size)| scalar(encoding, size)),
    }
}

/// One type the unit states, gathered until its members resolve.
struct Stated {
    /// The type's name.
    name: String,
    /// `DW_AT_byte_size`.
    size: u64,
    /// The members, as (name, offset, type reference).
    members: Vec<(String, u64, Option<u64>)>,
    /// The enumerator values, as (value, name).
    values: Vec<(u64, String)>,
    /// Whether this is an enumeration rather than a struct.
    is_enum: bool,
}

/// Reads one unit's header, returning what walking its entries needs.
///
/// DWARF 5 puts the unit's kind before the address size; 2 through 4 put the
/// abbreviation offset first and the address size last.
///
/// # Arguments
///
/// * `c` - A cursor at the unit's start; left at the first entry.
///
/// # Returns
///
/// `(end offset, address size, abbreviation offset, offset size)`, or `None`
/// when the header does not parse or the version is not read.
fn unit_header(c: &mut Cursor<'_>) -> Option<(usize, usize, u64, usize)> {
    let mut length = c.uint(4)?;
    let mut offset_size = 4usize;
    if length == 0xffff_ffff {
        offset_size = 8;
        length = c.uint(8)?;
    }
    if length == 0 {
        return None;
    }
    let end = usize::try_from(length).ok()?.checked_add(c.at)?;
    let version = c.uint(2)?;
    let (address_size, abbrev_offset) = if version >= 5 {
        c.skip(1)?;
        let size = c.u8()?;
        (usize::from(size), c.uint(offset_size)?)
    } else if version >= 2 {
        let off = c.uint(offset_size)?;
        (usize::from(c.u8()?), off)
    } else {
        return None;
    };
    Some((end, address_size, abbrev_offset, offset_size))
}

/// Reads the named functions out of a program's debug information.
///
/// A unit that does not parse is skipped and the rest of the file still
/// reads, which matters on a rebuilt image where one section may be damaged.
///
/// # Arguments
///
/// * `info` - `.debug_info`.
/// * `abbrev` - `.debug_abbrev`.
/// * `strings` - The string sections.
///
/// # Returns
///
/// The named functions, and the stated types by name.
fn read_in(info: &[u8], abbrev: &[u8], strings: &Strings<'_>) -> Debug {
    let mut out: Vec<Subprogram> = Vec::new();
    let mut types: BTreeMap<String, UserType> = BTreeMap::new();
    let mut at = 0usize;
    while at.saturating_add(11) < info.len() {
        let at_start = at;
        let mut c = Cursor::new(info, at);
        let Some((body_end, address_size, abbrev_offset, offset_size)) = unit_header(&mut c) else {
            break;
        };
        at = body_end;
        let end = body_end.min(info.len());
        let Some(table) = usize::try_from(abbrev_offset)
            .ok()
            .and_then(|o| abbreviations(abbrev, o))
        else {
            continue;
        };
        // Entries arrive in tree order, so the open function is the one a
        // parameter belongs to. `by_offset` keeps the names other entries
        // point at with an abstract origin.
        let mut by_offset: BTreeMap<u64, String> = BTreeMap::new();
        let mut depth: Vec<bool> = Vec::new();
        let mut open: Vec<usize> = Vec::new();
        // The frame base of each entry of `out`, at its index: a variable's
        // offset converts through the base of the subprogram it is inside.
        let mut bases: Vec<Option<FrameBase>> = Vec::new();
        let mut pending: Vec<(u64, u64)> = Vec::new();
        // The types this unit states, gathered with their members until the
        // unit is walked and the members' chains can resolve. A named type
        // opens a scope its members belong to; any other entry with children
        // closes it, so a member of a nested or anonymous type never lands
        // on the one outside it.
        let mut stated: Vec<Stated> = Vec::new();
        let mut type_scopes: Vec<Option<usize>> = Vec::new();
        // A type reference points forward as often as back, so the chains
        // are read after the unit is walked, not during it.
        let mut nodes: BTreeMap<u64, TypeNode> = BTreeMap::new();
        let mut unresolved: Vec<(usize, Option<u64>)> = Vec::new();
        let mut unresolved_params: Vec<(usize, usize, Option<u64>)> = Vec::new();
        let unit_base = u64::try_from(at_start).unwrap_or(0);
        while !c.done(end) {
            let here = c.at as u64;
            let Some(code) = c.uleb() else { break };
            if code == 0 {
                // The end of a sibling chain closes the innermost entry.
                if depth.pop() == Some(true) {
                    open.pop();
                }
                type_scopes.pop();
                continue;
            }
            let Some(abbreviation) = table.get(&code) else {
                break;
            };
            let mut entry = Entry::default();
            let mut read = true;
            for a in &abbreviation.attributes {
                let Some(v) = value(
                    &mut c,
                    a.form,
                    a.implicit,
                    address_size,
                    offset_size,
                    strings,
                ) else {
                    read = false;
                    break;
                };
                match (a.at, v) {
                    (AT_NAME, Value::Text(t)) => entry.name = Some(t),
                    (AT_LOW_PC, Value::Int(v)) => entry.low_pc = Some(v),
                    (AT_ABSTRACT_ORIGIN | AT_SPECIFICATION, Value::Int(v)) => {
                        entry.origin = Some(v);
                    }
                    (AT_TYPE, Value::Int(v)) => {
                        entry.type_ref = Some((v, a.form != FORM_REF_ADDR));
                    }
                    (AT_FRAME_BASE, Value::Expr(b)) => entry.frame_base = Some(b),
                    (AT_LOCATION, Value::Expr(b)) => entry.location = Some(b),
                    (AT_BYTE_SIZE, Value::Int(v)) => entry.byte_size = Some(v),
                    (AT_ENCODING, Value::Int(v)) => entry.encoding = Some(v),
                    (AT_MEMBER_LOCATION, Value::Int(v)) => entry.member_off = Some(v),
                    (AT_CONST_VALUE, Value::Int(v)) => entry.const_value = Some(v),
                    _ => {}
                }
            }
            if !read {
                break;
            }
            if let Some(n) = &entry.name {
                by_offset.insert(here, n.clone());
            }
            // Only `ref_addr` is section-relative; every other reference
            // form counts from its own unit's start, and a lookup needs the
            // section offset.
            let absolute = |r: Option<(u64, bool)>| {
                r.map(|(v, unit_relative)| {
                    if unit_relative {
                        unit_base.saturating_add(v)
                    } else {
                        v
                    }
                })
            };
            nodes.insert(
                here,
                TypeNode {
                    tag: abbreviation.tag,
                    name: entry.name.clone(),
                    inner: absolute(entry.type_ref),
                    scalar: entry.encoding.zip(entry.byte_size),
                },
            );
            let named_function = abbreviation.tag == TAG_SUBPROGRAM
                && entry.low_pc.is_some()
                && entry.name.is_some();
            if abbreviation.tag == TAG_SUBPROGRAM
                && let Some(low_pc) = entry.low_pc
            {
                match (&entry.name, entry.origin) {
                    (Some(name), _) => {
                        open.push(out.len());
                        unresolved.push((out.len(), absolute(entry.type_ref)));
                        bases.push(
                            entry.frame_base.as_deref().and_then(|expr| {
                                frame_base(expr, i64::try_from(address_size).ok()?)
                            }),
                        );
                        out.push(Subprogram {
                            low_pc,
                            name: name.clone(),
                            parameters: Vec::new(),
                            return_type: None,
                            locals: BTreeMap::new(),
                        });
                    }
                    // A cloned or inlined body names itself by pointing at the
                    // entry it came from, which may not have been read yet.
                    (None, Some(origin)) => pending.push((low_pc, origin)),
                    (None, None) => {}
                }
            } else if abbreviation.tag == TAG_FORMAL_PARAMETER
                && let Some(name) = entry.name.clone()
                && let Some(owner) = open.last().copied()
                && let Some(f) = out.get_mut(owner)
            {
                unresolved_params.push((owner, f.parameters.len(), absolute(entry.type_ref)));
                f.parameters.push(Parameter {
                    name,
                    type_name: None,
                });
            } else if abbreviation.tag == TAG_VARIABLE
                && let (Some(name), Some(expr)) = (&entry.name, &entry.location)
                && let Some(owner) = open.last().copied()
            {
                // The base the offset counts from converts it to the slot
                // the text names: the caller's frame pointer's word above
                // the entry stack, the frame pointer's word under it. The
                // base's `None` and the unconvertible offset both leave the
                // variable unnamed, never guessed onto a slot.
                let word = i64::try_from(address_size).unwrap_or(8);
                let slot = bases
                    .get(owner)
                    .copied()
                    .flatten()
                    .zip(fbreg(expr))
                    .and_then(|(base, off)| match base {
                        FrameBase::Caller => slot_held(off.checked_add(word)?),
                        FrameBase::FramePointer => {
                            frame_slot(i32::try_from(off).ok()?, true, word, 0)
                        }
                    });
                if local_name_ok(name)
                    && let Some(f) = out.get_mut(owner)
                {
                    take_local(&mut f.locals, slot, name);
                }
            } else if matches!(abbreviation.tag, TAG_MEMBER | TAG_ENUMERATOR)
                && let (Some(name), Some(owner)) =
                    (&entry.name, type_scopes.last().copied().flatten())
                && let Some(s) = stated.get_mut(owner)
                && is_ident(name)
            {
                if abbreviation.tag == TAG_MEMBER
                    && let Some(off) = entry.member_off
                    && s.members.len() < FIELDS_MAX
                {
                    s.members
                        .push((name.clone(), off, absolute(entry.type_ref)));
                } else if abbreviation.tag == TAG_ENUMERATOR
                    && let Some(value) = entry.const_value
                    && s.values.len() < ENUM_VALUES_MAX
                {
                    s.values.push((value, name.clone()));
                }
            }
            // A named struct or enum with children opens the scope its
            // members belong to; every other entry with children closes
            // it, so a member of a nested or anonymous type never lands on
            // the type outside it.
            let opened = if matches!(
                abbreviation.tag,
                TAG_STRUCTURE | TAG_CLASS | TAG_UNION | TAG_ENUMERATION
            ) && abbreviation.children
                && let (Some(name), Some(size)) = (&entry.name, entry.byte_size)
                && types.len() + stated.len() < TYPES_MAX
                && check_type_name(name).is_ok()
            {
                stated.push(Stated {
                    name: name.clone(),
                    size,
                    members: Vec::new(),
                    values: Vec::new(),
                    is_enum: abbreviation.tag == TAG_ENUMERATION,
                });
                Some(stated.len() - 1)
            } else {
                None
            };
            if abbreviation.children {
                depth.push(named_function);
                type_scopes.push(opened);
            }
        }
        for (low_pc, origin) in pending {
            if let Some(name) = by_offset.get(&origin) {
                bases.push(None);
                out.push(Subprogram {
                    low_pc,
                    name: name.clone(),
                    parameters: Vec::new(),
                    return_type: None,
                    locals: BTreeMap::new(),
                });
            }
        }
        // The chains resolve now that every entry of the unit is recorded.
        for (index, type_ref) in unresolved {
            if let Some(f) = out.get_mut(index) {
                f.return_type = type_name(&nodes, type_ref, TYPE_DEPTH).filter(|t| t != "void");
            }
        }
        for (owner, slot, type_ref) in unresolved_params {
            if let Some(p) = out.get_mut(owner).and_then(|f| f.parameters.get_mut(slot)) {
                p.type_name = type_name(&nodes, type_ref, TYPE_DEPTH);
            }
        }
        for s in stated {
            if s.is_enum {
                // The builder's own refusals - a name the language spells,
                // a value twice named, one past the width - are the
                // discipline a stated fact meets too.
                if let Ok(ty) = build_enum(&s.name, s.size, &s.values) {
                    types.insert(s.name, ty);
                }
                continue;
            }
            let mut fields: BTreeMap<u64, UserField> = BTreeMap::new();
            for (name, off, type_ref) in s.members {
                if fields.contains_key(&off) {
                    continue;
                }
                if let Some(ty) = type_expr(&nodes, type_ref, TYPE_DEPTH) {
                    fields.insert(off, UserField { name, ty });
                }
            }
            if fields.is_empty() {
                continue;
            }
            types.insert(
                s.name,
                UserType::Struct(UserStruct {
                    size: s.size,
                    fields,
                }),
            );
        }
    }
    out.sort_by(|l, r| l.low_pc.cmp(&r.low_pc).then_with(|| l.name.cmp(&r.name)));
    out.dedup_by(|l, r| l.low_pc == r.low_pc);
    Debug {
        subprograms: out,
        types,
    }
}

/// Finds a debug section by name, or by the shape of its bytes.
///
/// A stripped image loses the long section names, so `.debug_info` arrives as
/// `/19`. The content sniffer names it back, and an exact answer is preferred
/// over one naming two candidates.
///
/// # Arguments
///
/// * `sections` - The image's sections, mapped and file-only alike.
/// * `bytes` - The whole file.
/// * `want` - The section name being looked for.
///
/// # Returns
///
/// The section's bytes, or an empty slice when it is not there.
fn debug_section<'a>(sections: &[&Section], bytes: &'a [u8], want: &str) -> &'a [u8] {
    let body = |s: &Section| -> &'a [u8] {
        let start = usize::try_from(s.file_off.0).unwrap_or(usize::MAX);
        let end = usize::try_from(s.file_off.0.saturating_add(s.file_size)).unwrap_or(usize::MAX);
        bytes.get(start..end.min(bytes.len())).unwrap_or(&[])
    };
    if let Some(s) = sections.iter().find(|s| s.name == want) {
        return body(s);
    }
    let mut fallback: Option<&Section> = None;
    for &s in sections.iter().filter(|s| s.name.starts_with('/')) {
        match crate::headers::sniff_section(body(s)) {
            Some(guess) if guess == want => return body(s),
            Some(guess) if guess.contains(want) && fallback.is_none() => fallback = Some(s),
            _ => {}
        }
    }
    fallback.map_or(&[], body)
}

/// What a program's debug information states.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Debug {
    /// The named functions with addresses, by address.
    pub subprograms: Vec<Subprogram>,
    /// The struct layouts and enum constants, by type name, in the shape
    /// the overlay's user types take. Facts the file states, offered as
    /// proposals: nothing applies them, because the overlay is the agent's
    /// own record and a file's fact is not the agent's choice.
    pub types: BTreeMap<String, UserType>,
}

/// Reads what a program's debug information states.
///
/// An ELF's `.debug_*` sections carry no address (no segment maps them),
/// so the loader keeps them out of the mapped table and hands them over as
/// `unmapped`: a `-g` build's DWARF lives there, and only a few producers
/// give it an address.
///
/// # Arguments
///
/// * `sections` - The image's mapped sections, named or stripped.
/// * `unmapped` - Sections the file holds that no segment maps.
/// * `bytes` - The whole file.
///
/// # Returns
///
/// The named functions and the stated types. Empty when the program
/// carries no debug information.
#[must_use]
pub fn read(sections: &[Section], unmapped: &[Section], bytes: &[u8]) -> Debug {
    let all: Vec<&Section> = sections.iter().chain(unmapped).collect();
    let info = debug_section(&all, bytes, ".debug_info");
    let abbrev = debug_section(&all, bytes, ".debug_abbrev");
    if info.is_empty() || abbrev.is_empty() {
        return Debug::default();
    }
    let strings = Strings {
        text: debug_section(&all, bytes, ".debug_str"),
        lines: debug_section(&all, bytes, ".debug_line_str"),
    };
    read_in(info, abbrev, &strings)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Strings, read_in};

    /// Builds an abbreviation table declaring a function and a parameter.
    fn abbrev() -> Vec<u8> {
        vec![
            // code 1: DW_TAG_subprogram, has children, name (string), low_pc (addr)
            0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x00, 0x00,
            // code 2: DW_TAG_formal_parameter, no children, name (string)
            0x02, 0x05, 0x00, 0x03, 0x08, 0x00, 0x00, // end of table
            0x00,
        ]
    }

    /// Wraps `dies` in a DWARF 5 unit header.
    fn unit(dies: &[u8]) -> Vec<u8> {
        let mut body: Vec<u8> = Vec::new();
        body.extend_from_slice(&5u16.to_le_bytes()); // version
        body.push(0x01); // DW_UT_compile
        body.push(8); // address size
        body.extend_from_slice(&0u32.to_le_bytes()); // abbreviation offset
        body.extend_from_slice(dies);
        let mut out = u32::try_from(body.len())
            .expect("fits")
            .to_le_bytes()
            .to_vec();
        out.extend_from_slice(&body);
        out
    }

    /// A named function with its parameters is read out of a unit.
    #[test]
    fn a_named_function_is_read() {
        let mut dies: Vec<u8> = Vec::new();
        dies.push(0x01); // the subprogram
        dies.extend_from_slice(b"main\0");
        dies.extend_from_slice(&0x0001_4000u64.to_le_bytes());
        dies.push(0x02); // a parameter
        dies.extend_from_slice(b"argc\0");
        dies.push(0x02); // another
        dies.extend_from_slice(b"argv\0");
        dies.push(0x00); // end of the subprogram's children
        let info = unit(&dies);
        let strings = Strings {
            text: &[],
            lines: &[],
        };
        let found = read_in(&info, &abbrev(), &strings).subprograms;
        assert_eq!(found.len(), 1, "{found:?}");
        assert_eq!(found[0].low_pc, 0x0001_4000);
        assert_eq!(found[0].name, "main");
        let names: Vec<&str> = found[0]
            .parameters
            .iter()
            .map(|p| p.name.as_str())
            .collect();
        assert_eq!(names, vec!["argc", "argv"]);
    }

    /// A name held in `.debug_str` is resolved through the offset.
    #[test]
    fn a_name_resolves_through_the_string_section() {
        // code 1: subprogram, no children, name (strp), low_pc (addr)
        let abbrev: Vec<u8> = vec![0x01, 0x2e, 0x00, 0x03, 0x0e, 0x11, 0x01, 0x00, 0x00, 0x00];
        let mut dies: Vec<u8> = vec![0x01];
        dies.extend_from_slice(&4u32.to_le_bytes()); // offset into .debug_str
        dies.extend_from_slice(&0x2000u64.to_le_bytes());
        let info = unit(&dies);
        let strings = Strings {
            text: b"one\0resolved\0",
            lines: &[],
        };
        let found = read_in(&info, &abbrev, &strings).subprograms;
        assert_eq!(found.len(), 1, "{found:?}");
        assert_eq!(found[0].name, "resolved");
    }

    /// A type is read by following the chain of entries that build it.
    ///
    /// A parameter points at a pointer, which points at a const, which points
    /// at a base type, and only the whole chain says `const char *`.
    #[test]
    fn a_type_chain_reads_as_c_source() {
        // code 1: subprogram, children, name (string), low_pc (addr), type (ref4)
        // code 2: formal_parameter, no children, name (string), type (ref4)
        // code 3: pointer_type, no children, type (ref4)
        // code 4: const_type, no children, type (ref4)
        // code 5: base_type, no children, name (string)
        let abbrev: Vec<u8> = vec![
            0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x49, 0x13, 0x00, 0x00, //
            0x02, 0x05, 0x00, 0x03, 0x08, 0x49, 0x13, 0x00, 0x00, //
            0x03, 0x0f, 0x00, 0x49, 0x13, 0x00, 0x00, //
            0x04, 0x26, 0x00, 0x49, 0x13, 0x00, 0x00, //
            0x05, 0x24, 0x00, 0x03, 0x08, 0x00, 0x00, //
            0x00,
        ];
        // The unit body starts at offset 12, so the entries sit at known
        // unit-relative offsets, which is what a ref4 counts from.
        let mut dies: Vec<u8> = Vec::new();
        dies.push(0x01); // subprogram at 12
        dies.extend_from_slice(b"f\0");
        dies.extend_from_slice(&0x1000u64.to_le_bytes());
        dies.extend_from_slice(&45u32.to_le_bytes()); // returns the base type
        let param_at = 12 + dies.len();
        dies.push(0x02); // parameter
        dies.extend_from_slice(b"s\0");
        dies.extend_from_slice(&35u32.to_le_bytes()); // points at the pointer
        dies.push(0x00); // end of children
        let pointer_at = 12 + dies.len();
        dies.push(0x03);
        dies.extend_from_slice(&40u32.to_le_bytes()); // points at the const
        let const_at = 12 + dies.len();
        dies.push(0x04);
        dies.extend_from_slice(&45u32.to_le_bytes()); // points at the base type
        let base_at = 12 + dies.len();
        dies.push(0x05);
        dies.extend_from_slice(b"char\0");
        assert_eq!(
            (param_at, pointer_at, const_at, base_at),
            (27, 35, 40, 45),
            "the offsets the references assume"
        );
        let info = unit(&dies);
        let strings = Strings {
            text: &[],
            lines: &[],
        };
        let found = read_in(&info, &abbrev, &strings).subprograms;
        assert_eq!(found.len(), 1, "{found:?}");
        assert_eq!(found[0].return_type.as_deref(), Some("char"));
        assert_eq!(found[0].parameters.len(), 1);
        assert_eq!(
            found[0].parameters[0].type_name.as_deref(),
            Some("const char *")
        );
    }

    /// Builds an abbreviation table declaring subprograms that state a
    /// frame base, variables that state a location, and a lexical block.
    fn locals_abbrev() -> Vec<u8> {
        vec![
            // code 1: DW_TAG_subprogram, has children, name (string),
            // low_pc (addr), frame_base (exprloc)
            0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x70, 0x09, 0x00, 0x00,
            // code 2: DW_TAG_variable, no children, name (string),
            // location (exprloc)
            0x02, 0x34, 0x00, 0x03, 0x08, 0x02, 0x09, 0x00, 0x00,
            // code 3: DW_TAG_lexical_block, has children, no attributes
            0x03, 0x0b, 0x01, 0x00, 0x00, // end of table
            0x00,
        ]
    }

    /// Appends a variable's entry: code, name, then an exprloc.
    fn variable(dies: &mut Vec<u8>, code: u8, name: &str, expr: &[u8]) {
        dies.push(code);
        dies.extend_from_slice(name.as_bytes());
        dies.push(0);
        dies.push(u8::try_from(expr.len()).expect("fits"));
        dies.extend_from_slice(expr);
    }

    /// A frame-relative variable lands on the slot its subprogram's frame
    /// base states, whatever base the compiler chose.
    ///
    /// The caller's frame base sits a word above the entry stack pointer,
    /// the frame pointer's a word under it, so the same `DW_OP_fbreg`
    /// offset names a different slot under each. A variable inside a
    /// lexical block still lives in its function's frame, and a name the
    /// text synthesizes for itself, a slot past the span a frame holds, the
    /// return address's own slot, a location no whole `DW_OP_fbreg` states,
    /// another local's slot, and a frame base this reader does not reduce
    /// all leave the map without their name.
    #[test]
    fn fbreg_locals_land_by_their_frame_base() {
        let mut dies: Vec<u8> = Vec::new();
        // subprogram "cfa_fn": frame_base = DW_OP_call_frame_cfa
        dies.push(0x01);
        dies.extend_from_slice(b"cfa_fn\0");
        dies.extend_from_slice(&0x1000u64.to_le_bytes());
        dies.push(1);
        dies.extend_from_slice(&[0x9c]); // DW_OP_call_frame_cfa
        variable(&mut dies, 0x02, "a", &[0x91, 0x68]); // fbreg -0x18
        dies.push(0x03); // a lexical block, whose locals keep the frame
        variable(&mut dies, 0x02, "b", &[0x91, 0x70]); // fbreg -0x10
        dies.push(0x00); // end of the block's children
        variable(&mut dies, 0x02, "local_8", &[0x91, 0x60]); // name refused
        variable(&mut dies, 0x02, "at_zero", &[0x91, 0x78]); // the retaddr
        variable(&mut dies, 0x02, "far", &[0x91, 0x80, 0x80, 0x04]); // past span
        variable(&mut dies, 0x02, "reg", &[0x50]); // not an fbreg
        variable(&mut dies, 0x02, "empty", &[]); // no location stated
        variable(&mut dies, 0x02, "again", &[0x91, 0x68]); // a's own slot
        dies.push(0x00); // end of the subprogram's children
        // subprogram "bp_fn": frame_base = DW_OP_reg6 (rbp)
        dies.push(0x01);
        dies.extend_from_slice(b"bp_fn\0");
        dies.extend_from_slice(&0x2000u64.to_le_bytes());
        dies.push(1);
        dies.extend_from_slice(&[0x56]); // DW_OP_reg6
        variable(&mut dies, 0x02, "c", &[0x91, 0x70]); // fbreg -0x10
        dies.push(0x00);
        // subprogram "odd_fn": a frame base no slot crosses to
        dies.push(0x01);
        dies.extend_from_slice(b"odd_fn\0");
        dies.extend_from_slice(&0x3000u64.to_le_bytes());
        dies.push(2);
        dies.extend_from_slice(&[0x77, 0x00]); // DW_OP_breg7 +0
        variable(&mut dies, 0x02, "h", &[0x91, 0x70]);
        dies.push(0x00);
        let info = unit(&dies);
        let strings = Strings {
            text: &[],
            lines: &[],
        };
        let found = read_in(&info, &locals_abbrev(), &strings).subprograms;
        assert_eq!(found.len(), 3, "{found:?}");
        let locals = |name: &str| {
            found
                .iter()
                .find(|f| f.name == name)
                .unwrap_or_else(|| panic!("no {name}"))
                .locals
                .clone()
        };
        // The caller's base is a word above entry: fbreg -0x18 is slot
        // -0x10; the frame pointer's is a word under: fbreg -0x10 is slot
        // -0x18.
        assert_eq!(
            locals("cfa_fn"),
            [(-0x10, "a".to_owned()), (-0x08, "b".to_owned())]
                .into_iter()
                .collect::<std::collections::BTreeMap<_, _>>()
        );
        assert_eq!(
            locals("bp_fn"),
            [(-0x18i64, "c".to_owned())].into_iter().collect()
        );
        assert!(locals("odd_fn").is_empty(), "an unread base names nothing");
    }

    /// A 32-bit unit's frame pointer is `ebp`, register 5, and its caller
    /// base crosses by the four-byte word.
    #[test]
    fn a_32_bit_frame_pointer_is_ebp() {
        // code 1: subprogram, children, name (string), low_pc (addr4),
        // frame_base (exprloc); code 2: variable, name, location (exprloc)
        let abbrev: Vec<u8> = vec![
            0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x70, 0x09, 0x00, 0x00, //
            0x02, 0x34, 0x00, 0x03, 0x08, 0x02, 0x09, 0x00, 0x00, //
            0x00,
        ];
        let mut body: Vec<u8> = Vec::new();
        body.extend_from_slice(&5u16.to_le_bytes()); // version
        body.push(0x01); // DW_UT_compile
        body.push(4); // address size
        body.extend_from_slice(&0u32.to_le_bytes()); // abbreviation offset
        body.push(0x01);
        body.extend_from_slice(b"fn32\0");
        body.extend_from_slice(&0x4000u32.to_le_bytes());
        body.push(1);
        body.extend_from_slice(&[0x55]); // DW_OP_reg5 (ebp)
        variable(&mut body, 0x02, "d", &[0x91, 0x70]); // fbreg -0x10
        body.push(0x00);
        let mut info = u32::try_from(body.len())
            .expect("fits")
            .to_le_bytes()
            .to_vec();
        info.extend_from_slice(&body);
        let strings = Strings {
            text: &[],
            lines: &[],
        };
        let found = read_in(&info, &abbrev, &strings).subprograms;
        assert_eq!(found.len(), 1, "{found:?}");
        // ebp - 0x10 is the entry stack a four-byte word under it, slot
        // -0x14.
        assert_eq!(
            found[0].locals,
            [(-0x14i64, "d".to_owned())].into_iter().collect()
        );
    }

    /// Builds an abbreviation table declaring the entries a stated type
    /// walks: structures, members, base types, pointers, enumerations and
    /// enumerators.
    fn types_abbrev() -> Vec<u8> {
        vec![
            // code 1: DW_TAG_structure_type, has children, name (string),
            // byte_size (data1)
            0x01, 0x13, 0x01, 0x03, 0x08, 0x0b, 0x0b, 0x00, 0x00,
            // code 2: DW_TAG_member, no children, name (string),
            // data_member_location (data1), type (ref4)
            0x02, 0x0d, 0x00, 0x03, 0x08, 0x38, 0x0b, 0x49, 0x13, 0x00, 0x00,
            // code 3: DW_TAG_base_type, no children, name (string),
            // byte_size (data1), encoding (data1)
            0x03, 0x24, 0x00, 0x03, 0x08, 0x0b, 0x0b, 0x3e, 0x0b, 0x00, 0x00,
            // code 4: DW_TAG_pointer_type, no children, type (ref4)
            0x04, 0x0f, 0x00, 0x49, 0x13, 0x00, 0x00,
            // code 5: DW_TAG_enumeration_type, has children, name (string),
            // byte_size (data1)
            0x05, 0x04, 0x01, 0x03, 0x08, 0x0b, 0x0b, 0x00, 0x00,
            // code 6: DW_TAG_enumerator, no children, name (string),
            // const_value (data1)
            0x06, 0x28, 0x00, 0x03, 0x08, 0x1c, 0x0b, 0x00, 0x00,
            // code 7: DW_TAG_structure_type, has children, byte_size (data1)
            // alone: the anonymous one
            0x07, 0x13, 0x01, 0x0b, 0x0b, 0x00, 0x00, // end of table
            0x00,
        ]
    }

    /// Appends a `DW_FORM_string` name to the entries under construction.
    fn named(dies: &mut Vec<u8>, name: &str) {
        dies.extend_from_slice(name.as_bytes());
        dies.push(0);
    }

    /// A struct's members and an enum's constants land as the types the
    /// user-type language spells.
    ///
    /// A member resolves through its whole chain - a base type by its
    /// encoding, a pointer to what it points at, a named enum by its name -
    /// while one that repeats another's offset, one whose reference points
    /// at nothing, and one inside an anonymous struct contribute nothing,
    /// because none states a field an agent could state back.
    #[test]
    fn struct_members_and_enum_constants_land_as_types() {
        use crate::analysis::utypes::{TypeExpr, UserStruct, UserType};
        use std::collections::BTreeMap;
        let mut dies: Vec<u8> = Vec::new();
        // The unit body starts at 12, which is what a ref4 counts from.
        let die_at = |dies: &[u8]| u32::try_from(12 + dies.len()).expect("fits");
        let u32_at = die_at(&dies);
        dies.push(0x03);
        named(&mut dies, "unsigned int");
        dies.push(4); // byte size
        dies.push(0x07); // DW_ATE_unsigned
        let char_at = die_at(&dies);
        dies.push(0x03);
        named(&mut dies, "char");
        dies.push(1);
        dies.push(0x06); // DW_ATE_signed_char
        let ptr_at = die_at(&dies);
        dies.push(0x04);
        dies.extend_from_slice(&char_at.to_le_bytes());
        let enum_at = die_at(&dies);
        dies.push(0x05);
        named(&mut dies, "E");
        dies.push(4); // byte size
        for (name, value) in [("A", 0u8), ("B", 3u8)] {
            dies.push(0x06);
            named(&mut dies, name);
            dies.push(value);
        }
        dies.push(0x00); // end of the enumeration's children
        dies.push(0x01);
        named(&mut dies, "Point");
        dies.push(16); // byte size
        for (name, off, ty) in [
            ("x", 0u8, u32_at),
            ("text", 8, ptr_at),
            ("kind", 12, enum_at),
            ("dup", 0, u32_at),
            ("lost", 20, u32_at + 1),
        ] {
            dies.push(0x02);
            named(&mut dies, name);
            dies.push(off);
            dies.extend_from_slice(&ty.to_le_bytes());
        }
        // An anonymous struct inside `Point`: its member states a field of
        // a type nothing names, and lands nowhere.
        dies.push(0x07);
        dies.push(4);
        dies.push(0x02);
        named(&mut dies, "inner");
        dies.push(0);
        dies.extend_from_slice(&u32_at.to_le_bytes());
        dies.push(0x00); // end of the anonymous struct's children
        dies.push(0x00); // end of Point's children
        let info = unit(&dies);
        let strings = Strings {
            text: &[],
            lines: &[],
        };
        let read = read_in(&info, &types_abbrev(), &strings);
        assert!(read.subprograms.is_empty());
        let e = read.types.get("E").expect("the enum is stated");
        assert_eq!(
            e,
            &UserType::Enum(crate::analysis::utypes::UserEnum {
                size: 4,
                values: vec![(0, "A".to_owned()), (3, "B".to_owned())],
            })
        );
        let point = read.types.get("Point").expect("the struct is stated");
        let UserStruct { size, fields } = match point {
            UserType::Struct(s) => s,
            other => panic!("Point is not a struct: {other:?}"),
        };
        assert_eq!(*size, 16);
        assert_eq!(
            fields,
            &BTreeMap::from([
                (
                    0u64,
                    crate::analysis::utypes::UserField {
                        name: "x".to_owned(),
                        ty: TypeExpr::U32,
                    }
                ),
                (
                    8,
                    crate::analysis::utypes::UserField {
                        name: "text".to_owned(),
                        ty: TypeExpr::Ptr(Box::new(TypeExpr::Char)),
                    }
                ),
                (
                    12,
                    crate::analysis::utypes::UserField {
                        name: "kind".to_owned(),
                        ty: TypeExpr::Named("E".to_owned()),
                    }
                ),
            ])
        );
    }

    /// An enum a value names twice is refused whole, and one whose width
    /// the language does not spell lands not at all.
    #[test]
    fn enums_the_language_cannot_state_land_nowhere() {
        let mut dies: Vec<u8> = Vec::new();
        for (name, size) in [("Twice", 4u8), ("Narrow", 1u8)] {
            dies.push(0x05);
            named(&mut dies, name);
            dies.push(size);
            for (member, value) in [("A", 0u8), ("Also", 0u8)] {
                dies.push(0x06);
                named(&mut dies, member);
                dies.push(value);
            }
            dies.push(0x00);
        }
        let info = unit(&dies);
        let strings = Strings {
            text: &[],
            lines: &[],
        };
        let read = read_in(&info, &types_abbrev(), &strings);
        assert!(read.types.is_empty(), "{:?}", read.types.keys());
    }

    /// Arbitrary bytes are read without panicking, and name nothing.
    ///
    /// A reader of a rebuilt or damaged image is handed whatever the file
    /// holds, so every path out of it has to be a `None`, not a panic.
    #[test]
    fn arbitrary_bytes_name_nothing() {
        let strings = Strings {
            text: &[],
            lines: &[],
        };
        assert!(read_in(&[], &[], &strings).subprograms.is_empty());
        let noise: Vec<u8> = (0..4096u32).map(|k| (k * 31 % 253) as u8).collect();
        let _ = read_in(&noise, &noise, &strings);
        let truncated = unit(&[0x01]);
        let _ = read_in(&truncated, &abbrev(), &strings);
        for cut in 0..truncated.len() {
            let _ = read_in(&truncated[..cut], &abbrev(), &strings);
        }
    }

    /// A unit whose stated length runs to the top of the offset space
    /// names nothing and ends the walk, rather than adding its offset to
    /// the minimum-unit bound and overflowing.
    #[test]
    fn a_huge_stated_length_ends_the_walk() {
        // The 64-bit escape, then a length whose end offset lands on
        // `usize::MAX`, then the whole version-5 header the reader wants.
        let mut info = Vec::new();
        info.extend_from_slice(&u32::MAX.to_le_bytes());
        info.extend_from_slice(&(u64::MAX - 12).to_le_bytes());
        info.extend_from_slice(&5u16.to_le_bytes());
        info.push(0x01);
        info.push(8);
        info.extend_from_slice(&[0; 8]);
        let strings = Strings {
            text: &[],
            lines: &[],
        };
        assert!(read_in(&info, &abbrev(), &strings).subprograms.is_empty());
    }
}
