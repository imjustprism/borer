//! .NET metadata: the CLR header a managed PE carries and the ECMA-335
//! tables it points at.
//!
//! A .NET assembly is a PE whose one import is `mscoree!_CorExeMain` and
//! whose code is IL, which no x86 reader makes sense of. What it does carry
//! is metadata naming everything: every type and method it defines (each
//! method with the address of its body), every external member it uses,
//! every native function it calls through P/Invoke, and every string
//! literal its code loads. This reads that triage, not the IL: the CLR
//! header (`IMAGE_COR20_HEADER`, data directory 14), the metadata root and
//! its streams (`#~` or `#-`, `#Strings`, `#US`, `#GUID`, `#Blob`), the
//! table stream's row counts and index widths, and the rows of `Module`,
//! `TypeRef`, `TypeDef`, `MethodPtr`, `MethodDef`, `MemberRef`, `ModuleRef`,
//! `ImplMap`, `Assembly`, `AssemblyRef` and `NestedClass`.
//!
//! The bytes are untrusted. A stream that runs past the metadata, a table
//! stream whose row counts run past its end, a heap index past its heap or
//! a coded index naming no table refuses the metadata whole, with the
//! reason; nothing panics, and the counts read are capped. A method's name
//! goes on its body's address as a symbol: a data symbol for an IL body,
//! which the engine does not decompile, and a function for a native body
//! in a mixed-mode image, which the engine analyzes as it does any code.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::num::{from_usize, saturating_usize};
use crate::program::{Program, Symbol, SymbolKind};
use crate::strings::{Encoding, StringHit};
use crate::text::one_line;

/// Bytes of the CLR header (`IMAGE_COR20_HEADER`).
const COR20_LEN: usize = 72;

/// The metadata root's signature, `BSJB` read as a little-endian word.
const BSJB: u32 = 0x424a_5342;

/// Most bytes of metadata read, whatever the header states.
const META_MAX: usize = 1 << 30;

/// Longest name read out of `#Strings`, in bytes; a longer one is cut.
const NAME_MAX: usize = 1024;

/// Most rows read from one table; the counts say when more were there.
const ROWS_MAX: u32 = 1 << 20;

/// Most user strings read out of `#US`.
const STRINGS_MAX: usize = 1 << 18;

/// Longest user string kept whole, in UTF-16 code units.
const STRING_UNITS_MAX: usize = 4096;

/// Longest user string a row of the strings listing shows, in characters.
const DISPLAY_MAX: usize = 200;

/// Deepest nesting followed for a nested type's name.
const NEST_MAX: usize = 16;

/// Rows one read of the `borer://clr` listing shows.
pub const CLR_PAGE: usize = 200;

/// `COMIMAGE_FLAGS_NATIVE_ENTRYPOINT`: the entry is a native RVA, not a
/// method token.
const NATIVE_ENTRYPOINT: u32 = 0x10;

/// The `COMIMAGE_FLAGS_*` bits a summary names, with their words.
const FLAG_WORDS: [(u32, &str); 7] = [
    (0x1, "ilonly"),
    (0x2, "32bitreq"),
    (0x4, "il-library"),
    (0x8, "strongname"),
    (NATIVE_ENTRYPOINT, "native-entry"),
    (0x1_0000, "trackdebugdata"),
    (0x2_0000, "32bitpref"),
];

/// The `ImplFlags` bits of a method saying what its body is
/// (`MethodImplAttributes.CodeTypeMask`).
const CODE_TYPE: u16 = 0x3;

/// The table stream's `HeapSizes` bit saying an extra word follows the
/// row counts (`#-` streams).
const EXTRA_DATA: u8 = 0x40;

/// `Module`, the first table; the numbers follow ECMA-335 II.22.
const MODULE: u8 = 0x00;
/// `TypeRef`.
const TYPE_REF: u8 = 0x01;
/// `TypeDef`.
const TYPE_DEF: u8 = 0x02;
/// `Field`.
const FIELD: u8 = 0x04;
/// `MethodPtr`, the indirection an uncompressed (`#-`) stream lists
/// methods through.
const METHOD_PTR: u8 = 0x05;
/// `MethodDef`.
const METHOD_DEF: u8 = 0x06;
/// `Param`.
const PARAM: u8 = 0x08;
/// `InterfaceImpl`.
const INTERFACE_IMPL: u8 = 0x09;
/// `MemberRef`.
const MEMBER_REF: u8 = 0x0a;
/// `DeclSecurity`.
const DECL_SECURITY: u8 = 0x0e;
/// `StandAloneSig`.
const STAND_ALONE_SIG: u8 = 0x11;
/// `Event`.
const EVENT: u8 = 0x14;
/// `Property`.
const PROPERTY: u8 = 0x17;
/// `ModuleRef`.
const MODULE_REF: u8 = 0x1a;
/// `TypeSpec`.
const TYPE_SPEC: u8 = 0x1b;
/// `ImplMap`.
const IMPL_MAP: u8 = 0x1c;
/// `Assembly`.
const ASSEMBLY: u8 = 0x20;
/// `AssemblyRef`.
const ASSEMBLY_REF: u8 = 0x23;
/// `File`.
const FILE: u8 = 0x26;
/// `ExportedType`.
const EXPORTED_TYPE: u8 = 0x27;
/// `ManifestResource`.
const MANIFEST_RESOURCE: u8 = 0x28;
/// `NestedClass`.
const NESTED_CLASS: u8 = 0x29;
/// `GenericParam`.
const GENERIC_PARAM: u8 = 0x2a;
/// `MethodSpec`.
const METHOD_SPEC: u8 = 0x2b;
/// `GenericParamConstraint`.
const GENERIC_PARAM_CONSTRAINT: u8 = 0x2c;
/// The tables ECMA-335 defines, `0x00` to `0x2c`; a later one (a portable
/// PDB's) follows all of them in the stream, so none of these moves.
const TABLES: usize = 0x2d;
/// A coded index's tag that names no table.
const NO_TABLE: u8 = 0xff;

/// A coded index: a row of one of a few tables, the table in its low bits
/// (ECMA-335 II.24.2.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Coded {
    /// `TypeDef`, `TypeRef` or `TypeSpec`.
    TypeDefOrRef,
    /// `Field`, `Param` or `Property`.
    HasConstant,
    /// Any of the 22 tables an attribute can sit on.
    HasCustomAttribute,
    /// `Field` or `Param`.
    HasFieldMarshal,
    /// `TypeDef`, `MethodDef` or `Assembly`.
    HasDeclSecurity,
    /// `TypeDef`, `TypeRef`, `ModuleRef`, `MethodDef` or `TypeSpec`.
    MemberRefParent,
    /// `Event` or `Property`.
    HasSemantics,
    /// `MethodDef` or `MemberRef`.
    MethodDefOrRef,
    /// `Field` or `MethodDef`.
    MemberForwarded,
    /// `File`, `AssemblyRef` or `ExportedType`.
    Implementation,
    /// `MethodDef` or `MemberRef`, at tags 2 and 3.
    CustomAttributeType,
    /// `Module`, `ModuleRef`, `AssemblyRef` or `TypeRef`.
    ResolutionScope,
    /// `TypeDef` or `MethodDef`.
    TypeOrMethodDef,
}

impl Coded {
    /// The tables the tag selects, by tag; [`NO_TABLE`] for an unused tag.
    fn tables(self) -> &'static [u8] {
        match self {
            Self::TypeDefOrRef => &[TYPE_DEF, TYPE_REF, TYPE_SPEC],
            Self::HasConstant => &[FIELD, PARAM, PROPERTY],
            Self::HasCustomAttribute => &[
                METHOD_DEF,
                FIELD,
                TYPE_REF,
                TYPE_DEF,
                PARAM,
                INTERFACE_IMPL,
                MEMBER_REF,
                MODULE,
                DECL_SECURITY,
                PROPERTY,
                EVENT,
                STAND_ALONE_SIG,
                MODULE_REF,
                TYPE_SPEC,
                ASSEMBLY,
                ASSEMBLY_REF,
                FILE,
                EXPORTED_TYPE,
                MANIFEST_RESOURCE,
                GENERIC_PARAM,
                GENERIC_PARAM_CONSTRAINT,
                METHOD_SPEC,
            ],
            Self::HasFieldMarshal => &[FIELD, PARAM],
            Self::HasDeclSecurity => &[TYPE_DEF, METHOD_DEF, ASSEMBLY],
            Self::MemberRefParent => &[TYPE_DEF, TYPE_REF, MODULE_REF, METHOD_DEF, TYPE_SPEC],
            Self::HasSemantics => &[EVENT, PROPERTY],
            Self::MethodDefOrRef => &[METHOD_DEF, MEMBER_REF],
            Self::CustomAttributeType => &[NO_TABLE, NO_TABLE, METHOD_DEF, MEMBER_REF, NO_TABLE],
            Self::MemberForwarded => &[FIELD, METHOD_DEF],
            Self::Implementation => &[FILE, ASSEMBLY_REF, EXPORTED_TYPE],
            Self::ResolutionScope => &[MODULE, MODULE_REF, ASSEMBLY_REF, TYPE_REF],
            Self::TypeOrMethodDef => &[TYPE_DEF, METHOD_DEF],
        }
    }

    /// Bits of the index the tag takes.
    fn bits(self) -> u32 {
        match self {
            Self::HasFieldMarshal
            | Self::HasSemantics
            | Self::MethodDefOrRef
            | Self::MemberForwarded
            | Self::TypeOrMethodDef => 1,
            Self::TypeDefOrRef
            | Self::HasConstant
            | Self::HasDeclSecurity
            | Self::Implementation
            | Self::ResolutionScope => 2,
            Self::MemberRefParent | Self::CustomAttributeType => 3,
            Self::HasCustomAttribute => 5,
        }
    }

    /// Splits an index into its table and its one-based row.
    ///
    /// # Arguments
    ///
    /// * `v` - The index as the cell holds it.
    ///
    /// # Returns
    ///
    /// The table and the row, the row `0` for a null index; `None` for a
    /// tag naming no table.
    fn split(self, v: u32) -> Option<(u8, u32)> {
        let tag = v & ((1 << self.bits()) - 1);
        let table = *self.tables().get(saturating_usize(u64::from(tag)))?;
        (table != NO_TABLE).then_some((table, v >> self.bits()))
    }
}

/// What one column of a table holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Col {
    /// A two-byte constant.
    U16,
    /// A four-byte constant.
    U32,
    /// An index into `#Strings`.
    Str,
    /// An index into `#GUID`.
    Guid,
    /// An index into `#Blob`.
    Blob,
    /// A row of one table.
    Row(u8),
    /// A row of one of a few tables ([`Coded`]).
    Code(Coded),
}

/// Every ECMA-335 table's name and columns, by table number (II.22). The
/// `Constant` table's one-byte type and its pad read as one `U16`.
const SCHEMAS: [(&str, &[Col]); TABLES] = {
    use Coded as C;
    use Col::{Blob, Code, Guid, Row, Str, U16, U32};
    [
        ("Module", &[U16, Str, Guid, Guid, Guid]),
        ("TypeRef", &[Code(C::ResolutionScope), Str, Str]),
        (
            "TypeDef",
            &[
                U32,
                Str,
                Str,
                Code(C::TypeDefOrRef),
                Row(FIELD),
                Row(METHOD_DEF),
            ],
        ),
        ("FieldPtr", &[Row(FIELD)]),
        ("Field", &[U16, Str, Blob]),
        ("MethodPtr", &[Row(METHOD_DEF)]),
        ("MethodDef", &[U32, U16, U16, Str, Blob, Row(PARAM)]),
        ("ParamPtr", &[Row(PARAM)]),
        ("Param", &[U16, U16, Str]),
        ("InterfaceImpl", &[Row(TYPE_DEF), Code(C::TypeDefOrRef)]),
        ("MemberRef", &[Code(C::MemberRefParent), Str, Blob]),
        ("Constant", &[U16, Code(C::HasConstant), Blob]),
        (
            "CustomAttribute",
            &[
                Code(C::HasCustomAttribute),
                Code(C::CustomAttributeType),
                Blob,
            ],
        ),
        ("FieldMarshal", &[Code(C::HasFieldMarshal), Blob]),
        ("DeclSecurity", &[U16, Code(C::HasDeclSecurity), Blob]),
        ("ClassLayout", &[U16, U32, Row(TYPE_DEF)]),
        ("FieldLayout", &[U32, Row(FIELD)]),
        ("StandAloneSig", &[Blob]),
        ("EventMap", &[Row(TYPE_DEF), Row(EVENT)]),
        ("EventPtr", &[Row(EVENT)]),
        ("Event", &[U16, Str, Code(C::TypeDefOrRef)]),
        ("PropertyMap", &[Row(TYPE_DEF), Row(PROPERTY)]),
        ("PropertyPtr", &[Row(PROPERTY)]),
        ("Property", &[U16, Str, Blob]),
        (
            "MethodSemantics",
            &[U16, Row(METHOD_DEF), Code(C::HasSemantics)],
        ),
        (
            "MethodImpl",
            &[
                Row(TYPE_DEF),
                Code(C::MethodDefOrRef),
                Code(C::MethodDefOrRef),
            ],
        ),
        ("ModuleRef", &[Str]),
        ("TypeSpec", &[Blob]),
        (
            "ImplMap",
            &[U16, Code(C::MemberForwarded), Str, Row(MODULE_REF)],
        ),
        ("FieldRVA", &[U32, Row(FIELD)]),
        ("EncLog", &[U32, U32]),
        ("EncMap", &[U32]),
        ("Assembly", &[U32, U16, U16, U16, U16, U32, Blob, Str, Str]),
        ("AssemblyProcessor", &[U32]),
        ("AssemblyOS", &[U32, U32, U32]),
        (
            "AssemblyRef",
            &[U16, U16, U16, U16, U32, Blob, Str, Str, Blob],
        ),
        ("AssemblyRefProcessor", &[U32, Row(ASSEMBLY_REF)]),
        ("AssemblyRefOS", &[U32, U32, U32, Row(ASSEMBLY_REF)]),
        ("File", &[U32, Str, Blob]),
        (
            "ExportedType",
            &[U32, U32, Str, Str, Code(C::Implementation)],
        ),
        (
            "ManifestResource",
            &[U32, U32, Str, Code(C::Implementation)],
        ),
        ("NestedClass", &[Row(TYPE_DEF), Row(TYPE_DEF)]),
        ("GenericParam", &[U16, U16, Code(C::TypeOrMethodDef), Str]),
        ("MethodSpec", &[Code(C::MethodDefOrRef), Blob]),
        (
            "GenericParamConstraint",
            &[Row(GENERIC_PARAM), Code(C::TypeDefOrRef)],
        ),
    ]
};

/// What a method's body is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Body {
    /// IL, which the runtime compiles and borer does not decompile.
    Il,
    /// Native code in the image (a mixed-mode assembly), analyzed as any
    /// other code is.
    Native,
    /// Code the runtime supplies (`OPTIL` or `Runtime`).
    Runtime,
    /// No body in the image: abstract, `extern`, or a P/Invoke.
    None,
}

impl Body {
    /// The word a row prints.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Self::Il => "il",
            Self::Native => "native",
            Self::Runtime => "runtime",
            Self::None => "no-body",
        }
    }
}

/// One defined type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDef {
    /// Its `TypeDef` token, `0x02000000` plus its row.
    pub token: u32,
    /// Its full name: `Namespace.Name`, a nested type as `Outer/Inner`.
    pub name: String,
    /// How many of [`Clr::methods`] it owns.
    pub methods: usize,
}

/// One defined method.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Method {
    /// Its `MethodDef` token, `0x06000000` plus its row.
    pub token: u32,
    /// Its full name, `Namespace.Type::Name`.
    pub name: String,
    /// Its body's RVA, `0` for none.
    pub rva: u32,
    /// What its body is.
    pub body: Body,
}

/// One P/Invoke: a method the runtime binds to a native export.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PInvoke {
    /// The method's `MethodDef` token.
    pub token: u32,
    /// The method's full name, or `?` where the row names a field.
    pub method: String,
    /// The DLL, as its `ModuleRef` names it.
    pub dll: String,
    /// The export, by name or `#ordinal`.
    pub entry: String,
}

/// One external member the code uses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemberRef {
    /// Its `MemberRef` token, `0x0a000000` plus its row.
    pub token: u32,
    /// `Namespace.Type::Member`.
    pub name: String,
    /// Where its type comes from: an assembly's or a module's name, or `-`.
    pub scope: String,
}

/// One referenced assembly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssemblyRef {
    /// Its `AssemblyRef` token, `0x23000000` plus its row.
    pub token: u32,
    /// Its name.
    pub name: String,
    /// Its version, `major.minor.build.revision`.
    pub version: String,
}

/// One user string, a literal the code loads with `ldstr`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UserString {
    /// Its token, `0x70000000` plus its offset in `#US`.
    pub token: u32,
    /// File offset of its first character.
    pub off: u64,
    /// Its length in UTF-16 code units.
    pub units: usize,
    /// Its text, at most [`STRING_UNITS_MAX`] code units of it.
    pub text: String,
}

impl UserString {
    /// The row the strings listing gives it.
    #[must_use]
    pub fn hit(&self) -> StringHit {
        let shown: String = self.text.chars().take(DISPLAY_MAX).collect();
        let cut = if self.text.chars().nth(DISPLAY_MAX).is_some() {
            "..."
        } else {
            ""
        };
        StringHit {
            off: self.off,
            len: self.units,
            text: format!("{}{cut}", one_line(&crate::strings::escape_text(&shown))),
            encoding: Encoding::DotnetUs,
        }
    }
}

/// A .NET assembly's metadata, as far as triage reads it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clr {
    /// The CLR header's address.
    pub at: u64,
    /// The runtime version the header states, as `(major, minor)`: 2.5
    /// for every runtime from .NET 2.0 on.
    pub runtime: (u16, u16),
    /// The metadata root's version string (`v4.0.30319`).
    pub version: String,
    /// `COMIMAGE_FLAGS_*`.
    pub flags: u32,
    /// The entry point: a `MethodDef` token, or a native RVA when the
    /// flags say `NATIVE_ENTRYPOINT`; `0` for none.
    pub entry: u32,
    /// The module's name, `-` for none.
    pub module: String,
    /// The assembly's name and version, for a manifest module.
    pub assembly: Option<(String, String)>,
    /// Every defined type, in table order.
    pub types: Vec<TypeDef>,
    /// Every defined method, in table order.
    pub methods: Vec<Method>,
    /// Every P/Invoke, in table order.
    pub pinvokes: Vec<PInvoke>,
    /// Every external member, in table order.
    pub member_refs: Vec<MemberRef>,
    /// How many types it references (`TypeRef` rows read).
    pub type_refs: usize,
    /// Every referenced assembly, in table order.
    pub assembly_refs: Vec<AssemblyRef>,
    /// Every native module the P/Invokes name, in table order.
    pub module_refs: Vec<String>,
    /// Every user string, in heap order.
    pub user_strings: Vec<UserString>,
    /// The file extent of the `#US` heap, as `(offset, length)`.
    pub us_heap: Option<(u64, u64)>,
    /// A table held more rows than [`ROWS_MAX`], or `#US` more strings
    /// than [`STRINGS_MAX`], and the rest were not read.
    pub capped: bool,
}

impl Clr {
    /// The method whose body starts at `va`.
    ///
    /// # Arguments
    ///
    /// * `image_base` - The image's base, which a method's RVA counts from.
    /// * `va` - The address.
    ///
    /// # Returns
    ///
    /// The method, or `None` when no method's body starts there.
    #[must_use]
    pub fn method_at(&self, image_base: u64, va: u64) -> Option<&Method> {
        let rva = u32::try_from(va.checked_sub(image_base)?).ok()?;
        (rva != 0)
            .then(|| self.methods.iter().find(|m| m.rva == rva))
            .flatten()
    }

    /// Whether a file offset lies in the `#US` heap.
    ///
    /// # Arguments
    ///
    /// * `off` - The file offset.
    #[must_use]
    pub fn in_user_strings(&self, off: u64) -> bool {
        self.us_heap
            .is_some_and(|(start, len)| off >= start && off - start < len)
    }

    /// The entry point, as the summary names it: the method's token and
    /// name, or the native RVA.
    fn entry_text(&self, image_base: u64) -> String {
        if self.entry == 0 {
            return "none".to_owned();
        }
        if self.flags & NATIVE_ENTRYPOINT != 0 {
            return format!(
                "native {:#x}",
                image_base.saturating_add(u64::from(self.entry))
            );
        }
        let name = self
            .methods
            .iter()
            .find(|m| m.token == self.entry)
            .map_or("?", |m| m.name.as_str());
        format!("{:#010x} {name}", self.entry)
    }

    /// The header's flags as words.
    fn flag_words(&self) -> String {
        let words: Vec<&str> = FLAG_WORDS
            .iter()
            .filter(|(bit, _)| self.flags & bit != 0)
            .map(|(_, w)| *w)
            .collect();
        if words.is_empty() {
            "no flags".to_owned()
        } else {
            words.join(" ")
        }
    }

    /// Renders the `.net:` line of the program summary.
    ///
    /// # Arguments
    ///
    /// * `image_base` - The image's base, for a native entry's address.
    pub(crate) fn render(&self, image_base: u64) -> String {
        let what = self.assembly.as_ref().map_or_else(
            || format!("module {}", self.module),
            |(name, version)| format!("assembly {name} {version}"),
        );
        let natives = self
            .methods
            .iter()
            .filter(|m| m.body == Body::Native)
            .count();
        format!(
            ".net:    {what}, runtime {}.{}, metadata {}, {}; entry {}; types {}, methods {} (native {natives}), pinvokes {}, assembly refs {}, user strings {}{}; IL is not decompiled, borer://clr lists them\n",
            self.runtime.0,
            self.runtime.1,
            self.version,
            self.flag_words(),
            self.entry_text(image_base),
            self.types.len(),
            self.methods.len(),
            self.pinvokes.len(),
            self.assembly_refs.len(),
            self.user_strings.len(),
            if self.capped { " (capped)" } else { "" },
        )
    }

    /// The symbols the methods make: each method's name at its body's
    /// address, where no other symbol names it.
    ///
    /// An IL body is a data symbol, since it is not x86 code and seeds no
    /// function; a native body is a local function, analyzed as usual.
    ///
    /// # Arguments
    ///
    /// * `image_base` - The image's base.
    /// * `symbols` - The symbols the file states, which win.
    ///
    /// # Returns
    ///
    /// The new symbols, in table order.
    pub(crate) fn symbols(&self, image_base: u64, symbols: &[Symbol]) -> Vec<Symbol> {
        let named: std::collections::BTreeSet<u64> = symbols
            .iter()
            .filter(|s| s.kind != SymbolKind::Data)
            .map(|s| s.addr)
            .collect();
        self.methods
            .iter()
            .filter(|m| m.rva != 0)
            .filter_map(|m| {
                let addr = image_base.checked_add(u64::from(m.rva))?;
                let kind = match m.body {
                    Body::Native => SymbolKind::Local,
                    Body::Il | Body::Runtime | Body::None => SymbolKind::Data,
                };
                (!named.contains(&addr)).then(|| Symbol {
                    name: m.name.clone(),
                    addr,
                    kind,
                })
            })
            .collect()
    }
}

/// Reads a little-endian `u16` at `at`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
fn u16_at(b: &[u8], at: usize) -> Option<u16> {
    Some(u16::from_le_bytes(*b.get(at..)?.first_chunk::<2>()?))
}

/// Reads a little-endian `u32` at `at`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
fn u32_at(b: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_le_bytes(*b.get(at..)?.first_chunk::<4>()?))
}

/// Reads a little-endian `u64` at `at`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - Offset of the first byte.
fn u64_at(b: &[u8], at: usize) -> Option<u64> {
    Some(u64::from_le_bytes(*b.get(at..)?.first_chunk::<8>()?))
}

/// The table stream, its row counts read and every table located.
#[derive(Debug, Clone, Copy)]
struct Tables<'a> {
    /// The stream's bytes.
    data: &'a [u8],
    /// Rows per table.
    rows: [u32; TABLES],
    /// Where each table's first row starts in [`Tables::data`].
    start: [usize; TABLES],
    /// Bytes per row of each table.
    width: [usize; TABLES],
    /// Bytes of an index into `#Strings`, `#GUID` and `#Blob`: 2 or 4.
    heaps: [usize; 3],
}

impl<'a> Tables<'a> {
    /// Reads the stream's header and row counts and locates every table.
    ///
    /// # Arguments
    ///
    /// * `data` - The `#~` or `#-` stream.
    ///
    /// # Errors
    ///
    /// When the header or the counts run past the stream, or the tables
    /// the counts state do not fit in it, naming the first that runs past.
    fn read(data: &'a [u8]) -> Result<Self, String> {
        let short = || {
            format!(
                "the table stream's {} bytes end inside its header",
                data.len()
            )
        };
        let sizes = *data.get(6).ok_or_else(short)?;
        let valid = u64_at(data, 8).ok_or_else(short)?;
        let mut rows = [0u32; TABLES];
        let mut at = 24usize;
        for t in 0..64usize {
            if (valid >> t) & 1 == 0 {
                continue;
            }
            let n = u32_at(data, at).ok_or_else(|| {
                format!(
                    "the table stream's {} bytes end inside its row counts",
                    data.len()
                )
            })?;
            if let Some(slot) = rows.get_mut(t) {
                *slot = n;
            }
            at += 4;
        }
        if sizes & EXTRA_DATA != 0 {
            at += 4;
        }
        let wide = |bit: u8| if sizes & bit != 0 { 4 } else { 2 };
        let mut tables = Tables {
            data,
            rows,
            start: [0; TABLES],
            width: [0; TABLES],
            heaps: [wide(0x1), wide(0x2), wide(0x4)],
        };
        for (t, (name, schema)) in SCHEMAS.iter().enumerate() {
            let width: usize = schema.iter().map(|c| tables.col_width(*c)).sum();
            let n = rows.get(t).copied().unwrap_or(0);
            let end = saturating_usize(u64::from(n))
                .checked_mul(width)
                .and_then(|len| at.checked_add(len))
                .filter(|end| *end <= data.len())
                .ok_or_else(|| {
                    format!(
                        "the {name} table's {n} rows of {width} bytes run past the table stream's {} bytes",
                        data.len()
                    )
                })?;
            if let (Some(s), Some(w)) = (tables.start.get_mut(t), tables.width.get_mut(t)) {
                *s = at;
                *w = width;
            }
            at = end;
        }
        Ok(tables)
    }

    /// Rows in a table; `0` for a table this does not know.
    ///
    /// # Arguments
    ///
    /// * `t` - The table number.
    fn count(&self, t: u8) -> u32 {
        self.rows.get(usize::from(t)).copied().unwrap_or(0)
    }

    /// Rows of a table this reads, at most [`ROWS_MAX`].
    ///
    /// # Arguments
    ///
    /// * `t` - The table number.
    fn readable(&self, t: u8) -> u32 {
        self.count(t).min(ROWS_MAX)
    }

    /// Bytes one column takes (ECMA-335 II.24.2.6).
    ///
    /// # Arguments
    ///
    /// * `c` - The column.
    fn col_width(&self, c: Col) -> usize {
        /// The most rows a two-byte index addresses.
        const SMALL: u32 = 1 << 16;
        let heap = |i: usize| self.heaps.get(i).copied().unwrap_or(4);
        match c {
            Col::U16 => 2,
            Col::U32 => 4,
            Col::Str => heap(0),
            Col::Guid => heap(1),
            Col::Blob => heap(2),
            Col::Row(t) => {
                if self.count(t) < SMALL {
                    2
                } else {
                    4
                }
            }
            Col::Code(code) => {
                let most = code
                    .tables()
                    .iter()
                    .map(|t| self.count(*t))
                    .max()
                    .unwrap_or(0);
                if most < SMALL >> code.bits() { 2 } else { 4 }
            }
        }
    }

    /// Reads one cell.
    ///
    /// # Arguments
    ///
    /// * `t` - The table number.
    /// * `row` - The one-based row, at most the table's count.
    /// * `col` - The column's position in the table's schema.
    ///
    /// # Errors
    ///
    /// When the row or the column is not in the table.
    fn cell(&self, t: u8, row: u32, col: usize) -> Result<u32, String> {
        let i = usize::from(t);
        let (name, schema) = SCHEMAS.get(i).ok_or_else(|| format!("no table {t:#x}"))?;
        let c = *schema
            .get(col)
            .ok_or_else(|| format!("the {name} table has no column {col}"))?;
        let before: usize = schema.iter().take(col).map(|c| self.col_width(*c)).sum();
        let at = row
            .checked_sub(1)
            .filter(|_| row <= self.count(t))
            .and_then(|r| saturating_usize(u64::from(r)).checked_mul(*self.width.get(i)?))
            .and_then(|o| o.checked_add(*self.start.get(i)?))
            .and_then(|o| o.checked_add(before))
            .ok_or_else(|| format!("{name} row {row} is not one of its {} rows", self.count(t)))?;
        let value = match self.col_width(c) {
            2 => u16_at(self.data, at).map(u32::from),
            _ => u32_at(self.data, at),
        };
        value.ok_or_else(|| format!("{name} row {row} runs past the table stream"))
    }
}

/// The streams of a metadata root, by name.
#[derive(Debug, Clone, Copy, Default)]
struct Streams<'a> {
    /// `#~` or `#-`, the first of either.
    tables: Option<&'a [u8]>,
    /// `#Strings`.
    strings: &'a [u8],
    /// `#US`, and its offset in the metadata.
    us: Option<(usize, &'a [u8])>,
}

/// Reads one `#Strings` entry, made safe for a row ([`one_line`]).
///
/// # Arguments
///
/// * `heap` - The `#Strings` heap.
/// * `idx` - The index, `0` for the empty string.
/// * `what` - What the index names, for the error.
///
/// # Errors
///
/// When the index is past the heap.
fn string(heap: &[u8], idx: u32, what: &dyn Fn() -> String) -> Result<String, String> {
    if idx == 0 {
        return Ok(String::new());
    }
    let rest = heap
        .get(saturating_usize(u64::from(idx))..)
        .filter(|r| !r.is_empty())
        .ok_or_else(|| {
            format!(
                "{} is at #Strings offset {idx:#x}, past the heap's {:#x} bytes",
                what(),
                heap.len()
            )
        })?;
    let end = rest
        .iter()
        .take(NAME_MAX)
        .position(|b| *b == 0)
        .unwrap_or(rest.len().min(NAME_MAX));
    Ok(one_line(&String::from_utf8_lossy(
        rest.get(..end).unwrap_or_default(),
    )))
}

/// Reads the user strings of a `#US` heap, in heap order.
///
/// Each is a compressed length, then that many bytes: UTF-16LE characters
/// and one trailing flag byte. The walk stops at a length that does not
/// read or runs past the heap.
///
/// # Arguments
///
/// * `heap` - The heap.
/// * `file_off` - The heap's file offset.
///
/// # Returns
///
/// The strings, at most [`STRINGS_MAX`], and whether more were left.
fn user_strings(heap: &[u8], file_off: u64) -> (Vec<UserString>, bool) {
    let mut out = Vec::new();
    let mut pos = 0usize;
    while let Some(&b0) = heap.get(pos) {
        if out.len() >= STRINGS_MAX {
            return (out, true);
        }
        let (len, head) = if b0 & 0x80 == 0 {
            (usize::from(b0), 1)
        } else if b0 & 0xc0 == 0x80 {
            let Some(&b1) = heap.get(pos + 1) else {
                break;
            };
            ((usize::from(b0 & 0x3f) << 8) | usize::from(b1), 2)
        } else if b0 & 0xe0 == 0xc0 {
            let Some(rest) = heap.get(pos + 1..pos + 4) else {
                break;
            };
            let len = rest
                .iter()
                .fold(usize::from(b0 & 0x1f), |n, b| (n << 8) | usize::from(*b));
            (len, 4)
        } else {
            break;
        };
        let start = pos + head;
        let Some(body) = heap.get(start..start.saturating_add(len)) else {
            break;
        };
        let units = len / 2;
        if units > 0
            && let Ok(token_off) = u32::try_from(pos)
            && token_off < 1 << 24
        {
            let text: String = char::decode_utf16(
                body.chunks_exact(2)
                    .take(STRING_UNITS_MAX)
                    .filter_map(|c| c.first_chunk::<2>().map(|b| u16::from_le_bytes(*b))),
            )
            .map(|c| c.unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect();
            out.push(UserString {
                token: 0x7000_0000 | token_off,
                off: file_off.saturating_add(from_usize(start)),
                units,
                text,
            });
        }
        pos = start + len;
    }
    (out, false)
}

/// Reads the metadata root and finds its streams.
///
/// # Arguments
///
/// * `meta` - The metadata, from its root.
///
/// # Returns
///
/// The version string and the streams.
///
/// # Errors
///
/// When the signature is wrong, the header runs past the metadata, or a
/// stream runs past it.
fn root(meta: &[u8]) -> Result<(String, Streams<'_>), String> {
    let short = || format!("the metadata's {} bytes end inside its root", meta.len());
    let signature = u32_at(meta, 0).ok_or_else(short)?;
    if signature != BSJB {
        return Err(format!(
            "the metadata root's signature is {signature:#010x}, not BSJB"
        ));
    }
    let vlen = saturating_usize(u64::from(u32_at(meta, 12).ok_or_else(short)?));
    let version_bytes = meta
        .get(16..16usize.saturating_add(vlen))
        .ok_or_else(short)?;
    let version = one_line(
        String::from_utf8_lossy(version_bytes)
            .trim_end_matches('\0')
            .trim(),
    );
    let mut at = 16 + vlen;
    let count = u16_at(meta, at + 2).ok_or_else(short)?;
    at += 4;
    let mut streams = Streams::default();
    for _ in 0..count {
        let (Some(off), Some(size)) = (u32_at(meta, at), u32_at(meta, at + 4)) else {
            return Err(short());
        };
        let name_at = at + 8;
        let name_bytes = meta.get(name_at..).ok_or_else(short)?;
        let name_len = name_bytes
            .iter()
            .take(32)
            .position(|b| *b == 0)
            .ok_or_else(|| format!("a stream header at metadata offset {at:#x} has no name"))?;
        let name = String::from_utf8_lossy(name_bytes.get(..name_len).unwrap_or_default());
        at = name_at + (name_len + 4) / 4 * 4;
        let start = saturating_usize(u64::from(off));
        let body = start
            .checked_add(saturating_usize(u64::from(size)))
            .and_then(|end| meta.get(start..end))
            .ok_or_else(|| {
                format!(
                    "stream {} at metadata offset {off:#x}, {size:#x} bytes, runs past the metadata's {:#x} bytes",
                    one_line(&name),
                    meta.len()
                )
            })?;
        match &*name {
            "#~" | "#-" if streams.tables.is_none() => streams.tables = Some(body),
            "#Strings" if streams.strings.is_empty() => streams.strings = body,
            "#US" if streams.us.is_none() => streams.us = Some((start, body)),
            _ => {}
        }
    }
    Ok((version, streams))
}

/// Reads one table's rows into names through `f`, at most [`ROWS_MAX`].
///
/// # Arguments
///
/// * `t` - The tables.
/// * `table` - The table number.
/// * `f` - Reads one one-based row.
///
/// # Errors
///
/// The first error `f` gives.
fn rows<T>(
    t: &Tables<'_>,
    table: u8,
    mut f: impl FnMut(u32) -> Result<T, String>,
) -> Result<Vec<T>, String> {
    (1..=t.readable(table)).map(&mut f).collect()
}

/// The names the tables give, read once and shared by every row that
/// refers to them.
#[derive(Debug, Clone, Default)]
struct Names {
    /// Each `TypeDef` row's full name, by row less one.
    types: Vec<String>,
    /// Each `TypeRef` row's full name, by row less one.
    type_refs: Vec<String>,
    /// Each `TypeRef` row's scope: an assembly's or module's name.
    scopes: Vec<String>,
    /// Each `MethodDef` row's full name, by row less one.
    methods: Vec<String>,
    /// Each `ModuleRef` row's name, by row less one.
    modules: Vec<String>,
    /// Each `AssemblyRef` row's name, by row less one.
    assemblies: Vec<String>,
}

/// A name by one-based row, `?` for the null row or one past the list.
///
/// # Arguments
///
/// * `names` - The names, by row less one.
/// * `row` - The one-based row.
fn by_row(names: &[String], row: u32) -> &str {
    row.checked_sub(1)
        .and_then(|r| names.get(saturating_usize(u64::from(r))))
        .map_or("?", String::as_str)
}

/// Joins a namespace and a name the way `ildasm` writes a type.
///
/// # Arguments
///
/// * `namespace` - The namespace, empty for none.
/// * `name` - The type's name.
fn qualified(namespace: &str, name: &str) -> String {
    if namespace.is_empty() {
        name.to_owned()
    } else {
        format!("{namespace}.{name}")
    }
}

/// Reads the CLR header and the metadata of a PE that has one.
///
/// # Arguments
///
/// * `p` - The program, its sections and bytes read.
/// * `dir` - The CLR runtime header's data directory, `(rva, size)`.
///
/// # Returns
///
/// The metadata, as far as triage reads it.
///
/// # Errors
///
/// When the header or the metadata is not in the file, or any part of it
/// does not hold: the reason, naming the stream, table, row or index.
pub(crate) fn read(p: &Program, dir: (u32, u32)) -> Result<Clr, String> {
    let at = p.image_base.saturating_add(u64::from(dir.0));
    let head = p
        .read_va(at, COR20_LEN)
        .ok_or_else(|| format!("the CLR header at {at:#x} is not in the file"))?;
    let field = |o: usize| u32_at(head, o).unwrap_or(0);
    let cb = field(0);
    if saturating_usize(u64::from(cb)) < COR20_LEN {
        return Err(format!(
            "the CLR header states {cb} bytes, fewer than its {COR20_LEN}"
        ));
    }
    let runtime = (u16_at(head, 4).unwrap_or(0), u16_at(head, 6).unwrap_or(0));
    let (meta_rva, meta_size) = (field(8), field(12));
    let flags = field(16);
    let entry = field(20);
    let meta_va = p.image_base.saturating_add(u64::from(meta_rva));
    let want = saturating_usize(u64::from(meta_size)).min(META_MAX);
    let meta = p
        .read_va_upto(meta_va, want)
        .ok_or_else(|| format!("the metadata at {meta_va:#x} is not in the file"))?;
    let (version, streams) = root(meta)?;
    let data = streams
        .tables
        .ok_or("the metadata has no table stream (#~ or #-)")?;
    let t = Tables::read(data)?;
    let heap = streams.strings;
    let mut capped = TABLES_READ.iter().any(|table| t.count(*table) > ROWS_MAX);

    let mut names = Names::default();
    let str_cell = |table: u8, row: u32, col: usize| -> Result<String, String> {
        let idx = t.cell(table, row, col)?;
        let (name, _) = SCHEMAS
            .get(usize::from(table))
            .copied()
            .unwrap_or(("?", &[]));
        string(heap, idx, &|| format!("{name} row {row}'s name"))
    };
    names.modules = rows(&t, MODULE_REF, |r| str_cell(MODULE_REF, r, 0))?;
    names.assemblies = rows(&t, ASSEMBLY_REF, |r| str_cell(ASSEMBLY_REF, r, 6))?;

    let typedefs = rows(&t, TYPE_DEF, |r| {
        Ok((
            str_cell(TYPE_DEF, r, 2)?,
            str_cell(TYPE_DEF, r, 1)?,
            t.cell(TYPE_DEF, r, 5)?,
        ))
    })?;
    let mut enclosing: BTreeMap<u32, u32> = BTreeMap::new();
    for r in 1..=t.readable(NESTED_CLASS) {
        enclosing.insert(t.cell(NESTED_CLASS, r, 0)?, t.cell(NESTED_CLASS, r, 1)?);
    }
    names.types = (1..=t.readable(TYPE_DEF))
        .map(|row| {
            let mut parts: Vec<&str> = Vec::new();
            let mut cur = row;
            let mut namespace = "";
            for _ in 0..NEST_MAX {
                let Some((ns, name, _)) = cur
                    .checked_sub(1)
                    .and_then(|i| typedefs.get(saturating_usize(u64::from(i))))
                else {
                    break;
                };
                parts.push(name);
                namespace = ns;
                match enclosing.get(&cur) {
                    Some(&outer) if outer != cur => cur = outer,
                    _ => break,
                }
            }
            parts.reverse();
            qualified(namespace, &parts.join("/"))
        })
        .collect();

    let resolution = Coded::ResolutionScope;
    let refs = rows(&t, TYPE_REF, |r| {
        let scope = t.cell(TYPE_REF, r, 0)?;
        Ok((scope, str_cell(TYPE_REF, r, 2)?, str_cell(TYPE_REF, r, 1)?))
    })?;
    for (i, (scope, ns, name)) in refs.iter().enumerate() {
        let (mut full, mut owner) = (qualified(ns, name), *scope);
        let mut depth = 0;
        while let Some((TYPE_REF, outer)) = resolution.split(owner) {
            let Some((outer_scope, outer_ns, outer_name)) = outer
                .checked_sub(1)
                .and_then(|o| refs.get(saturating_usize(u64::from(o))))
            else {
                break;
            };
            depth += 1;
            if depth > NEST_MAX || from_usize(i).checked_add(1) == Some(u64::from(outer)) {
                break;
            }
            full = format!("{}/{full}", qualified(outer_ns, outer_name));
            owner = *outer_scope;
        }
        let scope = match resolution.split(owner) {
            Some((ASSEMBLY_REF, row)) => by_row(&names.assemblies, row).to_owned(),
            Some((MODULE_REF, row)) => by_row(&names.modules, row).to_owned(),
            Some((MODULE, _)) => "this module".to_owned(),
            Some(_) | None => "-".to_owned(),
        };
        names.type_refs.push(full);
        names.scopes.push(scope);
    }

    let defs = rows(&t, METHOD_DEF, |r| {
        Ok((
            t.cell(METHOD_DEF, r, 0)?,
            u16::try_from(t.cell(METHOD_DEF, r, 1)?).unwrap_or(0),
            str_cell(METHOD_DEF, r, 3)?,
        ))
    })?;
    let order: Vec<u32> = if t.count(METHOD_PTR) > 0 {
        rows(&t, METHOD_PTR, |r| t.cell(METHOD_PTR, r, 0))?
    } else {
        (1..=u32::try_from(defs.len()).unwrap_or(0)).collect()
    };
    let mut owner: Vec<Option<usize>> = vec![None; defs.len()];
    let mut owned = vec![0usize; typedefs.len()];
    let lists: Vec<usize> = typedefs
        .iter()
        .map(|(_, _, list)| saturating_usize(u64::from(*list)))
        .collect();
    let past = order.len().saturating_add(1);
    let mut cursor = 1usize;
    for (ty, from) in lists.iter().enumerate() {
        let from = (*from).clamp(cursor, past);
        let to = lists.get(ty + 1).copied().unwrap_or(past).clamp(from, past);
        cursor = to;
        for pos in from..to {
            let Some(def) = pos
                .checked_sub(1)
                .and_then(|p| order.get(p))
                .and_then(|d| d.checked_sub(1))
                .and_then(|d| owner.get_mut(saturating_usize(u64::from(d))))
            else {
                continue;
            };
            if def.is_none() {
                *def = Some(ty);
                if let Some(n) = owned.get_mut(ty) {
                    *n += 1;
                }
            }
        }
    }
    let methods: Vec<Method> = defs
        .iter()
        .zip(&owner)
        .enumerate()
        .map(|(i, ((rva, impl_flags, name), ty))| {
            let body = if *rva == 0 {
                Body::None
            } else {
                match impl_flags & CODE_TYPE {
                    0 => Body::Il,
                    1 => Body::Native,
                    _ => Body::Runtime,
                }
            };
            let owner = ty
                .and_then(|ty| names.types.get(ty))
                .map_or("?", String::as_str);
            Method {
                token: 0x0600_0000 | u32::try_from(i + 1).unwrap_or(0),
                name: format!("{owner}::{name}"),
                rva: *rva,
                body,
            }
        })
        .collect();
    names.methods = methods.iter().map(|m| m.name.clone()).collect();

    let types = names
        .types
        .iter()
        .zip(&owned)
        .enumerate()
        .map(|(i, (name, n))| TypeDef {
            token: 0x0200_0000 | u32::try_from(i + 1).unwrap_or(0),
            name: name.clone(),
            methods: *n,
        })
        .collect();

    let forwarded = Coded::MemberForwarded;
    let pinvokes = rows(&t, IMPL_MAP, |r| {
        let member = t.cell(IMPL_MAP, r, 1)?;
        let (token, method) = match forwarded.split(member) {
            Some((METHOD_DEF, row)) => (0x0600_0000 | row, by_row(&names.methods, row).to_owned()),
            Some((table, row)) => ((u32::from(table) << 24) | row, "?".to_owned()),
            None => {
                return Err(format!(
                    "ImplMap row {r}'s member {member:#x} names no table"
                ));
            }
        };
        Ok(PInvoke {
            token,
            method,
            dll: by_row(&names.modules, t.cell(IMPL_MAP, r, 3)?).to_owned(),
            entry: str_cell(IMPL_MAP, r, 2)?,
        })
    })?;

    let parent = Coded::MemberRefParent;
    let member_refs = rows(&t, MEMBER_REF, |r| {
        let class = t.cell(MEMBER_REF, r, 0)?;
        let member = str_cell(MEMBER_REF, r, 1)?;
        let (owner, scope) = match parent.split(class) {
            Some((TYPE_REF, row)) => (
                by_row(&names.type_refs, row).to_owned(),
                by_row(&names.scopes, row).to_owned(),
            ),
            Some((TYPE_DEF, row)) => (
                by_row(&names.types, row).to_owned(),
                "this module".to_owned(),
            ),
            Some((MODULE_REF, row)) => (by_row(&names.modules, row).to_owned(), "-".to_owned()),
            Some((METHOD_DEF, row)) => (
                by_row(&names.methods, row).to_owned(),
                "this module".to_owned(),
            ),
            Some(_) => ("<generic>".to_owned(), "-".to_owned()),
            None => {
                return Err(format!(
                    "MemberRef row {r}'s parent {class:#x} names no table"
                ));
            }
        };
        Ok(MemberRef {
            token: 0x0a00_0000 | r,
            name: format!("{owner}::{member}"),
            scope,
        })
    })?;

    let version_of = |table: u8, row: u32, first: usize| -> Result<String, String> {
        let parts = (first..first + 4)
            .map(|c| t.cell(table, row, c).map(|v| v.to_string()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(parts.join("."))
    };
    let assembly_refs = rows(&t, ASSEMBLY_REF, |r| {
        Ok(AssemblyRef {
            token: 0x2300_0000 | r,
            name: by_row(&names.assemblies, r).to_owned(),
            version: version_of(ASSEMBLY_REF, r, 0)?,
        })
    })?;
    let assembly = if t.count(ASSEMBLY) > 0 {
        Some((str_cell(ASSEMBLY, 1, 7)?, version_of(ASSEMBLY, 1, 1)?))
    } else {
        None
    };
    let module = if t.count(MODULE) > 0 {
        str_cell(MODULE, 1, 1)?
    } else {
        String::new()
    };
    let module = if module.is_empty() {
        "-".to_owned()
    } else {
        module
    };

    let heap_off = streams.us.and_then(|(start, heap)| {
        let off = p.va_to_offset(meta_va.saturating_add(from_usize(start)))?;
        Some((off, heap))
    });
    let (strings, us_heap) = match heap_off {
        Some((off, heap)) => {
            let (strings, more) = user_strings(heap, off);
            capped |= more;
            (strings, Some((off, from_usize(heap.len()))))
        }
        None => (Vec::new(), None),
    };

    Ok(Clr {
        at,
        runtime,
        version,
        flags,
        entry,
        module,
        assembly,
        types,
        methods,
        pinvokes,
        member_refs,
        type_refs: names.type_refs.len(),
        assembly_refs,
        module_refs: names.modules,
        user_strings: strings,
        us_heap,
        capped,
    })
}

/// The tables whose rows this reads, which [`ROWS_MAX`] caps.
const TABLES_READ: [u8; 9] = [
    TYPE_REF,
    TYPE_DEF,
    METHOD_PTR,
    METHOD_DEF,
    MEMBER_REF,
    MODULE_REF,
    IMPL_MAP,
    ASSEMBLY_REF,
    NESTED_CLASS,
];

/// Replaces the UTF-16 runs a walk of the file found inside the `#US` heap
/// with the heap's own strings, tagged [`Encoding::DotnetUs`].
///
/// The walk reads only ASCII characters, so it splits a user string at its
/// first other character and joins none of it to its token; the heap's
/// entries are the strings whole, so they replace what the walk found
/// there.
///
/// # Arguments
///
/// * `p` - The program.
/// * `wide` - The walk's UTF-16LE runs, in offset order.
/// * `min` - Shortest string kept, in code units.
///
/// # Returns
///
/// The runs in offset order; `wide` itself for a program with no `#US`.
#[must_use]
pub fn with_user_strings(p: &Program, mut wide: Vec<StringHit>, min: usize) -> Vec<StringHit> {
    let Some(clr) = p.clr() else {
        return wide;
    };
    if clr.us_heap.is_none() {
        return wide;
    }
    wide.retain(|h| !clr.in_user_strings(h.off));
    wide.extend(
        clr.user_strings
            .iter()
            .filter(|s| s.units >= min)
            .map(UserString::hit),
    );
    wide.sort_by_key(|h| h.off);
    wide
}

/// What a `borer://clr` read keeps: kinds, texts and a page.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Filter {
    /// The kinds kept; every kind when empty.
    kinds: Vec<&'static str>,
    /// Texts every kept row's name or detail contains, lowercased.
    texts: Vec<String>,
    /// Rows skipped.
    offset: usize,
    /// Most rows shown.
    limit: usize,
}

/// The kinds of row the listing has, in listing order.
const KINDS: [&str; 7] = [
    "type",
    "method",
    "pinvoke",
    "memberref",
    "asmref",
    "moduleref",
    "string",
];

impl Filter {
    /// Reads a spec: comma-separated kinds ([`KINDS`]), texts,
    /// `offset=<n>` and `limit=<n>`.
    ///
    /// # Arguments
    ///
    /// * `spec` - The spec, empty for everything.
    ///
    /// # Errors
    ///
    /// When an offset or a limit does not read.
    fn parse(spec: &str) -> Result<Self, String> {
        let mut f = Filter {
            limit: CLR_PAGE,
            ..Filter::default()
        };
        for word in spec.split(',').map(str::trim).filter(|w| !w.is_empty()) {
            if let Some(n) = word.strip_prefix("offset=") {
                f.offset = crate::table::row_offset(n)?;
            } else if let Some(n) = word.strip_prefix("limit=") {
                f.limit = crate::table::row_limit(n)?.min(CLR_PAGE);
            } else if let Some(kind) = KINDS.iter().find(|k| k.eq_ignore_ascii_case(word)) {
                f.kinds.push(kind);
            } else {
                f.texts.push(word.to_lowercase());
            }
        }
        Ok(f)
    }

    /// Whether a row is kept.
    ///
    /// # Arguments
    ///
    /// * `row` - The row's kind, name and detail.
    fn keeps(&self, row: &Row) -> bool {
        let text = format!("{}\t{}", row.name, row.detail).to_lowercase();
        (self.kinds.is_empty() || self.kinds.contains(&row.kind))
            && self.texts.iter().all(|t| text.contains(t.as_str()))
    }
}

/// One row of the listing.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    /// One of [`KINDS`].
    kind: &'static str,
    /// The metadata token.
    token: u32,
    /// The address, `-` for none.
    va: String,
    /// The name.
    name: String,
    /// What else the row says.
    detail: String,
}

/// Lists a .NET assembly's metadata: types, methods with their bodies'
/// addresses, P/Invokes, external members, referenced assemblies and
/// modules, and user strings, one table.
///
/// IL is not decompiled: a method's address is its IL body's, which the
/// listing says, and a native method in a mixed-mode image is code the
/// rest of the engine analyzes as usual.
///
/// # Arguments
///
/// * `p` - The program.
/// * `spec` - Comma-separated kinds (`type`, `method`, `pinvoke`,
///   `memberref`, `asmref`, `moduleref`, `string`) and texts a row's name
///   or detail contains, and `offset=<n>`, `limit=<n>`; empty for all.
///
/// # Returns
///
/// The listing, [`CLR_PAGE`] rows a page under a `# showing` line; a
/// one-line note for a program with no CLR header.
///
/// # Errors
///
/// When the metadata was refused, with the reason, or the spec's page
/// does not read.
pub fn clr_tsv(p: &Program, spec: &str) -> Result<String, String> {
    let filter = Filter::parse(spec)?;
    let clr = match &p.clr {
        None => {
            return Ok(
                "# not a .NET assembly: the image has no CLR runtime header (data directory 14)\n"
                    .to_owned(),
            );
        }
        Some(Err(why)) => return Err(format!("the .NET metadata is refused: {why}")),
        Some(Ok(clr)) => clr,
    };
    let base = p.image_base;
    let va = |rva: u32| {
        if rva == 0 {
            "-".to_owned()
        } else {
            format!("{:#x}", base.saturating_add(u64::from(rva)))
        }
    };
    let mut all: Vec<Row> = Vec::new();
    all.extend(clr.types.iter().map(|ty| Row {
        kind: "type",
        token: ty.token,
        va: "-".to_owned(),
        name: ty.name.clone(),
        detail: format!("{} methods", ty.methods),
    }));
    let pinvoked: BTreeMap<u32, &PInvoke> = clr.pinvokes.iter().map(|pi| (pi.token, pi)).collect();
    all.extend(clr.methods.iter().map(|m| match pinvoked.get(&m.token) {
        Some(pi) => Row {
            kind: "pinvoke",
            token: m.token,
            va: va(m.rva),
            name: m.name.clone(),
            detail: format!("{}!{}", pi.dll, pi.entry),
        },
        None => Row {
            kind: "method",
            token: m.token,
            va: va(m.rva),
            name: m.name.clone(),
            detail: m.body.word().to_owned(),
        },
    }));
    all.extend(clr.member_refs.iter().map(|m| Row {
        kind: "memberref",
        token: m.token,
        va: "-".to_owned(),
        name: m.name.clone(),
        detail: m.scope.clone(),
    }));
    all.extend(clr.assembly_refs.iter().map(|r| Row {
        kind: "asmref",
        token: r.token,
        va: "-".to_owned(),
        name: r.name.clone(),
        detail: r.version.clone(),
    }));
    all.extend(clr.module_refs.iter().enumerate().map(|(i, m)| Row {
        kind: "moduleref",
        token: 0x1a00_0000 | u32::try_from(i + 1).unwrap_or(0),
        va: "-".to_owned(),
        name: m.clone(),
        detail: "-".to_owned(),
    }));
    all.extend(clr.user_strings.iter().map(|s| {
        Row {
            kind: "string",
            token: s.token,
            va: p
                .offset_to_va(s.off)
                .map_or_else(|| "-".to_owned(), |v| format!("{v:#x}")),
            name: format!("\"{}\"", s.hit().text),
            detail: format!("{} chars", s.units),
        }
    }));
    let kept: Vec<&Row> = all.iter().filter(|r| filter.keeps(r)).collect();
    let total = kept.len();
    let mut out = String::new();
    let what = clr.assembly.as_ref().map_or_else(
        || format!("module {}", clr.module),
        |(name, version)| format!("assembly {name} {version} (module {})", clr.module),
    );
    let _ = writeln!(
        out,
        "# .NET {what}, runtime {}.{}, metadata {}, {}; entry {}",
        clr.runtime.0,
        clr.runtime.1,
        clr.version,
        clr.flag_words(),
        clr.entry_text(base)
    );
    out.push_str(
        "# IL is not decompiled: an il method's va is its IL body, a data symbol; a native method (mixed-mode) is code, analyzed as usual\n",
    );
    let counts: Vec<String> = KINDS
        .iter()
        .map(|k| format!("{k} {}", all.iter().filter(|r| r.kind == *k).count()))
        .collect();
    let _ = writeln!(
        out,
        "# {}; type refs {}{}",
        counts.join(", "),
        clr.type_refs,
        if clr.capped {
            "; capped: a table or #US held more than was read"
        } else {
            ""
        }
    );
    let start = filter.offset.min(total);
    let page: Vec<&&Row> = kept.iter().skip(start).take(filter.limit).collect();
    let _ = writeln!(
        out,
        "# showing {} of {total} from {start}; borer://clr/<kind or text> narrows (kinds: {}), offset=<n> pages",
        page.len(),
        KINDS.join(" ")
    );
    if page.is_empty() {
        return Ok(out);
    }
    out.push_str("kind\ttoken\tva\tname\tdetail\n");
    for r in page {
        let _ = writeln!(
            out,
            "{}\t{:#010x}\t{}\t{}\t{}",
            r.kind, r.token, r.va, r.name, r.detail
        );
    }
    Ok(out)
}
