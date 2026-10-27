//! CIL method bodies: the header and exception clauses of ECMA-335
//! II.25.4 and the instructions of Partition III.
//!
//! The bytes are untrusted: a body whose header, code or clauses run past
//! what was read is refused with the reason, and decoding stops at the
//! first byte that is no opcode or the first operand that runs past the
//! code, saying where; nothing panics and nothing reads past its slice.

use crate::num::{saturating_usize, u16_le, u32_le, u64_le};

/// Most bytes of code one body is read for; a longer body is refused.
pub const CODE_MAX: usize = 1 << 20;

/// Most exception clauses read from one body.
const CLAUSES_MAX: usize = 4096;

/// Most data sections followed after one body's code.
const SECTIONS_MAX: usize = 16;

/// The tiny header's format bits (`CorILMethod_TinyFormat`, II.25.4.2).
const TINY: u8 = 0x2;

/// The fat header's format bits (`CorILMethod_FatFormat`, II.25.4.3).
const FAT: u8 = 0x3;

/// The fat header's flag: data sections follow the code
/// (`CorILMethod_MoreSects`).
const MORE_SECTS: u16 = 0x8;

/// The fat header's flag: locals start zeroed (`CorILMethod_InitLocals`).
const INIT_LOCALS: u16 = 0x10;

/// A data section's kind bit: it holds exception clauses
/// (`CorILMethod_Sect_EHTable`, II.25.4.5).
const SECT_EH: u8 = 0x1;

/// A data section's kind bit: its clauses are fat (`CorILMethod_Sect_FatFormat`).
const SECT_FAT: u8 = 0x40;

/// A data section's kind bit: another section follows
/// (`CorILMethod_Sect_MoreSects`).
const SECT_MORE: u8 = 0x80;

/// The prefix byte of the two-byte opcodes (III.1.2.1).
pub const PREFIX: u8 = 0xfe;

/// The one-byte opcodes' names, by opcode; empty where none is defined
/// (III.1.9 and the opcode table of Partition III).
const ONE: [&str; 0xe1] = [
    "nop",
    "break",
    "ldarg.0",
    "ldarg.1",
    "ldarg.2",
    "ldarg.3",
    "ldloc.0",
    "ldloc.1",
    "ldloc.2",
    "ldloc.3",
    "stloc.0",
    "stloc.1",
    "stloc.2",
    "stloc.3",
    "ldarg.s",
    "ldarga.s",
    "starg.s",
    "ldloc.s",
    "ldloca.s",
    "stloc.s",
    "ldnull",
    "ldc.i4.m1",
    "ldc.i4.0",
    "ldc.i4.1",
    "ldc.i4.2",
    "ldc.i4.3",
    "ldc.i4.4",
    "ldc.i4.5",
    "ldc.i4.6",
    "ldc.i4.7",
    "ldc.i4.8",
    "ldc.i4.s",
    "ldc.i4",
    "ldc.i8",
    "ldc.r4",
    "ldc.r8",
    "",
    "dup",
    "pop",
    "jmp",
    "call",
    "calli",
    "ret",
    "br.s",
    "brfalse.s",
    "brtrue.s",
    "beq.s",
    "bge.s",
    "bgt.s",
    "ble.s",
    "blt.s",
    "bne.un.s",
    "bge.un.s",
    "bgt.un.s",
    "ble.un.s",
    "blt.un.s",
    "br",
    "brfalse",
    "brtrue",
    "beq",
    "bge",
    "bgt",
    "ble",
    "blt",
    "bne.un",
    "bge.un",
    "bgt.un",
    "ble.un",
    "blt.un",
    "switch",
    "ldind.i1",
    "ldind.u1",
    "ldind.i2",
    "ldind.u2",
    "ldind.i4",
    "ldind.u4",
    "ldind.i8",
    "ldind.i",
    "ldind.r4",
    "ldind.r8",
    "ldind.ref",
    "stind.ref",
    "stind.i1",
    "stind.i2",
    "stind.i4",
    "stind.i8",
    "stind.r4",
    "stind.r8",
    "add",
    "sub",
    "mul",
    "div",
    "div.un",
    "rem",
    "rem.un",
    "and",
    "or",
    "xor",
    "shl",
    "shr",
    "shr.un",
    "neg",
    "not",
    "conv.i1",
    "conv.i2",
    "conv.i4",
    "conv.i8",
    "conv.r4",
    "conv.r8",
    "conv.u4",
    "conv.u8",
    "callvirt",
    "cpobj",
    "ldobj",
    "ldstr",
    "newobj",
    "castclass",
    "isinst",
    "conv.r.un",
    "",
    "",
    "unbox",
    "throw",
    "ldfld",
    "ldflda",
    "stfld",
    "ldsfld",
    "ldsflda",
    "stsfld",
    "stobj",
    "conv.ovf.i1.un",
    "conv.ovf.i2.un",
    "conv.ovf.i4.un",
    "conv.ovf.i8.un",
    "conv.ovf.u1.un",
    "conv.ovf.u2.un",
    "conv.ovf.u4.un",
    "conv.ovf.u8.un",
    "conv.ovf.i.un",
    "conv.ovf.u.un",
    "box",
    "newarr",
    "ldlen",
    "ldelema",
    "ldelem.i1",
    "ldelem.u1",
    "ldelem.i2",
    "ldelem.u2",
    "ldelem.i4",
    "ldelem.u4",
    "ldelem.i8",
    "ldelem.i",
    "ldelem.r4",
    "ldelem.r8",
    "ldelem.ref",
    "stelem.i",
    "stelem.i1",
    "stelem.i2",
    "stelem.i4",
    "stelem.i8",
    "stelem.r4",
    "stelem.r8",
    "stelem.ref",
    "ldelem",
    "stelem",
    "unbox.any",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "conv.ovf.i1",
    "conv.ovf.u1",
    "conv.ovf.i2",
    "conv.ovf.u2",
    "conv.ovf.i4",
    "conv.ovf.u4",
    "conv.ovf.i8",
    "conv.ovf.u8",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "refanyval",
    "ckfinite",
    "",
    "",
    "mkrefany",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "ldtoken",
    "conv.u2",
    "conv.u1",
    "conv.i",
    "conv.ovf.i",
    "conv.ovf.u",
    "add.ovf",
    "add.ovf.un",
    "mul.ovf",
    "mul.ovf.un",
    "sub.ovf",
    "sub.ovf.un",
    "endfinally",
    "leave",
    "leave.s",
    "stind.i",
    "conv.u",
];

/// The two-byte opcodes' names, by second byte; empty where none is
/// defined.
const TWO: [&str; 0x1f] = [
    "arglist",
    "ceq",
    "cgt",
    "cgt.un",
    "clt",
    "clt.un",
    "ldftn",
    "ldvirtftn",
    "",
    "ldarg",
    "ldarga",
    "starg",
    "ldloc",
    "ldloca",
    "stloc",
    "localloc",
    "",
    "endfilter",
    "unaligned.",
    "volatile.",
    "tail.",
    "initobj",
    "constrained.",
    "cpblk",
    "initblk",
    "no.",
    "rethrow",
    "",
    "sizeof",
    "refanytype",
    "readonly.",
];

/// What follows an opcode (the operand types of III.1.9).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Arg {
    /// Nothing.
    None,
    /// A signed byte (`ldc.i4.s`).
    I8,
    /// An unsigned byte: an argument or local index, or a prefix's flags.
    U8,
    /// An unsigned two-byte argument or local index.
    U16,
    /// A four-byte integer.
    I32,
    /// An eight-byte integer.
    I64,
    /// A four-byte float.
    R4,
    /// An eight-byte float.
    R8,
    /// A metadata token.
    Token,
    /// A one-byte branch offset from the next instruction.
    BrS,
    /// A four-byte branch offset from the next instruction.
    Br,
    /// A count, then that many four-byte offsets from the end of the list.
    Switch,
}

/// The operand an opcode takes.
///
/// # Arguments
///
/// * `op` - The opcode, a two-byte one as `0xfe00` plus its second byte.
fn arg(op: u16) -> Arg {
    match op {
        0x0e..=0x13 | 0xfe12 | 0xfe19 => Arg::U8,
        0x1f => Arg::I8,
        0x20 => Arg::I32,
        0x21 => Arg::I64,
        0x22 => Arg::R4,
        0x23 => Arg::R8,
        0x27..=0x29
        | 0x6f..=0x75
        | 0x79
        | 0x7b..=0x81
        | 0x8c
        | 0x8d
        | 0x8f
        | 0xa3..=0xa5
        | 0xc2
        | 0xc6
        | 0xd0
        | 0xfe06
        | 0xfe07
        | 0xfe15
        | 0xfe16
        | 0xfe1c => Arg::Token,
        0x2b..=0x37 | 0xde => Arg::BrS,
        0x38..=0x44 | 0xdd => Arg::Br,
        0x45 => Arg::Switch,
        0xfe09..=0xfe0e => Arg::U16,
        _ => Arg::None,
    }
}

/// The name of an opcode.
///
/// # Arguments
///
/// * `op` - The opcode, a two-byte one as `0xfe00` plus its second byte.
///
/// # Returns
///
/// Its mnemonic, or `None` for a byte Partition III defines no opcode for.
#[must_use]
pub fn name(op: u16) -> Option<&'static str> {
    let [hi, lo] = op.to_be_bytes();
    let table: &[&str] = match hi {
        0 => &ONE,
        PREFIX => &TWO,
        _ => return None,
    };
    table
        .get(usize::from(lo))
        .copied()
        .filter(|n| !n.is_empty())
}

/// What kind of handler an exception clause has (II.25.4.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClauseKind {
    /// A typed handler (`COR_ILEXCEPTION_CLAUSE_EXCEPTION`), catching the
    /// class [`Clause::extra`] names.
    Catch,
    /// A filter (`COR_ILEXCEPTION_CLAUSE_FILTER`) whose code starts at
    /// [`Clause::extra`].
    Filter,
    /// A finally handler.
    Finally,
    /// A fault handler.
    Fault,
}

impl ClauseKind {
    /// The word a listing prints.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Self::Catch => "catch",
            Self::Filter => "filter",
            Self::Finally => "finally",
            Self::Fault => "fault",
        }
    }
}

/// One exception clause: a protected range and its handler, both as code
/// offsets with the end exclusive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Clause {
    /// The handler's kind.
    pub kind: ClauseKind,
    /// The protected range's first byte.
    pub try_start: u32,
    /// One past the protected range's last byte.
    pub try_end: u32,
    /// The handler's first byte.
    pub handler_start: u32,
    /// One past the handler's last byte.
    pub handler_end: u32,
    /// A [`ClauseKind::Catch`]'s class token or a [`ClauseKind::Filter`]'s
    /// code offset; `0` otherwise.
    pub extra: u32,
}

/// A method body's header and clauses (II.25.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodBody {
    /// The header is fat (12 bytes) rather than tiny (1 byte).
    pub fat: bool,
    /// The deepest the evaluation stack gets: 8 for a tiny header.
    pub max_stack: u16,
    /// Locals start zeroed.
    pub init_locals: bool,
    /// The locals' `StandAloneSig` token, `0` for none.
    pub locals: u32,
    /// Bytes of header before the code.
    pub header_len: usize,
    /// Bytes of code.
    pub code_len: usize,
    /// The exception clauses, in the order the sections list them.
    pub clauses: Vec<Clause>,
}

/// Rounds an offset up to the next multiple of four.
fn align4(at: usize) -> Option<usize> {
    at.checked_add(3).map(|a| a & !3)
}

/// Reads one exception clause, small or fat (II.25.4.6).
///
/// # Arguments
///
/// * `c` - The clause's bytes, 12 for a small clause and 24 for a fat one.
/// * `fat` - The clause is fat.
///
/// # Errors
///
/// When its flags name no kind.
fn clause(c: &[u8], fat: bool) -> Result<Clause, String> {
    let short = || "an exception clause ends early".to_owned();
    let (flags, try_start, try_len, handler_start, handler_len, extra) = if fat {
        let w = |i: usize| u32_le(c, i * 4).ok_or_else(short);
        (w(0)?, w(1)?, w(2)?, w(3)?, w(4)?, w(5)?)
    } else {
        let h = |i: usize| u16_le(c, i).map(u32::from).ok_or_else(short);
        let b = |i: usize| c.get(i).copied().map(u32::from).ok_or_else(short);
        (
            h(0)?,
            h(2)?,
            b(4)?,
            h(5)?,
            b(7)?,
            u32_le(c, 8).ok_or_else(short)?,
        )
    };
    let kind = match flags {
        0 => ClauseKind::Catch,
        1 => ClauseKind::Filter,
        2 => ClauseKind::Finally,
        4 => ClauseKind::Fault,
        _ => {
            return Err(format!(
                "an exception clause's flags are {flags:#x}, no kind II.25.4.6 names"
            ));
        }
    };
    Ok(Clause {
        kind,
        try_start,
        try_end: try_start.saturating_add(try_len),
        handler_start,
        handler_end: handler_start.saturating_add(handler_len),
        extra: if matches!(kind, ClauseKind::Catch | ClauseKind::Filter) {
            extra
        } else {
            0
        },
    })
}

/// Reads the data sections after a fat body's code (II.25.4.5).
///
/// # Arguments
///
/// * `bytes` - The body from its header.
/// * `from` - Where the code ends.
///
/// # Errors
///
/// When a section runs past `bytes`, states fewer bytes than its header, or
/// holds a clause that does not read.
fn sections(bytes: &[u8], from: usize) -> Result<Vec<Clause>, String> {
    let mut clauses = Vec::new();
    let mut at = align4(from).ok_or("the code's end overflows")?;
    for _ in 0..SECTIONS_MAX {
        let kind = *bytes
            .get(at)
            .ok_or_else(|| format!("a data section at body offset {at:#x} is past the body"))?;
        let fat = kind & SECT_FAT != 0;
        let size = if fat {
            bytes.get(at + 1..at + 4).map(|b| {
                b.iter()
                    .rev()
                    .fold(0usize, |n, x| (n << 8) | usize::from(*x))
            })
        } else {
            bytes.get(at + 1).copied().map(usize::from)
        }
        .filter(|s| *s >= 4)
        .ok_or_else(|| format!("the data section at body offset {at:#x} states no size"))?;
        let section = at
            .checked_add(size)
            .and_then(|end| bytes.get(at + 4..end))
            .ok_or_else(|| {
                format!(
                    "the data section at body offset {at:#x}, {size:#x} bytes, runs past the body"
                )
            })?;
        if kind & SECT_EH != 0 {
            let stride = if fat { 24 } else { 12 };
            for c in section.chunks_exact(stride) {
                if clauses.len() >= CLAUSES_MAX {
                    return Err(format!("more than {CLAUSES_MAX} exception clauses"));
                }
                clauses.push(clause(c, fat)?);
            }
        }
        if kind & SECT_MORE == 0 {
            return Ok(clauses);
        }
        at = align4(at + size).ok_or("a data section's end overflows")?;
    }
    Err(format!("more than {SECTIONS_MAX} data sections"))
}

/// Reads a method body's header and exception clauses.
///
/// # Arguments
///
/// * `bytes` - The body from its first byte; it may run on past the body.
///
/// # Returns
///
/// The header and clauses, and the code.
///
/// # Errors
///
/// As [`header`], or when a data section does not read.
pub fn body(bytes: &[u8]) -> Result<(MethodBody, &[u8]), String> {
    let (mut b, code) = header(bytes)?;
    if b.fat && u16_le(bytes, 0).is_some_and(|f| f & MORE_SECTS != 0) {
        b.clauses = sections(bytes, b.header_len + b.code_len)?;
    }
    Ok((b, code))
}

/// Reads a method body's header and finds its code, its exception clauses
/// unread.
///
/// # Arguments
///
/// * `bytes` - The body from its first byte; it may run on past the body.
///
/// # Returns
///
/// The header, its clauses empty, and the code.
///
/// # Errors
///
/// When the format bits name neither header, or the header or code runs
/// past `bytes` or past [`CODE_MAX`].
pub fn header(bytes: &[u8]) -> Result<(MethodBody, &[u8]), String> {
    let first = *bytes.first().ok_or("the body is empty")?;
    let (b, code_at) = match first & 0x3 {
        TINY => (
            MethodBody {
                fat: false,
                max_stack: 8,
                init_locals: false,
                locals: 0,
                header_len: 1,
                code_len: usize::from(first >> 2),
                clauses: Vec::new(),
            },
            1,
        ),
        FAT => {
            let short = || "the fat header runs past the body".to_owned();
            let flags = u16_le(bytes, 0).ok_or_else(short)?;
            let len = usize::from(flags >> 12) * 4;
            if len < 12 {
                return Err(format!(
                    "the fat header states {len} bytes, fewer than its 12"
                ));
            }
            let code_len = saturating_usize(u64::from(u32_le(bytes, 4).ok_or_else(short)?));
            let b = MethodBody {
                fat: true,
                max_stack: u16_le(bytes, 2).ok_or_else(short)?,
                init_locals: flags & INIT_LOCALS != 0,
                locals: u32_le(bytes, 8).ok_or_else(short)?,
                header_len: len,
                code_len,
                clauses: Vec::new(),
            };
            (b, len)
        }
        bits => {
            return Err(format!(
                "the header's format bits are {bits:#x}, neither tiny nor fat"
            ));
        }
    };
    if b.code_len > CODE_MAX {
        return Err(format!(
            "the body states {} bytes of code, more than {CODE_MAX} read",
            b.code_len
        ));
    }
    let end = code_at + b.code_len;
    let code = bytes.get(code_at..end).ok_or_else(|| {
        format!(
            "the body's {} bytes of code run past the {} read",
            b.code_len,
            bytes.len()
        )
    })?;
    Ok((b, code))
}

/// An instruction's operand.
#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    /// None.
    None,
    /// An integer constant.
    Int(i64),
    /// An argument or local index, or a prefix's flags.
    Var(u16),
    /// A float constant.
    Real(f64),
    /// A metadata token.
    Token(u32),
    /// A branch target, as a code offset; it may lie outside the code.
    Target(i64),
    /// A switch's targets, as code offsets.
    Switch(Vec<i64>),
}

/// One decoded instruction.
#[derive(Debug, Clone, PartialEq)]
pub struct Instr {
    /// Its offset in the code.
    pub off: u32,
    /// Its opcode, a two-byte one as `0xfe00` plus its second byte.
    pub op: u16,
    /// Its operand.
    pub operand: Operand,
    /// Its length in bytes.
    pub len: u32,
}

impl Instr {
    /// The instruction's mnemonic.
    #[must_use]
    pub fn name(&self) -> &'static str {
        name(self.op).unwrap_or("?")
    }
}

/// Reads one instruction's operand.
///
/// # Arguments
///
/// * `code` - The code.
/// * `at` - Where the operand starts.
/// * `a` - The operand's type.
///
/// # Returns
///
/// The operand and where the instruction ends, or `None` when the operand
/// runs past the code.
fn operand(code: &[u8], at: usize, a: Arg) -> Option<(Operand, usize)> {
    let next = |n: usize| at.checked_add(n).filter(|e| *e <= code.len());
    let rel = |end: usize, d: i64| i64::try_from(end).ok().map(|e| e.saturating_add(d));
    Some(match a {
        Arg::None => (Operand::None, at),
        Arg::I8 => (
            Operand::Int(i64::from(i8::from_le_bytes([*code.get(at)?]))),
            next(1)?,
        ),
        Arg::U8 => (Operand::Var(u16::from(*code.get(at)?)), next(1)?),
        Arg::U16 => (Operand::Var(u16_le(code, at)?), next(2)?),
        Arg::I32 => (
            Operand::Int(i64::from(u32_le(code, at)?.cast_signed())),
            next(4)?,
        ),
        Arg::I64 => (Operand::Int(u64_le(code, at)?.cast_signed()), next(8)?),
        Arg::R4 => (
            Operand::Real(f64::from(f32::from_bits(u32_le(code, at)?))),
            next(4)?,
        ),
        Arg::R8 => (Operand::Real(f64::from_bits(u64_le(code, at)?)), next(8)?),
        Arg::Token => (Operand::Token(u32_le(code, at)?), next(4)?),
        Arg::BrS => {
            let end = next(1)?;
            (
                Operand::Target(rel(end, i64::from(i8::from_le_bytes([*code.get(at)?])))?),
                end,
            )
        }
        Arg::Br => {
            let end = next(4)?;
            (
                Operand::Target(rel(end, i64::from(u32_le(code, at)?.cast_signed()))?),
                end,
            )
        }
        Arg::Switch => {
            let n = saturating_usize(u64::from(u32_le(code, at)?));
            let end = n.checked_mul(4).and_then(|len| next(4 + len))?;
            let targets = (0..n)
                .map(|i| rel(end, i64::from(u32_le(code, at + 4 + i * 4)?.cast_signed())))
                .collect::<Option<Vec<_>>>()?;
            (Operand::Switch(targets), end)
        }
    })
}

/// Decodes a body's code.
///
/// # Arguments
///
/// * `code` - The code, at most [`CODE_MAX`] bytes as [`body`] returns it.
///
/// # Returns
///
/// The instructions in code order, and why decoding stopped early: at a
/// byte that is no opcode or an operand that runs past the code.
#[must_use]
pub fn decode(code: &[u8]) -> (Vec<Instr>, Option<String>) {
    let mut out = Vec::new();
    let mut at = 0usize;
    while let Some(&b) = code.get(at) {
        let (op, after) = if b == PREFIX {
            match code.get(at + 1) {
                Some(&second) => (u16::from_be_bytes([PREFIX, second]), at + 2),
                None => {
                    return (
                        out,
                        Some(format!("IL_{at:04x}: a two-byte opcode is cut off")),
                    );
                }
            }
        } else {
            (u16::from(b), at + 1)
        };
        if name(op).is_none() {
            return (out, Some(format!("IL_{at:04x}: {op:#x} is no opcode")));
        }
        let Some((operand, end)) = operand(code, after, arg(op)) else {
            return (
                out,
                Some(format!("IL_{at:04x}: the operand runs past the code")),
            );
        };
        out.push(Instr {
            off: u32::try_from(at).unwrap_or(u32::MAX),
            op,
            operand,
            len: u32::try_from(end - at).unwrap_or(u32::MAX),
        });
        at = end;
    }
    (out, None)
}
