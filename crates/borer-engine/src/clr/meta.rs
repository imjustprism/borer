//! Metadata tokens as names: types, methods with their signatures, fields,
//! user strings and custom attributes, read on demand from the tables the
//! load located (ECMA-335 II.22 and II.23.2).
//!
//! The load keeps names, not signatures; a CIL listing names every token
//! it shows, so this reopens the metadata (cheap: the root and the table
//! stream's row counts) and reads the rows a token needs. Signatures are
//! untrusted blobs: each read is bounds-checked, nesting is capped at
//! [`DEPTH_MAX`] and a rendered name at [`super::QUALIFIED_MAX`] bytes.

use super::{
    Clr, Coded, FIELD, MEMBER_REF, METHOD_DEF, METHOD_SPEC, STAND_ALONE_SIG, TYPE_DEF, TYPE_REF,
    TYPE_SPEC, Tables, UserString, compressed, open, string,
};
use crate::num::saturating_usize;
use crate::program::Program;

/// Deepest a signature's types nest before the rest reads `...`.
const DEPTH_MAX: u8 = 16;

/// Most parameters a rendered signature lists.
const PARAMS_MAX: usize = 32;

/// A signature's calling convention bit: the method has `this` (II.23.2.1).
const HASTHIS: u8 = 0x20;

/// A signature's calling convention bit: the method is generic.
const GENERIC: u8 = 0x10;

/// The first byte of a field's signature (`FIELD`, II.23.2.4).
const FIELD_SIG: u8 = 0x06;

/// The first byte of a locals signature (`LOCAL_SIG`, II.23.2.6).
const LOCAL_SIG: u8 = 0x07;

/// The element type marking where a vararg call's extra arguments start
/// (`ELEMENT_TYPE_SENTINEL`, II.23.1.16).
const SENTINEL: u8 = 0x41;

/// A method signature, its types rendered (II.23.2.1 to II.23.2.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MethodSig {
    /// The method takes `this`: an instance method.
    pub this: bool,
    /// The return type.
    pub ret: String,
    /// The parameter types, `...` marking a vararg call's extra ones.
    pub params: Vec<String>,
}

/// A cursor over one blob.
#[derive(Debug, Clone, Copy)]
struct Blob<'a> {
    /// The blob's bytes.
    b: &'a [u8],
    /// The next byte to read.
    at: usize,
}

impl Blob<'_> {
    /// Reads one byte.
    fn byte(&mut self) -> Option<u8> {
        let v = *self.b.get(self.at)?;
        self.at += 1;
        Some(v)
    }

    /// Reads the next byte without moving.
    fn peek(&self) -> Option<u8> {
        self.b.get(self.at).copied()
    }

    /// Reads a compressed unsigned integer ([`compressed`]).
    fn uint(&mut self) -> Option<u32> {
        let (v, len) = compressed(self.b, self.at)?;
        self.at += len;
        Some(v)
    }
}

/// The metadata of a loaded assembly, reopened to name tokens.
#[derive(Debug, Clone)]
pub(crate) struct Meta<'a> {
    /// What the load read.
    pub clr: &'a Clr,
    /// The table stream.
    t: Tables<'a>,
    /// `#Strings`.
    strings: &'a [u8],
    /// `#Blob`.
    blob: &'a [u8],
}

impl<'a> Meta<'a> {
    /// Reopens a program's metadata.
    ///
    /// # Arguments
    ///
    /// * `p` - The program.
    ///
    /// # Errors
    ///
    /// When the program is no .NET assembly or its metadata was refused.
    pub(crate) fn open(p: &'a Program) -> Result<Self, String> {
        let clr = match &p.clr {
            Some(Ok(clr)) => clr,
            Some(Err(why)) => return Err(format!("the .NET metadata is refused: {why}")),
            None => {
                return Err(
                    "not a .NET assembly: the image has no CLR runtime header (data directory 14)"
                        .to_owned(),
                );
            }
        };
        let o = open(p, clr.at)?;
        Ok(Meta {
            clr,
            t: o.tables,
            strings: o.streams.strings,
            blob: o.streams.blob,
        })
    }

    /// Reads one cell, `None` for a row or column not in the table.
    fn cell(&self, table: u8, row: u32, col: usize) -> Option<u32> {
        self.t.cell(table, row, col).ok()
    }

    /// The blob a cell indexes, its compressed length read.
    fn blob_at(&self, table: u8, row: u32, col: usize) -> Option<Blob<'a>> {
        let at = saturating_usize(u64::from(self.cell(table, row, col)?));
        let (len, head) = compressed(self.blob, at)?;
        let start = at.checked_add(head)?;
        let b = self
            .blob
            .get(start..start.checked_add(saturating_usize(u64::from(len)))?)?;
        Some(Blob { b, at: 0 })
    }

    /// A type's name from a `TypeDef`, `TypeRef` or `TypeSpec` row.
    ///
    /// # Arguments
    ///
    /// * `table` - The table.
    /// * `row` - The one-based row.
    /// * `depth` - How deep in a signature this is.
    fn type_row(&self, table: u8, row: u32, depth: u8) -> String {
        let i = row
            .checked_sub(1)
            .map_or(usize::MAX, |r| saturating_usize(u64::from(r)));
        let name = match table {
            TYPE_DEF => self.clr.types.get(i).map(|t| t.name.clone()),
            TYPE_REF => self.clr.type_refs.get(i).cloned(),
            TYPE_SPEC => self
                .blob_at(TYPE_SPEC, row, 0)
                .map(|mut b| self.ty(&mut b, depth.saturating_add(1))),
            _ => None,
        };
        name.unwrap_or_else(|| format!("{:#010x}", (u32::from(table) << 24) | row))
    }

    /// Reads a `TypeDefOrRefOrSpecEncoded` (II.23.2.8) as a type's name.
    fn type_encoded(&self, b: &mut Blob<'_>, depth: u8) -> Option<String> {
        let v = b.uint()?;
        let table = [TYPE_DEF, TYPE_REF, TYPE_SPEC].get(saturating_usize(u64::from(v & 3)))?;
        Some(self.type_row(*table, v >> 2, depth))
    }

    /// Reads one type from a signature (II.23.2.12), rendered the way C#
    /// spells the built-in ones; `?` where the blob ends or names no type.
    fn ty(&self, b: &mut Blob<'_>, depth: u8) -> String {
        if depth > DEPTH_MAX {
            return "...".to_owned();
        }
        let d = depth.saturating_add(1);
        let Some(et) = b.byte() else {
            return "?".to_owned();
        };
        let word = match et {
            0x01 => "void",
            0x02 => "bool",
            0x03 => "char",
            0x04 => "sbyte",
            0x05 => "byte",
            0x06 => "short",
            0x07 => "ushort",
            0x08 => "int",
            0x09 => "uint",
            0x0a => "long",
            0x0b => "ulong",
            0x0c => "float",
            0x0d => "double",
            0x0e => "string",
            0x16 => "typedref",
            0x18 => "nint",
            0x19 => "nuint",
            0x1c => "object",
            _ => "",
        };
        if !word.is_empty() {
            return word.to_owned();
        }
        let text = match et {
            0x0f => Some(format!("{}*", self.ty(b, d))),
            0x10 => Some(format!("{}&", self.ty(b, d))),
            0x11 | 0x12 => self.type_encoded(b, d),
            0x13 => b.uint().map(|n| format!("!{n}")),
            0x1e => b.uint().map(|n| format!("!!{n}")),
            0x14 => self.array(b, d),
            0x15 => self.generic(b, d),
            0x1b => self
                .method_sig(b, d)
                .map(|s| format!("method {}", sig_text(&s, "*"))),
            0x1d => Some(format!("{}[]", self.ty(b, d))),
            0x1f | 0x20 => self.type_encoded(b, d).map(|_| self.ty(b, d)),
            0x45 => Some(format!("pinned {}", self.ty(b, d))),
            _ => None,
        };
        text.unwrap_or_else(|| "?".to_owned())
    }

    /// Reads a general array's shape after its element type (II.23.2.13).
    fn array(&self, b: &mut Blob<'_>, depth: u8) -> Option<String> {
        let elem = self.ty(b, depth);
        let rank = b.uint()?;
        for _ in 0..2 {
            let n = b.uint()?;
            for _ in 0..n {
                b.uint()?;
            }
        }
        let commas = ",".repeat(saturating_usize(u64::from(rank.saturating_sub(1))).min(32));
        Some(format!("{elem}[{commas}]"))
    }

    /// Reads a generic instantiation after `GENERICINST` (II.23.2.12).
    fn generic(&self, b: &mut Blob<'_>, depth: u8) -> Option<String> {
        b.byte()?;
        let base = self.type_encoded(b, depth)?;
        let n = b.uint()?;
        let args = self.types(b, n, depth)?;
        Some(format!("{base}<{}>", args.join(",")))
    }

    /// Reads `n` types, at most [`PARAMS_MAX`] of them kept, `None` when
    /// the blob ends first.
    fn types(&self, b: &mut Blob<'_>, n: u32, depth: u8) -> Option<Vec<String>> {
        let mut out = Vec::new();
        for i in 0..n {
            b.peek()?;
            if b.peek() == Some(SENTINEL) {
                b.byte();
                out.push("...".to_owned());
            }
            let t = self.ty(b, depth);
            if saturating_usize(u64::from(i)) < PARAMS_MAX {
                out.push(t);
            }
        }
        if saturating_usize(u64::from(n)) > PARAMS_MAX {
            out.push("...".to_owned());
        }
        Some(out)
    }

    /// Reads a method signature from its calling convention byte on.
    fn method_sig(&self, b: &mut Blob<'_>, depth: u8) -> Option<MethodSig> {
        let cc = b.byte()?;
        if cc & GENERIC != 0 {
            b.uint()?;
        }
        let n = b.uint()?;
        let ret = self.ty(b, depth);
        let params = self.types(b, n, depth)?;
        Some(MethodSig {
            this: cc & HASTHIS != 0,
            ret,
            params,
        })
    }

    /// A method's signature, from its `MethodDef` or `MemberRef` token; a
    /// `MethodSpec`'s is its generic method's.
    ///
    /// # Returns
    ///
    /// The signature, `None` for another token, a row not in the table or
    /// a blob that does not read as a method's.
    #[must_use]
    pub(crate) fn sig(&self, token: u32) -> Option<MethodSig> {
        let (table, row) = split(token);
        let mut b = match table {
            METHOD_DEF => self.blob_at(METHOD_DEF, row, 4)?,
            MEMBER_REF => self.blob_at(MEMBER_REF, row, 2)?,
            METHOD_SPEC => return self.sig(self.spec_method(row)?),
            _ => return None,
        };
        (b.peek()? != FIELD_SIG)
            .then(|| self.method_sig(&mut b, 0))
            .flatten()
    }

    /// The generic method a `MethodSpec` row instantiates, as a token.
    fn spec_method(&self, row: u32) -> Option<u32> {
        let (table, r) = Coded::MethodDefOrRef.split(self.cell(METHOD_SPEC, row, 0)?)?;
        Some((u32::from(table) << 24) | r)
    }

    /// A method's or field's bare name, `Owner::Name`, from its token.
    ///
    /// # Returns
    ///
    /// The name, `None` for a token naming no method or field this reads.
    #[must_use]
    pub(crate) fn member_name(&self, token: u32) -> Option<String> {
        let (table, row) = split(token);
        let i = saturating_usize(u64::from(row.checked_sub(1)?));
        match table {
            METHOD_DEF => Some(self.clr.methods.get(i)?.name.clone()),
            MEMBER_REF => {
                let name = &self.clr.member_refs.get(i)?.name;
                match Coded::MemberRefParent.split(self.cell(MEMBER_REF, row, 0)?)? {
                    (TYPE_SPEC, spec) => {
                        let member = name.rsplit_once("::").map_or(name.as_str(), |(_, m)| m);
                        Some(format!("{}::{member}", self.type_row(TYPE_SPEC, spec, 0)))
                    }
                    _ => Some(name.clone()),
                }
            }
            METHOD_SPEC => self.member_name(self.spec_method(row)?),
            FIELD => Some(self.field_name(row)),
            _ => None,
        }
    }

    /// A field's `Owner::name`; its owner is the type whose field list
    /// holds the row.
    fn field_name(&self, row: u32) -> String {
        let name = self
            .cell(FIELD, row, 1)
            .and_then(|i| string(self.strings, i, &|| String::new()).ok())
            .unwrap_or_else(|| "?".to_owned());
        let owner = (1..=self.t.readable(TYPE_DEF))
            .take_while(|ty| {
                self.cell(TYPE_DEF, *ty, 4)
                    .is_some_and(|first| first <= row)
            })
            .last()
            .map_or_else(|| "?".to_owned(), |ty| self.type_row(TYPE_DEF, ty, 0));
        format!("{owner}::{name}")
    }

    /// A token as a CIL listing shows it: a type's name, a method as
    /// `ret Owner::Name(params)`, a field as `type Owner::name`, a user
    /// string quoted, a signature as its types.
    ///
    /// # Arguments
    ///
    /// * `token` - The token.
    ///
    /// # Returns
    ///
    /// The text; the token in hex with `?` when it names no row this reads.
    #[must_use]
    pub(crate) fn token(&self, token: u32) -> String {
        let (table, row) = split(token);
        let text = match table {
            TYPE_DEF | TYPE_REF | TYPE_SPEC => Some(self.type_row(table, row, 0)),
            METHOD_DEF | MEMBER_REF | METHOD_SPEC => self.method_text(token),
            FIELD => {
                let ty = self.blob_at(FIELD, row, 2).map(|b| self.field_type(b));
                Some(format!(
                    "{} {}",
                    ty.as_deref().unwrap_or("?"),
                    self.field_name(row)
                ))
            }
            STAND_ALONE_SIG => self.blob_at(STAND_ALONE_SIG, row, 0).and_then(|mut b| {
                if b.peek()? == LOCAL_SIG {
                    b.byte();
                    let n = b.uint()?;
                    Some(format!("locals({})", self.types(&mut b, n, 0)?.join(", ")))
                } else {
                    self.method_sig(&mut b, 0).map(|s| sig_text(&s, "method"))
                }
            }),
            0x70 => self
                .user_string(token)
                .map(|s| format!("\"{}\"", s.hit().text)),
            _ => None,
        };
        let mut left = usize::MAX;
        super::kept(&mut left, text.unwrap_or_else(|| format!("{token:#010x}?")))
    }

    /// A method token as `ret Owner::Name(params)`, a `MethodSpec` with
    /// its type arguments after the name.
    fn method_text(&self, token: u32) -> Option<String> {
        let (table, row) = split(token);
        let mut name = self.member_name(token)?;
        if table == METHOD_SPEC
            && let Some(mut b) = self.blob_at(METHOD_SPEC, row, 1)
        {
            b.byte();
            let n = b.uint().unwrap_or(0);
            if let Some(args) = self.types(&mut b, n, 0) {
                name = format!("{name}<{}>", args.join(","));
            }
        }
        if let Some(s) = self.sig(token) {
            return Some(sig_text(&s, &name));
        }
        let field = (table == MEMBER_REF)
            .then(|| self.blob_at(MEMBER_REF, row, 2))
            .flatten()
            .filter(|b| b.peek() == Some(FIELD_SIG));
        Some(match field {
            Some(b) => format!("{} {name}", self.field_type(b)),
            None => name,
        })
    }

    /// A field signature's type (II.23.2.4), its `FIELD` byte first.
    fn field_type(&self, mut b: Blob<'_>) -> String {
        b.byte();
        self.ty(&mut b, 0)
    }

    /// A user string by its token.
    #[must_use]
    pub(crate) fn user_string(&self, token: u32) -> Option<&'a UserString> {
        let all = &self.clr.user_strings;
        all.binary_search_by_key(&token, |s| s.token)
            .ok()
            .and_then(|i| all.get(i))
    }
}

/// Splits a token into its table and row.
#[must_use]
fn split(token: u32) -> (u8, u32) {
    let [table, ..] = token.to_be_bytes();
    (table, token & 0x00ff_ffff)
}

/// A signature as `ret name(params)`.
fn sig_text(s: &MethodSig, name: &str) -> String {
    format!("{} {name}({})", s.ret, s.params.join(", "))
}
