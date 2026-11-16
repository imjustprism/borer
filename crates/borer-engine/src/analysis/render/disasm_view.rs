//! A function's disassembly block by block, written once into a [`Sink`] so
//! the plain-text listing ([`disasm_function_with`]) and the typed token
//! [`View`] ([`disasm_view`]) cannot drift.

use super::{Analysis, BasicBlock, Overlay, disasm, name_of, short_name};
use crate::analysis::decompile::lexer::{self, Lex, Piece};
use crate::analysis::decompile::view::{import_id, said};
use crate::analysis::syscalls::{self, SyscallSite};
use crate::isa::{Isa, a32, a64, rv};
use crate::num::from_usize;
use crate::program::{Feature, Program, SymbolKind};
use crate::view::{Builder, Kind, Ref, Sink, Unlinked, View};

/// Twenty-five spaces, the widest pad after an empty bytes column.
const BYTE_PAD: &str = "                         ";

/// Lowercase hexadecimal digits for zero-allocation row formatting.
const HEX: [u8; 16] = *b"0123456789abcdef";

/// Formats `v` in lowercase hexadecimal after `prefix` (`b"0x"` or `b"L_"`)
/// into `buf`.
///
/// # Arguments
///
/// * `prefix` - Two-byte ASCII prefix.
/// * `v` - Unsigned value to format.
/// * `buf` - Scratch buffer holding up to 18 bytes.
pub(super) fn hex_prefixed<'b>(prefix: &[u8; 2], mut v: u64, buf: &'b mut [u8; 18]) -> &'b str {
    let mut i = buf.len();
    loop {
        i -= 1;
        let d = usize::try_from(v & 0xf).unwrap_or(0);
        buf[i] = HEX[d];
        v >>= 4;
        if v == 0 {
            break;
        }
    }
    i -= 2;
    buf[i] = prefix[0];
    buf[i + 1] = prefix[1];
    std::str::from_utf8(&buf[i..]).unwrap_or_default()
}

/// Formats `byte` as two lowercase hexadecimal digits into `buf`.
///
/// # Arguments
///
/// * `byte` - Encoded instruction byte.
/// * `buf` - Two-byte scratch buffer.
pub(super) fn hex_byte(byte: u8, buf: &mut [u8; 2]) -> &str {
    buf[0] = HEX[usize::from(byte >> 4)];
    buf[1] = HEX[usize::from(byte & 0x0f)];
    std::str::from_utf8(buf).unwrap_or_default()
}

/// Whether a listing shows the encoded bytes beside each instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bytes {
    /// Address and text only.
    Hidden,
    /// A hex column between the address and the text.
    Shown,
}

/// Renders a whole function's disassembly block by block.
///
/// [`disasm_function_with`] with the bytes column as a flag.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the code bytes.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
/// * `max_instrs` - Hard cap on instructions; a `# instruction cap` line marks a cut.
/// * `with_bytes` - Adds the raw-bytes column.
///
/// # Returns
///
/// As [`disasm_function_with`].
#[must_use]
pub fn disasm_function(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    max_instrs: usize,
    with_bytes: bool,
) -> Option<String> {
    let bytes = if with_bytes {
        Bytes::Shown
    } else {
        Bytes::Hidden
    };
    disasm_function_with(p, a, o, entry, max_instrs, bytes)
}

/// Renders a whole function's disassembly block by block as plain text.
///
/// Block starts get `L_<addr>:` labels, overlay names and comments appear
/// inline, and branch targets that are functions or named addresses get a
/// `; name` suffix: an x86 near call or jmp whose first operand is the
/// target number, and any direct non-x86 branch whose decoder states it. A
/// Linux syscall site is tagged with its call (`; syscall socket`,
/// [`crate::analysis::syscalls`]), and a call that sends an Objective-C
/// message gets `; [recv sel]` instead of its target.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the code bytes.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
/// * `max_instrs` - Hard cap on instructions; a `# instruction cap` line marks a cut.
/// * `bytes` - Whether the raw-bytes column is shown.
///
/// # Returns
///
/// The header comment and the rows, or `None` when no function starts at
/// `entry` or the architecture has no disassembler.
#[must_use]
pub fn disasm_function_with(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    max_instrs: usize,
    bytes: Bytes,
) -> Option<String> {
    let cap = a
        .function(entry)
        .map_or(0, |f| f.instr_count.min(max_instrs).saturating_mul(48));
    let mut out = String::with_capacity(cap);
    disasm_into(p, a, o, entry, Pick::All(max_instrs), bytes, &mut out)?;
    Some(out)
}

/// Renders a whole function's disassembly block by block as a typed token
/// [`View`].
///
/// Runs the exact renderer of [`disasm_function_with`] over [`Builder`], so
/// [`View::spell`] equals [`disasm_function_with`] byte for byte, each
/// instruction's line answers its address ([`View::address`]), and each
/// link says who stated its referent's name ([`View::tokens_said`]).
///
/// # Arguments
///
/// * `p` - The loaded image, read for the code bytes.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
/// * `max_instrs` - Hard cap on instructions; a `# instruction cap` line marks a cut.
/// * `bytes` - Whether the raw-bytes column is shown.
///
/// # Returns
///
/// The view, or `None` when no function starts at `entry`, the architecture
/// has no disassembler, or the text outgrew 32-bit offsets.
#[must_use]
pub fn disasm_view(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    max_instrs: usize,
    bytes: Bytes,
) -> Option<View> {
    let mut b = Builder::default();
    disasm_into(p, a, o, entry, Pick::All(max_instrs), bytes, &mut b)?;
    b.finish(Unlinked::default())
        .map(|v| v.with_said(|r, w| said::of(p, a, o, r, w)))
}

/// Renders some of a function's blocks as a typed token [`View`], as
/// [`disasm_view`] renders them all.
///
/// The header, then each block named in `starts`, in address order, each
/// cut with a `// ... N more bytes` row
/// after its share of instructions: at most the per-block cap, and once
/// the total is spent one, so every block keeps its first row.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the code bytes.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
/// * `bytes` - Whether the raw-bytes column is shown.
/// * `starts` - The start addresses of the blocks to list, sorted.
/// * `rows` - Most instructions listed of one block, and in all.
///
/// # Returns
///
/// The view and the starts of the blocks cut short, in address order;
/// `None` as for [`disasm_view`].
#[must_use]
pub(crate) fn blocks_view(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    bytes: Bytes,
    starts: &[u64],
    (each, total): (usize, usize),
) -> Option<(View, Vec<u64>)> {
    let mut b = Builder::default();
    let short = disasm_into(
        p,
        a,
        o,
        entry,
        Pick::Blocks(starts, each, total),
        bytes,
        &mut b,
    )?;
    Some((b.finish(Unlinked::default())?, short))
}

/// Which of a function's instructions a listing shows.
#[derive(Debug, Clone, Copy)]
enum Pick<'a> {
    /// Every block, up to this many instructions in all.
    All(usize),
    /// The blocks starting at these sorted addresses, up to the first
    /// count of instructions of each and the second in all, but at least
    /// one of each.
    Blocks(&'a [u64], usize, usize),
}

/// Writes a function's listing into `out`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
/// * `pick` - Which blocks to list, and how many instructions.
/// * `bytes` - Whether the raw-bytes column is shown.
/// * `out` - The destination sink.
///
/// # Returns
///
/// The starts of the blocks cut short of their end by [`Pick::Blocks`],
/// when `entry` names a function and the architecture disassembles.
fn disasm_into<S: Sink>(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    pick: Pick<'_>,
    bytes: Bytes,
    out: &mut S,
) -> Option<Vec<u64>> {
    let (max_instrs, only, each) = match pick {
        Pick::All(n) => (n, None, None),
        Pick::Blocks(starts, n, total) => (total, Some(starts), Some(n)),
    };
    let f = a.function(entry)?;
    let isa = p.isa_for(Feature::Disasm).ok()?;
    out.put(
        &format!(
            "// {} @ {:#x}: {} instructions, {} blocks",
            name_of(a, o, f.entry),
            f.entry,
            f.instr_count,
            f.blocks.len()
        ),
        Kind::Comment,
        None,
    );
    out.end_line();
    let mut budget = max_instrs;
    let sites = syscalls::syscall_sites(p, a);
    let mut x86 = match isa {
        Isa::X86 { bits } => Some((bits, disasm::X86Format::new())),
        Isa::A64 | Isa::A32 | Isa::Rv(_) => None,
    };
    let ctx = RowCtx {
        program: p,
        analysis: a,
        overlay: o,
        sites: &sites,
        bytes,
    };
    let mut buf = [0u8; 18];
    let listed = |b: &&BasicBlock| only.is_none_or(|s| s.binary_search(&b.start).is_ok());
    let mut short = Vec::new();
    for b in f.blocks.iter().filter(listed) {
        let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(0);
        let Some(code) = p.read_va_upto(b.start, len.max(1)) else {
            continue;
        };
        if b.start != f.entry {
            out.put(
                hex_prefixed(b"L_", b.start, &mut buf),
                Kind::Label,
                Some(Ref::Address(b.start)),
            );
            out.define();
            out.put(":", Kind::Punct, None);
            out.end_line();
        }
        let room = each.map_or(budget, |n| n.min(budget).max(1));
        let mut reached = b.start;
        let shown = match x86.as_mut() {
            Some((bits, fmt)) => disasm::decode_x86(code, b.start, *bits, room, |row| {
                reached = row.va.saturating_add(from_usize(row.bytes.len()));
                ctx.x86_row(fmt, &row, out);
            }),
            None => {
                let lines = disasm::disassemble_program(p, code, b.start, isa, room);
                for l in &lines {
                    reached = l.va.saturating_add(from_usize(l.bytes.len()));
                    ctx.isa_row(l, isa, out);
                }
                lines.len()
            }
        };
        if each.is_some() && shown == room && reached < b.end {
            out.put(
                &format!("// ... {} more bytes", b.end - reached),
                Kind::Comment,
                None,
            );
            out.end_line();
            short.push(b.start);
        }
        budget = budget.saturating_sub(shown);
        if budget == 0 && each.is_none() {
            out.put(
                &format!("# instruction cap ({max_instrs}) reached"),
                Kind::Comment,
                None,
            );
            out.end_line();
            break;
        }
    }
    Some(short)
}

/// Shared read-only inputs for rendering each instruction row, the one
/// renderer of an instruction's line in a function listing and in the
/// linear listing ([`super::linear()`]).
pub(super) struct RowCtx<'a> {
    /// The loaded image.
    pub(super) program: &'a Program,
    /// The analysis.
    pub(super) analysis: &'a Analysis,
    /// User names and comments.
    pub(super) overlay: &'a Overlay,
    /// Resolved Linux syscall sites, sorted by address.
    pub(super) sites: &'a [SyscallSite],
    /// Whether the bytes column is shown.
    pub(super) bytes: Bytes,
}

impl RowCtx<'_> {
    /// Writes one decoded x86 instruction's lines: any user label, then the
    /// address, the text and the trailing annotations.
    ///
    /// # Arguments
    ///
    /// * `fmt` - The formatter, kept across a listing's instructions.
    /// * `row` - The decoded instruction.
    /// * `out` - The destination sink.
    pub(super) fn x86_row<S: Sink>(
        &self,
        fmt: &mut disasm::X86Format,
        row: &disasm::X86Decoded<'_>,
        out: &mut S,
    ) {
        self.write_head(row.va, row.bytes, out);
        let targets = fmt.write(row, out, |va| self.analysis.function(va).is_some());
        self.write_tail(row.va, targets.branch, targets.memory, out);
    }

    /// Writes one decoded instruction of an architecture other than x86:
    /// any user label, then the address, the text and the trailing
    /// annotations.
    ///
    /// # Arguments
    ///
    /// * `l` - The decoded instruction.
    /// * `isa` - The instruction set its text is written in.
    /// * `out` - The destination sink.
    pub(super) fn isa_row<S: Sink>(&self, l: &disasm::DisasmLine, isa: Isa, out: &mut S) {
        self.write_head(l.va, &l.bytes, out);
        write_isa_line(&l.text, l.target, isa, self.analysis, out);
        self.write_tail(l.va, l.target, None, out);
    }

    /// Writes any inline user label above `va`, then marks the line as
    /// showing `va` and writes the address token and the optional raw-bytes
    /// column.
    ///
    /// # Arguments
    ///
    /// * `va` - The instruction's address.
    /// * `raw` - The instruction's encoded bytes.
    /// * `out` - The destination sink.
    fn write_head<S: Sink>(&self, va: u64, raw: &[u8], out: &mut S) {
        if let Some(n) = self.overlay.names.get(&va) {
            out.put("            ", Kind::Space, None);
            out.put(&format!("; = {n} ="), Kind::Comment, None);
            out.end_line();
        }
        out.at(va);
        let mut buf = [0u8; 18];
        out.put(
            hex_prefixed(b"0x", va, &mut buf),
            Kind::Address,
            Some(Ref::Address(va)),
        );
        out.define();
        out.put("  ", Kind::Space, None);
        if self.bytes == Bytes::Shown {
            let mut pair = [0u8; 2];
            for (idx, &byte) in raw.iter().enumerate() {
                if idx > 0 {
                    out.put(" ", Kind::Space, None);
                }
                out.put(hex_byte(byte, &mut pair), Kind::Number, None);
            }
            let used = raw.len().saturating_mul(3).saturating_sub(1);
            let pad = 24usize.saturating_sub(used) + 1;
            out.put(&BYTE_PAD[..pad], Kind::Space, None);
        }
    }

    /// Writes the trailing target, import, Objective-C or syscall annotation
    /// and any user comment, then ends the line.
    ///
    /// # Arguments
    ///
    /// * `va` - The instruction's address.
    /// * `target` - Branch target eligible for a `; name` suffix.
    /// * `memory` - Bare memory operand's address, checked for an import slot.
    /// * `out` - The destination sink.
    fn write_tail<S: Sink>(&self, va: u64, target: Option<u64>, memory: Option<u64>, out: &mut S) {
        let (p, a, o) = (self.program, self.analysis, self.overlay);
        if let Some(message) = a.objc.messages.get(&va) {
            out.put("  ", Kind::Space, None);
            if let Some(r) = message.reaches
                && r.sure
                && a.function(r.imp).is_some()
            {
                out.put(&format!("; {} -> ", message.text()), Kind::Comment, None);
                out.put(
                    &name_of(a, o, r.imp),
                    Kind::Function,
                    Some(Ref::Function(r.imp)),
                );
            } else {
                out.put(&format!("; {}", message.shown(a, o)), Kind::Comment, None);
            }
        } else if let Some(target) = target
            && (a.function(target).is_some() || o.names.contains_key(&target))
        {
            out.put("  ", Kind::Space, None);
            out.put("; ", Kind::Comment, None);
            let (kind, link) = if a.function(target).is_some() {
                (Kind::Function, Ref::Function(target))
            } else {
                (Kind::Label, Ref::Address(target))
            };
            out.put(&short_name(a, o, target), kind, Some(link));
        } else if let Some((slot, name)) = import_at(p, memory) {
            out.put("  ", Kind::Space, None);
            out.put("; ", Kind::Comment, None);
            let id = import_id(p, a, slot).unwrap_or(slot);
            out.put(name, Kind::Function, Some(Ref::Import(id)));
        } else if let Ok(k) = self.sites.binary_search_by_key(&va, |s| s.at) {
            out.put("  ", Kind::Space, None);
            out.put(&format!("; {}", self.sites[k].label()), Kind::Comment, None);
        }
        if let Some(c) = o.comments.get(&va) {
            out.put("  ", Kind::Space, None);
            out.put(
                &format!("// {c}"),
                said::note_kind(c),
                Some(Ref::Comment(va)),
            );
        }
        out.end_line();
    }
}

/// Returns the import slot and name at `addr`, when `addr` is nonzero and
/// names an import symbol.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `addr` - Candidate memory operand address.
fn import_at(p: &Program, addr: Option<u64>) -> Option<(u64, &str)> {
    let addr = addr.filter(|&a| a != 0)?;
    p.symbols
        .iter()
        .find(|s| matches!(s.kind, SymbolKind::Import) && s.addr == addr)
        .map(|s| (addr, s.name.as_str()))
}

/// Tokenizes one non-x86 instruction's text into `out`, linking its branch
/// target token when `target` is present.
///
/// # Arguments
///
/// * `text` - Assembly text from [`a64::text`], [`a32::text`] or [`rv::text`].
/// * `target` - Direct branch or call target reported by the decoder.
/// * `isa` - The instruction set `text` is written in.
/// * `a` - Analysis, queried to distinguish [`Ref::Function`] from [`Ref::Address`].
/// * `out` - The destination sink.
fn write_isa_line<S: Sink>(text: &str, target: Option<u64>, isa: Isa, a: &Analysis, out: &mut S) {
    if text.is_empty() {
        return;
    }
    if text == "(bad)" {
        out.put(text, Kind::Text, None);
        return;
    }
    let (body, comment) = match text.find(';') {
        Some(idx) => (&text[..idx], Some(&text[idx..])),
        None => (text, None),
    };
    let mut mnem_end = 0;
    for (piece, span) in lexer::scan(body, 0) {
        if piece == Piece::Space {
            break;
        }
        mnem_end = span.end;
    }
    if mnem_end > 0 {
        out.put(&body[..mnem_end], Kind::Mnemonic, None);
    }
    let mut prev_punct: Option<&str> = None;
    for (piece, span) in lexer::scan(body, mnem_end) {
        let word = &body[span];
        match piece {
            Piece::Space => {
                prev_punct = None;
                out.put(word, Kind::Space, None);
            }
            Piece::Comment => {
                prev_punct = None;
                out.put(word, Kind::Comment, None);
            }
            Piece::Token(Lex::Punct) => {
                prev_punct = Some(word);
                out.put(word, Kind::Punct, None);
            }
            Piece::Token(Lex::Literal) => {
                prev_punct = None;
                out.put(word, Kind::String, None);
            }
            Piece::Token(Lex::Name) => {
                let kind = if prev_punct != Some(".") && isa_is_register(isa, word) {
                    Kind::Register
                } else {
                    Kind::Text
                };
                prev_punct = None;
                out.put(word, kind, None);
            }
            Piece::Token(Lex::Number) => {
                let link = target
                    .filter(|&t| {
                        !matches!(prev_punct, Some("#" | "-" | ".")) && parse_u64(word) == Some(t)
                    })
                    .map(|t| {
                        if a.function(t).is_some() {
                            Ref::Function(t)
                        } else {
                            Ref::Address(t)
                        }
                    });
                let kind = if link.is_some() {
                    Kind::Address
                } else {
                    Kind::Number
                };
                prev_punct = None;
                out.put(word, kind, link);
            }
        }
    }
    if let Some(c) = comment {
        out.put(c, Kind::Comment, None);
    }
}

/// Checks whether `word` is a register name of `isa`.
///
/// # Arguments
///
/// * `isa` - The instruction set.
/// * `word` - Candidate identifier token.
fn isa_is_register(isa: Isa, word: &str) -> bool {
    match isa {
        Isa::A64 => a64::is_register(word),
        Isa::A32 => a32::is_register(word),
        Isa::Rv(_) => rv::is_register(word),
        Isa::X86 { .. } => false,
    }
}

/// Parses an unsigned hexadecimal (`0x...`) or decimal literal from `word`.
///
/// # Arguments
///
/// * `word` - Numeric token spelling.
fn parse_u64(word: &str) -> Option<u64> {
    if let Some(hex) = word.strip_prefix("0x").or_else(|| word.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16).ok()
    } else {
        word.parse::<u64>().ok()
    }
}
