//! A function's disassembly block by block, written once into a [`Sink`] so
//! the plain-text listing ([`disasm_function_with`]) and the typed token
//! [`View`] ([`disasm_view`]) cannot drift.

use super::{Analysis, Overlay, disasm, name_of, short_name};
use crate::analysis::syscalls::{self, SyscallSite};
use crate::isa::Isa;
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
fn hex_prefixed<'b>(prefix: &[u8; 2], mut v: u64, buf: &'b mut [u8; 18]) -> &'b str {
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
fn hex_byte(byte: u8, buf: &mut [u8; 2]) -> &str {
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
    disasm_into(p, a, o, entry, max_instrs, bytes, &mut out)?;
    Some(out)
}

/// Renders a whole function's disassembly block by block as a typed token
/// [`View`].
///
/// Runs the exact renderer of [`disasm_function_with`] over [`Builder`], so
/// [`View::spell`] equals [`disasm_function_with`] byte for byte.
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
    disasm_into(p, a, o, entry, max_instrs, bytes, &mut b)?;
    b.finish(Unlinked::default())
}

/// Writes a function's listing into `out`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `entry` - The function's entry address.
/// * `max_instrs` - Hard cap on instructions.
/// * `bytes` - Whether the raw-bytes column is shown.
/// * `out` - The destination sink.
///
/// # Returns
///
/// `Some(())` when `entry` names a function and the architecture disassembles.
fn disasm_into<S: Sink>(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    max_instrs: usize,
    bytes: Bytes,
    out: &mut S,
) -> Option<()> {
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
    for b in &f.blocks {
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
        let shown = match x86.as_mut() {
            Some((bits, fmt)) => disasm::decode_x86(code, b.start, *bits, budget, |row| {
                ctx.write_head(row.va, row.bytes, out);
                let targets = fmt.write(&row, out, |va| a.function(va).is_some());
                ctx.write_tail(row.va, targets.branch, targets.memory, out);
            }),
            None => {
                let lines = disasm::disassemble_program(p, code, b.start, isa, budget);
                for l in &lines {
                    ctx.write_head(l.va, &l.bytes, out);
                    out.put(&l.text, Kind::Text, None);
                    ctx.write_tail(l.va, l.target, None, out);
                }
                lines.len()
            }
        };
        budget = budget.saturating_sub(shown);
        if budget == 0 {
            out.put(
                &format!("# instruction cap ({max_instrs}) reached"),
                Kind::Comment,
                None,
            );
            out.end_line();
            break;
        }
    }
    Some(())
}

/// Shared read-only inputs for rendering each instruction row.
struct RowCtx<'a> {
    /// The loaded image.
    program: &'a Program,
    /// The analysis.
    analysis: &'a Analysis,
    /// User names and comments.
    overlay: &'a Overlay,
    /// Resolved Linux syscall sites, sorted by address.
    sites: &'a [SyscallSite],
    /// Whether the bytes column is shown.
    bytes: Bytes,
}

impl RowCtx<'_> {
    /// Writes any inline user label above `va`, the address token and the
    /// optional raw-bytes column.
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
            out.put(name, Kind::Function, Some(Ref::Import(slot)));
        } else if let Ok(k) = self.sites.binary_search_by_key(&va, |s| s.at) {
            out.put("  ", Kind::Space, None);
            out.put(&format!("; {}", self.sites[k].label()), Kind::Comment, None);
        }
        if let Some(c) = o.comments.get(&va) {
            out.put("  ", Kind::Space, None);
            out.put(&format!("// {c}"), Kind::Comment, None);
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
