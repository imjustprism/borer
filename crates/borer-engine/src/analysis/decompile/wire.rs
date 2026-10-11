//! Wire formats: what a serializer writes onto its stream, read from its text.

use super::*;

/// Fewest serialized fields before a function earns a wire header.
///
/// One write through a stream is a helper; a run of them is a message.
pub(super) const WIRE_MIN: usize = 2;

/// Most fields listed in a wire header.
pub(super) const WIRE_FIELDS_MAX: usize = 24;

/// Heads a serializer with the wire format it reads or writes.
///
/// A message class encodes itself by taking its stream and handing it one
/// field at a time, so its own body holds the format: the order of the
/// fields, the object offset each comes from, and the bit width the call
/// asks for. Recovering that from an encoder is work an analyst does by
/// hand for every message in a protocol; the encoder states it, so the
/// header states it too, as `// wire: 1 bit this+0x20, 32 bits this+0x24`.
/// A width behind a typed helper is named by the helper instead, since the
/// width lives in the helper and not in this function.
///
/// # Arguments
///
/// * `text` - A decompiled function, before layouts.
///
/// # Returns
///
/// The text with a `// wire:` line, or unchanged when it serializes
/// nothing.
pub(super) fn wire_format(text: &str, streams: &[&str]) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let mut fields: Vec<String> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        if !stream_accessor(line, streams) {
            continue;
        }
        for step in 1..=WIRE_CALL_MAX {
            let Some(call) = lines.get(i + step) else {
                break;
            };
            if stream_accessor(call, streams) {
                break;
            }
            if let Some(f) = stream_field(&lines, i + step, call) {
                fields.push(f);
                break;
            }
        }
    }
    if fields.len() < WIRE_MIN {
        return text.to_owned();
    }
    let shown = fields.len().min(WIRE_FIELDS_MAX);
    let mut header = format!("// wire: {}", fields[..shown].join(", "));
    if fields.len() > shown {
        let _ = write!(header, " (+{} more)", fields.len() - shown);
    }
    let mut out: Vec<String> = lines.iter().map(|l| (*l).to_owned()).collect();
    out.insert(header_len(&lines), header);
    let mut joined = out.join("\n");
    joined.push('\n');
    joined
}

/// Tells whether a line takes the stream a serializer writes through: a
/// smart pointer's dereference of a class carrying a `[types] stream`
/// word.
///
/// # Arguments
///
/// * `line` - One emitted line.
/// * `streams` - The words.
pub(super) fn stream_accessor(line: &str, streams: &[&str]) -> bool {
    classes::deref_pointee(line).is_some_and(|c| streams.iter().any(|s| c.contains(s)))
}

/// Reads the field the call after a stream accessor serializes.
///
/// # Arguments
///
/// * `lines` - The function's lines.
/// * `at` - Index of the call line, which the value search runs back from.
/// * `call` - That call line.
///
/// # Returns
///
/// The field as `32 bits this+0x24`, `this+0x20 via sub_140cc9d34`, or
/// `None` when the line serializes nothing.
pub(super) fn stream_field(lines: &[&str], at: usize, call: &str) -> Option<String> {
    if let Some((width, var)) = stream_write(call) {
        let bits = if width == 1 { "1 bit" } else { "" };
        let unit = if bits.is_empty() {
            format!("{width} bits")
        } else {
            bits.to_owned()
        };
        return Some(match source_of(lines, at, &var) {
            Some(src) => format!("{unit} {src}"),
            None => unit,
        });
    }
    let (head, rest) = call.split_once('(')?;
    let name = head
        .rsplit(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == ':'))
        .next()?;
    let (_, tail) = rest.split_once(", ")?;
    let inner = tail.strip_suffix(");")?;
    let (base, off) = inner.split_once(" + ")?;
    if !matches!(base, "this" | "a1" | "a2") {
        return None;
    }
    let (off, _) = number(off)?;
    Some(format!("{base}+{} via {name}", offset_text(off)))
}

/// Reads the width and buffer of a stream write.
///
/// The call ends in the bit count and hands the stream a buffer, whether it
/// goes through a virtual slot (`vtable[21](&arg_0, 32)`) or a writer the
/// name of which resolved (`WriteBits(rax, &arg_0, 32)`). The width is the
/// argument after the buffer, since a materialized `this` can follow it,
/// and it is a bit count spelled in decimal, the way the emitter spells a
/// plain call argument: an argument spelled in hex came out of a mask or
/// an offset and is not a width.
///
/// # Arguments
///
/// * `call` - The call line.
///
/// # Returns
///
/// The bit width and the variable holding the value; `None` when the
/// argument after the buffer is not a decimal count from 1 to 64.
pub(super) fn stream_write(call: &str) -> Option<(u64, String)> {
    let inner = call.trim_end_matches(';').strip_suffix(')')?;
    let mut depth = 0i32;
    let mut open = None;
    for (i, c) in inner.char_indices().rev() {
        match c {
            ')' => depth += 1,
            '(' if depth == 0 => {
                open = Some(i);
                break;
            }
            '(' => depth -= 1,
            _ => {}
        }
    }
    let args = split_arguments(inner.get(open? + 1..)?);
    let at = args.iter().position(|a| a.starts_with('&'))?;
    let width: u64 = args.get(at + 1)?.trim().parse().ok()?;
    if !(1..=64).contains(&width) {
        return None;
    }
    Some((width, args.get(at)?.trim_start_matches('&').to_owned()))
}

/// Names where a serialized value was last read from.
///
/// # Arguments
///
/// * `lines` - The function's lines.
/// * `at` - Index of the write; the search runs backwards from there.
/// * `var` - The variable the call writes from.
///
/// # Returns
///
/// `this+0x24` when the value came from a field, else `None`.
pub(super) fn source_of(lines: &[&str], at: usize, var: &str) -> Option<String> {
    let mut want = var.to_owned();
    let mut end = at;
    for _ in 0..WIRE_HOPS_MAX {
        let head = format!("{want} = ");
        let mut found = None;
        for (k, line) in lines[..end].iter().enumerate().rev().take(WIRE_SOURCE_MAX) {
            if let Some(rest) = line.trim().strip_prefix(&head) {
                found = Some((k, rest.trim_end_matches(';').to_owned()));
                break;
            }
        }
        let (k, rest) = found?;
        if let Some((base, off)) = rest.rsplit_once(" + ")
            && let Some(base) = base.rsplit('(').next()
            && let Some((off, _)) = number(off.trim_end_matches(')'))
            && matches!(base, "this" | "a1" | "a2")
        {
            return Some(format!("{base}+{}", offset_text(off)));
        }
        want = one_register(&rest, &want)?;
        end = k;
    }
    None
}

/// Names the one register an expression reads, when it reads exactly one.
///
/// # Arguments
///
/// * `expr` - The right-hand side of an assignment.
/// * `dst` - The name being assigned; a register that keeps part of its own
///   value is being updated, not read from somewhere else.
///
/// # Returns
///
/// The register, or `None` when the expression reads none or several.
pub(super) fn one_register(expr: &str, dst: &str) -> Option<String> {
    let mut seen: Option<&str> = None;
    let mut at = 0;
    while at < expr.len() {
        let rest = expr.get(at..)?;
        let len = rest.find(|c: char| !is_ident_char(c)).unwrap_or(rest.len());
        if len == 0 {
            at += rest.chars().next().map_or(1, char::len_utf8);
            continue;
        }
        let word = rest.get(..len)?;
        at += len;
        if !is_register_name(word) || word == dst {
            continue;
        }
        if seen.is_some_and(|s| s != word) {
            return None;
        }
        seen = Some(word);
    }
    seen.map(str::to_owned)
}

/// Longest run searched back for where a serialized value came from.
pub(super) const WIRE_SOURCE_MAX: usize = 6;

/// Register copies followed back to the field a value came from.
///
/// A flag reaches the stream through a compare and a mask, so the field is
/// two or three assignments above the write.
pub(super) const WIRE_HOPS_MAX: usize = 4;

/// Longest run searched forward from a stream for the call that writes.
///
/// A value is often computed into a buffer first, so the write is not
/// always the line after the stream was taken.
pub(super) const WIRE_CALL_MAX: usize = 4;

#[cfg(test)]
mod tests {
    use super::stream_write;

    /// A width is a bit count spelled in decimal, whatever its value.
    ///
    /// The check that the count was spelled in decimal compared a hex
    /// spelling's digit count with the decimal one's, so `0x20` passed as
    /// 32 bits while `0xa` was refused: whether a mask handed to a slot
    /// read as a width depended on its value.
    ///
    /// # Panics
    ///
    /// When a decimal width is refused or a hex one is read as a width.
    #[test]
    fn a_width_is_a_decimal_bit_count() {
        assert_eq!(
            stream_write("vtable[21](&arg_0, 10);"),
            Some((10, "arg_0".to_owned()))
        );
        assert_eq!(
            stream_write("WriteBits(rax, &arg_0, 32);"),
            Some((32, "arg_0".to_owned()))
        );
        assert_eq!(
            stream_write("vtable[21](&arg_0, 32, this);"),
            Some((32, "arg_0".to_owned()))
        );
        assert_eq!(stream_write("vtable[21](&arg_0, 0xa);"), None);
        assert_eq!(stream_write("vtable[21](&arg_0, 0x20);"), None);
        assert_eq!(stream_write("vtable[21](&arg_0, 0);"), None);
        assert_eq!(stream_write("vtable[21](&arg_0, 65);"), None);
    }
}
