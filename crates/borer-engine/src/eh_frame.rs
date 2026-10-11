//! Function extents from `.eh_frame`, the DWARF call frame information a GCC
//! or Clang toolchain emits for every function it can unwind through.
//!
//! The section is a sequence of length-prefixed records: CIEs (id `0`) carry
//! the pointer encoding their FDEs use; FDEs carry `initial_location` and
//! `address_range`. The records are walked once in order and a CIE is parsed
//! the first time an FDE points at it. Stripped binaries keep this section,
//! so it seeds discovery where the symbol table cannot.
//!
//! A CIE whose augmentation names an `L` encoding also ties each of its
//! FDEs to the function's language-specific data area, which [`fdes`]
//! reads alongside the extent and [`crate::lsda`] turns into call sites.

use std::collections::BTreeMap;

/// `DW_EH_PE_omit`: no value present.
const OMIT: u8 = 0xff;
/// Escape value of a 32-bit length field announcing a 64-bit length.
const LENGTH_64: u32 = 0xffff_ffff;
/// Longest LEB128 encoding accepted (ten bytes hold 70 bits).
const LEB_MAX: u32 = 10;

/// Reads DWARF-encoded fields from a section mapped at a known address.
pub(crate) struct Cursor<'a> {
    /// Section bytes.
    pub(crate) bytes: &'a [u8],
    /// Current offset into `bytes`.
    pub(crate) pos: usize,
    /// Virtual address of `bytes[0]`.
    pub(crate) base: u64,
    /// Whether `DW_EH_PE_absptr` is eight bytes (64-bit image).
    pub(crate) ptr64: bool,
}

impl<'a> Cursor<'a> {
    /// Takes the next `n` bytes.
    ///
    /// # Arguments
    ///
    /// * `n` - Byte count.
    ///
    /// # Returns
    ///
    /// The bytes, or `None` past the end of the section.
    pub(crate) fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(n)?;
        let s = self.bytes.get(self.pos..end)?;
        self.pos = end;
        Some(s)
    }

    /// Reads one byte.
    pub(crate) fn u8(&mut self) -> Option<u8> {
        self.take(1).and_then(|s| s.first().copied())
    }

    /// Reads a little-endian `u16`.
    fn u16(&mut self) -> Option<u16> {
        self.take(2)
            .and_then(|s| s.try_into().ok())
            .map(u16::from_le_bytes)
    }

    /// Reads a little-endian `u32`.
    fn u32(&mut self) -> Option<u32> {
        self.take(4)
            .and_then(|s| s.try_into().ok())
            .map(u32::from_le_bytes)
    }

    /// Reads a little-endian `u64`.
    fn u64(&mut self) -> Option<u64> {
        self.take(8)
            .and_then(|s| s.try_into().ok())
            .map(u64::from_le_bytes)
    }

    /// Reads a little-endian `i16`, sign-extended.
    fn i16(&mut self) -> Option<i64> {
        self.take(2)
            .and_then(|s| s.try_into().ok())
            .map(|b| i64::from(i16::from_le_bytes(b)))
    }

    /// Reads a little-endian `i32`, sign-extended.
    fn i32(&mut self) -> Option<i64> {
        self.take(4)
            .and_then(|s| s.try_into().ok())
            .map(|b| i64::from(i32::from_le_bytes(b)))
    }

    /// Reads an unsigned LEB128 value.
    ///
    /// # Returns
    ///
    /// The value, or `None` when the section ends or the encoding exceeds
    /// [`LEB_MAX`] bytes.
    pub(crate) fn uleb(&mut self) -> Option<u64> {
        let mut v = 0u64;
        for i in 0..LEB_MAX {
            let b = self.u8()?;
            v |= u64::from(b & 0x7f).checked_shl(7 * i).unwrap_or(0);
            if b & 0x80 == 0 {
                return Some(v);
            }
        }
        None
    }

    /// Reads a signed LEB128 value.
    ///
    /// # Returns
    ///
    /// The value, or `None` when the section ends or the encoding exceeds
    /// [`LEB_MAX`] bytes.
    pub(crate) fn sleb(&mut self) -> Option<i64> {
        let mut v = 0i64;
        let mut shift = 0u32;
        for _ in 0..LEB_MAX {
            let b = self.u8()?;
            v |= i64::from(b & 0x7f).checked_shl(shift).unwrap_or(0);
            shift += 7;
            if b & 0x80 == 0 {
                if b & 0x40 != 0 {
                    v |= (-1i64).checked_shl(shift).unwrap_or(0);
                }
                return Some(v);
            }
        }
        None
    }

    /// Reads a NUL-terminated string (without the terminator).
    fn cstr(&mut self) -> Option<&'a [u8]> {
        let rest = self.bytes.get(self.pos..)?;
        let n = rest.iter().position(|&b| b == 0)?;
        let s = rest.get(..n)?;
        self.pos = self.pos.checked_add(n)?.checked_add(1)?;
        Some(s)
    }

    /// Reads a pointer in a `DW_EH_PE` encoding.
    ///
    /// The low nibble selects the format and bits 4..6 the application:
    /// absolute or `pcrel` (relative to the field's own address). `textrel`,
    /// `datarel` and `funcrel` do not occur in `.eh_frame` and end the parse.
    /// The `indirect` bit is ignored, so the slot address comes back; that
    /// only happens for the personality routine, which is skipped anyway.
    ///
    /// # Arguments
    ///
    /// * `enc` - The `DW_EH_PE` byte.
    ///
    /// # Returns
    ///
    /// The value, or `None` for `omit`, an unsupported encoding, or a
    /// truncated section.
    pub(crate) fn pointer(&mut self, enc: u8) -> Option<u64> {
        if enc == OMIT {
            return None;
        }
        let field = self.base.wrapping_add(u64::try_from(self.pos).ok()?);
        let raw = match enc & 0x0f {
            0x00 if self.ptr64 => self.u64()?,
            0x00 => u64::from(self.u32()?),
            0x01 => self.uleb()?,
            0x02 => u64::from(self.u16()?),
            0x03 => u64::from(self.u32()?),
            0x04 | 0x0c => self.u64()?,
            0x09 => self.sleb()?.cast_unsigned(),
            0x0a => self.i16()?.cast_unsigned(),
            0x0b => self.i32()?.cast_unsigned(),
            _ => return None,
        };
        match enc & 0x70 {
            0x00 => Some(raw),
            0x10 => Some(field.wrapping_add(raw)),
            _ => None,
        }
    }

    /// Reads an LSDA call-site table field: an unsigned offset in the
    /// encoding the LSDA's header names, applied to nothing.
    ///
    /// The call-site fields are offsets from the function's start or its
    /// landing-pad base, never pointers, so an encoding that applies one
    /// (`pcrel` or worse) or the `indirect` bit is a producer this does not
    /// read, not a value to reinterpret.
    ///
    /// # Arguments
    ///
    /// * `enc` - The `DW_EH_PE` byte the call-site table's header names.
    ///
    /// # Returns
    ///
    /// The value, or `None` for an encoding with an application bit, the
    /// `indirect` bit, or a format call-site tables do not use.
    pub(crate) fn offset(&mut self, enc: u8) -> Option<u64> {
        if enc & 0xf0 != 0 {
            return None;
        }
        match enc {
            0x01 => self.uleb(),
            0x02 => self.u16().map(u64::from),
            0x03 => self.u32().map(u64::from),
            0x04 => self.u64(),
            _ => None,
        }
    }
}

/// What an FDE needs from its CIE.
#[derive(Debug, Clone, Copy)]
struct Cie {
    /// `DW_EH_PE` encoding of the FDE's location and range fields.
    fde_enc: u8,
    /// `DW_EH_PE` encoding of the FDE's LSDA pointer, [`OMIT`] when the
    /// augmentation names no `L` entry.
    lsda_enc: u8,
}

/// Parses the CIE starting at `off`.
///
/// Versions 1, 3 and 4 are understood; a `z` augmentation is walked letter
/// by letter for the `R` (FDE pointer encoding), `P` (personality) and `L`
/// (LSDA encoding) entries, and the legacy `eh` augmentation's pointer is
/// skipped. Without an `R` entry the FDE pointers are absolute.
///
/// # Arguments
///
/// * `bytes` - The section.
/// * `base` - Virtual address of the section.
/// * `ptr64` - Whether absolute pointers are eight bytes.
/// * `off` - Offset of the CIE's length field.
///
/// # Returns
///
/// The CIE, or `None` for a malformed record or an unknown augmentation.
fn parse_cie(bytes: &[u8], base: u64, ptr64: bool, off: usize) -> Option<Cie> {
    let mut c = Cursor {
        bytes,
        pos: off,
        base,
        ptr64,
    };
    let len = c.u32()?;
    if len == LENGTH_64 {
        c.u64()?;
    }
    if c.u32()? != 0 {
        return None;
    }
    let version = c.u8()?;
    let aug = c.cstr()?;
    if aug.starts_with(b"eh") {
        c.pointer(0x00)?;
    }
    if version >= 4 {
        c.u8()?;
        c.u8()?;
    }
    c.uleb()?;
    c.sleb()?;
    if version == 1 {
        c.u8()?;
    } else {
        c.uleb()?;
    }
    let mut fde_enc = 0x00;
    let mut lsda_enc = OMIT;
    if aug.first() == Some(&b'z') {
        c.uleb()?;
        for &ch in aug.get(1..)? {
            match ch {
                b'R' => fde_enc = c.u8()?,
                b'L' => lsda_enc = c.u8()?,
                b'P' => {
                    let enc = c.u8()?;
                    c.pointer(enc)?;
                }
                b'S' | b'B' => {}
                _ => return None,
            }
        }
    }
    Some(Cie { fde_enc, lsda_enc })
}

/// One FDE: the extent it declares for a function, and its language-specific
/// data area when the CIE names an `L` encoding and the record carries the
/// pointer.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Fde {
    /// Entry of the function the record describes.
    pub(crate) start: u64,
    /// End of the function (exclusive).
    pub(crate) end: u64,
    /// Address of the function's LSDA, or `None` when the CIE's augmentation
    /// names no `L` encoding or the FDE's augmentation data is empty.
    pub(crate) lsda: Option<u64>,
}

/// Reads an FDE's LSDA pointer out of its augmentation data.
///
/// Under a `z` augmentation the FDE's data area opens with its own byte
/// length; the `L` encoding the CIE named reads the pointer from it when the
/// area holds anything. A pointer the area cannot deliver leaves the FDE
/// with none - the extent stands, the call sites are simply not found.
///
/// # Arguments
///
/// * `c` - The cursor, at the byte after the FDE's address range.
/// * `cie` - The CIE the FDE points at.
///
/// # Returns
///
/// The LSDA's address, or `None` when the CIE names no `L` encoding, the
/// augmentation data is empty, or the pointer does not parse.
fn lsda_of(c: &mut Cursor<'_>, cie: Cie) -> Option<u64> {
    if cie.lsda_enc == OMIT {
        return None;
    }
    let len = usize::try_from(c.uleb()?).ok()?;
    if len == 0 {
        return None;
    }
    c.pointer(cie.lsda_enc)
}

/// Walks every FDE in an `.eh_frame` section.
///
/// Records are walked in order; a record whose length runs past the section,
/// an FDE whose CIE cannot be parsed, or one with a zero start or range is
/// skipped. The walk stops at the zero-length terminator or the first record
/// whose length field is truncated.
///
/// # Arguments
///
/// * `bytes` - The section contents.
/// * `base` - Virtual address of the section.
/// * `ptr64` - Whether the image is 64-bit (`DW_EH_PE_absptr` width).
///
/// # Returns
///
/// The FDEs, sorted by extent and deduplicated by it.
pub(crate) fn fdes(bytes: &[u8], base: u64, ptr64: bool) -> Vec<Fde> {
    let mut out: Vec<Fde> = Vec::new();
    let mut cies: BTreeMap<usize, Option<Cie>> = BTreeMap::new();
    let mut pos = 0usize;
    while pos < bytes.len() {
        let mut c = Cursor {
            bytes,
            pos,
            base,
            ptr64,
        };
        let Some(len32) = c.u32() else { break };
        if len32 == 0 {
            break;
        }
        let len = if len32 == LENGTH_64 {
            match c.u64() {
                Some(l) => l,
                None => break,
            }
        } else {
            u64::from(len32)
        };
        let content = c.pos;
        let Some(next) = usize::try_from(len)
            .ok()
            .and_then(|l| content.checked_add(l))
            .filter(|n| *n <= bytes.len())
        else {
            break;
        };
        if let Some(id) = c.u32()
            && id != 0
            && let Some(cie_off) = usize::try_from(id)
                .ok()
                .and_then(|d| content.checked_sub(d))
            && let Some(cie) = *cies
                .entry(cie_off)
                .or_insert_with(|| parse_cie(bytes, base, ptr64, cie_off))
            && let Some(start) = c.pointer(cie.fde_enc)
            && let Some(range) = c.pointer(cie.fde_enc & 0x0f)
            && start != 0
            && range != 0
        {
            let lsda = lsda_of(&mut c, cie);
            out.push(Fde {
                start,
                end: start.wrapping_add(range),
                lsda,
            });
        }
        pos = next;
    }
    out.sort_unstable_by_key(|f| (f.start, f.end));
    out.dedup_by_key(|f| (f.start, f.end));
    out
}

/// Collects the `(start, end)` extents of every FDE in an `.eh_frame` section.
///
/// # Arguments
///
/// * `bytes` - The section contents.
/// * `base` - Virtual address of the section.
/// * `ptr64` - Whether the image is 64-bit (`DW_EH_PE_absptr` width).
///
/// # Returns
///
/// The extents, sorted and deduplicated.
pub(crate) fn function_ranges(bytes: &[u8], base: u64, ptr64: bool) -> Vec<(u64, u64)> {
    fdes(bytes, base, ptr64)
        .into_iter()
        .map(|f| (f.start, f.end))
        .collect()
}
