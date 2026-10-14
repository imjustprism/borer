//! Width conversions that say what they keep.
//!
//! An `as` cast between integer widths silently truncates, wraps or drops
//! a sign; the workspace warns on every one. These are the conversions the
//! engine means on purpose, each named for what it does, so a reader sees
//! "the low 32 bits" or "the same bits read as signed" rather than a cast
//! whose intent has to be guessed. A conversion that can fail (a 64-bit
//! count into a `usize`, a value into a narrower type it must fit) goes
//! through `try_from` at the call site, where the failure has a meaning.
//! The little-endian word readers the header and table walks share live
//! here too, so one bounds discipline answers a hostile offset everywhere.

/// The low 32 bits of a value.
///
/// # Arguments
///
/// * `v` - The value.
#[must_use]
#[expect(
    clippy::cast_possible_truncation,
    reason = "the low bits are the point"
)]
pub const fn lo32(v: u64) -> u32 {
    v as u32
}

/// The low 16 bits of a value.
///
/// # Arguments
///
/// * `v` - The value.
#[must_use]
#[expect(
    clippy::cast_possible_truncation,
    reason = "the low bits are the point"
)]
pub const fn lo16(v: u64) -> u16 {
    v as u16
}

/// The low 8 bits of a value.
///
/// # Arguments
///
/// * `v` - The value.
#[must_use]
#[expect(
    clippy::cast_possible_truncation,
    reason = "the low bits are the point"
)]
pub const fn lo8(v: u64) -> u8 {
    v as u8
}

/// The low 32 bits of a value, sign-extended to 64.
///
/// What a 32-bit operation leaves in a register when the value is signed.
///
/// # Arguments
///
/// * `v` - The value.
#[must_use]
pub const fn sext32(v: u64) -> u64 {
    (lo32(v).cast_signed() as i64).cast_unsigned()
}

/// A count or offset as a `usize`, saturating at the platform's limit.
///
/// For sizes that bound a loop or an allocation, where a value past
/// `usize::MAX` means "everything" and never a wrap to something small.
///
/// # Arguments
///
/// * `v` - The value.
#[must_use]
pub fn saturating_usize(v: u64) -> usize {
    usize::try_from(v).unwrap_or(usize::MAX)
}

/// A `usize` as a `u64`: lossless on every platform the engine builds for.
///
/// # Arguments
///
/// * `v` - The value.
#[must_use]
pub fn from_usize(v: usize) -> u64 {
    u64::try_from(v).unwrap_or(u64::MAX)
}

/// A count as a float for a ratio or a statistic.
///
/// The rounding past fifty-three bits does not matter there.
///
/// # Arguments
///
/// * `v` - The count.
#[must_use]
#[expect(
    clippy::cast_precision_loss,
    reason = "a statistic, not an exact value"
)]
pub const fn as_f64(v: u64) -> f64 {
    v as f64
}

/// A `usize` count as a float, as [`as_f64`].
///
/// # Arguments
///
/// * `v` - The count.
#[must_use]
#[expect(
    clippy::cast_precision_loss,
    reason = "a statistic, not an exact value"
)]
pub const fn usize_f64(v: usize) -> f64 {
    v as f64
}

/// Reads a little-endian `u16` at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset of the value's first byte.
///
/// # Returns
///
/// The value, or `None` when `data` holds fewer than two bytes from `at`.
#[must_use]
pub fn u16_le(data: &[u8], at: usize) -> Option<u16> {
    let b: [u8; 2] = data.get(at..at.checked_add(2)?)?.try_into().ok()?;
    Some(u16::from_le_bytes(b))
}

/// Reads a little-endian `u32` at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset of the value's first byte.
///
/// # Returns
///
/// The value, or `None` when `data` holds fewer than four bytes from `at`.
#[must_use]
pub fn u32_le(data: &[u8], at: usize) -> Option<u32> {
    let b: [u8; 4] = data.get(at..at.checked_add(4)?)?.try_into().ok()?;
    Some(u32::from_le_bytes(b))
}

/// Reads a little-endian `u64` at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset of the value's first byte.
///
/// # Returns
///
/// The value, or `None` when `data` holds fewer than eight bytes from `at`.
#[must_use]
pub fn u64_le(data: &[u8], at: usize) -> Option<u64> {
    let b: [u8; 8] = data.get(at..at.checked_add(8)?)?.try_into().ok()?;
    Some(u64::from_le_bytes(b))
}

#[cfg(test)]
mod tests {
    use super::{lo8, lo16, lo32, saturating_usize, sext32, u16_le, u32_le, u64_le};

    /// Each conversion keeps the bits it names and nothing else.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn conversions_keep_what_they_name() {
        assert_eq!(lo32(0x1_2345_6789), 0x2345_6789);
        assert_eq!(lo16(0x1_2345_6789), 0x6789);
        assert_eq!(lo8(0x1_2345_6789), 0x89);
        assert_eq!(sext32(0xffff_fd30), 0xffff_ffff_ffff_fd30);
        assert_eq!(sext32(0x7fff_ffff), 0x7fff_ffff);
        assert_eq!(saturating_usize(5), 5);
    }

    /// Each reader returns the little-endian word at the offset, and
    /// `None` where the bytes (or the offset itself) run out.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn little_endian_reads_stop_at_the_end() {
        let b = [0x78, 0x56, 0x34, 0x12, 0xf0, 0xde, 0xbc, 0x9a];
        assert_eq!(u16_le(&b, 0), Some(0x5678));
        assert_eq!(u16_le(&b, 6), Some(0x9abc));
        assert_eq!(u32_le(&b, 4), Some(0x9abc_def0));
        assert_eq!(u64_le(&b, 0), Some(0x9abc_def0_1234_5678));
        assert_eq!(u16_le(&b, 7), None);
        assert_eq!(u32_le(&b, 5), None);
        assert_eq!(u64_le(&b, 1), None);
        assert_eq!(u32_le(&[], usize::MAX), None);
        assert_eq!(u64_le(&b, usize::MAX), None);
    }
}
