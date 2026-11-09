//! The C string and memory functions whose answer is a pure function of
//! their arguments and of memory, modeled for an imported call.
//!
//! A check that runs `strlen` or `strcmp` decides on their answer, and the
//! default answer, zero, reads every string as empty and every pair as
//! equal. These answer as C defines them, in the C locale: each argument
//! read through the target's convention ([`Emulator::api_arg`]), each byte
//! through a load, so an unmapped or null pointer faults where the real
//! call would, each element spending a step of the budget as a `rep`
//! iteration does. A scan stops at [`API_COPY_MAX`] bytes: a string with
//! no terminator within it, or a count past it, stops the run rather than
//! answering what the call did not compute.

use super::API_COPY_MAX;
use crate::emulate::{CANCEL_EVERY, Emulator, Limit, Stop};
use crate::num::{from_usize, lo8, lo32, saturating_usize};
use crate::program::BinaryFormat;

/// Longest needle `strstr` searches for, so the search stays linear in the
/// haystack's cap.
const NEEDLE_MAX: usize = 0x100;

/// How a compare reads two characters: as they are, or folded to lower
/// case in the C locale.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fold {
    /// Compared as they are, `unsigned char` or `wchar_t` values.
    Exact,
    /// `A`..`Z` folded to `a`..`z`; a character at or above `0x80` is the
    /// locale's to fold, so the compare gives up.
    Ascii,
}

impl Emulator<'_> {
    /// Answers a C string or memory function by what C defines it to do.
    ///
    /// # Arguments
    ///
    /// * `api` - The imported function's bare name.
    ///
    /// # Returns
    ///
    /// The value to leave in `rax`; `None` when the call is not one of
    /// these, or a case-folding one met a character the locale decides.
    ///
    /// # Errors
    ///
    /// A fault where a load or store faults, [`Stop::Budget`] when the scan
    /// outruns the budget, [`Stop::Unmodeled`] past [`API_COPY_MAX`], and
    /// [`Stop::MemoryFull`] when a store would overflow memory.
    pub(super) fn c_library(&mut self, api: &str) -> Result<Option<u64>, Stop> {
        let w = self.wchar();
        let (a, b, n) = (self.api_arg(0), self.api_arg(1), self.api_arg(2));
        Ok(Some(match api {
            "strlen" => self.c_len(api, a, 1, None)?,
            "strnlen" => self.c_len(api, a, 1, Some(b))?,
            "wcslen" => self.c_len(api, a, w, None)?,
            "wcsnlen" => self.c_len(api, a, w, Some(b))?,
            "lstrlenA" | "lstrlenW" => {
                let size = if api.ends_with('W') { 2 } else { 1 };
                self.c_len(api, a, size, None).or_else(seh_zero)?
            }
            "strcmp" => return self.c_cmp(api, (a, b), 1, None, true, Fold::Exact),
            "strncmp" => return self.c_cmp(api, (a, b), 1, Some(n), true, Fold::Exact),
            "memcmp" | "bcmp" => return self.c_cmp(api, (a, b), 1, Some(n), false, Fold::Exact),
            "wcscmp" => return self.c_cmp(api, (a, b), w, None, true, Fold::Exact),
            "wcsncmp" => return self.c_cmp(api, (a, b), w, Some(n), true, Fold::Exact),
            "_stricmp" | "_strcmpi" | "strcasecmp" => {
                return self.c_cmp(api, (a, b), 1, None, true, Fold::Ascii);
            }
            "_strnicmp" | "strncasecmp" => {
                return self.c_cmp(api, (a, b), 1, Some(n), true, Fold::Ascii);
            }
            "_wcsicmp" => return self.c_cmp(api, (a, b), w, None, true, Fold::Ascii),
            "_wcsnicmp" => return self.c_cmp(api, (a, b), w, Some(n), true, Fold::Ascii),
            "tolower" | "toupper" => return Ok(ascii_case(api, lo32(a))),
            _ => return self.c_copy_or_search(api, (a, b, n), w),
        }))
    }

    /// The copies and searches of [`Emulator::c_library`].
    ///
    /// # Arguments
    ///
    /// * `api` - The function's bare name.
    /// * `(a, b, n)` - Its first three arguments.
    /// * `w` - Bytes in one `wchar_t` of the target.
    ///
    /// # Returns
    ///
    /// The value to leave in `rax`, or `None` for any other name.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`].
    fn c_copy_or_search(
        &mut self,
        api: &str,
        (a, b, n): (u64, u64, u64),
        w: usize,
    ) -> Result<Option<u64>, Stop> {
        Ok(Some(match api {
            "strcpy" => self.c_copy(api, a, b, 1, None).map(|()| a)?,
            "strncpy" => self.c_copy(api, a, b, 1, Some(n)).map(|()| a)?,
            "wcscpy" => self.c_copy(api, a, b, w, None).map(|()| a)?,
            "wcsncpy" => self.c_copy(api, a, b, w, Some(n)).map(|()| a)?,
            "strcat" => self.c_cat(api, a, b, 1).map(|()| a)?,
            "wcscat" => self.c_cat(api, a, b, w).map(|()| a)?,
            "lstrcpyA" => self
                .c_copy(api, a, b, 1, None)
                .map(|()| a)
                .or_else(seh_zero)?,
            "lstrcatA" => self.c_cat(api, a, b, 1).map(|()| a).or_else(seh_zero)?,
            "strdup" | "_strdup" => self.c_dup(api, a)?,
            "strchr" => self.c_chr(api, a, u64::from(lo8(b)), 1, false)?,
            "strrchr" => self.c_chr(api, a, u64::from(lo8(b)), 1, true)?,
            "wcschr" => self.c_chr(api, a, low_bytes(b, w), w, false)?,
            "wcsrchr" => self.c_chr(api, a, low_bytes(b, w), w, true)?,
            "memchr" => self.c_memchr(api, a, u64::from(lo8(b)), n)?,
            "strpbrk" => {
                let k = self.c_span(api, a, b, false)?;
                let k = saturating_usize(k);
                if self.unit(a, k, 1)? == 0 {
                    0
                } else {
                    self.narrow(a.wrapping_add(from_usize(k)))
                }
            }
            "strstr" => self.c_str(api, a, b, 1)?,
            "wcsstr" => self.c_str(api, a, b, w)?,
            "strspn" => self.c_span(api, a, b, true)?,
            "strcspn" => self.c_span(api, a, b, false)?,
            _ => return Ok(None),
        }))
    }

    /// Bytes in one `wchar_t`: two on Windows (and a raw image, read as
    /// Windows), four in the ELF and Mach-O C libraries.
    fn wchar(&self) -> usize {
        match self.program.format {
            BinaryFormat::Elf | BinaryFormat::MachO => 4,
            BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => 2,
        }
    }

    /// Spends one step of the budget on one element of a scan.
    ///
    /// A scan steps through every [`CANCEL_EVERY`] boundary one at a time,
    /// so it looks at the cancel flag at each as a run of instructions does;
    /// a long scan cannot carry the count past a boundary unseen.
    ///
    /// # Errors
    ///
    /// [`Stop::Budget`] when the budget is spent, and the time limit when
    /// the cancel flag is raised at a boundary.
    fn spend(&mut self) -> Result<(), Stop> {
        if self.steps >= self.budget {
            return Err(Stop::Budget);
        }
        self.steps += 1;
        if self.steps.is_multiple_of(CANCEL_EVERY)
            && self
                .cancel
                .as_ref()
                .is_some_and(crate::cancel::Cancel::is_raised)
        {
            return Err(Stop::Limit(Limit::Time));
        }
        Ok(())
    }

    /// Reads the `k`th character of `size` bytes from `at`, as a load does.
    ///
    /// # Errors
    ///
    /// A fault where nothing backs a byte.
    fn unit(&self, at: u64, k: usize, size: usize) -> Result<u64, Stop> {
        self.load(at.wrapping_add(from_usize(k.wrapping_mul(size))), size)
    }

    /// The characters before the first zero at `at`: `strlen`, or at most
    /// `max` of them for `strnlen`.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`]: no zero within the cap is unmodeled.
    fn c_len(&mut self, api: &str, at: u64, size: usize, max: Option<u64>) -> Result<u64, Stop> {
        let cap = API_COPY_MAX / size;
        let limit = max.map_or(cap, |m| saturating_usize(m).min(cap));
        for k in 0..limit {
            self.spend()?;
            if self.unit(at, k, size)? == 0 {
                return Ok(from_usize(k));
            }
        }
        match max {
            Some(m) if from_usize(limit) == m => Ok(m),
            _ => Err(past_cap(api, API_COPY_MAX)),
        }
    }

    /// Compares two strings or blocks character by character, as C's
    /// compare family does.
    ///
    /// # Arguments
    ///
    /// * `api` - The function's name, for a stop.
    /// * `(x, y)` - The two pointers.
    /// * `size` - Bytes per character.
    /// * `n` - At most this many characters (`strncmp`, `memcmp`).
    /// * `nul` - Whether a zero ends both (the `str` and `wcs` forms).
    /// * `fold` - Whether case is folded.
    ///
    /// # Returns
    ///
    /// The sign C promises, `-1`, `0` or `1`, as `eax` holds an `int`;
    /// `None` when a folded compare met a character at or above `0x80`.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`].
    fn c_cmp(
        &mut self,
        api: &str,
        (x, y): (u64, u64),
        size: usize,
        n: Option<u64>,
        nul: bool,
        fold: Fold,
    ) -> Result<Option<u64>, Stop> {
        let cap = API_COPY_MAX / size;
        let limit = n.map_or(cap, |m| saturating_usize(m).min(cap));
        for k in 0..limit {
            self.spend()?;
            let (p, q) = (self.unit(x, k, size)?, self.unit(y, k, size)?);
            if fold == Fold::Ascii && (p >= 0x80 || q >= 0x80) {
                return Ok(None);
            }
            let (p, q) = (fold_key(p, size, fold), fold_key(q, size, fold));
            if p != q {
                return Ok(Some(sign(p < q)));
            }
            if nul && p == 0 {
                return Ok(Some(0));
            }
        }
        match n {
            Some(m) if from_usize(limit) == m => Ok(Some(0)),
            _ => Err(past_cap(api, API_COPY_MAX)),
        }
    }

    /// Copies characters from `src` to `dst`: to and with the terminator
    /// (`strcpy`), or exactly `n`, zeros past the terminator (`strncpy`).
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`]; a count past the cap is unmodeled before
    /// anything is written.
    fn c_copy(
        &mut self,
        api: &str,
        dst: u64,
        src: u64,
        size: usize,
        n: Option<u64>,
    ) -> Result<(), Stop> {
        let cap = API_COPY_MAX / size;
        let limit = n.map_or(Ok(cap), |m| within_cap(api, m, cap))?;
        let mut ended = false;
        for k in 0..limit {
            self.spend()?;
            let c = if ended { 0 } else { self.unit(src, k, size)? };
            self.write(dst.wrapping_add(from_usize(k.wrapping_mul(size))), c, size)?;
            if c == 0 && n.is_none() {
                return Ok(());
            }
            ended |= c == 0;
        }
        if n.is_some() {
            Ok(())
        } else {
            Err(past_cap(api, API_COPY_MAX))
        }
    }

    /// A copy of the string at `src` in a region the modeled allocator
    /// hands out, as `strdup` makes one with `malloc`.
    ///
    /// # Returns
    ///
    /// The copy's address, or zero, `NULL`, when no region is left.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`].
    fn c_dup(&mut self, api: &str, src: u64) -> Result<u64, Stop> {
        let at = self.allocate();
        if at != 0 {
            self.c_copy(api, at, src, 1, None)?;
        }
        Ok(at)
    }

    /// Appends the string at `src` to the one at `dst`, as `strcat` does.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`].
    fn c_cat(&mut self, api: &str, dst: u64, src: u64, size: usize) -> Result<(), Stop> {
        let end = self.c_len(api, dst, size, None)?;
        let at = dst.wrapping_add(end.wrapping_mul(from_usize(size)));
        self.c_copy(api, at, src, size, None)
    }

    /// The first (or, with `last`, the final) character `c` in the string
    /// at `at`, its terminator included, as `strchr` and `strrchr` find it.
    ///
    /// # Returns
    ///
    /// Its address, or zero, `NULL`, when the string holds none.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`].
    fn c_chr(&mut self, api: &str, at: u64, c: u64, size: usize, last: bool) -> Result<u64, Stop> {
        let mut found = 0;
        for k in 0..API_COPY_MAX / size {
            self.spend()?;
            let u = self.unit(at, k, size)?;
            if u == c {
                found = self.narrow(at.wrapping_add(from_usize(k.wrapping_mul(size))));
                if !last {
                    return Ok(found);
                }
            }
            if u == 0 {
                return Ok(found);
            }
        }
        Err(past_cap(api, API_COPY_MAX))
    }

    /// The first byte `c` in the `n` bytes at `at`, as `memchr` finds it.
    ///
    /// # Returns
    ///
    /// Its address, or zero when none of the `n` is it.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`].
    fn c_memchr(&mut self, api: &str, at: u64, c: u64, n: u64) -> Result<u64, Stop> {
        let limit = within_cap(api, n, API_COPY_MAX)?;
        for k in 0..limit {
            self.spend()?;
            if self.unit(at, k, 1)? == c {
                return Ok(self.narrow(at.wrapping_add(from_usize(k))));
            }
        }
        Ok(0)
    }

    /// The first place the string at `needle` occurs in the one at `hay`,
    /// as `strstr` finds it; an empty needle occurs at the start.
    ///
    /// # Returns
    ///
    /// Its address, or zero when it does not occur.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`], and unmodeled for a needle past
    /// [`NEEDLE_MAX`] characters.
    fn c_str(&mut self, api: &str, hay: u64, needle: u64, size: usize) -> Result<u64, Stop> {
        let want = self.c_units(api, needle, size, NEEDLE_MAX)?;
        if want.is_empty() {
            return Ok(hay);
        }
        let mut have = Vec::new();
        for k in 0..API_COPY_MAX / size {
            self.spend()?;
            let u = self.unit(hay, k, size)?;
            if u == 0 {
                return Ok(0);
            }
            have.push(u);
            if have.ends_with(&want) {
                let start = have.len() - want.len();
                return Ok(self.narrow(hay.wrapping_add(from_usize(start.wrapping_mul(size)))));
            }
        }
        Err(past_cap(api, API_COPY_MAX))
    }

    /// The characters of the string at `at` before its terminator, at most
    /// `cap` of them.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`]; a string longer than `cap` is unmodeled.
    fn c_units(&mut self, api: &str, at: u64, size: usize, cap: usize) -> Result<Vec<u64>, Stop> {
        let mut out = Vec::new();
        for k in 0..cap {
            self.spend()?;
            let u = self.unit(at, k, size)?;
            if u == 0 {
                return Ok(out);
            }
            out.push(u);
        }
        Err(past_cap(api, cap.saturating_mul(size)))
    }

    /// The length of the string at `at`'s first run of bytes in the set at
    /// `set` (`strspn`), or of bytes outside it (`strcspn`).
    ///
    /// The set is read once into a table of the 256 byte values, so each
    /// byte of the string is one look-up whatever the set's length.
    ///
    /// # Errors
    ///
    /// As [`Emulator::c_library`].
    fn c_span(&mut self, api: &str, at: u64, set: u64, inside: bool) -> Result<u64, Stop> {
        let mut member = [false; 256];
        for u in self.c_units(api, set, 1, API_COPY_MAX)? {
            if let Some(m) = member.get_mut(saturating_usize(u)) {
                *m = true;
            }
        }
        for k in 0..API_COPY_MAX {
            self.spend()?;
            let u = self.unit(at, k, 1)?;
            let found = member.get(saturating_usize(u)).copied().unwrap_or(false);
            if u == 0 || found != inside {
                return Ok(from_usize(k));
            }
        }
        Err(past_cap(api, API_COPY_MAX))
    }
}

/// A character's compare key: folded to lower case when `fold` asks, and a
/// four-byte `wchar_t` read as the signed `int` the ELF libraries compare.
///
/// # Arguments
///
/// * `c` - The character as loaded.
/// * `size` - Its width in bytes.
/// * `fold` - Whether case is folded.
fn fold_key(c: u64, size: usize, fold: Fold) -> i64 {
    let c = if fold == Fold::Ascii && (u64::from(b'A')..=u64::from(b'Z')).contains(&c) {
        c | 0x20
    } else {
        c
    };
    if size == 4 {
        i64::from(lo32(c).cast_signed())
    } else {
        i64::try_from(c).unwrap_or(i64::MAX)
    }
}

/// The low `size` bytes of `v`: a `wchar_t` argument as the callee reads it.
///
/// # Arguments
///
/// * `v` - The argument's register or stack word.
/// * `size` - Bytes in one `wchar_t`.
fn low_bytes(v: u64, size: usize) -> u64 {
    let bits = u32::try_from(size.saturating_mul(8)).unwrap_or(64);
    if bits >= 64 {
        v
    } else {
        v & ((1u64 << bits) - 1)
    }
}

/// `-1` as `eax` holds an `int`, or `1`.
///
/// # Arguments
///
/// * `less` - Whether the first operand compared below the second.
fn sign(less: bool) -> u64 {
    if less {
        u64::from((-1i32).cast_unsigned())
    } else {
        1
    }
}

/// `tolower` or `toupper` in the C locale: `A`..`Z` and `a`..`z` change,
/// any other character below `0x80` and `EOF` stay as they are.
///
/// # Arguments
///
/// * `api` - `tolower` or `toupper`.
/// * `c` - The argument, an `int`.
///
/// # Returns
///
/// The answer, or `None` for a character at or above `0x80`, which the
/// locale decides.
fn ascii_case(api: &str, c: u32) -> Option<u64> {
    if c.cast_signed() == -1 {
        return Some(u64::from(c));
    }
    let b = u8::try_from(c).ok().filter(u8::is_ascii)?;
    let out = if api == "tolower" {
        b.to_ascii_lowercase()
    } else {
        b.to_ascii_uppercase()
    };
    Some(u64::from(out))
}

/// A count within the cap one call models, or the stop that says it is
/// past it.
///
/// # Arguments
///
/// * `api` - The function, for the stop.
/// * `n` - The count the call asks for.
/// * `cap` - The most it may be.
///
/// # Errors
///
/// [`Stop::Unmodeled`] when `n` is past `cap`.
pub(super) fn within_cap(api: &str, n: u64, cap: usize) -> Result<usize, Stop> {
    usize::try_from(n)
        .ok()
        .filter(|n| *n <= cap)
        .ok_or_else(|| past_cap(api, cap))
}

/// The stop of a call that reads or writes past what one call is modeled
/// for.
///
/// # Arguments
///
/// * `api` - The function.
/// * `cap` - The most it may read or write.
fn past_cap(api: &str, cap: usize) -> Stop {
    Stop::Unmodeled(format!(
        "{api} past {cap:#x}, more than one modeled call reads or writes"
    ))
}

/// A `lstr` function's answer to a fault: the Windows `lstr` family
/// catches the access violation and answers zero.
///
/// # Arguments
///
/// * `stop` - Why the call stopped.
///
/// # Errors
///
/// Any stop but a fault.
fn seh_zero(stop: Stop) -> Result<u64, Stop> {
    if matches!(stop, Stop::Fault(_)) {
        Ok(0)
    } else {
        Err(stop)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{Arch, Program, Section};

    /// A raised cancel flag stops a long string scan at the first step
    /// boundary the scan reaches, as it stops a run of instructions there.
    ///
    /// The scan is called directly: a run looks at the flag before its
    /// first instruction and would stop there, before the scan began.
    ///
    /// # Panics
    ///
    /// When the scan runs on past a boundary with the flag raised.
    #[test]
    fn a_raised_cancel_flag_stops_a_string_scan() {
        /// Where the scanned string sits.
        const AT: u64 = 0x10_0000;
        let p = Program::raw(
            vec![0; 0x1000],
            Arch::X86_64,
            0x1000,
            Some(0x1000),
            vec![Section::mapped(".text", 0x1000, 0, 0x1000, false, true)],
        );
        let flag = crate::cancel::Cancel::new();
        let Some(mut emu) = flag.within(|| Emulator::new(&p, 1_000_000)) else {
            panic!("an x64 image emulates");
        };
        for k in 0..3 * CANCEL_EVERY {
            emu.poke(AT + from_usize(k), b'A');
        }
        assert!(emu.set_register("rcx", AT));
        flag.raise();
        assert_eq!(emu.c_library("strlen"), Err(Stop::Limit(Limit::Time)));
        assert_eq!(emu.steps, CANCEL_EVERY);
    }
}
