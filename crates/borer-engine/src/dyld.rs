//! Mach-O fixups, applied to the image the way dyld does.
//!
//! A Mach-O states every pointer the loader touches in one of two tables.
//! ld64 targeting macOS 12 or iOS 15 on writes chained fixups
//! (`LC_DYLD_CHAINED_FIXUPS`): each fixup is the pointer word itself,
//! encoded with the distance to the next one, so a segment's fixups are
//! chains its page table starts, and on disk a pointer reads as its
//! encoding rather than an address. A rebase holds its target, an address
//! or an offset from the image base by pointer format; a bind holds an
//! ordinal into an imports table naming the symbol, its library and an
//! addend. A firmware or kernel image keeps its chain starts in a
//! `__TEXT,__chain_starts` section instead. Older images carry
//! `LC_DYLD_INFO` opcodes: a byte program per kind whose run lists the
//! rebased words, which already hold their targets, and the bound slots.
//!
//! [`read`] decodes either into claims settled by
//! [`crate::reloc::settle`]: a chained rebase's word is written with its
//! target (an arm64e pointer's authentication bits stripped), a chained
//! bind's slot with zero, the one address the image cannot know, and every
//! bind names its slot after its import. The pointer formats read are
//! `DYLD_CHAINED_PTR_64` and `_64_OFFSET`, the arm64e ones (`ARM64E`,
//! `ARM64E_KERNEL`, `ARM64E_USERLAND`, `ARM64E_USERLAND24` and
//! `ARM64E_FIRMWARE`) and the kernel cache ones (`64_KERNEL_CACHE`,
//! `X86_64_KERNEL_CACHE`); the 32-bit formats, the shared cache's and the
//! segmented one are refused. A chain that leaves its segment, runs into a
//! word a chain walked already, or comes past the cap is cut there and
//! counted as refused, so a hostile table costs a bounded walk, never a
//! panic or a hang.

use std::collections::BTreeMap;

use goblin::mach::MachO;
use goblin::mach::load_command::CommandVariant;

use crate::fxmap::FxHashSet;
use crate::macho::uleb;
use crate::program::Section;
use crate::reloc::{Bind, Claim, ENTRIES_MAX, Import, Relocs, Table, file_range, settle};

/// `DYLD_CHAINED_PTR_START_NONE`: a page no chain starts in.
const START_NONE: u16 = 0xffff;
/// `DYLD_CHAINED_PTR_START_MULTI`: a page whose chains start in a list,
/// which only the 32-bit formats use.
const START_MULTI: u16 = 0x8000;
/// Longest import name read.
const NAME_MAX: usize = 4096;
/// `REBASE_TYPE_POINTER` and `BIND_TYPE_POINTER`: a pointer-sized word.
const TYPE_POINTER: u8 = 1;
/// `MH_PIE`: the image loads at a random base.
const MH_PIE: u32 = 0x0020_0000;
/// The file types that always load at a random base: `MH_DYLIB`,
/// `MH_BUNDLE` and `MH_KEXT_BUNDLE`.
const SLID: [u32; 3] = [0x6, 0x8, 0xb];

/// One segment as its load command maps it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Segment {
    /// Where it is mapped.
    vmaddr: u64,
    /// Its size in memory.
    vmsize: u64,
    /// Its first byte's offset in the whole file.
    fileoff: u64,
    /// Bytes the file holds of it.
    filesize: u64,
}

impl Segment {
    /// Finds the file bytes of `len` bytes at `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - The first byte's address.
    /// * `len` - The byte count.
    ///
    /// # Returns
    ///
    /// The first byte's offset in the whole file, or `None` when the
    /// segment's file bytes do not hold them all.
    fn file_off(&self, va: u64, len: u64) -> Option<u64> {
        let rel = va.checked_sub(self.vmaddr)?;
        (rel.checked_add(len)? <= self.filesize.min(self.vmsize)).then(|| self.fileoff + rel)
    }

    /// Tells whether the segment maps `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - An address.
    fn holds(&self, va: u64) -> bool {
        va >= self.vmaddr && va - self.vmaddr < self.vmsize
    }
}

/// How one chained pointer format packs a fixup into its word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Format {
    /// `DYLD_CHAINED_PTR_64` (`offset` false) and `_64_OFFSET` (true): a
    /// 36-bit target and a top byte, a 24-bit ordinal and an 8-bit addend,
    /// a 12-bit next counted in 4-byte strides.
    Ptr64 {
        /// The target is an offset from the image base, not an address.
        offset: bool,
    },
    /// The arm64e formats: an 11-bit next, the authentication bit 63 and
    /// the bind bit 62.
    Arm64e {
        /// Bytes per unit of next.
        stride: u64,
        /// An unauthenticated rebase's target is an offset from the image
        /// base, not an address.
        offset: bool,
        /// A bind's ordinal is 24 bits wide, not 16.
        wide: bool,
    },
    /// The kernel cache formats: rebases only, a 30-bit offset into the
    /// cache level its two bits name, a 12-bit next.
    Kernel {
        /// Bytes per unit of next.
        stride: u64,
    },
}

/// What one chained word asks of the loader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fixup {
    /// A pointer into the image.
    Rebase {
        /// The address it holds once fixed up.
        target: u64,
        /// The loader signs it.
        auth: bool,
    },
    /// A slot bound to an import.
    Bind {
        /// Index into the imports table.
        ordinal: u64,
        /// What the word adds to the import's address.
        addend: i64,
        /// The loader signs it.
        auth: bool,
    },
    /// A word this does not read: a kernel cache level past the image's.
    Unread,
}

/// Reads `n` bits of `w` from bit `lo`.
///
/// # Arguments
///
/// * `w` - The word.
/// * `lo` - The lowest bit.
/// * `n` - The width, below 64.
fn bits(w: u64, lo: u32, n: u32) -> u64 {
    (w >> lo) & ((1u64 << n) - 1)
}

impl Format {
    /// Reads a pointer format's code.
    ///
    /// # Arguments
    ///
    /// * `code` - The `DYLD_CHAINED_PTR_*` value.
    ///
    /// # Returns
    ///
    /// The format and its name, or `None` for one this does not read.
    fn of(code: u64) -> Option<(Format, &'static str)> {
        // SPEC: <mach-o/fixup-chains.h>, the DYLD_CHAINED_PTR_* values.
        let arm64e = |stride, offset, wide| Format::Arm64e {
            stride,
            offset,
            wide,
        };
        Some(match code {
            1 => (arm64e(8, false, false), "DYLD_CHAINED_PTR_ARM64E"),
            2 => (Format::Ptr64 { offset: false }, "DYLD_CHAINED_PTR_64"),
            6 => (Format::Ptr64 { offset: true }, "DYLD_CHAINED_PTR_64_OFFSET"),
            7 => (arm64e(4, true, false), "DYLD_CHAINED_PTR_ARM64E_KERNEL"),
            8 => (
                Format::Kernel { stride: 4 },
                "DYLD_CHAINED_PTR_64_KERNEL_CACHE",
            ),
            9 => (arm64e(8, true, false), "DYLD_CHAINED_PTR_ARM64E_USERLAND"),
            10 => (arm64e(4, false, false), "DYLD_CHAINED_PTR_ARM64E_FIRMWARE"),
            11 => (
                Format::Kernel { stride: 1 },
                "DYLD_CHAINED_PTR_X86_64_KERNEL_CACHE",
            ),
            12 => (arm64e(8, true, true), "DYLD_CHAINED_PTR_ARM64E_USERLAND24"),
            _ => return None,
        })
    }

    /// Bytes per unit of a word's next field.
    fn stride(self) -> u64 {
        match self {
            Format::Ptr64 { .. } => 4,
            Format::Arm64e { stride, .. } | Format::Kernel { stride } => stride,
        }
    }

    /// Decodes one chained word.
    ///
    /// # Arguments
    ///
    /// * `w` - The word as the file holds it.
    /// * `base` - The image base an offset counts from.
    ///
    /// # Returns
    ///
    /// The fixup and the distance to the next word in strides, zero at the
    /// chain's end.
    fn decode(self, w: u64, base: u64) -> (Fixup, u64) {
        // SPEC: <mach-o/fixup-chains.h>, dyld_chained_ptr_64_rebase/_bind,
        // dyld_chained_ptr_arm64e_* and dyld_chained_ptr_64_kernel_cache_rebase.
        match self {
            Format::Ptr64 { offset } => {
                let fixup = if bits(w, 63, 1) == 1 {
                    Fixup::Bind {
                        ordinal: bits(w, 0, 24),
                        addend: bits(w, 24, 8).cast_signed(),
                        auth: false,
                    }
                } else {
                    let target = bits(w, 0, 36);
                    let target = if offset {
                        base.wrapping_add(target)
                    } else {
                        target
                    };
                    Fixup::Rebase {
                        target: target | (bits(w, 36, 8) << 56),
                        auth: false,
                    }
                };
                (fixup, bits(w, 51, 12))
            }
            Format::Arm64e { offset, wide, .. } => {
                let auth = bits(w, 63, 1) == 1;
                let fixup = match (bits(w, 62, 1) == 1, auth) {
                    (false, false) => {
                        let target = bits(w, 0, 43);
                        let target = if offset {
                            base.wrapping_add(target)
                        } else {
                            target
                        };
                        Fixup::Rebase {
                            target: target | (bits(w, 43, 8) << 56),
                            auth,
                        }
                    }
                    (false, true) => Fixup::Rebase {
                        target: base.wrapping_add(bits(w, 0, 32)),
                        auth,
                    },
                    (true, _) => Fixup::Bind {
                        ordinal: bits(w, 0, if wide { 24 } else { 16 }),
                        addend: if auth {
                            0
                        } else {
                            (bits(w, 32, 19) << 45).cast_signed() >> 45
                        },
                        auth,
                    },
                };
                (fixup, bits(w, 51, 11))
            }
            Format::Kernel { .. } => {
                let fixup = if bits(w, 30, 2) == 0 {
                    Fixup::Rebase {
                        target: base.wrapping_add(bits(w, 0, 30)),
                        auth: bits(w, 63, 1) == 1,
                    }
                } else {
                    Fixup::Unread
                };
                (fixup, bits(w, 51, 12))
            }
        }
    }
}

/// Reads a little-endian `u16` at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset.
fn u16_at(data: &[u8], at: usize) -> Option<u16> {
    let b = data.get(at..at.checked_add(2)?)?;
    Some(u16::from_le_bytes([*b.first()?, *b.get(1)?]))
}

/// Reads a little-endian `u32` at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset.
fn u32_at(data: &[u8], at: usize) -> Option<u32> {
    let mut le = [0u8; 4];
    le.copy_from_slice(data.get(at..at.checked_add(4)?)?);
    Some(u32::from_le_bytes(le))
}

/// Reads a little-endian `u64` at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset.
fn u64_at(data: &[u8], at: usize) -> Option<u64> {
    let mut le = [0u8; 8];
    le.copy_from_slice(data.get(at..at.checked_add(8)?)?);
    Some(u64::from_le_bytes(le))
}

/// Reads the SLEB128 at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset, moved past the value.
fn sleb(data: &[u8], at: &mut usize) -> Option<i64> {
    let mut value: u64 = 0;
    let mut shift = 0u32;
    loop {
        let b = *data.get(*at)?;
        *at += 1;
        if shift < 64 {
            value |= u64::from(b & 0x7f) << shift;
        }
        shift = shift.saturating_add(7);
        if b & 0x80 == 0 {
            if shift < 64 && b & 0x40 != 0 {
                value |= u64::MAX << shift;
            }
            return Some(value.cast_signed());
        }
    }
}

/// Reads the NUL-terminated name at `at`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset.
///
/// # Returns
///
/// The name and its length without the NUL, or `None` when no NUL ends it
/// within [`NAME_MAX`] bytes or it is empty.
fn name_at(data: &[u8], at: usize) -> Option<(String, usize)> {
    let rest = data.get(at..)?;
    let len = rest.iter().take(NAME_MAX).position(|&b| b == 0)?;
    let name = rest.get(..len).filter(|n| !n.is_empty())?;
    Some((String::from_utf8_lossy(name).into_owned(), len))
}

/// The fixups one image claims, gathered before they settle.
struct Walk<'a> {
    /// The whole file.
    file: &'a [u8],
    /// The image's mapped sections.
    sections: &'a [Section],
    /// The image's segments, in load-command order.
    segments: &'a [Segment],
    /// The image base offsets count from.
    base: u64,
    /// The linked libraries, which a bind's ordinal counts into.
    libraries: usize,
    /// The words claimed.
    claims: Vec<Claim>,
    /// Every word a chain walked or an opcode bind named: a chain running
    /// into one is cut there, and a rebase of a slot a lazy bind names
    /// (every lazy pointer is both, holding its stub helper until bound)
    /// leaves the slot to the bind.
    taken: FxHashSet<u64>,
    /// The imports named so far.
    imports: Vec<Import>,
    /// Each import's index in [`Walk::imports`], by name, ordinal and weak
    /// flag, for the opcode binds that name one symbol many times.
    interned: BTreeMap<(String, i64, bool), usize>,
    /// Entries refused.
    refused: usize,
    /// Fixups left to read, claimed or refused, before the cap.
    fuel: usize,
}

impl Walk<'_> {
    /// Spends one unit of fuel.
    ///
    /// # Returns
    ///
    /// `false` when none is left, counting the fixup past the cap as
    /// refused.
    fn spend(&mut self) -> bool {
        if self.fuel == 0 {
            self.refused += 1;
            return false;
        }
        self.fuel -= 1;
        true
    }

    /// Tells whether a library ordinal names a library the image links or
    /// one of the special lookups.
    ///
    /// # Arguments
    ///
    /// * `ordinal` - The ordinal, the special ones negative.
    fn known(&self, ordinal: i64) -> bool {
        (-3..=0).contains(&ordinal) || usize::try_from(ordinal).is_ok_and(|o| o <= self.libraries)
    }

    /// Interns an import.
    ///
    /// # Arguments
    ///
    /// * `name` - The symbol's name.
    /// * `ordinal` - Its library ordinal.
    /// * `weak` - Whether it is a weak import.
    ///
    /// # Returns
    ///
    /// Its index in [`Walk::imports`].
    fn intern(&mut self, name: &str, ordinal: i64, weak: bool) -> usize {
        let next = self.imports.len();
        let k = *self
            .interned
            .entry((name.to_owned(), ordinal, weak))
            .or_insert(next);
        if k == next {
            self.imports.push(Import {
                name: name.to_owned(),
                ordinal,
                weak,
            });
        }
        k
    }

    /// Claims one word.
    ///
    /// # Arguments
    ///
    /// * `va` - The word's address.
    /// * `width` - Its width in bytes.
    /// * `value` - What the loader writes, `None` where the word already
    ///   holds it.
    /// * `bind` - The bind naming the slot, `None` for a rebase.
    /// * `auth` - Whether the loader signs it.
    fn claim(&mut self, va: u64, width: u64, value: Option<u64>, bind: Option<Bind>, auth: bool) {
        match file_range(self.sections, va, width) {
            Some(at) => self.claims.push(Claim {
                va,
                at,
                value,
                site: bind.is_none(),
                bind,
                auth,
            }),
            None => self.refused += 1,
        }
    }

    /// Walks one chain.
    ///
    /// # Arguments
    ///
    /// * `segment` - The segment the chain must stay in.
    /// * `start` - Its first word's address.
    /// * `format` - The pointer format.
    /// * `table` - The imports table a bind's ordinal indexes: each entry's
    ///   index in [`Walk::imports`] and addend, `None` where it names no
    ///   import this reads.
    fn chain(
        &mut self,
        segment: &Segment,
        start: u64,
        format: Format,
        table: &[Option<(usize, i64)>],
    ) {
        let mut va = start;
        loop {
            if !self.spend() {
                return;
            }
            let Some(w) = segment
                .file_off(va, 8)
                .and_then(|off| u64_at(self.file, usize::try_from(off).ok()?))
            else {
                self.refused += 1;
                return;
            };
            if !self.taken.insert(va) {
                self.refused += 1;
                return;
            }
            let (fixup, next) = format.decode(w, self.base);
            match fixup {
                Fixup::Rebase { target, auth } => self.claim(va, 8, Some(target), None, auth),
                Fixup::Bind {
                    ordinal,
                    addend,
                    auth,
                } => match usize::try_from(ordinal)
                    .ok()
                    .and_then(|k| table.get(k).copied().flatten())
                {
                    Some((import, own)) => self.claim(
                        va,
                        8,
                        Some(0),
                        Some(Bind {
                            slot: va,
                            import,
                            addend: own.wrapping_add(addend),
                            lazy: false,
                        }),
                        auth,
                    ),
                    None => self.refused += 1,
                },
                Fixup::Unread => self.refused += 1,
            }
            if next == 0 {
                return;
            }
            let Some(after) = next
                .checked_mul(format.stride())
                .and_then(|d| va.checked_add(d))
            else {
                self.refused += 1;
                return;
            };
            va = after;
        }
    }

    /// Reads a chained fixups payload: its imports, then every chain its
    /// segments' page tables start.
    ///
    /// # Arguments
    ///
    /// * `data` - The `LC_DYLD_CHAINED_FIXUPS` payload.
    ///
    /// # Returns
    ///
    /// The name of the first pointer format read, `None` when no segment
    /// holds a chain.
    fn chained(&mut self, data: &[u8]) -> Option<&'static str> {
        let field = |k: usize| u32_at(data, k * 4).and_then(|v| usize::try_from(v).ok());
        let (
            Some(0),
            Some(starts),
            Some(imports),
            Some(symbols),
            Some(count),
            Some(kind),
            Some(packed),
        ) = (
            field(0),
            field(1),
            field(2),
            field(3),
            field(4),
            field(5),
            field(6),
        )
        else {
            self.refused += 1;
            return None;
        };
        let table = self.import_table(data, imports, symbols, count, kind, packed);
        let mut first = None;
        let Some(segments) = field_at(data, starts) else {
            self.refused += 1;
            return None;
        };
        self.refused += usize::from(segments > self.segments.len());
        for i in 0..segments.min(self.segments.len()) {
            let Some(info) = i
                .checked_mul(4)
                .and_then(|o| starts.checked_add(4 + o))
                .and_then(|at| field_at(data, at))
            else {
                self.refused += 1;
                break;
            };
            if info == 0 {
                continue;
            }
            let Some(at) = starts.checked_add(info) else {
                self.refused += 1;
                continue;
            };
            if let Some(name) = self.segment_chains(data, at, i, &table) {
                first.get_or_insert(name);
            }
        }
        first
    }

    /// Reads the imports table of a chained fixups payload.
    ///
    /// # Arguments
    ///
    /// * `data` - The payload.
    /// * `at` - Where the table starts.
    /// * `symbols` - Where the names start.
    /// * `count` - The entries it states.
    /// * `kind` - `DYLD_CHAINED_IMPORT`, `_ADDEND` or `_ADDEND64`.
    /// * `packed` - The names' format: `0` plain, else compressed.
    ///
    /// # Returns
    ///
    /// Each entry's index in [`Walk::imports`] and addend, `None` for one
    /// whose name or library does not read.
    fn import_table(
        &mut self,
        data: &[u8],
        at: usize,
        symbols: usize,
        count: usize,
        kind: usize,
        packed: usize,
    ) -> Vec<Option<(usize, i64)>> {
        // SPEC: <mach-o/fixup-chains.h>, dyld_chained_import,
        // dyld_chained_import_addend and dyld_chained_import_addend64.
        let size = match kind {
            1 => 4,
            2 => 8,
            3 => 16,
            _ => {
                self.refused += usize::from(count > 0);
                return Vec::new();
            }
        };
        let held = count
            .min(data.len().saturating_sub(at) / size)
            .min(ENTRIES_MAX);
        self.refused += usize::from(held < count);
        let mut out = Vec::with_capacity(held);
        for k in 0..held {
            let entry = at.saturating_add(k * size);
            let raw = if size == 16 {
                u64_at(data, entry)
            } else {
                u32_at(data, entry).map(u64::from)
            };
            let Some(raw) = raw else {
                out.push(None);
                continue;
            };
            let (ordinal, weak, name, addend) = match size {
                16 => {
                    let lib = bits(raw, 0, 16);
                    (
                        special(lib, 0xfff0, 0x1_0000),
                        bits(raw, 16, 1) == 1,
                        bits(raw, 32, 32),
                        u64_at(data, entry + 8).map_or(0, u64::cast_signed),
                    )
                }
                _ => (
                    special(bits(raw, 0, 8), 0xf0, 0x100),
                    bits(raw, 8, 1) == 1,
                    bits(raw, 9, 23),
                    if size == 8 {
                        u32_at(data, entry + 4).map_or(0, |a| i64::from(a.cast_signed()))
                    } else {
                        0
                    },
                ),
            };
            let named = (packed == 0)
                .then(|| usize::try_from(name).ok())
                .flatten()
                .and_then(|n| symbols.checked_add(n))
                .and_then(|n| name_at(data, n))
                .filter(|_| self.known(ordinal));
            out.push(named.map(|(n, _)| (self.intern(&n, ordinal, weak), addend)));
        }
        out
    }

    /// Walks the chains one segment's page table starts.
    ///
    /// # Arguments
    ///
    /// * `data` - The chained fixups payload.
    /// * `at` - Where the segment's `dyld_chained_starts_in_segment` is.
    /// * `index` - The segment's index in load-command order.
    /// * `table` - The imports table ([`Walk::chain`]).
    ///
    /// # Returns
    ///
    /// The pointer format's name, or `None` when the segment's table does
    /// not read or names a format this does not read.
    fn segment_chains(
        &mut self,
        data: &[u8],
        at: usize,
        index: usize,
        table: &[Option<(usize, i64)>],
    ) -> Option<&'static str> {
        // SPEC: <mach-o/fixup-chains.h>, dyld_chained_starts_in_segment:
        // size, page_size, pointer_format, segment_offset,
        // max_valid_pointer, page_count, page_start[].
        let header = (
            u16_at(data, at.saturating_add(4)),
            u16_at(data, at.saturating_add(6)),
            u64_at(data, at.saturating_add(8)),
            u16_at(data, at.saturating_add(20)),
        );
        let (Some(page_size), Some(code), Some(offset), Some(pages)) = header else {
            self.refused += 1;
            return None;
        };
        let (Some((format, name)), Some(segment)) = (
            Format::of(u64::from(code)),
            self.segments.get(index).copied(),
        ) else {
            self.refused += 1;
            return None;
        };
        if page_size == 0 {
            self.refused += 1;
            return None;
        }
        let first = self.base.wrapping_add(offset);
        for page in 0..pages {
            let Some(start) = u16_at(
                data,
                at.saturating_add(22).saturating_add(usize::from(page) * 2),
            ) else {
                self.refused += 1;
                break;
            };
            if start == START_NONE {
                continue;
            }
            if start & START_MULTI != 0 {
                self.refused += 1;
                continue;
            }
            let va = first
                .wrapping_add(u64::from(page) * u64::from(page_size))
                .wrapping_add(u64::from(start));
            self.chain(&segment, va, format, table);
        }
        Some(name)
    }

    /// Walks the chains a `__TEXT,__chain_starts` section lists.
    ///
    /// # Arguments
    ///
    /// * `data` - The section's bytes: a `dyld_chained_starts_offsets`.
    ///
    /// # Returns
    ///
    /// The pointer format's name, or `None` when the section does not read
    /// or names a format this does not read.
    fn section_chains(&mut self, data: &[u8]) -> Option<&'static str> {
        let (Some(code), Some(count)) = (u32_at(data, 0), u32_at(data, 4)) else {
            self.refused += 1;
            return None;
        };
        let Some((format, name)) = Format::of(u64::from(code)) else {
            self.refused += 1;
            return None;
        };
        let count = usize::try_from(count).unwrap_or(usize::MAX);
        let listed = count.min(data.len().saturating_sub(8) / 4);
        self.refused += usize::from(listed < count);
        for k in 0..listed {
            let Some(start) = u32_at(data, 8 + k * 4) else {
                break;
            };
            let va = self.base.wrapping_add(u64::from(start));
            match self.segments.iter().find(|s| s.holds(va)).copied() {
                Some(segment) => self.chain(&segment, va, format, &[]),
                None => self.refused += 1,
            }
        }
        Some(name)
    }

    /// Runs an `LC_DYLD_INFO` rebase program.
    ///
    /// # Arguments
    ///
    /// * `program` - The opcode bytes.
    /// * `word` - The pointer width in bytes.
    fn rebases(&mut self, program: &[u8], word: u64) {
        // SPEC: <mach-o/loader.h>, REBASE_OPCODE_*; dyld stops at DONE.
        let mut at = 0usize;
        let mut segment: Option<Segment> = None;
        let mut off = 0u64;
        let mut kind = 0u8;
        while let Some(&op) = program.get(at) {
            at += 1;
            let imm = op & 0x0f;
            let (times, skip) = match op & 0xf0 {
                0x00 => return,
                0x10 => {
                    kind = imm;
                    continue;
                }
                0x20 => {
                    segment = self.segments.get(usize::from(imm)).copied();
                    let Some(o) = uleb(program, &mut at) else {
                        self.refused += 1;
                        return;
                    };
                    off = o;
                    continue;
                }
                0x30 => {
                    let Some(d) = uleb(program, &mut at) else {
                        self.refused += 1;
                        return;
                    };
                    off = off.wrapping_add(d);
                    continue;
                }
                0x40 => {
                    off = off.wrapping_add(u64::from(imm).wrapping_mul(word));
                    continue;
                }
                0x50 => (u64::from(imm), 0),
                0x60 => match uleb(program, &mut at) {
                    Some(n) => (n, 0),
                    None => {
                        self.refused += 1;
                        return;
                    }
                },
                0x70 => match uleb(program, &mut at) {
                    Some(d) => (1, d),
                    None => {
                        self.refused += 1;
                        return;
                    }
                },
                0x80 => match (uleb(program, &mut at), uleb(program, &mut at)) {
                    (Some(n), Some(d)) => (n, d),
                    _ => {
                        self.refused += 1;
                        return;
                    }
                },
                _ => {
                    self.refused += 1;
                    return;
                }
            };
            for _ in 0..times {
                if !self.spend() {
                    return;
                }
                let va = segment.map(|s| s.vmaddr.wrapping_add(off));
                match (segment, va) {
                    (Some(s), Some(va)) if s.file_off(va, word).is_some() => {
                        if kind == TYPE_POINTER && !self.taken.contains(&va) {
                            self.claim(va, word, None, None, false);
                        }
                    }
                    _ => self.refused += 1,
                }
                off = off.wrapping_add(skip).wrapping_add(word);
            }
        }
    }

    /// Runs an `LC_DYLD_INFO` bind program.
    ///
    /// # Arguments
    ///
    /// * `program` - The opcode bytes.
    /// * `word` - The pointer width in bytes.
    /// * `lazy` - Whether it is the lazy program, whose entries each end
    ///   with `DONE` rather than the program.
    fn binds(&mut self, program: &[u8], word: u64, lazy: bool) {
        // SPEC: <mach-o/loader.h>, BIND_OPCODE_*; the lazy program ends
        // each entry with DONE, the others end there.
        let mut at = 0usize;
        let mut segment: Option<Segment> = None;
        let mut off = 0u64;
        let mut kind = TYPE_POINTER;
        let mut ordinal = 0i64;
        let mut name: Option<String> = None;
        let mut weak = false;
        let mut addend = 0i64;
        while let Some(&op) = program.get(at) {
            at += 1;
            let imm = op & 0x0f;
            let (times, skip) = match op & 0xf0 {
                0x00 if lazy => continue,
                0x00 => return,
                0x10 => {
                    ordinal = i64::from(imm);
                    continue;
                }
                0x20 => {
                    let Some(o) = uleb(program, &mut at) else {
                        self.refused += 1;
                        return;
                    };
                    ordinal = i64::try_from(o).unwrap_or(i64::MAX);
                    continue;
                }
                0x30 => {
                    ordinal = if imm == 0 { 0 } else { i64::from(imm) - 16 };
                    continue;
                }
                0x40 => {
                    let Some((n, len)) = name_at(program, at) else {
                        self.refused += 1;
                        return;
                    };
                    at = at.saturating_add(len + 1);
                    name = Some(n);
                    weak = imm & 0x1 != 0;
                    continue;
                }
                0x50 => {
                    kind = imm;
                    continue;
                }
                0x60 => {
                    let Some(a) = sleb(program, &mut at) else {
                        self.refused += 1;
                        return;
                    };
                    addend = a;
                    continue;
                }
                0x70 => {
                    segment = self.segments.get(usize::from(imm)).copied();
                    let Some(o) = uleb(program, &mut at) else {
                        self.refused += 1;
                        return;
                    };
                    off = o;
                    continue;
                }
                0x80 => {
                    let Some(d) = uleb(program, &mut at) else {
                        self.refused += 1;
                        return;
                    };
                    off = off.wrapping_add(d);
                    continue;
                }
                0x90 => (1, 0),
                0xa0 => match uleb(program, &mut at) {
                    Some(d) => (1, d),
                    None => {
                        self.refused += 1;
                        return;
                    }
                },
                0xb0 => (1, u64::from(imm).wrapping_mul(word)),
                0xc0 => match (uleb(program, &mut at), uleb(program, &mut at)) {
                    (Some(n), Some(d)) => (n, d),
                    _ => {
                        self.refused += 1;
                        return;
                    }
                },
                _ => {
                    self.refused += 1;
                    return;
                }
            };
            for _ in 0..times {
                if !self.spend() {
                    return;
                }
                let va = segment.map(|s| s.vmaddr.wrapping_add(off));
                match (segment, va, name.as_deref()) {
                    (Some(s), Some(va), Some(n))
                        if s.file_off(va, word).is_some() && self.known(ordinal) =>
                    {
                        if kind == TYPE_POINTER && self.taken.insert(va) {
                            let import = self.intern(n, ordinal, weak);
                            let bind = Bind {
                                slot: va,
                                import,
                                addend,
                                lazy,
                            };
                            self.claim(va, word, None, Some(bind), false);
                        }
                    }
                    _ => self.refused += 1,
                }
                off = off.wrapping_add(skip).wrapping_add(word);
            }
        }
    }
}

/// Reads an unsigned value of a table's width as a library ordinal.
///
/// # Arguments
///
/// * `v` - The value.
/// * `floor` - The lowest value that stands for a special ordinal.
/// * `span` - Two to the width: what a special value is less by.
fn special(v: u64, floor: u64, span: i64) -> i64 {
    let signed = i64::try_from(v).unwrap_or(i64::MAX);
    if v > floor { signed - span } else { signed }
}

/// Reads a `u32` offset as a `usize`.
///
/// # Arguments
///
/// * `data` - The bytes.
/// * `at` - The offset of the field.
fn field_at(data: &[u8], at: usize) -> Option<usize> {
    u32_at(data, at).and_then(|v| usize::try_from(v).ok())
}

/// Reads the file bytes a `linkedit_data_command`-style range names.
///
/// # Arguments
///
/// * `file` - The whole file.
/// * `base` - Where the image begins in the file.
/// * `off` - The range's offset from the image's start.
/// * `size` - Its size.
fn linkedit(file: &[u8], base: usize, off: u32, size: u32) -> Option<&[u8]> {
    let start = base.checked_add(usize::try_from(off).ok()?)?;
    file.get(start..start.checked_add(usize::try_from(size).ok()?)?)
}

/// Applies one Mach-O image's fixups.
///
/// The chained fixups command wins; without it the `__chain_starts`
/// section, then the dyld info opcodes. An image with none of them is a
/// static or pre-fixup image, whose words already hold their targets.
///
/// # Arguments
///
/// * `file` - The whole file.
/// * `m` - The image.
/// * `base` - Where the image begins in the file.
/// * `image_base` - Where `__TEXT` is mapped, which offsets count from.
/// * `sections` - The image's sections, fit to the file.
/// * `chain_starts` - The `__TEXT,__chain_starts` section's bytes, when
///   the image has one.
/// * `libraries` - How many libraries the image links, which a bind's
///   ordinal counts into.
///
/// # Returns
///
/// The relocated image, its binds and the counts.
pub(crate) fn read(
    file: &[u8],
    m: &MachO<'_>,
    base: usize,
    image_base: u64,
    sections: &[Section],
    chain_starts: Option<&[u8]>,
    libraries: usize,
) -> Relocs {
    let segments: Vec<Segment> = m
        .load_commands
        .iter()
        .filter_map(|lc| {
            let (vmaddr, vmsize, fileoff, filesize) = match &lc.command {
                CommandVariant::Segment64(s) => (s.vmaddr, s.vmsize, s.fileoff, s.filesize),
                CommandVariant::Segment32(s) => (
                    u64::from(s.vmaddr),
                    u64::from(s.vmsize),
                    u64::from(s.fileoff),
                    u64::from(s.filesize),
                ),
                _ => return None,
            };
            Some(Segment {
                vmaddr,
                vmsize,
                fileoff: fileoff.saturating_add(crate::num::from_usize(base)),
                filesize,
            })
        })
        .collect();
    let mut walk = Walk {
        file,
        sections,
        segments: &segments,
        base: image_base,
        libraries,
        claims: Vec::new(),
        taken: FxHashSet::default(),
        imports: Vec::new(),
        interned: BTreeMap::new(),
        refused: 0,
        fuel: ENTRIES_MAX,
    };
    let chained = m.load_commands.iter().find_map(|lc| match &lc.command {
        CommandVariant::DyldChainedFixups(c) => Some((c.dataoff, c.datasize)),
        _ => None,
    });
    let info = m.load_commands.iter().find_map(|lc| match &lc.command {
        CommandVariant::DyldInfo(d) | CommandVariant::DyldInfoOnly(d) => Some(*d),
        _ => None,
    });
    let word: u64 = if m.is_64 { 8 } else { 4 };
    /// What names a chained table whose pointer format did not read.
    const NO_FORMAT: &str = "no pointer format read";
    let table = if let Some((off, size)) = chained {
        let format = match linkedit(file, base, off, size) {
            Some(data) => walk.chained(data),
            None => {
                walk.refused += 1;
                None
            }
        };
        Some(Table::Chained(format.unwrap_or(NO_FORMAT)))
    } else if let Some(data) = chain_starts {
        Some(Table::Chained(
            walk.section_chains(data).unwrap_or(NO_FORMAT),
        ))
    } else if let Some(d) = info {
        for (off, size, lazy) in [
            (d.bind_off, d.bind_size, false),
            (d.lazy_bind_off, d.lazy_bind_size, true),
        ] {
            if let Some(program) = linkedit(file, base, off, size) {
                walk.binds(program, word, lazy);
            }
        }
        if let Some(program) = linkedit(file, base, d.rebase_off, d.rebase_size) {
            walk.rebases(program, word);
        }
        Some(Table::Opcodes)
    } else {
        None
    };
    let mut relocs = Relocs::default();
    let Some(table) = table else {
        return relocs;
    };
    relocs.table = table;
    relocs.refused = walk.refused;
    relocs.imports = walk.imports;
    let pic = m.header.flags & MH_PIE != 0 || SLID.contains(&m.header.filetype);
    settle(file, walk.claims, word, pic, &mut relocs);
    relocs
}
