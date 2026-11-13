//! Bounds checks for file-stated sizes before `pdb` 0.8.0 slices or allocates from them.

use std::collections::BTreeSet;
use std::io::{Cursor, Read, Seek, SeekFrom};

/// MSF 7.00 file header magic.
const MSF_MAGIC: &[u8; 32] = b"Microsoft C/C++ MSF 7.00\r\n\x1aDS\0\0\0";

/// Largest MSF stream directory accepted, in bytes.
const MSF_DIR_MAX: u32 = 64 << 20;

/// Reads a little-endian `u16` at `at`.
///
/// # Arguments
///
/// * `b` - Byte slice to read from.
/// * `at` - Byte offset of the two-byte field.
///
/// # Returns
///
/// The decoded `u16`, or `None` when `at..at + 2` falls outside `b`.
fn u16_at(b: &[u8], at: usize) -> Option<u16> {
    Some(u16::from_le_bytes(
        b.get(at..at.checked_add(2)?)?.try_into().ok()?,
    ))
}

/// Reads a little-endian `u32` at `at`.
///
/// # Arguments
///
/// * `b` - Byte slice to read from.
/// * `at` - Byte offset of the four-byte field.
///
/// # Returns
///
/// The decoded `u32`, or `None` when `at..at + 4` falls outside `b`.
fn u32_at(b: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_le_bytes(
        b.get(at..at.checked_add(4)?)?.try_into().ok()?,
    ))
}

/// Reads the pages named by four-byte indices in `table` from `r`.
///
/// # Arguments
///
/// * `r` - Seekable MSF byte source.
/// * `table` - Packed little-endian `u32` page numbers.
/// * `page_size` - MSF page size in bytes.
/// * `pages_used` - Header-stated page bound.
/// * `file_pages` - Pages backed by the file's actual byte length.
/// * `byte_len` - Exact byte length to truncate the concatenated pages to.
///
/// # Returns
///
/// The assembled stream bytes, or `None` when any page index is out of range or unreadable.
fn read_pages<R: Read + Seek>(
    r: &mut R,
    table: &[u8],
    page_size: usize,
    pages_used: u32,
    file_pages: u32,
    byte_len: usize,
) -> Option<Vec<u8>> {
    let count = table.len() / 4;
    let mut out = vec![0u8; count.checked_mul(page_size)?];
    let ps64 = u64::try_from(page_size).ok()?;
    for i in 0..count {
        let pg = u32_at(table, i * 4)?;
        if pg == 0 || pg > pages_used || pg >= file_pages {
            return None;
        }
        r.seek(SeekFrom::Start(u64::from(pg).checked_mul(ps64)?))
            .ok()?;
        let dst = out.get_mut(i * page_size..(i + 1) * page_size)?;
        r.read_exact(dst).ok()?;
    }
    out.truncate(byte_len);
    Some(out)
}

/// Checks that `r` holds an MSF 7.00 container whose directory and stream sizes cannot
/// amplify a small file into multi-gigabyte allocations through repeated page numbers.
///
/// # Arguments
///
/// * `r` - Seekable reader over the candidate PDB.
/// * `file_len` - Verified byte length of `r`.
///
/// # Returns
///
/// `true` when the MSF header, directory page list and stream directory stay within bounds
/// and `r` has been rewound to byte 0.
pub(super) fn msf_ok<R: Read + Seek>(r: &mut R, file_len: u64) -> bool {
    msf_check(r, file_len).is_some()
}

/// Checks an in-memory PDB byte slice with [`msf_ok`].
///
/// # Arguments
///
/// * `bytes` - Candidate PDB file bytes.
///
/// # Returns
///
/// `true` when `bytes` passes [`msf_ok`].
pub(super) fn msf_bytes_ok(bytes: &[u8]) -> bool {
    u64::try_from(bytes.len()).is_ok_and(|len| msf_ok(&mut Cursor::new(bytes), len))
}

/// Inner fallible implementation of [`msf_ok`].
///
/// # Arguments
///
/// * `r` - Seekable reader over the candidate PDB.
/// * `file_len` - Verified byte length of `r`.
///
/// # Returns
///
/// `Some(())` when every MSF table bound holds and `r` is rewound to byte 0.
fn msf_check<R: Read + Seek>(r: &mut R, file_len: u64) -> Option<()> {
    if !(4096..=super::PDB_LEN_MAX).contains(&file_len) {
        return None;
    }
    r.seek(SeekFrom::Start(0)).ok()?;
    let mut p0 = [0u8; 4096];
    r.read_exact(&mut p0).ok()?;
    if !p0.starts_with(MSF_MAGIC) {
        return None;
    }
    let page_size = u32_at(&p0, 32)?;
    let pages_used = u32_at(&p0, 40)?;
    let dir_size = u32_at(&p0, 44)?;
    if !page_size.is_power_of_two()
        || !(0x100..=0x80_0000).contains(&page_size)
        || pages_used == 0
        || dir_size > MSF_DIR_MAX
        || u64::from(dir_size) > file_len
    {
        return None;
    }
    let ps = usize::try_from(page_size).ok()?;
    let ps64 = u64::from(page_size);
    let file_pages = u32::try_from(file_len / ps64).ok()?;
    let ds = usize::try_from(dir_size).ok()?;
    let dir_pages = ds.div_ceil(ps);
    let list_bytes = dir_pages.checked_mul(4)?;
    let list_pages = list_bytes.div_ceil(ps);
    let list_end = 52usize.checked_add(list_pages.checked_mul(4)?)?;
    let list_tbl = p0.get(52..list_end)?;
    let dir_tbl = read_pages(r, list_tbl, ps, pages_used, file_pages, list_bytes)?;
    let dir = read_pages(r, &dir_tbl, ps, pages_used, file_pages, ds)?;
    let count = usize::try_from(u32_at(&dir, 0)?).ok()?;
    let sizes_end = 4usize.checked_add(count.checked_mul(4)?)?;
    if sizes_end > dir.len() {
        return None;
    }
    let mut total_pages = 0u64;
    let page_cap = u64::from(file_pages).saturating_mul(2);
    for i in 0..count {
        let sz = u32_at(&dir, 4 + i * 4)?;
        if sz != u32::MAX {
            if u64::from(sz) > file_len {
                return None;
            }
            total_pages = total_pages.checked_add(u64::from(sz).div_ceil(ps64))?;
            if total_pages > page_cap {
                return None;
            }
        }
    }
    let sp_bytes = usize::try_from(total_pages).ok()?.checked_mul(4)?;
    let pages_slice = dir.get(sizes_end..sizes_end.checked_add(sp_bytes)?)?;
    for chunk in pages_slice.chunks_exact(4) {
        let pg = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        if pg == 0 || pg > pages_used || pg >= file_pages {
            return None;
        }
    }
    r.seek(SeekFrom::Start(0)).ok()?;
    Some(())
}

/// Parses the DBI header and `DbgDataHdr` slice out of Stream 3 with checked `u32` sums.
///
/// # Arguments
///
/// * `s3` - Raw bytes of Stream 3 (`DBI`).
///
/// # Returns
///
/// The `module_list_size` and the `DbgDataHdr` slice, or `None` when the header or its
/// six preceding substream sizes overflow or run past `s3`.
fn dbi_parts(s3: &[u8]) -> Option<(usize, &[u8])> {
    if s3.len() < 64 || u32_at(s3, 0) != Some(u32::MAX) {
        return None;
    }
    let mut sum = 0u32;
    for off in [24usize, 28, 32, 36, 40, 52] {
        sum = sum.checked_add(u32_at(s3, off)?)?;
    }
    let mod_len = usize::try_from(u32_at(s3, 24)?).ok()?;
    let extra_at = 64usize.checked_add(usize::try_from(sum).ok()?)?;
    let dbg_len = usize::try_from(u32_at(s3, 48)?).ok()?;
    if dbg_len % 2 != 0 {
        return None;
    }
    let dbg = s3.get(extra_at..extra_at.checked_add(dbg_len)?)?;
    Some((mod_len, dbg))
}

/// Checks Stream 3's substream bounds before `db.address_map()` runs `DBIExtraStreams::new`.
///
/// # Arguments
///
/// * `db` - The opened PDB.
///
/// # Returns
///
/// `true` when Stream 3 is present and its substream sizes do not overflow `u32` or `s3`.
pub(super) fn dbi_extra_ok<'s>(db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>) -> bool {
    db.raw_stream(pdb::StreamIndex(3))
        .ok()
        .flatten()
        .is_some_and(|s3| dbi_parts(s3.as_slice()).is_some())
}

/// Checked section base addresses and optional `OMAP` table mirroring `pdb::AddressMap`.
#[derive(Debug)]
pub(super) struct AddrGuard {
    /// Virtual address of each 1-based original (or image) section header.
    section_vas: Vec<u32>,
    /// Sorted `(source_address, target_address)` pairs when `original_section_headers` is active.
    omap: Option<Vec<(u32, u32)>>,
}

impl AddrGuard {
    /// Builds the checked address-translation guard from Stream 3's `DbgDataHdr` streams.
    ///
    /// # Arguments
    ///
    /// * `db` - The opened PDB.
    ///
    /// # Returns
    ///
    /// The guard when Stream 3 and its referenced section and OMAP streams are well-formed.
    pub(super) fn open<'s>(db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>) -> Option<Self> {
        let (_, dbg) = {
            let s3 = db.raw_stream(pdb::StreamIndex(3)).ok()??;
            let (m, d) = dbi_parts(s3.as_slice())?;
            (m, d.to_vec())
        };
        let idx = |at: usize| u16_at(&dbg, at).unwrap_or(0xffff);
        let omap_to = idx(6);
        let omap_from = idx(8);
        let sec_hdrs = idx(10);
        let orig_hdrs = idx(20);
        if orig_hdrs == 0xffff {
            let section_vas = if sec_hdrs == 0xffff {
                Vec::new()
            } else {
                read_section_vas(db, sec_hdrs)?
            };
            Some(Self {
                section_vas,
                omap: None,
            })
        } else {
            if sec_hdrs != 0xffff {
                let _ = read_section_vas(db, sec_hdrs)?;
            }
            let section_vas = read_section_vas(db, orig_hdrs)?;
            let _ = read_omap(db, omap_to, false)?;
            let omap = Some(read_omap(db, omap_from, true)?);
            Some(Self { section_vas, omap })
        }
    }

    /// Translates `offset` to an RVA only after checking that section addition and OMAP lookup
    /// neither overflow `u32` nor trip `OMAPRecord::translate`'s ordering assertion.
    ///
    /// # Arguments
    ///
    /// * `map` - The crate's parsed address map.
    /// * `offset` - Section-relative offset from a symbol or line record.
    ///
    /// # Returns
    ///
    /// The translated image RVA, or `None` when unmapped or overflowing.
    pub(super) fn rva_of(
        &self,
        map: &pdb::AddressMap<'_>,
        offset: pdb::PdbInternalSectionOffset,
    ) -> Option<u32> {
        let slot = usize::from(offset.section).checked_sub(1)?;
        let internal = self.section_vas.get(slot)?.checked_add(offset.offset)?;
        if let Some(omap) = &self.omap {
            let i = match omap.binary_search_by_key(&internal, |&(src, _)| src) {
                Ok(i) => i,
                Err(0) => return None,
                Err(i) => i - 1,
            };
            let (src, dst) = omap[i];
            if dst == 0 {
                return None;
            }
            let _ = internal.checked_sub(src)?.checked_add(dst)?;
        }
        offset.to_rva(map).map(|r| r.0)
    }
}

/// Reads `virtual_address` from every 40-byte `IMAGE_SECTION_HEADER` in stream `id`.
///
/// # Arguments
///
/// * `db` - The opened PDB.
/// * `id` - Stream number naming a section header table.
///
/// # Returns
///
/// Each section's `virtual_address`, or `None` when the stream is missing or misaligned.
fn read_section_vas<'s>(db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>, id: u16) -> Option<Vec<u32>> {
    let stream = db.raw_stream(pdb::StreamIndex(id)).ok()??;
    let b = stream.as_slice();
    if b.len() % 40 != 0 {
        return None;
    }
    b.chunks_exact(40).map(|row| u32_at(row, 12)).collect()
}

/// Validates an 8-byte-record OMAP stream and optionally checks non-decreasing `source_address`.
///
/// # Arguments
///
/// * `db` - The opened PDB.
/// * `id` - Stream number naming the OMAP table.
/// * `require_sorted` - Whether `source_address` must be monotonic non-decreasing.
///
/// # Returns
///
/// The `(source_address, target_address)` pairs when `require_sorted` holds (empty otherwise),
/// or `None` when missing, misaligned or unsorted.
fn read_omap<'s>(
    db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
    id: u16,
    require_sorted: bool,
) -> Option<Vec<(u32, u32)>> {
    let stream = db.raw_stream(pdb::StreamIndex(id)).ok()??;
    let b = stream.as_slice();
    if b.len() % 8 != 0 {
        return None;
    }
    if !require_sorted {
        return Some(Vec::new());
    }
    let mut out = Vec::with_capacity(b.len() / 8);
    let mut prev = 0u32;
    for (i, rec) in b.chunks_exact(8).enumerate() {
        let src = u32_at(rec, 0)?;
        let dst = u32_at(rec, 4)?;
        if i > 0 && src < prev {
            return None;
        }
        prev = src;
        out.push((src, dst));
    }
    Some(out)
}

/// Evaluates per-module line-program bounds in lockstep with `dbi.modules()`.
///
/// # Arguments
///
/// * `db` - The opened PDB.
///
/// # Returns
///
/// One boolean per module yielded by `dbi.modules()`, `true` only when the module's stream
/// holds `symbols_size + line_size` whole and every C13 `DEBUG_S_LINES` block is sound.
pub(super) fn module_line_flags<'s>(db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>) -> Vec<bool> {
    let Some(mod_bytes) = ({
        let s3 = db.raw_stream(pdb::StreamIndex(3)).ok().flatten();
        s3.and_then(|s| {
            let (mod_len, _) = dbi_parts(s.as_slice())?;
            s.as_slice()
                .get(64..64usize.checked_add(mod_len)?)
                .map(<[u8]>::to_vec)
        })
    }) else {
        return Vec::new();
    };
    let mut flags = Vec::new();
    let mut pos = 0usize;
    while pos < mod_bytes.len() {
        let Some(hdr) = pos.checked_add(64).and_then(|end| mod_bytes.get(pos..end)) else {
            break;
        };
        let stream_id = u16_at(hdr, 34).unwrap_or(0xffff);
        let sym_sz = u32_at(hdr, 36).and_then(|v| usize::try_from(v).ok());
        let lines_sz = u32_at(hdr, 40).and_then(|v| usize::try_from(v).ok());
        let c13_sz = u32_at(hdr, 44).and_then(|v| usize::try_from(v).ok());
        let Some(after_mod) = skip_cstr(&mod_bytes, pos + 64) else {
            break;
        };
        let Some(after_obj) = skip_cstr(&mod_bytes, after_mod) else {
            break;
        };
        let next = after_obj.next_multiple_of(4);
        if next > mod_bytes.len() {
            break;
        }
        pos = next;
        let ok = match (sym_sz, lines_sz, c13_sz) {
            (Some(s), Some(l), Some(c)) if stream_id != 0xffff => {
                module_line_ok(db, stream_id, s, l, c).is_some()
            }
            _ => false,
        };
        flags.push(ok);
    }
    flags
}

/// Advances past one NUL-terminated byte string starting at `at`.
///
/// # Arguments
///
/// * `b` - Enclosing buffer.
/// * `at` - Start offset of the C string.
///
/// # Returns
///
/// Offset immediately past the NUL byte, or `None` when unterminated.
fn skip_cstr(b: &[u8], at: usize) -> Option<usize> {
    let rel = b.get(at..)?.iter().position(|&c| c == 0)?;
    at.checked_add(rel)?.checked_add(1)
}

/// Verifies one module's stream length and C13 `DEBUG_S_LINES` subsections.
///
/// # Arguments
///
/// * `db` - The opened PDB.
/// * `stream_id` - Module stream number from `DBIModuleInfo`.
/// * `sym_sz` - Stated `symbols_size` in bytes.
/// * `lines_sz` - Stated C11 `lines_size` in bytes.
/// * `c13_sz` - Stated C13 `c13_lines_size` in bytes.
///
/// # Returns
///
/// `Some(())` when `sym_sz + line_sz` fits inside the module stream and any C13 line
/// subsections obey block-size and monotonic-offset invariants.
fn module_line_ok<'s>(
    db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
    stream_id: u16,
    sym_sz: usize,
    lines_sz: usize,
    c13_sz: usize,
) -> Option<()> {
    let line_sz = if lines_sz > 0 { lines_sz } else { c13_sz };
    let end = sym_sz.checked_add(line_sz)?;
    let stream = db.raw_stream(pdb::StreamIndex(stream_id)).ok()??;
    let line_bytes = stream.as_slice().get(sym_sz..end)?;
    if lines_sz == 0 && !c13_lines_ok(line_bytes) {
        return None;
    }
    Some(())
}

/// Checks every `DEBUG_S_LINES` (`0xf2`) subsection in `data` against `pdb` 0.8.0's assertions.
///
/// # Arguments
///
/// * `data` - The module's C13 line-subsection bytes (`stream[symbols_size..end]`).
///
/// # Returns
///
/// `true` when every `0xf2` subsection has well-sized blocks and non-decreasing offsets
/// within `code_size` that do not overflow `u32` when added to the contribution's offset.
fn c13_lines_ok(data: &[u8]) -> bool {
    let mut pos = 0usize;
    while pos < data.len() {
        let (Some(kind), Some(len)) = (
            u32_at(data, pos),
            u32_at(data, pos + 4).and_then(|n| usize::try_from(n).ok()),
        ) else {
            return true;
        };
        let Some(body_end) = pos.checked_add(8).and_then(|p| p.checked_add(len)) else {
            return false;
        };
        let Some(body) = data.get(pos + 8..body_end) else {
            return true;
        };
        if kind == 0xf2 && !lines_subsection_ok(body) {
            return false;
        }
        pos = body_end;
    }
    true
}

/// Validates a single `DEBUG_S_LINES` (`0xf2`) subsection body.
///
/// # Arguments
///
/// * `body` - Subsection payload starting with the 12-byte `DebugLinesHeader`.
///
/// # Returns
///
/// `true` when header arithmetic, block sizes and line-entry offsets cannot panic in `pdb`.
fn lines_subsection_ok(body: &[u8]) -> bool {
    let (Some(sec_off), Some(flags), Some(code_size)) =
        (u32_at(body, 0), u16_at(body, 6), u32_at(body, 8))
    else {
        return true;
    };
    if sec_off.checked_add(code_size).is_none() {
        return false;
    }
    let per_line = if flags & 1 != 0 { 12usize } else { 8usize };
    let mut pos = 12usize;
    let mut prev_off: Option<u32> = None;
    while pos < body.len() {
        let (Some(num_lines), Some(block_size)) = (
            u32_at(body, pos + 4).and_then(|n| usize::try_from(n).ok()),
            u32_at(body, pos + 8).and_then(|n| usize::try_from(n).ok()),
        ) else {
            return true;
        };
        let Some(data_sz) = block_size.checked_sub(12) else {
            return false;
        };
        if num_lines.checked_mul(per_line) != Some(data_sz) {
            return false;
        }
        let Some(block_end) = pos.checked_add(12).and_then(|p| p.checked_add(data_sz)) else {
            return false;
        };
        let Some(entries) = body.get(pos + 12..pos + 12 + num_lines * 8) else {
            return true;
        };
        if body.len() < block_end {
            return true;
        }
        for entry in entries.chunks_exact(8) {
            let Some(off) = u32_at(entry, 0) else {
                return false;
            };
            let line_start = u32_at(entry, 4).unwrap_or(0) & 0x00ff_ffff;
            if matches!(line_start, 0xfee_fee | 0xf00_f00) {
                continue;
            }
            if off > code_size
                || sec_off.checked_add(off).is_none()
                || prev_off.is_some_and(|p| off < p)
            {
                return false;
            }
            prev_off = Some(off);
        }
        pos = block_end;
    }
    true
}

/// Checks Stream 1's named-stream map offsets before `db.string_table()` slices `&names_buf[off..]`.
///
/// # Arguments
///
/// * `db` - The opened PDB.
///
/// # Returns
///
/// `true` when every named-stream entry offset fits inside `names_size`.
pub(super) fn names_table_ok<'s>(db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>) -> bool {
    let Some(s1) = db.raw_stream(pdb::StreamIndex(1)).ok().flatten() else {
        return false;
    };
    let b = s1.as_slice();
    let Some(names_sz) = u32_at(b, 28).and_then(|n| usize::try_from(n).ok()) else {
        return false;
    };
    let Some(map_at) = 32usize.checked_add(names_sz) else {
        return false;
    };
    let (Some(count), Some(ok_words)) = (
        u32_at(b, map_at).and_then(|n| usize::try_from(n).ok()),
        u32_at(b, map_at + 8).and_then(|n| usize::try_from(n).ok()),
    ) else {
        return true;
    };
    let Some(del_at) = ok_words
        .checked_mul(4)
        .and_then(|n| map_at.checked_add(12)?.checked_add(n))
    else {
        return false;
    };
    let Some(del_words) = u32_at(b, del_at).and_then(|n| usize::try_from(n).ok()) else {
        return true;
    };
    let Some(mut cur) = del_words
        .checked_mul(4)
        .and_then(|n| del_at.checked_add(4)?.checked_add(n))
    else {
        return false;
    };
    let mut names_id = None;
    for _ in 0..count {
        let (Some(name_off), Some(stream_id)) = (
            u32_at(b, cur).and_then(|n| usize::try_from(n).ok()),
            u16_at(b, cur + 4),
        ) else {
            break;
        };
        if name_off > names_sz {
            return false;
        }
        if b.get(32 + name_off..32 + names_sz)
            .is_some_and(|s| s.starts_with(b"/names\0"))
        {
            names_id = Some(stream_id);
        }
        let Some(next) = cur.checked_add(8) else {
            return false;
        };
        cur = next;
    }
    if let Some(id) = names_id
        && let Some(ns) = db.raw_stream(pdb::StreamIndex(id)).ok().flatten()
    {
        return u32_at(ns.as_slice(), 8)
            .and_then(|n| usize::try_from(n).ok())
            .and_then(|n| 12usize.checked_add(n))
            .is_some_and(|end| end <= ns.as_slice().len());
    }
    true
}

/// Validated TPI stream index filter preventing panics and multi-gigabyte allocations in `pdb`.
#[derive(Debug, Default)]
pub(super) struct TpiGuard {
    /// Type indices whose raw record fails leaf-specific invariants.
    bad: BTreeSet<u32>,
}

impl TpiGuard {
    /// Checks Stream 2's header and scans its records for unsafe leaf payloads.
    ///
    /// # Arguments
    ///
    /// * `db` - The opened PDB.
    ///
    /// # Returns
    ///
    /// The guard when `TypeInformation::iter` and `finder` are safe to run, or `None` when
    /// Stream 2 is empty or its header indices or sizes would panic or over-allocate.
    pub(super) fn open<'s>(db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>) -> Option<Self> {
        let s2 = db.raw_stream(pdb::StreamIndex(2)).ok()??;
        let b = s2.as_slice();
        if b.len() < 56 || u32::try_from(b.len()).is_err() {
            return None;
        }
        let hdr_sz = usize::try_from(u32_at(b, 4)?).ok()?;
        let min_idx = u32_at(b, 8)?;
        let max_idx = u32_at(b, 12)?;
        if !(56..=1024).contains(&hdr_sz)
            || hdr_sz > b.len()
            || min_idx < 0x1000
            || max_idx < min_idx
        {
            return None;
        }
        let max_recs = u32::try_from((b.len() - hdr_sz) / 2).ok()?;
        if max_idx - min_idx > max_recs || min_idx.checked_add(max_recs).is_none() {
            return None;
        }
        let mut bad = BTreeSet::new();
        let mut pos = hdr_sz;
        let mut idx = min_idx;
        while let Some(rec_len) = u16_at(b, pos).map(usize::from) {
            if rec_len < 2 {
                break;
            }
            let Some(rec) = pos
                .checked_add(2)
                .and_then(|p| p.checked_add(rec_len))
                .and_then(|end| b.get(pos + 2..end))
            else {
                break;
            };
            if !tpi_record_ok(rec) {
                bad.insert(idx);
            }
            pos += 2 + rec_len;
            idx += 1;
        }
        Some(Self { bad })
    }

    /// Parses `item` only when its leaf is one `pdb.rs` consumes and its record passed checks.
    ///
    /// # Arguments
    ///
    /// * `item` - Type item returned by `TypeFinder::find`.
    ///
    /// # Returns
    ///
    /// The parsed `TypeData`, or `None` when skipped or malformed.
    pub(super) fn parse_type<'t>(&self, item: &pdb::Type<'t>) -> Option<pdb::TypeData<'t>> {
        let raw_idx = item.index().0;
        if raw_idx >= 0x1000 && (!is_signature_leaf(item.raw_kind()) || self.bad.contains(&raw_idx))
        {
            return None;
        }
        item.parse().ok()
    }
}

/// Whether `leaf` is one of the 19 `CodeView` type leaves signature resolution inspects.
///
/// # Arguments
///
/// * `leaf` - Raw 16-bit leaf kind of a TPI record.
///
/// # Returns
///
/// `true` when [`super::resolve`], [`super::arguments`] or [`super::type_text`] uses `leaf`.
fn is_signature_leaf(leaf: u16) -> bool {
    matches!(
        leaf,
        0x1001
            | 0x1002
            | 0x1003
            | 0x1004
            | 0x1005
            | 0x1006
            | 0x1007
            | 0x1008
            | 0x1009
            | 0x1201
            | 0x1205
            | 0x1503
            | 0x1504
            | 0x1505
            | 0x1506
            | 0x1507
            | 0x1516
            | 0x1519
            | 0x1609
    )
}

/// Checks leaf-specific invariants on one TPI record body `rec` (`leaf` included).
///
/// # Arguments
///
/// * `rec` - Record bytes after the two-byte length prefix.
///
/// # Returns
///
/// `true` when `pdb::Type::parse` cannot panic or over-allocate on `rec`.
fn tpi_record_ok(rec: &[u8]) -> bool {
    let Some(leaf) = u16_at(rec, 0) else {
        return false;
    };
    match leaf {
        0x1201 => u32_at(rec, 2)
            .and_then(|c| usize::try_from(c).ok())
            .and_then(|c| c.checked_mul(4)?.checked_add(6))
            .is_none_or(|need| need <= rec.len()),
        0x1003 | 0x1503 | 0x1516 => array_record_ok(rec, leaf == 0x1516),
        0x1004 | 0x1504 | 0x1005 | 0x1505 | 0x1519 => unsigned_prefix_ok(rec, 18),
        0x1609 => unsigned_prefix_ok(rec, 20),
        0x1006 | 0x1506 => unsigned_prefix_ok(rec, 10),
        _ => true,
    }
}

/// Checks that `parse_unsigned` at `at` will not hit `unreachable!()` on an unknown prefix.
///
/// # Arguments
///
/// * `rec` - TPI record bytes.
/// * `at` - Offset where `parse_unsigned` reads its two-byte prefix.
///
/// # Returns
///
/// `true` when `at` is past `rec` (`UnexpectedEof`) or holds an unsigned `LF_*` prefix.
fn unsigned_prefix_ok(rec: &[u8], at: usize) -> bool {
    u16_at(rec, at).is_none_or(|p| p < 0x8000 || matches!(p, 0x8000 | 0x8002 | 0x8004 | 0x800a))
}

/// Checks `LF_ARRAY*` records so `parse_unsigned` and `assert!(buf.is_empty())` cannot panic.
///
/// # Arguments
///
/// * `rec` - TPI record bytes.
/// * `strided` - Whether `rec` is `LF_STRIDED_ARRAY` (`0x1516`), which carries a 4-byte stride.
///
/// # Returns
///
/// `true` when `rec` either returns `Err` cleanly or leaves `buf` empty after padding.
fn array_record_ok(rec: &[u8], strided: bool) -> bool {
    let mut pos = if strided { 14usize } else { 10usize };
    loop {
        let Some(pfx) = u16_at(rec, pos) else {
            return true;
        };
        let step = if pfx < 0x8000 {
            2usize
        } else {
            match pfx {
                0x8000 => 3,
                0x8002 => 4,
                0x8004 => 6,
                0x800a => 10,
                _ => return false,
            }
        };
        if step == 10 {
            let Some(hi) = u32_at(rec, pos + 6) else {
                return true;
            };
            if hi != 0 {
                return true;
            }
        }
        pos += step;
        let Some(&next) = rec.get(pos) else {
            return true;
        };
        if next == 0 {
            pos += 1;
            break;
        }
    }
    while let Some(&pad) = rec.get(pos) {
        if pad < 0xf0 {
            break;
        }
        pos += 1;
        if pad > 0xf0 {
            let skip = usize::from(pad & 0x0f) - 1;
            if pos + skip > rec.len() {
                return true;
            }
            pos += skip;
        }
    }
    pos == rec.len()
}

/// Whether `kind` is one of the module-body symbol kinds `gather` parses (`Data`,
/// `RegisterRelative`, or `Local`), avoiding `S_CONSTANT`'s `Variant` `unreachable!()`.
///
/// # Arguments
///
/// * `kind` - Raw 16-bit symbol record kind.
///
/// # Returns
///
/// `true` when `kind` parses to `SymbolData::Data`, `RegisterRelative` or `Local`.
pub(super) fn is_body_symbol(kind: u16) -> bool {
    matches!(
        kind,
        0x1007 | 0x1008 | 0x1020 | 0x1021 | 0x110c | 0x110d | 0x1111 | 0x111c | 0x111d | 0x113e
    )
}

/// Gathers `S_PUB32` and `S_PUB32_ST` records from `db.global_symbols()` into `out`.
///
/// # Arguments
///
/// * `db` - The opened PDB.
/// * `map` - Address map translating section offsets to RVAs.
/// * `guard` - Checked RVA translation guard.
/// * `out` - Destination symbol accumulator.
pub(super) fn collect_globals<'s>(
    db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
    map: &pdb::AddressMap<'s>,
    guard: &AddrGuard,
    out: &mut super::Gathered,
) {
    use pdb::FallibleIterator as _;
    let Ok(globals) = db.global_symbols() else {
        return;
    };
    let mut it = globals.iter();
    while let Ok(Some(s)) = it.next() {
        if matches!(s.raw_kind(), 0x1009 | 0x110e)
            && let Ok(pdb::SymbolData::Public(p)) = s.parse()
        {
            let rva = guard.rva_of(map, p.offset);
            if p.function || p.code {
                out.take(rva, p.name, None, None);
            } else {
                out.take_data(rva, p.name);
            }
        }
    }
}

/// Frame pointer register numbers (`CV_REG_EBP` and `CV_AMD64_RBP`).
const FRAME_PTR: [u16; 2] = [22, 334];

/// Stack pointer register numbers (`CV_REG_ESP` and `CV_AMD64_RSP`).
const STACK_PTR: [u16; 2] = [21, 335];

/// Reads how far a procedure's frame reaches below the entry stack pointer from `S_FRAMEPROC`.
///
/// # Arguments
///
/// * `raw` - Raw `S_FRAMEPROC` bytes, kind included.
///
/// # Returns
///
/// Checked sum of frame size (`+2`) and saved-register bytes (`+14`), or `None` when truncated.
pub(super) fn frame_size(raw: &[u8]) -> Option<i64> {
    let word = |at: usize| u32_at(raw, at).map(i64::from);
    word(2)?.checked_add(word(14)?)
}

/// Reads the signed offset from a raw `S_DEFRANGE_FRAMEPOINTER_REL` record.
///
/// # Arguments
///
/// * `raw` - Raw symbol bytes, kind included.
///
/// # Returns
///
/// Signed offset from the frame base, or `None` when truncated.
pub(super) fn defrange_offset(raw: &[u8]) -> Option<i32> {
    Some(i32::from_le_bytes(raw.get(2..6)?.try_into().ok()?))
}

/// Reads `(register, offset)` from a raw `S_DEFRANGE_REGISTER_REL` record.
///
/// # Arguments
///
/// * `raw` - Raw symbol bytes, kind included.
///
/// # Returns
///
/// Register number and signed offset, or `None` when truncated.
pub(super) fn defrange_register(raw: &[u8]) -> Option<(u16, i32)> {
    Some((
        u16_at(raw, 2)?,
        i32::from_le_bytes(raw.get(6..10)?.try_into().ok()?),
    ))
}

/// Reads `(offset, name)` from a raw `S_BPREL32` record.
///
/// # Arguments
///
/// * `raw` - Raw symbol bytes, kind included.
///
/// # Returns
///
/// Signed frame-pointer offset and non-empty UTF-8 name, or `None` when truncated or invalid.
pub(super) fn bprel32(raw: &[u8]) -> Option<(i32, &str)> {
    let off = i32::from_le_bytes(raw.get(2..6)?.try_into().ok()?);
    let name = raw.get(10..)?;
    let end = name.iter().position(|&b| b == 0).unwrap_or(name.len());
    let name = std::str::from_utf8(&name[..end]).ok()?;
    (!name.is_empty()).then_some((off, name))
}

/// Maps `reg` to `Some(true)` for frame pointer, `Some(false)` for stack pointer, else `None`.
///
/// # Arguments
///
/// * `reg` - `CodeView` register number.
///
/// # Returns
///
/// Frame-base selector for [`crate::dwarf::frame_slot`].
pub(super) fn base_kind(reg: u16) -> Option<bool> {
    if FRAME_PTR.contains(&reg) {
        Some(true)
    } else if STACK_PTR.contains(&reg) {
        Some(false)
    } else {
        None
    }
}
