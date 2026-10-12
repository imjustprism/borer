//! A minimal ELF64 writer for tests.
//!
//! Each section sits at the file offset equal to its address, one RWX
//! `PT_LOAD` maps the file from address 0, and a `PT_DYNAMIC` covers the
//! `.dynamic` section when there is one, so the loader reads the dynamic
//! table through the program headers as it does a linked image's. The
//! section header string table and the section headers follow the last
//! section.

#![expect(
    clippy::expect_used,
    reason = "a fixture whose fields do not fit has no useful recovery"
)]

/// `SHT_PROGBITS`.
pub(crate) const PROGBITS: u32 = 1;
/// `SHT_STRTAB`.
pub(crate) const STRTAB: u32 = 3;
/// `SHT_RELA`.
pub(crate) const RELA: u32 = 4;
/// `SHT_DYNAMIC`.
pub(crate) const DYNAMIC: u32 = 6;
/// `SHT_DYNSYM`.
pub(crate) const DYNSYM: u32 = 11;
/// `SHT_RELR`.
pub(crate) const RELR: u32 = 19;
/// `SHF_WRITE | SHF_ALLOC`.
pub(crate) const WA: u64 = 3;
/// `SHF_ALLOC`.
pub(crate) const A: u64 = 2;
/// `SHF_ALLOC | SHF_EXECINSTR`.
pub(crate) const AX: u64 = 6;
/// `ET_EXEC`.
pub(crate) const ET_EXEC: u16 = 2;
/// `ET_DYN`.
pub(crate) const ET_DYN: u16 = 3;
/// `EM_X86_64`.
pub(crate) const EM_X86_64: u16 = 62;

/// One section of a built image.
pub(crate) struct Sec {
    /// Its name.
    pub(crate) name: &'static str,
    /// `sh_type`.
    pub(crate) sh_type: u32,
    /// `sh_flags`.
    pub(crate) flags: u64,
    /// Its address, which is also its file offset; at least `0x1000`.
    pub(crate) addr: u64,
    /// Its bytes.
    pub(crate) data: Vec<u8>,
    /// `sh_link`: a section index, counting the null section as 0.
    pub(crate) link: u32,
    /// `sh_entsize`.
    pub(crate) entsize: u64,
}

impl Sec {
    /// A section with no link and no entry size.
    ///
    /// # Arguments
    ///
    /// * `name` - Its name.
    /// * `sh_type` - `sh_type`.
    /// * `flags` - `sh_flags`.
    /// * `addr` - Its address and file offset.
    /// * `data` - Its bytes.
    pub(crate) fn new(
        name: &'static str,
        sh_type: u32,
        flags: u64,
        addr: u64,
        data: Vec<u8>,
    ) -> Self {
        Sec {
            name,
            sh_type,
            flags,
            addr,
            data,
            link: 0,
            entsize: 0,
        }
    }
}

/// Writes a little-endian value of `n` bytes at `off`, growing `out`.
///
/// # Arguments
///
/// * `out` - The image.
/// * `off` - The file offset.
/// * `v` - The value.
/// * `n` - Its width in bytes.
fn put(out: &mut Vec<u8>, off: usize, v: u64, n: usize) {
    if out.len() < off + n {
        out.resize(off + n, 0);
    }
    out[off..off + n].copy_from_slice(&v.to_le_bytes()[..n]);
}

/// An `Elf64_Rela` entry.
///
/// # Arguments
///
/// * `offset` - `r_offset`, the slot.
/// * `sym` - The dynamic symbol index.
/// * `ty` - The relocation type.
/// * `addend` - `r_addend`.
pub(crate) fn rela(offset: u64, sym: u32, ty: u32, addend: i64) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&offset.to_le_bytes());
    out.extend_from_slice(&((u64::from(sym) << 32) | u64::from(ty)).to_le_bytes());
    out.extend_from_slice(&addend.to_le_bytes());
    out
}

/// An `Elf64_Sym` entry.
///
/// # Arguments
///
/// * `name` - Offset of its name in the string table.
/// * `info` - `st_info`: binding and type.
/// * `shndx` - The section it is defined in, 0 for an import.
/// * `value` - Its address.
pub(crate) fn sym(name: u32, info: u8, shndx: u16, value: u64) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&name.to_le_bytes());
    out.push(info);
    out.push(0);
    out.extend_from_slice(&shndx.to_le_bytes());
    out.extend_from_slice(&value.to_le_bytes());
    out.extend_from_slice(&0u64.to_le_bytes());
    out
}

/// A dynamic table from `(tag, value)` pairs, ended by `DT_NULL`.
///
/// # Arguments
///
/// * `entries` - The entries.
pub(crate) fn dynamic(entries: &[(u64, u64)]) -> Vec<u8> {
    let mut out = Vec::new();
    for (tag, value) in entries.iter().chain(&[(0, 0)]) {
        out.extend_from_slice(&tag.to_le_bytes());
        out.extend_from_slice(&value.to_le_bytes());
    }
    out
}

/// Builds an ELF64 little-endian image.
///
/// # Arguments
///
/// * `e_type` - `ET_EXEC` or `ET_DYN`.
/// * `machine` - `e_machine`.
/// * `entry` - The entry point.
/// * `secs` - The sections in table order, each at its address.
///
/// # Panics
///
/// When an address or a size does not fit the platform's `usize`.
pub(crate) fn build(e_type: u16, machine: u16, entry: u64, secs: &[Sec]) -> Vec<u8> {
    let mut out = vec![0u8; 0x1000];
    for s in secs {
        let at = usize::try_from(s.addr).expect("fits");
        if out.len() < at + s.data.len() {
            out.resize(at + s.data.len(), 0);
        }
        out[at..at + s.data.len()].copy_from_slice(&s.data);
    }
    let loaded = out.len();
    let mut shstr = vec![0u8];
    let mut names = Vec::new();
    for name in secs.iter().map(|s| s.name).chain([".shstrtab"]) {
        names.push(u32::try_from(shstr.len()).expect("fits"));
        shstr.extend_from_slice(name.as_bytes());
        shstr.push(0);
    }
    let shstr_off = out.len();
    out.extend_from_slice(&shstr);
    let shoff = out.len().next_multiple_of(8);
    let count = secs.len() + 2;
    out.resize(shoff + count * 64, 0);
    let header = |out: &mut Vec<u8>, i: usize, fields: [u64; 9]| {
        let off = shoff + i * 64;
        let [name, ty, flags, addr, offset, size, link, align, entsize] = fields;
        put(out, off, name, 4);
        put(out, off + 4, ty, 4);
        put(out, off + 8, flags, 8);
        put(out, off + 16, addr, 8);
        put(out, off + 24, offset, 8);
        put(out, off + 32, size, 8);
        put(out, off + 40, link, 4);
        put(out, off + 48, align, 8);
        put(out, off + 56, entsize, 8);
    };
    for (i, s) in secs.iter().enumerate() {
        let size = u64::try_from(s.data.len()).expect("fits");
        header(
            &mut out,
            i + 1,
            [
                u64::from(names[i]),
                u64::from(s.sh_type),
                s.flags,
                s.addr,
                s.addr,
                size,
                u64::from(s.link),
                8,
                s.entsize,
            ],
        );
    }
    let shstr_len = u64::try_from(shstr.len()).expect("fits");
    let shstr_at = u64::try_from(shstr_off).expect("fits");
    header(
        &mut out,
        secs.len() + 1,
        [
            u64::from(names[secs.len()]),
            u64::from(STRTAB),
            0,
            0,
            shstr_at,
            shstr_len,
            0,
            1,
            0,
        ],
    );
    let dynamic = secs.iter().find(|s| s.sh_type == DYNAMIC);
    out[..8].copy_from_slice(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0]);
    put(&mut out, 0x10, u64::from(e_type), 2);
    put(&mut out, 0x12, u64::from(machine), 2);
    put(&mut out, 0x14, 1, 4);
    put(&mut out, 0x18, entry, 8);
    put(&mut out, 0x20, 0x40, 8);
    put(&mut out, 0x28, u64::try_from(shoff).expect("fits"), 8);
    put(&mut out, 0x34, 64, 2);
    put(&mut out, 0x36, 56, 2);
    put(&mut out, 0x38, if dynamic.is_some() { 2 } else { 1 }, 2);
    put(&mut out, 0x3a, 64, 2);
    put(&mut out, 0x3c, u64::try_from(count).expect("fits"), 2);
    put(&mut out, 0x3e, u64::try_from(count - 1).expect("fits"), 2);
    let phdr = |out: &mut Vec<u8>, off: usize, ty: u64, at: u64, size: u64| {
        put(out, off, ty, 4);
        put(out, off + 4, 7, 4);
        put(out, off + 8, at, 8);
        put(out, off + 16, at, 8);
        put(out, off + 24, at, 8);
        put(out, off + 32, size, 8);
        put(out, off + 40, size, 8);
        put(out, off + 48, 0x1000, 8);
    };
    phdr(&mut out, 0x40, 1, 0, u64::try_from(loaded).expect("fits"));
    if let Some(d) = dynamic {
        let size = u64::try_from(d.data.len()).expect("fits");
        phdr(&mut out, 0x78, 2, d.addr, size);
    }
    out
}
