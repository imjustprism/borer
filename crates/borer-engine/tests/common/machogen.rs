//! A minimal 64-bit Mach-O writer for tests.
//!
//! Each segment's bytes sit at its file offset, the first one holding the
//! header and the load commands, which the writer lays over its first
//! bytes: a fixture keeps its first section past them. Every segment
//! command is written first, in the order given, then the extra commands
//! the fixture builds with the helpers here.

#![expect(
    clippy::expect_used,
    clippy::missing_panics_doc,
    reason = "a fixture whose fields do not fit has no useful recovery"
)]

/// `CPU_TYPE_X86_64`.
pub(crate) const X86_64: u32 = 0x0100_0007;
/// `CPU_TYPE_ARM64`.
pub(crate) const ARM64: u32 = 0x0100_000c;
/// `MH_EXECUTE`.
pub(crate) const EXECUTE: u32 = 2;
/// `MH_PIE`.
pub(crate) const PIE: u32 = 0x0020_0000;
/// `S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS`.
pub(crate) const CODE: u32 = 0x8000_0400;
/// `VM_PROT_READ | VM_PROT_EXECUTE`.
pub(crate) const RX: u32 = 5;
/// `VM_PROT_READ | VM_PROT_WRITE`.
pub(crate) const RW: u32 = 3;
/// `VM_PROT_READ`.
pub(crate) const R: u32 = 1;

/// One section of a segment.
pub(crate) struct Sect {
    /// Its name.
    pub(crate) name: &'static str,
    /// Its address.
    pub(crate) addr: u64,
    /// Its size in bytes.
    pub(crate) size: u64,
    /// Its flags: the type in the low byte, the attributes above.
    pub(crate) flags: u32,
}

/// One segment of a built image.
pub(crate) struct Seg {
    /// Its name.
    pub(crate) name: &'static str,
    /// Where it is mapped.
    pub(crate) vmaddr: u64,
    /// Its file offset.
    pub(crate) fileoff: u64,
    /// Its file bytes: the file size, and the memory size rounded up to a
    /// page.
    pub(crate) bytes: Vec<u8>,
    /// Its protection.
    pub(crate) prot: u32,
    /// Its sections, which must lie in its bytes.
    pub(crate) sections: Vec<Sect>,
}

/// Writes a little-endian value of `n` bytes at `off`, growing `out`.
///
/// # Arguments
///
/// * `out` - The image.
/// * `off` - The file offset.
/// * `v` - The value.
/// * `n` - Its width in bytes.
pub(crate) fn put(out: &mut Vec<u8>, off: usize, v: u64, n: usize) {
    if out.len() < off + n {
        out.resize(off + n, 0);
    }
    out[off..off + n].copy_from_slice(&v.to_le_bytes()[..n]);
}

/// Writes a NUL-padded 16-byte name at `off`.
///
/// # Arguments
///
/// * `out` - The image.
/// * `off` - The file offset.
/// * `name` - The name, at most 16 bytes.
fn name16(out: &mut Vec<u8>, off: usize, name: &str) {
    put(out, off, 0, 8);
    put(out, off + 8, 0, 8);
    out[off..off + name.len()].copy_from_slice(name.as_bytes());
}

/// A `linkedit_data_command` (`LC_FUNCTION_STARTS`,
/// `LC_DYLD_CHAINED_FIXUPS`) naming file bytes.
///
/// # Arguments
///
/// * `cmd` - The command.
/// * `off` - The data's file offset.
/// * `size` - Its size.
pub(crate) fn linkedit(cmd: u32, off: u64, size: usize) -> Vec<u8> {
    let mut out = Vec::new();
    put(&mut out, 0, u64::from(cmd), 4);
    put(&mut out, 4, 16, 4);
    put(&mut out, 8, off, 4);
    put(&mut out, 12, u64::try_from(size).expect("fits"), 4);
    out
}

/// An `LC_MAIN` entering at `entryoff` from `__TEXT`.
///
/// # Arguments
///
/// * `entryoff` - The entry's offset from the image base.
pub(crate) fn main(entryoff: u64) -> Vec<u8> {
    let mut out = Vec::new();
    put(&mut out, 0, 0x8000_0028, 4);
    put(&mut out, 4, 24, 4);
    put(&mut out, 8, entryoff, 8);
    put(&mut out, 16, 0, 8);
    out
}

/// An `LC_LOAD_DYLIB` naming `path`, padded to a multiple of eight.
///
/// # Arguments
///
/// * `path` - The install name.
pub(crate) fn dylib(path: &str) -> Vec<u8> {
    let size = (24 + path.len() + 1).div_ceil(8) * 8;
    let mut out = vec![0u8; size];
    put(&mut out, 0, 0xc, 4);
    put(&mut out, 4, u64::try_from(size).expect("small"), 4);
    put(&mut out, 8, 24, 4);
    out[24..24 + path.len()].copy_from_slice(path.as_bytes());
    out
}

/// An `LC_DYLD_INFO_ONLY` naming the rebase, bind and lazy bind programs.
///
/// # Arguments
///
/// * `rebase` - The rebase program's file offset and size.
/// * `bind` - The bind program's.
/// * `lazy` - The lazy bind program's.
pub(crate) fn dyld_info(rebase: (u64, usize), bind: (u64, usize), lazy: (u64, usize)) -> Vec<u8> {
    let mut out = vec![0u8; 48];
    put(&mut out, 0, 0x8000_0022, 4);
    put(&mut out, 4, 48, 4);
    for (k, (off, size)) in [rebase, bind, (0, 0), lazy].into_iter().enumerate() {
        put(&mut out, 8 + k * 8, off, 4);
        put(&mut out, 12 + k * 8, u64::try_from(size).expect("fits"), 4);
    }
    out
}

/// One segment's chain starts in a chained fixups payload.
pub(crate) struct Starts {
    /// The segment's index in load-command order.
    pub(crate) segment: usize,
    /// `DYLD_CHAINED_PTR_*`.
    pub(crate) format: u16,
    /// The segment's offset from the image base.
    pub(crate) offset: u64,
    /// Bytes per page.
    pub(crate) page_size: u16,
    /// Each page's first fixup's offset in the page, `0xffff` for none.
    pub(crate) pages: Vec<u16>,
}

/// An `LC_DYLD_CHAINED_FIXUPS` payload: the header, the starts of each
/// segment named, and a `DYLD_CHAINED_IMPORT` table.
///
/// # Arguments
///
/// * `segments` - How many segments the image has.
/// * `starts` - The segments with chains.
/// * `imports` - `(library ordinal, weak, name)` per import, the name with
///   its C underscore.
pub(crate) fn chained(segments: usize, starts: &[Starts], imports: &[(u8, bool, &str)]) -> Vec<u8> {
    let mut out = vec![0u8; 32];
    let starts_at = out.len();
    let index = starts_at + 4;
    let mut body = index + 4 * segments;
    out.resize(body, 0);
    put(
        &mut out,
        starts_at,
        u64::try_from(segments).expect("fits"),
        4,
    );
    for s in starts {
        let at = body - starts_at;
        put(
            &mut out,
            index + 4 * s.segment,
            u64::try_from(at).expect("fits"),
            4,
        );
        let size = 22 + 2 * s.pages.len();
        put(&mut out, body, u64::try_from(size).expect("fits"), 4);
        put(&mut out, body + 4, u64::from(s.page_size), 2);
        put(&mut out, body + 6, u64::from(s.format), 2);
        put(&mut out, body + 8, s.offset, 8);
        put(&mut out, body + 16, 0, 4);
        put(
            &mut out,
            body + 20,
            u64::try_from(s.pages.len()).expect("fits"),
            2,
        );
        for (k, p) in s.pages.iter().enumerate() {
            put(&mut out, body + 22 + 2 * k, u64::from(*p), 2);
        }
        body = (body + size).next_multiple_of(4);
        out.resize(body, 0);
    }
    let imports_at = out.len();
    let symbols_at = imports_at + 4 * imports.len();
    let mut names = vec![0u8];
    for (k, (ordinal, weak, name)) in imports.iter().enumerate() {
        let name_off = u64::try_from(names.len()).expect("fits");
        let raw = u64::from(*ordinal) | (u64::from(*weak) << 8) | (name_off << 9);
        put(&mut out, imports_at + 4 * k, raw, 4);
        names.extend_from_slice(name.as_bytes());
        names.push(0);
    }
    out.resize(symbols_at, 0);
    out.extend_from_slice(&names);
    let header = [0, starts_at, imports_at, symbols_at, imports.len(), 1, 0];
    for (k, v) in header.into_iter().enumerate() {
        put(&mut out, k * 4, u64::try_from(v).expect("fits"), 4);
    }
    out
}

/// Builds a 64-bit little-endian Mach-O.
///
/// # Arguments
///
/// * `cpu` - The CPU type.
/// * `flags` - The header flags.
/// * `segs` - The segments, in load-command order.
/// * `extra` - The other load commands, in order.
pub(crate) fn build(cpu: u32, flags: u32, segs: &[Seg], extra: &[Vec<u8>]) -> Vec<u8> {
    let mut out = Vec::new();
    for s in segs {
        let at = usize::try_from(s.fileoff).expect("fits");
        if out.len() < at + s.bytes.len() {
            out.resize(at + s.bytes.len(), 0);
        }
        out[at..at + s.bytes.len()].copy_from_slice(&s.bytes);
    }
    let mut cmds: Vec<u8> = Vec::new();
    for s in segs {
        let at = cmds.len();
        let size = 72 + 80 * s.sections.len();
        cmds.resize(at + size, 0);
        let len = u64::try_from(s.bytes.len()).expect("fits");
        put(&mut cmds, at, 0x19, 4);
        put(&mut cmds, at + 4, u64::try_from(size).expect("fits"), 4);
        name16(&mut cmds, at + 8, s.name);
        put(&mut cmds, at + 24, s.vmaddr, 8);
        put(&mut cmds, at + 32, len.next_multiple_of(0x1000), 8);
        put(&mut cmds, at + 40, s.fileoff, 8);
        put(&mut cmds, at + 48, len, 8);
        put(&mut cmds, at + 56, u64::from(s.prot), 4);
        put(&mut cmds, at + 60, u64::from(s.prot), 4);
        put(
            &mut cmds,
            at + 64,
            u64::try_from(s.sections.len()).expect("fits"),
            4,
        );
        for (k, sect) in s.sections.iter().enumerate() {
            let row = at + 72 + 80 * k;
            name16(&mut cmds, row, sect.name);
            name16(&mut cmds, row + 16, s.name);
            put(&mut cmds, row + 32, sect.addr, 8);
            put(&mut cmds, row + 40, sect.size, 8);
            put(&mut cmds, row + 48, s.fileoff + (sect.addr - s.vmaddr), 4);
            put(&mut cmds, row + 64, u64::from(sect.flags), 4);
        }
    }
    for c in extra {
        cmds.extend_from_slice(c);
    }
    let ncmds = segs.len() + extra.len();
    put(&mut out, 0, 0xfeed_facf, 4);
    put(&mut out, 4, u64::from(cpu), 4);
    put(&mut out, 8, 3, 4);
    put(&mut out, 12, u64::from(EXECUTE), 4);
    put(&mut out, 16, u64::try_from(ncmds).expect("fits"), 4);
    put(&mut out, 20, u64::try_from(cmds.len()).expect("fits"), 4);
    put(&mut out, 24, u64::from(flags), 4);
    out[32..32 + cmds.len()].copy_from_slice(&cmds);
    out
}
