//! Dry-run patch planning for x86 and x86-64: given a target address and the
//! replacement machine code, work out the bytes to write without ever
//! touching the file on disk.
//!
//! A modding agent asks "replace the instructions at X with these bytes" and
//! gets back the whole original instructions the replacement overwrites (with
//! the `nop` padding named), the branch and RIP-relative references the new
//! code carries, whether the replacement fits in place or needs a code cave
//! (and which padding runs in executable sections are usable), a patch file
//! another tool applies, and an emulator check of the planned bytes.
//!
//! The replacement arrives as machine-code bytes, not assembly text:
//! iced-x86's `code_asm` feature is a programmatic builder, not a text
//! assembler, so there is no text to parse. [`assemble`] re-encodes those
//! bytes at their destination through iced's block encoder, which is what
//! fixes a relative branch or a RIP-relative load up when the code moves into
//! a cave.

use std::fmt::Write as _;

use crate::analysis::{Analysis, Overlay, resolve_suggesting};
use crate::disasm::{DisasmLine, disassemble, render};
use crate::emulate::{Emulator, Stop};
use crate::isa::Isa;
use crate::isa::x86::{
    BlockEncoder, BlockEncoderOptions, Code, Decoder, DecoderOptions, Instruction,
    InstructionBlock, OpKind,
};
use crate::program::Program;
use crate::text::hex;

/// Most replacement bytes a plan accepts: a patch is small, and a larger
/// request is a mistake worth refusing rather than a cave to detour into.
const MAX_NEW: usize = 1024;

/// Most original instructions a coverage scan decodes before giving up on an
/// in-place fit: a replacement that needs more than this many whole
/// instructions is detouring, not overwriting.
const MAX_ORIG_INSTRS: usize = 64;

/// Bytes a near relative jump encodes to (`e9` and a 32-bit displacement):
/// the smallest region a detour trampoline can overwrite.
const TRAMPOLINE_LEN: usize = 5;

/// Most usable code caves a plan lists.
const MAX_CAVES: usize = 16;

/// Shortest run of one padding byte that counts as a cave.
const CAVE_MIN: usize = 8;

/// Steps the emulator takes when checking the planned bytes.
const VERIFY_STEPS: usize = 256;

/// The byte an unused `nop` slot is filled with when a replacement is shorter
/// than the instructions it overwrites.
const NOP: u8 = 0x90;

/// A run of padding inside an executable section, usable to hold detoured
/// code.
#[derive(Debug, Clone, Copy)]
struct Cave {
    /// Virtual address of the run's first byte.
    va: u64,
    /// File offset of the run's first byte.
    off: u64,
    /// Length of the run in bytes.
    len: usize,
    /// The padding byte the run repeats.
    byte: u8,
}

/// One contiguous region a patch rewrites: the bytes there now and the bytes
/// to write, always the same length so the file never grows.
#[derive(Debug, Clone)]
struct Region {
    /// Virtual address of the first byte.
    va: u64,
    /// File offset of the first byte.
    off: u64,
    /// The bytes at the region now.
    old: Vec<u8>,
    /// The bytes to write, the same length as `old`.
    new: Vec<u8>,
    /// What the region is, for the plan's prose.
    role: &'static str,
}

/// What a parsed spec asks for.
#[derive(Debug)]
struct Spec<'a> {
    /// The target, an address or a name.
    at: &'a str,
    /// The replacement bytes.
    new: Vec<u8>,
    /// Force a detour through a cave even when the bytes would fit in place.
    detour: bool,
    /// A cave to use, as the caller named it, instead of searching.
    cave: Option<&'a str>,
}

/// Plans a patch and renders it, the body of `borer://patch/{spec}`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - For resolving a name to its address.
/// * `overlay` - For resolving a user name.
/// * `spec` - `<at>/<hexbytes>[,detour][,cave=<addr>]`.
///
/// # Returns
///
/// The plan as `#`-headed tables.
///
/// # Errors
///
/// When the image is not x86, the spec does not read, the target is unmapped
/// or not in an executable section, the bytes do not decode, or no cave holds
/// a detour that does not fit in place.
pub fn plan_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    spec: &str,
) -> Result<String, String> {
    let Some(Isa::X86 { bits }) = program.arch.isa() else {
        return Err("patch planning is x86 and x86-64 only".to_owned());
    };
    let spec = parse_spec(spec)?;
    let at = resolve_suggesting(program, analysis, overlay, spec.at)?;
    let section = program
        .section_at(at)
        .filter(|s| s.executable)
        .ok_or_else(|| format!("{at:#x} is not in an executable section"))?;
    let new_instrs = decode_all(&spec.new, at, bits)?;
    let assembled = assemble(&new_instrs, at, bits)?;
    let mut out = format!(
        "# patch {at:#x} in {} ({bits}-bit): {} bytes of new code\n",
        section.name,
        assembled.len()
    );
    out.push_str(&references(&new_instrs, "new code"));
    let detour = spec.detour || coverage(program, at, assembled.len()).is_none();
    let regions = if detour {
        plan_detour(
            program,
            analysis,
            overlay,
            at,
            &new_instrs,
            spec.cave,
            &mut out,
        )?
    } else {
        plan_in_place(program, at, &assembled, &mut out)?
    };
    out.push_str(&patch_file(program, &regions));
    out.push_str(&verify(program, at, &regions));
    Ok(out)
}

/// Reads a spec into its parts.
///
/// # Arguments
///
/// * `spec` - The URI argument.
///
/// # Errors
///
/// When the spec has no `/`, the bytes are missing or not hex pairs, an
/// option is unknown, or the bytes run past [`MAX_NEW`].
fn parse_spec(spec: &str) -> Result<Spec<'_>, String> {
    let (at, rest) = spec
        .split_once('/')
        .ok_or("expected borer://patch/<at>/<hexbytes>[,detour][,cave=<addr>]")?;
    let mut parts = rest.split(',');
    let hex = parts.next().unwrap_or("");
    let new = crate::text::parse_hex_bytes(hex).ok_or_else(|| {
        format!(
            "the replacement is pairs of hex digits, not {}",
            crate::text::quoted(hex)
        )
    })?;
    if new.is_empty() {
        return Err("the replacement is empty; give the new code as hex bytes".to_owned());
    }
    if new.len() > MAX_NEW {
        return Err(format!("the replacement is at most {MAX_NEW} bytes"));
    }
    let mut out = Spec {
        at: at.trim(),
        new,
        detour: false,
        cave: None,
    };
    for opt in parts {
        match opt.trim() {
            "detour" => out.detour = true,
            o => match o.strip_prefix("cave=") {
                Some(addr) => out.cave = Some(addr.trim()),
                None => return Err(format!("unknown option {}", crate::text::quoted(o))),
            },
        }
    }
    Ok(out)
}

/// Decodes bytes into whole instructions at a virtual address.
///
/// # Arguments
///
/// * `bytes` - The machine code.
/// * `va` - Where the code is imagined to sit, so a relative branch reads as
///   the absolute target the caller meant.
/// * `bits` - 32 or 64.
///
/// # Returns
///
/// The decoded instructions.
///
/// # Errors
///
/// When a byte does not start a valid instruction, or the last instruction is
/// cut off by the end of the bytes.
fn decode_all(bytes: &[u8], va: u64, bits: u32) -> Result<Vec<Instruction>, String> {
    let mut decoder = Decoder::with_ip(bits, bytes, va, DecoderOptions::NONE);
    let mut instrs = Vec::new();
    while decoder.can_decode() {
        let offset = decoder.position();
        let instr = decoder.decode();
        if instr.code() == Code::INVALID {
            return Err(format!(
                "the replacement does not decode at offset {offset}"
            ));
        }
        instrs.push(instr);
    }
    Ok(instrs)
}

/// Encodes instructions at a virtual address, fixing relative branches and
/// RIP-relative operands up to the new address.
///
/// # Arguments
///
/// * `instrs` - The instructions to encode.
/// * `ip` - Where the first instruction will sit.
/// * `bits` - 32 or 64.
///
/// # Returns
///
/// The encoded bytes.
///
/// # Errors
///
/// When iced cannot encode an instruction at `ip` (an operand out of range).
fn assemble(instrs: &[Instruction], ip: u64, bits: u32) -> Result<Vec<u8>, String> {
    let block = InstructionBlock::new(instrs, ip);
    BlockEncoder::encode(bits, block, BlockEncoderOptions::NONE)
        .map(|r| r.code_buffer)
        .map_err(|e| format!("the bytes do not encode at {ip:#x}: {e}"))
}

/// Lists the position-dependent references a run of code carries: direct
/// branches and RIP-relative memory operands, each with its absolute target.
///
/// These are what a detour's encoder fixes up, and what an in-place patch
/// keeps pointing where it did.
///
/// # Arguments
///
/// * `instrs` - The instructions.
/// * `what` - The code's name, for the header.
///
/// # Returns
///
/// A `#`-headed table, or a one-line note when there are none.
fn references(instrs: &[Instruction], what: &str) -> String {
    let mut rows = String::new();
    for i in instrs {
        if i.op_kinds().any(|k| {
            matches!(
                k,
                OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
            )
        }) {
            let _ = writeln!(rows, "{:#x}\tbranch\t{:#x}", i.ip(), i.near_branch_target());
        } else if i.is_ip_rel_memory_operand() {
            let _ = writeln!(
                rows,
                "{:#x}\trip-rel\t{:#x}",
                i.ip(),
                i.memory_displacement64()
            );
        }
    }
    if rows.is_empty() {
        return format!("# references in {what}: none\n");
    }
    format!("# references in {what}: va kind target\n{rows}")
}

/// Finds the whole original instructions a replacement of `need` bytes
/// overwrites, starting at `at`.
///
/// # Arguments
///
/// * `program` - The image.
/// * `at` - The target address.
/// * `need` - Bytes the replacement is long.
///
/// # Returns
///
/// The covered instructions and their total byte length (at least `need`), or
/// `None` when whole instructions cannot cover `need` within the section's
/// file bytes.
fn coverage(program: &Program, at: u64, need: usize) -> Option<(Vec<DisasmLine>, usize)> {
    let bits = program.arch.bitness()?;
    let window = program.read_va_upto(at, need.saturating_add(16).max(need))?;
    let lines = disassemble(window, at, bits, MAX_ORIG_INSTRS);
    let mut covered = 0usize;
    let mut out = Vec::new();
    for line in lines {
        if line.text == "(bad)" || line.bytes.is_empty() {
            return None;
        }
        covered = covered.saturating_add(line.bytes.len());
        out.push(line);
        if covered >= need {
            return Some((out, covered));
        }
    }
    None
}

/// Plans an in-place overwrite: the replacement, then `nop` padding out to the
/// end of the whole instructions it lands on.
///
/// # Arguments
///
/// * `program` - The image.
/// * `at` - The target address.
/// * `assembled` - The replacement bytes.
/// * `out` - The plan being built.
///
/// # Returns
///
/// The single region to rewrite.
///
/// # Errors
///
/// When the target's bytes are not readable or do not map to a file offset.
fn plan_in_place(
    program: &Program,
    at: u64,
    assembled: &[u8],
    out: &mut String,
) -> Result<Vec<Region>, String> {
    let (orig, covered) = coverage(program, at, assembled.len())
        .ok_or_else(|| format!("whole instructions at {at:#x} cannot cover the replacement"))?;
    let pad = covered.saturating_sub(assembled.len());
    let _ = write!(
        out,
        "# fit: in place, overwriting {covered} bytes ({} instructions), {pad} nop padding\n# overwrites: va bytes text\n",
        orig.len()
    );
    out.push_str(&render(&orig, true));
    let (off, old) = file_bytes(program, at, covered, out)?;
    let mut new = assembled.to_vec();
    new.resize(covered, NOP);
    Ok(vec![Region {
        va: at,
        off,
        old,
        new,
        role: "patch",
    }])
}

/// Plans a detour through a code cave.
///
/// A `jmp` to the cave replaces the whole instructions at the target, and the
/// cave holds the new code then a `jmp` back to just after them. The replaced
/// instructions are not re-run: the new code stands in for them, as for an
/// in-place patch; only a hook that keeps the original behavior would re-run
/// them, and this is a replacement.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - For resolving a named cave.
/// * `overlay` - For user names.
/// * `at` - The target address.
/// * `new_instrs` - The replacement, decoded.
/// * `cave_opt` - A cave the caller named, or `None` to search.
/// * `out` - The plan being built.
///
/// # Returns
///
/// The trampoline region and the cave region.
///
/// # Errors
///
/// When the target cannot hold a trampoline, no cave is large enough, a named
/// cave is unusable, or encoding fails.
fn plan_detour(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    at: u64,
    new_instrs: &[Instruction],
    cave_opt: Option<&str>,
    out: &mut String,
) -> Result<Vec<Region>, String> {
    let bits = program.arch.bitness().unwrap_or(64);
    let (orig, covered) = coverage(program, at, TRAMPOLINE_LEN)
        .ok_or_else(|| format!("{at:#x} has no room for a {TRAMPOLINE_LEN}-byte jump"))?;
    let back = at.saturating_add(crate::num::from_usize(covered));
    let body = |cave_va: u64| -> Result<Vec<u8>, String> {
        let mut out = assemble(new_instrs, cave_va, bits)?;
        let before_jmp = cave_va.saturating_add(crate::num::from_usize(out.len()));
        out.extend_from_slice(&assemble(&[near_jmp(bits, back)?], before_jmp, bits)?);
        Ok(out)
    };
    let avoid = (at, back);
    let fits = |c: &Cave| body(c.va).is_ok_and(|b| b.len() <= c.len);
    let caves = find_caves(program, at, avoid, fits);
    let cave = choose_cave(program, analysis, overlay, &caves, cave_opt, avoid)?;
    let code = body(cave.va)?;
    if code.len() > cave.len {
        return Err(format!(
            "the detour needs {} bytes but the cave at {:#x} holds {}",
            code.len(),
            cave.va,
            cave.len
        ));
    }
    let used = (
        cave.va,
        cave.va.saturating_add(crate::num::from_usize(code.len())),
    );
    if overlaps(used, avoid) {
        return Err(format!(
            "the cave at {:#x} overlaps the bytes the jump overwrites",
            cave.va
        ));
    }
    let trampoline = assemble(&[near_jmp(bits, cave.va)?], at, bits)?;
    if trampoline.len() > covered {
        return Err(format!(
            "the jump to the cave at {:#x} is {} bytes but only {covered} were reserved; the cave is too far for a short jump",
            cave.va,
            trampoline.len()
        ));
    }
    let _ = write!(
        out,
        "# fit: detour to a cave at {:#x}, overwriting {covered} bytes ({} instructions), {} nop padding\n# overwrites: va bytes text\n",
        cave.va,
        orig.len(),
        covered.saturating_sub(trampoline.len())
    );
    out.push_str(&render(&orig, true));
    out.push_str(&caves_table(&caves, cave.va));
    let mut tramp = trampoline;
    tramp.resize(covered, NOP);
    let (at_off, at_old) = file_bytes(program, at, covered, out)?;
    let (cave_off, cave_old) = file_bytes(program, cave.va, code.len(), out)?;
    Ok(vec![
        Region {
            va: at,
            off: at_off,
            old: at_old,
            new: tramp,
            role: "trampoline",
        },
        Region {
            va: cave.va,
            off: cave_off,
            old: cave_old,
            new: code,
            role: "cave",
        },
    ])
}

/// Builds a near relative jump to an absolute target.
///
/// # Arguments
///
/// * `bits` - 32 or 64.
/// * `target` - The absolute address to jump to.
///
/// # Errors
///
/// When iced rejects the branch.
fn near_jmp(bits: u32, target: u64) -> Result<Instruction, String> {
    let code = if bits == 64 {
        Code::Jmp_rel32_64
    } else {
        Code::Jmp_rel32_32
    };
    Instruction::with_branch(code, target).map_err(|e| format!("cannot build a jump: {e}"))
}

/// Picks the cave to detour into: the one the caller named, else the first
/// listed run.
///
/// # Arguments
///
/// * `program` - The image, for a named cave's section and run.
/// * `analysis` - For resolving a named cave.
/// * `overlay` - For a user name.
/// * `caves` - The runs the detour encodes at and fits in, longest first.
/// * `named` - A cave address or name the caller gave, or `None`.
/// * `avoid` - The `[start, end)` the trampoline overwrites, which a cave must
///   not touch.
///
/// # Errors
///
/// When a named cave does not resolve, is out of a jump's reach or is not a
/// padding run in executable code, or when no run is listed. [`plan_detour`] checks a named cave's length and overlap
/// against the code it encodes there.
fn choose_cave(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    caves: &[Cave],
    named: Option<&str>,
    avoid: (u64, u64),
) -> Result<Cave, String> {
    if let Some(text) = named {
        let va = resolve_suggesting(program, analysis, overlay, text)?;
        if !reachable(program, avoid.0, va) {
            return Err(format!(
                "the cave {va:#x} is too far from {:#x} for a relative jump",
                avoid.0
            ));
        }
        let (len, byte) = padding_run(program, va).ok_or_else(|| {
            format!("the cave {va:#x} is not a run of padding (00, cc or 90) in executable code")
        })?;
        let off = program
            .va_to_offset(va)
            .ok_or_else(|| format!("the cave {va:#x} has no file offset"))?;
        return Ok(Cave { va, off, len, byte });
    }
    caves
        .first()
        .copied()
        .ok_or_else(|| "no code cave holds the detour and encodes it; free a larger run".to_owned())
}

/// Measures the run of a single padding byte (`00`, `cc` or `90`) starting at
/// `va` inside its executable section's file bytes.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The run's first byte.
///
/// # Returns
///
/// The run's length and byte, or `None` when `va` is not padding in an
/// executable section.
fn padding_run(program: &Program, va: u64) -> Option<(usize, u8)> {
    let s = program.section_at(va).filter(|s| s.executable)?;
    let bytes = program.section_bytes(s)?;
    let start = usize::try_from(va.checked_sub(s.va.0)?).ok()?;
    let byte = *bytes.get(start)?;
    if !matches!(byte, 0x00 | 0xcc | NOP) {
        return None;
    }
    let len = bytes
        .get(start..)?
        .iter()
        .take_while(|&&b| b == byte)
        .count();
    Some((len, byte))
}

/// Finds candidate code caves for a detour.
///
/// A cave is a run of a single padding byte (`00`, `cc` or `90`) at least
/// [`CAVE_MIN`] long inside an executable section, in reach of a relative jump
/// from `at`, clear of the bytes the trampoline overwrites and holding the
/// detour as it encodes there (the longest run may be out of reach of an
/// operand the new code reads, so this is checked before the cap). These are
/// candidates, not proven-free space: a run of `90` or `00` can be real
/// instructions on a path the plan has not ruled out, so the caller confirms a
/// cave before trusting it.
///
/// # Arguments
///
/// * `program` - The image.
/// * `at` - The patch site, for the reachability filter.
/// * `avoid` - The `[start, end)` the trampoline overwrites.
/// * `fits` - Whether the detour encodes at a run and fits in it.
///
/// # Returns
///
/// Up to [`MAX_CAVES`] caves, longest first, then by address.
fn find_caves(
    program: &Program,
    at: u64,
    avoid: (u64, u64),
    fits: impl Fn(&Cave) -> bool,
) -> Vec<Cave> {
    let mut caves = Vec::new();
    for s in program.sections.iter().filter(|s| s.executable) {
        let Some(bytes) = program.section_bytes(s) else {
            continue;
        };
        let mut i = 0usize;
        while i < bytes.len() {
            let byte = bytes[i];
            let mut j = i;
            while j < bytes.len() && bytes[j] == byte {
                j += 1;
            }
            let len = j - i;
            let va = s.va.0.saturating_add(crate::num::from_usize(i));
            let end = s.va.0.saturating_add(crate::num::from_usize(j));
            if matches!(byte, 0x00 | 0xcc | NOP)
                && len >= CAVE_MIN
                && reachable(program, at, va)
                && !overlaps((va, end), avoid)
            {
                let cave = Cave {
                    va,
                    off: s.file_off.0.saturating_add(crate::num::from_usize(i)),
                    len,
                    byte,
                };
                if fits(&cave) {
                    caves.push(cave);
                }
                if caves.len() >= MAX_CAVES * 2 {
                    keep_best(&mut caves);
                }
            }
            i = j;
        }
    }
    keep_best(&mut caves);
    caves
}

/// Keeps the [`MAX_CAVES`] longest caves, ties by address.
///
/// # Arguments
///
/// * `caves` - The caves found so far.
fn keep_best(caves: &mut Vec<Cave>) {
    caves.sort_by(|a, b| b.len.cmp(&a.len).then(a.va.cmp(&b.va)));
    caves.truncate(MAX_CAVES);
}

/// Tells whether the trampoline's relative jump at `at` reaches `va`: its
/// displacement counts from the jump's end, and in 32-bit code it wraps, so
/// every address does.
///
/// # Arguments
///
/// * `program` - The image, for its bitness.
/// * `at` - The jump's address.
/// * `va` - The target.
fn reachable(program: &Program, at: u64, va: u64) -> bool {
    let end = at.wrapping_add(crate::num::from_usize(TRAMPOLINE_LEN));
    let delta = i128::from(va) - i128::from(end);
    program.arch.bitness() == Some(32) || i32::try_from(delta).is_ok()
}

/// Tells whether two `[start, end)` ranges share a byte.
///
/// # Arguments
///
/// * `a` - One range.
/// * `b` - The other.
fn overlaps(a: (u64, u64), b: (u64, u64)) -> bool {
    a.0 < b.1 && b.0 < a.1
}

/// Renders the cave candidates, marking the one chosen.
///
/// # Arguments
///
/// * `caves` - The usable runs.
/// * `chosen` - The address of the one the plan uses.
fn caves_table(caves: &[Cave], chosen: u64) -> String {
    let mut out = String::from("# caves: va off size byte used\n");
    for c in caves {
        let _ = writeln!(
            out,
            "{:#x}\t{:#x}\t{}\t{:#04x}\t{}",
            c.va,
            c.off,
            c.len,
            c.byte,
            if c.va == chosen { "yes" } else { "" }
        );
    }
    if caves.is_empty() {
        out.push_str("# none\n");
    }
    out.push_str(
        "# caves are padding runs, candidates only: not proven unreachable, confirm before use\n",
    );
    out
}

/// Reads the raw file bytes at `va`'s file offset, the bytes a patch's `old`
/// column must match on disk.
///
/// The disassembly and the plan read the loaded image ([`Program::read_va`]),
/// which carries an ELF's dynamic relocations; a patch applier reads the file.
/// When the two differ in the range, the loader rewrites bytes there, so a
/// `# warning:` line is appended and the applier's byte check would want the
/// file's bytes, which this returns.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The range's first byte.
/// * `len` - The range's length.
/// * `out` - The plan, for a relocation warning.
///
/// # Returns
///
/// The file offset and the `len` raw file bytes there.
///
/// # Errors
///
/// When `va` has no file offset or the file holds fewer than `len` bytes there.
fn file_bytes(
    program: &Program,
    va: u64,
    len: usize,
    out: &mut String,
) -> Result<(u64, Vec<u8>), String> {
    let off = program
        .va_to_offset(va)
        .ok_or_else(|| format!("{va:#x} has no file offset"))?;
    let raw = program
        .read_off_upto(off, len)
        .filter(|b| b.len() == len)
        .ok_or_else(|| format!("{va:#x} is not {len} file bytes"))?
        .to_vec();
    if program.read_va(va, len) != Some(raw.as_slice()) {
        let _ = writeln!(
            out,
            "# warning: a loader relocation rewrites bytes in {va:#x}..{:#x}; the plan reads the loaded image, the file differs",
            va.saturating_add(crate::num::from_usize(len))
        );
    }
    Ok((off, raw))
}

/// Renders the patch file: a documented header and one line per region.
///
/// Each line is `<file-offset> <old-bytes> <new-bytes>`, all hex, `old` and
/// `new` the same length. An applier seeks the offset, checks the bytes there
/// equal `old`, and writes `new`; borer itself writes nothing.
///
/// # Arguments
///
/// * `program` - The image, for its path in the header.
/// * `regions` - The regions to rewrite.
fn patch_file(program: &Program, regions: &[Region]) -> String {
    let mut out = String::from("# patchfile borer-patch-v1\n");
    let _ = writeln!(out, "# file {}", program.path.display());
    out.push_str("# format: <file-offset-hex> <old-hex> <new-hex>, equal length, verify old before writing new\n");
    for r in regions {
        let _ = writeln!(
            out,
            "{:#x} {} {}\t# {} at {:#x}",
            r.off,
            hex(&r.old),
            hex(&r.new),
            r.role,
            r.va
        );
    }
    out
}

/// Emulates the planned bytes in place from `at` and reports whether the
/// machine stepped through them without faulting on them.
///
/// The check is best-effort: it confirms the bytes decode and run, not that
/// the patch is correct. It says so, and says when it could not run at all.
///
/// # Arguments
///
/// * `program` - The image.
/// * `at` - Where execution starts.
/// * `regions` - The regions, poked into the machine before running.
fn verify(program: &Program, at: u64, regions: &[Region]) -> String {
    let Some(mut emu) = Emulator::new(program, VERIFY_STEPS) else {
        return "# verify: not run, no emulator for this image\n".to_owned();
    };
    emu.set_permissive(true);
    emu.set_fill(Some(0));
    for r in regions {
        emu.poke_run(r.va, &r.new);
    }
    let run = emu.run(at);
    let clean = matches!(
        run.stop,
        Stop::Returned | Stop::Stopped(_) | Stop::Budget | Stop::Exited | Stop::Limit(_)
    );
    if clean {
        format!(
            "# verify: emulated {} steps from {at:#x}, stop={}; the bytes decoded and ran with no fault, deeper behavior unchecked\n",
            run.steps, run.stop
        )
    } else {
        format!(
            "# verify: emulated {} steps from {at:#x}, stop={}; the machine faulted on the run, the planned bytes are not confirmed\n",
            run.steps, run.stop
        )
    }
}

#[cfg(test)]
mod tests {
    use super::plan_tsv;
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program, Section};

    /// Plans a patch against a one-page x86-64 image whose code starts at
    /// `0x1000` and whose tail is `int3` padding.
    ///
    /// # Arguments
    ///
    /// * `code` - The bytes at `0x1000`.
    /// * `spec` - The patch spec.
    ///
    /// # Errors
    ///
    /// As [`plan_tsv`] refuses the spec.
    fn plan(code: &[u8], spec: &str) -> Result<String, String> {
        let p = Program::raw_x64(code);
        let a = Analysis::compute(&p);
        plan_tsv(&p, &a, &Overlay::default(), spec)
    }

    /// A replacement shorter than the instruction it lands on is planned in
    /// place with `nop` padding, and its patch line keeps the old and new
    /// bytes the same length.
    ///
    /// # Panics
    ///
    /// When the fit, the padding, the patch line or the verify line is wrong.
    #[test]
    fn a_short_replacement_is_planned_in_place_with_nop_padding() {
        let out = plan(
            &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3], // ASM: mov eax,1 ; ret
            "0x1000/31c0",                         // ASM: xor eax,eax
        )
        .expect("a plan");
        assert!(
            out.contains("# fit: in place, overwriting 5 bytes (1 instructions), 3 nop padding"),
            "{out}"
        );
        assert!(out.contains("# patchfile borer-patch-v1"), "{out}");
        assert!(out.contains("0x0 b801000000 31c0909090"), "{out}");
        assert!(out.contains("# references in new code: none"), "{out}");
        assert!(out.contains("# verify: emulated"), "{out}");
    }

    /// Forcing a detour writes a jump over the target and lays the new code,
    /// the displaced instruction and a jump back into a cave, listing the
    /// caves and emitting two patch lines.
    ///
    /// # Panics
    ///
    /// When the fit, the caves table or the two regions are wrong.
    #[test]
    fn a_detour_uses_a_cave_and_emits_two_regions() {
        let out = plan(
            &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3], // ASM: mov eax,1 ; ret
            "0x1000/90,detour",                    // ASM: nop
        )
        .expect("a plan");
        assert!(out.contains("# fit: detour to a cave at 0x1006"), "{out}");
        assert!(out.contains("# caves: va off size byte used"), "{out}");
        assert!(out.contains("# trampoline at 0x1000"), "{out}");
        assert!(out.contains("# cave at 0x1006"), "{out}");
    }

    /// A detour replaces the instructions it jumps over: the cave holds the
    /// new code and a jump back, never a replay of the replaced bytes.
    ///
    /// # Panics
    ///
    /// When the replaced `mov eax,1` is re-emitted into the cave.
    #[test]
    fn a_detour_does_not_replay_the_replaced_instructions() {
        let out = plan(
            &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3], // ASM: mov eax,1 ; ret
            "0x1000/31c0,detour",                  // ASM: xor eax,eax
        )
        .expect("a plan");
        let cave_line = out
            .lines()
            .find(|l| l.contains("# cave at"))
            .expect("a cave region line");
        assert!(
            !cave_line.contains("b801000000"),
            "replayed the replaced mov into the cave: {cave_line}"
        );
        assert!(
            cave_line.contains("31c0"),
            "cave begins with the new code: {cave_line}"
        );
    }

    /// A named cave that overlaps the bytes the jump overwrites is refused, so
    /// the plan never emits two regions that write over each other.
    ///
    /// # Panics
    ///
    /// When the overlapping cave is accepted.
    #[test]
    fn a_cave_over_the_patch_site_is_refused() {
        let err = plan(
            &[0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0xc3], // ASM: nop x6 ; ret
            "0x1000/cc,detour,cave=0x1000",
        )
        .unwrap_err();
        assert!(err.contains("overlap"), "{err}");
    }

    /// A detour skips a longer cave its new code cannot encode at and takes
    /// the next listed one that holds it.
    ///
    /// The `rip`-relative load reads `0x17fffffff`: from the longest run at
    /// `0x80001000` that is past a 32-bit displacement, from the run beside
    /// the site it is not.
    ///
    /// # Panics
    ///
    /// When the plan is refused or picks the far cave.
    #[test]
    fn a_detour_skips_a_cave_its_code_cannot_encode_at() {
        let mut bytes = vec![0xcc; 0x200];
        bytes[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1 ; ret
        let site = Section::mapped(".text", 0x1_0000_0000, 0, 0x40, false, true);
        let far = Section::mapped(".far", 0x8000_1000, 0x100, 0x100, false, true);
        let p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1_0000_0000), vec![site, far]);
        let a = Analysis::compute(&p);
        let out = plan_tsv(
            &p,
            &a,
            &Overlay::default(),
            "0x100000000/488b05f8ffff7f,detour", // ASM: mov rax,[rip+0x7ffffff8]
        )
        .expect("a plan");
        assert!(
            out.contains("# fit: detour to a cave at 0x10000000"),
            "{out}"
        );
    }

    /// In 32-bit code a jump's displacement wraps, so a cave at the top of
    /// the address space is in reach of a patch at its bottom.
    ///
    /// # Panics
    ///
    /// When the far cave is refused.
    #[test]
    fn a_32_bit_detour_reaches_across_the_address_space() {
        let mut bytes = vec![0xcc; 0x200];
        bytes[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1 ; ret
        let site = Section::mapped(".text", 0x1000, 0, 0x6, false, true);
        let top = Section::mapped(".top", 0xffff_0000, 0x100, 0x40, false, true);
        let p = Program::raw(bytes, Arch::X86, 0, Some(0x1000), vec![site, top]);
        let a = Analysis::compute(&p);
        let out = plan_tsv(
            &p,
            &a,
            &Overlay::default(),
            "0x1000/90,detour,cave=0xffff0000",
        )
        .expect("a plan");
        assert!(
            out.contains("# fit: detour to a cave at 0xffff0000"),
            "{out}"
        );
    }

    /// A request to place a cave by address encodes the body there.
    ///
    /// # Panics
    ///
    /// When the named cave is not used.
    #[test]
    fn a_named_cave_is_used() {
        let out = plan(
            &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3], // ASM: mov eax,1 ; ret
            "0x1000/90,detour,cave=0x1100",
        )
        .expect("a plan");
        assert!(out.contains("# fit: detour to a cave at 0x1100"), "{out}");
        assert!(out.contains("# cave at 0x1100"), "{out}");
    }

    /// Bad hex, bytes that do not decode, an oversized replacement, a spec
    /// with no bytes and a target outside executable code are each refused.
    ///
    /// # Panics
    ///
    /// When any of these is accepted.
    #[test]
    fn malformed_requests_are_refused() {
        let code = &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3];
        assert!(plan(code, "0x1000/zz").is_err());
        assert!(
            plan(code, "0x1000/48") // ASM: rex prefix, no instruction
                .unwrap_err()
                .contains("does not decode")
        );
        let big = format!("0x1000/{}", "90".repeat(super::MAX_NEW + 1));
        assert!(plan(code, &big).unwrap_err().contains("at most"));
        assert!(plan(code, "0x1000").is_err());
        assert!(plan(code, "0x90000/90").unwrap_err().contains("executable"));
    }

    /// A non-x86 image is refused before any byte is read.
    ///
    /// # Panics
    ///
    /// When an arm64 image is not refused.
    #[test]
    fn a_non_x86_image_is_refused() {
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let p = Program::raw(vec![0u8; 0x100], Arch::Arm64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let err = plan_tsv(&p, &a, &Overlay::default(), "0x1000/90").expect_err("refused");
        assert!(err.contains("x86"), "{err}");
    }
}
