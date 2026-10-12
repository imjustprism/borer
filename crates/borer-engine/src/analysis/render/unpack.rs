//! Protector work: the devirtualizer's trace and the unpacker's run, report and
//! rebuilt image.

use super::*;
use crate::text::one_line;

/// Instructions the devirtualizer runs before giving up.
pub(super) const DEVIRT_BUDGET: usize = 2_000_000;

/// Most virtual instructions listed in a trace.
pub(super) const DEVIRT_TRACE_MAX: usize = 2000;

/// Recovers the virtual program a virtualized function runs.
///
/// A protector replaces a function with a bytecode interpreter: a dispatch
/// loop reads an opcode and jumps through a table to the handler for it. The
/// static map ([`vm_dispatch_tsv`]) names the handlers; this runs the
/// interpreter and records which handler fires at each step, so the output is
/// the sequence of operations the original function performed, read off the
/// machine rather than reconstructed by hand. The dispatch is the indirect
/// jump taken most, since the interpreter loops on it once per virtual
/// instruction, among those that are a real dispatch loop: a site
/// `borer://vm` finds ([`dispatch_loops`]), or one the run took to at least
/// [`VM_MIN_FETCHED`] distinct handlers, the least `borer://vm` takes for a
/// dispatch. An import thunk or a two-way branch jumps through one site to
/// one or two targets and is no machine, and a run with no such site says
/// so rather than tracing one. Each distinct handler is given a name and summarized once;
/// the trace is then that alphabet. A handler is summarized from the bytes
/// the run executed, which are the image's for a static VM and the run's
/// memory where the protector decrypted them into a section the file does
/// not back. Registers can be set in the target
/// (`0x140abc,rcx=0x...`) to supply the VM's context pointer where the entry
/// does not build it.
///
/// The run is best-effort by default, like the unpacker's: a VM interpreter
/// reads through imports and memory the OS loader fills at run time, and
/// faulting on the first such read recovers one virtual instruction and
/// stops. Installing the import stubs and reading zero from unmapped memory
/// lets the dispatch loop turn far enough to trace the virtual program. A
/// `strict` token faults on the first missing read instead. A `budget=N`
/// token raises the step cap toward a full run, up to
/// [`UNPACK_BUDGET_MAX`], for a protector whose dispatch starts only after a
/// bootstrap that decrypts for a hundred million steps or more; the default
/// covers a VM whose bytecode is present in the image. A register preset
/// that does not read or sets nothing is refused, as the unpacker refuses
/// one, rather than dropped from a run that then answers a different
/// question.
///
/// This reads a VM whose bytecode is present in the image, which covers
/// VMProtect-style and most custom virtualizers; a protector that decrypts
/// its bytecode at runtime (Themida) leaves nothing to trace statically, and
/// the run stops at the fault where it would need that bytecode.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: functions, blocks, jump tables.
/// * `o` - User names.
/// * `target` - The virtualized function's address, with optional `budget=N`
///   and registers.
///
/// # Returns
///
/// The recovered virtual program as text.
///
/// # Errors
///
/// When the target is not a function, a directive does not read, a register
/// cannot be set, or the architecture is not emulated.
pub fn devirtualize_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    target: &str,
) -> Result<String, String> {
    x86_only(p, "devirt")?;
    let (addr, parts) = spec_head(target);
    let entry = resolve(a, o, addr).ok_or_else(|| {
        if addr.is_empty() {
            unresolved(addr)
        } else {
            format!("no function {}", one_line(addr))
        }
    })?;
    let rest: Vec<&str> = parts.map(str::trim).filter(|t| !t.is_empty()).collect();
    let budget = match budget_token(rest.iter().copied()) {
        None => DEVIRT_BUDGET,
        Some(v) => parse_count(v)
            .ok_or_else(|| format!("bad budget in budget={}", one_line(v)))?
            .min(UNPACK_BUDGET_MAX),
    };
    let mut emu = Emulator::new(p, budget).ok_or_else(|| String::from("unknown architecture"))?;
    emu.install_imports();
    let strict = rest.iter().any(|p| matches!(*p, "strict" | "nobesteffort"));
    emu.set_permissive(!strict);
    for token in rest
        .iter()
        .filter(|t| !matches!(**t, "strict" | "nobesteffort"))
    {
        let (reg, value) = token.split_once('=').ok_or_else(|| {
            format!(
                "cannot read the directive {}; use strict, budget=N, or reg=value",
                one_line(token)
            )
        })?;
        let reg = reg.trim();
        if reg.eq_ignore_ascii_case("budget") {
            continue;
        }
        let v =
            parse_addr(value.trim()).ok_or_else(|| format!("bad value in {}", one_line(token)))?;
        let reg = reg.trim();
        if !emu.set_register(reg.to_lowercase().as_str(), v) {
            return Err(format!(
                "{} is not a register this can set; use rax..r15 or rsp",
                one_line(reg)
            ));
        }
    }
    let run = emu.run(entry);
    let jumps = emu.indirect_jumps();
    if jumps.is_empty() {
        return Ok(format!(
            "# {}: no dispatch ran ({} after {} steps); the bytecode may be encrypted or the VM needs its context pointer set\n",
            name_of(a, o, entry),
            run.stop,
            run.steps
        ));
    }
    let mut sites: BTreeMap<u64, (usize, BTreeSet<u64>)> = BTreeMap::new();
    for (from, to) in jumps {
        let site = sites.entry(*from).or_default();
        site.0 += 1;
        site.1.insert(*to);
    }
    let loops = dispatch_loops(p, a);
    let Some(dispatch) = sites
        .iter()
        .filter(|(from, (_, targets))| {
            targets.len() >= VM_MIN_FETCHED || loops.iter().any(|d| d.site == **from)
        })
        .max_by_key(|(_, (n, _))| *n)
        .map(|(from, _)| *from)
    else {
        let widest = sites.values().map(|(_, t)| t.len()).max().unwrap_or(0);
        let why = loops.iter().find(|d| d.entry == entry).map_or_else(
            || "a thunk or a switch is no interpreter".to_owned(),
            |d| {
                format!(
                    "the run stopped before the dispatch borer://vm finds at {:#x}",
                    d.site
                )
            },
        );
        return Ok(format!(
            "# {}: no dispatch loop ran ({} after {} steps): {} indirect jump{} from {} site{}, none a dispatch borer://vm finds and none reaching {VM_MIN_FETCHED} handlers (the most was {widest}); {why}\n",
            name_of(a, o, entry),
            run.stop,
            run.steps,
            jumps.len(),
            plural(jumps.len()),
            sites.len(),
            plural(sites.len())
        ));
    };
    let trace: Vec<u64> = jumps
        .iter()
        .filter(|(from, _)| *from == dispatch)
        .map(|(_, to)| *to)
        .collect();
    let mut order: Vec<u64> = Vec::new();
    for h in &trace {
        if !order.contains(h) {
            order.push(*h);
        }
    }
    let name_of_handler = |h: u64| {
        order
            .iter()
            .position(|x| *x == h)
            .map_or_else(|| "?".to_owned(), |i| format!("v{i}"))
    };
    let mut out = format!(
        "# {}: {} virtual instructions over {} handlers, dispatch at {dispatch:#x} ({})\n",
        name_of(a, o, entry),
        trace.len(),
        order.len(),
        run.stop
    );
    out.push_str("# handlers:\n");
    let span = usize::try_from(HANDLER_SPAN).unwrap_or(0);
    for h in &order {
        let live = emu.code_at(*h, span);
        let (n, effect) = if live.is_empty() {
            handler_effect(p, a, *h)
        } else {
            handler_effect_code(p, *h, &live)
        };
        let _ = writeln!(
            out,
            "  {:<4} {h:#x}  {n} instrs  {effect}",
            name_of_handler(*h)
        );
    }
    out.push_str("# virtual program:\n");
    let shown: Vec<String> = trace
        .iter()
        .take(DEVIRT_TRACE_MAX)
        .map(|h| name_of_handler(*h))
        .collect();
    for line in shown.chunks(20) {
        let _ = writeln!(out, "  {}", line.join(" "));
    }
    elided_line(&mut out, trace.len(), DEVIRT_TRACE_MAX, "");
    Ok(out)
}

/// Instructions the unpacking trace runs before giving up.
pub(super) const UNPACK_BUDGET: usize = 10_000_000;

/// Ceiling on a caller-supplied `budget=`, so a request cannot run unbounded.
pub(super) const UNPACK_BUDGET_MAX: usize = 200_000_000;

/// Most materialized regions listed before the rest are summarized.
pub(super) const UNPACK_REGION_MAX: usize = 32;

/// Instructions disassembled at the recovered original entry point.
pub(super) const UNPACK_OEP_PEEK: usize = 12;

/// Bytes of the largest materialized region sampled for its entropy.
pub(super) const UNPACK_ENTROPY_SAMPLE: usize = 0x10000;

/// Functions named as new to the materialized image before the rest are
/// counted.
pub(super) const UNPACK_FRESH_MAX: usize = 8;

/// Payload size past which a fault reads as a VM guard, not a stalled bootstrap.
///
/// A run that decrypted at least this much and then faulted has done the
/// unpacking and stopped at what runs the payload — a virtual machine or an
/// anti-emulation check — rather than stalled early for a missing import.
pub(super) const VM_CEILING_BYTES: u64 = 0x10_0000;

/// A parsed unpack request: where to start, how long to run, and what to
/// preset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct UnpackSpec {
    /// Where the run starts.
    pub(super) entry: u64,
    /// Most instructions the run may take.
    pub(super) budget: usize,
    /// Fault on the first transfer to an unresolved import instead of
    /// skipping it.
    pub(super) strict: bool,
    /// Register presets for the VM's context, as `(name as written,
    /// value)`, in spec order.
    pub(super) presets: Vec<(String, u64)>,
}

impl UnpackSpec {
    /// Parses `[<address>][,budget=N][,strict][,<reg>=<value>...]`.
    ///
    /// An empty address is the image's entry point. `budget=N` raises the
    /// step cap toward a full unpack, up to [`UNPACK_BUDGET_MAX`]; a budget
    /// that is not a count ([`parse_count`]) is refused rather than left at
    /// the default or read as hex, so a caller who asked for more steps
    /// does not get another run back with no sign of it. `strict` (or
    /// `nobesteffort`) faults on the first read of memory the loader would
    /// fill, which pins exactly what a simple packer's bootstrap still
    /// needs. The rest are register presets.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded image, for its entry point.
    /// * `a` - The analysis, for resolving a name.
    /// * `o` - User names.
    /// * `target` - The spec.
    ///
    /// # Returns
    ///
    /// The parsed spec.
    ///
    /// # Errors
    ///
    /// Why the spec is refused: the start does not resolve, the budget
    /// cannot be read, a directive has no `=`, or a preset's value cannot be
    /// read.
    pub(super) fn parse(
        p: &Program,
        a: &Analysis,
        o: &Overlay,
        target: &str,
    ) -> Result<Self, String> {
        let (addr, parts) = spec_head(target);
        let entry = if addr.is_empty() {
            p.entry
                .ok_or_else(|| String::from("the image has no entry point; give a start address"))?
        } else {
            resolve(a, o, addr).ok_or_else(|| format!("no start address {}", one_line(addr)))?
        };
        let pairs: Vec<&str> = parts.collect();
        let budget = match budget_token(pairs.iter().copied()) {
            None => UNPACK_BUDGET,
            Some(v) => parse_count(v)
                .ok_or_else(|| format!("bad budget in budget={}", one_line(v)))?
                .min(UNPACK_BUDGET_MAX),
        };
        let strict = pairs
            .iter()
            .any(|p| matches!(p.trim(), "strict" | "nobesteffort"));
        let mut presets: Vec<(String, u64)> = Vec::new();
        for pair in &pairs {
            let token = pair.trim();
            if token.is_empty() || matches!(token, "strict" | "nobesteffort") {
                continue;
            }
            let (key, value) = token.split_once('=').ok_or_else(|| {
                format!(
                    "cannot read the directive {}; use budget=N, strict, or reg=value",
                    one_line(token)
                )
            })?;
            let key = key.trim();
            if key.eq_ignore_ascii_case("budget") {
                continue;
            }
            let v = parse_addr(value.trim())
                .ok_or_else(|| format!("bad value in {}", one_line(token)))?;
            presets.push((key.to_owned(), v));
        }
        Ok(Self {
            entry,
            budget,
            strict,
            presets,
        })
    }
}

/// The value of the `budget=` directive among a spec's directives, if any.
///
/// # Arguments
///
/// * `directives` - The tokens after the address.
fn budget_token<'s>(mut directives: impl Iterator<Item = &'s str>) -> Option<&'s str> {
    directives.find_map(|part| {
        let (k, v) = part.split_once('=')?;
        k.trim().eq_ignore_ascii_case("budget").then(|| v.trim())
    })
}

/// Runs a packer's bootstrap and reports the code it decrypts into memory.
///
/// A protector ships the real program encrypted and rebuilds it at run time:
/// the entry stub decrypts code into memory and jumps to it. This runs that
/// stub in the emulator with each write overlaid back onto the instruction
/// stream, so decrypted code executes as itself (self-modifying code), and
/// records every region the run materializes and the first one it executes,
/// which is the original entry point. It is the dynamic step static
/// disassembly cannot take, done headless and without running the sample.
///
/// Best-effort is the default: a packer bootstrap reads through memory the
/// OS loader fills at run time (unresolved imports), and skipping those
/// transfers rather than faulting is what lets it run to its payload. It
/// matches the file-writing path ([`unpacked_image`]), so the report and the
/// dump stop the same way. A preset naming a register that sets nothing
/// stops the run, since it would otherwise read as a preset that was
/// applied and the run would answer a different question.
///
/// The run is bounded and models a subset of the instruction set, so a heavy
/// commercial packer (Themida) usually stops in its bootstrap before the
/// program is whole; the output is then the regions decrypted so far and the
/// instruction the run could not pass, which is itself a map of the packer's
/// first stage: the last instruction executed is where the bootstrap needs
/// the OS loader (a resolved import, a mapped header) the emulator lacks. A
/// run that decrypted its payload and then derailed, or faulted after
/// reaching an original entry point, has hit a VM or anti-emulation guard:
/// the emulator ran the first layer but the code past it depends on state
/// only a real process has, and the report says so and points at the tool
/// that does have it. A simple in-place decryptor unpacks fully and the
/// entry-point disassembly is the real code.
///
/// The largest region's entropy is the evidence the unpacking worked:
/// decrypted code reads far below the packed 7.9+, so the reader can see
/// the payload is real content even when the run never reached its entry,
/// and high entropy after the write means a further layer the bootstrap
/// decrypts later. Analyzing the image the run built is the point: a packed
/// program's own sections hold a decryptor and a blob, so discovery over
/// them finds a handful of functions, and discovery over what the decryptor
/// produced finds the program.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `target` - Where to start, the entry by default, with optional `reg=val`
///   presets and a `budget=N` step cap for pushing toward a full unpack.
///
/// # Returns
///
/// The unpacking trace as text.
///
/// # Errors
///
/// When the spec is refused, as [`UnpackSpec::parse`] says why, a preset
/// sets nothing, or the architecture is not emulated.
pub fn unpack_tsv(p: &Program, a: &Analysis, o: &Overlay, target: &str) -> Result<String, String> {
    x86_only(p, "unpack")?;
    let spec = UnpackSpec::parse(p, a, o, target)?;
    let mut emu =
        Emulator::new(p, spec.budget).ok_or_else(|| String::from("unknown architecture"))?;
    emu.install_imports();
    emu.set_permissive(!spec.strict);
    for (name, v) in &spec.presets {
        if !emu.set_register(name.to_lowercase().as_str(), *v) {
            return Err(format!(
                "{} is not a register this can set; use rax..r15 or rsp",
                one_line(name)
            ));
        }
    }
    let entry = spec.entry;
    let run = emu.run(entry);
    let regions = emu.materialized();
    let total: u64 = regions.iter().map(|(_, n)| *n).sum();
    let mut out = format!(
        "# {}: emulated unpacking from {entry:#x}\n",
        name_of(a, o, entry)
    );
    let _ = writeln!(out, "# stopped: {} after {} steps", run.stop, run.steps);
    if emu.skipped() > 0 {
        let _ = writeln!(
            out,
            "# best-effort: {} transfer(s) to unresolved imports skipped",
            emu.skipped()
        );
    }
    if matches!(
        run.stop,
        Stop::Fault(_) | Stop::Unmodeled(_) | Stop::Derailed(_)
    ) && let Some(bits) = p.arch.bitness()
    {
        let at = emu.last_ip();
        let code = emu.code_at(at, 16);
        if let Some(line) = disasm::disassemble(&code, at, bits, 1).first() {
            let _ = writeln!(out, "# blocked at {at:#x}: {}", line.text);
        }
    }
    let derailed = matches!(run.stop, Stop::Derailed(_)) && total > 0;
    let faulted_after_payload =
        matches!(run.stop, Stop::Fault(_)) && (emu.oep().is_some() || total >= VM_CEILING_BYTES);
    if derailed || faulted_after_payload {
        out.push_str(
            "# the run decrypted its payload and then left ordinary code for a VM or \
             anti-emulation guard; static emulation stops at this layer.\n",
        );
    }
    let calls = emu.api_calls();
    if !calls.is_empty() {
        let mut counts: Vec<(String, usize)> = Vec::new();
        for name in calls {
            match counts.iter_mut().find(|(n, _)| n == name) {
                Some((_, c)) => *c += 1,
                None => counts.push((name.clone(), 1)),
            }
        }
        let shown: Vec<String> = counts
            .iter()
            .map(|(n, c)| {
                if *c > 1 {
                    format!("{n} x{c}")
                } else {
                    n.clone()
                }
            })
            .collect();
        let _ = writeln!(out, "# APIs the bootstrap called: {}", shown.join(", "));
    }
    if regions.is_empty() {
        out.push_str(
            "# nothing unpacked: the run wrote no code outside the stack before it stopped\n",
        );
        return Ok(out);
    }
    let _ = writeln!(
        out,
        "# materialized: {} region(s), {total} bytes written into memory",
        regions.len()
    );
    let oep = emu.oep();
    for (start, len) in regions.iter().take(UNPACK_REGION_MAX) {
        let end = start.wrapping_add(*len);
        let tag = if oep == Some(*start) {
            "  <- entry point executed here"
        } else if oep.is_some_and(|x| x >= *start && x < end) {
            "  (executed)"
        } else {
            ""
        };
        let _ = writeln!(out, "  {start:#x}..{end:#x}  {len} bytes{tag}");
    }
    elided_line(&mut out, regions.len(), UNPACK_REGION_MAX, " regions");
    if let Some((start, len)) = regions.iter().max_by_key(|(_, n)| *n).copied() {
        let sample = emu.code_at(
            start,
            crate::num::saturating_usize(len).min(UNPACK_ENTROPY_SAMPLE),
        );
        if !sample.is_empty() {
            let e = crate::entropy::shannon(&sample);
            let head: Vec<String> = sample.iter().take(16).map(|b| format!("{b:02x}")).collect();
            let verdict = if e >= 7.0 {
                " (still packed: a further layer)"
            } else if e <= 6.7 {
                " (reads as decrypted code or data)"
            } else {
                ""
            };
            let _ = writeln!(
                out,
                "# largest region {start:#x}: entropy {e:.2}{verdict}, first bytes {}",
                head.join(" ")
            );
        }
    }
    if let Some(oep) = oep {
        let _ = writeln!(
            out,
            "# original entry point (first decrypted code executed): {oep:#x}"
        );
        let code = emu.code_at(oep, 64);
        if let Some(bits) = p.arch.bitness() {
            for line in disasm::disassemble(&code, oep, bits, UNPACK_OEP_PEEK) {
                let _ = writeln!(out, "  {:<#13x} {}", line.va, line.text);
            }
        }
    } else {
        out.push_str(
            "# no written code was executed: the writes were data, or the run ended before reaching them\n",
        );
    }
    if let Some(rebuilt) = rebuild(p, &emu, &regions) {
        let after = Analysis::compute(&rebuilt);
        let _ = writeln!(
            out,
            "# re-analyzed the materialized image: {} functions against {} before",
            after.functions.len(),
            a.functions.len()
        );
        let fresh: Vec<u64> = after
            .functions
            .iter()
            .map(|f| f.entry)
            .filter(|e| a.function(*e).is_none())
            .collect();
        if !fresh.is_empty() {
            let shown: Vec<String> = fresh
                .iter()
                .take(UNPACK_FRESH_MAX)
                .map(|e| format!("{e:#x}"))
                .collect();
            let _ = writeln!(
                out,
                "# {} function(s) only the materialized image has: {}{}",
                fresh.len(),
                shown.join(", "),
                plus_more(fresh.len(), UNPACK_FRESH_MAX)
            );
        }
    }
    Ok(out)
}

/// Runs a program's unpacking and returns the image it materialized.
///
/// The bytes of the rebuilt image, for writing out so the payload can be
/// loaded as a file by borer or by anything else. A tool reads a file, and
/// an unpacked program that exists only inside one emulator run is a report
/// rather than a program.
///
/// # Arguments
///
/// * `p` - The packed image.
/// * `entry` - Where to start the run, usually the image's entry point.
/// * `budget` - Step cap for the run, as [`unpack_start`] reads it; held to
///   1..=[`UNPACK_BUDGET_MAX`]. A packer that decrypts megabytes needs a
///   higher cap than the default to fill its sections.
///
/// # Returns
///
/// The rebuilt bytes, the original entry point the run reached, and whether the
/// run was truncated by the step budget (so the image may be partial and a
/// larger budget would fill more); or `None` when the run materialized nothing
/// that lands inside the file.
#[must_use]
pub fn unpacked_image(
    p: &Program,
    entry: u64,
    budget: usize,
) -> Option<(Vec<u8>, Option<u64>, bool)> {
    let budget = budget.clamp(1, UNPACK_BUDGET_MAX);
    let mut emu = Emulator::new(p, budget)?;
    emu.install_imports();
    emu.set_permissive(true);
    let run = emu.run(entry);
    let truncated = matches!(run.stop, Stop::Budget | Stop::MemoryFull(_));
    let regions = emu.materialized();
    let rebuilt = rebuild(p, &emu, &regions)?;
    Some((rebuilt.bytes, emu.oep(), truncated))
}

/// Reads an unpack spec for the file-writing path: where the run starts
/// and its step cap.
///
/// The spec is read by the grammar [`unpack_tsv`] reads, so `unpack <file>
/// <addr>,budget=N <out>` starts where the report starts and fills as much,
/// and a directive the report refuses is refused here rather than dropped.
/// [`unpacked_image`] runs best-effort with no presets, so a spec asking
/// for `strict` or a register is refused too: the image written would not
/// be the run asked for.
///
/// # Arguments
///
/// * `p` - The loaded image, for its entry point.
/// * `a` - The analysis, for resolving a name.
/// * `o` - User names.
/// * `spec` - The unpack argument, address first.
///
/// # Returns
///
/// The start and the step cap.
///
/// # Errors
///
/// When the spec is refused, as [`UnpackSpec::parse`] says why, or it asks
/// for `strict` or a preset.
pub fn unpack_start(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    spec: &str,
) -> Result<(u64, usize), String> {
    x86_only(p, "unpack")?;
    let spec = UnpackSpec::parse(p, a, o, spec)?;
    if spec.strict || !spec.presets.is_empty() {
        return Err(String::from(
            "writing the image runs best-effort with no register presets; drop strict and reg=value, or leave out the output file for the report",
        ));
    }
    Ok((spec.entry, spec.budget))
}

/// The original program over the bytes a run materialized.
///
/// # Arguments
///
/// * `p` - The original image, whose headers, symbols and the rest are kept.
/// * `bytes` - The rebuilt bytes.
/// * `oep` - The original entry point the run reached; the original's entry
///   stays when there is none.
/// * `sections` - The section table the rebuilt bytes follow.
fn materialized(p: &Program, bytes: Vec<u8>, oep: Option<u64>, sections: Vec<Section>) -> Program {
    Program {
        path: p.path.clone(),
        bytes,
        format: p.format,
        arch: p.arch,
        is_64: p.is_64,
        entry: oep.or(p.entry),
        image_base: p.image_base,
        sections,
        symbols: p.symbols.clone(),
        function_ranges: p.function_ranges.clone(),
        headers: p.headers.clone(),
        debug_functions: p.debug_functions.clone(),
        debug_types: p.debug_types.clone(),
        pdb: p.pdb,
        pdb_record: p.pdb_record.clone(),
        pdb_source: p.pdb_source.clone(),
        flat_fallback: p.flat_fallback,
    }
}

/// Builds a program whose bytes are what the run put in memory.
///
/// Unpacking ends with an image that exists only in the emulator, and every
/// tool reads a file. Writing the materialized regions over a copy of the
/// original's bytes gives an image the rest of the engine can analyze, which
/// is what turns a list of written regions into the program the packer was
/// hiding.
///
/// A PE is rebuilt in the layout the loader maps it in ([`rebuild_pe`]), so
/// a section the file backs with no bytes (a protector's `.themida`, where
/// the decrypted payload lands) can hold what the run wrote. Other formats
/// keep the in-place copy, which is exact where the file already has the
/// room: a region the loader would map but the file does not hold cannot be
/// written back without inventing a section. The section table and the
/// headers are the original's: a packed program's sections already cover
/// the addresses its decryptor writes into, since that is where it intends
/// the payload to run. The entry point becomes the one the run reached
/// first, which is the original entry the packer hid.
///
/// # Arguments
///
/// * `p` - The original image.
/// * `emu` - The finished run, holding the bytes it wrote.
/// * `regions` - The materialized regions, as `(start, length)`.
///
/// # Returns
///
/// The rebuilt program, or `None` when nothing landed inside the file.
pub(super) fn rebuild(p: &Program, emu: &Emulator<'_>, regions: &[(u64, u64)]) -> Option<Program> {
    /// Most bytes copied out of the run, so one program cannot fill memory.
    const COPY_MAX: u64 = 64 << 20;
    if regions.is_empty() {
        return None;
    }
    if p.format == BinaryFormat::Pe {
        return rebuild_pe(p, emu, regions, COPY_MAX);
    }
    let mut bytes = p.bytes.clone();
    let mut written = 0u64;
    'regions: for (start, len) in regions {
        for k in 0..*len {
            if written >= COPY_MAX {
                break 'regions;
            }
            let va = start.wrapping_add(k);
            let Some(byte) = emu.peek(va) else {
                continue;
            };
            let Some(off) = p.section_at(va).and_then(|s| {
                usize::try_from(s.file_off + (va - s.va))
                    .ok()
                    .filter(|o| *o < bytes.len())
            }) else {
                continue;
            };
            if let Some(slot) = bytes.get_mut(off) {
                *slot = byte;
                written += 1;
            }
        }
    }
    (written > 0).then(|| materialized(p, bytes, emu.oep(), p.sections.clone()))
}

/// Rebuilds a PE in memory layout, so an unpacked payload lands in the file.
///
/// A packer decrypts into sections the file barely backs: `.themida` has a
/// megabytes-wide virtual size and zero raw bytes, so writing the payload back
/// at the original file offsets drops it on the floor. Laying the image out the
/// way the loader maps it — file offset equal to virtual address, each
/// section's raw data its mapped data — gives every written byte a home and
/// still parses as a PE, the same shape the live dumper writes. The headers
/// are the file's leading bytes, up to the first section's address; each
/// section's original file bytes go at its address, so headers, imports and
/// any section the run never touched are still there to read; and what the
/// run decrypted into memory, the payload the packer hid, is overlaid on
/// top. A zero or wild image size is a header the packer mangled past use.
/// The entry becomes the original entry point the run reached, when it
/// reached one.
///
/// # Arguments
///
/// * `p` - The packed image.
/// * `emu` - The finished run, holding the bytes it wrote.
/// * `regions` - The materialized regions, as `(start, length)`.
/// * `copy_max` - Ceiling on bytes copied out of the run.
///
/// # Returns
///
/// The rebuilt program, whose sections' file extent is their mapped extent,
/// or `None` when the layout is implausible or the run wrote nothing into
/// the image.
pub(super) fn rebuild_pe(
    p: &Program,
    emu: &Emulator<'_>,
    regions: &[(u64, u64)],
    copy_max: u64,
) -> Option<Program> {
    let base = p.image_base;
    let image_end = p
        .sections
        .iter()
        .map(|s| s.va + s.vsize.max(s.file_size))
        .max()?;
    let image_size = usize::try_from(image_end.checked_sub(base)?).ok()?;
    if image_size == 0 || image_size > 0x8000_0000 {
        return None;
    }
    let mut buf = vec![0u8; image_size];

    let first_va = p.sections.iter().map(|s| s.va).min()?;
    let headers_len = usize::try_from(first_va.checked_sub(base)?)
        .ok()?
        .min(p.bytes.len())
        .min(image_size);
    buf[..headers_len].copy_from_slice(&p.bytes[..headers_len]);

    for s in &p.sections {
        let Ok(rva) = usize::try_from(s.va.wrapping_sub(base)) else {
            continue;
        };
        if rva >= image_size {
            continue;
        }
        if let Some(src) = p.section_bytes(s) {
            let n = src.len().min(image_size - rva);
            buf[rva..rva + n].copy_from_slice(&src[..n]);
        }
    }

    let mut written = 0u64;
    'regions: for (start, len) in regions {
        for k in 0..*len {
            if written >= copy_max {
                break 'regions;
            }
            let va = start.wrapping_add(k);
            let Some(byte) = emu.peek(va) else {
                continue;
            };
            let Ok(off) = usize::try_from(va.wrapping_sub(base)) else {
                continue;
            };
            if let Some(slot) = buf.get_mut(off) {
                *slot = byte;
                written += 1;
            }
        }
    }
    if written == 0 {
        return None;
    }

    retarget_pe_to_memory_layout(&mut buf, base, emu.oep());

    let sections = p
        .sections
        .iter()
        .map(|s| Section {
            file_off: s.va.wrapping_sub(base),
            file_size: s.vsize.max(s.file_size),
            ..s.clone()
        })
        .collect();
    Some(materialized(p, buf, emu.oep(), sections))
}

/// Rewrites a PE's section table to memory layout and points its entry at `oep`.
///
/// After the bytes are laid out by address, each section's raw data is its
/// mapped data: `SizeOfRawData` becomes `VirtualSize` and `PointerToRawData`
/// becomes `VirtualAddress`, the transform the live dumper applies so the
/// written file loads and parses. When the run reached an original entry point,
/// `AddressOfEntryPoint` is set to it so the image is analyzed from the real
/// start rather than the packer's stub. Every field is bounds-checked; a header
/// too mangled to walk is left as it is.
///
/// # Arguments
///
/// * `buf` - The address-laid-out image, modified in place.
/// * `base` - The image's preferred load base.
/// * `oep` - The original entry point the run reached, if any.
pub(super) fn retarget_pe_to_memory_layout(buf: &mut [u8], base: u64, oep: Option<u64>) {
    let read_u32 = |b: &[u8], o: usize| {
        b.get(o..o + 4)
            .and_then(|s| s.try_into().ok())
            .map(u32::from_le_bytes)
    };
    let read_u16 = |b: &[u8], o: usize| {
        b.get(o..o + 2)
            .and_then(|s| s.try_into().ok())
            .map(u16::from_le_bytes)
    };
    let Some(pe) = read_u32(buf, 0x3c).and_then(|v| usize::try_from(v).ok()) else {
        return;
    };
    if buf.get(pe..pe + 4) != Some(b"PE\0\0") {
        return;
    }
    let Some(n_sections) = read_u16(buf, pe + 6).map(usize::from) else {
        return;
    };
    let Some(opt) = read_u16(buf, pe + 0x14).map(usize::from) else {
        return;
    };
    if let Some(oep) = oep
        && let Ok(rva) = u32::try_from(oep.wrapping_sub(base))
        && let Some(slot) = buf.get_mut(pe + 0x28..pe + 0x2c)
    {
        slot.copy_from_slice(&rva.to_le_bytes());
    }
    let sec_table = pe + 0x18 + opt;
    for i in 0..n_sections {
        let sh = sec_table + i * 40;
        let (Some(vsize), Some(vaddr)) = (read_u32(buf, sh + 8), read_u32(buf, sh + 12)) else {
            break;
        };
        // SPEC: IMAGE_SECTION_HEADER.SizeOfRawData at +0x10 takes VirtualSize.
        if let Some(slot) = buf.get_mut(sh + 0x10..sh + 0x14) {
            slot.copy_from_slice(&vsize.to_le_bytes());
        }
        // SPEC: IMAGE_SECTION_HEADER.PointerToRawData at +0x14 takes VirtualAddress.
        if let Some(slot) = buf.get_mut(sh + 0x14..sh + 0x18) {
            slot.copy_from_slice(&vaddr.to_le_bytes());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{UNPACK_BUDGET, UnpackSpec, devirtualize_tsv, unpack_start};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program, Section};

    /// An unpack spec refuses a budget that is not a count, a directive
    /// with no value and a preset that does not read, naming each; the
    /// file path refuses what it would not honor.
    ///
    /// # Panics
    ///
    /// When a malformed spec parses, or a refusal does not name its token.
    #[test]
    fn an_unpack_spec_refuses_what_it_cannot_read() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        for (spec, token) in [
            ("0x1000,budget=abc", "budget=abc"),
            ("0x1000,foo", "directive foo"),
            ("0x1000,rcx=zz", "rcx=zz"),
            ("nowhere", "no start address nowhere"),
        ] {
            let err = UnpackSpec::parse(&p, &a, &o, spec).unwrap_err();
            assert!(err.contains(token), "{spec}: {err}");
        }
        assert_eq!(
            UnpackSpec::parse(&p, &a, &o, "0x1000,budget=0x100").map(|s| s.budget),
            Ok(0x100)
        );
        assert_eq!(unpack_start(&p, &a, &o, ""), Ok((0x1000, UNPACK_BUDGET)));
        assert!(unpack_start(&p, &a, &o, "0x1000,strict").is_err());
    }

    /// The devirtualizer refuses a directive it cannot read and a register
    /// it cannot set, where it dropped both and ran anyway.
    ///
    /// A budget that is not a count is refused the way the unpacker refuses
    /// one, and a budgeted run parses.
    ///
    /// # Panics
    ///
    /// When a malformed directive runs.
    #[test]
    fn devirtualizing_refuses_a_preset_it_cannot_apply() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let err = devirtualize_tsv(&p, &a, &o, "0x1000,foo").unwrap_err();
        assert!(err.contains("directive foo"), "{err}");
        let err = devirtualize_tsv(&p, &a, &o, "0x1000,eaxx=1").unwrap_err();
        assert!(err.starts_with("eaxx is not a register"), "{err}");
        assert_eq!(
            devirtualize_tsv(&p, &a, &o, "nowhere").unwrap_err(),
            "no function nowhere"
        );
        assert!(devirtualize_tsv(&p, &a, &o, "0x1000,strict").is_ok());
        let err = devirtualize_tsv(&p, &a, &o, "0x1000,budget=abc").unwrap_err();
        assert!(err.contains("bad budget in budget=abc"), "{err}");
        assert!(devirtualize_tsv(&p, &a, &o, "0x1000,budget=0x100").is_ok());
    }

    /// A handler the image cannot read but the run decrypted is summarized
    /// from the run's memory, where it read `unreadable`.
    ///
    /// The program writes three two-byte handlers (`jmp rdi`, back to the
    /// dispatch) into a section the file does not back, then dispatches to
    /// each in turn, so every handler runs in memory the emulator
    /// materialized; their effect must come from those bytes. It wrote one
    /// handler that jumped to itself, which a dispatch needs three of.
    ///
    /// # Panics
    ///
    /// When the dispatch is not found or the handler reads unreadable.
    #[test]
    fn a_handler_decrypted_by_the_run_is_summarized_from_its_memory() {
        /// Writes the handlers, then dispatches through `rax` to each.
        const CODE: [u8; 59] = [
            0x48, 0xbb, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ASM: mov rbx,0x2000
            0x66, 0xc7, 0x03, 0xff, 0xe7, // ASM: mov word ptr [rbx],0xe7ff
            0x66, 0xc7, 0x43, 0x10, 0xff, 0xe7, // ASM: mov word ptr [rbx+0x10],0xe7ff
            0x66, 0xc7, 0x43, 0x20, 0xff, 0xe7, // ASM: mov word ptr [rbx+0x20],0xe7ff
            0x48, 0xbf, 0x27, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ASM: mov rdi,0x1027
            0x31, 0xc9, // ASM: xor ecx,ecx
            0x83, 0xf9, 0x03, // ASM: cmp ecx,3
            0x73, 0x0e, // ASM: jae 0x103a
            0x48, 0x89, 0xc8, // ASM: mov rax,rcx
            0x48, 0xc1, 0xe0, 0x04, // ASM: shl rax,4
            0xff, 0xc1, // ASM: inc ecx
            0x48, 0x01, 0xd8, // ASM: add rax,rbx
            0xff, 0xe0, // ASM: jmp rax
            0xc3, // ASM: ret
        ];
        let text = Section::mapped(".text", 0x1000, 0, CODE.len() as u64, false, true);
        let empty = Section {
            name: ".handler".to_owned(),
            va: 0x2000,
            vsize: 0x1000,
            file_off: 0x2000,
            file_size: 0,
            readable: true,
            writable: true,
            executable: true,
        };
        let p = Program::raw(
            CODE.to_vec(),
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text, empty],
        );
        let a = Analysis::compute(&p);
        let out = devirtualize_tsv(&p, &a, &Overlay::default(), "0x1000,budget=1000").unwrap();
        assert!(
            out.contains("3 virtual instructions over 3 handlers, dispatch at 0x1038"),
            "{out}"
        );
        assert!(!out.contains("unreadable"), "{out}");
        assert!(!out.contains(" 0 instrs"), "{out}");
    }

    /// A lone indirect jump is no dispatch loop and is not traced as one.
    ///
    /// It reaches one target, as an import thunk does; any indirect jump was
    /// taken for the dispatch, so a `jmp [memset]` thunk read as a
    /// one-handler machine.
    ///
    /// # Panics
    ///
    /// When the lone jump is traced as a dispatch.
    #[test]
    fn a_lone_indirect_jump_is_not_a_dispatch() {
        let mut code = vec![0x48, 0xb8, 0x10, 0x10, 0, 0, 0, 0, 0, 0]; // ASM: mov rax,0x1010
        code.extend([0xff, 0xe0]); // ASM: jmp rax
        code.resize(0x10, 0xcc);
        code.push(0xc3); // ASM: ret
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let out = devirtualize_tsv(&p, &a, &Overlay::default(), "0x1000").unwrap();
        assert!(out.contains(": no dispatch loop ran ("), "{out}");
        assert!(
            out.contains(
                "1 indirect jump from 1 site, none a dispatch borer://vm finds and none reaching 3 handlers (the most was 1)"
            ),
            "{out}"
        );
        assert!(!out.contains("virtual instructions"), "{out}");
    }
}
