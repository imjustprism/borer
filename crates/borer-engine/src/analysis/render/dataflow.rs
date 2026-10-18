//! Value passes: taint, proposed layouts, why an address is what it is, and the
//! register conventions they share.

use super::*;
use crate::analysis::decompile::lift;

/// Where a value pass starts and what it follows: `<address>[,<register>]`.
#[derive(Debug, Clone)]
pub(super) struct ValueSpec {
    /// The instruction the pass starts from.
    pub(super) start: u64,
    /// Entry of the function containing `start`.
    pub(super) entry: u64,
    /// The register the value is in at `start`, lowercase as the caller
    /// spelled it.
    pub(super) wanted: String,
    /// That register in the target's width.
    pub(super) seed: Register,
    /// Decoder bitness of the program.
    pub(super) bitness: u32,
}

impl ValueSpec {
    /// Parses the spec.
    ///
    /// A register the spec names is checked before the function is looked
    /// up, so a misspelled one is refused as such wherever it points.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded image, whose conventions pick the default.
    /// * `a` - The analysis, for resolving a name and finding the function.
    /// * `o` - User names.
    /// * `spec` - `<address>` or `<address>,<register>`, where the register
    ///   may be `aN`, the decompiler's name for the argument the function's
    ///   convention passes in that register.
    /// * `bitness` - Decoder bitness of the program; `None` refuses the pass.
    /// * `follow` - The register followed when the spec names none.
    ///
    /// # Returns
    ///
    /// The parsed spec.
    ///
    /// # Errors
    ///
    /// Why the pass is refused: the address does not resolve, the
    /// architecture is unknown, a part follows the register (it was dropped
    /// unread), the register is not one the target has, or no function
    /// contains the address.
    pub(super) fn parse(
        p: &Program,
        a: &Analysis,
        o: &Overlay,
        spec: &str,
        bitness: Option<u32>,
        follow: Follow,
    ) -> Result<Self, String> {
        let (where_, mut rest) = spec_head(spec);
        let start = locate(a, o, where_).ok_or_else(|| unresolved(where_))?;
        let bitness = bitness.ok_or_else(|| String::from("unknown architecture"))?;
        let names = RegisterNames::for_bitness(bitness);
        let named = rest.next().map(|r| r.trim().to_lowercase());
        if let Some(extra) = rest.next() {
            return Err(format!(
                "the spec is <address>[,<register>]; {} is one part too many",
                crate::text::quoted(extra.trim())
            ));
        }
        let register = |wanted: &str| {
            iced_register(wanted, bitness).ok_or_else(|| {
                format!(
                    "{} is not a general register; use {} or a1, a2, ...",
                    crate::text::one_line(wanted),
                    names.range
                )
            })
        };
        let argument = named
            .as_deref()
            .and_then(|n| n.strip_prefix('a')?.parse::<usize>().ok())
            .filter(|&k| k >= 1);
        let given = match argument {
            Some(_) => None,
            None => named.as_deref().map(register).transpose()?,
        };
        let entry = a
            .function_at(start)
            .ok_or_else(|| format!("no function contains {start:#x}"))?
            .entry;
        let (wanted, seed) = match (named.zip(given), argument) {
            (Some(named), _) => named,
            (None, Some(k)) => {
                let regs = if bitness == 32 {
                    &[][..]
                } else {
                    argument_registers(p, entry, bitness)
                };
                let seed = regs.get(k - 1).map(|r| canonical(*r, bitness)).ok_or_else(|| {
                    format!(
                        "a{k} does not arrive in a register under this function's convention ({} register arguments); name the register it is in",
                        regs.len()
                    )
                })?;
                (format!("{seed:?}").to_lowercase(), seed)
            }
            (None, None) => {
                let seed = match follow {
                    Follow::Result => register(names.result)?,
                    Follow::FirstArgument => argument_registers(p, entry, bitness)
                        .first()
                        .map_or_else(|| register(names.result), |r| Ok(canonical(*r, bitness)))?,
                };
                (format!("{seed:?}").to_lowercase(), seed)
            }
        };
        Ok(Self {
            start,
            entry,
            wanted,
            seed,
            bitness,
        })
    }
}

/// The register a value pass follows when its spec names none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Follow {
    /// Where a call leaves its result: what `taint` follows.
    Result,
    /// Where the function's first argument arrives by its own convention:
    /// the pointer `layout` follows.
    FirstArgument,
}

/// Follows a value forward through a function and reports where it lands.
///
/// The question an agent asks about a recovered key, a decrypted buffer or a
/// call's result is where it goes: is it hashed, is it compared, does it
/// reach the network. Reading the disassembly answers that eventually; this
/// answers it directly, by carrying a taint from one register through the
/// moves and arithmetic that spread it and reporting the two things that
/// matter, the calls a tainted value is passed to and the memory it is
/// stored into.
///
/// A call is decided first and on the convention, not on the operands: the
/// argument registers are not operands of a `call`, so nothing about the
/// instruction itself says the value is being passed, and this is the
/// answer the whole pass exists for. The same convention lets the callee
/// destroy the volatile registers, so whatever they held is gone, and the
/// callee's own result is not the tainted value unless it passed it back,
/// which this cannot know. A stack probe is the exception: it reads a size,
/// not an argument, so it neither consumes the value nor clears anything.
///
/// Registers are followed. A store to memory is reported as a place the
/// value went, not followed further, because tracking it would need the
/// frame analysis the decompiler keeps to itself; saying so is better than a
/// silent half-answer. A register written from something untainted is
/// cleared, which is what keeps a long function from reporting everything.
///
/// The pass runs over the function's instructions in address order, twice,
/// so a value that a loop carries backwards to an earlier instruction is
/// still caught.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the code bytes.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - `<address>` or `<address>,<register>`; the register defaults to
///   `rax`, which is where a call leaves its result.
///
/// # Returns
///
/// One line per instruction that moved the value, the calls and stores it
/// reached, and the registers holding it at the end.
///
/// # Errors
///
/// When the spec is refused, as [`ValueSpec::parse`] says why.
pub fn taint_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    /// Lines reported before the rest are counted instead.
    const LINES_MAX: usize = 80;
    /// Passes over the function, so a loop's back edge is followed once.
    const PASSES: usize = 2;
    x86_reading(p, "taint")?;
    let ValueSpec {
        start,
        entry,
        wanted,
        seed,
        bitness,
    } = ValueSpec::parse(p, a, o, spec, p.arch.bitness(), Follow::Result)?;
    let instrs = function_instructions(p, a, entry);
    let (arguments, volatile) = (
        argument_registers(p, entry, bitness),
        volatile_registers(p, entry, bitness),
    );

    let mut tainted: BTreeSet<Register> = BTreeSet::new();
    tainted.insert(seed);
    let mut lines: Vec<String> = Vec::new();
    let mut calls: Vec<String> = Vec::new();
    let mut stores: Vec<String> = Vec::new();
    let mut noted_calls: BTreeSet<String> = BTreeSet::new();
    let mut noted_stores: BTreeSet<String> = BTreeSet::new();
    let mut factory = InstructionInfoFactory::new();
    for pass in 0..PASSES {
        for i in &instrs {
            if pass == 0 && i.ip() <= start {
                continue;
            }
            let info = factory.info(i);
            let mut reads: Vec<Register> = Vec::new();
            let mut writes: Vec<Register> = Vec::new();
            for ur in info.used_registers() {
                let r = canonical(ur.register(), bitness);
                match ur.access() {
                    OpAccess::Read | OpAccess::CondRead => reads.push(r),
                    OpAccess::ReadWrite | OpAccess::ReadCondWrite => {
                        reads.push(r);
                        writes.push(r);
                    }
                    OpAccess::Write | OpAccess::CondWrite => writes.push(r),
                    OpAccess::None | OpAccess::NoMemAccess => {}
                }
            }
            let carried: Vec<Register> = reads
                .iter()
                .copied()
                .filter(|r| tainted.contains(r))
                .collect();
            let text = || {
                disasm::disassemble(
                    p.read_va_upto(i.ip(), i.len()).unwrap_or(&[]),
                    i.ip(),
                    bitness,
                    1,
                )
                .first()
                .map_or_else(|| format!("{i}"), |l| l.text.clone())
            };
            if matches!(
                i.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                let preserves = preserves_registers(a, o, i);
                let passed: Vec<String> = arguments
                    .iter()
                    .enumerate()
                    .filter(|(_, r)| tainted.contains(&canonical(**r, bitness)))
                    .map(|(k, _)| format!("argument {}", k + 1))
                    .collect();
                if !passed.is_empty() && !preserves {
                    let callee = callee_name(a, o, i);
                    let note = format!(
                        "{:<#12x} {callee} takes it as {}",
                        i.ip(),
                        passed.join(" and ")
                    );
                    if noted_calls.insert(note.clone()) {
                        calls.push(note);
                    }
                }
                if !preserves {
                    for r in volatile {
                        tainted.remove(&canonical(*r, bitness));
                    }
                }
                continue;
            }
            if carried.is_empty() {
                for w in writes {
                    tainted.remove(&w);
                }
                continue;
            }
            if info.used_memory().iter().any(|m| {
                matches!(
                    m.access(),
                    OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite
                )
            }) {
                let note = format!("{:<#12x} stored by {}", i.ip(), text());
                if noted_stores.insert(note.clone()) {
                    stores.push(note);
                }
            }
            let spread: Vec<Register> = writes
                .iter()
                .copied()
                .filter(|w| !tainted.contains(w))
                .collect();
            for w in &spread {
                tainted.insert(*w);
            }
            if pass == 0 && !spread.is_empty() && lines.len() < LINES_MAX {
                let names: Vec<String> = spread
                    .iter()
                    .map(|r| format!("{r:?}").to_lowercase())
                    .collect();
                lines.push(format!(
                    "{:<#12x} {:<34} now in {}",
                    i.ip(),
                    text(),
                    names.join(", ")
                ));
            }
        }
    }
    let mut out = format!(
        "# {wanted} from {start:#x} forward through {}\n",
        short_name(a, o, entry)
    );
    if lines.is_empty() && calls.is_empty() && stores.is_empty() {
        out.push_str("# the value is not read again in this function\n");
        return Ok(out);
    }
    if !lines.is_empty() {
        out.push_str("# carried by\n");
        for l in &lines {
            let _ = writeln!(out, "{l}");
        }
    }
    if !calls.is_empty() {
        out.push_str("# reaches\n");
        for l in calls.iter().take(LINES_MAX) {
            let _ = writeln!(out, "{l}");
        }
    }
    if !stores.is_empty() {
        out.push_str("# stored into memory (not followed further)\n");
        for l in stores.iter().take(LINES_MAX) {
            let _ = writeln!(out, "{l}");
        }
    }
    let held: Vec<String> = tainted
        .iter()
        .map(|r| format!("{r:?}").to_lowercase())
        .collect();
    if !held.is_empty() {
        let _ = writeln!(out, "# still held in {}", held.join(", "));
    }
    Ok(out)
}

/// Proposes a structure from what a function does through one pointer.
///
/// A function handed a pointer reads and writes fields at fixed offsets from
/// it, and those offsets are the structure's layout. Recovering it needs no
/// type information and no debug data, only the arithmetic the code already
/// does: a `lea` that moves 0x18 into another register is a field at 0x18,
/// and the width of the access that follows is the field's size.
///
/// Offsets are tracked, not just taint: a register that took the address of
/// a field carries that field's offset, so an access through it lands at the
/// right place instead of at the base. That is the difference between a
/// layout and a list of guesses. An access through a register that holds an
/// offset is a field; a `lea` computes an address, so it moves the offset
/// along; a plain move carries it; and anything else written stops holding
/// one, which is what keeps unrelated pointers out. A field whose address is
/// handed to a function is described by what that function is, which is
/// worth more than a size.
///
/// A field's size is the width of the access, which is what the code says
/// rather than what the source declared: two adjacent four-byte reads of an
/// eight-byte field read as two fields, and the output says how often each
/// was seen so a reader can judge. Several widths at one offset is what the
/// code did, so all are reported: a byte write into an eight-byte field is a
/// flag in it. An instruction counts once however many passes read it, an
/// offset below the pointer (an embedded member's container) reads `-0x8`,
/// and the header counts every row, a field only handed to a call included.
///
/// # Arguments
///
/// * `p` - The loaded image, read for the code bytes.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - `<address>` or `<address>,<register>`; the register defaults to
///   the first argument by the function's own convention ([`Follow`]):
///   `rcx` on a PE, `rdi` on an ELF or Mach-O, `rax` for a Go function,
///   `ecx` in 32-bit code.
///
/// # Returns
///
/// One row per offset with its size, how it is accessed, and how many
/// instructions touched it.
///
/// # Errors
///
/// When the spec is refused, as [`ValueSpec::parse`] says why, or the
/// function's code does not read.
pub fn layout_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    /// Fields reported before the rest are counted.
    const FIELDS_MAX: usize = 64;
    let Accesses {
        spec: ValueSpec { entry, wanted, .. },
        fields,
        taken,
    } = accesses(p, a, o, spec)?;
    let mut out = format!(
        "# structure through {wanted} of {}, from {} access site(s)\n",
        short_name(a, o, entry),
        fields.values().map(|f| f.sites.len()).sum::<usize>()
    );
    if fields.is_empty() && taken.is_empty() {
        out.push_str("# nothing is accessed through it in this function\n");
        return Ok(out);
    }
    let offsets: BTreeSet<i64> = fields.keys().chain(taken.keys()).copied().collect();
    let width = |at: &i64| {
        fields.get(at).map_or(0, |f| {
            i64::from(f.widths.iter().copied().max().unwrap_or(0))
        })
    };
    let low = offsets.first().copied().unwrap_or(0).min(0);
    let high = offsets
        .iter()
        .map(|at| at.saturating_add(width(at)))
        .max()
        .unwrap_or(0);
    let _ = writeln!(
        out,
        "# {} field(s) over {:#x} bytes\n# offset  size  access        seen",
        offsets.len(),
        high.saturating_sub(low)
    );
    for at in offsets.iter().take(FIELDS_MAX) {
        let shown = if *at < 0 {
            format!("-{:#x}", at.unsigned_abs())
        } else {
            format!("{at:#x}")
        };
        let note = taken.get(at).map_or(String::new(), |n| format!("  {n}"));
        let Some(f) = fields.get(at) else {
            let _ = writeln!(out, "{shown:<8} {:<5} {:<13} -{note}", "-", "addressed");
            continue;
        };
        let access = match (f.read, f.written) {
            (true, true) => "read, written",
            (true, false) => "read",
            (false, true) => "written",
            (false, false) => "addressed",
        };
        let mut widths = f.widths.clone();
        widths.sort_unstable();
        let size = widths
            .iter()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join("/");
        let _ = writeln!(
            out,
            "{shown:<8} {size:<5} {access:<13} {}x{note}",
            f.sites.len()
        );
    }
    more_line(&mut out, offsets.len(), FIELDS_MAX, "fields not listed");
    Ok(out)
}

/// The fields a pointer's accesses show, for a struct to be stated from
/// them ([`crate::analysis::apply::from_pointer`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PointerFields {
    /// Entry of the function the pointer is followed through.
    pub entry: u64,
    /// The register followed, lowercase as the spec spelled it.
    pub register: String,
    /// The parameter position the register holds, when the spec starts at
    /// the function's entry and the register carries an argument there.
    pub param: Option<usize>,
    /// The widest access at each offset, in bytes.
    pub widths: BTreeMap<i64, u32>,
    /// The offsets only handed to calls, which state no width.
    pub addressed: Vec<i64>,
}

/// Reads the fields a function's accesses through one pointer show, as
/// [`layout_tsv`] proposes them, with the parameter the pointer arrives
/// in.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names and types.
/// * `spec` - `<address>` or `<address>,<register>`, as [`layout_tsv`]
///   reads it.
///
/// # Returns
///
/// The fields and where the pointer comes from.
///
/// # Errors
///
/// When the spec is refused or the function's code does not read.
pub fn layout_fields(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    spec: &str,
) -> Result<PointerFields, String> {
    let Accesses {
        spec: parsed,
        fields,
        taken,
    } = accesses(p, a, o, spec)?;
    let param = (parsed.start == parsed.entry)
        .then(|| {
            crate::analysis::decompile::signature::passing(p, a, o, parsed.entry)
                .regs
                .iter()
                .position(|r| r.full_register() == parsed.seed.full_register())
        })
        .flatten();
    Ok(PointerFields {
        entry: parsed.entry,
        register: parsed.wanted,
        param,
        widths: fields
            .iter()
            .filter_map(|(at, f)| Some((*at, f.widths.iter().copied().max()?)))
            .collect(),
        addressed: taken
            .keys()
            .filter(|at| !fields.contains_key(at))
            .copied()
            .collect(),
    })
}

/// What a function does through one pointer: the fields it reads and
/// writes by offset, and the offsets it only hands to calls.
struct Accesses {
    /// The parsed spec.
    spec: ValueSpec,
    /// The fields accessed, by offset from the pointer.
    fields: BTreeMap<i64, Field>,
    /// The offsets handed to calls, with what each call is.
    taken: BTreeMap<i64, String>,
}

/// Follows one pointer through a function, collecting what [`layout_tsv`]
/// reports (its documentation says how the offsets are tracked).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - `<address>` or `<address>,<register>`.
///
/// # Errors
///
/// When the spec is refused or the function's code does not read.
fn accesses(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<Accesses, String> {
    /// Passes over the function, so a loop's back edge is followed once.
    const PASSES: usize = 2;
    /// Largest offset treated as a field rather than an unrelated pointer.
    const SPAN_MAX: i64 = 1 << 16;
    x86_reading(p, "layout")?;
    let parsed = ValueSpec::parse(
        p,
        a,
        o,
        spec,
        p.arch.bitness().or(Some(64)),
        Follow::FirstArgument,
    )?;
    let ValueSpec {
        start,
        entry,
        seed,
        bitness,
        ..
    } = parsed;
    let instrs = function_instructions(p, a, entry);
    if instrs.is_empty() {
        return Err(format!("no code at {entry:#x}"));
    }
    let (arguments, volatile) = (
        argument_registers(p, entry, bitness),
        volatile_registers(p, entry, bitness),
    );
    let mut holds: BTreeMap<Register, i64> = BTreeMap::new();
    holds.insert(seed, 0);
    let mut fields: BTreeMap<i64, Field> = BTreeMap::new();
    let mut taken: BTreeMap<i64, String> = BTreeMap::new();
    let mut factory = InstructionInfoFactory::new();
    for _ in 0..PASSES {
        for i in &instrs {
            if i.ip() < start {
                continue;
            }
            if let Some(base) = holds.get(&canonical(i.memory_base(), bitness)).copied()
                && i.memory_base() != Register::None
            {
                let at = base.saturating_add(disasm::displacement(i, bitness));
                let size = i.memory_size().size();
                if at.abs() < SPAN_MAX && size > 0 {
                    let info = factory.info(i);
                    let (mut read, mut write) = (false, false);
                    for m in info.used_memory() {
                        match m.access() {
                            OpAccess::Read | OpAccess::CondRead => read = true,
                            OpAccess::Write | OpAccess::CondWrite => write = true,
                            OpAccess::ReadWrite | OpAccess::ReadCondWrite => {
                                read = true;
                                write = true;
                            }
                            OpAccess::None | OpAccess::NoMemAccess => {}
                        }
                    }
                    let slot = fields.entry(at).or_default();
                    slot.read |= read;
                    slot.written |= write;
                    slot.sites.insert(i.ip());
                    let width = u32::try_from(size).unwrap_or(0);
                    if !slot.widths.contains(&width) {
                        slot.widths.push(width);
                    }
                }
            }
            if i.mnemonic() == Mnemonic::Lea
                && let Some(base) = holds.get(&canonical(i.memory_base(), bitness)).copied()
            {
                let at = base.saturating_add(i.memory_displacement64().cast_signed());
                if i.op0_kind() == OpKind::Register && at.abs() < SPAN_MAX {
                    holds.insert(canonical(i.op0_register(), bitness), at);
                    continue;
                }
            }
            let moved = i.mnemonic() == Mnemonic::Mov
                && i.op0_kind() == OpKind::Register
                && i.op1_kind() == OpKind::Register;
            if moved && let Some(base) = holds.get(&canonical(i.op1_register(), bitness)).copied() {
                holds.insert(canonical(i.op0_register(), bitness), base);
                continue;
            }
            if matches!(
                i.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                let preserves = preserves_registers(a, o, i);
                for (k, r) in arguments.iter().enumerate() {
                    if preserves {
                        break;
                    }
                    let Some(at) = holds.get(&canonical(*r, bitness)).copied() else {
                        continue;
                    };
                    let note = format!("passed to {} as argument {}", callee_name(a, o, i), k + 1);
                    taken.entry(at).or_insert(note);
                }
                if !preserves {
                    for r in volatile {
                        holds.remove(&canonical(*r, bitness));
                    }
                }
                continue;
            }
            let info = factory.info(i);
            for ur in info.used_registers() {
                if matches!(
                    ur.access(),
                    OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite
                ) {
                    holds.remove(&canonical(ur.register(), bitness));
                }
            }
        }
    }
    Ok(Accesses {
        spec: parsed,
        fields,
        taken,
    })
}

/// One offset a function touches through a pointer.
#[derive(Default)]
pub(super) struct Field {
    /// Access widths seen at this offset, in the order first seen.
    pub(super) widths: Vec<u32>,
    /// The offset is read.
    pub(super) read: bool,
    /// The offset is written.
    pub(super) written: bool,
    /// The instructions that touched it, each once however many passes
    /// read it.
    pub(super) sites: BTreeSet<u64>,
}

/// Decodes every instruction of a function, in address order.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The instructions, deduplicated by address; empty when the function is not
/// known or its bytes are not readable.
pub(super) fn function_instructions(p: &Program, a: &Analysis, entry: u64) -> Vec<Instruction> {
    let Some((f, bitness)) = a.function(entry).zip(p.arch.bitness()) else {
        return Vec::new();
    };
    let mut instrs: Vec<Instruction> = Vec::new();
    for b in &f.blocks {
        let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(0);
        let Some(code) = p.read_va_upto(b.start, len.max(1)) else {
            continue;
        };
        let mut d = Decoder::with_ip(bitness, code, b.start, DecoderOptions::NONE);
        while d.can_decode() {
            let i = d.decode();
            if i.is_invalid() || i.ip() >= b.end {
                break;
            }
            instrs.push(i);
        }
    }
    instrs.sort_by_key(Instruction::ip);
    instrs.dedup_by_key(|i| i.ip());
    instrs
}

/// Says what is at an address, and how borer knows.
///
/// Every other tool answers with a fact and leaves its origin implicit, so a
/// reader cannot tell the difference between a name the compiler wrote down,
/// a name a signature string implied, a name the user set, and `sub_` plus an
/// address. Those four carry completely different weight, and an agent
/// deciding whether to trust an answer needs to know which it has.
///
/// This reports the answer and its evidence together, in this order: what
/// the address is; where its name came from, which is the whole point; why
/// the function was discovered at all, which is not the same as what it is;
/// what refers to it; and what borer worked out by running the code, for
/// data a value recovered from it. A comment the user recorded comes last,
/// and one opening with a question mark is something a reader guessed and
/// has not shown, which is reported as an open question rather than a
/// finding, since the difference is the point of recording it.
///
/// The target is a function by name or address first; failing that,
/// anything the program names: an import, an export, a data symbol.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names and comments.
/// * `target` - An address or a name.
///
/// # Returns
///
/// A short report, one fact per line, each with where it came from.
///
/// # Errors
///
/// When the target names nothing.
pub fn why_tsv(p: &Program, a: &Analysis, o: &Overlay, target: &str) -> Result<String, String> {
    /// Referring sites listed before the rest are counted.
    const SITES_MAX: usize = 8;
    let va = locate(a, o, target)
        .or_else(|| crate::analysis::resolve(p, a, o, target).ok())
        .ok_or_else(|| unresolved(target))?;
    let mut out = String::new();
    let section = p.section_at(va);
    let debug = p.debug_functions.iter().find(|d| d.low_pc == va);
    let symbol = a.symbol_at(p, va);
    let function = a.function(va);
    let containing = a.function_at(va);

    match (function, containing) {
        (Some(f), _) => {
            let _ = writeln!(
                out,
                "# {va:#x} is the entry of {}: {} bytes, {} blocks, {} instructions",
                short_name(a, o, va),
                f.size(),
                f.blocks.len(),
                f.instr_count
            );
        }
        (None, Some(f)) => {
            let block = f
                .blocks
                .iter()
                .filter(|b| b.start <= va)
                .max_by_key(|b| b.start);
            let _ = writeln!(
                out,
                "# {va:#x} is inside {}, in the block at {}",
                short_name(a, o, f.entry),
                block.map_or_else(|| String::from("?"), |b| format!("{:#x}", b.start))
            );
        }
        (None, None) => {
            let _ = writeln!(
                out,
                "# {va:#x} is not in any discovered function{}",
                section.map_or_else(String::new, |s| format!(", it is in {}", s.name))
            );
        }
    }
    if let Some(s) = section {
        let _ = writeln!(
            out,
            "# section {} at {:#x}, {} and {}",
            s.name,
            s.va.0,
            s.perms(),
            if s.executable { "code" } else { "data" }
        );
    }

    let go = p.go.as_ref().filter(|g| g.lists(va));
    let method = p
        .clr()
        .and_then(|c| c.method_at(p.image_base, va))
        .filter(|m| p.symbols.iter().any(|s| s.addr == va && s.name == m.name));
    let origin = if let Some(n) = o.names.get(&va) {
        format!("you set it: {n}")
    } else if let Some(d) = debug {
        format!(
            "the debug information records it as {}, so it is what the compiler called it",
            d.name
        )
    } else if let (Some(g), Some(s)) = (
        go,
        symbol.filter(|s| s.addr == va && s.kind == SymbolKind::Local),
    ) {
        format!(
            "the Go function table (pclntab, {}) records it: {}",
            g.version.releases(),
            s.name
        )
    } else if let Some(m) = method {
        format!(
            "the .NET metadata records it as method {:#010x} {}, {}",
            m.token,
            m.name,
            match m.body {
                crate::clr::Body::Native => "a native method, analyzed as code",
                crate::clr::Body::Il | crate::clr::Body::Runtime | crate::clr::Body::None =>
                    "an IL body, which borer does not decompile",
            }
        )
    } else if let Some(s) = symbol.filter(|s| s.addr == va) {
        format!(
            "the {} symbol table: {}",
            s.kind.name(),
            crate::search::demangled_name(&s.name)
        )
    } else if let Some(f) = function.filter(|f| f.name.is_some()) {
        let name = f.name.clone().unwrap_or_default();
        if f.name_inferred {
            format!("{}: {name}", f.name_source.describe())
        } else {
            format!("declared in the binary: {name}")
        }
    } else {
        String::from("nothing names it, so the name is the address")
    };
    let _ = writeln!(out, "# name: {origin}");
    if let Some(d) = debug {
        let params: Vec<String> = d
            .parameters
            .iter()
            .map(|q| match &q.type_name {
                Some(t) if t.ends_with(['*', '&']) => format!("{t}{}", q.name),
                Some(t) => format!("{t} {}", q.name),
                None => q.name.clone(),
            })
            .collect();
        let _ = writeln!(
            out,
            "# signature, from the debug information: {} {}({})",
            d.return_type
                .clone()
                .unwrap_or_else(|| String::from("void")),
            d.name,
            params.join(", ")
        );
    }

    if let Some(f) = function {
        let mut how: Vec<String> = Vec::new();
        if p.entry == Some(va) {
            how.push(String::from("the image's entry point"));
        }
        if p.symbols
            .iter()
            .any(|s| s.addr == va && s.kind == SymbolKind::Export)
        {
            how.push(String::from("an export"));
        }
        if p.function_ranges.iter().any(|(s, _)| *s == va) {
            how.push(String::from("an entry in the exception or symbol table"));
        }
        if debug.is_some() {
            how.push(String::from("the debug information"));
        }
        if go.is_some() {
            how.push(String::from("the Go function table"));
        }
        if method.is_some() {
            how.push(String::from("the .NET metadata"));
        }
        if !f.callers.is_empty() {
            how.push(format!("{} call site(s)", f.callers.len()));
        }
        if how.is_empty() {
            how.push(String::from(
                "a sweep of the code, with nothing else pointing at it",
            ));
        }
        let _ = writeln!(out, "# discovered by: {}", how.join(", then "));
    }

    if let Some(sites) = a.xrefs.get(&va) {
        let shown: Vec<String> = sites
            .iter()
            .take(SITES_MAX)
            .map(|s| {
                s.from_entry.map_or_else(
                    || format!("{:#x}", s.va),
                    |e| format!("{:#x} in {}", s.va, short_name(a, o, e)),
                )
            })
            .collect();
        let _ = writeln!(
            out,
            "# referenced from {} site(s): {}{}",
            sites.len(),
            shown.join(", "),
            plus_more(sites.len(), SITES_MAX)
        );
    }

    if let Some((_, literal)) = string_literal(p, va, STRING_MATCH_CAP) {
        let _ = writeln!(out, "# the bytes here read as a string: {literal}");
    }
    for g in recovered_strings(p, a)
        .found
        .iter()
        .filter(|g| g.built_by == va)
    {
        let _ = writeln!(
            out,
            "# running it recovers {:?}, which is not in the strings table",
            g.text
        );
    }
    if let Some(c) = o.comments.get(&va) {
        match c.trim_start().strip_prefix('?') {
            Some(claim) => {
                let _ = writeln!(
                    out,
                    "# an open question you recorded: {}",
                    claim.trim_start()
                );
            }
            None => {
                let _ = writeln!(out, "# a finding you recorded: {c}");
            }
        }
    }
    Ok(out)
}

/// Refuses an arm64 program for a reading that follows x86 instructions.
///
/// The agent learns it is the instruction set, not the address.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `what` - The reading, as its resource names it.
///
/// # Errors
///
/// The sentence for an arm64 program.
pub(super) fn x86_reading(p: &Program, what: &str) -> Result<(), String> {
    match p.arch.isa() {
        Some(crate::isa::Isa::A64) => Err(format!(
            "{what} follows x86 and x86-64 instructions only; this {} file's arm64 code decompiles (decompile) but is not followed this way yet",
            p.format.name()
        )),
        Some(crate::isa::Isa::X86 { .. }) | None => Ok(()),
    }
}

/// Says why a spec's address token was refused.
///
/// An empty token says that nothing was given, where `cannot resolve `
/// followed by nothing read as a truncated message.
///
/// # Arguments
///
/// * `token` - The token as the spec carried it, trimmed.
///
/// # Returns
///
/// The message.
pub(super) fn unresolved(token: &str) -> String {
    if token.is_empty() {
        String::from("no address or name given")
    } else {
        format!("cannot resolve {}", crate::text::one_line(token))
    }
}

/// Reads a count or a length in a spec: `0x`-hex or decimal.
///
/// An address may be written as bare hex, so [`parse_addr`] reads `abc` as
/// `0xabc`; a count written `steps=abc` is a typo, and reading it as 2748
/// steps ran a different experiment than the one asked for with nothing
/// to say so.
///
/// # Arguments
///
/// * `text` - The value as written.
///
/// # Returns
///
/// The count, or `None` when the text is not one.
pub(super) fn parse_count(text: &str) -> Option<usize> {
    let t = text.trim();
    match t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        Some(hex) => usize::from_str_radix(hex, 16).ok(),
        None => t.parse().ok(),
    }
}

/// The registers a function's arguments, and the arguments of the calls it
/// makes, travel in, in convention order, as the value passes read them.
///
/// On a 64-bit target they are the function's own convention's, as the
/// decompiler names its `a1`..`aN` ([`lift::conv_at`]): `rcx`, `rdx`, `r8`,
/// `r9` on a PE, `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9` on an ELF or
/// Mach-O, Go's for a function its table lists. A 32-bit `cdecl` or
/// `stdcall` call passes every argument on the stack, so a value left in
/// `edx` is not an argument, and only `ecx` is taken: where a `thiscall`
/// method takes `this` and a `fastcall` callee its first argument, as the
/// vtable scans read 32-bit code.
///
/// # Arguments
///
/// * `p` - The loaded image, whose format and Go table pick the convention.
/// * `entry` - The function's entry.
/// * `bitness` - Decoder bitness of the program.
pub(super) fn argument_registers(p: &Program, entry: u64, bitness: u32) -> &'static [Register] {
    if bitness == 32 {
        &[Register::ECX]
    } else {
        lift::conv_at(p, entry, bitness).args
    }
}

/// The registers a call made by a function lets the callee destroy, by the
/// function's own convention ([`lift::conv_at`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `entry` - The function's entry.
/// * `bitness` - Decoder bitness of the program.
pub(super) fn volatile_registers(p: &Program, entry: u64, bitness: u32) -> &'static [Register] {
    lift::conv_at(p, entry, bitness).volatile
}

/// Names what a call goes to: the target of a direct call of any width,
/// `an indirect call` otherwise.
///
/// # Arguments
///
/// * `a` - The analysis, to name the target.
/// * `o` - User names.
/// * `i` - The call instruction.
pub(super) fn callee_name(a: &Analysis, o: &Overlay, i: &Instruction) -> String {
    if is_near_call(i) {
        short_name(a, o, i.near_branch_target())
    } else {
        String::from("an indirect call")
    }
}

/// Whether a call goes to a helper that preserves every register.
///
/// A compiler emits a stack probe in the prologue, before the arguments are
/// homed, and the code after it reads them as if nothing had happened,
/// because nothing did. Applying the calling convention to these would drop
/// the value being followed on the first instruction of most functions, and
/// reporting one as a consumer of an argument is noise: a probe reads a
/// size.
///
/// # Arguments
///
/// * `a` - The analysis, to name the target.
/// * `o` - User names.
/// * `i` - The call instruction.
///
/// # Returns
///
/// Whether the callee leaves every register as it found it.
pub(in crate::analysis) fn preserves_registers(a: &Analysis, o: &Overlay, i: &Instruction) -> bool {
    /// Helpers that preserve every register.
    const PRESERVING: [&str; 5] = [
        "__chkstk",
        "___chkstk_ms",
        "__chkstk_ms",
        "__security_check_cookie",
        "_alloca",
    ];
    is_near_call(i) && PRESERVING.contains(&short_name(a, o, i.near_branch_target()).as_str())
}

/// Whether a call goes to a prologue helper that builds the caller's frame.
///
/// `__SEH_prolog4` and `__EH_prolog3` push the exception registration, set
/// `ebp` and return with the stack lower, so the caller's own prologue
/// continues after the call as if nothing had been called: its arguments are
/// still in place, and the registers it saves next are still its saves.
///
/// # Arguments
///
/// * `a` - The analysis, to name the target.
/// * `o` - User names.
/// * `i` - The call instruction.
///
/// # Returns
///
/// Whether the callee is one of the frame helpers.
pub(in crate::analysis) fn frame_helper(a: &Analysis, o: &Overlay, i: &Instruction) -> bool {
    /// The MSVC prologue helpers, as [`crate::analysis::functions::frame_helper_name`] names them.
    const HELPERS: [&str; 2] = ["__SEH_prolog4", "__EH_prolog3"];
    is_near_call(i) && HELPERS.contains(&short_name(a, o, i.near_branch_target()).as_str())
}

/// Whether a call goes to an epilogue helper that tears the caller's frame
/// down.
///
/// `__SEH_epilog4` and `__EH_epilog3` unlink the exception registration,
/// restore the saved registers, release the frame and return to the
/// caller's own return address, so the caller's `ret` right after the
/// call is the function's return and nothing else.
///
/// # Arguments
///
/// * `a` - The analysis, to name the target.
/// * `o` - User names.
/// * `i` - The call instruction.
///
/// # Returns
///
/// Whether the callee is one of the epilogue helpers.
pub(in crate::analysis) fn epilog_helper(a: &Analysis, o: &Overlay, i: &Instruction) -> bool {
    /// The MSVC epilogue helpers, as [`crate::analysis::functions::epilog_helper_name`] names them.
    const HELPERS: [&str; 2] = ["__SEH_epilog4", "__EH_epilog3"];
    is_near_call(i) && HELPERS.contains(&short_name(a, o, i.near_branch_target()).as_str())
}

/// Whether an instruction is a call to a near, direct target of any width.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(super) fn is_near_call(i: &Instruction) -> bool {
    i.mnemonic() == Mnemonic::Call
        && matches!(
            i.op0_kind(),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
        )
}

/// The register names a target's code is written in: what a value pass
/// defaults to and what it tells the caller to use.
pub(super) struct RegisterNames {
    /// Where a call leaves its result.
    pub(super) result: &'static str,
    /// The names accepted, as an error message spells them.
    pub(super) range: &'static str,
}

impl RegisterNames {
    /// Picks the names for a decoder bitness.
    ///
    /// # Arguments
    ///
    /// * `bitness` - 32 or 64.
    pub(super) fn for_bitness(bitness: u32) -> Self {
        if bitness == 32 {
            Self {
                result: "eax",
                range: "eax..edi",
            }
        } else {
            Self {
                result: "rax",
                range: "rax..r15",
            }
        }
    }
}

/// The key a value pass files a register under.
///
/// That is the whole register in the target's width, `ecx` for `cl` or
/// `ecx` on a 32-bit target and `rcx` on a 64-bit one, the form
/// [`iced_register`] hands back for a seed. Keying a 32-bit operand by its 64-bit parent missed the seed, so a value
/// never spread and a write never cleared what it overwrote.
///
/// # Arguments
///
/// * `r` - A register an instruction names.
/// * `bitness` - Decoder bitness of the program.
pub(super) fn canonical(r: Register, bitness: u32) -> Register {
    if bitness == 32 {
        r.full_register32()
    } else {
        r.full_register()
    }
}

/// Resolves a lowercase general register name for the value passes.
///
/// Both spellings of a legacy register are taken (`rax` and `eax`), and
/// the register handed back is the one the target's code names: the 32-bit
/// form on a 32-bit target, where `r8`..`r15` do not exist.
///
/// # Arguments
///
/// * `name` - The lowercase name.
/// * `bitness` - Decoder bitness of the program.
///
/// # Returns
///
/// The register, or `None` when the name is not one the target has.
pub(super) fn iced_register(name: &str, bitness: u32) -> Option<Register> {
    let (wide, legacy) = match name {
        "rax" | "eax" => (Register::RAX, true),
        "rbx" | "ebx" => (Register::RBX, true),
        "rcx" | "ecx" => (Register::RCX, true),
        "rdx" | "edx" => (Register::RDX, true),
        "rsi" | "esi" => (Register::RSI, true),
        "rdi" | "edi" => (Register::RDI, true),
        "rbp" | "ebp" => (Register::RBP, true),
        "rsp" | "esp" => (Register::RSP, true),
        "r8" => (Register::R8, false),
        "r9" => (Register::R9, false),
        "r10" => (Register::R10, false),
        "r11" => (Register::R11, false),
        "r12" => (Register::R12, false),
        "r13" => (Register::R13, false),
        "r14" => (Register::R14, false),
        "r15" => (Register::R15, false),
        _ => return None,
    };
    match bitness {
        32 if legacy => Some(wide.full_register32()),
        32 => None,
        _ => Some(wide),
    }
}

/// Largest region a single experiment dump reads back, in bytes.
pub(super) const DUMP_MAX: usize = 4096;

/// A parsed experiment: where to start, what state to set, what to read back.
///
/// The surface an agent drives to change how a routine behaves and see the
/// result: set registers and arguments, write bytes (data to set up, or code
/// to patch a check away), halt at a chosen address, and read regions back.
/// Every field comes from one comma-separated string so a client passes it
/// through a single parameter and repeats the run with one edit.
#[derive(Debug, Default)]
pub(super) struct ExperimentSpec {
    /// Address execution starts at.
    pub(super) entry: u64,
    /// Registers to set, as `(lowercase name, value)`.
    pub(super) regs: Vec<(String, u64)>,
    /// Arguments to set, as `(position from zero, value)`: `a1` is position 0.
    pub(super) args: Vec<(usize, u64)>,
    /// Bytes to write before the run, as `(address, bytes)`.
    pub(super) writes: Vec<(u64, Vec<u8>)>,
    /// Regions to hexdump after the run, as `(address, length read, length
    /// asked)`: the read stops at [`DUMP_MAX`] bytes and at the end of the
    /// address space.
    pub(super) dumps: Vec<(u64, usize, usize)>,
    /// Address to halt at, if any.
    pub(super) stop: Option<u64>,
    /// Instruction budget.
    pub(super) budget: usize,
    /// Instructions to trace, step by step.
    pub(super) trace: usize,
    /// The value whose first appearance the run watches for.
    pub(super) origin: Option<u64>,
    /// How many of the hottest addresses and most-read pages to report;
    /// zero profiles nothing.
    pub(super) profile: usize,
}

impl ExperimentSpec {
    /// Parses the comma-separated spec.
    ///
    /// The first token is the start address or a function name. A bare
    /// address runs as given, function or not: the experiment surface starts
    /// anywhere, at a block, a loop head or mid-routine ([`emulate_tsv`]
    /// refuses a start nothing maps). The rest are directives:
    /// `reg=val` sets a register, `aN=val` the argument the decompiler names
    /// `aN`, counting from one as it does (`a1` is the first, so a name copied
    /// out of the pseudo-C sets that argument; `a0` names none and is refused
    /// rather than read as the first), `w<addr>=<hex>`
    /// writes bytes, `stop=<addr>` halts there, `steps=<n>` sets the budget
    /// (at most [`BUDGET_MAX`], as `run` takes; more is refused, not run for
    /// hours), `trace=<n>` records what each of the last `n` instructions changed
    /// (the run's head is watched by giving it a small `steps=`),
    /// `origin=<v>` names the instruction that first produced `v` in a
    /// register or in memory, `profile=<n>` reports the `n` most-executed
    /// addresses and most-read pages off the stack (where a budget went),
    /// and `dump=<addr>:<len>` reads a region back as a load reads it (what
    /// the run wrote over the image's bytes, `??` where a load faults), at
    /// most [`DUMP_MAX`] bytes, saying when it read fewer. A bare `reg=val` stays
    /// backward compatible with the older register-only form. Every count
    /// and length is `0x`-hex or decimal ([`parse_count`]): `dump=0x3000:0x80`
    /// is as natural as `:128` next to the addresses around it, and a word
    /// is refused rather than read as hex. A dump stops at the end of the
    /// address space rather than wrapping to zero, which would misreport
    /// what it read.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis, for resolving a name.
    /// * `o` - The overlay, for resolving a name.
    /// * `target` - The spec string.
    ///
    /// # Returns
    ///
    /// The parsed spec, or a message naming the directive that did not parse.
    ///
    /// # Errors
    ///
    /// When the start token does not resolve, or a directive is malformed.
    pub(super) fn parse(a: &Analysis, o: &Overlay, target: &str) -> Result<Self, String> {
        /// Most rows a profile reports of each kind.
        const PROFILE_MAX: usize = 64;
        let (addr, parts) = spec_head(target);
        let entry = locate(a, o, addr).ok_or_else(|| unresolved(addr))?;
        let mut spec = Self {
            entry,
            budget: EMULATE_BUDGET,
            origin: None,
            ..Self::default()
        };
        for raw in parts {
            let text = raw.trim();
            if text.is_empty() {
                continue;
            }
            let token = crate::text::one_line(text);
            let (key, value) = text.split_once('=').ok_or_else(|| {
                format!(
                    "cannot read the directive {token}; use reg=v, aN=v, w<addr>=<hex>, stop=<addr>, steps=N, trace=N, origin=v, profile=N or dump=<addr>:<len>"
                )
            })?;
            let key = key.trim();
            let value = value.trim();
            if let Some(rest) = key.strip_prefix('w') {
                let at = parse_addr(rest).ok_or_else(|| format!("bad write address in {token}"))?;
                let bytes =
                    parse_hex_bytes(value).ok_or_else(|| format!("bad write bytes in {token}"))?;
                spec.writes.push((at, bytes));
            } else if key == "stop" {
                spec.stop =
                    Some(parse_addr(value).ok_or_else(|| format!("bad stop address in {token}"))?);
            } else if key == "origin" {
                spec.origin =
                    Some(parse_addr(value).ok_or_else(|| format!("bad origin value in {token}"))?);
            } else if key == "trace" {
                spec.trace =
                    parse_count(value).ok_or_else(|| format!("bad trace count in {token}"))?;
            } else if key == "profile" {
                spec.profile = parse_count(value)
                    .ok_or_else(|| format!("bad profile count in {token}"))?
                    .min(PROFILE_MAX);
            } else if key == "steps" {
                spec.budget =
                    parse_count(value).ok_or_else(|| format!("bad step count in {token}"))?;
                if spec.budget > BUDGET_MAX {
                    return Err(format!("{token}: steps is at most {BUDGET_MAX}"));
                }
            } else if key == "dump" {
                let (addr, len) = value
                    .split_once(':')
                    .ok_or_else(|| format!("dump needs addr:len in {token}"))?;
                let addr = parse_addr(addr.trim())
                    .ok_or_else(|| format!("bad dump address in {token}"))?;
                let len = parse_count(len).ok_or_else(|| format!("bad dump length in {token}"))?;
                let room =
                    usize::try_from((u64::MAX - addr).saturating_add(1)).unwrap_or(usize::MAX);
                spec.dumps.push((addr, len.min(DUMP_MAX).min(room), len));
            } else if let Some(n) = key.strip_prefix('a').filter(|n| !n.is_empty()) {
                if let Ok(number) = n.parse::<usize>() {
                    let position = number.checked_sub(1).ok_or_else(|| {
                        format!(
                            "{token}: arguments count from one as the decompiler names them; a1 is the first"
                        )
                    })?;
                    let v = parse_addr(value)
                        .ok_or_else(|| format!("bad argument value in {token}"))?;
                    spec.args.push((position, v));
                } else {
                    let v = parse_addr(value)
                        .ok_or_else(|| format!("bad register value in {token}"))?;
                    spec.regs.push((key.to_lowercase(), v));
                }
            } else {
                let v =
                    parse_addr(value).ok_or_else(|| format!("bad register value in {token}"))?;
                spec.regs.push((key.to_lowercase(), v));
            }
        }
        Ok(spec)
    }

    /// Renders the setup as a note for the header, empty when nothing was set.
    pub(super) fn setup_note(&self) -> String {
        let mut parts: Vec<String> = Vec::new();
        for (r, v) in &self.regs {
            parts.push(format!("{r}={v:#x}"));
        }
        for (position, v) in &self.args {
            parts.push(format!("a{}={v:#x}", position + 1));
        }
        for (at, bytes) in &self.writes {
            parts.push(format!("w{at:#x}={} bytes", bytes.len()));
        }
        if parts.is_empty() {
            String::new()
        } else {
            format!(" with {}", parts.join(" "))
        }
    }
}

/// Parses a run of hex byte pairs, spaces allowed, into bytes.
///
/// # Arguments
///
/// * `text` - Hex digits, optionally space-separated (`90 90` or `9090`).
///
/// # Returns
///
/// The bytes, or `None` when a character is not hex or the digit count is odd.
pub(super) fn parse_hex_bytes(text: &str) -> Option<Vec<u8>> {
    let clean: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    if clean.is_empty() || !clean.len().is_multiple_of(2) {
        return None;
    }
    (0..clean.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(clean.get(i..i + 2)?, 16).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{ExperimentSpec, argument_registers, layout_tsv, parse_count, taint_tsv, why_tsv};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program, Section};

    /// A 32-bit program whose one page of code at `0x1000` starts with
    /// `code`, padded with `int3`.
    ///
    /// # Arguments
    ///
    /// * `code` - The first bytes of the page.
    fn raw_x86(code: &[u8]) -> Program {
        let mut bytes = vec![0xcc; 0x1000];
        bytes[..code.len()].copy_from_slice(code);
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        Program::raw(bytes, Arch::X86, 0, Some(0x1000), vec![text])
    }

    /// A layout stops following a register an untracked move or `lea`
    /// overwrites, counts each access once over both passes, prints an
    /// offset below the pointer as negative, and counts its rows in the
    /// header.
    ///
    /// It kept the stale offset, so the stack writes through `rax` and
    /// `rdx` read as fields at 0x18 and 0x0, every access was seen twice,
    /// and -8 printed as `0xfffffffffffffff8`.
    ///
    /// # Panics
    ///
    /// When a stack access reads as a field or a count or offset is off.
    #[test]
    fn a_layout_drops_a_register_an_untracked_write_overwrites() {
        let p = Program::raw_x64(&[
            0x48, 0x8d, 0x41, 0x10, // ASM: lea rax,[rcx+0x10]
            0x48, 0x89, 0xe0, // ASM: mov rax,rsp
            0x48, 0x89, 0x58, 0x08, // ASM: mov [rax+8],rbx
            0x8b, 0x41, 0x08, // ASM: mov eax,[rcx+8]
            0x48, 0x89, 0xca, // ASM: mov rdx,rcx
            0x48, 0x8d, 0x54, 0x24, 0x20, // ASM: lea rdx,[rsp+0x20]
            0x89, 0x1a, // ASM: mov [rdx],ebx
            0x89, 0x59, 0xf8, // ASM: mov [rcx-8],ebx
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let out = layout_tsv(&p, &a, &Overlay::default(), "0x1000").expect("a layout");
        assert_eq!(
            out,
            "# structure through rcx of sub_1000, from 2 access site(s)\n\
             # 2 field(s) over 0x14 bytes\n\
             # offset  size  access        seen\n\
             -0x8     4     written       1x\n\
             0x8      4     read          1x\n"
        );
    }

    /// A 32-bit call is direct and takes only `ecx`.
    ///
    /// A value spreads through 32-bit registers, a direct call is named, not
    /// an indirect call, and only `ecx` is an argument register: a `cdecl` or
    /// `stdcall` callee takes its arguments on the stack, so `edx` reaching
    /// the call is not one. Operands were keyed by
    /// their 64-bit parents and never met the seed, only a 64-bit branch
    /// was read as direct, and `edx` was the second argument.
    ///
    /// # Panics
    ///
    /// When a direct call reads as indirect or `edx` as an argument.
    #[test]
    fn a_32_bit_call_is_direct_and_takes_only_ecx() {
        let p = raw_x86(&[
            0x8b, 0x41, 0x04, // ASM: mov eax,[ecx+4]
            0x8d, 0x51, 0x08, // ASM: lea edx,[ecx+8]
            0xe8, 0x05, 0x00, 0x00, 0x00, // ASM: call 0x1010
            0xc3, // ASM: ret
            0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let layout = layout_tsv(&p, &a, &o, "0x1000").expect("a layout");
        assert!(
            layout.contains("0x0      -     addressed     -  passed to sub_1010 as argument 1\n"),
            "{layout}"
        );
        assert!(!layout.contains("argument 2"), "{layout}");
        assert!(!layout.contains("\n0x8 "), "{layout}");
        let taint = taint_tsv(&p, &a, &o, "0x1003,edx").expect("a taint");
        assert!(!taint.contains("takes it"), "{taint}");
        let taint = taint_tsv(&p, &a, &o, "0x1000,ecx").expect("a taint");
        assert!(taint.contains("now in edx\n"), "{taint}");
        assert!(
            taint.contains("sub_1010 takes it as argument 1\n"),
            "{taint}"
        );
        assert!(!taint.contains("indirect"), "{taint}");
    }

    /// A count is `0x`-hex or decimal; a word is not read as bare hex.
    ///
    /// # Panics
    ///
    /// When a word reads as a count or a count does not read.
    #[test]
    fn a_count_is_hex_or_decimal_never_a_word() {
        assert_eq!(parse_count("0x80"), Some(128));
        assert_eq!(parse_count(" 128 "), Some(128));
        assert_eq!(parse_count("abc"), None);
        assert_eq!(parse_count(""), None);
    }

    /// A malformed directive is refused naming its token, not run with a
    /// default: `steps=abc` read as hex ran 2748 steps.
    ///
    /// # Panics
    ///
    /// When a malformed directive parses, or its refusal does not name it.
    #[test]
    fn an_experiment_refuses_a_malformed_directive() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        for (spec, token) in [
            ("0x1000,steps=abc", "steps=abc"),
            ("0x1000,steps=99999999999", "steps is at most 20000000"),
            ("0x1000,trace=zz", "trace=zz"),
            ("0x1000,dump=0x1000:abc", "dump=0x1000:abc"),
            ("0x1000,foo", "directive foo"),
            ("0x1000,w0x1=zz", "w0x1=zz"),
        ] {
            let err = ExperimentSpec::parse(&a, &o, spec).unwrap_err();
            assert!(err.contains(token), "{spec}: {err}");
        }
        assert_eq!(
            ExperimentSpec::parse(&a, &o, "nowhere").unwrap_err(),
            "cannot resolve nowhere"
        );
    }

    /// A value pass and `why` refuse an empty or unresolvable target with
    /// the message alone, no `#` report line around it.
    ///
    /// # Panics
    ///
    /// When a refusal answers, or carries a report's `#` or newline.
    #[test]
    fn value_passes_refuse_what_names_nothing() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        assert_eq!(
            why_tsv(&p, &a, &o, "nowhere").unwrap_err(),
            "cannot resolve nowhere"
        );
        assert_eq!(
            taint_tsv(&p, &a, &o, "").unwrap_err(),
            "no address or name given"
        );
        assert_eq!(
            layout_tsv(&p, &a, &o, "0x5000").unwrap_err(),
            "no function contains 0x5000"
        );
    }

    /// A spec naming the argument `aN`, as the decompiler does, follows the
    /// register the convention passes it in, and an argument past the
    /// register ones is refused with what to name instead.
    ///
    /// Agents read `a1` in `decompile` and asked `taint/<f>,a1`; the spec
    /// took registers only and refused it.
    ///
    /// # Panics
    ///
    /// When `a1` answers differently from its register, or `a9` is taken.
    #[test]
    fn a_spec_names_an_argument_as_the_decompiler_does() {
        let p = Program::raw_x64(&[0x48, 0x89, 0xc8, 0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let first = format!("{:?}", argument_registers(&p, 0x1000, 64)[0]).to_lowercase();
        assert_eq!(
            taint_tsv(&p, &a, &o, "0x1000,a1"),
            taint_tsv(&p, &a, &o, &format!("0x1000,{first}"))
        );
        let refused = taint_tsv(&p, &a, &o, "0x1000,a9").unwrap_err();
        assert!(
            refused.starts_with("a9 does not arrive in a register"),
            "{refused}"
        );
        let bad = taint_tsv(&p, &a, &o, "0x1000,zz").unwrap_err();
        assert!(bad.contains("or a1, a2, ..."), "{bad}");
    }

    /// A part after the ones a spec takes is refused, where `taint`,
    /// `layout` and `run` dropped it unread and answered another question.
    ///
    /// # Panics
    ///
    /// When the extra part is accepted or refused with another reason.
    #[test]
    fn a_spec_part_too_many_is_refused() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let refusal = "the spec is <address>[,<register>]; 'rdx' is one part too many";
        assert_eq!(
            taint_tsv(&p, &a, &o, "0x1000,rcx,rdx").unwrap_err(),
            refusal
        );
        assert_eq!(
            layout_tsv(&p, &a, &o, "0x1000,rcx,rdx").unwrap_err(),
            refusal
        );
        assert_eq!(
            crate::analysis::render::run_tsv(&p, &a, &o, "0x1000,steps=5,x/1").unwrap_err(),
            "run takes <function>[,steps=N]/<input>[;<input>...]; 'x' is one part too many"
        );
    }
}
