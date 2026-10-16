//! Running code on a probe: argument solving and naming checksums by the values
//! they produce.

use super::*;
use crate::analysis::decompile::decompile_named;
use crate::analysis::decompile::signature::{passing, printed};
use crate::text::{one_line, quoted};

/// Check values a standard checksum produces for the probe string.
///
/// The de-facto check vector for a checksum is `"123456789"`, and every
/// published specification states the value its algorithm returns for it.
/// Matching one turns "a table matching CRC-32C is present" into "this
/// function computes CRC-32C", which is the difference between a lead and a
/// fact.
pub(super) static CHECK_VALUES: &[(&str, u64)] =
    &[("CRC-32", 0xcbf4_3926), ("CRC-32C", 0xe306_9283)];

/// The probe string every entry in [`CHECK_VALUES`] is stated against.
pub(super) const PROBE: &[u8] = b"123456789";

/// Scratch address the probe input is written to, clear of any section and
/// inside the target's address space.
///
/// # Arguments
///
/// * `p` - The loaded image, for its width.
pub(super) fn probe_buf(p: &Program) -> u64 {
    if p.is_64 {
        0x0000_7f00_0000_0000
    } else {
        0x7f00_0000
    }
}

/// Scratch address handed to a receiver-shaped call, clear of the probe.
pub(super) const SCRATCH: u64 = 0x0000_7f00_0001_0000;

/// A value a function compares against, and where it was read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Candidate {
    /// The value tried as the argument.
    pub(super) value: u64,
    /// The instruction that compares against it; `None` for a value tried
    /// on every function.
    pub(super) from: Option<u64>,
}

/// Searches for an argument value that makes a function answer differently.
///
/// A check compares its input against a value the code carries, so the value
/// that satisfies it is already in the function: `cmp eax, 0x1337` names the
/// serial it wants. Trying every constant the function compares against,
/// rather than every 64-bit number, turns an impossible search into a few
/// dozen runs, and running them is what proves which one works instead of
/// arguing from the disassembly. The constants are gathered in the order the
/// function reads them, each with where it was found, so an answer can be
/// traced back to its comparison.
///
/// What comes back is the grouping: the values that produce one answer and
/// the values that produce another, the smallest group first, since a check
/// accepts few inputs and rejects the rest. A single value standing apart
/// from all the others is the one the check is looking for, and the report
/// says which comparison it came from. A flat answer with a pointer argument
/// is explained as such: a constant put in a pointer is read as an address,
/// so the function checks whatever that address holds, which is nothing,
/// and varying the buffer is the useful move.
///
/// This is not a solver. A check that hashes its input before comparing, or
/// derives the expected value at run time, has no constant to harvest and
/// the report says nothing was distinguished rather than inventing a value.
/// When that flat answer is a counted loop leaking a few bits of a product,
/// the report names [`partial_tsv`] instead of asking for another sample.
/// An argument index that cannot be read is refused rather than taken as the
/// first argument, so a caller who asked about `a2` and mistyped it does not
/// read a report about `a1` with nothing to say the question changed; so is
/// one the function's signature does not list ([`beyond_parameters`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - `<address>` or `<address>,<argument index>`; the index counts
///   from one and defaults to the first argument.
///
/// # Returns
///
/// The answers the candidates produced, grouped, with where each candidate
/// value was found.
///
/// # Errors
///
/// When the address does not resolve or is in no function, the argument
/// index does not read or names no parameter, a part follows it (it was
/// dropped unread), or the architecture is not emulated.
pub fn solve_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    /// Candidate values tried, so one function cannot run for ever.
    const CANDIDATES_MAX: usize = 48;
    /// Instructions each run is given.
    const BUDGET: usize = 50_000;
    x86_only(p, "solve")?;
    /// Groups of answers listed before the rest are counted.
    const GROUPS_MAX: usize = 6;
    /// Values spelled per answer before the rest are counted.
    const VALUES_MAX: usize = 8;
    let (where_, mut rest) = spec_head(spec);
    let start = locate(a, o, where_).ok_or_else(|| unresolved(where_))?;
    let named = rest.next().map(str::trim).filter(|t| !t.is_empty());
    let slot = match named {
        None => 0,
        Some(t) => t
            .strip_prefix('a')
            .and_then(|n| n.parse::<usize>().ok())
            .ok_or_else(|| {
                format!(
                    "cannot read the argument {}; use a1, a2, ... counting from one",
                    one_line(t)
                )
            })?
            .checked_sub(1)
            .ok_or_else(|| String::from("arguments count from one; a1 is the first"))?,
    };
    if let Some(extra) = rest.next() {
        return Err(format!(
            "solve takes <address>[,aN]; {} is one part too many",
            quoted(extra.trim())
        ));
    }
    let f = a
        .function_at(start)
        .ok_or_else(|| format!("no function contains {start:#x}"))?;
    let entry = f.entry;
    if named.is_some() {
        beyond_parameters(p, a, o, entry, slot)?;
    }
    let instrs = function_instructions(p, a, entry);
    let candidates = compared_constants(
        &instrs,
        [0, 1, u64::MAX]
            .iter()
            .map(|&value| Candidate { value, from: None })
            .collect(),
        CANDIDATES_MAX,
    );
    let pass = passing(p, a, o, entry);
    let mut answers: BTreeMap<String, Vec<Candidate>> = BTreeMap::new();
    for c in &candidates {
        let mut emu = Emulator::new(p, BUDGET)
            .ok_or_else(|| String::from("this architecture is not emulated yet"))?;
        emu.install_imports();
        emu.set_permissive(true);
        let sp = emu.register("rsp").unwrap_or(0);
        pass.place_arg(&mut emu, sp, slot, c.value);
        let run = emu.run(entry);
        let answer = match run.stop {
            Stop::Returned => {
                format!("returns {:#x}", emu.register("rax").unwrap_or(0))
            }
            other => format!("does not return: {other}"),
        };
        answers.entry(answer).or_default().push(*c);
    }
    let mut out = format!(
        "# argument {} of {}, over {} value(s) the function compares against\n",
        slot + 1,
        short_name(a, o, entry),
        candidates.len()
    );
    if answers.len() <= 1 {
        let same = answers.keys().next().cloned().unwrap_or_default();
        let _ = writeln!(
            out,
            "# every candidate {same}, so none of its own constants decides this"
        );
        if let Some(hint) = partial::partial_hint(p, a, o, entry) {
            let _ = writeln!(out, "# next: {hint}");
        }
        let register = pass.regs.get(slot).map(|r| r.full_register());
        let dereferenced = register.is_some_and(|r| {
            instrs.iter().any(|i| {
                !matches!(i.mnemonic(), Mnemonic::Lea | Mnemonic::Nop)
                    && i.memory_base().full_register() == r
            })
        });
        if dereferenced {
            let _ = writeln!(
                out,
                "# argument {0} is read through, so it is a pointer: a constant in it is an address, not a value. Set up a buffer instead, with emulate {entry:#x},a{0}=<addr>,w<addr>=<bytes>",
                slot + 1
            );
        }
        // The constants the code compares against do not decide the
        // answer, but the arithmetic between the argument and the
        // comparison may: invert it, and run what it states.
        let text = decompile_named(p, a, o, entry);
        if let Some(solved) = text
            .as_ref()
            .and_then(|t| crate::analysis::decompile::interp::Script::read(p, a, o, entry, t).ok())
            .and_then(|s| s.solve_for(slot))
        {
            let (value, line, zero, with) = solved;
            let _ = writeln!(
                out,
                "# chain: a{} = {value:#x} inverts the comparison at line {line} - the run of it {} where zero {}",
                slot + 1,
                with,
                zero
            );
            if let Some(lines) = text
                .as_ref()
                .map(|t| t.lines().nth(line - 1).map(str::to_owned))
            {
                let _ = lines.map(|l| writeln!(out, "# {l}"));
            }
        }
        return Ok(out);
    }
    let mut grouped: Vec<(&String, &Vec<Candidate>)> = answers.iter().collect();
    grouped.sort_by_key(|(_, vs)| vs.len());
    for (answer, values) in grouped.iter().take(GROUPS_MAX) {
        let shown: Vec<String> = values
            .iter()
            .take(VALUES_MAX)
            .map(|c| {
                c.from.map_or_else(
                    || format!("{:#x}", c.value),
                    |from| format!("{:#x} (from {from:#x})", c.value),
                )
            })
            .collect();
        let _ = writeln!(
            out,
            "# {answer}: {}{}",
            shown.join(", "),
            plus_more(values.len(), VALUES_MAX)
        );
    }
    more_line(&mut out, grouped.len(), GROUPS_MAX, "answers not listed");
    Ok(out)
}

/// Gathers the constants a function compares against, in the order it
/// reads them, each with the instruction that compares: what [`solve_tsv`]
/// tries as an argument and [`vectors_tsv`] seeds inputs with.
///
/// The immediates of `cmp`, `test`, `sub`, `xor` and `and`, each value once.
///
/// # Arguments
///
/// * `instrs` - The function's instructions.
/// * `candidates` - Values already gathered; a constant among them is not
///   added again.
/// * `max` - The count past which no further instruction is read.
///
/// # Returns
///
/// `candidates` with the constants after them.
pub(super) fn compared_constants(
    instrs: &[Instruction],
    mut candidates: Vec<Candidate>,
    max: usize,
) -> Vec<Candidate> {
    for i in instrs {
        if !matches!(
            i.mnemonic(),
            Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Sub | Mnemonic::Xor | Mnemonic::And
        ) {
            continue;
        }
        for n in 0..i.op_count() {
            let value = match i.op_kind(n) {
                OpKind::Immediate8 => u64::from(i.immediate8()),
                OpKind::Immediate8to16
                | OpKind::Immediate8to32
                | OpKind::Immediate8to64
                | OpKind::Immediate16
                | OpKind::Immediate32
                | OpKind::Immediate32to64
                | OpKind::Immediate64 => i.immediate(n),
                _ => continue,
            };
            if !candidates.iter().any(|c| c.value == value) {
                candidates.push(Candidate {
                    value,
                    from: Some(i.ip()),
                });
            }
        }
        if candidates.len() >= max {
            break;
        }
    }
    candidates
}

/// Refuses an argument the function's recovered signature does not list.
///
/// `solve 0x401000,a99` ran 48 emulations varying a register no
/// convention passes anything in and reported `argument 99` as if it were
/// one. A signature that does not print, or a variadic one, refuses
/// nothing: the argument may be real where the text cannot say.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `entry` - The function's entry.
/// * `slot` - The argument asked for, from zero.
///
/// # Errors
///
/// When the signature lists fewer arguments than `slot + 1`, naming it.
fn beyond_parameters(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    slot: usize,
) -> Result<(), String> {
    let word = u8::try_from(p.arch.bitness().unwrap_or(64)).unwrap_or(64);
    let Some(sig) = decompile_named(p, a, o, entry).and_then(|t| printed(&t, word).ok()) else {
        return Ok(());
    };
    let count = sig.parameter_kinds().len();
    if slot < count || sig.text.contains("...") {
        return Ok(());
    }
    Err(format!(
        "{} takes {} ({}); a{} is not one of them",
        short_name(a, o, entry),
        match count {
            0 => "no parameters".to_owned(),
            1 => "1 parameter".to_owned(),
            n => format!("{n} parameters"),
        },
        sig.text,
        slot + 1
    ))
}

/// Runs a function on one prepared input and reports what came back.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `entry` - The function to run.
/// * `writes` - Memory to set up first, as `(address, bytes)`.
/// * `args` - Argument values, in convention order.
///
/// # Returns
///
/// The result in `rax` and the machine, so memory can be read back, or
/// `None` when the run did not reach a return.
pub(super) fn run_probe<'p>(
    p: &'p Program,
    entry: u64,
    writes: &[(u64, &[u8])],
    args: &[u64],
) -> Option<(u64, Emulator<'p>)> {
    /// Instructions one probe is given.
    const BUDGET: usize = 100_000;
    let mut emu = Emulator::new(p, BUDGET)?;
    emu.install_imports();
    for (at, bytes) in writes {
        poke_all(&mut emu, *at, bytes);
    }
    for (slot, v) in args.iter().enumerate() {
        emu.set_arg(slot, *v);
    }
    let run = emu.run(entry);
    if !matches!(run.stop, Stop::Returned) {
        return None;
    }
    let rax = emu.register("rax").unwrap_or(0);
    Some((rax, emu))
}

/// Names a library function by what it computes, by running it.
///
/// A statically linked binary has no symbol for `strlen`, and a signature
/// database only recognizes the builds it was made from. Running the
/// function answers the question directly: a routine that returns 9 for a
/// nine-character string, 3 for a three-character one and 0 for an empty one
/// is `strlen`, whatever its bytes look like and whoever compiled it.
///
/// Every answer needs a second probe that a wrong guess would fail, because
/// one matching value is a coincidence: a function returning 9 might be
/// returning its argument's low byte. The pair is what makes this proof by
/// execution rather than a guess. The probes, in order: a length (three
/// strings, three answers, and no argument echoed back); a copy (the
/// destination holds the source, and the length is obeyed); a fill (the
/// byte lands, and only as far as the count says); a comparison (equal is
/// zero, and unequal is not); a number (the digits, not the pointer, and
/// not the first character); and a case change, taking the character by
/// value.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `entry` - The function to identify.
///
/// # Returns
///
/// The name and the evidence for it, or `None` when nothing matched.
pub(super) fn identify_behaviour(p: &Program, entry: u64) -> Option<(&'static str, String)> {
    /// Where a probe's first buffer goes.
    const ONE: u64 = 0x0000_7f00_0002_0000;
    /// Where a probe's second buffer goes.
    const TWO: u64 = 0x0000_7f00_0003_0000;
    let nine: &[u8] = b"123456789\0";
    let three: &[u8] = b"abc\0";
    let empty: &[u8] = b"\0";
    let run = |writes: &[(u64, &[u8])], args: &[u64]| run_probe(p, entry, writes, args);
    let read = |emu: &Emulator<'_>, at: u64, len: u64| -> Vec<u8> {
        (0..len).map(|k| emu.peek(at + k).unwrap_or(0xff)).collect()
    };

    if let Some((a, _)) = run(&[(ONE, nine)], &[ONE])
        && a == 9
        && let Some((b, _)) = run(&[(ONE, three)], &[ONE])
        && b == 3
        && let Some((c, _)) = run(&[(ONE, empty)], &[ONE])
        && c == 0
    {
        return Some((
            "strlen",
            String::from("returns 9, 3 and 0 for strings of those lengths"),
        ));
    }
    if let Some((_, emu)) = run(
        &[(ONE, nine), (TWO, b"\0\0\0\0\0\0\0\0\0\0")],
        &[TWO, ONE, 9],
    ) && read(&emu, TWO, 9) == b"123456789"
        && let Some((_, short)) = run(
            &[(ONE, nine), (TWO, b"\0\0\0\0\0\0\0\0\0\0")],
            &[TWO, ONE, 3],
        )
        && read(&short, TWO, 4) == b"123\0"
    {
        return Some((
            "memcpy",
            String::from("copies the source into the destination, for the length given"),
        ));
    }
    if let Some((_, emu)) = run(&[(ONE, b"\0\0\0\0\0\0\0\0\0\0")], &[ONE, 0x41, 4])
        && read(&emu, ONE, 5) == b"AAAA\0"
    {
        return Some((
            "memset",
            String::from("writes the byte given, exactly as many times as asked"),
        ));
    }
    if let Some((same, _)) = run(&[(ONE, nine), (TWO, nine)], &[ONE, TWO, 9])
        && same == 0
        && let Some((diff, _)) = run(&[(ONE, nine), (TWO, three)], &[ONE, TWO, 9])
        && diff != 0
    {
        return Some((
            "memcmp or strcmp",
            String::from("returns zero for equal buffers and non-zero for different ones"),
        ));
    }
    if let Some((v, _)) = run(&[(ONE, nine)], &[ONE])
        && v == 123_456_789
    {
        return Some((
            "atoi or strtol",
            String::from("returns 123456789 for that string of digits"),
        ));
    }
    if let Some((up, _)) = run(&[], &[u64::from(b'a')])
        && up == u64::from(b'A')
        && let Some((same, _)) = run(&[], &[u64::from(b'A')])
        && same == u64::from(b'A')
    {
        return Some((
            "toupper",
            String::from("maps 'a' to 'A' and leaves 'A' alone"),
        ));
    }
    if let Some((down, _)) = run(&[], &[u64::from(b'A')])
        && down == u64::from(b'a')
        && let Some((same, _)) = run(&[], &[u64::from(b'a')])
        && same == u64::from(b'a')
    {
        return Some((
            "tolower",
            String::from("maps 'A' to 'a' and leaves 'a' alone"),
        ));
    }
    None
}

/// One argument shape that did not reach a return, by its most lenient
/// try: the run with unmapped reads as zero, which goes at least as far as
/// the strict one.
#[derive(Debug, Clone)]
pub(super) struct Attempt {
    /// The shape tried, as [`oracle_tsv`] names it.
    pub(super) shape: &'static str,
    /// How the run ended, and after how many steps.
    pub(super) outcome: String,
}

/// Runs a function on a known input and reports what it returned.
///
/// A constant table says which algorithm a function resembles; running it
/// says which algorithm it is. The function is called as `f(pointer, length)`
/// over the probe string, and the result is matched against the check values
/// the standards publish.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its analysis.
/// * `o` - Names for the report.
/// * `target` - A function entry, an interior address or a name.
///
/// # Returns
///
/// One line naming the call, one naming the result, and the identification
/// when a check value matched.
///
/// # Errors
///
/// When the target is not a discovered function, or the architecture is
/// not emulated.
pub fn oracle_tsv(p: &Program, a: &Analysis, o: &Overlay, target: &str) -> Result<String, String> {
    /// Instructions one run is given.
    const BUDGET: usize = 200_000;
    x86_only(p, "oracle")?;
    /// Argument shapes tried, as `(description, arguments)`.
    ///
    /// A checksum is written `f(buffer, length)` as often as `f(length,
    /// buffer)`, and a method takes a receiver first. Calling one shape only
    /// faults on every function written another way, which says nothing
    /// about the function.
    const SHAPES: &[(&str, &[usize])] = &[
        ("buffer, length", &[0, 1]),
        ("length, buffer", &[1, 0]),
        ("buffer", &[0]),
        ("this, buffer, length", &[2, 0, 1]),
    ];
    let entry = parse_addr(target)
        .and_then(|va| a.function_at(va))
        .or_else(|| {
            a.functions
                .iter()
                .find(|f| name_of(a, o, f.entry) == target)
        })
        .map(|f| f.entry)
        .ok_or_else(|| format!("no discovered function at {}", quoted(target)))?;
    let mut attempts: Vec<Attempt> = Vec::new();
    for (shape, order) in SHAPES {
        for permissive in [false, true] {
            let mut emu = Emulator::new(p, BUDGET)
                .ok_or_else(|| String::from("this architecture is not emulated yet"))?;
            emu.install_imports();
            emu.set_permissive(permissive);
            poke_all(&mut emu, probe_buf(p), PROBE);
            let values = [probe_buf(p), from_usize(PROBE.len()), SCRATCH];
            for (slot, which) in order.iter().enumerate() {
                emu.set_arg(slot, values[*which]);
            }
            let run = emu.run(entry);
            let rax = emu.register("rax").unwrap_or(0);
            let returned = matches!(run.stop, Stop::Returned);
            if permissive {
                attempts.push(Attempt {
                    shape,
                    outcome: format!("{} after {} steps", run.stop, run.steps),
                });
            }
            if returned {
                let low = rax & 0xffff_ffff;
                let mut out = format!(
                    "# ran {}({shape}) over \"{}\"{}: returned after {} steps\n",
                    name_of(a, o, entry),
                    String::from_utf8_lossy(PROBE),
                    if permissive {
                        ", unmapped reads as zero"
                    } else {
                        ""
                    },
                    run.steps
                );
                let _ = writeln!(out, "# rax {rax:#x}   eax {low:#x}");
                if let Some((what, evidence)) = identify_behaviour(p, entry) {
                    let _ = writeln!(out, "# it is {what}: {evidence}");
                }
                match CHECK_VALUES.iter().find(|(_, v)| *v == low || *v == rax) {
                    Some((name, _)) => {
                        let _ = writeln!(
                            out,
                            "# {name} confirmed: it returns the published check value"
                        );
                    }
                    None => out.push_str(
                        "# no published check value matched; the result is the function's own\n",
                    ),
                }
                return Ok(out);
            }
        }
    }
    let mut out = format!(
        "# {} did not run to a return over \"{}\" in any argument shape\n",
        name_of(a, o, entry),
        String::from_utf8_lossy(PROBE)
    );
    out.push_str("# shape                 outcome\n");
    for attempt in &attempts {
        let _ = writeln!(out, "{:<22} {}", attempt.shape, attempt.outcome);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{oracle_tsv, solve_tsv};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::Program;

    /// A solve or an oracle run refuses a target or an argument it cannot
    /// read, with the message alone.
    ///
    /// # Panics
    ///
    /// When a refusal answers, or says something else.
    #[test]
    fn running_refuses_what_it_cannot_read() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        for (spec, message) in [
            ("nowhere", "cannot resolve nowhere"),
            (
                "0x1000,ax",
                "cannot read the argument ax; use a1, a2, ... counting from one",
            ),
            ("0x1000,a0", "arguments count from one; a1 is the first"),
            (
                "0x1000,aaa2",
                "cannot read the argument aaa2; use a1, a2, ... counting from one",
            ),
            ("0x5000", "no function contains 0x5000"),
            (
                "0x1000,a1,a2",
                "solve takes <address>[,aN]; 'a2' is one part too many",
            ),
        ] {
            assert_eq!(solve_tsv(&p, &a, &o, spec).unwrap_err(), message, "{spec}");
        }
        assert_eq!(
            oracle_tsv(&p, &a, &o, "").unwrap_err(),
            "no discovered function at ''"
        );
    }

    /// A refusal quotes the caller's text cut to one row: every spec
    /// renderer echoed a 30 KB spec whole in its error.
    ///
    /// # Panics
    ///
    /// When a refusal runs past a row.
    #[test]
    fn a_refusal_quotes_a_long_spec_cut_short() {
        use crate::analysis::render::{
            devirtualize_tsv, emulate_tsv, run_tsv, taint_tsv, unpack_tsv, vm_dispatch_tsv,
        };
        /// Longest refusal a row of quoted text makes.
        const ROW: usize = 600;
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let long = "A".repeat(30_000);
        let specs = [
            long.clone(),
            format!("0x1000,{long}"),
            format!("0x1000,steps={long}"),
            format!("0x1000,{long}=1"),
            format!("0x1000/{long}"),
            format!("0x1000,budget={long}"),
        ];
        type Renderer = fn(&Program, &Analysis, &Overlay, &str) -> Result<String, String>;
        let renderers: [(&str, Renderer); 8] = [
            ("solve", solve_tsv),
            ("oracle", oracle_tsv),
            ("emulate", emulate_tsv),
            ("run", run_tsv),
            ("taint", taint_tsv),
            ("devirt", devirtualize_tsv),
            ("unpack", unpack_tsv),
            ("vm", vm_dispatch_tsv),
        ];
        for (name, render) in renderers {
            for spec in &specs {
                if let Err(why) = render(&p, &a, &o, spec) {
                    assert!(
                        why.len() < ROW,
                        "{name}: {} bytes: {}",
                        why.len(),
                        &why[..80]
                    );
                }
            }
        }
    }

    /// A solve refuses an argument the function's signature does not list,
    /// naming the signature, and answers one it lists.
    ///
    /// `a99` ran every candidate through a register nothing passes and
    /// reported `argument 99` as an answer.
    ///
    /// # Panics
    ///
    /// When an argument past the signature answers, or one in it is refused.
    #[test]
    fn solve_refuses_an_argument_the_signature_does_not_list() {
        let o = Overlay::default();
        let read = Program::raw_x64(&[
            0x8b, 0x01, // ASM: mov eax,[rcx]
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&read);
        let refused = solve_tsv(&read, &a, &o, "0x1000,a99").unwrap_err();
        assert!(
            refused.starts_with("sub_1000 takes 1 parameter (")
                && refused.ends_with("); a99 is not one of them"),
            "{refused}"
        );
        assert!(solve_tsv(&read, &a, &o, "0x1000,a1").is_ok());
    }

    /// A flat solve calls an argument a pointer only when read through.
    ///
    /// Something must load or store through it, not a `lea` compute from it,
    /// and the hint names the argument as `emulate` reads it, from one; the
    /// hint said `a0=`, which `emulate` refuses, and any `lea` made a pointer.
    ///
    /// # Panics
    ///
    /// When a `lea` makes a pointer, a load does not, or the hint is
    /// zero-based.
    #[test]
    fn a_flat_solve_calls_an_argument_a_pointer_only_when_read_through() {
        let o = Overlay::default();
        let read = Program::raw_x64(&[
            0x8b, 0x01, // ASM: mov eax,[rcx]
            0xc3, // ASM: ret
        ]);
        let out = solve_tsv(&read, &Analysis::compute(&read), &o, "0x1000").unwrap();
        assert!(out.contains("argument 1 is read through"), "{out}");
        assert!(out.contains("emulate 0x1000,a1=<addr>,"), "{out}");
        let computed = Program::raw_x64(&[
            0x48, 0x8d, 0x41, 0x08, // ASM: lea rax,[rcx+8]
            0x31, 0xc0, // ASM: xor eax,eax
            0xc3, // ASM: ret
        ]);
        let out = solve_tsv(&computed, &Analysis::compute(&computed), &o, "0x1000").unwrap();
        assert!(out.contains("every candidate returns 0x0"), "{out}");
        assert!(!out.contains("read through"), "{out}");
    }
}
