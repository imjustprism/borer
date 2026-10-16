//! Obfuscated control flow and data: flattened dispatchers, VM handler tables
//! and stack-built strings.

use super::*;

/// Fewest cases a switch needs before it reads as a flattening dispatcher.
pub(super) const FLAT_MIN_CASES: usize = 6;

/// One flattening dispatcher: a switch most of whose cases come back to it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Dispatcher {
    /// The indirect jump through the case table.
    pub(super) site: u64,
    /// Start of the block holding the dispatch, which is where a case has
    /// to come back to.
    pub(super) head: u64,
    /// Entry of the function it is in.
    pub(super) entry: u64,
    /// How many cases the table holds.
    pub(super) cases: usize,
    /// How many of them return to the dispatch.
    pub(super) back: usize,
}

/// Finds the functions whose control flow has been flattened.
///
/// Flattening rewrites a function as one loop around a switch: every basic
/// block becomes a case, the block order is destroyed, and a state variable
/// says which case runs next. The shape is the same one a virtual machine's
/// dispatch has, except the jump goes through a resolved table rather than a
/// register, so the blocks look like ordinary code and only their
/// arrangement is wrong.
///
/// The test is the one that separates a dispatcher from a `switch`: most of
/// the cases must come back to the dispatch. An ordinary switch's arms leave
/// the function or fall through to the code after it.
///
/// Knowing a function is flattened changes how its output should be read:
/// the cases are in table order, which is not execution order, and the
/// variable the switch reads is the program counter of the original. Running
/// the function is what recovers the order ([`dispatch_order`]): each trip
/// through the dispatch is one original block, in the sequence the program
/// actually takes them, so a described dispatcher ends with the order one
/// run took.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: functions, blocks and resolved jump tables.
/// * `o` - User names.
/// * `filter` - Empty for every flattened function, or an address or name
///   to describe that one.
///
/// # Returns
///
/// One row per dispatcher with its case count and how many return to it, or
/// the case list for a single dispatcher.
///
/// # Errors
///
/// When the filter names nothing, or no dispatcher is at or in what it
/// names; a filter that resolved to nothing listed every dispatcher, an
/// answer to a question nobody asked.
pub fn flattening_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    filter: &str,
) -> Result<String, String> {
    /// Cases listed when describing one dispatcher.
    const CASES_MAX: usize = 256;
    /// Dispatchers listed when describing them all.
    const DISPATCHERS_MAX: usize = 400;
    /// Steps of the recovered order shown before the rest are counted.
    const ORDER_MAX: usize = 64;
    let filter = filter.trim();
    let wanted = if filter.is_empty() {
        None
    } else {
        Some(locate(a, o, filter).ok_or_else(|| unresolved(filter))?)
    };
    let mut found: Vec<Dispatcher> = a
        .jump_tables
        .iter()
        .filter_map(|(site, cases)| flattened(a, *site, cases))
        .collect();
    found.sort_by(|l, r| r.cases.cmp(&l.cases).then(l.site.cmp(&r.site)));
    let Some(target) = wanted else {
        if found.is_empty() {
            return Ok(String::from(
                "# no flattened control flow: no switch whose cases mostly return to it\n",
            ));
        }
        let mut out = format!(
            "# {} flattened function{}; borer://flat/<address> for the cases\n",
            found.len(),
            plural(found.len())
        );
        out.push_str("# dispatch      cases  return  function\n");
        for d in found.iter().take(DISPATCHERS_MAX) {
            let _ = writeln!(
                out,
                "{:<#14x} {:<6} {:<7} {}",
                d.site,
                d.cases,
                d.back,
                short_name(a, o, d.entry)
            );
        }
        more_line(
            &mut out,
            found.len(),
            DISPATCHERS_MAX,
            "dispatchers not listed",
        );
        return Ok(out);
    };
    let &Dispatcher {
        site,
        head,
        entry,
        cases,
        back,
    } = found
        .iter()
        .find(|d| d.site == target || d.entry == target)
        .ok_or_else(|| format!("no flattening dispatch at or in {target:#x}"))?;
    let empty: Vec<u64> = Vec::new();
    let targets = a.jump_tables.get(&site).unwrap_or(&empty);
    let mut out = format!(
        "# {}: {cases} cases through the dispatch at {site:#x}, {back} of them return to it\n",
        short_name(a, o, entry)
    );
    out.push_str(
        "# the cases are in table order, which is not the order they run: the switch reads the\n\
         # original program counter, so the block order of this function carries no meaning\n",
    );
    out.push_str("# case  block          instructions  ends\n");
    let Some(f) = a.function(entry) else {
        return Ok(out);
    };
    for (n, t) in targets.iter().enumerate().take(CASES_MAX) {
        let block = f.blocks.iter().find(|b| b.start == *t);
        let instrs = block.map_or(0, |b| {
            let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(0);
            p.read_va_upto(b.start, len.max(1)).map_or(0, |code| {
                if p.arch.isa() == Some(crate::isa::Isa::A64) {
                    disasm::disassemble_isa(code, b.start, crate::isa::Isa::A64, 64).len()
                } else {
                    disasm::disassemble(code, b.start, 64, 64).len()
                }
            })
        });
        let ends = block.map_or("unknown", |b| match b.term {
            BlockTerm::Ret => "returns",
            BlockTerm::Invalid => "bad code",
            BlockTerm::Jmp
            | BlockTerm::Cond
            | BlockTerm::Call
            | BlockTerm::Indirect
            | BlockTerm::Fall
                if *t == head || reaches(f, *t, head) =>
            {
                "back to the dispatch"
            }
            BlockTerm::Indirect => "another indirect jump",
            BlockTerm::Jmp | BlockTerm::Cond | BlockTerm::Call | BlockTerm::Fall => "elsewhere",
        });
        let _ = writeln!(out, "{n:<6} {t:<#14x} {instrs:<13} {ends}");
    }
    more_line(&mut out, targets.len(), CASES_MAX, "cases not listed");
    if let Some((order, why)) = dispatch_order(p, entry, site) {
        if order.is_empty() {
            let _ = writeln!(
                out,
                "# running it never reached the dispatch: the run ended {why}"
            );
            out.push_str(
                "# it needs state nothing set; emulate <entry>,aN=<addr>,w<addr>=<bytes> builds it\n",
            );
        } else {
            let shown: Vec<String> = order
                .iter()
                .take(ORDER_MAX)
                .map(|t| {
                    targets
                        .iter()
                        .position(|c| c == t)
                        .map_or_else(|| format!("{t:#x}"), |n| format!("case {n}"))
                })
                .collect();
            let _ = writeln!(
                out,
                "# the order one run took, which is the original block order for that input:\n#   {}{}",
                shown.join(" -> "),
                plus_more(order.len(), ORDER_MAX)
            );
        }
    }
    Ok(out)
}

/// Judges one resolved jump table as [`flattening_tsv`] does: a switch of
/// at least [`FLAT_MIN_CASES`] cases most of which come back to it.
///
/// # Arguments
///
/// * `a` - The analysis: functions and blocks.
/// * `site` - The indirect jump through the table.
/// * `cases` - The table's targets.
///
/// # Returns
///
/// The dispatcher, or `None` when the switch is not one.
pub(super) fn flattened(a: &Analysis, site: u64, cases: &[u64]) -> Option<Dispatcher> {
    if cases.len() < FLAT_MIN_CASES {
        return None;
    }
    let f = a.function_at(site)?;
    let head = f
        .blocks
        .iter()
        .find(|b| b.start <= site && site < b.end)?
        .start;
    let back = cases
        .iter()
        .filter(|t| **t != head && reaches(f, **t, head))
        .count();
    (back * 2 > cases.len()).then_some(Dispatcher {
        site,
        head,
        entry: f.entry,
        cases: cases.len(),
        back,
    })
}

/// Runs a flattened function and records the cases its dispatch took.
///
/// Flattening destroys the block order and keeps the program counter in a
/// variable, so the order cannot be read off the code. It can be watched:
/// every trip through the dispatch is one original block, and the sequence
/// of them is the order the program runs for that input.
///
/// A function reached with nothing in its arguments takes the path for a
/// null pointer, which is usually an immediate return, so the run is tried
/// over several argument shapes, handing it a buffer the way the oracle
/// does, and the longest path any shape reaches is the one reported: it is
/// the most of the function that was seen. The dispatch is what is being
/// watched, not the memory, so an unknown read answers zero rather than
/// ending the run.
///
/// One run is one path, which is what this claims and no more. A different
/// argument takes a different path, and `emulate` sets arguments before a
/// run.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `entry` - The flattened function.
/// * `site` - Its dispatch, whose jumps are the ones that count.
///
/// # Returns
///
/// The case targets in the order they ran and how the run ended, or `None`
/// when the architecture is not emulated.
pub(super) fn dispatch_order(p: &Program, entry: u64, site: u64) -> Option<(Vec<u64>, String)> {
    /// Instructions the run is given.
    const BUDGET: usize = 2_000_000;
    let probe_len = from_usize(PROBE.len());
    let shapes: [&[u64]; 3] = [
        &[],
        &[probe_buf(p), probe_len],
        &[probe_buf(p), probe_buf(p), probe_len, probe_len],
    ];
    let mut best: Vec<u64> = Vec::new();
    let mut why = String::from("no run was made");
    for args in shapes {
        let mut emu = Emulator::new(p, BUDGET)?;
        emu.install_imports();
        emu.set_permissive(true);
        poke_all(&mut emu, probe_buf(p), PROBE);
        for (slot, v) in args.iter().enumerate() {
            emu.set_arg(slot, *v);
        }
        let run = emu.run(entry);
        let order: Vec<u64> = emu
            .indirect_jumps()
            .iter()
            .filter(|(from, _)| *from == site)
            .map(|(_, to)| *to)
            .collect();
        if order.len() > best.len() || best.is_empty() {
            why = format!("{} after {} steps", run.stop, run.steps);
            best = order;
        }
    }
    Some((best, why))
}

/// Fewest table targets before an indirect jump reads as a dispatcher
/// rather than a `switch`.
pub(super) const VM_MIN_HANDLERS: usize = 12;

/// Fewest targets a dispatch that fetches its index from memory needs:
/// below this a two-way branch is not a machine, fetched or not.
pub(super) const VM_MIN_FETCHED: usize = 3;

/// Most handlers described in one read.
pub(super) const VM_HANDLERS_MAX: usize = 400;

/// Instructions read from a handler before it is summarized.
pub(super) const HANDLER_INSTRS: usize = 24;

/// One interpreter dispatch loop: an indirect jump through a handler table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct DispatchLoop {
    /// The indirect jump.
    pub(super) site: u64,
    /// Entry of the function holding it.
    pub(super) entry: u64,
    /// The distinct handlers the table points at, in table order.
    pub(super) handlers: Vec<u64>,
    /// How many of them lead back to the jump.
    pub(super) back: usize,
}

/// Finds the program's dispatch loops, as [`vm_dispatch_tsv`] judges them.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading a dispatch's block.
/// * `a` - The analysis: functions, blocks and resolved jump tables.
///
/// # Returns
///
/// The loops, the most handlers first, then by site.
pub(super) fn dispatch_loops(p: &Program, a: &Analysis) -> Vec<DispatchLoop> {
    let mut found: Vec<DispatchLoop> = a
        .functions
        .iter()
        .flat_map(|f| dispatch_loops_in(p, a, f))
        .collect();
    found.sort_by_key(|d| (std::cmp::Reverse(d.handlers.len()), d.site));
    found
}

/// Finds the dispatch loops of one function, as [`dispatch_loops`] judges
/// them, in block order.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading a dispatch's block.
/// * `a` - The analysis: blocks and resolved jump tables.
/// * `f` - The function.
///
/// # Returns
///
/// Its loops, none for an ordinary function.
pub(super) fn dispatch_loops_in(p: &Program, a: &Analysis, f: &Function) -> Vec<DispatchLoop> {
    let bits = p.arch.bitness();
    let mut found: Vec<DispatchLoop> = Vec::new();
    for b in &f.blocks {
        if b.term != BlockTerm::Indirect {
            continue;
        }
        let Some((site, targets)) = a.jump_tables.range(b.start..b.end).next() else {
            continue;
        };
        let mut seen: BTreeSet<u64> = BTreeSet::new();
        let handlers: Vec<u64> = targets
            .iter()
            .copied()
            .filter(|t| seen.insert(*t))
            .collect();
        if handlers.len() < VM_MIN_FETCHED {
            continue;
        }
        let back = handlers.iter().filter(|t| reaches(f, **t, b.start)).count();
        if back * 2 < handlers.len() {
            continue;
        }
        if handlers.len() < VM_MIN_HANDLERS
            && !bits.is_some_and(|bits| fetches_index_from_memory(p, f, b, bits))
        {
            continue;
        }
        found.push(DispatchLoop {
            site: *site,
            entry: f.entry,
            handlers,
            back,
        });
    }
    found
}

/// Finds the dispatch loops in the program, or describes one of them.
///
/// An interpreter runs one loop: fetch the next operation, jump through a
/// table to the code for it, and come back. That shape is what a virtualizing
/// protector leaves behind, and it is what tells a reader that a function is
/// no longer the code that was written but a program for a machine hidden
/// inside it. A dispatch is an indirect jump with a table of at least
/// [`VM_MIN_HANDLERS`] targets where most of those targets lead back to the
/// jump itself; a `switch` in ordinary code fails that test, since its arms
/// leave. A smaller table is still a dispatch when the block fetches its
/// index from memory ([`fetches_index_from_memory`]): a hand-written
/// interpreter of a dozen opcodes jumps through five or six targets it
/// reads out of its program, where an ordinary small `switch` indexes a
/// value it computed.
///
/// # Arguments
///
/// * `p` - The loaded image, for reading the handlers.
/// * `a` - The analysis: functions, blocks and resolved jump tables.
/// * `o` - User names.
/// * `filter` - Empty for the list of dispatches, or a dispatch address, or
///   the address or name of the function holding one, to describe its
///   handlers.
///
/// # Returns
///
/// The listing as text.
///
/// # Errors
///
/// When the filter names nothing, or no dispatch loop is at what it names;
/// a filter that did not read as an address listed every loop, an answer
/// to a question nobody asked.
pub fn vm_dispatch_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    filter: &str,
) -> Result<String, String> {
    let filter = filter.trim();
    let wanted = if filter.is_empty() {
        None
    } else {
        Some(locate(a, o, filter).ok_or_else(|| unresolved(filter))?)
    };
    let found = dispatch_loops(p, a);
    let Some(want) = wanted else {
        let mut out = format!(
            "# {} dispatch loop{} found; borer://vm/<address> for the handlers\n",
            found.len(),
            plural(found.len())
        );
        out.push_str("# site          handlers  return  function\n");
        for d in found.iter().take(VM_HANDLERS_MAX) {
            let _ = writeln!(
                out,
                "{:<#13x} {:>8}  {:>6}  {}",
                d.site,
                d.handlers.len(),
                d.back,
                name_of(a, o, d.entry)
            );
        }
        more_line(
            &mut out,
            found.len(),
            VM_HANDLERS_MAX,
            "dispatch loops not listed",
        );
        return Ok(out);
    };
    let d = found
        .iter()
        .find(|d| d.site == want || d.entry == want)
        .ok_or_else(|| format!("no dispatch loop at {}", crate::text::one_line(filter)))?;
    let mut out = format!(
        "# {} handlers of the dispatch at {:#x} in {}, {} of them return to it\n",
        d.handlers.len(),
        d.site,
        name_of(a, o, d.entry),
        d.back
    );
    if let Some(f) = a.function(d.entry)
        && let Some(vip) = virtual_pointer(p, f)
    {
        match vip.stored {
            Some((at, set)) => {
                let _ = writeln!(
                    out,
                    "# operations are read through {}, pointed at {at:#x} by {set:#x}",
                    vip.register
                );
            }
            None => {
                let _ = writeln!(
                    out,
                    "# operations are read through {}; where it is pointed is not a fixed address",
                    vip.register
                );
            }
        }
    }
    out.push_str("# index  handler        instrs  effect\n");
    for (i, h) in d.handlers.iter().enumerate().take(VM_HANDLERS_MAX) {
        let (n, effect) = handler_effect(p, a, *h);
        let _ = writeln!(out, "{i:>6}  {h:<#13x} {n:>6}  {effect}");
    }
    more_line(
        &mut out,
        d.handlers.len(),
        VM_HANDLERS_MAX,
        "handlers not listed",
    );
    let (_, _, hint) = constraint_shape(p, a, d);
    out.push_str(&hint);
    out.push_str(&decode_shape(p, a, d));
    Ok(out)
}

/// Reports the algebraic shape a dispatch loop's handler set forms.
///
/// A crackme's virtual machine often implements its check as conditional
/// arithmetic: an add or xor that only fires when a data bit tests true
/// creates one unknown bit per handler. Enough of these on a bounded state
/// form a linear relation system a lattice-reduction solver (LLL, BKZ)
/// cracks in seconds, where inverting the virtual cipher round by round
/// is exponential. A modular-exponentiation shape points at index
/// calculus instead. The hint names the shape so the analyst reaches for
/// the right tool, and counts the constraints so the difficulty is
/// visible before any are solved.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `d` - The dispatch loop.
///
/// # Returns
///
/// `(conditional operations, arithmetic operations, the hint line)`.
fn constraint_shape(p: &Program, a: &Analysis, d: &DispatchLoop) -> (usize, usize, String) {
    /// Fewest conditional operations before the hint fires.
    const LATTICE_MIN: usize = 8;
    let mut conditional = 0usize;
    let mut arithmetic = 0usize;
    let mut modular = 0usize;
    for &h in &d.handlers {
        let (_, effect) = handler_effect(p, a, h);
        let low = effect.to_lowercase();
        if low.contains("div") || low.contains("mod") {
            modular += 1;
        }
        if low.contains("add") || low.contains("sub") || low.contains("mul") {
            arithmetic += 1;
        }
        if (low.contains("test") || low.contains("cmp") || low.contains("je"))
            && (low.contains("add")
                || low.contains("sub")
                || low.contains("xor")
                || low.contains("or")
                || low.contains("mul"))
        {
            conditional += 1;
        }
    }
    let hint = if conditional >= LATTICE_MIN && arithmetic >= LATTICE_MIN {
        format!(
            "# constraint shape: {conditional} conditional and {arithmetic} arithmetic operations on a bounded state; lattice reduction (LLL or BKZ) applies, each conditional contributing one unknown bit
"
        )
    } else if modular >= 3 && arithmetic >= LATTICE_MIN {
        format!(
            "# constraint shape: {modular} modular and {arithmetic} arithmetic operations; a discrete-log or modular-equation shape, index calculus applies
"
        )
    } else if conditional > 0 {
        format!(
            "# constraint shape: {conditional} conditional operation{} — too few for a lattice hint
",
            plural(conditional)
        )
    } else {
        String::new()
    };
    (conditional, arithmetic, hint)
}

/// Most blocks read back from a dispatch site before the decode shape is
/// given up on.
pub(super) const DECODE_BLOCKS_MAX: usize = 16;

/// Most instructions in those blocks before the decode shape is given up on.
pub(super) const DECODE_INSTRS_MAX: usize = 128;

/// Fewest operand loads through one base register that count as the fetch.
pub(super) const DECODE_FETCH_MIN: usize = 2;

/// Instructions searched after a call for the key rebuild it starts.
pub(super) const DECODE_ADVANCE_WINDOW: usize = 6;

/// The 64-bit register a name spells, or `None` when it is not one.
///
/// A fetch reads its fields into partial registers (`edx`, `r9d`, `al`) and
/// the instructions around it mix whole and partial names of the same
/// storage (`xor rcx,rbx` one line, `xor al,bh` the next), so every operand
/// is compared by the full register it names.
///
/// # Arguments
///
/// * `reg` - An operand as the disassembly spells it.
///
/// # Returns
///
/// The 64-bit register it names, or `None` for memory, immediates and names
/// outside the general-purpose set.
fn wide(reg: &str) -> Option<&'static str> {
    const PAIRS: [(&str, &str); 36] = [
        ("rax", "rax"),
        ("eax", "rax"),
        ("ax", "rax"),
        ("al", "rax"),
        ("ah", "rax"),
        ("rbx", "rbx"),
        ("ebx", "rbx"),
        ("bx", "rbx"),
        ("bl", "rbx"),
        ("bh", "rbx"),
        ("rcx", "rcx"),
        ("ecx", "rcx"),
        ("cx", "rcx"),
        ("cl", "rcx"),
        ("ch", "rcx"),
        ("rdx", "rdx"),
        ("edx", "rdx"),
        ("dx", "rdx"),
        ("dl", "rdx"),
        ("dh", "rdx"),
        ("rsi", "rsi"),
        ("esi", "rsi"),
        ("si", "rsi"),
        ("sil", "rsi"),
        ("rdi", "rdi"),
        ("edi", "rdi"),
        ("di", "rdi"),
        ("dil", "rdi"),
        ("rbp", "rbp"),
        ("ebp", "rbp"),
        ("bp", "rbp"),
        ("bpl", "rbp"),
        ("rsp", "rsp"),
        ("esp", "rsp"),
        ("sp", "rsp"),
        ("spl", "rsp"),
    ];
    if let Some(found) = PAIRS.iter().find(|(n, _)| *n == reg) {
        return Some(found.1);
    }
    let stripped = reg.strip_prefix('r')?;
    let num = if let Ok(num) = stripped.parse::<usize>() {
        num
    } else {
        stripped[..stripped.len().saturating_sub(1)].parse().ok()?
    };
    if !(8..=15).contains(&num) {
        return None;
    }
    let names = ["r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"];
    names.get(num - 8).copied()
}

/// Reports how a dispatch loop decodes the operations it fetches.
///
/// A plain interpreter reads `op|dst|src|imm` out of its program and jumps.
/// A harder machine xors what it fetched with a key register before the
/// jump, and the hardest rebuilds that key every step out of the machine's
/// own state — a mixer call whose result is xored with a register-file slot
/// and written back. Then the bytecode on disk is noise for every run but
/// the one that produced it: the program only decodes correctly while the
/// machine is doing what the author intended, which makes the decode itself
/// the check (the "quine lock" of `VoidVault v7.1`, whose passphrase bytes
/// are the decryption key of its own program). That shape is never solved
/// statically — it is solved per input step, with derailment as the oracle.
///
/// The two facts are read apart, and only their combination says the hard
/// thing: an xor before the dispatch with no rebuild is a fixed key, found
/// once and then decoded like any other encrypted bytecode.
///
/// The search walks the blocks that reach the dispatch site backwards, so
/// a fetch and a mix split across blocks are still seen together, and stops
/// at handler entries: a handler's body is the operation, not the fetch.
/// One shared tail that every handler jumps back to is also a handler entry
/// and still lands in the window when the loop's back edge comes from it —
/// which is where this machine keeps its key rebuild.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `d` - The dispatch loop.
///
/// # Returns
///
/// The hint lines, empty when the fetch is plain.
fn decode_shape(p: &Program, a: &Analysis, d: &DispatchLoop) -> String {
    let Some(f) = a.function(d.entry) else {
        return String::new();
    };
    let Some(bitness) = p.arch.bitness() else {
        return String::new();
    };
    let mut preds: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for b in &f.blocks {
        for &s in &b.successors {
            preds.entry(s).or_default().push(b.start);
        }
        if b.term == BlockTerm::Call && f.blocks.iter().any(|x| x.start == b.end) {
            preds.entry(b.end).or_default().push(b.start);
        }
    }
    let handlers: BTreeSet<u64> = d.handlers.iter().copied().collect();
    let Some(site) = f
        .blocks
        .iter()
        .find(|b| d.site >= b.start && d.site < b.end)
    else {
        return String::new();
    };
    let mut window: BTreeSet<u64> = BTreeSet::new();
    let mut queue: std::collections::VecDeque<u64> = std::collections::VecDeque::from([site.start]);
    let mut instrs = 0usize;
    let mut walked = 0usize;
    while let Some(start) = queue.pop_front() {
        if !window.insert(start) {
            continue;
        }
        let Some(b) = f.blocks.iter().find(|b| b.start == start) else {
            continue;
        };
        let len = usize::try_from(b.end - b.start).unwrap_or(0);
        instrs += len / 4 + 1;
        if handlers.contains(&start) {
            continue;
        }
        walked += 1;
        if walked >= DECODE_BLOCKS_MAX || instrs > DECODE_INSTRS_MAX {
            break;
        }
        if let Some(up) = preds.get(&start) {
            queue.extend(up.iter().copied());
        }
    }
    let mut lines: Vec<disasm::DisasmLine> = Vec::new();
    for &start in &window {
        let Some(b) = f.blocks.iter().find(|b| b.start == start) else {
            continue;
        };
        let len = usize::try_from(b.end - b.start).unwrap_or(0);
        if let Some(code) = p.read_va(start, len) {
            lines.extend(disasm::disassemble(code, start, bitness, HANDLER_INSTRS));
        }
    }
    let mut fields: Vec<&'static str> = Vec::new();
    let mut bases: Vec<&'static str> = Vec::new();
    let mut loads: Vec<(String, String)> = Vec::new();
    for l in &lines {
        let text = l.text.as_str();
        let Some((mnemonic, operands)) = text.split_once(char::is_whitespace) else {
            continue;
        };
        let Some((dst, src)) = operands.split_once(',') else {
            continue;
        };
        let fetched = matches!(mnemonic, "movzx" | "movsx") && src.contains("byte [")
            || mnemonic == "mov" && src.starts_with('[');
        if !fetched {
            continue;
        }
        let Some(open) = src.find('[') else {
            continue;
        };
        let Some(close) = src[open..].find(']') else {
            continue;
        };
        let inside = &src[open + 1..open + close];
        let parts: Vec<&str> = inside.split(['+', '-']).filter(|p| !p.is_empty()).collect();
        if parts.len() > 2 {
            continue;
        }
        let small = match parts.as_slice() {
            [_] => true,
            [_, disp] => disp
                .strip_suffix('h')
                .unwrap_or(disp)
                .parse::<u16>()
                .is_ok_and(|d| d <= 0xF),
            _ => false,
        };
        let Some(base) = parts.iter().find(|p| wide(p).is_some()).copied() else {
            continue;
        };
        if !small {
            continue;
        }
        loads.push((dst.trim().to_owned(), base.trim().to_owned()));
    }
    for base in loads.iter().map(|(_, b)| b).collect::<BTreeSet<_>>() {
        let group: Vec<&(String, String)> = loads.iter().filter(|(_, b)| b == base).collect();
        if group.len() < DECODE_FETCH_MIN {
            continue;
        }
        let Some(wide_base) = wide(base) else {
            continue;
        };
        bases.push(wide_base);
        for (dst, _) in group {
            if let Some(w) = wide(dst) {
                fields.push(w);
            }
        }
    }
    if fields.is_empty() {
        return String::new();
    }
    let mut partners: BTreeSet<&'static str> = BTreeSet::new();
    for l in &lines {
        let text = l.text.as_str();
        let Some(("xor", operands)) = text.split_once(char::is_whitespace) else {
            continue;
        };
        let Some((a, b)) = operands.split_once(',') else {
            continue;
        };
        let (Some(a), Some(b)) = (wide(a.trim()), wide(b.trim())) else {
            continue;
        };
        let field_a = fields.contains(&a);
        let field_b = fields.contains(&b);
        if field_a == field_b {
            continue;
        }
        let other = if field_a { b } else { a };
        if bases.contains(&other) {
            continue;
        }
        partners.insert(other);
    }
    if partners.is_empty() {
        return String::new();
    }
    for (i, l) in lines.iter().enumerate() {
        if !l.text.starts_with("call ") {
            continue;
        }
        let mixer = l
            .text
            .strip_prefix("call ")
            .and_then(|t| t.trim().strip_suffix('h'))
            .and_then(|t| u64::from_str_radix(t, 16).ok())
            .unwrap_or(l.va);
        for j in i + 1..(i + DECODE_ADVANCE_WINDOW).min(lines.len()) {
            if !lines[j].text.starts_with("xor rax,[") {
                continue;
            }
            for after in lines.iter().take((j + 3).min(lines.len())).skip(j + 1) {
                let text = after.text.as_str();
                let Some(("mov", operands)) = text.split_once(char::is_whitespace) else {
                    continue;
                };
                let Some((dst, src)) = operands.split_once(',') else {
                    continue;
                };
                if src.trim() != "rax" {
                    continue;
                }
                if let Some(w) = wide(dst.trim())
                    && partners.contains(w)
                {
                    return format!(
                        "# decode shape: running-key fetch — the operands are xored with {w} before the dispatch, and every step rebuilds {w} from the mixer at {mixer:#x} xored with the register file, so the program reads correctly only on the run that produced it: the decode is the check, solve per input step with derailment as the oracle\n"
                    );
                }
            }
        }
    }
    let keys = partners.iter().copied().collect::<Vec<_>>().join("/");
    format!(
        "# decode shape: the fetched operands are xored with {keys} before the dispatch — the bytecode is stored encrypted; recover the key to read it statically\n"
    )
}

/// The address a `lea` or `mov` reads from, when it is a fixed one.
///
/// A rip-relative operand names an address the text prints only as an
/// offset, so the instruction is decoded and its target computed rather than
/// read from the rendering.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `va` - The instruction's address.
///
/// # Returns
///
/// The fixed source address, or `None` when the operand is not one.
pub(super) fn load_target(p: &Program, va: u64) -> Option<u64> {
    let bitness = p.arch.bitness()?;
    let code = p.read_va(va, 16)?;
    let mut decoder = Decoder::with_ip(bitness, code, va, DecoderOptions::NONE);
    let instr = decoder.decode();
    if instr.is_invalid() || instr.memory_base() == Register::None {
        return None;
    }
    match instr.memory_base() {
        Register::RIP | Register::EIP => Some(instr.ip_rel_memory_address()),
        Register::None => Some(instr.memory_displacement64()),
        _ => None,
    }
}

/// The register a dispatch loop fetches its operations through, and where
/// it is pointed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct VirtualPointer {
    /// The register, as the disassembly spells it.
    pub(super) register: String,
    /// `(the address it is pointed at, the instruction that points it)`,
    /// when the function sets it from a fixed address.
    pub(super) stored: Option<(u64, u64)>,
}

/// Finds the register a dispatch loop fetches its operations through.
///
/// An interpreter reads the next operation from a pointer and advances it,
/// so the register that both indexes a plain memory read and is stepped by
/// one is the virtual instruction pointer. The fetch and the step need not
/// share a block with the jump, so the whole function is read. Where the
/// function sets that register from a fixed address, that address is where
/// the operations are stored.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The function holding the loop.
///
/// # Returns
///
/// The pointer, or `None` when no register is both read through and stepped.
pub(super) fn virtual_pointer(p: &Program, f: &Function) -> Option<VirtualPointer> {
    let bitness = p.arch.bitness()?;
    let mut lines: Vec<disasm::DisasmLine> = Vec::new();
    for b in &f.blocks {
        let len = usize::try_from(b.end - b.start).unwrap_or(0);
        if let Some(code) = p.read_va(b.start, len) {
            lines.extend(disasm::disassemble(code, b.start, bitness, 256));
        }
    }
    let mut loaded: Vec<String> = Vec::new();
    let mut stepped: Vec<String> = Vec::new();
    for l in &lines {
        let text = l.text.as_str();
        if let Some(open) = text.find('[')
            && let Some(close) = text[open..].find(']')
        {
            let inside = &text[open + 1..open + close];
            if !inside.contains('*') && !inside.contains('+') && !inside.contains('-') {
                loaded.push(inside.to_owned());
            }
        }
        let mut words = text.split_whitespace();
        let mnemonic = words.next().unwrap_or("");
        let operand = words.next().unwrap_or("").trim_end_matches(',').to_owned();
        if mnemonic == "inc" || (mnemonic == "add" && text.ends_with(",1")) {
            stepped.push(operand);
        }
    }
    let register = loaded
        .into_iter()
        .find(|r| stepped.iter().any(|s| s == r))?;
    let stored = lines.iter().find_map(|l| {
        let text = l.text.as_str();
        let (mnemonic, rest) = text.split_once(char::is_whitespace).unwrap_or((text, ""));
        let dst = rest.split(',').next().unwrap_or("").trim();
        if dst != register || !matches!(mnemonic, "lea" | "mov") {
            return None;
        }
        load_target(p, l.va)
            .filter(|at| p.section_at(*at).is_some())
            .map(|at| (at, l.va))
    });
    Some(VirtualPointer { register, stored })
}

/// Tells whether `from` leads back to `to` inside one function.
///
/// # Arguments
///
/// * `f` - The function whose blocks are walked.
/// * `from` - The block to start at.
/// * `to` - The block looked for.
pub(super) fn reaches(f: &Function, from: u64, to: u64) -> bool {
    let mut seen: BTreeSet<u64> = BTreeSet::new();
    let mut work = vec![from];
    while let Some(at) = work.pop() {
        if at == to {
            return true;
        }
        if !seen.insert(at) {
            continue;
        }
        let Some(b) = f.blocks.iter().find(|b| b.start == at) else {
            continue;
        };
        work.extend(b.successors.iter().copied());
    }
    false
}

/// Most blocks walked backwards from a dispatch looking for its fetch.
pub(super) const FETCH_WALK_MAX: usize = 16;

/// Whether the register an indirect jump indexes its table with was last
/// written by a fetch from memory.
///
/// A small table does not by itself separate an interpreter from a
/// `switch`: both jump through a handful of targets that mostly come back.
/// What separates them is where the index comes from: an interpreter
/// fetches the next opcode out of its program, a memory read on the way to
/// the jump (`movzx ecx, byte [r9+r10-1]`), while an ordinary `switch`
/// indexes a value it computed (`and eax, 3` over a call's result) or was
/// handed. The last writer is what matters, so the walk goes backwards
/// through the blocks that fall into the dispatch, instruction by
/// instruction, until one writes the index register; a call stops it
/// (calls clobber the volatile registers) and so does a plain move. The
/// fetch must read through a register base other than the stack: a value
/// reloaded from a stack slot is a variable the program wrote, not a
/// program it reads.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The function holding the dispatch.
/// * `b` - The block that ends in the indirect jump.
/// * `bits` - The decoder bitness of the program.
///
/// # Returns
/// Whether a load of the indexing register from non-stack memory is what
/// reaches the jump.
pub(super) fn fetches_index_from_memory(
    p: &Program,
    f: &Function,
    b: &BasicBlock,
    bits: u32,
) -> bool {
    let Some(idx) = table_index_register(&block_instructions(p, f, b.start, bits)) else {
        return false;
    };
    let mut at = b.start;
    for _ in 0..FETCH_WALK_MAX {
        let Some(prev) = f
            .blocks
            .iter()
            .find(|x| x.end == at && x.start != x.end)
            .map(|x| x.start)
        else {
            return false;
        };
        let block = block_instructions(p, f, prev, bits);
        let mut info = InstructionInfoFactory::new();
        let mut hit = false;
        for i in block.iter().rev() {
            if writes(i, &mut info, idx) {
                hit = fetches(i, idx);
                break;
            }
        }
        if hit {
            return true;
        }
        at = prev;
    }
    false
}

/// The register a block's indirect jump reads its table through.
///
/// The read is the last instruction with a scaled index (`movsxd rcx,
/// [r11+rcx*4]`) or the jump itself when it reads memory (`jmp
/// [rax*8+T]`); rel32 tables compile to the first shape, absolute ones to
/// the second.
///
/// # Arguments
///
/// * `instrs` - The block's instructions, in order.
///
/// # Returns
/// The index register at full width, or `None` when nothing scales an
/// index.
fn table_index_register(instrs: &[Instruction]) -> Option<Register> {
    instrs
        .iter()
        .filter(|i| {
            i.mnemonic() != Mnemonic::Lea
                && (0..i.op_count()).any(|op| i.op_kind(op) == OpKind::Memory)
                && matches!(i.memory_index_scale(), 4 | 8)
                && i.memory_index() != Register::None
        })
        .map(|i| i.memory_index().full_register())
        .next_back()
}

/// Whether an instruction writes `want`, as a destination operand or by
/// being a call.
///
/// A compare or test names its first operand without writing it, so the
/// registers come from the instruction's access info, not its operand
/// order; a call clobbers every volatile register and stops the walk
/// wherever it lands.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `info` - The access-info factory the register access is read through.
/// * `want` - The register at full width.
fn writes(i: &Instruction, info: &mut InstructionInfoFactory, want: Register) -> bool {
    matches!(
        i.flow_control(),
        FlowControl::Call | FlowControl::IndirectCall
    ) || info.info(i).used_registers().iter().any(|u| {
        matches!(
            u.access(),
            OpAccess::Write | OpAccess::CondWrite | OpAccess::ReadWrite | OpAccess::ReadCondWrite
        ) && u.register().full_register() == want
    })
}

/// Whether an instruction loads `want` from non-stack memory.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `want` - The register at full width.
fn fetches(i: &Instruction, want: Register) -> bool {
    i.op0_kind() == OpKind::Register
        && i.op1_kind() == OpKind::Memory
        && matches!(
            i.mnemonic(),
            Mnemonic::Mov | Mnemonic::Movzx | Mnemonic::Movsx | Mnemonic::Movsxd
        )
        && i.op0_register().full_register() == want
        && !matches!(
            i.memory_base(),
            Register::None
                | Register::RIP
                | Register::EIP
                | Register::RSP
                | Register::ESP
                | Register::RBP
                | Register::EBP
        )
}

/// One block's instructions, decoded.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The function holding the block.
/// * `start` - The block's start address.
/// * `bits` - The decoder bitness of the program.
///
/// # Returns
/// The decoded instructions, empty when the block or its bytes are gone.
fn block_instructions(p: &Program, f: &Function, start: u64, bits: u32) -> Vec<Instruction> {
    let Some(b) = f.blocks.iter().find(|b| b.start == start) else {
        return Vec::new();
    };
    let len = usize::try_from(b.end - b.start).unwrap_or(0);
    let Some(code) = p.read_va(b.start, len) else {
        return Vec::new();
    };
    let mut instrs: Vec<Instruction> = Vec::new();
    let mut i = Instruction::default();
    let mut d = Decoder::with_ip(bits, code, b.start, DecoderOptions::NONE);
    while d.can_decode() {
        d.decode_out(&mut i);
        instrs.push(i);
    }
    instrs
}

/// Bytes of a handler the summarizer reads when the analysis knows no
/// function there.
pub(super) const HANDLER_SPAN: u64 = 64;

/// Summarizes what one handler does.
///
/// The mnemonics are read rather than the pseudo-C, since a handler is a
/// dozen instructions and what matters is which operation it carries out and
/// whether it touches memory. The operation is named from what it does
/// ([`virtual_op`]), because a reader of a devirtualized trace needs the
/// operation, not a list of mnemonics, and the mnemonics stay as the
/// evidence for it.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the handler's block.
/// * `at` - The handler's first instruction.
///
/// # Returns
///
/// `(instructions read, a description)`.
pub(super) fn handler_effect(p: &Program, a: &Analysis, at: u64) -> (usize, String) {
    let end = a
        .function_at(at)
        .and_then(|f| f.blocks.iter().find(|b| b.start == at).map(|b| b.end))
        .unwrap_or(at + HANDLER_SPAN);
    let len = usize::try_from(end.saturating_sub(at)).unwrap_or(0).max(1);
    let Some(code) = p.read_va(at, len) else {
        return (0, "unreadable".to_owned());
    };
    handler_effect_code(p, at, code)
}

/// Summarizes a handler from instruction bytes a caller holds.
///
/// The same reading [`handler_effect`] gives the image's bytes, over bytes
/// from anywhere else: a run's memory, once a protector has decrypted its
/// handlers there and the image still reads them as `unreadable`.
///
/// # Arguments
///
/// * `p` - The loaded image, for its architecture.
/// * `at` - The handler's first instruction.
/// * `code` - Its instruction bytes, from the image or a run's memory.
///
/// # Returns
///
/// `(instructions read, a description)`.
pub(super) fn handler_effect_code(p: &Program, at: u64, code: &[u8]) -> (usize, String) {
    let Some(bitness) = p.arch.bitness() else {
        return (0, "unknown architecture".to_owned());
    };
    let lines = disasm::disassemble(code, at, bitness, HANDLER_INSTRS);
    let ops = handler_ops(&lines);
    let memory = lines.iter().any(|l| l.text.contains('['));
    let kind = if ops.is_empty() {
        "moves only".to_owned()
    } else {
        ops.join(" ")
    };
    let where_ = if memory { " through memory" } else { "" };
    (
        lines.len(),
        format!("{}: {kind}{where_}", virtual_op(&ops, memory)),
    )
}

/// The mnemonics that name a handler's operation, moves excluded.
///
/// The same reading [`handler_effect_code`] summarizes: a handler's moves
/// reach its operands and are not its operation, so the first use of each
/// remaining mnemonic, in order, is the handler in one word.
///
/// # Arguments
///
/// * `lines` - The handler's disassembly.
///
/// # Returns
///
/// The mnemonics in first-seen order, moves excluded.
pub(super) fn handler_ops(lines: &[disasm::DisasmLine]) -> Vec<&str> {
    let mut ops: Vec<&str> = Vec::new();
    for l in lines {
        let mnemonic = l.text.split_whitespace().next().unwrap_or("");
        if matches!(
            mnemonic,
            "mov" | "movzx" | "movsx" | "lea" | "nop" | "jmp" | "push" | "pop" | "ret"
        ) {
            continue;
        }
        if !ops.contains(&mnemonic) {
            ops.push(mnemonic);
        }
    }
    ops
}

/// Names the virtual operation a handler implements.
///
/// A virtualizing protector compiles each original instruction into a
/// bytecode operation and one handler per operation. Naming the operation is
/// what turns a trace of handler addresses into a program: `VADD VLOAD
/// VBRANCH` says what ran, where three addresses say only that three
/// handlers did.
///
/// The name comes from what the handler's instructions do, and the
/// instructions are reported next to it, so a classification that is wrong
/// is visible rather than authoritative.
///
/// # Arguments
///
/// * `ops` - The mnemonics the handler uses, moves excluded.
/// * `memory` - Whether it touches memory.
///
/// # Returns
///
/// The operation's name.
pub(super) fn virtual_op(ops: &[&str], memory: bool) -> &'static str {
    let any = |names: &[&str]| names.iter().any(|n| ops.contains(n));
    if any(&["call"]) {
        return "calls out of the machine";
    }
    if any(&["cmp", "test"]) {
        return "a virtual compare or branch";
    }
    if any(&[
        "add", "sub", "inc", "dec", "adc", "sbb", "neg", "imul", "mul", "div", "idiv",
    ]) {
        return "virtual arithmetic";
    }
    if any(&["xor", "and", "or", "not"]) {
        return "virtual logic";
    }
    if any(&["shl", "shr", "sar", "rol", "ror", "rcl", "rcr"]) {
        return "a virtual shift or rotate";
    }
    if ops.is_empty() && memory {
        return "a virtual load or store";
    }
    if ops.is_empty() {
        return "a virtual register move";
    }
    "an operation this does not classify"
}

/// Fewest separate stores that build a run before it counts as a stack
/// string rather than a wide constant that happens to read as text.
pub(super) const STACK_STRING_STORES: usize = 2;

/// Shortest stack string reported.
pub(super) const STACK_STRING_LEN: usize = 6;

/// Most stack strings listed in one read.
pub(super) const STACK_STRINGS_MAX: usize = 400;

/// One string a function assembles on its stack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct StackString {
    /// Entry of the function that builds it.
    pub(super) entry: u64,
    /// The store that writes its first character.
    pub(super) at: u64,
    /// The text its stores spell.
    pub(super) text: String,
}

/// Recovers the strings functions assemble on their stacks.
///
/// The stores are immediates to a base register plus a displacement;
/// grouped by base and read in offset order they spell the text. A run
/// counts only when several separate stores build it, since one four-byte
/// store of a constant like `DXT1` is not a hidden string.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: functions and their blocks.
/// * `want` - Lowercase substring the text must contain, or empty.
///
/// # Returns
///
/// The strings by function in address order, each function's by base
/// register and offset; empty for an architecture with no decoder width.
pub(super) fn stack_strings(p: &Program, a: &Analysis, want: &str) -> Vec<StackString> {
    let Some(bitness) = p.arch.bitness() else {
        return Vec::new();
    };
    let mut rows: Vec<StackString> = Vec::new();
    for f in &a.functions {
        let mut frames: BTreeMap<Register, BTreeMap<i64, u8>> = BTreeMap::new();
        let mut store_of: BTreeMap<(Register, i64), usize> = BTreeMap::new();
        let mut stores: Vec<u64> = Vec::new();
        each_instruction(p, f, bitness, |i| {
            if let Some((base, disp, bytes)) = immediate_store(i, bitness) {
                for (k, byte) in bytes.iter().enumerate() {
                    let off = disp + i64::try_from(k).unwrap_or(0);
                    frames.entry(base).or_default().insert(off, *byte);
                    store_of.insert((base, off), stores.len());
                }
                stores.push(i.ip());
            }
        });
        for (base, slots) in &frames {
            let placed = slots.iter().map(|(off, b)| (off.cast_unsigned(), *b));
            for (start, text) in printable_runs(placed) {
                let used = slots
                    .range(start.cast_signed()..)
                    .take(text.len())
                    .filter_map(|(off, _)| store_of.get(&(*base, *off)))
                    .collect::<BTreeSet<_>>()
                    .len();
                if text.chars().count() >= STACK_STRING_LEN
                    && used >= STACK_STRING_STORES
                    && text.to_lowercase().contains(want)
                {
                    let first = store_of
                        .get(&(*base, start.cast_signed()))
                        .and_then(|n| stores.get(*n));
                    rows.push(StackString {
                        entry: f.entry,
                        at: first.copied().unwrap_or(f.entry),
                        text,
                    });
                }
            }
        }
    }
    rows
}

/// Recovers the strings a function assembles on its stack.
///
/// Malware keeps a string out of the data sections by writing it onto the
/// stack a byte, word or dword at a time and using it in place, so it never
/// appears in a strings dump. The strings are those of [`stack_strings`].
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis: functions and their blocks.
/// * `o` - User names.
/// * `filter` - Case-insensitive substring of the recovered text, or empty.
///
/// # Returns
///
/// The listing as text.
pub fn stack_strings_tsv(p: &Program, a: &Analysis, o: &Overlay, filter: &str) -> String {
    if let Err(why) = x86_reading(p, "stackstrings") {
        return format!("# {why}\n");
    }
    if p.arch.bitness().is_none() {
        return "# unknown architecture\n".to_owned();
    }
    let rows = stack_strings(p, a, &filter.to_lowercase());
    let mut out = format!(
        "# {} stack string{}{}\n",
        rows.len().min(STACK_STRINGS_MAX),
        plural(rows.len()),
        narrows(rows.len(), STACK_STRINGS_MAX, "stackstrings")
    );
    out.push_str("# function                       string\n");
    for r in rows.iter().take(STACK_STRINGS_MAX) {
        let _ = writeln!(out, "{:<30}  {:?}", name_of(a, o, r.entry), r.text);
    }
    out
}

/// The base, displacement and bytes of a `mov [base+disp], imm` store.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `bitness` - Decoder bitness of the program.
///
/// # Returns
///
/// `(base register, displacement, the immediate's little-endian bytes)`, or
/// `None` when the instruction is not an immediate store to a based address.
pub(super) fn immediate_store(i: &Instruction, bitness: u32) -> Option<(Register, i64, Vec<u8>)> {
    use crate::isa::x86::MemorySize;
    if i.mnemonic() != Mnemonic::Mov || i.op_count() != 2 {
        return None;
    }
    if i.op0_kind() != OpKind::Memory || i.memory_index() != Register::None {
        return None;
    }
    let base = i.memory_base();
    if base == Register::None || base == Register::RIP || base == Register::EIP {
        return None;
    }
    let imm = match i.op1_kind() {
        OpKind::Immediate8 => u64::from(i.immediate8()),
        OpKind::Immediate16 => u64::from(i.immediate16()),
        OpKind::Immediate32 => u64::from(i.immediate32()),
        OpKind::Immediate8to32 => i64::from(i.immediate8to32()).cast_unsigned(),
        _ => return None,
    };
    let width = match i.memory_size() {
        MemorySize::UInt8 | MemorySize::Int8 => 1,
        MemorySize::UInt16 | MemorySize::Int16 => 2,
        MemorySize::UInt32 | MemorySize::Int32 => 4,
        _ => return None,
    };
    let disp = disasm::displacement(i, bitness);
    Some((base, disp, imm.to_le_bytes()[..width].to_vec()))
}

#[cfg(test)]
mod tests {
    use super::{flattening_tsv, vm_dispatch_tsv};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::Program;

    /// A filter that names nothing is refused, where it listed every
    /// dispatcher; a name reaches the loop listing as an address does.
    ///
    /// # Panics
    ///
    /// When a filter naming nothing lists, or a name is not resolved.
    #[test]
    fn a_filter_naming_nothing_is_refused() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        assert_eq!(
            flattening_tsv(&p, &a, &o, "nowhere").unwrap_err(),
            "cannot resolve nowhere"
        );
        assert_eq!(
            vm_dispatch_tsv(&p, &a, &o, "nowhere").unwrap_err(),
            "cannot resolve nowhere"
        );
        assert_eq!(
            vm_dispatch_tsv(&p, &a, &o, "sub_1000").unwrap_err(),
            "no dispatch loop at sub_1000"
        );
        assert!(
            vm_dispatch_tsv(&p, &a, &o, " ")
                .unwrap()
                .starts_with("# 0 dispatch loop")
        );
    }
}
