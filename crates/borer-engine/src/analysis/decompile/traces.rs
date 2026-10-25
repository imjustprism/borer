//! The structure check: the control flow the text claims, checked against
//! the binary's.
//!
//! The decompiled text and the function's control-flow graph become the
//! same kind of graph, whose steps a reader can see on both sides: a call
//! to a function the code names outright (by its name), a return, and the
//! end of a path that never returns. Branches, loops, switches, `break`,
//! `continue` and `goto` are the silent choices and jumps between them; a
//! label is silent too, but it names a block, so the text's path through
//! `L_x:` must be where the binary can be at block `x`. Each side's paths
//! must be the other's: every path the text claims (an `if` taken either
//! way, any arm of a switch) is a path of the binary, and every path of
//! the binary is one the text claims, both up to those steps.
//!
//! The check is a subset construction over the other side (one side's path
//! against every place the other may be, `seen` once each), with fuel. It
//! is blind to data and to a test whose outcome both sides get wrong alike:
//! it says the text calls what the binary calls, in an order the binary
//! can, and returns where the binary can, which is what a structuring or
//! text pass gets wrong when it binds a `break` to the wrong loop, drops an
//! arm, or sends a `goto` elsewhere. The graph is the one the structurer
//! was handed: edges the lifter proved dead are left out, as the text
//! leaves them out.

use std::collections::BTreeSet;
use std::rc::Rc;

use crate::isa::x86::{Decoder, DecoderOptions, FlowControl, Instruction, OpKind};
use crate::isa::{Isa, a32, a64};

use super::expr_render::bare;
use super::{decompile_plain_full, lift, lift_a32, lift_a64, matching_paren, name_fields};
use crate::analysis::render::{epilog_helper, frame_helper};
use crate::analysis::{
    Analysis, BlockTerm, Function, Overlay, decompiled_cached, is_executable_va, name_of, striped,
};
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::program::{Program, SymbolKind};

/// Most states one direction of the check visits, counting every node a
/// closure walks, before it gives up unchecked.
const FUEL: usize = 2_000_000;

/// Deepest nesting of the text's structures the parser follows.
const DEPTH: usize = 512;

/// The graph the structurer was handed: each block's successors once the
/// edges of conditions and switches the lifter folded to a constant are
/// gone, by block index.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LiveCfg {
    /// The successors of each block of the function, by index into its
    /// blocks.
    pub(crate) succs: Vec<Vec<usize>>,
}

impl LiveCfg {
    /// The bytes the graph holds, which the memo keeping it counts.
    pub(crate) fn bytes(&self) -> usize {
        self.succs.capacity() * size_of::<Vec<usize>>()
            + self
                .succs
                .iter()
                .map(|s| s.capacity() * size_of::<usize>())
                .sum::<usize>()
    }
}

/// What the structure check found for one function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Structure {
    /// Every path of either side is a path of the other, up to calls,
    /// returns and labels.
    Agrees,
    /// One side has a path the other lacks.
    Disagrees(Box<Disagreement>),
    /// Nothing is claimed: why the check could not run to the end.
    Unchecked(&'static str),
}

/// Which side holds a path the other lacks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    /// The text claims a path the binary does not have.
    Text,
    /// The binary has a path the text does not claim.
    Binary,
}

/// A path one side has and the other cannot follow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Disagreement {
    /// The side whose path it is.
    pub side: Side,
    /// Where that side takes the step: a line number of the text (1-based)
    /// or an address of the binary.
    pub at: u64,
    /// The step: `call NAME`, `return` or `label L_<addr>`.
    pub step: String,
    /// What the other side could do there instead, at most a few, and
    /// where it stood: lines of the text or addresses of the binary.
    pub other: Vec<String>,
}

/// The names the text gives instructions that are no calls.
///
/// A `rep stos` is `memset`, a byte-counting loop `strlen`, `sqrtsd` is
/// `sqrt`: a call the text writes under one of them may be one of those
/// instead.
pub(super) const INTRINSICS: [&str; 9] = [
    "memset", "memcpy", "memmove", "strlen", "wcslen", "sqrt", "fabs", "fmin", "fmax",
];

/// A call as both sides spell it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Callee {
    /// A call to the function with this index in the names.
    Named(u32),
    /// A call the other side may show or not: one the binary makes through
    /// a register or memory it does not name (`None`, any name), or one
    /// the text writes under a name it also gives an instruction.
    Maybe(Option<u32>),
}

impl Callee {
    /// Tells whether a step of one side can be this step of the other.
    ///
    /// # Arguments
    ///
    /// * `other` - The other side's call.
    fn meets(self, other: Callee) -> bool {
        match (self, other) {
            (Callee::Named(a), Callee::Named(b)) => a == b,
            (Callee::Named(a), Callee::Maybe(b)) | (Callee::Maybe(b), Callee::Named(a)) => {
                b.is_none_or(|b| b == a)
            }
            (Callee::Maybe(a), Callee::Maybe(b)) => a.is_none() || b.is_none() || a == b,
        }
    }
}

/// A node of a path graph.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Node {
    /// A call, then the node after it.
    Call(Callee, u32),
    /// A return.
    Ret,
    /// The end of a path that does not return: a call that never returns,
    /// a trap, a jump nobody resolved.
    Halt,
    /// A silent step to any of these nodes: a branch, a switch, a jump.
    Go(Vec<u32>),
    /// A switch with no `default` arm: its arms, and the node it falls out
    /// to. Falling out is a path the other side may take through it, but
    /// not one the text claims: the switch has no default either because
    /// the value never misses every case (a jump table's bounds are tested
    /// before it) or because the default is where the switch falls out.
    Switch(Vec<u32>, u32),
    /// The text's label of the block with this index, then the node after
    /// it.
    Label(u32, u32),
}

/// A node of a path graph, by its index among that graph's nodes.
///
/// The index `u32::MAX` stands for no node: what a graph with more nodes
/// than a `u32` names hands out, which every read treats as past every
/// node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NodeIx(u32);

impl NodeIx {
    /// The index as a position of one of its graph's per-node `Vec`s, past
    /// every element when it stands for no node.
    fn pos(self) -> usize {
        usize::try_from(self.0).unwrap_or(usize::MAX)
    }
}

/// One side's paths.
#[derive(Debug, Default)]
struct Graph {
    /// The nodes.
    nodes: Vec<Node>,
    /// Where each node is: a text line number, or a binary address.
    site: Vec<u64>,
}

impl Graph {
    /// Adds a node.
    ///
    /// # Arguments
    ///
    /// * `node` - The node.
    /// * `site` - Where it is.
    fn add(&mut self, node: Node, site: u64) -> u32 {
        self.nodes.push(node);
        self.site.push(site);
        u32::try_from(self.nodes.len() - 1).unwrap_or(u32::MAX)
    }

    /// The node at an index.
    ///
    /// # Arguments
    ///
    /// * `ix` - The index.
    ///
    /// # Returns
    ///
    /// The node, or `None` when the index stands for no node, which every
    /// walk reads as [`Node::Halt`].
    fn node(&self, ix: NodeIx) -> Option<&Node> {
        self.nodes.get(ix.pos())
    }

    /// Where the node at an index is: a text line number, or a binary
    /// address.
    ///
    /// # Arguments
    ///
    /// * `ix` - The index.
    ///
    /// # Returns
    ///
    /// The site, or `None` when the index stands for no node.
    fn site(&self, ix: NodeIx) -> Option<u64> {
        self.site.get(ix.pos()).copied()
    }

    /// Points the node at an index at successors, when it stands for one.
    ///
    /// # Arguments
    ///
    /// * `ix` - The index.
    /// * `to` - The successors.
    fn set_go(&mut self, ix: NodeIx, to: Vec<u32>) {
        if let Some(slot) = self.nodes.get_mut(ix.pos()) {
            *slot = Node::Go(to);
        }
    }

    /// Points every step past the silent steps with one way on, so a walk
    /// never stops at them.
    ///
    /// # Returns
    ///
    /// Where each node now leads: itself, or the first node past its chain
    /// of single steps (a chain that cycles stops on the cycle).
    fn compress(&mut self) -> Vec<u32> {
        let n = self.nodes.len();
        let past = |g: &Graph, mut x: u32| {
            for _ in 0..n {
                match g.node(NodeIx(x)).unwrap_or(&Node::Halt) {
                    Node::Go(to) if to.len() == 1 => x = to[0],
                    _ => break,
                }
            }
            x
        };
        let to: Vec<u32> = (0..n)
            .map(|i| past(self, u32::try_from(i).unwrap_or(u32::MAX)))
            .collect();
        let at = |x: &mut u32| *x = to.get(NodeIx(*x).pos()).copied().unwrap_or(*x);
        for node in &mut self.nodes {
            match node {
                Node::Call(_, next) | Node::Label(_, next) => at(next),
                Node::Go(all) => all.iter_mut().for_each(at),
                Node::Switch(all, out) => {
                    all.iter_mut().for_each(at);
                    at(out);
                }
                Node::Ret | Node::Halt => {}
            }
        }
        to
    }
}

/// The calls a function's graph names, and how each is spelled.
#[derive(Debug, Default)]
struct Names {
    /// The names, by index.
    names: Vec<String>,
    /// Each name's index.
    index: FxHashMap<String, u32>,
    /// Names whose call never returns: the block that calls it has no
    /// successor.
    noreturn: BTreeSet<u32>,
    /// Names the header says the text leaves out: a call to one is a step
    /// the text may write or not, as it writes a check it could not fold.
    dropped: BTreeSet<u32>,
    /// What each call target reads as, worked out once: a near target
    /// (`true`) or a slot read through (`false`), by address.
    seen: FxHashMap<(bool, u64), Option<Callee>>,
    /// The names by their last byte, where a call's `(` follows it.
    by_last: FxHashMap<u8, Vec<u32>>,
}

impl Names {
    /// The index of a name, added if new.
    ///
    /// # Arguments
    ///
    /// * `name` - The name as the text writes it.
    fn intern(&mut self, name: &str) -> u32 {
        if let Some(&i) = self.index.get(name) {
            return i;
        }
        let i = u32::try_from(self.names.len()).unwrap_or(u32::MAX);
        self.names.push(name.to_owned());
        self.index.insert(name.to_owned(), i);
        if let Some(&last) = name.as_bytes().last() {
            self.by_last.entry(last).or_default().push(i);
        }
        i
    }

    /// A name by its index.
    ///
    /// # Arguments
    ///
    /// * `k` - The index [`Names::intern`] returned.
    ///
    /// # Returns
    ///
    /// The name, or `None` when the index stands for none.
    fn name(&self, k: u32) -> Option<&str> {
        self.names
            .get(usize::try_from(k).unwrap_or(usize::MAX))
            .map(String::as_str)
    }
}

/// How the text says it treated the calls to one function, from its
/// header notes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Quiet {
    /// Written as the call it is.
    Shown,
    /// Left out: it does nothing but return, or it checks a stack
    /// protector the text folded.
    Dropped,
    /// Read in place or called through the register it jumps through:
    /// the text writes another call, or none.
    Other,
}

/// Tells how the header of `text` says calls to `name` were written.
///
/// # Arguments
///
/// * `notes` - The text's `// note:` and `// folded:` header lines.
/// * `name` - The callee's full name.
fn quiet(notes: &[&str], name: &str) -> Quiet {
    let listed = |list: &str| {
        list == name
            || list.starts_with(&format!("{name}, "))
            || list.ends_with(&format!(", {name}"))
            || list.contains(&format!(", {name}, "))
    };
    for line in notes {
        if let Some(folded) = line.strip_prefix("// folded: ")
            && let Some((list, _)) = folded
                .split_once("; calls to ")
                .and_then(|(_, r)| r.split_once(" are left out"))
            && listed(list)
        {
            return Quiet::Dropped;
        }
        let Some(note) = line.strip_prefix("// note: ") else {
            continue;
        };
        if let Some((list, _)) = note
            .strip_prefix("calls to ")
            .and_then(|r| r.split_once(" are left out"))
            && listed(list)
        {
            return Quiet::Dropped;
        }
        let other = [
            " is read in place",
            " are read in place",
            " only jumps through ",
        ]
        .iter()
        .find_map(|m| note.split_once(m).map(|(list, _)| list));
        if other.is_some_and(listed) {
            return Quiet::Other;
        }
    }
    Quiet::Shown
}

/// Where a call or jump of the binary goes, as the check reads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Dest {
    /// A direct target.
    Near(u64),
    /// The address of the slot it reads its target from.
    Slot(u64),
    /// A register or memory no constant names.
    Unknown,
}

/// A call in a block, as the check reads it.
#[derive(Debug, Clone, Copy)]
struct Site {
    /// Where it goes.
    dest: Dest,
    /// Its address.
    at: u64,
    /// Whether it goes to a frame helper, which builds or tears down the
    /// caller's frame and which the text writes as no call at all.
    helper: bool,
    /// Whether it runs only under a condition no block of the graph tests
    /// (an ARM32 predicated `bl`), so the text may write it or not.
    guarded: bool,
}

/// What the check reads of one block: its calls, in order, and its last
/// instruction's address and, for a jump, where it goes.
#[derive(Debug, Default)]
struct BlockCode {
    /// The calls.
    calls: Vec<Site>,
    /// The last instruction, `None` when nothing decodes.
    last: Option<(u64, Dest)>,
}

/// Decodes every block of a function for the check, in block order and in
/// the program's instruction set.
///
/// An x86 call or jump goes near, through a slot, or through a register;
/// an arm64 or ARM32 one goes near or through a register. The ARM blocks
/// are the lifter's ([`lift_a32::decode_blocks`]), so an `IT` block's
/// conditions carry across blocks and a guarded instruction behind the
/// test its block was split off at runs unconditionally.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions, for the frame helpers' names.
/// * `overlay` - The names in force.
/// * `f` - The function.
fn function_code(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
) -> Vec<BlockCode> {
    match program.arch.isa() {
        Some(Isa::X86 { bits }) => f
            .blocks
            .iter()
            .map(|b| x86_block(program, analysis, overlay, bits, b.start, b.end))
            .collect(),
        Some(Isa::A64) => arm_code(&lift_a64::decode_blocks(program, f), |i| {
            (i.va, i.target(), i.flow == a64::Flow::Call, false)
        }),
        Some(Isa::A32) => arm_code(&lift_a32::decode_blocks(program, f), |i| {
            (
                i.va & !a32::SKIP,
                i.target(),
                i.flow() == a32::Flow::Call,
                i.predicated(),
            )
        }),
        None => f.blocks.iter().map(|_| BlockCode::default()).collect(),
    }
}

/// Reads decoded ARM blocks for the check.
///
/// # Arguments
///
/// * `blocks` - Each block's instructions.
/// * `read` - An instruction's address, direct target, whether it calls
///   and whether it runs under a condition.
fn arm_code<I>(
    blocks: &[Vec<I>],
    read: impl Fn(&I) -> (u64, Option<u64>, bool, bool),
) -> Vec<BlockCode> {
    blocks
        .iter()
        .map(|v| {
            let mut out = BlockCode::default();
            for i in v {
                let (at, target, call, guarded) = read(i);
                let dest = target.map_or(Dest::Unknown, Dest::Near);
                if call {
                    out.calls.push(Site {
                        dest,
                        at,
                        helper: false,
                        guarded,
                    });
                }
                out.last = Some((at, dest));
            }
            out
        })
        .collect()
}

/// Decodes one x86 block for the check.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions, for the frame helpers' names.
/// * `overlay` - The names in force.
/// * `bits` - 32 or 64.
/// * `start` - The block's first address.
/// * `end` - The address past its last instruction.
fn x86_block(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    bits: u32,
    start: u64,
    end: u64,
) -> BlockCode {
    let mut out = BlockCode::default();
    let len = usize::try_from(end.saturating_sub(start)).unwrap_or(0);
    let Some(bytes) = program
        .read_va_upto(start, len)
        .filter(|_| is_executable_va(program, start))
    else {
        return out;
    };
    let dest = |i: &Instruction| {
        if matches!(
            i.op0_kind(),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
        ) {
            Dest::Near(i.near_branch_target())
        } else {
            lift::static_target(i).map_or(Dest::Unknown, Dest::Slot)
        }
    };
    let mut last = None;
    for i in Decoder::with_ip(bits, bytes, start, DecoderOptions::NONE)
        .into_iter()
        .take_while(|i| !i.is_invalid())
    {
        if matches!(
            i.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            out.calls.push(Site {
                dest: dest(&i),
                at: i.ip(),
                helper: frame_helper(analysis, overlay, &i) || epilog_helper(analysis, overlay, &i),
                guarded: false,
            });
        }
        last = Some(i);
    }
    out.last = last.map(|i| (i.ip(), dest(&i)));
    out
}

/// The name of the import a slot holds, as the lifter writes it.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its symbol index.
/// * `slot` - The address a call or jump reads its target from.
fn import_at(program: &Program, analysis: &Analysis, slot: u64) -> Option<String> {
    let import = |s: &&crate::program::Symbol| s.kind == SymbolKind::Import && s.addr == slot;
    analysis
        .symbol_at(program, slot)
        .filter(import)
        .or_else(|| program.symbols.iter().find(import))
        .filter(|_| slot != 0)
        .map(|s| bare(&crate::search::demangled_name(&s.name)).into_owned())
}

/// What a call or jump out of the function reaches, as a callee.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions.
/// * `overlay` - The names in force.
/// * `notes` - The text's header notes.
/// * `names` - The names met so far, and what each target read as.
/// * `dest` - Where the call or jump goes.
/// * `helper` - Whether it is a frame helper's call ([`Site::helper`]).
///
/// # Returns
///
/// The callee, or `None` for a frame helper's call, which the text never
/// writes. A call the header says the text leaves out is one it may still
/// write, where it could not fold the check around it, so it is a step
/// the text may take or not, under the name it would write.
fn callee(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    notes: &[&str],
    names: &mut Names,
    dest: Dest,
    helper: bool,
) -> Option<Callee> {
    let key = match dest {
        Dest::Near(t) => (true, t),
        Dest::Slot(slot) => (false, slot),
        Dest::Unknown => return Some(Callee::Maybe(None)),
    };
    if let Some(c) = names.seen.get(&key) {
        return *c;
    }
    let c = if !key.0 {
        let import = import_at(program, analysis, key.1);
        Some(import.map_or(Callee::Maybe(None), |n| Callee::Named(names.intern(&n))))
    } else if helper {
        None
    } else {
        let full = name_of(analysis, overlay, key.1);
        match quiet(notes, &full) {
            Quiet::Shown => Some(Callee::Named(names.intern(&bare(&full)))),
            Quiet::Dropped => {
                let k = names.intern(&bare(&full));
                names.dropped.insert(k);
                Some(Callee::Maybe(Some(k)))
            }
            Quiet::Other => Some(Callee::Maybe(None)),
        }
    };
    names.seen.insert(key, c);
    c
}

/// The binary's paths through one function.
///
/// Each block is a chain of its calls ending in what it does last: a
/// return, a silent step to its live successors, a halt for a call that
/// never returns (one with no successor, or whose only way on leaves the
/// function after a call that ends the path,
/// [`crate::analysis::functions::call_ends_path`]) or a trap, a tail call
/// (the call, then a return), or a halt for a jump out of the function the
/// text writes as `goto *`.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions.
/// * `overlay` - The names in force.
/// * `f` - The function.
/// * `live` - Its live successors.
/// * `notes` - The text's `// note:` header lines.
/// * `names` - Receives the names the calls use.
///
/// # Returns
///
/// The graph and each block's first node.
fn binary_graph(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
    live: &LiveCfg,
    notes: &[&str],
    names: &mut Names,
) -> (Graph, Vec<u32>) {
    let mut g = Graph::default();
    let halt = g.add(Node::Halt, f.entry);
    let heads: Vec<u32> = f
        .blocks
        .iter()
        .map(|b| g.add(Node::Go(Vec::new()), b.start))
        .collect();
    let code = function_code(program, analysis, overlay, f);
    for (k, b) in f.blocks.iter().enumerate() {
        let (sites, last) = code.get(k).map_or((&[][..], None), |c| (&*c.calls, c.last));
        let mut calls: Vec<(Callee, u64)> = Vec::new();
        for site in sites {
            let c = callee(
                program,
                analysis,
                overlay,
                notes,
                names,
                site.dest,
                site.helper,
            );
            let c = match c {
                Some(Callee::Named(n)) if site.guarded => Some(Callee::Maybe(Some(n))),
                c => c,
            };
            if let Some(c) = c {
                calls.push((c, site.at));
            }
        }
        let succs = live.succs.get(k).map_or(&[][..], Vec::as_slice);
        let mut next: Vec<u32> = succs
            .iter()
            .filter_map(|s| heads.get(*s).copied())
            .collect();
        let outside = b
            .successors
            .iter()
            .any(|s| f.blocks.binary_search_by_key(s, |b| b.start).is_err())
            || (b.term == BlockTerm::Fall && b.successors.is_empty());
        let end = match b.term {
            BlockTerm::Ret => g.add(Node::Ret, last.map_or(b.start, |(at, _)| at)),
            BlockTerm::Invalid => halt,
            BlockTerm::Jmp | BlockTerm::Indirect if next.is_empty() => {
                let out = last.and_then(|(_, dest)| {
                    callee(program, analysis, overlay, notes, names, dest, false)
                });
                let at = last.map_or(b.start, |(at, _)| at);
                match out {
                    Some(Callee::Maybe(Some(k))) if names.dropped.contains(&k) => halt,
                    Some(c) => {
                        let ret = g.add(Node::Ret, at);
                        g.add(Node::Call(c, ret), at)
                    }
                    None => halt,
                }
            }
            BlockTerm::Call
                if b.successors.is_empty()
                    || (next.is_empty()
                        && outside
                        && crate::analysis::functions::call_ends_path(program, analysis, b)) =>
            {
                if let Some((Callee::Named(n) | Callee::Maybe(Some(n)), _)) = calls.last() {
                    names.noreturn.insert(*n);
                }
                halt
            }
            BlockTerm::Jmp
            | BlockTerm::Indirect
            | BlockTerm::Cond
            | BlockTerm::Call
            | BlockTerm::Fall => {
                if outside {
                    next.push(halt);
                }
                g.add(Node::Go(next), b.start)
            }
        };
        let mut chain = end;
        for &(c, at) in calls.iter().rev() {
            chain = g.add(Node::Call(c, chain), at);
        }
        if let Some(&head) = heads.get(k) {
            g.set_go(NodeIx(head), vec![chain]);
        }
    }
    (g, heads)
}

/// A structure of the text, as its lines nest.
#[derive(Debug)]
pub(super) enum Stmt {
    /// `L_<addr>:` on this line.
    Label(u64, usize),
    /// A statement on this line.
    Plain(usize),
    /// `if (c)` on this line, its arm, and its `else` arm.
    If(usize, Vec<Stmt>, Vec<Stmt>),
    /// `while (1)`.
    Loop(Vec<Stmt>),
    /// `while (c)` on this line.
    While(usize, Vec<Stmt>),
    /// `for (init; c; step)` on this line.
    For(usize, Vec<Stmt>),
    /// `do { } while (c);`, the condition on this line.
    Do(Vec<Stmt>, usize),
    /// `switch (v)` on this line, and its arms in order, each marked when
    /// it is the default and with the line its labels stand on.
    Switch(usize, Vec<(bool, usize, Vec<Stmt>)>),
    /// `goto L_<addr>;`.
    Goto(u64),
    /// `break;`.
    Break,
    /// `continue;`.
    Continue,
    /// `return ...;` on this line.
    Return(usize),
    /// A path the text ends: `goto *x;` or a trap.
    Halt(usize),
    /// `try {` or `__try {` on this line, its body, and its handlers in
    /// order, each with the line of its head.
    Try(usize, Vec<Stmt>, Vec<(Handler, usize, Vec<Stmt>)>),
}

/// The head of a guarded region's handler.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Handler {
    /// `} catch (decl) {`: entered by a throw the body makes.
    Catch,
    /// `} __except (filter) {`: entered by a fault the filter accepts.
    Except,
    /// `} __finally {`: run however the body is left.
    Finally,
}

/// Reads the text's lines into its structures.
#[derive(Debug)]
struct Parser<'t> {
    /// The body's lines, comments and string contents blanked, trimmed.
    lines: &'t [String],
    /// The next line to read.
    at: usize,
    /// The first line of the body in the whole text.
    base: usize,
}

impl<'t> Parser<'t> {
    /// The 1-based line number of a body line in the whole text.
    ///
    /// # Arguments
    ///
    /// * `i` - The body line.
    fn line(&self, i: usize) -> usize {
        self.base + i + 1
    }

    /// The next line holding anything, and its index.
    fn peek(&mut self) -> Option<(usize, &'t str)> {
        while self.lines.get(self.at).is_some_and(String::is_empty) {
            self.at += 1;
        }
        self.lines.get(self.at).map(|t| (self.at, t.as_str()))
    }

    /// Reads statements up to the `}` that closes them, which stays unread.
    ///
    /// # Arguments
    ///
    /// * `depth` - How deep the structures nest here.
    ///
    /// # Errors
    ///
    /// The text ends inside a structure, nests deeper than [`DEPTH`], or holds a
    /// line the parser does not know.
    fn block(&mut self, depth: usize) -> Result<Vec<Stmt>, &'static str> {
        if depth > DEPTH {
            return Err("nesting too deep");
        }
        let mut out = Vec::new();
        while let Some((_, t)) = self.peek() {
            if t.starts_with('}') {
                break;
            }
            out.push(self.stmt(depth)?);
        }
        Ok(out)
    }

    /// Reads the line that closes a block, and its index.
    fn closer(&mut self) -> Option<(usize, &'t str)> {
        let next = self.peek()?;
        self.at += 1;
        Some(next)
    }

    /// Reads one statement or structure.
    ///
    /// # Arguments
    ///
    /// * `depth` - How deep the structures nest here.
    ///
    /// # Errors
    ///
    /// The text ends inside a structure or holds a line the parser does not
    /// know.
    fn stmt(&mut self, depth: usize) -> Result<Stmt, &'static str> {
        let (i, t) = self.closer().ok_or("text ends inside a structure")?;
        let line = self.line(i);
        if let Some(addr) = t
            .strip_suffix(':')
            .and_then(|l| l.strip_prefix("L_"))
            .and_then(|h| u64::from_str_radix(h, 16).ok())
        {
            return Ok(Stmt::Label(addr, line));
        }
        if t.starts_with("if (") {
            let close = matching_paren(t, 3).ok_or("unbalanced condition")?;
            let rest = t.get(close + 1..).unwrap_or("").trim();
            if rest == "{" {
                return self.if_chain(line, depth);
            }
            let arm = simple(rest, line)?;
            return Ok(Stmt::If(line, vec![arm], Vec::new()));
        }
        if t == "while (1) {" {
            let body = self.block(depth + 1)?;
            self.closer();
            return Ok(Stmt::Loop(body));
        }
        if t.starts_with("while (") && t.ends_with(") {") {
            let body = self.block(depth + 1)?;
            self.closer();
            return Ok(Stmt::While(line, body));
        }
        if t.starts_with("for (") && t.ends_with(") {") {
            let body = self.block(depth + 1)?;
            self.closer();
            return Ok(Stmt::For(line, body));
        }
        if t == "do {" {
            let body = self.block(depth + 1)?;
            let (at, closer) = self.closer().ok_or("text ends inside a do")?;
            if !(closer.starts_with("} while (") && closer.ends_with(");")) {
                return Err("do without its while");
            }
            return Ok(Stmt::Do(body, self.line(at)));
        }
        if t.starts_with("switch (") && t.ends_with(") {") {
            return self.switch(line, depth);
        }
        if t == "try {" || t == "__try {" {
            return self.guarded(line, depth);
        }
        simple(t, line)
    }

    /// Reads a guarded region after its opening line, up to the `}` that
    /// closes its last handler.
    ///
    /// # Arguments
    ///
    /// * `line` - The line of `try {` or `__try {`.
    /// * `depth` - How deep the structures nest here.
    ///
    /// # Errors
    ///
    /// The text ends inside the region or closes a part of it with a line
    /// no handler has.
    fn guarded(&mut self, line: usize, depth: usize) -> Result<Stmt, &'static str> {
        let body = self.block(depth + 1)?;
        let mut handlers = Vec::new();
        loop {
            let (at, closer) = self.closer().ok_or("text ends inside a try")?;
            let head = match closer {
                "}" if !handlers.is_empty() => return Ok(Stmt::Try(line, body, handlers)),
                "} __finally {" => Handler::Finally,
                _ if closer.starts_with("} catch (") && closer.ends_with(") {") => Handler::Catch,
                _ if closer.starts_with("} __except (") && closer.ends_with(") {") => {
                    Handler::Except
                }
                _ => return Err("unknown closer of a try"),
            };
            handlers.push((head, self.line(at), self.block(depth + 1)?));
        }
    }

    /// Reads an `if` chain after its opening line, its `else if` arms nested
    /// in its `else`.
    ///
    /// # Arguments
    ///
    /// * `line` - The line of the condition.
    /// * `depth` - How deep the structures nest here.
    ///
    /// # Errors
    ///
    /// The text ends inside the chain or closes it with a line no `if` has.
    fn if_chain(&mut self, line: usize, depth: usize) -> Result<Stmt, &'static str> {
        let then = self.block(depth + 1)?;
        let (at, closer) = self.closer().ok_or("text ends inside an if")?;
        if closer == "}" {
            return Ok(Stmt::If(line, then, Vec::new()));
        }
        if closer == "} else {" {
            let other = self.block(depth + 1)?;
            self.closer();
            return Ok(Stmt::If(line, then, other));
        }
        if closer.starts_with("} else if (") && closer.ends_with(") {") {
            let nested = self.if_chain(self.line(at), depth + 1)?;
            return Ok(Stmt::If(line, then, vec![nested]));
        }
        Err("unknown closer of an if")
    }

    /// Reads a switch after its opening line.
    ///
    /// # Arguments
    ///
    /// * `line` - The line of the value switched on.
    /// * `depth` - How deep the structures nest here.
    ///
    /// # Errors
    ///
    /// The text ends inside the switch or holds an arm with no `case`.
    fn switch(&mut self, line: usize, depth: usize) -> Result<Stmt, &'static str> {
        let mut arms = Vec::new();
        loop {
            let (i, t) = self.closer().ok_or("text ends inside a switch")?;
            if t == "}" {
                return Ok(Stmt::Switch(line, arms));
            }
            let mut rest = t;
            let mut labels = 0;
            let mut default = false;
            loop {
                if let Some(r) = rest.strip_prefix("default:") {
                    default = true;
                    rest = r.trim_start();
                } else if let Some(r) = rest.strip_prefix("case ") {
                    rest = r
                        .split_once(':')
                        .ok_or("case without a colon")?
                        .1
                        .trim_start();
                } else {
                    break;
                }
                labels += 1;
            }
            if labels == 0 {
                return Err("switch arm without a case");
            }
            let body = match rest {
                "{" => {
                    let body = self.block(depth + 1)?;
                    self.closer();
                    body
                }
                "" => Vec::new(),
                other => vec![simple(other, self.line(i))?],
            };
            arms.push((default, self.line(i), body));
        }
    }
}

/// Reads a body's lines into its structures.
///
/// # Arguments
///
/// * `lines` - The body's lines, blanked ([`blank`]).
/// * `base` - The index of the body's first line in the whole text.
///
/// # Errors
///
/// The body does not nest, or holds a line the parser does not know.
pub(super) fn statements(lines: &[String], base: usize) -> Result<Vec<Stmt>, &'static str> {
    let mut p = Parser { lines, at: 0, base };
    let stmts = p.block(0)?;
    if p.peek().is_some() {
        return Err("text closes a block it never opened");
    }
    Ok(stmts)
}

/// Reads a line that opens no structure.
///
/// # Arguments
///
/// * `t` - The line, trimmed.
/// * `line` - Its number.
///
/// # Errors
///
/// The line opens or closes a structure, or jumps to no block.
fn simple(t: &str, line: usize) -> Result<Stmt, &'static str> {
    if t.ends_with('{') || t.starts_with('}') {
        return Err("structure where a statement belongs");
    }
    if let Some(target) = t.strip_prefix("goto ").and_then(|g| g.strip_suffix(';')) {
        return match target.strip_prefix("L_") {
            Some(h) => u64::from_str_radix(h, 16)
                .map(Stmt::Goto)
                .map_err(|_| "goto to no block"),
            None => Ok(Stmt::Halt(line)),
        };
    }
    Ok(match t {
        "break;" => Stmt::Break,
        "continue;" => Stmt::Continue,
        _ if super::is_return(t) => Stmt::Return(line),
        _ if t.ends_with("__builtin_trap();") => Stmt::Halt(line),
        _ => Stmt::Plain(line),
    })
}

/// The condition in the parentheses after `kw` on a line.
///
/// # Arguments
///
/// * `line` - The line, blanked.
/// * `kw` - What stands before the parenthesis: `if (` or `while (`.
///
/// # Returns
///
/// The text between the parentheses, or `None` when the line has no such
/// condition.
fn condition<'l>(line: &'l str, kw: &str) -> Option<&'l str> {
    let open = line.find(kw)? + kw.len() - 1;
    let close = matching_paren(line, open)?;
    line.get(open + 1..close)
}

/// Blanks the parts of a line no step can come from: the contents of its
/// string literals, and its comments.
///
/// # Arguments
///
/// * `line` - One line of the text.
pub(super) fn blank(line: &str) -> String {
    if !line.contains(['"', '/']) {
        return line.trim().to_owned();
    }
    let mut out = String::with_capacity(line.len());
    let mut chars = line.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '"' => {
                out.push('"');
                while let Some(s) = chars.next() {
                    if s == '\\' {
                        chars.next();
                        out.push_str("  ");
                    } else if s == '"' {
                        break;
                    } else {
                        out.push(' ');
                    }
                }
                out.push('"');
            }
            '/' if chars.peek() == Some(&'*') => {
                chars.next();
                out.push_str("  ");
                let mut star = false;
                for s in chars.by_ref() {
                    out.push(' ');
                    if star && s == '/' {
                        break;
                    }
                    star = s == '*';
                }
            }
            '/' if chars.peek() == Some(&'/') => break,
            other => out.push(other),
        }
    }
    out.trim().to_owned()
}

/// The calls a stretch of text makes, in the order they run: a call runs
/// once the parenthesis closing its arguments is reached, so an argument's
/// call runs first.
///
/// A name spelled through its import slot (`__imp_Beep`, as the text calls
/// an import from a wrapper named like it) is a call to that import.
///
/// # Arguments
///
/// * `t` - The stretch, blanked.
/// * `names` - The names the binary calls.
fn calls_in(t: &str, names: &Names) -> Vec<u32> {
    let mut found: Vec<(usize, u32)> = Vec::new();
    for (p, _) in t.match_indices('(') {
        let before = t.get(..p).unwrap_or("");
        let Some(last) = before.as_bytes().last() else {
            continue;
        };
        let best = names
            .by_last
            .get(last)
            .into_iter()
            .flatten()
            .filter_map(|&k| Some((k, names.name(k)?)))
            .filter(|(_, n)| {
                before.strip_suffix(*n).is_some_and(|head| {
                    let head = head.strip_suffix("__imp_").unwrap_or(head);
                    head.chars()
                        .next_back()
                        .is_none_or(|c| !(c.is_alphanumeric() || "_:~>.$@?".contains(c)))
                })
            })
            .max_by_key(|(_, n)| n.len());
        if let Some((k, _)) = best {
            found.push((matching_paren(t, p).unwrap_or(t.len()), k));
        }
    }
    found.sort_unstable();
    found.into_iter().map(|(_, n)| n).collect()
}

/// Builds the text's graph from its structures.
#[derive(Debug)]
struct Builder<'n> {
    /// The graph being built.
    g: Graph,
    /// The names the binary calls.
    names: &'n Names,
    /// The blanked body lines.
    lines: &'n [String],
    /// The first line of the body in the whole text.
    base: usize,
    /// Each label's nodes, by address: a block the text writes twice
    /// has its label twice, and a `goto` may land on either copy.
    labels: FxHashMap<u64, Vec<u32>>,
    /// The nodes a `goto` jumps from, and where to.
    gotos: Vec<(u32, u64)>,
    /// The block index of each block start.
    blocks: &'n FxHashMap<u64, u32>,
    /// The node every path that cannot return ends at.
    halt: u32,
}

impl Builder<'_> {
    /// The calls of a stretch of a body line, chained in front of `next`;
    /// a call that never returns ends the chain.
    ///
    /// # Arguments
    ///
    /// * `line` - The 1-based line number.
    /// * `part` - Which part of the line, or all of it.
    /// * `next` - The node after the calls.
    fn chain(&mut self, line: usize, part: Option<&str>, next: u32) -> u32 {
        let text = part.unwrap_or_else(|| {
            let whole = self
                .lines
                .get(line.saturating_sub(self.base + 1))
                .map_or("", String::as_str);
            condition(whole, "if (")
                .filter(|_| whole.starts_with("if ("))
                .map_or(whole, |c| whole.get(c.len() + 5..).unwrap_or(""))
        });
        let calls = calls_in(text, self.names);
        let site = u64::try_from(line).unwrap_or(0);
        let mut node = next;
        let mut ends = false;
        for &n in calls.iter().rev() {
            if !ends && self.names.noreturn.contains(&n) {
                node = self.halt;
                ends = true;
            }
            let name = self.names.name(n).unwrap_or("");
            let callee = if INTRINSICS.contains(&name) || self.names.dropped.contains(&n) {
                Callee::Maybe(Some(n))
            } else {
                Callee::Named(n)
            };
            node = self.g.add(Node::Call(callee, node), site);
        }
        node
    }

    /// The test a condition makes, its calls run as C runs them: the
    /// operands of a top-level `&&` or `||` one at a time, a later one only
    /// when the earlier ones left the outcome open.
    ///
    /// # Arguments
    ///
    /// * `line` - The 1-based line number.
    /// * `cond` - The condition.
    /// * `t` - Where the text goes when it holds.
    /// * `f` - Where it goes otherwise.
    ///
    /// # Returns
    ///
    /// The node that starts the test.
    fn test(&mut self, line: usize, cond: &str, t: u32, f: u32) -> u32 {
        let cond = cond.trim();
        let inner = cond
            .strip_prefix('(')
            .and_then(|r| r.strip_suffix(')'))
            .filter(|_| matching_paren(cond, 0) == Some(cond.len() - 1))
            .unwrap_or(cond);
        if let Some((op, parts)) = super::structure::logical_operands(inner) {
            let mut entry: Option<u32> = None;
            for part in parts.iter().rev() {
                entry = Some(match entry {
                    None => self.test(line, part, t, f),
                    Some(rest) if op == "||" => self.test(line, part, t, rest),
                    Some(rest) => self.test(line, part, rest, f),
                });
            }
            if let Some(e) = entry {
                return e;
            }
        }
        let go = self.g.add(Node::Go(vec![t, f]), 0);
        self.chain(line, Some(cond), go)
    }

    /// The condition of the structure that opens or closes on a line.
    ///
    /// # Arguments
    ///
    /// * `line` - The 1-based line number.
    /// * `kw` - What stands before its parenthesis: `if (` or `while (`.
    fn condition_at(&self, line: usize, kw: &str) -> String {
        self.lines
            .get(line.saturating_sub(self.base + 1))
            .and_then(|l| condition(l, kw))
            .unwrap_or("")
            .to_owned()
    }

    /// A silent node with no successor yet.
    fn hole(&mut self) -> u32 {
        self.g.add(Node::Go(Vec::new()), 0)
    }

    /// Points a silent node at its successors.
    ///
    /// # Arguments
    ///
    /// * `n` - The node.
    /// * `to` - Its successors.
    fn fill(&mut self, n: u32, to: Vec<u32>) {
        self.g.set_go(NodeIx(n), to);
    }

    /// Builds a run of statements in front of `next`.
    ///
    /// # Arguments
    ///
    /// * `stmts` - The statements.
    /// * `next` - Where the run continues.
    /// * `brk` - Where `break` goes.
    /// * `cont` - Where `continue` goes.
    ///
    /// # Errors
    ///
    /// A `break` or `continue` stands outside every loop, or a `for` header
    /// has no three parts.
    fn run(
        &mut self,
        stmts: &[Stmt],
        next: u32,
        brk: Option<u32>,
        cont: Option<u32>,
    ) -> Result<u32, &'static str> {
        let mut next = next;
        for s in stmts.iter().rev() {
            next = self.stmt(s, next, brk, cont)?;
        }
        Ok(next)
    }

    /// Builds one statement in front of `next`.
    ///
    /// # Arguments
    ///
    /// * `s` - The statement.
    /// * `next` - Where it continues.
    /// * `brk` - Where `break` goes.
    /// * `cont` - Where `continue` goes.
    ///
    /// # Errors
    ///
    /// A `break` or `continue` stands outside every loop, or a `for` header
    /// has no three parts.
    fn stmt(
        &mut self,
        s: &Stmt,
        next: u32,
        brk: Option<u32>,
        cont: Option<u32>,
    ) -> Result<u32, &'static str> {
        Ok(match s {
            Stmt::Label(addr, line) => {
                let site = u64::try_from(*line).unwrap_or(0);
                let node = match self.blocks.get(addr) {
                    Some(&b) => self.g.add(Node::Label(b, next), site),
                    None => self.g.add(Node::Go(vec![next]), site),
                };
                self.labels.entry(*addr).or_default().push(node);
                node
            }
            Stmt::Plain(line) => self.chain(*line, None, next),
            Stmt::If(line, then, other) => {
                let t = self.run(then, next, brk, cont)?;
                let f = self.run(other, next, brk, cont)?;
                let cond = self.condition_at(*line, "if (");
                self.test(*line, &cond, t, f)
            }
            Stmt::Loop(body) => {
                let head = self.hole();
                let entry = self.run(body, head, Some(next), Some(head))?;
                self.fill(head, vec![entry]);
                head
            }
            Stmt::While(line, body) => {
                let start = self.hole();
                let entry = self.run(body, start, Some(next), Some(start))?;
                let cond = self.condition_at(*line, "while (");
                let test = self.test(*line, &cond, entry, next);
                self.fill(start, vec![test]);
                start
            }
            Stmt::For(line, body) => {
                let header = self
                    .lines
                    .get(line.saturating_sub(self.base + 1))
                    .map_or(String::new(), Clone::clone);
                let inner = header
                    .strip_prefix("for (")
                    .and_then(|h| h.strip_suffix(") {"))
                    .unwrap_or("");
                let parts: Vec<&str> = inner.split("; ").collect();
                let [init, test_part, step] = parts.as_slice() else {
                    return Err("for header without three parts");
                };
                let start = self.hole();
                let inc = self.chain(*line, Some(step), start);
                let entry = self.run(body, inc, Some(next), Some(inc))?;
                let test = self.test(*line, test_part, entry, next);
                self.fill(start, vec![test]);
                self.chain(*line, Some(init), start)
            }
            Stmt::Do(body, line) => {
                let start = self.hole();
                let entry = self.run(body, start, Some(next), Some(start))?;
                let cond = self.condition_at(*line, "while (");
                let test = self.test(*line, &cond, entry, next);
                self.fill(start, vec![test]);
                entry
            }
            Stmt::Switch(line, arms) => {
                let mut follow = next;
                let mut entries = Vec::with_capacity(arms.len() + 1);
                for (_, _, body) in arms.iter().rev() {
                    follow = self.run(body, follow, Some(next), cont)?;
                    entries.push(follow);
                }
                let dispatch = if arms.iter().any(|(default, _, _)| *default) {
                    Node::Go(entries)
                } else {
                    Node::Switch(entries, next)
                };
                let dispatch = self.g.add(dispatch, 0);
                self.chain(*line, None, dispatch)
            }
            Stmt::Goto(addr) => {
                let jump = self.hole();
                self.gotos.push((jump, *addr));
                jump
            }
            Stmt::Break => self.g.add(
                Node::Go(vec![brk.ok_or("break outside a loop or switch")?]),
                0,
            ),
            Stmt::Continue => self
                .g
                .add(Node::Go(vec![cont.ok_or("continue outside a loop")?]), 0),
            Stmt::Return(line) => {
                let ret = self.g.add(Node::Ret, u64::try_from(*line).unwrap_or(0));
                self.chain(*line, None, ret)
            }
            Stmt::Halt(line) => self.chain(*line, None, self.halt),
            Stmt::Try(..) => return Err("a guarded region"),
        })
    }
}

/// The text's paths through its body.
///
/// # Arguments
///
/// * `text` - The decompiled function, header first.
/// * `names` - The names the binary calls.
/// * `blocks` - The block index of each block start.
///
/// # Returns
///
/// The graph and its entry, or why the text could not be read.
///
/// # Errors
///
/// The text does not parse, or a `goto` names a label it lacks.
fn text_graph(
    text: &str,
    names: &Names,
    blocks: &FxHashMap<u64, u32>,
) -> Result<(Graph, u32), &'static str> {
    let all: Vec<&str> = text.lines().collect();
    let base = all
        .iter()
        .position(|l| l.trim().is_empty())
        .map_or(0, |i| i + 1);
    let lines: Vec<String> = all
        .get(base..)
        .unwrap_or(&[])
        .iter()
        .map(|l| blank(l))
        .collect();
    let stmts = statements(&lines, base)?;
    let mut b = Builder {
        g: Graph::default(),
        names,
        lines: &lines,
        base,
        labels: FxHashMap::default(),
        gotos: Vec::new(),
        blocks,
        halt: 0,
    };
    b.halt = b.g.add(Node::Halt, 0);
    let end = b.g.add(Node::Ret, u64::try_from(all.len()).unwrap_or(0));
    let entry = b.run(&stmts, end, None, None)?;
    for (jump, addr) in std::mem::take(&mut b.gotos) {
        let to = b
            .labels
            .get(&addr)
            .ok_or("goto to a label the text lacks")?
            .clone();
        b.fill(jump, to);
    }
    Ok((b.g, entry))
}

/// What a side can do next from a set of places, before any step a reader
/// sees.
#[derive(Debug, Default)]
struct Reach {
    /// The calls it can make next, and where each leaves it.
    calls: Vec<(Callee, u32)>,
    /// It can return.
    ret: bool,
    /// It can stop without returning.
    halt: bool,
}

/// One side of the check, walked as a set of places at once.
#[derive(Debug)]
struct Places<'g> {
    /// Its graph.
    g: &'g Graph,
    /// What each set of places reaches, computed once.
    cache: FxHashMap<Vec<u32>, Rc<Reach>>,
}

impl Places<'_> {
    /// What the side can do next from `from`, spending fuel on every node
    /// the walk visits.
    ///
    /// A silent step, a label and a call the binary makes through a
    /// pointer (which the text may not show) are passed through.
    ///
    /// # Arguments
    ///
    /// * `from` - The places, sorted.
    /// * `fuel` - What the walk may still spend.
    ///
    /// # Returns
    ///
    /// The reach, or `None` once the fuel runs out.
    fn reach(&mut self, from: &[u32], fuel: &mut usize) -> Option<Rc<Reach>> {
        if let Some(r) = self.cache.get(from) {
            return Some(Rc::clone(r));
        }
        let mut seen: FxHashSet<u32> = FxHashSet::default();
        let mut stack: Vec<u32> = from.to_vec();
        let mut r = Reach::default();
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            *fuel = fuel.checked_sub(1)?;
            match self.g.node(NodeIx(n)).unwrap_or(&Node::Halt) {
                Node::Call(c, next) => {
                    r.calls.push((*c, *next));
                    if matches!(c, Callee::Maybe(_)) {
                        stack.push(*next);
                    }
                }
                Node::Ret => r.ret = true,
                Node::Halt => r.halt = true,
                Node::Go(to) => stack.extend(to.iter().copied()),
                Node::Switch(to, out) => {
                    stack.extend(to.iter().copied());
                    stack.push(*out);
                }
                Node::Label(_, next) => stack.push(*next),
            }
        }
        r.calls.sort_unstable();
        r.calls.dedup();
        let r = Rc::new(r);
        self.cache.insert(from.to_vec(), Rc::clone(&r));
        Some(r)
    }

    /// Tells whether the side can be at `target` from `from` without a
    /// step a reader sees.
    ///
    /// # Arguments
    ///
    /// * `from` - The places.
    /// * `target` - The node.
    /// * `fuel` - What the walk may still spend.
    fn reaches(&self, from: &[u32], target: u32, fuel: &mut usize) -> Option<bool> {
        let mut seen: FxHashSet<u32> = FxHashSet::default();
        let mut stack: Vec<u32> = from.to_vec();
        while let Some(n) = stack.pop() {
            if n == target {
                return Some(true);
            }
            if !seen.insert(n) {
                continue;
            }
            *fuel = fuel.checked_sub(1)?;
            match self.g.node(NodeIx(n)).unwrap_or(&Node::Halt) {
                Node::Call(Callee::Maybe(_), next) | Node::Label(_, next) => stack.push(*next),
                Node::Go(to) => stack.extend(to.iter().copied()),
                Node::Switch(to, out) => {
                    stack.extend(to.iter().copied());
                    stack.push(*out);
                }
                Node::Call(Callee::Named(_), _) | Node::Ret | Node::Halt => {}
            }
        }
        Some(false)
    }
}

/// The last observable steps of a path, oldest first, with `n` taken.
///
/// # Arguments
///
/// * `last` - The steps so far.
/// * `n` - The step taken.
fn step(last: [u32; 3], n: u32) -> [u32; 3] {
    [last[1], last[2], n]
}

/// Sorts and deduplicates a set of places.
///
/// # Arguments
///
/// * `v` - The places.
fn settled(mut v: Vec<u32>) -> Rc<[u32]> {
    v.sort_unstable();
    v.dedup();
    Rc::from(v)
}

/// Walks every path of `a` and follows each on `b`.
///
/// `a` is walked a path at a time and `b` as the set of places it may be
/// at (each pair once), so a step of `a` that no place of `b` can take is
/// a path `a` has and `b` lacks; a `b` that may stop there instead takes
/// it as its own end and claims nothing past it. With `heads`, a label of
/// `a` is a place of `b`: `b` must reach that block's first node silently,
/// and is there afterwards.
///
/// # Arguments
///
/// * `a` - The side whose paths are walked, and its entry.
/// * `b` - The side that must follow them, and its entry.
/// * `heads` - `b`'s first node of each block and its address, when
///   `a`'s labels name them.
/// * `side` - Which side `a` is.
/// * `names` - The callees' names, for the report.
///
/// # Returns
///
/// The first path `b` cannot follow, `None` when it follows all, or why
/// the walk stopped short.
///
/// # Errors
///
/// The walk runs out of fuel.
fn included(
    (a, a_entry): (&Graph, u32),
    (b, b_entry): (&Graph, u32),
    heads: Option<&[(u32, u64)]>,
    side: Side,
    names: &Names,
) -> Result<Option<Disagreement>, &'static str> {
    let mut fuel = FUEL;
    let mut places = Places {
        g: b,
        cache: FxHashMap::default(),
    };
    let mut seen: FxHashSet<(u32, Rc<[u32]>)> = FxHashSet::default();
    let mut work: Vec<(u32, Rc<[u32]>, [u32; 3])> =
        vec![(a_entry, Rc::from([b_entry]), [u32::MAX; 3])];
    let report = |at: u32, last: [u32; 3], step: String, r: &Reach, from: &[u32]| {
        let mut other: Vec<String> = r
            .calls
            .iter()
            .filter_map(|(c, _)| match c {
                Callee::Named(n) | Callee::Maybe(Some(n)) => {
                    names.name(*n).map(|s| format!("call {s}"))
                }
                Callee::Maybe(None) => None,
            })
            .take(4)
            .collect();
        if r.ret {
            other.push("return".to_owned());
        }
        let near: Vec<String> = from
            .iter()
            .take(4)
            .map(|n| format!("{:#x}", b.site(NodeIx(*n)).unwrap_or(0)))
            .collect();
        other.push(format!("from {}", near.join(" ")));
        let trail: Vec<String> = last
            .iter()
            .filter_map(|n| a.site(NodeIx(*n)))
            .map(|s| format!("{s:#x}"))
            .collect();
        if !trail.is_empty() {
            other.push(format!("after {}", trail.join(" ")));
        }
        Disagreement {
            side,
            at: a.site(NodeIx(at)).unwrap_or(0),
            step,
            other,
        }
    };
    while let Some((n, from, last)) = work.pop() {
        fuel = fuel.checked_sub(1).ok_or("out of fuel")?;
        if !seen.insert((n, Rc::clone(&from))) {
            continue;
        }
        match a.node(NodeIx(n)).unwrap_or(&Node::Halt) {
            Node::Go(to) | Node::Switch(to, _) => {
                work.extend(to.iter().map(|t| (*t, Rc::clone(&from), last)));
            }
            Node::Halt => {}
            Node::Label(block, next) => {
                let Some(heads) = heads else {
                    work.push((*next, from, last));
                    continue;
                };
                let (head, addr) = heads
                    .get(usize::try_from(*block).unwrap_or(usize::MAX))
                    .copied()
                    .unwrap_or((u32::MAX, 0));
                if places
                    .reaches(&from, head, &mut fuel)
                    .ok_or("out of fuel")?
                {
                    work.push((*next, Rc::from([head]), step(last, n)));
                    continue;
                }
                let r = places.reach(&from, &mut fuel).ok_or("out of fuel")?;
                if !r.halt {
                    let step = format!("label L_{addr:x}");
                    return Ok(Some(report(n, last, step, &r, &from)));
                }
            }
            Node::Call(c, next) => {
                let r = places.reach(&from, &mut fuel).ok_or("out of fuel")?;
                let mut to: Vec<u32> = r
                    .calls
                    .iter()
                    .filter(|(o, _)| c.meets(*o))
                    .map(|(_, t)| *t)
                    .collect();
                if let Callee::Maybe(_) = c {
                    to.extend(from.iter().copied());
                } else if to.is_empty() && !r.halt {
                    let Callee::Named(k) = c else { continue };
                    let name = names.name(*k).unwrap_or("?");
                    return Ok(Some(report(n, last, format!("call {name}"), &r, &from)));
                }
                if !to.is_empty() {
                    work.push((*next, settled(to), step(last, n)));
                }
            }
            Node::Ret => {
                let r = places.reach(&from, &mut fuel).ok_or("out of fuel")?;
                if !r.ret && !r.halt {
                    return Ok(Some(report(n, last, "return".to_owned(), &r, &from)));
                }
            }
        }
    }
    Ok(None)
}

/// Checks a function's decompiled text against the graph its structurer
/// was handed.
///
/// Every path of the text must be a path of the binary and every path of
/// the binary one of the text, up to the calls the code names, the returns
/// and the labels.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names the text was written under.
/// * `entry` - The function's entry.
/// * `text` - Its text, header first, as a decompile entry point wrote it.
/// * `live` - The graph its structurer was handed.
///
/// # Returns
///
/// The verdict: agreement, the first path one side has and the other
/// lacks, or why the check did not run to the end.
#[must_use]
pub fn check(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: &str,
    live: &LiveCfg,
) -> Structure {
    let Some(f) = analysis.function(entry) else {
        return Structure::Unchecked("no function starts there");
    };
    let notes: Vec<&str> = text
        .lines()
        .take_while(|l| l.starts_with("//"))
        .filter(|l| l.starts_with("// note: ") || l.starts_with("// folded: "))
        .collect();
    let mut names = Names::default();
    let (mut bin, heads) = binary_graph(program, analysis, overlay, f, live, &notes, &mut names);
    let blocks: FxHashMap<u64, u32> = f
        .blocks
        .iter()
        .enumerate()
        .filter_map(|(i, b)| Some((b.start, u32::try_from(i).ok()?)))
        .collect();
    let Some(&bin_entry) = blocks
        .get(&f.entry)
        .and_then(|b| heads.get(usize::try_from(*b).unwrap_or(usize::MAX)))
    else {
        return Structure::Unchecked("the entry starts no block");
    };
    let (mut txt, txt_entry) = match text_graph(text, &names, &blocks) {
        Ok(g) => g,
        Err(why) => return Structure::Unchecked(why),
    };
    let past = |to: &[u32], n: u32| to.get(NodeIx(n).pos()).copied().unwrap_or(n);
    let (bin_to, txt_to) = (bin.compress(), txt.compress());
    let heads: Vec<(u32, u64)> = heads
        .iter()
        .zip(&f.blocks)
        .map(|(h, b)| (past(&bin_to, *h), b.start))
        .collect();
    let (bin_entry, txt_entry) = (past(&bin_to, bin_entry), past(&txt_to, txt_entry));
    let claims = included(
        (&txt, txt_entry),
        (&bin, bin_entry),
        Some(&heads),
        Side::Text,
        &names,
    );
    let misses = || {
        included(
            (&bin, bin_entry),
            (&txt, txt_entry),
            None,
            Side::Binary,
            &names,
        )
    };
    match claims.and_then(|c| match c {
        Some(d) => Ok(Some(d)),
        None => misses(),
    }) {
        Ok(None) => Structure::Agrees,
        Ok(Some(d)) => Structure::Disagrees(Box::new(d)),
        Err(why) => Structure::Unchecked(why),
    }
}

/// Checks one function's text as [`decompile`](super::decompile) or
/// [`decompile_named`](super::decompile_named) wrote it, against the graph
/// the memoized decompilation's structurer was handed.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names the text was written under.
/// * `entry` - The function's entry.
/// * `text` - The text.
///
/// # Returns
///
/// The verdict of [`check`]; unchecked when the function does not
/// decompile.
#[must_use]
pub fn check_structure(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: &str,
) -> Structure {
    let d = decompiled_cached(program, analysis, overlay, overlay.fingerprint(), entry);
    match d.as_ref() {
        Some(d) => check(program, analysis, overlay, entry, text, &d.live),
        None => Structure::Unchecked("the function does not decompile"),
    }
}

/// Decompiles many functions as [`decompile_named_all`](super::decompile_named_all)
/// does, each with the graph its structurer was handed, one stripe of them
/// per core.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names to apply.
/// * `entries` - Function entries, in any order.
///
/// # Returns
///
/// One result per entry, in order: the text and its graph, or `None` where
/// the function does not decompile.
#[must_use]
pub fn decompile_with_cfg_all(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entries: &[u64],
) -> Vec<Option<(String, LiveCfg)>> {
    striped(entries, |&e| {
        let d = decompile_plain_full(program, analysis, overlay, e)?;
        let text = name_fields(program, analysis, overlay, e, &d.text)?;
        Some((text, d.live))
    })
    .into_iter()
    .map(Option::flatten)
    .collect()
}

/// Checks many functions' texts, one stripe of them per core.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names the texts were written under.
/// * `entries` - The functions' entries.
/// * `texts` - Each one's text and graph, as
///   [`decompile_with_cfg_all`] returns them.
///
/// # Returns
///
/// One verdict per entry, in order, `None` where there is no text.
#[must_use]
pub fn check_all(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entries: &[u64],
    texts: &[Option<(String, LiveCfg)>],
) -> Vec<Option<Structure>> {
    let items: Vec<(u64, Option<&(String, LiveCfg)>)> = entries
        .iter()
        .copied()
        .zip(texts.iter().map(Option::as_ref))
        .collect();
    striped(&items, |(e, t)| {
        t.map(|(text, live)| check(program, analysis, overlay, *e, text, live))
    })
    .into_iter()
    .map(Option::flatten)
    .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A call written through its import slot is the call to that import,
    /// and a longer name ending in the callee's is not.
    ///
    /// # Panics
    ///
    /// When the calls read differ.
    #[test]
    fn a_call_through_its_import_slot_is_the_import() {
        let mut names = Names::default();
        let k = names.intern("_set_app_type");
        assert_eq!(calls_in("return __imp__set_app_type(a1);", &names), vec![k]);
        assert_eq!(calls_in("return _set_app_type(a1);", &names), vec![k]);
        assert!(calls_in("return my_set_app_type(a1);", &names).is_empty());
        assert!(calls_in("return x__imp__set_app_type(a1);", &names).is_empty());
    }
}
