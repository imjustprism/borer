//! An e-graph over a MIR body's values: equality saturation for readable
//! idioms.
//!
//! An e-class is a set of MIR operations ([`Inst`]) that compute the same
//! bits, and an e-node is an [`Inst`] whose operands ([`Val`]) name
//! e-classes rather than body values. Every MIR op is a pure function of
//! the block's entry state (a load reads memory as it was where the block
//! started), so a whole body goes in. [`Rule`]s add equal forms, each one
//! checked against the MIR evaluator in the tests, and extraction picks
//! the form of least readability cost ([`cost`]).
//!
//! The graph is deterministic by construction: classes are numbered in
//! insertion order, a union keeps the smaller id, rules run in the fixed
//! order of [`Rule::ALL`] over the classes in id order, and extraction
//! breaks a tie of cost by the earlier node of a class. The hash map is
//! only ever looked up, never iterated. Growth stops at [`GROWTH`] times
//! the input's nodes or after [`ITERATIONS`] rounds, whichever comes
//! first.
//!
//! Nothing in the decompile's output reads it: [`simplify`] is an opt-in
//! pass the tests and the measurement sweep call.

mod rules;
#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod sweep;
#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests;

pub(in super::super) use rules::Rule;

use super::{Body, Inst, MTy, Prov, Val};
use crate::fxmap::FxHashMap;

/// The most rounds of rule application before extraction.
const ITERATIONS: usize = 8;

/// The most e-nodes a graph holds, as a multiple of its input's nodes.
const GROWTH: usize = 4;

/// The cost of a cast: a width change or a reinterpretation.
const CAST: u32 = 3;

/// The cost of a constant that is neither small, a power of two, a mask
/// nor a sign bit: a magic number the reader has to decode.
const MAGIC: u32 = 4;

/// The cost of the high half of a wide product, which C spells as a
/// helper over a double-width multiply.
const WIDE: u32 = 4;

/// The largest constant that reads as a plain number.
const SMALL: u64 = 255;

/// One e-class: the equal forms of a value.
#[derive(Debug, Clone)]
struct Class {
    /// The e-nodes, in the order they joined; operands are class ids.
    nodes: Vec<Inst>,
    /// The type every form has.
    ty: MTy,
    /// The provenance of the first form, which every form inherits.
    prov: Prov,
}

/// An e-graph of MIR values.
#[derive(Debug, Clone)]
pub(in super::super) struct EGraph {
    /// The machine word's width.
    word: u8,
    /// The union-find parent of each class, by id; a root is its own.
    parent: Vec<Val>,
    /// The classes by id; only a root's entry is current.
    classes: Vec<Class>,
    /// Each canonical e-node's class.
    memo: FxHashMap<Inst, Val>,
    /// The e-nodes held, over every root class.
    count: usize,
    /// The most e-nodes [`EGraph::add`] lets the graph hold.
    budget: usize,
}

/// What [`simplify`] made of one value.
#[derive(Debug, Clone)]
pub(in super::super) struct Simplified {
    /// The extracted form, in a body of its own.
    pub(in super::super) body: Body,
    /// The value in [`Simplified::body`].
    pub(in super::super) root: Val,
    /// The extracted form's readability cost.
    pub(in super::super) cost: u32,
    /// The input form's readability cost.
    pub(in super::super) input_cost: u32,
}

/// Returns the operands of an operation.
///
/// # Arguments
///
/// * `inst` - The operation.
fn operands(inst: &Inst) -> Vec<Val> {
    match inst {
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Undef(_) => Vec::new(),
        Inst::Load { addr, .. } => vec![*addr],
        Inst::Bin { l, r, .. }
        | Inst::Ovf { l, r, .. }
        | Inst::Wide { l, r, .. }
        | Inst::FBin { l, r, .. }
        | Inst::ICmp { l, r, .. }
        | Inst::FCmp { l, r, .. } => vec![*l, *r],
        Inst::Un { x, .. }
        | Inst::Ext { x, .. }
        | Inst::Trunc { x, .. }
        | Inst::Bitcast { x, .. }
        | Inst::Convert { x, .. }
        | Inst::FUn { x, .. }
        | Inst::Splat { x, .. } => vec![*x],
        Inst::Select { c, t, f } => vec![*c, *t, *f],
        Inst::Helper { args, .. } => args.clone(),
    }
}

/// Returns an operation with each operand mapped.
///
/// # Arguments
///
/// * `inst` - The operation.
/// * `f` - Maps one operand.
fn remap(inst: &Inst, mut f: impl FnMut(Val) -> Val) -> Inst {
    let mut out = inst.clone();
    match &mut out {
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Undef(_) => {}
        Inst::Load { addr, .. } => *addr = f(*addr),
        Inst::Bin { l, r, .. }
        | Inst::Ovf { l, r, .. }
        | Inst::Wide { l, r, .. }
        | Inst::FBin { l, r, .. }
        | Inst::ICmp { l, r, .. }
        | Inst::FCmp { l, r, .. } => {
            *l = f(*l);
            *r = f(*r);
        }
        Inst::Un { x, .. }
        | Inst::Ext { x, .. }
        | Inst::Trunc { x, .. }
        | Inst::Bitcast { x, .. }
        | Inst::Convert { x, .. }
        | Inst::FUn { x, .. }
        | Inst::Splat { x, .. } => *x = f(*x),
        Inst::Select { c, t, f: e } => {
            *c = f(*c);
            *t = f(*t);
            *e = f(*e);
        }
        Inst::Helper { args, .. } => {
            for a in args.iter_mut() {
                *a = f(*a);
            }
        }
    }
    out
}

/// Tells whether a constant reads as a plain number: small, small
/// negated, a power of two, a low mask or a sign bit.
///
/// # Arguments
///
/// * `w` - The constant's width.
/// * `bits` - Its bits.
fn plain(w: u8, bits: u64) -> bool {
    let m = super::super::verify::low(w);
    let neg = bits.wrapping_neg() & m;
    bits <= SMALL
        || neg <= SMALL
        || bits.is_power_of_two()
        || bits.wrapping_add(1) & bits == 0
        || (!bits & m).wrapping_add(1) & (!bits & m) == 0
}

/// Returns the readability cost of one operation, not counting its
/// operands.
///
/// Fewer nodes cost less, every cast costs [`CAST`], a magic constant
/// [`MAGIC`] and a wide product [`WIDE`]; a named helper (`min`, `llabs`)
/// costs one node, less than the operators it stands for.
///
/// # Arguments
///
/// * `inst` - The operation.
pub(in super::super) fn cost(inst: &Inst) -> u32 {
    match inst {
        Inst::Const { w, bits } => {
            if plain(*w, *bits) {
                1
            } else {
                MAGIC
            }
        }
        Inst::Ext { .. } | Inst::Trunc { .. } | Inst::Bitcast { .. } | Inst::Convert { .. } => CAST,
        Inst::Wide { .. } => WIDE,
        Inst::Select { .. } | Inst::Ovf { .. } | Inst::Splat { .. } => 2,
        Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Bin { .. }
        | Inst::Un { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => 1,
    }
}

/// Returns the index of a value.
///
/// # Arguments
///
/// * `v` - The value.
fn index(v: Val) -> usize {
    usize::try_from(v.0).unwrap_or(usize::MAX)
}

/// Returns the value of an index.
///
/// # Arguments
///
/// * `i` - The index.
fn val(i: usize) -> Val {
    Val(u32::try_from(i).unwrap_or(u32::MAX))
}

impl EGraph {
    /// Starts an empty graph.
    ///
    /// # Arguments
    ///
    /// * `word` - The machine word's width.
    /// * `budget` - The most e-nodes it may hold.
    fn new(word: u8, budget: usize) -> Self {
        Self {
            word,
            parent: Vec::new(),
            classes: Vec::new(),
            memo: FxHashMap::default(),
            count: 0,
            budget,
        }
    }

    /// Seeds a graph with the values one value of a body reads.
    ///
    /// # Arguments
    ///
    /// * `body` - The body.
    /// * `root` - The value.
    ///
    /// # Returns
    ///
    /// The graph, with a budget of [`GROWTH`] times the values read, and
    /// the root's class; `None` for a value of another body.
    pub(in super::super) fn seed(body: &Body, root: Val) -> Option<(Self, Val)> {
        let top = index(root);
        body.nodes.get(top)?;
        let mut live = vec![false; top + 1];
        if let Some(l) = live.get_mut(top) {
            *l = true;
        }
        for i in (0..=top).rev() {
            if !live.get(i).copied().unwrap_or(false) {
                continue;
            }
            for v in body
                .nodes
                .get(i)
                .map(|n| operands(&n.inst))
                .unwrap_or_default()
            {
                if let Some(l) = live.get_mut(index(v)) {
                    *l = true;
                }
            }
        }
        let read = live.iter().filter(|&&l| l).count();
        let mut g = Self::new(body.word, read.saturating_mul(GROWTH));
        let mut class = vec![val(0); top + 1];
        for (i, node) in body.nodes.iter().enumerate().take(top + 1) {
            if !live.get(i).copied().unwrap_or(false) {
                continue;
            }
            let inst = remap(&node.inst, |v| class.get(index(v)).copied().unwrap_or(v));
            let id = g.add(inst, node.ty, node.prov)?;
            if let Some(c) = class.get_mut(i) {
                *c = id;
            }
        }
        let id = class.get(top).copied()?;
        Some((g, id))
    }

    /// Returns the root class of a class.
    ///
    /// # Arguments
    ///
    /// * `v` - The class id.
    pub(in super::super) fn find(&self, mut v: Val) -> Val {
        while let Some(&p) = self.parent.get(index(v)) {
            if p == v {
                break;
            }
            v = p;
        }
        v
    }

    /// Tells whether two classes are one.
    ///
    /// # Arguments
    ///
    /// * `a` - One class.
    /// * `b` - The other.
    pub(in super::super) fn same(&self, a: Val, b: Val) -> bool {
        self.find(a) == self.find(b)
    }

    /// Returns a class's forms.
    ///
    /// # Arguments
    ///
    /// * `v` - The class id.
    pub(in super::super) fn nodes(&self, v: Val) -> &[Inst] {
        self.classes
            .get(index(self.find(v)))
            .map_or(&[], |c| c.nodes.as_slice())
    }

    /// Returns a class's type, [`MTy::I`] of 64 bits for an unknown id.
    ///
    /// # Arguments
    ///
    /// * `v` - The class id.
    pub(in super::super) fn ty(&self, v: Val) -> MTy {
        self.classes
            .get(index(self.find(v)))
            .map_or(MTy::I(64), |c| c.ty)
    }

    /// Returns the machine word's width.
    pub(in super::super) fn word(&self) -> u8 {
        self.word
    }

    /// Returns the integer constant a class holds.
    ///
    /// # Arguments
    ///
    /// * `v` - The class id.
    ///
    /// # Returns
    ///
    /// The constant's bits, or `None` when no form is a constant.
    pub(in super::super) fn konst(&self, v: Val) -> Option<u64> {
        self.nodes(v).iter().find_map(|n| match n {
            Inst::Const { bits, .. } => Some(*bits),
            Inst::FConst { .. }
            | Inst::Reg(_)
            | Inst::Frame(_)
            | Inst::Tls
            | Inst::Load { .. }
            | Inst::Bin { .. }
            | Inst::Ovf { .. }
            | Inst::Wide { .. }
            | Inst::Un { .. }
            | Inst::Ext { .. }
            | Inst::Trunc { .. }
            | Inst::Bitcast { .. }
            | Inst::Convert { .. }
            | Inst::FBin { .. }
            | Inst::FUn { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Select { .. }
            | Inst::Splat { .. }
            | Inst::Helper { .. }
            | Inst::Undef(_) => None,
        })
    }

    /// Returns the provenance of a class.
    ///
    /// # Arguments
    ///
    /// * `v` - The class id.
    pub(in super::super) fn prov(&self, v: Val) -> Prov {
        self.classes
            .get(index(self.find(v)))
            .map_or(Prov::ENTRY, |c| c.prov)
    }

    /// Adds a form, or finds the class that already holds it.
    ///
    /// # Arguments
    ///
    /// * `inst` - The form, its operands class ids.
    /// * `ty` - Its type.
    /// * `prov` - Where it came from.
    ///
    /// # Returns
    ///
    /// Its class, or `None` when a new form would pass the budget.
    pub(in super::super) fn add(&mut self, inst: Inst, ty: MTy, prov: Prov) -> Option<Val> {
        let inst = remap(&inst, |v| self.find(v));
        if let Some(&id) = self.memo.get(&inst) {
            return Some(self.find(id));
        }
        if self.count >= self.budget {
            return None;
        }
        let id = val(self.classes.len());
        self.memo.insert(inst.clone(), id);
        self.parent.push(id);
        self.classes.push(Class {
            nodes: vec![inst],
            ty,
            prov,
        });
        self.count += 1;
        Some(id)
    }

    /// Joins two classes, the smaller id the root.
    ///
    /// # Arguments
    ///
    /// * `a` - One class.
    /// * `b` - The other.
    ///
    /// # Returns
    ///
    /// Whether they were apart.
    fn union(&mut self, a: Val, b: Val) -> bool {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return false;
        }
        let (root, child) = if a < b { (a, b) } else { (b, a) };
        let moved = self
            .classes
            .get_mut(index(child))
            .map(|c| std::mem::take(&mut c.nodes))
            .unwrap_or_default();
        if let Some(c) = self.classes.get_mut(index(root)) {
            c.nodes.extend(moved);
        }
        if let Some(p) = self.parent.get_mut(index(child)) {
            *p = root;
        }
        true
    }

    /// Restores the graph's invariants after unions: every form's
    /// operands canonical, no form twice, and two classes holding one
    /// form joined, until nothing changes.
    fn rebuild(&mut self) {
        loop {
            self.memo.clear();
            let mut joins = Vec::new();
            let mut count = 0;
            for i in 0..self.classes.len() {
                let id = val(i);
                if self.find(id) != id {
                    continue;
                }
                let nodes = self
                    .classes
                    .get_mut(i)
                    .map(|c| std::mem::take(&mut c.nodes))
                    .unwrap_or_default();
                let mut kept: Vec<Inst> = Vec::with_capacity(nodes.len());
                for n in nodes {
                    let n = remap(&n, |v| self.find(v));
                    if kept.contains(&n) {
                        continue;
                    }
                    match self.memo.get(&n) {
                        Some(&other) if other != id => joins.push((other, id)),
                        Some(_) => {}
                        None => {
                            self.memo.insert(n.clone(), id);
                        }
                    }
                    kept.push(n);
                }
                count += kept.len();
                if let Some(c) = self.classes.get_mut(i) {
                    c.nodes = kept;
                }
            }
            self.count = count;
            let mut joined = false;
            for (a, b) in joins {
                joined |= self.union(a, b);
            }
            if !joined {
                return;
            }
        }
    }

    /// Applies rules until none adds anything, the budget is spent or
    /// [`ITERATIONS`] rounds have run.
    ///
    /// Each round reads the forms as they stood at its start, applies the
    /// rules in their order to each in class order, and joins what they
    /// found at its end.
    ///
    /// # Arguments
    ///
    /// * `rules` - The rules, applied in this order.
    pub(in super::super) fn saturate(&mut self, rules: &[Rule]) {
        for _ in 0..ITERATIONS {
            let snapshot: Vec<(Val, Inst)> = (0..self.classes.len())
                .map(val)
                .filter(|&id| self.find(id) == id)
                .flat_map(|id| self.nodes(id).iter().map(move |n| (id, n.clone())))
                .collect::<Vec<_>>();
            let before = self.count;
            let mut found = Vec::new();
            'rules: for rule in rules {
                for (id, node) in &snapshot {
                    if self.count >= self.budget {
                        break 'rules;
                    }
                    if let Some(new) = rule.apply(self, *id, node) {
                        found.push((*id, new));
                    }
                }
            }
            let mut joined = false;
            for (a, b) in found {
                joined |= self.union(a, b);
            }
            self.rebuild();
            if !joined && self.count == before {
                return;
            }
        }
    }

    /// Picks each class's cheapest form.
    ///
    /// # Returns
    ///
    /// For each class id, the cost of its cheapest form and that form's
    /// index in the class, or `None` for a class no finite form reaches
    /// or one that is not a root.
    fn best(&self) -> Vec<Option<(u32, usize)>> {
        let mut best: Vec<Option<(u32, usize)>> = vec![None; self.classes.len()];
        let mut changed = true;
        while changed {
            changed = false;
            for (i, class) in self.classes.iter().enumerate() {
                if self.find(val(i)) != val(i) {
                    continue;
                }
                for (k, n) in class.nodes.iter().enumerate() {
                    let mut total = cost(n);
                    let mut known = true;
                    for v in operands(n) {
                        match best.get(index(self.find(v))).copied().flatten() {
                            Some((c, _)) => total = total.saturating_add(c),
                            None => known = false,
                        }
                    }
                    let cur = best.get(i).copied().flatten();
                    if known && cur.is_none_or(|(c, _)| total < c) {
                        if let Some(b) = best.get_mut(i) {
                            *b = Some((total, k));
                        }
                        changed = true;
                    }
                }
            }
        }
        best
    }

    /// Writes a class's cheapest form into a new body.
    ///
    /// # Arguments
    ///
    /// * `root` - The class.
    /// * `provs` - The provenance table of the body the graph was seeded
    ///   from, which the new body keeps.
    ///
    /// # Returns
    ///
    /// The body, the value and its cost, or `None` when no finite form
    /// reaches the class.
    pub(in super::super) fn extract(
        &self,
        root: Val,
        provs: &[Vec<u64>],
    ) -> Option<(Body, Val, u32)> {
        let best = self.best();
        let root = self.find(root);
        let (total, _) = best.get(index(root)).copied().flatten()?;
        let mut body = Body::new(self.word);
        body.provs = provs.to_vec();
        let mut emitted: Vec<Option<Val>> = vec![None; self.classes.len()];
        let mut stack = vec![(root, false)];
        while let Some((c, ready)) = stack.pop() {
            if emitted.get(index(c)).copied().flatten().is_some() {
                continue;
            }
            let (_, k) = best.get(index(c)).copied().flatten()?;
            let node = self.classes.get(index(c))?.nodes.get(k)?;
            if ready {
                let inst = remap(node, |v| {
                    emitted
                        .get(index(self.find(v)))
                        .copied()
                        .flatten()
                        .unwrap_or(v)
                });
                let v = body.push(inst, self.ty(c), self.prov(c));
                if let Some(e) = emitted.get_mut(index(c)) {
                    *e = Some(v);
                }
            } else {
                stack.push((c, true));
                for v in operands(node).into_iter().rev() {
                    stack.push((self.find(v), false));
                }
            }
        }
        let v = emitted.get(index(root)).copied().flatten()?;
        Some((body, v, total))
    }
}

/// Returns the readability cost of one value of a body as a tree.
///
/// # Arguments
///
/// * `body` - The body.
/// * `v` - The value.
pub(in super::super) fn tree_cost(body: &Body, v: Val) -> u32 {
    let mut memo: Vec<Option<u32>> = vec![None; body.nodes.len()];
    for (i, node) in body.nodes.iter().enumerate().take(index(v) + 1) {
        let total = operands(&node.inst)
            .into_iter()
            .fold(cost(&node.inst), |t, o| {
                t.saturating_add(memo.get(index(o)).copied().flatten().unwrap_or(0))
            });
        if let Some(m) = memo.get_mut(i) {
            *m = Some(total);
        }
    }
    memo.get(index(v)).copied().flatten().unwrap_or(0)
}

/// Simplifies one value of a body with the rules given.
///
/// # Arguments
///
/// * `body` - The body.
/// * `root` - The value.
/// * `rules` - The rules enabled, applied in this order; [`Rule::ALL`] for
///   every one.
///
/// # Returns
///
/// The cheapest form found, or `None` for a value of another body.
pub(in super::super) fn simplify(body: &Body, root: Val, rules: &[Rule]) -> Option<Simplified> {
    let (mut g, id) = EGraph::seed(body, root)?;
    g.saturate(rules);
    let (out, v, cost) = g.extract(id, &body.provs)?;
    Some(Simplified {
        body: out,
        root: v,
        cost,
        input_cost: tree_cost(body, root),
    })
}
