//! A compare tree over one value written as a `switch`.
//!
//! A `switch` a compiler did not turn into a jump table (sparse values, a
//! `sub`/`je` ladder, a balanced tree of `cmp`s) is a tree of pure
//! conditional blocks that all test the same value: `v == K` picks a body,
//! `v <= K` splits the remaining values between two subtrees, and whatever
//! matches nothing lands in one residual block, the default. Read back as
//! nested `if`s the bodies sit at every depth with gotos between them; as
//! a `switch` they sit side by side under their values.

use super::*;

/// Fewest case bodies a tree needs before it reads better as a `switch`;
/// with fewer, an `if`/`else if` chain says the same in fewer lines.
const LADDER_MIN_CASES: usize = 3;

/// Most compare blocks a tree may have.
const LADDER_MAX_NODES: usize = 64;

/// What one block of the tree tests about the value.
enum Test {
    /// `v == k` at this width; the flag says whether the branch target is
    /// the equal side (`je`) or the fall-through is (`jne`).
    Eq(Expr, u64, u8, bool),
    /// An ordered comparison of `v` against a constant: a split, both sides
    /// of which continue the tree or fall into the default.
    Ord(Expr),
}

impl Test {
    /// The value the test is about.
    fn value(&self) -> &Expr {
        match self {
            Test::Eq(v, ..) | Test::Ord(v) => v,
        }
    }
}

/// Reads the value a condition compares against a constant, and how.
///
/// `sub`/`dec` ladders compare the running difference against zero; those
/// fold back onto the value ([`expr::Cond::simplify`]).
///
/// # Arguments
///
/// * `cond` - The block's branch condition.
fn test_of(cond: &expr::Cond) -> Option<Test> {
    use crate::isa::x86::ConditionCode as C;
    let cond = cond.simplify().unwrap_or_else(|| cond.clone());
    match (cond.cc.0, &cond.flags) {
        (C::e | C::ne, Flags::Cmp(v, Expr::Const(k), bits)) => {
            Some(Test::Eq(v.clone(), *k, *bits, cond.cc.0 == C::e))
        }
        (C::e | C::ne, Flags::Test(l, r, bits)) if l == r => {
            Some(Test::Eq(l.clone(), 0, *bits, cond.cc.0 == C::e))
        }
        (
            C::b | C::be | C::a | C::ae | C::l | C::le | C::g | C::ge,
            Flags::Cmp(v, Expr::Const(_), _),
        ) => Some(Test::Ord(v.clone())),
        _ => None,
    }
}

/// One edge of the compare tree being read: where it comes from, the
/// block it enters, and the value it carries when it is an equality's
/// matching side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Edge {
    /// The compare block the edge leaves.
    from: usize,
    /// The block it enters.
    to: usize,
    /// The value `v` equals along it, or `None` for the other side of an
    /// equality or either side of an ordered split.
    case: Option<u64>,
}

/// Renders a case value: small ones in decimal, the rest in hex.
///
/// # Arguments
///
/// * `k` - The value, masked to the compare's width.
fn case_label(k: u64) -> String {
    if k < 0x1_0000 {
        format!("case {k}:")
    } else {
        format!("case {k:#x}:")
    }
}

/// Writes the compare tree rooted at block `i` as a `switch`.
///
/// From the root's branch, every successor that is a pure conditional
/// block entered only from the tree and testing the same value joins the
/// tree; every other successor is a leaf. A leaf reached only along
/// `v == K` edges is a case body under those values; a leaf reached any
/// other way (the far side of a split, the `!=` side of the last compare)
/// is the default, and the tree qualifies when there is at most one such
/// block, at least [`LADDER_MIN_CASES`] case bodies, and no leaf is a loop
/// header or lies beyond the loop being written. The tree's own blocks
/// produce no text; the bodies are emitted as a jump table's arms are
/// ([`emit_switch`]), the default among them unless it is where the arms
/// join, in which case the switch falls out into it.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `i` - The root block, whose statements are already written.
/// * `cond` - The root's branch condition.
/// * `t` - The root's branch target block.
/// * `f` - The root's fall-through block.
/// * `out` - Receives the text.
/// * `depth` - Structuring nesting depth.
///
/// # Returns
///
/// The block after the switch, or `None` when the root heads no such tree.
#[expect(clippy::too_many_arguments, reason = "the structurer's shape")]
pub(super) fn try_ladder<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    i: usize,
    cond: &expr::Cond,
    t: usize,
    f: usize,
    out: &mut String,
    depth: usize,
) -> Option<usize> {
    if depth >= MAX_DEPTH || t == f {
        return None;
    }
    let root = test_of(cond)?;
    let v = root.value().clone();
    // A loop's condition is the loop's, however it tests.
    if cycle_of(st, i).is_some_and(|(_, entry)| entry == i) {
        return None;
    }
    let edges = |work: &mut Vec<Edge>, from: usize, test: &Test, t: usize, f: usize| {
        let edge = |to: usize, case: Option<u64>| Edge { from, to, case };
        match test {
            Test::Eq(_, k, bits, target_is_eq) => {
                let k = if *bits >= 64 {
                    *k
                } else {
                    *k & ((1u64 << *bits) - 1)
                };
                let (case, rest) = if *target_is_eq { (t, f) } else { (f, t) };
                work.push(edge(case, Some(k)));
                work.push(edge(rest, None));
            }
            Test::Ord(_) => {
                work.push(edge(t, None));
                work.push(edge(f, None));
            }
        }
    };
    let mut nodes: Vec<usize> = Vec::new();
    let mut cases: BTreeMap<usize, Vec<u64>> = BTreeMap::new();
    let mut residual: BTreeSet<usize> = BTreeSet::new();
    let mut work: Vec<Edge> = Vec::new();
    edges(&mut work, i, &root, t, f);
    while let Some(Edge { from, to: b, case }) = work.pop() {
        if let Some(k) = case {
            if !residual.contains(&b) {
                cases.entry(b).or_default().push(k);
            }
            continue;
        }
        if b != i
            && !nodes.contains(&b)
            && nodes.len() < LADDER_MAX_NODES
            && let Some((c2, t2, f2)) = pure_condition(ctx, st, from, b)
            && let Some(test) = test_of(&c2)
            && *test.value() == v
        {
            nodes.push(b);
            edges(&mut work, b, &test, t2, f2);
            continue;
        }
        residual.insert(b);
        cases.remove(&b);
    }
    if residual.len() > 1 || cases.len() < LADDER_MIN_CASES || cases.len() > SWITCH_ARMS_MAX {
        return None;
    }
    let values: usize = cases.values().map(Vec::len).sum();
    if values > SWITCH_VALUES_MAX {
        return None;
    }
    let leaves = cases.keys().chain(residual.iter());
    for &l in leaves {
        if l == i || nodes.contains(&l) || st.outside(l) || st.loops.contains(&l) {
            return None;
        }
    }
    let switch_expr = v.render(&ctx.names());
    for &n in &nodes {
        st.emitted[n] = true;
    }
    let mut arms: Vec<(usize, Vec<u64>)> = cases.into_iter().collect();
    for (_, ks) in &mut arms {
        ks.sort_unstable();
        ks.dedup();
    }
    arms.sort_by_key(|(_, ks)| ks.first().copied().unwrap_or(0));
    let arms: Vec<Arm> = arms
        .into_iter()
        .map(|(body, ks)| Arm {
            body,
            labels: ks.into_iter().map(case_label).collect(),
        })
        .collect();
    let default = residual.iter().next().copied();
    let headers: BTreeSet<usize> = [i].into_iter().chain(nodes.iter().copied()).collect();
    Some(emit_switch(
        ctx,
        st,
        &headers,
        &switch_expr,
        &arms,
        default,
        out,
        depth,
    ))
}
