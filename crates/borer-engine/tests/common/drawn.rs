//! What every control-flow graph ([`cfg`]) and layered drawing
//! ([`layout`]) must hold, as checks the integration tests and the dogfood
//! sweep share, and digests of a drawing to compare across runs.

use borer_engine::analysis::render::{Cfg, Drawing, Graph, GraphEdge, Route, Routed};
use std::collections::BTreeMap;

/// A node's box: left, top, right and bottom grid lines.
type Box4 = (i64, i64, i64, i64);

/// Returns the graph a [`Cfg`] was laid out from.
///
/// # Arguments
///
/// * `g` - The control-flow graph.
/// * `entry` - The function's entry, whose block is the root.
pub(crate) fn graph_of(g: &Cfg, entry: u64) -> Graph {
    Graph {
        sizes: g.nodes.iter().map(|n| n.size).collect(),
        edges: g
            .edges
            .iter()
            .map(|e| GraphEdge {
                from: e.from,
                to: e.to,
                route: if e.back { Route::Up } else { Route::Down },
            })
            .collect(),
        root: g.nodes.iter().position(|n| n.start == entry).unwrap_or(0),
    }
}

/// Checks that each node covers exactly the listing rows whose instruction
/// lies in its block, from the first such row to the last, then the
/// `// ... N more bytes` row of a block cut short.
///
/// # Arguments
///
/// * `g` - The control-flow graph.
///
/// # Errors
///
/// Names the first node that does not.
pub(crate) fn rows(g: &Cfg) -> Result<(), String> {
    let v = &g.listing;
    let mut want: Vec<Vec<usize>> = vec![Vec::new(); g.nodes.len()];
    for i in 0..v.lines() {
        let Some(va) = v.address(i) else { continue };
        let k = g.nodes.partition_point(|n| n.start <= va);
        if let Some(k) = k.checked_sub(1).filter(|&k| va < g.nodes[k].end) {
            want[k].push(i);
        }
    }
    for (n, want) in g.nodes.iter().zip(&want) {
        let got: Vec<usize> = n
            .lines
            .clone()
            .filter(|&i| v.address(i).is_some())
            .collect();
        let last = if n.shortened { 2 } else { 1 };
        let ends = (want.first().copied(), want.last().copied());
        if &got != want || ends != (Some(n.lines.start), n.lines.end.checked_sub(last)) {
            return Err(format!(
                "block {:#x} covers rows {:?}, its instructions are on {want:?}",
                n.start, n.lines
            ));
        }
    }
    Ok(())
}

/// Returns whether the open segment from `a` to `b` passes through the
/// inside of a box, borders excluded.
///
/// # Arguments
///
/// * `a` - One end.
/// * `b` - The other, on the same row or column.
/// * `r` - The box.
fn cuts(a: (i64, i64), b: (i64, i64), r: Box4) -> bool {
    let (x0, x1) = (a.0.min(b.0), a.0.max(b.0));
    let (y0, y1) = (a.1.min(b.1), a.1.max(b.1));
    let across = |lo: i64, hi: i64, rlo: i64, rhi: i64| {
        if lo == hi {
            rlo < lo && lo < rhi
        } else {
            lo < rhi && rlo < hi
        }
    };
    across(x0, x1, r.0, r.2) && across(y0, y1, r.1, r.3)
}

/// Returns each route's points as `i64` pairs.
///
/// # Arguments
///
/// * `l` - The drawing.
fn points(l: &Drawing) -> Vec<Vec<(i64, i64)>> {
    l.routes
        .iter()
        .map(|r| {
            r.iter()
                .map(|&(x, y)| (i64::from(x), i64::from(y)))
                .collect()
        })
        .collect()
}

/// Counts the crossings of the layered routes from the drawing alone: the
/// points where one route's horizontal run passes through another's
/// vertical one, neither at an end.
///
/// # Arguments
///
/// * `l` - The drawing.
fn drawn_crossings(l: &Drawing) -> usize {
    let (mut across, mut down) = (Vec::new(), Vec::new());
    for (e, (pts, &how)) in points(l).iter().zip(&l.routed).enumerate() {
        if how != Routed::Layered {
            continue;
        }
        for s in pts.windows(2) {
            let (a, b) = (s[0], s[1]);
            if a.1 == b.1 && a.0 != b.0 {
                across.push((a.1, a.0.min(b.0), a.0.max(b.0), e));
            } else if a.0 == b.0 && a.1 != b.1 {
                down.push((a.0, a.1.min(b.1), a.1.max(b.1), e));
            }
        }
    }
    down.sort_unstable();
    across
        .iter()
        .map(|&(y, x0, x1, e)| {
            let from = down.partition_point(|v| v.0 <= x0);
            down[from..]
                .iter()
                .take_while(|v| v.0 < x1)
                .filter(|v| v.3 != e && v.1 < y && y < v.2)
                .count()
        })
        .sum()
}

/// Each line a run lies along, keyed by whether it runs down and its fixed
/// coordinate, to the runs on it: their two ends and their edge.
type Lines = BTreeMap<(bool, i64), Vec<(i64, i64, usize)>>;

/// Checks that no two edges' runs overlap along one line, across or down.
///
/// # Arguments
///
/// * `pts` - Each route's points.
///
/// # Errors
///
/// Names the first two edges whose runs overlap.
fn runs_apart(pts: &[Vec<(i64, i64)>]) -> Result<(), String> {
    let mut lines = Lines::new();
    for (e, route) in pts.iter().enumerate() {
        for s in route.windows(2) {
            let (a, b) = (s[0], s[1]);
            if a.1 == b.1 {
                lines
                    .entry((true, a.1))
                    .or_default()
                    .push((a.0.min(b.0), a.0.max(b.0), e));
            } else if a.0 == b.0 {
                lines
                    .entry((false, a.0))
                    .or_default()
                    .push((a.1.min(b.1), a.1.max(b.1), e));
            }
        }
    }
    for (y, runs) in &mut lines {
        runs.sort_unstable();
        for (i, a) in runs.iter().enumerate() {
            if let Some(b) = runs[i + 1..]
                .iter()
                .take_while(|b| b.0 <= a.1)
                .find(|b| b.2 != a.2)
            {
                return Err(format!(
                    "edges {} and {} run along line {y:?} together",
                    a.2, b.2
                ));
            }
        }
    }
    Ok(())
}

/// Returns each node's box as drawn, after checking the drawing has every
/// node and edge and draws each node at least as wide as asked and as tall.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `l` - Its drawing.
///
/// # Errors
///
/// Names the first node or edge missing, or the first box drawn too small.
fn boxes(g: &Graph, l: &Drawing) -> Result<Vec<Box4>, String> {
    if l.at.len() != g.sizes.len()
        || l.sizes.len() != g.sizes.len()
        || l.routes.len() != g.edges.len()
        || l.routed.len() != g.edges.len()
    {
        return Err("a node or edge is missing".to_owned());
    }
    if let Some(i) =
        (0..g.sizes.len()).find(|&i| l.sizes[i].0 < g.sizes[i].0 || l.sizes[i].1 != g.sizes[i].1)
    {
        return Err(format!(
            "node {i} is drawn {:?}, asked {:?}",
            l.sizes[i], g.sizes[i]
        ));
    }
    Ok(l.at
        .iter()
        .zip(&l.sizes)
        .map(|(&(x, y), &(w, h))| {
            let (x, y) = (i64::from(x), i64::from(y));
            (x, y, x + i64::from(w), y + i64::from(h))
        })
        .collect())
}

/// Checks a drawing of a graph.
///
/// Every node and route point lies inside the size; no two boxes overlap;
/// each edge routed down that leaves a node the root reaches over such
/// edges ends below its source's bottom (the nodes it does not reach are
/// drawn below the rest, so their edges may go up); each route runs in
/// horizontal and vertical steps from a point on its source's bottom edge
/// to one on its target's top edge, through no box and along no other
/// route's line; the crossings the drawing shows are those it reports, and
/// no more than before the reduction.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `l` - Its drawing.
///
/// # Errors
///
/// Names the first broken rule.
pub(crate) fn check(g: &Graph, l: &Drawing) -> Result<(), String> {
    let boxes = boxes(g, l)?;
    let (sw, sh) = (i64::from(l.size.0), i64::from(l.size.1));
    let inside = |(x, y): (i64, i64)| (0..=sw).contains(&x) && (0..=sh).contains(&y);
    for (i, b) in boxes.iter().enumerate() {
        if !inside((b.0, b.1)) || !inside((b.2, b.3)) {
            return Err(format!("node {i} {b:?} is outside {:?}", l.size));
        }
    }
    let mut by_x: Vec<usize> = (0..boxes.len()).collect();
    by_x.sort_by_key(|&i| boxes[i].0);
    for (k, &i) in by_x.iter().enumerate() {
        for &j in by_x[k + 1..]
            .iter()
            .take_while(|&&j| boxes[j].0 < boxes[i].2)
        {
            let (a, b) = (boxes[i], boxes[j]);
            if a.1 < b.3 && b.1 < a.3 {
                return Err(format!("nodes {i} {a:?} and {j} {b:?} overlap"));
            }
        }
    }
    let mut rows: BTreeMap<i64, Vec<usize>> = BTreeMap::new();
    for (i, b) in boxes.iter().enumerate() {
        rows.entry(b.1).or_default().push(i);
    }
    let tallest = boxes.iter().map(|b| b.3 - b.1).max().unwrap_or(0);
    let mut outs = vec![Vec::new(); boxes.len()];
    for e in g.edges.iter().filter(|e| e.route == Route::Down) {
        outs[e.from].push(e.to);
    }
    let mut reached = vec![false; boxes.len()];
    let mut todo = vec![g.root];
    while let Some(u) = todo.pop() {
        if !std::mem::replace(&mut reached[u], true) {
            todo.extend(outs[u].iter().copied());
        }
    }
    let pts = points(l);
    for (k, (e, route)) in g.edges.iter().zip(&pts).enumerate() {
        let (u, v) = (e.from, e.to);
        let (src, dst) = (boxes[u], boxes[v]);
        if e.route == Route::Down && u != v && reached[u] && dst.1 <= src.3 {
            return Err(format!("edge {k} {u}->{v} does not go down"));
        }
        let (Some(&first), Some(&last)) = (route.first(), route.last()) else {
            return Err(format!("edge {k} has no route"));
        };
        if first.1 != src.3 || !(src.0..=src.2).contains(&first.0) {
            return Err(format!(
                "edge {k} starts at {first:?}, not on {src:?}'s bottom"
            ));
        }
        if last.1 != dst.1 || !(dst.0..=dst.2).contains(&last.0) || !inside(last) {
            return Err(format!("edge {k} ends at {last:?}, not on {dst:?}'s top"));
        }
        for s in route.windows(2) {
            let (a, b) = (s[0], s[1]);
            if !inside(a) || (a.0 != b.0 && a.1 != b.1) {
                return Err(format!("edge {k} steps from {a:?} to {b:?}"));
            }
            let (y0, y1) = (a.1.min(b.1), a.1.max(b.1));
            for (_, ids) in rows.range(y0 - tallest..=y1) {
                if let Some(&i) = ids.iter().find(|&&i| cuts(a, b, boxes[i])) {
                    return Err(format!("edge {k} runs {a:?}-{b:?} through node {i}"));
                }
            }
        }
    }
    runs_apart(&pts)?;
    let seen = drawn_crossings(l);
    if seen != l.crossings || l.crossings > l.crossings_before {
        return Err(format!(
            "the drawing shows {seen} crossings, reports {} after reduction and {} before",
            l.crossings, l.crossings_before
        ));
    }
    Ok(())
}

/// Returns FNV-1a over a run of words.
///
/// # Arguments
///
/// * `words` - The words, in order.
fn fnv(words: impl IntoIterator<Item = i64>) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for v in words {
        for b in v.to_le_bytes() {
            h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
    }
    h
}

/// Returns a digest of a graph and its drawing: every node size, edge and
/// how it was routed, every coordinate and the size, in order.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `l` - Its drawing.
pub(crate) fn digest(g: &Graph, l: &Drawing) -> u64 {
    let wide = |x: usize| i64::try_from(x).unwrap_or(-1);
    let sizes = g
        .sizes
        .iter()
        .chain(&l.sizes)
        .flat_map(|&(w, h)| [i64::from(w), i64::from(h)]);
    let edges = g.edges.iter().flat_map(|e| {
        let up = i64::from(e.route == Route::Up);
        [wide(e.from), wide(e.to), up]
    });
    let routed = l.routed.iter().map(|&r| match r {
        Routed::Layered => 0,
        Routed::Side => 1,
        Routed::Missing => 2,
    });
    let at = l.at.iter().flat_map(|&(x, y)| [i64::from(x), i64::from(y)]);
    let routes = points(l)
        .into_iter()
        .flat_map(|r| std::iter::once((wide(r.len()), 0)).chain(r))
        .flat_map(|(x, y)| [x, y]);
    let size = [i64::from(l.size.0), i64::from(l.size.1)];
    fnv(sizes
        .chain(edges)
        .chain(routed)
        .chain(at)
        .chain(routes)
        .chain(size))
}

/// Returns a digest of a control-flow graph: its drawing's ([`digest`]),
/// then each edge's kind.
///
/// # Arguments
///
/// * `g` - The control-flow graph.
/// * `entry` - The function's entry.
pub(crate) fn cfg_digest(g: &Cfg, entry: u64) -> u64 {
    let kinds = format!("{:?}", g.edges.iter().map(|e| &e.kind).collect::<Vec<_>>());
    let head = digest(&graph_of(g, entry), &g.layout());
    fnv(std::iter::once(i64::from_le_bytes(head.to_le_bytes())).chain(kinds.bytes().map(i64::from)))
}
