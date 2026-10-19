//! The measurement sweep: what the e-graph's rules change on real
//! binaries.
//!
//! ```text
//! BORER_EGRAPH="a.exe;b.dll" cargo test -p borer-engine --lib egraph::sweep -- --ignored --nocapture
//! ```
//!
//! Every block of every function is lifted as the verifier lifts it, each
//! value the block leaves (a register, a stored address and value, the
//! branch condition) is lowered to MIR and simplified with every rule, and
//! the sweep counts the values whose extracted form is cheaper, which
//! rules alone make each one cheaper, the time the e-graph takes against
//! a full decompile, and a sample of forms before and after.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::time::{Duration, Instant};

use super::super::super::expr::Key;
use super::super::super::lift::{BlockFacts, Env, Pass, exec_block};
use super::super::super::new_ctx;
use super::super::super::verify::{Effect, Probe};
use super::super::build::Builder;
use super::super::{BinOp, Body, IPred, Inst, UnOp, Val, WideOp};
use super::{Rule, simplify};
use crate::analysis::decompile::decompile_all;
use crate::analysis::{Analysis, Overlay};
use crate::program::Program;

/// How deep a rendered form goes before it elides.
const SHOW_DEPTH: u8 = 10;

/// The most samples kept for one set of rules, per binary.
const SAMPLES_PER_KIND: usize = 3;

/// Renders one value of a body as C-like text, for the samples.
///
/// # Arguments
///
/// * `body` - The body.
/// * `v` - The value.
/// * `depth` - How much deeper to render.
fn show(body: &Body, v: Val, depth: u8) -> String {
    let Some(d) = depth.checked_sub(1) else {
        return "..".to_owned();
    };
    let Some(node) = body.node(v) else {
        return "?".to_owned();
    };
    let s = |x: Val| show(body, x, d);
    match &node.inst {
        Inst::Const { bits, .. } => {
            if *bits < 1024 {
                bits.to_string()
            } else {
                format!("{bits:#x}")
            }
        }
        Inst::FConst { bits, .. } => format!("f{bits:#x}"),
        Inst::Reg(Key::Reg(r)) => format!("{r:?}").to_lowercase(),
        Inst::Reg(k) => format!("{k:?}"),
        Inst::Frame(off) => format!("sp{off:+}"),
        Inst::Tls => "tls".to_owned(),
        Inst::Load { addr, ty } => format!("*({ty:?})({})", s(*addr)),
        Inst::Bin { op, w, l, r } => {
            let sym = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::UDiv => "/u",
                BinOp::SDiv => "/s",
                BinOp::URem => "%u",
                BinOp::SRem => "%s",
                BinOp::And => "&",
                BinOp::Or => "|",
                BinOp::Xor => "^",
                BinOp::Shl => "<<",
                BinOp::LShr => ">>u",
                BinOp::AShr => ">>s",
                BinOp::Rotl => "rotl",
                BinOp::Rotr => "rotr",
            };
            format!("({} {sym}{w} {})", s(*l), s(*r))
        }
        Inst::Ovf { op, w, l, r } => format!("{op:?}{w}({}, {})", s(*l), s(*r)),
        Inst::Wide { op, w, l, r } => {
            let name = match op {
                WideOp::UMulHi => "mulhi",
                WideOp::SMulHi => "smulhi",
            };
            format!("{name}{w}({}, {})", s(*l), s(*r))
        }
        Inst::Un { op, x, .. } => match op {
            UnOp::Neg => format!("-{}", s(*x)),
            UnOp::Not => format!("~{}", s(*x)),
            UnOp::Parity => format!("parity({})", s(*x)),
        },
        Inst::Ext {
            signed,
            from,
            to,
            x,
            ..
        } => {
            let t = if *signed { "i" } else { "u" };
            format!("({t}{from}->{to}){}", s(*x))
        }
        Inst::Trunc { to, x } => format!("(u{to}){}", s(*x)),
        Inst::Bitcast { to, x } => format!("bitcast<{to:?}>({})", s(*x)),
        Inst::Convert { to, x, .. } => format!("convert<{to:?}>({})", s(*x)),
        Inst::FBin { op, l, r, .. } => format!("f{op:?}({}, {})", s(*l), s(*r)),
        Inst::FUn { op, x, .. } => format!("f{op:?}({})", s(*x)),
        Inst::ICmp { pred, l, r, .. } => {
            let sym = match pred {
                IPred::Eq => "==",
                IPred::Ne => "!=",
                IPred::Ult => "<u",
                IPred::Ule => "<=u",
                IPred::Ugt => ">u",
                IPred::Uge => ">=u",
                IPred::Slt => "<s",
                IPred::Sle => "<=s",
                IPred::Sgt => ">s",
                IPred::Sge => ">=s",
            };
            format!("({} {sym} {})", s(*l), s(*r))
        }
        Inst::FCmp { pred, l, r, .. } => format!("fcmp{pred:?}({}, {})", s(*l), s(*r)),
        Inst::Select { c, t, f } => format!("({} ? {} : {})", s(*c), s(*t), s(*f)),
        Inst::Splat { lane, x } => format!("splat{lane}({})", s(*x)),
        Inst::Helper { h, args, .. } => {
            let a: Vec<String> = args.iter().map(|x| s(*x)).collect();
            format!("{h}({})", a.join(", "))
        }
        Inst::Undef(why) => format!("undef({why:?})"),
    }
}

/// What the sweep found over one binary.
#[derive(Default)]
struct Tally {
    /// Values simplified.
    roots: usize,
    /// Values whose extracted form is cheaper.
    changed: usize,
    /// Changed values by the rules that alone make them cheaper.
    kinds: BTreeMap<String, usize>,
    /// Samples of changed values, by kind.
    samples: BTreeMap<String, Vec<(String, String)>>,
    /// Time spent lowering to MIR.
    lower: Duration,
    /// Time spent in the e-graph.
    graph: Duration,
}

impl Tally {
    /// Simplifies one value and counts it.
    ///
    /// # Arguments
    ///
    /// * `body` - The block's body.
    /// * `v` - The value.
    fn value(&mut self, body: &Body, v: Val) {
        self.roots += 1;
        let t = Instant::now();
        let out = simplify(body, v, &Rule::ALL);
        self.graph += t.elapsed();
        let Some(out) = out else { return };
        if out.cost >= out.input_cost {
            return;
        }
        self.changed += 1;
        let alone: Vec<String> = Rule::ALL
            .iter()
            .filter(|r| simplify(body, v, &[**r]).is_some_and(|o| o.cost < o.input_cost))
            .map(|r| format!("{r:?}"))
            .collect();
        let kind = if alone.is_empty() {
            "combined".to_owned()
        } else {
            alone.join("+")
        };
        *self.kinds.entry(kind.clone()).or_default() += 1;
        let kept = self.samples.entry(kind).or_default();
        if kept.len() < SAMPLES_PER_KIND {
            kept.push((
                show(body, v, SHOW_DEPTH),
                show(&out.body, out.root, SHOW_DEPTH),
            ));
        }
    }
}

/// Sweeps every `BORER_EGRAPH` binary and prints what the rules change.
#[test]
#[ignore = "set BORER_EGRAPH to binary paths to run this sweep"]
#[expect(clippy::disallowed_methods, reason = "the sweep reports its own time")]
#[expect(clippy::print_stdout, reason = "the sweep is a report")]
fn the_rules_measured_on_real_binaries() {
    let paths = std::env::var("BORER_EGRAPH").expect("BORER_EGRAPH env var");
    for path in paths.split(';').filter(|p| !p.is_empty()) {
        let p = Program::load_with(std::path::Path::new(path), false).expect("load");
        let Some(bitness) = p.arch.bitness() else {
            println!("{path}: not x86, skipped");
            continue;
        };
        let word = u8::try_from(bitness).expect("32 or 64");
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
        let t = Instant::now();
        let texts = decompile_all(&p, &a, &overlay, &entries);
        let decompile = t.elapsed();
        let mut tally = Tally::default();
        for f in &a.functions {
            let starts = f.blocks.iter().map(|b| b.start).collect();
            let mut ctx = new_ctx(&p, &a, &overlay, f, bitness, starts, &[]);
            ctx.symbolic_only = true;
            ctx.flag_readers = vec![false; f.blocks.len()];
            ctx.rebase_flags = vec![None; f.blocks.len()];
            for block in &f.blocks {
                let mut instrs = Vec::new();
                let mut va = block.start;
                while va < block.end {
                    let Some(i) = ctx.decode(va) else { break };
                    va = i.next_ip();
                    instrs.push(i);
                }
                ctx.probe = Some(Probe::default());
                let mut env = Env::entry();
                let out = exec_block(
                    &mut ctx,
                    &instrs,
                    None,
                    &mut env,
                    Pass::Dataflow,
                    None,
                    BlockFacts::default(),
                );
                let probe = ctx.probe.take().unwrap_or_default();
                let t = Instant::now();
                let mut b = Builder::new(word, &probe.temps, &[block.start]);
                let mut roots: Vec<Val> = env.vals.values().map(|e| b.value(e)).collect();
                for effect in &probe.effects {
                    if let Effect::Store { addr, value, .. } = effect {
                        roots.push(b.value(addr));
                        roots.push(b.value(value));
                    }
                }
                if let Some(branch) = &out.branch {
                    roots.push(b.condition(&branch.cond));
                }
                tally.lower += t.elapsed();
                for v in roots {
                    tally.value(&b.body, v);
                }
            }
        }
        let mut report = format!(
            "# {path}: {} functions ({} decompiled), decompile_all {decompile:?}; {} values, {} cheaper; e-graph {:?} ({:.1}% of decompile_all), lowering {:?}\n",
            entries.len(),
            texts.iter().filter(|t| t.is_some()).count(),
            tally.roots,
            tally.changed,
            tally.graph,
            100.0 * tally.graph.as_secs_f64() / decompile.as_secs_f64().max(1e-9),
            tally.lower,
        );
        for (kind, n) in &tally.kinds {
            writeln!(report, "{kind}\t{n}").expect("write");
        }
        for (kind, samples) in &tally.samples {
            for (before, after) in samples {
                writeln!(report, "[{kind}] {before}\n    => {after}").expect("write");
            }
        }
        println!("{report}");
    }
}
