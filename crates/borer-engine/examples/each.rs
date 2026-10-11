//! Decompiles every function of a binary one at a time, naming each on
//! stderr before it starts, so a crash or an abort names its function.
//!
//! ```text
//! cargo run --release --example each -- <binary> [named] [from-index]
//! ```
//!
//! `named` runs the named decompile the tools use; `from-index` skips the
//! functions before that index in discovery order.

use std::error::Error;
use std::io::Write as _;

use borer_engine::analysis::decompile::{decompile, decompile_named};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Program;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let path = args
        .first()
        .ok_or("usage: each <binary> [named] [from-index]")?;
    let named = args.iter().any(|a| a == "named");
    let from: usize = args
        .iter()
        .skip(1)
        .find_map(|a| a.parse().ok())
        .unwrap_or(0);
    let p = Program::load(std::path::Path::new(path))?;
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    eprintln!("functions: {}", a.functions.len());
    let mut slow: Vec<(u128, u64)> = Vec::new();
    for (i, f) in a.functions.iter().enumerate().skip(from) {
        eprint!("{i} {:#x}\r", f.entry);
        std::io::stderr().flush()?;
        #[expect(
            clippy::disallowed_methods,
            reason = "each function's time is the report"
        )]
        let t0 = std::time::Instant::now();
        let text = if named {
            decompile_named(&p, &a, &o, f.entry)
        } else {
            decompile(&p, &a, &o, f.entry)
        };
        let ms = t0.elapsed().as_millis();
        if ms > 2000 {
            slow.push((ms, f.entry));
        }
        if text.is_none() {
            eprintln!("\nfailed: {:#x}", f.entry);
        }
    }
    slow.sort_unstable_by(|x, y| y.cmp(x));
    eprintln!(
        "\nslowest: {:?}",
        slow.iter()
            .take(10)
            .map(|(ms, e)| format!("{e:#x}={ms}ms"))
            .collect::<Vec<_>>()
    );
    Ok(())
}
