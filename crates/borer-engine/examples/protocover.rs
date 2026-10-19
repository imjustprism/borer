//! Counts the calls of a binary that reach an import with a full typed
//! prototype: the curated type library's, and with the SDK library under
//! it.
//!
//! ```text
//! cargo run --release --example protocover -- <binary>...
//! ```
//!
//! A call counts once per call site, whether it reaches the import's slot
//! directly or through a thunk that jumps to it. Output lines are
//! `key=value` pairs so a script can parse them.

use std::error::Error;

use borer_engine::analysis::{Analysis, RefKind, sdk, typelib};
use borer_engine::program::{Program, SymbolKind};

fn main() -> Result<(), Box<dyn Error>> {
    let paths: Vec<String> = std::env::args().skip(1).collect();
    if paths.is_empty() {
        return Err("usage: protocover <binary>...".into());
    }
    for path in &paths {
        let p = Program::load(std::path::Path::new(path))?;
        let a = Analysis::compute(&p);
        let (mut calls, mut curated, mut typed, mut imports, mut declared) = (0, 0, 0, 0, 0);
        for s in p
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        {
            let name = s.name.split_once('!').map_or(s.name.as_str(), |(_, n)| n);
            let direct = a.xrefs_to(s.addr);
            let through: usize = direct
                .iter()
                .filter(|r| r.kind == RefKind::Jmp && r.from_entry == Some(r.va))
                .map(|r| {
                    a.xrefs_to(r.va)
                        .iter()
                        .filter(|c| c.kind == RefKind::Call)
                        .count()
                })
                .sum();
            let n = direct.iter().filter(|r| r.kind == RefKind::Call).count() + through;
            let any = typelib::declared(name, p.format);
            let wide = sdk::declared(name, |os| os.serves(p.format));
            let narrow = any.filter(|d| wide.is_none_or(|w| !std::ptr::eq(*d, w)));
            imports += 1;
            declared += usize::from(any.is_some());
            calls += n;
            if narrow.is_some() {
                curated += n;
            }
            if any.is_some() {
                typed += n;
            }
        }
        println!(
            "binary={path} imports={imports} imports_typed={declared} calls={calls} \
             calls_curated={curated} calls_typed={typed}"
        );
    }
    Ok(())
}
