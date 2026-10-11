//! The engine's integration tests as one binary: every file here is a
//! module, so the engine is linked once for all of them instead of once
//! per file. `dogfood` and `bench` stay binaries of their own, since the
//! gate and the benchmark run them by name.
#[path = "../common/mod.rs"]
mod common;
#[path = "../common/decompiled.rs"]
mod decompiled;
#[path = "../common/gotos.rs"]
mod gotos;
#[path = "../common/nebula.rs"]
mod nebula;
#[path = "../common/raw.rs"]
mod raw;

mod analysis;
mod decompile;
mod discovery;
mod elf;
mod engine;
mod families;
mod groundtruth;
mod hashing;
mod hostile;
mod lsda;
mod macho;
mod protection;
mod regression;
mod search;
mod structure;
mod x86;
