//! The engine's integration tests as one binary: every file here is a
//! module, so the engine is linked once for all of them instead of once
//! per file. `dogfood` and `bench` stay binaries of their own, since the
//! gate and the benchmark run them by name, and so does `hostile`, whose
//! counting allocator measures a process's whole heap.
#[path = "../common/mod.rs"]
mod common;
#[path = "../common/decompiled.rs"]
mod decompiled;
#[path = "../common/elfgen.rs"]
mod elfgen;
#[path = "../common/gotos.rs"]
mod gotos;
#[path = "../common/nebula.rs"]
mod nebula;
#[path = "../common/raw.rs"]
mod raw;

mod a64;
mod a64_decompile;
mod a64_emulate;
mod a64_lift;
mod analysis;
mod calls;
mod carve;
mod decoded;
mod decompile;
mod discovery;
mod elf;
mod emulate_calls;
mod engine;
mod families;
mod go;
mod groundtruth;
mod hashing;
mod iocs;
mod layout;
mod libsig;
mod lsda;
mod macho;
mod next;
mod protection;
mod protos;
mod regression;
mod reloc;
mod search;
mod structure;
mod syscalls;
mod typelib;
mod types;
mod x86;
