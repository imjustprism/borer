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
#[path = "../common/fixture_pack.rs"]
mod fixture_pack;
#[path = "../common/gotos.rs"]
mod gotos;
#[path = "../common/machogen.rs"]
mod machogen;
mod minidump;
#[path = "../common/raw.rs"]
mod raw;

mod a32;
mod a32_decompile;
mod a32_emulate;
mod a32_lift;
mod a64;
mod a64_decompile;
mod a64_emulate;
mod a64_lift;
mod abi;
mod analysis;
mod calls;
mod carve;
mod clr;
mod decoded;
mod decompile;
mod discovery;
mod eh;
mod elf;
mod emulate_calls;
mod engine;
mod families;
mod fixups;
mod float_results;
mod go;
mod groundtruth;
mod hashing;
mod idioms;
mod iocs;
mod layout;
mod libsig;
mod lsda;
mod macho;
mod memo;
mod negfields;
mod next;
mod noise;
mod objc;
mod protection;
mod protos;
mod regression;
mod reloc;
mod search;
mod strings;
mod structure;
mod syscalls;
mod textcheck;
mod typelib;
mod types;
mod unit;
mod x86;
