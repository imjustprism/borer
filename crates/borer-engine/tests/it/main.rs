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
mod a64_joins;
mod a64_lift;
mod abi;
mod analysis;
mod arguments;
mod bounds;
mod bundle;
mod calls;
mod capabilities;
mod carve;
mod clr;
mod clr_il;
mod com;
mod cpuid;
mod decoded;
mod decompile;
mod discovery;
mod dwarf;
mod eh;
mod elf;
mod emptystr;
mod emulate_calls;
mod engine;
mod families;
mod fixups;
mod float_results;
mod folds;
mod go;
mod groundtruth;
mod hashing;
mod hkey;
mod idioms;
mod iocs;
mod layout;
mod libsig;
mod lsda;
mod macho;
mod memo;
mod metadata;
mod negfields;
mod next;
mod noise;
mod objc;
mod opcodes;
mod param_types;
mod protection;
mod protos;
mod rdtsc;
mod regression;
mod reloc;
mod replay_rows;
mod replayed;
mod returns;
mod riprel;
mod rv;
mod rv_decompile;
mod rv_emulate;
mod rv_lift;
mod search;
mod shapes;
mod strings;
mod structure;
mod syscalls;
mod tells;
mod textcheck;
mod toolchain;
mod typelib;
mod types;
mod unchecked;
mod unit;
mod void_results;
mod wire_tables;
mod x86;
