//! borer-engine: the analysis core of borer.
//!
//! The crate is pure and synchronous: no async runtime, no MCP types, no
//! filesystem writes. Every function is a deterministic function of its
//! inputs, so results are reproducible byte for byte and the crate can later
//! compile to WASM. [`program::Program`] holds only facts derived from the
//! file; user annotations live in a separate [`analysis::Overlay`]. Every
//! potentially unbounded output is capped or paged by its caller.
//!
//! # Examples
//!
//! Any PE or ELF works; the running binary itself is a convenient fixture.
//!
//! ```
//! use borer_engine::analysis::Analysis;
//! use borer_engine::program::Program;
//!
//! let path = std::env::current_exe()?;
//! let program = Program::load(&path)?;
//! let analysis = Analysis::compute(&program);
//! assert!(!analysis.functions.is_empty());
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

pub mod analysis;
pub mod bundle;
pub mod cancel;
pub mod carve;
pub mod clr;
pub mod crypto;
pub mod disasm;
pub mod dwarf;
mod dyld;
mod eh_frame;
pub mod emulate;
pub mod entropy;
pub mod fileinfo;
pub mod fxmap;
pub mod go;
pub mod hashing;
pub mod headers;
pub mod hexdump;
pub mod ioc;
pub mod isa;
pub mod layout;
pub mod libsets;
pub mod libsig;
pub mod live;
mod lsda;
pub mod macho;
pub mod memory;
mod minidump;
pub mod num;
pub mod pack;
pub mod patch;
pub mod pdb;
pub mod program;
pub mod reloc;
pub mod rsrc;
pub mod script;
pub mod search;
pub mod strings;
pub mod table;
pub mod text;
pub(crate) mod timing;
pub mod toolchain;
pub mod unwind;
pub mod winconst;
