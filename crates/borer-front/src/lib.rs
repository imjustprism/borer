//! What borer's front ends, the MCP server and the app, share outside the pure engine:
//! where they look for a binary's companions when their user names nothing else, read from
//! the environment ([`places`]), the byte budget every answer is cut to ([`budget`]), how they write a project file ([`project_file`]), which
//! the engine, writing no files, only spells, and the tools they both list and run
//! ([`tools`]).
//!
//! The engine reads no environment variable; this crate is where both front ends read the
//! same ones the same way, so a person and an agent get the same packs and PDB names.

pub mod budget;
pub mod places;
pub mod project_file;
pub mod tools;
