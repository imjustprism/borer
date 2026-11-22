//! What borer's front ends, the MCP server and the app, share outside the pure engine:
//! where they look for a binary's companions when their user names nothing else, read from
//! the environment ([`places`]), the byte budget every answer is cut to ([`budget`]), the deadline a request stops at
//! ([`deadline`]), how they write a project file ([`project_file`]), which
//! the engine, writing no files, only spells, the tools they both list and run
//! ([`tools`]), and what a latest-release answer from GitHub means to this build
//! ([`release`]), and the protocol the app speaks with Claude Code's command line when the
//! chat runs its turns through it ([`claude_code`]).
//!
//! The engine reads no environment variable; this crate is where both front ends read the
//! same ones the same way, so a person and an agent get the same packs and PDB names.

pub mod budget;
pub mod claude_code;
pub mod deadline;
pub mod places;
pub mod project_file;
pub mod release;
pub mod tools;
