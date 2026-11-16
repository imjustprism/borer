//! What borer's front ends, the MCP server and the app, share outside the pure engine:
//! where they look for a binary's companions when their user names nothing else, read from
//! the environment ([`places`]).
//!
//! The engine reads no environment variable; this crate is where both front ends read the
//! same ones the same way, so a person and an agent get the same packs and PDB names.

pub mod places;
