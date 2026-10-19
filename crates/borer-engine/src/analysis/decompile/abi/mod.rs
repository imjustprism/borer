//! The application binary interface of each target: how a function takes
//! its parameters and hands back its result, which registers it preserves,
//! and which registers a call changes.
//!
//! The tables cover System V x86-64, Microsoft x64, Go's register ABI and
//! the 32-bit cdecl, stdcall, fastcall and thiscall conventions
//! ([`Conv`]), and the arm64 procedure call standard ([`a64`]). A
//! function's shape, what it takes as both lifters read it, is built once
//! ([`shape`]).
//!
//! A linkage stub reaches the function its slot binds ([`bound`],
//! [`reached`]).

pub(crate) mod a64;
mod conv;
mod function;
mod stubs;

pub(crate) use conv::*;
pub(in crate::analysis::decompile) use function::shape;
pub(crate) use stubs::{bound, reached};
