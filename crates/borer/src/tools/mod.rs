//! The tool handlers, one module per area, each with its own router;
//! `main.rs` sums the routers into the one the server answers by.

pub(crate) mod annotate;
pub(crate) mod bytes;
pub(crate) mod decompile;
pub(crate) mod functions;
pub(crate) mod live;
pub(crate) mod livescan;
pub(crate) mod load;
pub(crate) mod query;
pub(crate) mod search;
