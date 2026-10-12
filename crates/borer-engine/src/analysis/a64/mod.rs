//! Function discovery for AArch64 (arm64) code.
//!
//! [`discover()`] finds an arm64 program's functions the way
//! [`super::functions`] finds an x86 one's: from the entry point, the
//! symbols and the extents the file declares (`.pdata`, `.eh_frame`, sized
//! `STT_FUNC` symbols, a Mach-O image's function starts and compact unwind
//! table), following branches, taking `bl` targets as new functions and
//! tail calls as callees, ending a path at a call that never returns, then
//! guessing at the gaps no function covers that open the way an arm64
//! function opens ([`prologue`]). A `br` through a bounded jump table has
//! its cases walked ([`switch`]); a call to a stub after an import, or
//! through the import's slot, that never returns ends its path, and the
//! stubs are named after their imports ([`stubs`]). Once the functions are
//! final, the constants their registers hold give the data, table and slot
//! references ([`refs`]). It shares the seeds, the fuel, the never-returning
//! names, the naming pass, the jump-table checks and the reference index
//! with the x86 walk, and reads instructions only through
//! [`crate::isa::a64`].

mod discover;
mod prologue;
mod refs;
mod stubs;
mod switch;

pub(crate) use discover::discover;
pub(crate) use refs::constant_in;
