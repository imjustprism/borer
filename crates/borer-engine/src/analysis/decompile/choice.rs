//! Choice points: the places a decompile guesses what the machine meant,
//! each with its renderings in order, most readable first and literal last.
//!
//! A text pass is one ([`Site::Pass`]): applied, then skipped for the
//! function. The decompiler records the others it met while it wrote the
//! text ([`Decompiled::sites`](super::Decompiled)): a frame slot every
//! access read as a float ([`Site::Slot`]) and a 64-bit integer return
//! ([`Site::Return`]). [`Choices`] holds the sites a decompile renders at
//! their literal rung, carried by [`super::super::Overlay::choices`] (the
//! passes by [`super::super::Overlay::passes`]), so a text built with some
//! moved is memoized apart from the plain one. The repair search
//! ([`crate::analysis::render::repair_iso`]) moves them when the text and
//! the binary disagree.

use std::collections::BTreeSet;

use super::Pass;
use crate::analysis::Overlay;

/// What kind of guess a choice point is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Kind {
    /// A type the solve picked over the machine's: the solved type, then
    /// the machine type with explicit bit casts.
    TypeConflict,
    /// Fields of a struct, then the scalars at their offsets.
    StructScalars,
    /// A frame object as an array, then as the bytes at its offsets.
    FrameView,
    /// A text pass: applied, then skipped for the function.
    PassApplication,
    /// The signedness a value is spelled with: as solved, then the
    /// machine's unsigned lane.
    Signedness,
}

impl Kind {
    /// Returns the kind's name, as a report spells it.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::TypeConflict => "type",
            Self::StructScalars => "struct",
            Self::FrameView => "frame",
            Self::PassApplication => "pass",
            Self::Signedness => "sign",
        }
    }
}

/// One choice point of a function's text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Site {
    /// A text pass.
    Pass(Pass),
    /// The frame slot at this offset from the entry stack pointer, which
    /// every access read or wrote as a float ([`super::frame::Frame`]).
    Slot(i64),
    /// The value a 64-bit integer return hands back.
    Return,
}

impl Site {
    /// Returns what kind of guess the site is.
    #[must_use]
    pub const fn kind(self) -> Kind {
        match self {
            Self::Slot(_)
            | Self::Pass(
                Pass::FloatLanes | Pass::LaneLocals | Pass::FloatBitReads | Pass::FloatBitCopies,
            ) => Kind::TypeConflict,
            Self::Pass(Pass::ApplyLayouts | Pass::NameFields | Pass::NameOwnFields) => {
                Kind::StructScalars
            }
            Self::Pass(Pass::StackArrays) => Kind::FrameView,
            Self::Return | Self::Pass(Pass::TypeParameters | Pass::TypeLocals) => Kind::Signedness,
            Self::Pass(_) => Kind::PassApplication,
        }
    }

    /// Returns the site's renderings, most readable first and literal last.
    #[must_use]
    pub const fn rungs(self) -> [&'static str; 2] {
        match self {
            Self::Slot(_) => ["solved float", "machine integer, read through bit casts"],
            Self::Return => ["as C converts it", "masked to its 32-bit lane"],
            Self::Pass(Pass::StackArrays) => ["array", "bytes at offsets"],
            Self::Pass(Pass::ApplyLayouts | Pass::NameFields | Pass::NameOwnFields) => {
                ["struct fields", "scalars at offsets"]
            }
            Self::Pass(Pass::TypeParameters | Pass::TypeLocals) => {
                ["solved signedness", "register width, signed at each use"]
            }
            Self::Pass(_) => ["applied", "skipped"],
        }
    }

    /// Returns the site as a report names it.
    #[must_use]
    pub fn name(self) -> String {
        match self {
            Self::Pass(p) => format!("pass {}", p.name()),
            Self::Slot(k) => format!("slot local_{:x}", k.unsigned_abs()),
            Self::Return => "return".to_owned(),
        }
    }

    /// Returns an overlay that renders this site at its literal rung, the
    /// rest as `o` has them.
    ///
    /// # Arguments
    ///
    /// * `o` - The overlay to move the site in.
    ///
    /// # Returns
    ///
    /// The moved overlay.
    #[must_use]
    pub fn moved(self, o: &Overlay) -> Overlay {
        let mut out = o.clone();
        match self {
            Self::Pass(p) => out.passes = out.passes.without(p),
            Self::Slot(_) | Self::Return => {
                out.choices.0.insert(self);
            }
        }
        out
    }
}

/// The recorded choice points a decompile renders at their literal rung;
/// empty for the readable text.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Choices(BTreeSet<Site>);

impl Choices {
    /// Tells whether every site renders as readably as it can.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Tells whether a site renders at its literal rung.
    ///
    /// # Arguments
    ///
    /// * `site` - The site.
    #[must_use]
    pub fn literal(&self, site: Site) -> bool {
        self.0.contains(&site)
    }

    /// Returns the moved sites in order, for a fingerprint.
    pub fn sites(&self) -> impl Iterator<Item = Site> + '_ {
        self.0.iter().copied()
    }
}

#[cfg(test)]
mod tests {
    use super::{Choices, Kind, Overlay, Pass, Site};

    /// A move renders one site literally and leaves the original alone;
    /// a pass moves through the overlay's passes, the rest through its
    /// choices.
    ///
    /// # Panics
    ///
    /// When the check fails.
    #[test]
    fn a_move_renders_one_site_literally() {
        let o = Overlay::default();
        let slot = Site::Slot(-0xc).moved(&o);
        assert!(slot.choices.literal(Site::Slot(-0xc)));
        assert!(!slot.choices.literal(Site::Return));
        assert!(slot.passes.is_empty());
        let pass = Site::Pass(Pass::StackArrays).moved(&o);
        assert!(!pass.passes.runs(Pass::StackArrays));
        assert!(pass.choices.is_empty());
        assert_eq!(o.choices, Choices::default());
        assert_ne!(slot.fingerprint(), o.fingerprint());
        assert_ne!(slot.fingerprint(), Site::Return.moved(&o).fingerprint());
    }

    /// Each kind the design names has a site, and every site's literal
    /// rung is its last.
    ///
    /// # Panics
    ///
    /// When the check fails.
    #[test]
    fn every_kind_has_a_site() {
        let sites = [
            Site::Slot(-8),
            Site::Return,
            Site::Pass(Pass::StackArrays),
            Site::Pass(Pass::ApplyLayouts),
            Site::Pass(Pass::Elvis),
        ];
        let kinds: Vec<Kind> = sites.iter().map(|s| s.kind()).collect();
        for k in [
            Kind::TypeConflict,
            Kind::StructScalars,
            Kind::FrameView,
            Kind::PassApplication,
            Kind::Signedness,
        ] {
            assert!(kinds.contains(&k), "{}", k.name());
        }
        assert_eq!(Site::Pass(Pass::Elvis).rungs(), ["applied", "skipped"]);
        assert_eq!(Site::Slot(-0x1c).name(), "slot local_1c");
    }
}
