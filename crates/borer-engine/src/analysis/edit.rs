//! Edits of the overlay as values.
//!
//! The entries an edit writes are each a [`Change`] that names the entry,
//! what it held and what it holds, so their inverses, in reverse order,
//! take the edit back ([`revert`]).
//!
//! The keys are the maps a project saves; the name tables, where they come
//! from, the passes left out and the choice points moved are never saved
//! and never written by an edit, so no change names them.
//!
//! What a tool asks for is an [`Edit`]. [`plan`] checks a list of them
//! against the program, its analysis and the overlay and works out the
//! changes they make. [`commit`] writes them only to the overlay, of the
//! program, they were planned over, refusing one planned over another as
//! [`Stale`] so the caller plans it again; only to entries that still hold
//! what each change found there; and only while the overlay stays within a
//! project's caps and its types validate. Anything else it refuses, with
//! nothing written.

use std::collections::{BTreeMap, BTreeSet, btree_map};
use std::fmt;

use super::decompile::decompile_named;
use super::protos::{self, Proto, Var, VarKey};
use super::reads::{Tag, Tracked};
use super::stated::{self, Field, Mode, Statement};
use super::utypes::{self, TypeExpr, UserType};
use super::{Analysis, Overlay, apply, cdecl, name_of, parse_addr, project, resolve};
use crate::program::Program;

/// What one entry of the overlay held and holds, `None` for an absent side.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Swap<V> {
    /// What it held before, `None` when it was absent.
    old: Option<V>,
    /// What it holds after, `None` when the edit removed it.
    new: Option<V>,
}

impl<V> Swap<V> {
    /// Returns what the entry held before, `None` when it was absent.
    #[must_use]
    pub const fn before(&self) -> Option<&V> {
        self.old.as_ref()
    }

    /// Returns what the entry holds after, `None` when it was removed.
    #[must_use]
    pub const fn after(&self) -> Option<&V> {
        self.new.as_ref()
    }

    /// Returns the swap that takes this one back.
    fn flip(self) -> Self {
        Self {
            old: self.new,
            new: self.old,
        }
    }
}

/// Returns the swap that writes `new`, its old side read when it is
/// written ([`Overlay::assign`]).
///
/// # Arguments
///
/// * `new` - What the entry holds after, `None` to remove it.
pub(crate) const fn to<V>(new: Option<V>) -> Swap<V> {
    Swap { old: None, new }
}

/// One entry of the overlay an edit added, removed or replaced, keyed by
/// the map it is in, so its key and its values are always of one kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Change {
    /// [`Overlay::names`], by address.
    Name(u64, Swap<String>),
    /// [`Overlay::comments`], by address.
    Comment(u64, Swap<String>),
    /// [`Overlay::types`], by the type's name.
    Type(String, Swap<UserType>),
    /// [`Overlay::applied`], by address.
    Applied(u64, Swap<TypeExpr>),
    /// [`Overlay::prototypes`], by function entry.
    Proto(u64, Swap<Proto>),
    /// [`Overlay::vars`], by function entry and the variable.
    Var(u64, VarKey, Swap<Var>),
    /// [`Overlay::fields`], by class and byte offset.
    Field(String, u64, Swap<Field>),
}

impl Change {
    /// Spells the entry the change is of, for a message.
    fn entry(&self) -> String {
        match self {
            Self::Name(at, _) => format!("the name at {at:#x}"),
            Self::Comment(at, _) => format!("the comment at {at:#x}"),
            Self::Type(name, _) => format!("type {}", crate::text::one_line(name)),
            Self::Applied(at, _) => format!("the type applied at {at:#x}"),
            Self::Proto(at, _) => format!("the prototype of {at:#x}"),
            Self::Var(at, ..) => format!("a variable of {at:#x}"),
            Self::Field(class, off, _) => {
                format!("field {}+{off:#x}", crate::text::one_line(class))
            }
        }
    }

    /// Returns the change that takes this one back: the same entry, from
    /// what this one leaves to what it found.
    #[must_use]
    pub fn inverse(&self) -> Self {
        match self.clone() {
            Self::Name(at, s) => Self::Name(at, s.flip()),
            Self::Comment(at, s) => Self::Comment(at, s.flip()),
            Self::Type(name, s) => Self::Type(name, s.flip()),
            Self::Applied(at, s) => Self::Applied(at, s.flip()),
            Self::Proto(at, s) => Self::Proto(at, s.flip()),
            Self::Var(at, key, s) => Self::Var(at, key, s.flip()),
            Self::Field(class, off, s) => Self::Field(class, off, s.flip()),
        }
    }
}

/// Writes `new` at `key` of `map`, or removes the entry when `new` is
/// `None`.
///
/// # Arguments
///
/// * `map` - The overlay map.
/// * `key` - The entry.
/// * `new` - What it holds after.
///
/// # Returns
///
/// What the entry held and holds.
fn swap<K: Ord, V: Clone, T: Tag>(map: &mut Tracked<K, V, T>, key: K, new: Option<V>) -> Swap<V> {
    let old = match &new {
        Some(v) => map.insert(key, v.clone()),
        None => map.remove(&key),
    };
    Swap { old, new }
}

/// Writes `new` at `inner` of `outer` in a map of maps, or removes it,
/// dropping an outer entry left empty: a function stating no variable and
/// a class stating no field leave the overlay.
///
/// # Arguments
///
/// * `map` - The overlay map of maps.
/// * `(outer, inner)` - The entry.
/// * `new` - What it holds after.
///
/// # Returns
///
/// What the entry held and holds.
fn swap_in<K: Ord, J: Ord, V: Clone, T: Tag>(
    map: &mut Tracked<K, BTreeMap<J, V>, T>,
    (outer, inner): (K, J),
    new: Option<V>,
) -> Swap<V> {
    let old = match (&new, map.entry(outer)) {
        (Some(v), held) => held.or_default().insert(inner, v.clone()),
        (None, btree_map::Entry::Occupied(mut held)) => {
            let old = held.get_mut().remove(&inner);
            if held.get().is_empty() {
                held.remove();
            }
            old
        }
        (None, btree_map::Entry::Vacant(_)) => None,
    };
    Swap { old, new }
}

/// Adds a change for each key whose entries differ between two maps, in
/// key order.
///
/// # Arguments
///
/// * `out` - The changes, extended.
/// * `(a, b)` - The map before and after.
/// * `change` - Makes the change of a key and its swap.
fn diff<K: Ord + Clone, V: PartialEq + Clone>(
    out: &mut Vec<Change>,
    (a, b): (&BTreeMap<K, V>, &BTreeMap<K, V>),
    change: impl Fn(K, Swap<V>) -> Change,
) {
    let keys: BTreeSet<&K> = a.keys().chain(b.keys()).collect();
    out.extend(keys.into_iter().filter_map(|k| {
        let (old, new) = (a.get(k), b.get(k));
        (old != new).then(|| {
            let swap = Swap {
                old: old.cloned(),
                new: new.cloned(),
            };
            change(k.clone(), swap)
        })
    }));
}

/// Returns a map of maps as one map by the outer then the inner key.
///
/// # Arguments
///
/// * `map` - The map of maps.
fn flat<K: Ord + Clone, J: Ord + Clone, V: Clone>(
    map: &BTreeMap<K, BTreeMap<J, V>>,
) -> BTreeMap<(K, J), V> {
    map.iter()
        .flat_map(|(k, inner)| {
            inner
                .iter()
                .map(|(j, v)| ((k.clone(), j.clone()), v.clone()))
        })
        .collect()
}

impl Overlay {
    /// Returns the fingerprint of the facts an edit writes: the
    /// [`Overlay::fingerprint`] of the overlay without its name tables,
    /// where they come from, the passes left out and the choice points
    /// moved, so a plan made over a copy that reads the binary's tables
    /// commits to the overlay it was copied from.
    #[must_use]
    pub fn edits_key(&self) -> u64 {
        self.without_tables().fingerprint()
    }

    /// Tells whether the overlay holds at a change's entry what the change
    /// found there, its old side, reading it unnoted ([`Tracked::raw`]).
    ///
    /// # Arguments
    ///
    /// * `change` - The change.
    fn holds(&self, change: &Change) -> bool {
        match change {
            Change::Name(at, s) => self.names.raw().get(at) == s.before(),
            Change::Comment(at, s) => self.comments.raw().get(at) == s.before(),
            Change::Type(name, s) => self.types.raw().get(name) == s.before(),
            Change::Applied(at, s) => self.applied.raw().get(at) == s.before(),
            Change::Proto(at, s) => self.prototypes.raw().get(at) == s.before(),
            Change::Var(at, key, s) => {
                self.vars.raw().get(at).and_then(|v| v.get(key)) == s.before()
            }
            Change::Field(class, off, s) => {
                self.fields.raw().get(class).and_then(|f| f.get(off)) == s.before()
            }
        }
    }

    /// Writes a change's new side at its entry, whatever the entry holds.
    ///
    /// # Arguments
    ///
    /// * `change` - The change; its old side is not read.
    ///
    /// # Returns
    ///
    /// The change as written: the entry, what it held and what it holds.
    pub(crate) fn assign(&mut self, change: Change) -> Change {
        match change {
            Change::Name(at, s) => Change::Name(at, swap(&mut self.names, at, s.new)),
            Change::Comment(at, s) => Change::Comment(at, swap(&mut self.comments, at, s.new)),
            Change::Type(name, s) => {
                let s = swap(&mut self.types, name.clone(), s.new);
                Change::Type(name, s)
            }
            Change::Applied(at, s) => Change::Applied(at, swap(&mut self.applied, at, s.new)),
            Change::Proto(at, s) => Change::Proto(at, swap(&mut self.prototypes, at, s.new)),
            Change::Var(at, key, s) => {
                Change::Var(at, key, swap_in(&mut self.vars, (at, key), s.new))
            }
            Change::Field(class, off, s) => {
                let s = swap_in(&mut self.fields, (class.clone(), off), s.new);
                Change::Field(class, off, s)
            }
        }
    }

    /// Writes the fields stated of `class` as `fields`, one change per
    /// offset that differs; no field leaves the class out of the overlay.
    ///
    /// # Arguments
    ///
    /// * `class` - The class.
    /// * `fields` - Its fields after, by byte offset.
    ///
    /// # Returns
    ///
    /// The changes written, in offset order.
    pub(crate) fn restate(&mut self, class: &str, fields: &BTreeMap<u64, Field>) -> Vec<Change> {
        let was = self.fields.raw().get(class).cloned().unwrap_or_default();
        let mut out = Vec::new();
        diff(&mut out, (&was, fields), |off, s| {
            Change::Field(class.to_owned(), off, s)
        });
        out.into_iter().map(|c| self.assign(c)).collect()
    }

    /// Returns what differs between this overlay and `after`, one change
    /// per entry added, removed or replaced, map by map in key order.
    ///
    /// # Arguments
    ///
    /// * `after` - The overlay the changes lead to.
    ///
    /// # Returns
    ///
    /// The changes; empty when the two state the same saved facts.
    pub(crate) fn changes(&self, after: &Self) -> Vec<Change> {
        let mut out = Vec::new();
        let names = (self.names.raw(), after.names.raw());
        diff(&mut out, names, Change::Name);
        let comments = (self.comments.raw(), after.comments.raw());
        diff(&mut out, comments, Change::Comment);
        let types = (self.types.raw(), after.types.raw());
        diff(&mut out, types, Change::Type);
        let applied = (self.applied.raw(), after.applied.raw());
        diff(&mut out, applied, Change::Applied);
        let protos = (self.prototypes.raw(), after.prototypes.raw());
        diff(&mut out, protos, Change::Proto);
        let vars = (flat(self.vars.raw()), flat(after.vars.raw()));
        diff(&mut out, (&vars.0, &vars.1), |(at, key), s| {
            Change::Var(at, key, s)
        });
        let fields = (flat(self.fields.raw()), flat(after.fields.raw()));
        diff(&mut out, (&fields.0, &fields.1), |(class, off), s| {
            Change::Field(class, off, s)
        });
        out
    }
}

/// Whether a name another address answers to is taken from it or refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Force {
    /// A name another address answers to is refused: two places of one
    /// name make every later lookup of it ambiguous.
    Refuse,
    /// The name is set whoever else answers to it.
    Take,
}

/// One edit a tool asks for, its addresses and values parsed.
#[derive(Debug, Clone)]
pub enum Edit {
    /// Names the function `at` is in, or the address itself when it is in
    /// none.
    Name {
        /// An address inside the function or the data named.
        at: u64,
        /// The name.
        name: String,
    },
    /// Comments an address.
    Comment {
        /// The address.
        at: u64,
        /// The comment.
        text: String,
    },
    /// Defines the types C declarations state, laid out by the binary's
    /// ABI ([`cdecl`]).
    Declare {
        /// The declarations.
        text: String,
    },
    /// States fields of a user struct, of a class borer recovered, or of
    /// a struct it defines ([`stated::plan`]).
    Fields {
        /// The struct or the class.
        name: String,
        /// The struct's size in bytes, when one is stated.
        size: Option<u64>,
        /// The fields by byte offset, in the order stated.
        fields: Vec<(u64, Field)>,
        /// Whether the fields add to what the name states or take its
        /// place.
        mode: Mode,
    },
    /// Defines an enum.
    Enum {
        /// The enum's name.
        name: String,
        /// Its width in bytes.
        size: u64,
        /// Each value and its name, in the order stated.
        values: Vec<(u64, String)>,
    },
    /// Defines a typedef.
    Alias {
        /// The typedef's name.
        name: String,
        /// The type it stands for.
        ty: TypeExpr,
    },
    /// Applies a type at a data global, which the decompiler then types
    /// the variable it renders there by.
    Apply {
        /// The global's address.
        at: u64,
        /// The type.
        ty: TypeExpr,
    },
    /// States a function's prototype.
    Proto {
        /// The function's entry.
        entry: u64,
        /// The prototype.
        proto: Proto,
    },
    /// Names, and types when a type is stated, a variable of a function,
    /// or a field of the class the function's object is of
    /// ([`stated::plan_at`]).
    Var {
        /// The function's entry.
        entry: u64,
        /// The variable as the function's text shows it (`a1`,
        /// `local_58`), or a name stated before.
        var: String,
        /// The offset `var` reads as when it spells an unnamed field as
        /// the text prints one (`field_0x270`).
        field: Option<u64>,
        /// Its new name.
        name: Option<String>,
        /// Its type as C, when one is stated.
        ty: Option<String>,
    },
    /// Defines the struct a recovered layout shows and states the
    /// prototypes that type a pointer with it, the layout read over the
    /// overlay the edit is planned over.
    Layout {
        /// Where the layout is read from.
        from: Laid,
        /// The struct's name.
        name: String,
    },
    /// Puts a project's annotations in place of the overlay's.
    Project(Box<Overlay>),
}

/// Where a layout to define as a struct is read from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Laid {
    /// The class of that name borer recovered ([`apply::from_class`]).
    Class(String),
    /// The accesses through a pointer, `<address>[,<register>]` as
    /// `borer://layout` reads it ([`apply::from_pointer`]).
    Pointer(String),
}

/// One thing a plan does, as facts a front end spells in its own words.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Line {
    /// An address takes a name.
    Named {
        /// The function's entry, or the data address.
        target: u64,
        /// Whether the target is a function rather than data.
        function: bool,
        /// The name it went by.
        old: String,
        /// The name it takes.
        new: String,
        /// The number the name also reads as, when it reads as one
        /// ([`parse_addr`]).
        number: Option<u64>,
    },
    /// An address takes a comment.
    Commented {
        /// The address.
        at: u64,
    },
    /// Types are defined from C declarations.
    Declared {
        /// How many.
        types: usize,
        /// The ABI they are laid out by.
        abi: &'static str,
        /// One line per type and per thing read loosely
        /// ([`cdecl::describe`]).
        lines: Vec<String>,
    },
    /// A type, a field, a prototype or a variable is stated.
    Stated {
        /// What a dry run says it would do, after `would`.
        would: String,
        /// What was done.
        done: String,
    },
    /// The types a stated prototype names that no user type and no C
    /// type word borer knows spells, so each passes as a word.
    Unknown(Vec<String>),
    /// A layout is defined as a struct.
    Laid {
        /// The struct's name.
        name: String,
        /// How many prototypes type a pointer with it.
        prototypes: usize,
        /// The struct with its fields, each prototype, then the notes
        /// ([`apply::Plan::describe`]).
        lines: Vec<String>,
    },
}

/// A list of edits checked and worked out over one overlay, ready to be
/// shown and committed; only [`plan`] and [`revert`] make one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    /// The program and the overlay the plan was made over ([`base`]);
    /// [`commit`] writes it to that overlay of that program only.
    base: u64,
    /// The entries it writes, in the order written.
    changes: Vec<Change>,
    /// What it does, one line per thing done, in the order of the edits.
    lines: Vec<Line>,
}

impl Plan {
    /// Returns the entries the plan writes, in the order written: what
    /// [`revert`] takes back once the plan is committed.
    #[must_use]
    pub fn changes(&self) -> &[Change] {
        &self.changes
    }

    /// Returns what the plan does, one line per thing done, in the order
    /// of the edits.
    #[must_use]
    pub fn lines(&self) -> &[Line] {
        &self.lines
    }
}

/// Why [`plan`] refused one edit of its list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refused {
    /// The index of the edit refused.
    pub edit: usize,
    /// Why, as the agent reads it.
    pub why: String,
}

impl fmt::Display for Refused {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.why)
    }
}

impl std::error::Error for Refused {}

/// Why [`commit`] refused a plan: another edit was committed to the overlay
/// since the plan was made over it, so the plan is made again.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Stale;

impl fmt::Display for Stale {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            "the annotations changed since this edit was checked; nothing was applied, so check it again",
        )
    }
}

impl std::error::Error for Stale {}

/// A plan as it is worked out: the overlay its edits leave so far, and
/// what they wrote and did.
struct Draft {
    /// The overlay the plan was made over, with the edits so far written.
    overlay: Overlay,
    /// The entries written so far.
    changes: Vec<Change>,
    /// What the edits so far do.
    lines: Vec<Line>,
}

impl Draft {
    /// Writes a change's new side to the draft's overlay and keeps the
    /// change as written.
    ///
    /// # Arguments
    ///
    /// * `change` - The change; its old side is read as it is written.
    fn put(&mut self, change: Change) {
        let written = self.overlay.assign(change);
        self.changes.push(written);
    }

    /// Checks one edit over the draft and writes it there.
    ///
    /// # Arguments
    ///
    /// * `(p, a)` - The program and its analysis.
    /// * `edit` - The edit.
    /// * `force` - Whether a taken name is taken or refused.
    ///
    /// # Errors
    ///
    /// When the edit is refused; the message says why.
    fn step(
        &mut self,
        (p, a): (&Program, &Analysis),
        edit: &Edit,
        force: Force,
    ) -> Result<(), String> {
        let word: u64 = if p.is_64 { 8 } else { 4 };
        match edit {
            Edit::Name { at, name } => self.name((p, a), *at, name, force),
            Edit::Comment { at, text } => {
                self.put(Change::Comment(*at, to(Some(text.clone()))));
                self.lines.push(Line::Commented { at: *at });
                Ok(())
            }
            Edit::Declare { text } => self.declare((p, a), text),
            Edit::Fields {
                name,
                size,
                fields,
                mode,
            } => {
                let statement = Statement {
                    name,
                    size: *size,
                    fields,
                    mode: *mode,
                };
                let plan = stated::plan(p, a, &self.overlay, &statement)?;
                stated::retyped(p, a, &self.overlay, plan.defined())?;
                self.stated(plan);
                Ok(())
            }
            Edit::Enum { name, size, values } => {
                let ty = utypes::build_enum(name, *size, values).map_err(|e| e.to_string())?;
                self.define((p, a), name, ty)
            }
            Edit::Alias { name, ty } => {
                let ty = utypes::build_alias(name, ty, &self.overlay.types, word)
                    .map_err(|e| e.to_string())?;
                self.define((p, a), name, ty)
            }
            Edit::Apply { at, ty } => self.apply_at(a, *at, ty, word),
            Edit::Proto { entry, proto } => self.prototype((p, a), *entry, proto),
            Edit::Var {
                entry,
                var,
                field,
                name,
                ty,
            } => {
                let named = (name.as_deref(), ty.as_deref());
                self.var((p, a), *entry, (var, *field), named)
            }
            Edit::Layout { from, name } => self.layout((p, a), from, name),
            Edit::Project(loaded) => {
                for change in self.overlay.changes(loaded) {
                    self.put(change);
                }
                Ok(())
            }
        }
    }

    /// Defines a recovered layout as a struct and types the pointers it is
    /// read through with it, the layout read over the draft.
    ///
    /// # Arguments
    ///
    /// * `(p, a)` - The program and its analysis.
    /// * `from` - Where the layout is read from.
    /// * `name` - The struct's name.
    ///
    /// # Errors
    ///
    /// When nothing belongs to the class, the pointer is refused, or the
    /// struct is ([`apply::from_class`], [`apply::from_pointer`]).
    fn layout(
        &mut self,
        (p, a): (&Program, &Analysis),
        from: &Laid,
        name: &str,
    ) -> Result<(), String> {
        let o = &self.overlay;
        let plan = match from {
            Laid::Class(class) => {
                apply::from_class(p, a, o, &apply::class_named(p, a, o, class)?, name)?
            }
            Laid::Pointer(spec) => apply::from_pointer(p, a, o, spec, name)?,
        };
        self.lines.push(Line::Laid {
            name: name.to_owned(),
            prototypes: plan.prototypes.len(),
            lines: plan.describe(a, o),
        });
        for change in plan.changes() {
            self.put(change);
        }
        Ok(())
    }

    /// Keeps a line saying what a statement would do and did.
    ///
    /// # Arguments
    ///
    /// * `would` - What a dry run says, after `would`.
    /// * `done` - What was done.
    fn said(&mut self, would: String, done: String) {
        self.lines.push(Line::Stated { would, done });
    }

    /// Writes a statement of fields planned over the draft, and says what
    /// it does.
    ///
    /// # Arguments
    ///
    /// * `plan` - The statement's plan ([`stated::plan`]).
    fn stated(&mut self, plan: stated::Plan) {
        self.said(plan.would(), plan.done());
        let written = plan.write(&mut self.overlay);
        self.changes.extend(written);
    }

    /// Defines the types C declarations state.
    ///
    /// # Arguments
    ///
    /// * `(p, a)` - The program and its analysis.
    /// * `text` - The declarations.
    ///
    /// # Errors
    ///
    /// When the text is refused (a construct the subset does not read, an
    /// offset assertion that fails), or the types with the overlay's would
    /// not validate or would leave a stated field standing no longer
    /// ([`stated::standing`]).
    fn declare(&mut self, (p, a): (&Program, &Analysis), text: &str) -> Result<(), String> {
        let abi = cdecl::Abi::of(p);
        let o = &self.overlay;
        let declared = cdecl::parse(text, &o.types, abi).map_err(|e| e.to_string())?;
        let mut types = BTreeMap::clone(&o.types);
        for (name, ty, _) in &declared.types {
            types.insert(name.clone(), ty.clone());
        }
        utypes::validate(&types, &o.applied).map_err(|e| e.to_string())?;
        if declared
            .types
            .iter()
            .any(|(name, ..)| o.types.contains_key(name))
        {
            stated::standing(p, a, o, &types)?;
        }
        self.lines.push(Line::Declared {
            types: declared.types.len(),
            abi: abi.name(),
            lines: cdecl::describe(&declared),
        });
        for (name, ty, _) in declared.types {
            self.put(Change::Type(name, to(Some(ty))));
        }
        Ok(())
    }

    /// Defines one type, checked as [`stated::retyped`] checks it.
    ///
    /// # Arguments
    ///
    /// * `(p, a)` - The program and its analysis.
    /// * `name` - The type's name.
    /// * `ty` - The type.
    ///
    /// # Errors
    ///
    /// When a field stated with the type it replaces would no longer
    /// stand, or the types it leaves do not validate.
    fn define(
        &mut self,
        (p, a): (&Program, &Analysis),
        name: &str,
        ty: UserType,
    ) -> Result<(), String> {
        stated::retyped(p, a, &self.overlay, Some((name, &ty)))?;
        let described = ty.describe(name);
        self.said(
            format!("define {described}"),
            format!("defined {described}"),
        );
        self.put(Change::Type(name.to_owned(), to(Some(ty))));
        Ok(())
    }

    /// Applies a type at a data global.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis, for the classes a type may name.
    /// * `at` - The global's address.
    /// * `ty` - The type.
    /// * `word` - The machine word in bytes.
    ///
    /// # Errors
    ///
    /// When the type sizes to nothing ([`stated::undefined`]), or the
    /// overlay would apply more types than a project file holds.
    fn apply_at(&mut self, a: &Analysis, at: u64, ty: &TypeExpr, word: u64) -> Result<(), String> {
        let o = &self.overlay;
        let width = utypes::width_of(&o.types, ty, word).ok_or_else(|| {
            stated::undefined(Some(a), o, ty, "set_type(name=..., fields=[...]) first")
        })?;
        let count = o
            .applied
            .len()
            .saturating_add(usize::from(!o.applied.contains_key(&at)));
        project::room("applied types", count, utypes::APPLIED_MAX)?;
        let renders = if utypes::named_enum(&o.types, ty).is_some() {
            "names its values"
        } else {
            "names its fields"
        };
        let spelled = ty.spell();
        self.said(
            format!("apply {spelled} at {at:#x} ({width} byte(s)); decompile then {renders}"),
            format!("applied {spelled} at {at:#x} ({width} byte(s)); decompile {renders}"),
        );
        self.put(Change::Applied(at, to(Some(ty.clone()))));
        Ok(())
    }

    /// States a function's prototype, noting the types it names that pass
    /// as a word.
    ///
    /// # Arguments
    ///
    /// * `(p, a)` - The program and its analysis.
    /// * `entry` - The function's entry.
    /// * `proto` - The prototype.
    ///
    /// # Errors
    ///
    /// When the overlay states as many prototypes as it holds.
    fn prototype(
        &mut self,
        (p, a): (&Program, &Analysis),
        entry: u64,
        proto: &Proto,
    ) -> Result<(), String> {
        let o = &self.overlay;
        if o.prototypes.len() >= protos::PROTOTYPES_MAX && !o.prototypes.contains_key(&entry) {
            return Err(format!(
                "the overlay states {} prototypes, the most it holds",
                o.prototypes.len()
            ));
        }
        let fname = name_of(a, o, entry);
        let bits = if p.is_64 { 64 } else { 32 };
        let unknown: Vec<String> = proto
            .ret
            .iter()
            .chain(proto.params.iter().map(|q| &q.ty))
            .filter(|t| t.pass(&o.types, bits, p.format).is_none())
            .map(protos::CType::spell)
            .collect();
        let spelled = proto.spell();
        self.said(
            format!(
                "state {fname} ({entry:#x}) as {spelled}; decompile then renders its signature, its body and every call to it by it"
            ),
            format!("stated {fname} ({entry:#x}) as {spelled}"),
        );
        if !unknown.is_empty() {
            self.lines.push(Line::Unknown(unknown));
        }
        self.put(Change::Proto(entry, to(Some(proto.clone()))));
        Ok(())
    }

    /// Names, and types when a type is stated, a variable of a function,
    /// or the field of its class a `var` spelling an unnamed field names.
    ///
    /// # Arguments
    ///
    /// * `(p, a)` - The program and its analysis.
    /// * `entry` - The function's entry.
    /// * `(var, field)` - The variable, and the offset it reads as when it
    ///   spells an unnamed field.
    /// * `(name, ty)` - Its new name, and its type if one is stated.
    ///
    /// # Errors
    ///
    /// When the variable, the field or the name is refused, or the
    /// function's text names no such variable.
    fn var(
        &mut self,
        (p, a): (&Program, &Analysis),
        entry: u64,
        (var, field): (&str, Option<u64>),
        (name, ty): (Option<&str>, Option<&str>),
    ) -> Result<(), String> {
        if let Some(off) = field.filter(|_| stated_key(&self.overlay, entry, var).is_none()) {
            let name =
                name.ok_or("naming a field needs `name`, its new name (`type` is optional)")?;
            let ty = ty
                .map(utypes::parse_type)
                .transpose()
                .map_err(|e| e.to_string())?;
            let field = Field {
                name: name.to_owned(),
                ty,
            };
            let plan = stated::plan_at(p, a, &self.overlay, entry, off, field)?;
            self.stated(plan);
            return Ok(());
        }
        let (key, named) = plan_var(p, &self.overlay, entry, var, (name, ty))?;
        let (stack, shadow, frame) = protos::slot_words(p, entry);
        let spelled = key.spell(stack, shadow, frame);
        let o = &self.overlay;
        let fname = name_of(a, o, entry);
        let held = o.vars.get(&entry);
        if !held.is_some_and(|v| v.contains_key(&key))
            && let Some(text) = decompile_named(p, a, o, entry)
            && !names_word(&text, var)
            && !names_word(&text, &spelled)
        {
            return Err(format!(
                "{fname} has no variable {spelled}: its text never names it, so a type there would invent a parameter the code does not take; decompile it for the variables it has"
            ));
        }
        let what = format!("{spelled} of {fname} ({entry:#x}) {}", named.spell());
        self.said(
            format!("name {what}; decompile then renders it so"),
            format!("named {what}"),
        );
        self.put(Change::Var(entry, key, to(Some(named))));
        Ok(())
    }

    /// Names the function `at` is in, or `at` itself when it is in none.
    ///
    /// # Arguments
    ///
    /// * `(p, a)` - The program and its analysis.
    /// * `at` - An address inside the function or the data named.
    /// * `name` - The name.
    /// * `force` - Whether a name another address answers to is taken.
    ///
    /// # Errors
    ///
    /// Under [`Force::Refuse`], when another address answers to the name,
    /// or the name reads as something else that is taken ([`resolve`]).
    fn name(
        &mut self,
        (p, a): (&Program, &Analysis),
        at: u64,
        name: &str,
        force: Force,
    ) -> Result<(), String> {
        let target = a.function_at(at).map_or(at, |f| f.entry);
        let old = name_of(a, &self.overlay, target);
        self.put(Change::Name(target, to(Some(name.to_owned()))));
        if force == Force::Refuse {
            taken(p, a, &self.overlay, target, name)?;
        }
        self.lines.push(Line::Named {
            target,
            function: a.function(target).is_some(),
            old,
            new: name.to_owned(),
            number: parse_addr(name),
        });
        Ok(())
    }

    /// Writes a change taken back over the draft, refusing what [`plan`]
    /// refuses of the entry it leaves: a name another address answers to,
    /// a variable's name another of the function's has. It says what it
    /// does as a plan does: a name's line, a comment's, else what it takes
    /// back.
    ///
    /// # Arguments
    ///
    /// * `(p, a)` - The program and its analysis.
    /// * `change` - The inverse of a committed change.
    ///
    /// # Errors
    ///
    /// When the entry no longer holds what the change found there, or what
    /// it leaves is refused.
    fn undo(&mut self, (p, a): (&Program, &Analysis), change: Change) -> Result<(), String> {
        if !self.overlay.holds(&change) {
            return Err(changed(&change));
        }
        let named = if let Change::Name(target, s) = &change {
            s.after().map(|n| (*target, n.clone()))
        } else {
            None
        };
        let var = if let Change::Var(entry, key, s) = &change {
            s.after().map(|v| (*entry, *key, v.name.clone()))
        } else {
            None
        };
        let renamed = if let Change::Name(target, _) = &change {
            Some((*target, name_of(a, &self.overlay, *target)))
        } else {
            None
        };
        let what = change.entry();
        let line = match &change {
            Change::Name(..) => None,
            Change::Comment(at, s) if s.after().is_some() => Some(Line::Commented { at: *at }),
            Change::Comment(..)
            | Change::Type(..)
            | Change::Applied(..)
            | Change::Proto(..)
            | Change::Var(..)
            | Change::Field(..) => Some(Line::Stated {
                would: format!("take back {what}"),
                done: format!("took back {what}"),
            }),
        };
        self.put(change);
        if let Some((target, name)) = &named {
            taken(p, a, &self.overlay, *target, name)?;
        }
        if let Some((entry, key, name)) = var {
            var_taken(p, &self.overlay, (entry, key), &name)?;
        }
        if let Some((target, old)) = renamed {
            self.lines.push(Line::Named {
                target,
                function: a.function(target).is_some(),
                old,
                new: name_of(a, &self.overlay, target),
                number: named.as_ref().and_then(|(_, n)| parse_addr(n)),
            });
        }
        self.lines.extend(line);
        Ok(())
    }
}

/// Says that a change's entry no longer holds what the change found there.
///
/// # Arguments
///
/// * `change` - The change.
fn changed(change: &Change) -> String {
    format!(
        "{} changed since this edit was planned; nothing was applied",
        change.entry()
    )
}

/// Refuses a name `target` takes when another address answers to it, or
/// the name reads as something else that is taken ([`resolve`]).
///
/// # Arguments
///
/// * `(p, a, o)` - The program, its analysis and the overlay that names
///   `target` so.
/// * `target` - The function's entry, or the data address.
/// * `name` - The name.
///
/// # Errors
///
/// When the name resolves anywhere else; the message says how to take it.
fn taken(p: &Program, a: &Analysis, o: &Overlay, target: u64, name: &str) -> Result<(), String> {
    match resolve(p, a, o, name) {
        Ok(found) if found == target => Ok(()),
        Ok(found) => Err(format!(
            "'{name}' already names {found:#x}; pick another name, or force=true to take it"
        )),
        Err(why) => Err(format!(
            "'{name}' is taken ({why}); pick another name, or force=true to take it"
        )),
    }
}

/// Refuses a name for a function's variable that another of its variables
/// already has.
///
/// # Arguments
///
/// * `p` - The loaded program, for how the function's text spells slots.
/// * `o` - The overlay.
/// * `(entry, key)` - The function and the variable named.
/// * `name` - The name.
///
/// # Errors
///
/// When another variable of the function has the name; the message names
/// it as the function's text spells it.
fn var_taken(
    p: &Program,
    o: &Overlay,
    (entry, key): (u64, VarKey),
    name: &str,
) -> Result<(), String> {
    let other = o
        .vars
        .get(&entry)
        .and_then(|vs| vs.iter().find(|(k, v)| v.name == name && **k != key));
    match other {
        Some((other, _)) => {
            let (stack, shadow, frame) = protos::slot_words(p, entry);
            Err(format!(
                "{name} already names {} of this function",
                other.spell(stack, shadow, frame)
            ))
        }
        None => Ok(()),
    }
}

/// Tells whether `text` holds `word` as a whole identifier, not inside a
/// longer one (`a1` is not in `a12` or `data1`).
///
/// # Arguments
///
/// * `text` - The text searched.
/// * `word` - The identifier.
fn names_word(text: &str, word: &str) -> bool {
    let ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    !word.is_empty()
        && text.match_indices(word).any(|(i, _)| {
            !text[..i].chars().next_back().is_some_and(ident)
                && !text[i + word.len()..].chars().next().is_some_and(ident)
        })
}

/// Finds the variable of a function that a name was stated for: one a
/// statement named before, else a parameter the function's prototype names.
///
/// # Arguments
///
/// * `o` - The overlay.
/// * `entry` - The function.
/// * `var` - The name.
///
/// # Returns
///
/// The variable, or `None` when nothing stated of the function gives it
/// that name.
fn stated_key(o: &Overlay, entry: u64, var: &str) -> Option<VarKey> {
    o.vars
        .get(&entry)
        .and_then(|vs| vs.iter().find(|(_, v)| v.name == var).map(|(k, _)| *k))
        .or_else(|| {
            let params = &o.prototypes.get(&entry)?.params;
            let i = params.iter().position(|q| q.name == var)?;
            u8::try_from(i).ok().map(VarKey::Param)
        })
}

/// Reads what a statement of a function's variable states: which variable
/// `var` names, and the name and type it takes.
///
/// `var` is the name the text shows (`a1`, `local_58`, `arg_8`) or one
/// stated before, the variable's or the prototype's parameter's. A slot's
/// name is read by the distances the function's text numbers its slots by
/// ([`protos::slot_words`]), so `arg_8` names the slot an arm64, ARM32 or
/// RISC-V text calls `arg_10`.
///
/// # Arguments
///
/// * `p` - The loaded program, for the function's convention.
/// * `o` - The overlay.
/// * `entry` - The function.
/// * `var` - The variable.
/// * `(name, ty)` - Its new name, and its type if one is stated.
///
/// # Errors
///
/// When `var` names no parameter or slot, `name` is missing or refused,
/// the type does not parse, another variable of the function already has
/// the name, or the overlay holds as many variables as it can.
fn plan_var(
    p: &Program,
    o: &Overlay,
    entry: u64,
    var: &str,
    (name, ty): (Option<&str>, Option<&str>),
) -> Result<(VarKey, Var), String> {
    let (stack, _, frame) = protos::slot_words(p, entry);
    let stated = o.vars.get(&entry);
    let key = stated_key(o, entry, var).map_or_else(
        || VarKey::parse(var, stack, frame).map_err(|e| e.to_string()),
        Ok,
    )?;
    let name = name.ok_or("naming a variable needs `name`, its new name (`type` is optional)")?;
    let decl = ty.map_or_else(|| name.to_owned(), |t| format!("{t} {name}"));
    let var = Var::parse(&decl).map_err(|e| e.to_string())?;
    var_taken(p, o, (entry, key), &var.name)?;
    let held: usize = o.vars.values().map(BTreeMap::len).sum();
    if held >= protos::VARS_MAX && !stated.is_some_and(|vs| vs.contains_key(&key)) {
        return Err(format!(
            "the overlay states {held} variables, the most it holds"
        ));
    }
    Ok((key, var))
}

/// Returns what a plan made over `overlay` of `program` is keyed by.
///
/// The program's bytes ([`Program::digest`]) and where they map are
/// folded with the overlay's [`Overlay::edits_key`], so a plan commits to
/// no other program's overlay that happens to state the same.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `overlay` - The overlay.
fn base(program: &Program, overlay: &Overlay) -> u64 {
    let [b0, b1, b2, b3, b4, b5, b6, b7, ..] = program.digest();
    let file = u64::from_le_bytes([b0, b1, b2, b3, b4, b5, b6, b7]);
    let mapped = super::functions::mix(file, program.image_base);
    super::functions::mix(mapped, overlay.edits_key())
}

/// Checks `edits` in order over `overlay`, each over what the ones before
/// it leave, and works out the changes they make, writing nothing.
///
/// The overlay the edits leave must hold no more than a project file
/// holds ([`project::held`]), so a dry run refuses what its commit would.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis, for the functions an address is in and
///   the names they go by.
/// * `overlay` - The overlay the edits are made over.
/// * `edits` - The edits.
/// * `force` - Whether a name another address answers to is taken or
///   refused.
///
/// # Returns
///
/// The plan, keyed by `program` and `overlay` ([`base`]).
///
/// # Errors
///
/// A [`Refused`] naming the first edit refused and why, or, when the
/// edits together would take the overlay past a cap, the cap.
pub fn plan(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    edits: &[Edit],
    force: Force,
) -> anyhow::Result<Plan> {
    let mut draft = Draft {
        overlay: overlay.clone(),
        changes: Vec::with_capacity(edits.len()),
        lines: Vec::with_capacity(edits.len()),
    };
    for (i, edit) in edits.iter().enumerate() {
        draft
            .step((program, analysis), edit, force)
            .map_err(|why| Refused { edit: i, why })?;
    }
    project::held(&draft.overlay).map_err(anyhow::Error::msg)?;
    Ok(Plan {
        base: base(program, overlay),
        changes: draft.changes,
        lines: draft.lines,
    })
}

/// Writes a plan's changes to the overlay it was made over.
///
/// Each goes to an entry that still holds what the change found there;
/// then what the analysis read under the overlay before is carried over
/// to the one it leaves ([`super::Derived::moved`]): a result that read
/// none of the entries written is kept.
///
/// What the plan leaves is held to a project's caps ([`project::held`])
/// and, when it writes a type or an application, to the checks a
/// project's types pass on load ([`utypes::validate`]).
///
/// # Arguments
///
/// * `program` - The loaded image the overlay annotates.
/// * `analysis` - The analysis whose memo is carried over.
/// * `overlay` - The overlay written.
/// * `plan` - The plan.
///
/// # Errors
///
/// [`Stale`] when `overlay`, or `program`, is not the one the plan was
/// made over; else
/// when an entry no longer holds what a change found there (an edit
/// committed since changed it), when the overlay would hold more than a
/// project file holds, or when its types would not validate. Either way
/// nothing was written.
pub fn commit(
    program: &Program,
    analysis: &Analysis,
    overlay: &mut Overlay,
    plan: &Plan,
) -> anyhow::Result<()> {
    if plan.base != base(program, overlay) {
        return Err(Stale.into());
    }
    let before = overlay.clone();
    for change in &plan.changes {
        if !overlay.holds(change) {
            *overlay = before;
            return Err(anyhow::Error::msg(changed(change)));
        }
        overlay.assign(change.clone());
    }
    let typed = plan
        .changes
        .iter()
        .any(|c| matches!(c, Change::Type(..) | Change::Applied(..)));
    let checked = project::held(overlay).and_then(|()| {
        if typed {
            utypes::validate(&overlay.types, &overlay.applied).map_err(|e| e.to_string())
        } else {
            Ok(())
        }
    });
    if let Err(why) = checked {
        *overlay = before;
        return Err(anyhow::Error::msg(why));
    }
    analysis.derived.moved(analysis, &before, overlay);
    Ok(())
}

/// Plans taking back a committed plan's changes ([`Plan::changes`]).
///
/// Their inverses, the last first, are checked over the overlay as it is
/// now as [`plan`] checks what it writes, so an undo leaves nothing a plan
/// refuses, and spelled as its lines ([`Plan::lines`]). A plan made stale
/// by a commit since ([`Stale`]) is made again by its caller.
///
/// # Arguments
///
/// * `program` - The loaded image the overlay annotates.
/// * `analysis` - Its analysis.
/// * `overlay` - The overlay the changes were committed to, as it is now.
/// * `changes` - The changes taken back.
///
/// # Errors
///
/// When an entry no longer holds what its change left there (an edit
/// since changed it), or taking the changes back would leave a name
/// another address answers to, a function's two variables of one name,
/// or a class's stated fields that no longer stand
/// ([`stated::validate`]). Caps and types are checked by [`commit`].
pub fn revert(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    changes: &[Change],
) -> anyhow::Result<Plan> {
    let mut draft = Draft {
        overlay: overlay.clone(),
        changes: Vec::with_capacity(changes.len()),
        lines: Vec::new(),
    };
    for change in changes.iter().rev() {
        draft
            .undo((program, analysis), change.inverse())
            .map_err(anyhow::Error::msg)?;
    }
    let fielded = draft
        .changes
        .iter()
        .any(|c| matches!(c, Change::Type(..) | Change::Field(..)));
    if fielded {
        stated::validate(&draft.overlay).map_err(anyhow::Error::msg)?;
    }
    Ok(Plan {
        base: base(program, overlay),
        changes: draft.changes,
        lines: draft.lines,
    })
}
