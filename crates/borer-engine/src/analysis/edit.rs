//! Edits of the overlay as values.
//!
//! The entries an edit writes, each a
//! [`Change`] that names what the entry held and what it holds, so a list
//! of them replays the edit ([`Overlay::apply`]) and their inverses, in
//! reverse order, take it back ([`Change::inverse`]).
//!
//! The keys are the maps a project saves; the name tables, where they come
//! from, the passes left out and the choice points moved are never saved
//! and never written by an edit, so no change names them.
//!
//! What a tool asks for is an [`Edit`]. [`plan`] checks a list of them
//! against the program, its analysis and the overlay and works out the
//! changes they make, and [`commit`] writes those changes to the overlay
//! they were planned over, and to no other: two edits planned at once
//! cannot both pass a check the first one's write would fail.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use super::protos::{Proto, Var, VarKey};
use super::reads::{Tag, Tracked};
use super::stated::Field;
use super::utypes::{TypeExpr, UserType};
use super::{Analysis, Overlay, name_of, parse_addr, project, resolve};
use crate::program::Program;

/// One entry of the overlay: the map it is in and its key there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Key {
    /// [`Overlay::names`], by address.
    Name(u64),
    /// [`Overlay::comments`], by address.
    Comment(u64),
    /// [`Overlay::types`], by the type's name.
    Type(String),
    /// [`Overlay::applied`], by address.
    Applied(u64),
    /// [`Overlay::prototypes`], by function entry.
    Proto(u64),
    /// [`Overlay::vars`], by function entry: every variable stated of it.
    Vars(u64),
    /// [`Overlay::fields`], by class: every field stated of it.
    Fields(String),
}

/// What an entry of the overlay holds, of the kind its [`Key`] names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// A name or a comment.
    Text(String),
    /// A user type.
    Type(UserType),
    /// A type applied at an address.
    Applied(TypeExpr),
    /// A stated prototype.
    Proto(Proto),
    /// The variables stated of one function.
    Vars(BTreeMap<VarKey, Var>),
    /// The fields stated of one class.
    Fields(BTreeMap<u64, Field>),
}

/// One entry an edit added, removed or replaced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    /// The entry.
    pub key: Key,
    /// What it held before, `None` when it was absent.
    pub old: Option<Value>,
    /// What it holds after, `None` when the edit removed it.
    pub new: Option<Value>,
}

impl Change {
    /// Returns the change that takes this one back: the same entry, from
    /// what this one leaves to what it found.
    #[must_use]
    pub fn inverse(&self) -> Self {
        Self {
            key: self.key.clone(),
            old: self.new.clone(),
            new: self.old.clone(),
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
fn set<K: Ord, V, T: Tag>(map: &mut Tracked<K, V, T>, key: K, new: Option<V>) {
    match new {
        Some(v) => map.insert(key, v),
        None => map.remove(&key),
    };
}

/// Adds a change for each key whose entries differ between two maps, in
/// key order.
///
/// # Arguments
///
/// * `out` - The changes, extended.
/// * `(a, b)` - The map before and after.
/// * `key` - Makes the [`Key`] of an entry.
/// * `value` - Makes the [`Value`] of an entry.
fn diff<K: Ord + Clone, V: PartialEq + Clone>(
    out: &mut Vec<Change>,
    (a, b): (&BTreeMap<K, V>, &BTreeMap<K, V>),
    key: impl Fn(K) -> Key,
    value: impl Fn(V) -> Value,
) {
    let keys: BTreeSet<&K> = a.keys().chain(b.keys()).collect();
    out.extend(keys.into_iter().filter_map(|k| {
        let (old, new) = (a.get(k), b.get(k));
        (old != new).then(|| Change {
            key: key(k.clone()),
            old: old.cloned().map(&value),
            new: new.cloned().map(&value),
        })
    }));
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

    /// Returns what the overlay holds at `key`, reading it unnoted
    /// ([`Tracked::raw`]).
    ///
    /// # Arguments
    ///
    /// * `key` - The entry.
    ///
    /// # Returns
    ///
    /// The value, `None` when the entry is absent.
    fn value(&self, key: &Key) -> Option<Value> {
        match key {
            Key::Name(at) => self.names.raw().get(at).cloned().map(Value::Text),
            Key::Comment(at) => self.comments.raw().get(at).cloned().map(Value::Text),
            Key::Type(name) => self.types.raw().get(name).cloned().map(Value::Type),
            Key::Applied(at) => self.applied.raw().get(at).cloned().map(Value::Applied),
            Key::Proto(at) => self.prototypes.raw().get(at).cloned().map(Value::Proto),
            Key::Vars(at) => self.vars.raw().get(at).cloned().map(Value::Vars),
            Key::Fields(class) => self.fields.raw().get(class).cloned().map(Value::Fields),
        }
    }

    /// Writes `new` at `key`, or removes the entry when `new` is `None`.
    ///
    /// A value not of its key's kind writes nothing; no edit makes one.
    ///
    /// # Arguments
    ///
    /// * `key` - The entry.
    /// * `new` - What it holds after.
    ///
    /// # Returns
    ///
    /// The change: the entry, what it held and what it holds now.
    pub fn put(&mut self, key: Key, new: Option<Value>) -> Change {
        let old = self.value(&key);
        match (&key, new.clone()) {
            (Key::Name(at), Some(Value::Text(t))) => set(&mut self.names, *at, Some(t)),
            (Key::Name(at), None) => set(&mut self.names, *at, None),
            (Key::Comment(at), Some(Value::Text(t))) => set(&mut self.comments, *at, Some(t)),
            (Key::Comment(at), None) => set(&mut self.comments, *at, None),
            (Key::Type(n), Some(Value::Type(ty))) => set(&mut self.types, n.clone(), Some(ty)),
            (Key::Type(n), None) => set(&mut self.types, n.clone(), None),
            (Key::Applied(at), Some(Value::Applied(ty))) => set(&mut self.applied, *at, Some(ty)),
            (Key::Applied(at), None) => set(&mut self.applied, *at, None),
            (Key::Proto(at), Some(Value::Proto(p))) => set(&mut self.prototypes, *at, Some(p)),
            (Key::Proto(at), None) => set(&mut self.prototypes, *at, None),
            (Key::Vars(at), Some(Value::Vars(v))) => set(&mut self.vars, *at, Some(v)),
            (Key::Vars(at), None) => set(&mut self.vars, *at, None),
            (Key::Fields(c), Some(Value::Fields(f))) => set(&mut self.fields, c.clone(), Some(f)),
            (Key::Fields(c), None) => set(&mut self.fields, c.clone(), None),
            (
                Key::Name(_)
                | Key::Comment(_)
                | Key::Type(_)
                | Key::Applied(_)
                | Key::Proto(_)
                | Key::Vars(_)
                | Key::Fields(_),
                Some(
                    Value::Text(_)
                    | Value::Type(_)
                    | Value::Applied(_)
                    | Value::Proto(_)
                    | Value::Vars(_)
                    | Value::Fields(_),
                ),
            ) => {}
        }
        Change { key, old, new }
    }

    /// Applies `changes` in order: each writes its new value at its key,
    /// or removes the entry when it has none ([`Overlay::put`]).
    ///
    /// # Arguments
    ///
    /// * `changes` - The changes.
    pub fn apply(&mut self, changes: &[Change]) {
        for change in changes {
            self.put(change.key.clone(), change.new.clone());
        }
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
    #[must_use]
    pub fn changes(&self, after: &Self) -> Vec<Change> {
        let mut out = Vec::new();
        let names = (self.names.raw(), after.names.raw());
        diff(&mut out, names, Key::Name, Value::Text);
        let comments = (self.comments.raw(), after.comments.raw());
        diff(&mut out, comments, Key::Comment, Value::Text);
        let types = (self.types.raw(), after.types.raw());
        diff(&mut out, types, Key::Type, Value::Type);
        let applied = (self.applied.raw(), after.applied.raw());
        diff(&mut out, applied, Key::Applied, Value::Applied);
        let protos = (self.prototypes.raw(), after.prototypes.raw());
        diff(&mut out, protos, Key::Proto, Value::Proto);
        let vars = (self.vars.raw(), after.vars.raw());
        diff(&mut out, vars, Key::Vars, Value::Vars);
        let fields = (self.fields.raw(), after.fields.raw());
        diff(&mut out, fields, Key::Fields, Value::Fields);
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
}

/// A list of edits checked and worked out over one overlay, ready to be
/// shown and committed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    /// The [`Overlay::edits_key`] of the overlay the plan was made over;
    /// [`commit`] writes it to that overlay only.
    pub base: u64,
    /// The entries it writes, in the order written.
    pub changes: Vec<Change>,
    /// What it does, one line per thing done, in the order of the edits.
    pub lines: Vec<Line>,
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
    /// Writes `new` at `key` of the draft's overlay and keeps the change.
    ///
    /// # Arguments
    ///
    /// * `key` - The entry.
    /// * `new` - What it holds after.
    fn put(&mut self, key: Key, new: Option<Value>) {
        let change = self.overlay.put(key, new);
        self.changes.push(change);
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
        match edit {
            Edit::Name { at, name } => self.name((p, a), *at, name, force),
            Edit::Comment { at, text } => {
                self.put(Key::Comment(*at), Some(Value::Text(text.clone())));
                self.lines.push(Line::Commented { at: *at });
                Ok(())
            }
        }
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
        self.put(Key::Name(target), Some(Value::Text(name.to_owned())));
        if force == Force::Refuse {
            match resolve(p, a, &self.overlay, name) {
                Ok(found) if found == target => {}
                Ok(found) => {
                    return Err(format!(
                        "'{name}' already names {found:#x}; pick another name, or force=true to take it"
                    ));
                }
                Err(why) => {
                    return Err(format!(
                        "'{name}' is taken ({why}); pick another name, or force=true to take it"
                    ));
                }
            }
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
/// The plan, whose base is `overlay`'s [`Overlay::edits_key`].
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
        base: overlay.edits_key(),
        changes: draft.changes,
        lines: draft.lines,
    })
}

/// Writes a plan's changes to the overlay it was made over.
///
/// It then carries
/// what the analysis read under the overlay before over to the one it
/// leaves ([`super::Derived::moved`]): a result that read none of the
/// entries written is kept.
///
/// # Arguments
///
/// * `analysis` - The analysis whose memo is carried over.
/// * `overlay` - The overlay written.
/// * `plan` - The plan.
///
/// # Returns
///
/// The changes written.
///
/// # Errors
///
/// [`Stale`] when `overlay` is not the one the plan was made over; else,
/// when the overlay would hold more than a project file holds
/// ([`project::held`]), the cap. Either way nothing was written.
pub fn commit(
    analysis: &Analysis,
    overlay: &mut Overlay,
    plan: &Plan,
) -> anyhow::Result<Vec<Change>> {
    if plan.base != overlay.edits_key() {
        return Err(Stale.into());
    }
    let before = overlay.clone();
    let changes: Vec<Change> = plan
        .changes
        .iter()
        .map(|c| overlay.put(c.key.clone(), c.new.clone()))
        .collect();
    if let Err(why) = project::held(overlay) {
        *overlay = before;
        return Err(anyhow::Error::msg(why));
    }
    analysis.derived.moved(analysis, &before, overlay);
    Ok(changes)
}
