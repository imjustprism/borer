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

use std::collections::{BTreeMap, BTreeSet};

use super::Overlay;
use super::protos::{Proto, Var, VarKey};
use super::reads::{Tag, Tracked};
use super::stated::Field;
use super::utypes::{TypeExpr, UserType};

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
