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

use super::decompile::decompile_named;
use super::protos::{self, Proto, Var, VarKey};
use super::reads::{Tag, Tracked};
use super::stated::{self, Field, Mode, Statement};
use super::utypes::{self, TypeExpr, UserType};
use super::{Analysis, Overlay, cdecl, name_of, parse_addr, project, resolve};
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
        let word: u64 = if p.is_64 { 8 } else { 4 };
        match edit {
            Edit::Name { at, name } => self.name((p, a), *at, name, force),
            Edit::Comment { at, text } => {
                self.put(Key::Comment(*at), Some(Value::Text(text.clone())));
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
        }
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
        let (key, new) = plan.write();
        self.put(key, new);
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
            self.put(Key::Type(name), Some(Value::Type(ty)));
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
        self.put(Key::Type(name.to_owned()), Some(Value::Type(ty)));
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
        self.put(Key::Applied(at), Some(Value::Applied(ty.clone())));
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
        self.put(Key::Proto(entry), Some(Value::Proto(proto.clone())));
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
        let mut vars = held.cloned().unwrap_or_default();
        vars.insert(key, named);
        self.said(
            format!("name {what}; decompile then renders it so"),
            format!("named {what}"),
        );
        self.put(Key::Vars(entry), Some(Value::Vars(vars)));
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
    let (stack, shadow, frame) = protos::slot_words(p, entry);
    let stated = o.vars.get(&entry);
    let key = stated_key(o, entry, var).map_or_else(
        || VarKey::parse(var, stack, frame).map_err(|e| e.to_string()),
        Ok,
    )?;
    let name = name.ok_or("naming a variable needs `name`, its new name (`type` is optional)")?;
    let decl = ty.map_or_else(|| name.to_owned(), |t| format!("{t} {name}"));
    let var = Var::parse(&decl).map_err(|e| e.to_string())?;
    if let Some((other, _)) =
        stated.and_then(|vs| vs.iter().find(|(k, v)| v.name == var.name && **k != key))
    {
        return Err(format!(
            "{} already names {} of this function",
            var.name,
            other.spell(stack, shadow, frame)
        ));
    }
    let held: usize = o.vars.values().map(BTreeMap::len).sum();
    if held >= protos::VARS_MAX && !stated.is_some_and(|vs| vs.contains_key(&key)) {
        return Err(format!(
            "the overlay states {held} variables, the most it holds"
        ));
    }
    Ok((key, var))
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
