//! The overlay facts a memoized result read, so an edit lets go of only the
//! results that read what it changed.
//!
//! Each map of an [`Overlay`] is a [`Tracked`] map. Looking one key up
//! ([`Tracked::get`], [`Tracked::contains_key`]) notes that key as read;
//! every other read (iterating, borrowing the whole map) notes the whole
//! field. A note goes to the result being built on this thread, the top of
//! a per-thread stack of [`Frame`]s that [`recording`] pushes around each
//! build in [`super::Derived`]. A result built inside another's build adds
//! its reads to the outer one, built or found, so what an outer result
//! read includes what it took from inner ones. A thread a build spawns
//! takes the build's frame along ([`Handle`]), so work spread across cores
//! is noted too.
//!
//! A whole-program index read under the names (the methods of each class,
//! the functions going by each name) reads every name, so a result that
//! took it would read every name too. Where a result looks the index up by
//! one value, it takes the index unnoted ([`unnoted`]) and notes the value
//! instead: the class it looked up ([`note_class`]), or the body whose
//! `name(` calls it matched ([`note_body`]).
//!
//! An edit is the facts that differ between two overlays ([`Edit`]): the
//! keys whose entries were added, removed or changed, by field, and for a
//! renamed address its class and the call to it by name, before and after.
//! A result
//! whose reads miss every one of them reads the same facts under the
//! new overlay as under the old, and a result is a pure function of what
//! it reads, so it is the same result. That makes the read-set the granularity
//! of invalidation and the fingerprint only the key it is filed under.
//!
//! A read-set holds its keys sorted, as a byte string of variable-length
//! gaps between them ([`Reads::keys`]): an address a few bytes past the one
//! before it costs one or two bytes. Keys that are not addresses (a type's
//! name, a class) are folded to 64 bits by a seedless hash, so two
//! keys may share a fact; that only lets go of a result that did not need
//! to go.

use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::sync::{Arc, Mutex, PoisonError};

use crate::fxmap::FxHashSet;

use super::{Analysis, Overlay};

/// One kind of fact a result reads: a map of an [`Overlay`] by its key, or
/// a value names take.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Field {
    /// [`Overlay::names`], by address.
    Names,
    /// [`Overlay::comments`], by address.
    Comments,
    /// [`Overlay::types`], by the type's name.
    Types,
    /// [`Overlay::applied`], by address.
    Applied,
    /// [`Overlay::prototypes`], by function entry.
    Prototypes,
    /// [`Overlay::vars`], by function entry.
    Vars,
    /// [`Overlay::enums`], by the encoding function's name.
    Enums,
    /// The functions a name qualifies with a class
    /// ([`super::classes::class_of`]), by the class.
    Class,
}

impl Field {
    /// Every field, in order; a field's place is its code in
    /// [`Reads::keys`].
    const ALL: [Self; 8] = [
        Self::Names,
        Self::Comments,
        Self::Types,
        Self::Applied,
        Self::Prototypes,
        Self::Vars,
        Self::Enums,
        Self::Class,
    ];

    /// The field's bit in a mask of fields, by its [`Field::code`].
    const fn bit(self) -> u8 {
        1 << self.code()
    }

    /// The field's code in [`Reads::keys`], its place in [`Field::ALL`].
    const fn code(self) -> u8 {
        match self {
            Self::Names => 0,
            Self::Comments => 1,
            Self::Types => 2,
            Self::Applied => 3,
            Self::Prototypes => 4,
            Self::Vars => 5,
            Self::Enums => 6,
            Self::Class => 7,
        }
    }
}

/// Names the [`Field`] a [`Tracked`] map is, in its type.
pub trait Tag {
    /// The field.
    const FIELD: Field;
}

/// Declares the zero-sized [`Tag`] of each field.
macro_rules! tags {
    ($($(#[$doc:meta])* $tag:ident => $field:ident;)*) => {$(
        $(#[$doc])*
        #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
        pub struct $tag;

        impl Tag for $tag {
            const FIELD: Field = Field::$field;
        }
    )*};
}

tags! {
    /// The tag of [`Overlay::names`].
    NamesTag => Names;
    /// The tag of [`Overlay::comments`].
    CommentsTag => Comments;
    /// The tag of [`Overlay::types`].
    TypesTag => Types;
    /// The tag of [`Overlay::applied`].
    AppliedTag => Applied;
    /// The tag of [`Overlay::prototypes`].
    PrototypesTag => Prototypes;
    /// The tag of [`Overlay::vars`].
    VarsTag => Vars;
    /// The tag of [`Overlay::enums`].
    EnumsTag => Enums;
}

/// A map key folded to the 64 bits a read-set holds.
pub trait FactKey {
    /// Returns the key's fact: an address as itself, text by a seedless
    /// hash of its bytes.
    fn fact(&self) -> u64;
}

impl FactKey for u64 {
    fn fact(&self) -> u64 {
        *self
    }
}

/// The FNV-1a 64-bit offset basis, where a text's fact starts.
const FNV_BASIS: u64 = 0xcbf2_9ce4_8422_2325;

/// The FNV-1a 64-bit prime, each byte of a text's fact multiplied in.
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

impl FactKey for str {
    fn fact(&self) -> u64 {
        self.bytes()
            .fold(FNV_BASIS, |h, b| (h ^ u64::from(b)).wrapping_mul(FNV_PRIME))
    }
}

impl FactKey for String {
    fn fact(&self) -> u64 {
        self.as_str().fact()
    }
}

/// A map of an [`Overlay`] that notes what a build reads of it.
///
/// A key looked up is noted as that key; anything else that reads the map
/// (through [`Deref`], [`DerefMut`] or iteration) is noted as the whole
/// field, so no read goes unnoted. Writing through [`DerefMut`] notes the
/// whole field too, since a write can read (an `insert` returns the entry
/// it replaced).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(
    transparent,
    bound(serialize = "K: serde::Serialize + Ord, V: serde::Serialize")
)]
#[serde(bound(deserialize = "K: serde::Deserialize<'de> + Ord, V: serde::Deserialize<'de>"))]
pub struct Tracked<K, V, T> {
    /// The entries.
    map: BTreeMap<K, V>,
    /// Which field the map is.
    #[serde(skip)]
    tag: PhantomData<T>,
}

impl<K, V, T> Default for Tracked<K, V, T> {
    fn default() -> Self {
        Self {
            map: BTreeMap::new(),
            tag: PhantomData,
        }
    }
}

impl<K, V, T> From<BTreeMap<K, V>> for Tracked<K, V, T> {
    fn from(map: BTreeMap<K, V>) -> Self {
        Self {
            map,
            tag: PhantomData,
        }
    }
}

impl<K: Ord, V, T> FromIterator<(K, V)> for Tracked<K, V, T> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        BTreeMap::from_iter(iter).into()
    }
}

impl<K: Ord, V, T: Tag> Tracked<K, V, T> {
    /// Returns the entry at `key`, noting the key as read.
    ///
    /// # Arguments
    ///
    /// * `key` - The key, or a borrowed form of it.
    ///
    /// # Returns
    ///
    /// The entry, `None` when there is none.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + FactKey + ?Sized,
    {
        note(T::FIELD, key.fact());
        self.map.get(key)
    }

    /// Tells whether there is an entry at `key`, noting the key as read.
    ///
    /// # Arguments
    ///
    /// * `key` - The key, or a borrowed form of it.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + FactKey + ?Sized,
    {
        note(T::FIELD, key.fact());
        self.map.contains_key(key)
    }
}

impl<K, V, T> Tracked<K, V, T> {
    /// Returns the entries without noting a read: for keying a memo by the
    /// overlay ([`Overlay::fingerprint`]), copying it, and telling two
    /// overlays apart ([`Edit::between`]), none of which reaches a result.
    #[must_use]
    pub(crate) const fn raw(&self) -> &BTreeMap<K, V> {
        &self.map
    }
}

impl<K, V, T: Tag> Deref for Tracked<K, V, T> {
    type Target = BTreeMap<K, V>;

    fn deref(&self) -> &Self::Target {
        note_whole(T::FIELD);
        &self.map
    }
}

impl<K, V, T: Tag> DerefMut for Tracked<K, V, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        note_whole(T::FIELD);
        &mut self.map
    }
}

impl<'a, K, V, T: Tag> IntoIterator for &'a Tracked<K, V, T> {
    type Item = (&'a K, &'a V);
    type IntoIter = std::collections::btree_map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        note_whole(T::FIELD);
        self.map.iter()
    }
}

impl<K, V, T: Tag> IntoIterator for Tracked<K, V, T> {
    type Item = (K, V);
    type IntoIter = std::collections::btree_map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        note_whole(T::FIELD);
        self.map.into_iter()
    }
}

/// Bits of a value each byte of a [`put_varint`] value carries.
const VARINT_BITS: u32 = 7;

/// The bits of a [`put_varint`] byte that carry the value.
const VARINT_LOW: u8 = 0x7f;

/// The bit of a [`put_varint`] byte set when more bytes follow.
const VARINT_MORE: u8 = 0x80;

/// Appends `v` to `out` seven bits a byte, low bits first, the top bit of
/// each byte but the last set.
///
/// # Arguments
///
/// * `out` - The byte string.
/// * `v` - The value.
fn put_varint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let low = crate::num::lo8(v) & VARINT_LOW;
        v >>= VARINT_BITS;
        if v == 0 {
            out.push(low);
            return;
        }
        out.push(low | VARINT_MORE);
    }
}

/// Reads one value [`put_varint`] wrote, advancing `at`.
///
/// # Arguments
///
/// * `bytes` - The byte string.
/// * `at` - Where the value starts; left past it.
///
/// # Returns
///
/// The value, or `None` past the end.
fn take_varint(bytes: &[u8], at: &mut usize) -> Option<u64> {
    let mut v = 0_u64;
    let mut shift = 0_u32;
    loop {
        let b = *bytes.get(*at)?;
        *at += 1;
        v |= u64::from(b & VARINT_LOW).checked_shl(shift)?;
        if b & VARINT_MORE == 0 {
            return Some(v);
        }
        shift += VARINT_BITS;
    }
}

/// The overlay facts one result read: frozen from a [`Frame`] when its
/// build ends.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Reads {
    /// Fields read whole, as [`Field::bit`]s.
    whole: u8,
    /// How many keys [`Reads::keys`] holds.
    len: usize,
    /// The keys read, sorted by field then key: for each field read by key,
    /// its [`Field::code`] byte, the count of its keys, its first key, and
    /// the gap from each key to the next, each count, key and gap a
    /// [`put_varint`] value.
    keys: Box<[u8]>,
    /// The bodies whose `name(` calls the result looked names up by
    /// ([`note_body`]).
    texts: Box<[Arc<str>]>,
    /// Bytes of the bodies the build itself noted, not those it took with
    /// another result, which that result counts.
    own_texts: usize,
}

impl Reads {
    /// Returns the heap bytes the read-set holds of its own: its keys, the
    /// handles of its bodies, and the bodies its build noted itself.
    #[must_use]
    pub fn bytes(&self) -> usize {
        self.keys.len() + size_of_val(&*self.texts) + self.own_texts
    }

    /// Returns how many keys the read-set names.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Tells whether the read-set names no key, no whole field and no body.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.whole == 0 && self.len == 0 && self.texts.is_empty()
    }

    /// Tells whether `field` was read whole.
    ///
    /// # Arguments
    ///
    /// * `field` - The field.
    #[must_use]
    pub const fn whole(&self, field: Field) -> bool {
        self.whole & field.bit() != 0
    }

    /// Returns the keys read, sorted by field then key.
    ///
    /// # Returns
    ///
    /// Each key with its field, decoded from [`Reads::keys`] as it is
    /// asked for.
    pub fn keys(&self) -> impl Iterator<Item = (Field, u64)> + '_ {
        let mut at = 0;
        let mut field = None;
        let mut left = 0_u64;
        let mut key = 0_u64;
        std::iter::from_fn(move || {
            if left == 0 {
                let code = *self.keys.get(at)?;
                at += 1;
                field = Field::ALL.get(usize::from(code)).copied();
                left = take_varint(&self.keys, &mut at)?;
                key = take_varint(&self.keys, &mut at)?;
            } else {
                key = key.wrapping_add(take_varint(&self.keys, &mut at)?);
            }
            left -= 1;
            Some((field?, key))
        })
    }
}

/// What many results read of the overlay, summed
/// ([`super::Derived::read_stats`]).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct ReadStats {
    /// Results counted.
    pub results: usize,
    /// Keys their read-sets name, summed.
    pub keys: usize,
    /// Heap bytes their read-sets hold, summed.
    pub bytes: usize,
    /// Results that read [`Overlay::names`] whole, so any rename lets them
    /// go.
    pub names_whole: usize,
}

impl ReadStats {
    /// Returns the sums with one more result's reads added.
    ///
    /// # Arguments
    ///
    /// * `reads` - What the result read.
    #[must_use]
    pub fn with(self, reads: &Reads) -> Self {
        Self {
            results: self.results + 1,
            keys: self.keys + reads.len(),
            bytes: self.bytes + reads.bytes(),
            names_whole: self.names_whole + usize::from(reads.whole(Field::Names)),
        }
    }
}

/// What a build has read so far, shared by the threads it runs on.
#[derive(Debug, Default)]
struct Frame {
    /// Fields read whole, as [`Field::bit`]s.
    whole: u8,
    /// Keys read.
    keys: FxHashSet<(Field, u64)>,
    /// Bodies looked names up by, each once.
    texts: Vec<Arc<str>>,
    /// Bytes of the bodies the build itself noted.
    own_texts: usize,
}

impl Frame {
    /// Freezes what was read into a [`Reads`], keys in order.
    ///
    /// # Returns
    ///
    /// The read-set, its keys encoded as [`Reads::keys`] says.
    fn freeze(self) -> Reads {
        let mut sorted: Vec<(Field, u64)> = self.keys.into_iter().collect();
        sorted.sort_unstable();
        let mut keys = Vec::new();
        for run in sorted.chunk_by(|a, b| a.0 == b.0) {
            let Some(&(field, first)) = run.first() else {
                continue;
            };
            keys.push(field.code());
            put_varint(&mut keys, crate::num::from_usize(run.len()));
            put_varint(&mut keys, first);
            for pair in run.windows(2) {
                if let [(_, a), (_, b)] = pair {
                    put_varint(&mut keys, b - a);
                }
            }
        }
        Reads {
            whole: self.whole,
            len: sorted.len(),
            keys: keys.into_boxed_slice(),
            texts: self.texts.into_boxed_slice(),
            own_texts: self.own_texts,
        }
    }

    /// Adds a body, unless the frame holds it already.
    ///
    /// # Arguments
    ///
    /// * `text` - The body.
    fn add_text(&mut self, text: &Arc<str>) {
        if !self.texts.iter().any(|t| Arc::ptr_eq(t, text)) {
            self.texts.push(Arc::clone(text));
        }
    }
}

/// A frame shared between the threads of one build.
type Shared = Arc<Mutex<Frame>>;

thread_local! {
    /// The frames of the builds running on this thread, innermost last.
    static FRAMES: RefCell<Vec<Shared>> = const { RefCell::new(Vec::new()) };
}

/// Applies `f` to the innermost frame on this thread, when a build runs.
///
/// # Arguments
///
/// * `f` - Adds to the frame.
fn with_top(f: impl FnOnce(&mut Frame)) {
    FRAMES.with(|frames| {
        if let Some(top) = frames.borrow().last() {
            f(&mut top.lock().unwrap_or_else(PoisonError::into_inner));
        }
    });
}

/// Notes `key` of `field` as read by the build running on this thread.
///
/// # Arguments
///
/// * `field` - The overlay map.
/// * `key` - The key's [`FactKey::fact`].
fn note(field: Field, key: u64) {
    with_top(|frame| {
        frame.keys.insert((field, key));
    });
}

/// Notes `field` as read whole by the build running on this thread.
///
/// # Arguments
///
/// * `field` - The overlay map.
fn note_whole(field: Field) {
    with_top(|frame| frame.whole |= field.bit());
}

/// Notes that the build running on this thread took the functions a name
/// qualifies with `class` from an index it took [`unnoted`].
///
/// # Arguments
///
/// * `class` - The class, as [`super::classes::class_of`] spells it.
pub(crate) fn note_class(class: &str) {
    note(Field::Class, class.fact());
}

/// Notes that the build running on this thread took, from an index it took
/// [`unnoted`], the functions going by every display name `name` for which
/// `name(` occurs in `body`.
///
/// # Arguments
///
/// * `body` - The text whose calls were looked up.
pub(crate) fn note_body(body: &Arc<str>) {
    with_top(|frame| {
        frame.own_texts += body.len();
        frame.add_text(body);
    });
}

/// Adds what a result read to the build running on this thread, which
/// took that result.
///
/// # Arguments
///
/// * `reads` - What the result read.
pub(crate) fn absorb(reads: &Reads) {
    if reads.is_empty() {
        return;
    }
    with_top(|frame| {
        frame.whole |= reads.whole;
        frame.keys.extend(reads.keys());
        for text in &reads.texts {
            frame.add_text(text);
        }
    });
}

/// Pops this thread's innermost frame when dropped, so a build that
/// unwinds leaves the stack as it found it.
struct Pop;

impl Drop for Pop {
    fn drop(&mut self) {
        FRAMES.with(|frames| frames.borrow_mut().pop());
    }
}

/// Runs `f` with `frame` as this thread's innermost frame.
///
/// # Arguments
///
/// * `frame` - Collects what `f` reads.
/// * `f` - The work.
///
/// # Returns
///
/// What `f` returned.
fn within<R>(frame: Shared, f: impl FnOnce() -> R) -> R {
    FRAMES.with(|frames| frames.borrow_mut().push(frame));
    let _pop = Pop;
    f()
}

/// Runs a build, noting what it reads.
///
/// # Arguments
///
/// * `make` - The build.
///
/// # Returns
///
/// What `make` returned, and the overlay facts it and every result it took
/// read.
pub(crate) fn recording<R>(make: impl FnOnce() -> R) -> (R, Reads) {
    let frame = Shared::default();
    let value = within(Arc::clone(&frame), make);
    let frame = std::mem::take(&mut *frame.lock().unwrap_or_else(PoisonError::into_inner));
    (value, frame.freeze())
}

/// Runs `f` without noting what it reads into the build running on this
/// thread.
///
/// For taking a whole-program index the build then looks up by one value,
/// which it notes itself ([`note_class`], [`note_body`]).
///
/// # Arguments
///
/// * `f` - Takes the index.
///
/// # Returns
///
/// What `f` returned.
pub(crate) fn unnoted<R>(f: impl FnOnce() -> R) -> R {
    within(Shared::default(), f)
}

/// The build running on one thread, for a thread it spawns to note its
/// reads into.
#[derive(Debug, Clone, Default)]
pub(crate) struct Handle(Option<Shared>);

impl Handle {
    /// Returns the build running on this thread, if any.
    pub(crate) fn here() -> Self {
        Self(FRAMES.with(|frames| frames.borrow().last().cloned()))
    }

    /// Runs `f`, on whatever thread, noting its reads into the build this
    /// handle names.
    ///
    /// # Arguments
    ///
    /// * `f` - The work.
    ///
    /// # Returns
    ///
    /// What `f` returned.
    pub(crate) fn enter<R>(self, f: impl FnOnce() -> R) -> R {
        match self.0 {
            Some(frame) => within(frame, f),
            None => f(),
        }
    }
}

/// The facts that differ between two overlays.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Edit {
    /// Fields with any key changed, as [`Field::bit`]s.
    fields: u8,
    /// Keys whose entries were added, removed or changed, and the classes
    /// a renamed address went by before and after.
    keys: FxHashSet<(Field, u64)>,
    /// `name(` for each display name a renamed address went by before and
    /// after, as a body that called it reads.
    calls: Vec<String>,
}

impl Edit {
    /// Returns the facts that differ between `before` and `after`.
    ///
    /// # Arguments
    ///
    /// * `analysis` - Supplies the names functions go by without the
    ///   overlay's.
    /// * `before` - The overlay results were read under.
    /// * `after` - The overlay now in force.
    ///
    /// # Returns
    ///
    /// The edit, or `None` when the two differ in where name tables come
    /// from ([`Overlay::enum_source`]), which no read-set notes.
    #[must_use]
    pub fn between(analysis: &Analysis, before: &Overlay, after: &Overlay) -> Option<Self> {
        if before.enum_source != after.enum_source {
            return None;
        }
        let mut edit = Self::default();
        for renamed in edit.diff(&before.names, &after.names) {
            for o in [before, after] {
                edit.renamed(analysis, o, renamed);
            }
        }
        edit.diff(&before.comments, &after.comments);
        edit.diff(&before.types, &after.types);
        edit.diff(&before.applied, &after.applied);
        edit.diff(&before.prototypes, &after.prototypes);
        edit.diff(&before.vars, &after.vars);
        edit.diff(&before.enums, &after.enums);
        Some(edit)
    }

    /// Tells whether the edit changed nothing.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.fields == 0
    }

    /// Tells whether the edit changed a fact `reads` names: a key read, any
    /// key of a field read whole, or a call a body read names.
    ///
    /// # Arguments
    ///
    /// * `reads` - What a result read.
    #[must_use]
    pub fn touches(&self, reads: &Reads) -> bool {
        reads.whole & self.fields != 0
            || reads.keys().any(|k| self.keys.contains(&k))
            || reads
                .texts
                .iter()
                .any(|body| self.calls.iter().any(|call| body.contains(call.as_str())))
    }

    /// Adds the keys of one field whose entries differ between `a` and `b`.
    ///
    /// # Arguments
    ///
    /// * `a` - The field before.
    /// * `b` - The field after.
    ///
    /// # Returns
    ///
    /// The keys that differ.
    fn diff<K: Ord + FactKey + Clone, V: PartialEq, T: Tag>(
        &mut self,
        a: &Tracked<K, V, T>,
        b: &Tracked<K, V, T>,
    ) -> Vec<K> {
        let (a, b) = (a.raw(), b.raw());
        let changed: Vec<K> = a
            .iter()
            .filter(|(k, v)| b.get(*k) != Some(*v))
            .map(|(k, _)| k)
            .chain(b.keys().filter(|k| !a.contains_key(*k)))
            .cloned()
            .collect();
        for key in &changed {
            self.fields |= T::FIELD.bit();
            self.keys.insert((T::FIELD, key.fact()));
        }
        changed
    }

    /// Adds the class `at` goes by under `overlay`, and the call a body
    /// makes to it by its display name ([`super::name_of`]).
    ///
    /// # Arguments
    ///
    /// * `analysis` - Supplies the names functions go by without the
    ///   overlay's.
    /// * `overlay` - The overlay before or after the edit.
    /// * `at` - A renamed address.
    fn renamed(&mut self, analysis: &Analysis, overlay: &Overlay, at: u64) {
        let declared = overlay
            .names
            .raw()
            .get(&at)
            .or_else(|| analysis.function(at).and_then(|f| f.name.as_ref()));
        if let Some(class) = declared.and_then(|n| super::classes::class_of(n)) {
            self.fields |= Field::Class.bit();
            self.keys.insert((Field::Class, class.fact()));
        }
        self.calls
            .push(declared.map_or_else(|| format!("sub_{at:x}("), |n| format!("{n}(")));
    }
}

#[cfg(test)]
mod tests {
    use super::{FactKey, Field, Handle, absorb, note_body, note_class, recording, unnoted};
    use crate::analysis::Overlay;
    use std::sync::Arc;

    /// A build's reads come back as it made them, in order.
    ///
    /// A key looked up, keys far apart and at the ends of the range, a
    /// field read whole, a value noted, and what a thread it spawned read
    /// all come back; what it read unnoted does not.
    ///
    /// # Panics
    ///
    /// When a read is lost, one read unnoted is kept, or a body is counted
    /// twice.
    #[test]
    fn a_build_reads_back_what_it_read() {
        let mut o = Overlay::default();
        o.names.insert(0x1000, "f".to_owned());
        let body: Arc<str> = Arc::from("f(1);");
        let ((), read) = recording(|| {
            o.names.get(&0x1000);
            o.names.contains_key(&u64::MAX);
            o.names.get(&0);
            o.comments.get(&0x1_4000_1000);
            assert!(o.types.is_empty());
            note_class("Player");
            note_body(&body);
            let here = Handle::here();
            std::thread::scope(|s| {
                s.spawn(|| here.enter(|| o.applied.get(&0x2000).is_none()));
            });
            unnoted(|| o.prototypes.get(&0x3000).is_none());
        });
        let keys: Vec<(Field, u64)> = read.keys().collect();
        assert_eq!(
            keys,
            vec![
                (Field::Names, 0),
                (Field::Names, 0x1000),
                (Field::Names, u64::MAX),
                (Field::Comments, 0x1_4000_1000),
                (Field::Applied, 0x2000),
                (Field::Class, "Player".fact()),
            ]
        );
        assert_eq!(read.len(), keys.len());
        assert!(read.whole(Field::Types) && !read.whole(Field::Names));
        let ((), outer) = recording(|| absorb(&read));
        assert_eq!(outer.keys().collect::<Vec<_>>(), keys);
        assert!(outer.whole(Field::Types));
        assert_eq!(
            read.bytes(),
            outer.bytes() + body.len(),
            "the body counts once"
        );
    }
}
