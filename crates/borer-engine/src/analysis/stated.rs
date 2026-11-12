//! The fields an agent states of a class borer recovered or of a user
//! struct, merged by offset into what the name stated before.
//!
//! A class's stated fields are kept in [`Overlay::fields`] beside the
//! layout its methods show. A recovered layout is evidence, and an agent
//! often knows one thing more about one field: the member's name from an
//! assert string, or its type. Stating that must not cost the rest, so a
//! statement holds only the offsets it names and every other field stays
//! as recovered. A stated name is the first source of a class's field
//! labels ([`labels`], which [`super::classes::field_labels`] starts
//! from), so every decompile of the class's methods and every listing of
//! its fields prints it, and a layout marks the row it came from
//! ([`notes`]).
//!
//! A statement is planned before it is written ([`plan`]): the fields it
//! names take their offsets among those the name stated before, which all
//! stay unless the statement asks to replace them ([`Mode`]), and the plan
//! says how many fields it keeps, changes and adds. A type stated of a
//! class's field is held to the widths the class's code accesses the
//! field at ([`check`]). A field a method's text prints through `this` is
//! stated at the method too, of the class the method's object is of
//! ([`plan_at`]).

use std::collections::{BTreeMap, BTreeSet};

use super::classes::{self, FieldLabel, FieldUse};
use super::protos::VarKey;
use super::utypes::{self, TypeExpr, UserStruct, UserType};
use super::{Analysis, Function, Overlay, bare_name, name_of};
use crate::program::{Feature, Program};

/// One field an agent stated of a class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// The member's name, as the decompiler renders it (`this->name`).
    pub name: String,
    /// The type stated with the name; `None` leaves the field the width
    /// the class's code accesses it at.
    pub ty: Option<TypeExpr>,
}

impl Field {
    /// Spells the field as the listings write it after its offset.
    ///
    /// # Returns
    ///
    /// The name, then a space and the type when one was stated
    /// (`m_count u32`): a name holds no space, so the two read back apart.
    #[must_use]
    pub fn spell(&self) -> String {
        match &self.ty {
            Some(ty) => format!("{} {}", self.name, ty.spell()),
            None => self.name.clone(),
        }
    }

    /// Reads a field back from its spelling ([`Field::spell`]), as a
    /// project file holds it.
    ///
    /// # Arguments
    ///
    /// * `text` - The name, or the name, a space and the type.
    ///
    /// # Returns
    ///
    /// The field; its name is checked with the others its class states
    /// ([`validate`]).
    ///
    /// # Errors
    ///
    /// When the type after the name is not one the language spells.
    pub fn parse(text: &str) -> anyhow::Result<Field> {
        let (name, ty) = text
            .split_once(' ')
            .map_or((text, None), |(name, ty)| (name, Some(ty)));
        Ok(Field {
            name: name.to_owned(),
            ty: ty.map(utypes::parse_type).transpose()?,
        })
    }
}

/// Lists what an overlay states beyond its types and their applications,
/// as rows of the `types` listing ([`utypes::list_tsv`]).
///
/// A `class` row holds the class, `-` and the fields stated of it, each
/// `off name type` with the type left out where none was stated; then the
/// prototypes and the variables ([`super::protos::rows`]).
///
/// # Arguments
///
/// * `overlay` - The overlay.
///
/// # Returns
///
/// The rows: classes in name order, then functions in address order.
#[must_use]
pub fn rows(overlay: &Overlay) -> Vec<String> {
    let mut out: Vec<String> = overlay
        .fields
        .iter()
        .map(|(class, fields)| {
            let stated: Vec<String> = fields
                .iter()
                .map(|(off, field)| format!("{off:#x} {}", field.spell()))
                .collect();
            format!("class\t{class}\t-\t{}", stated.join(", "))
        })
        .collect();
    out.extend(super::protos::rows(&overlay.prototypes, &overlay.vars));
    out
}

/// Checks the fields an overlay states of classes, as a project file
/// hands them over.
///
/// Each field is checked by itself ([`sound`]) and each class's fields
/// together ([`coherent`], [`apart`]), under the caps a statement is held
/// to, each named type sized once ([`utypes::Widths`]) and the deadline in
/// force read once per class ([`crate::cancel::Cancel::whole`]); the
/// caller counts a project file's tables before it reads them. A project
/// file does not say its binary's pointer width, so typed fields are held
/// apart at the narrowest one: two that share a byte with 4-byte pointers
/// share it with any, and an overlap only wider pointers make is found
/// where the file meets its binary ([`settled`]), with what only the
/// binary's code can tell: the widths a field is accessed at and the names
/// the class's code gives its other fields.
///
/// # Arguments
///
/// * `overlay` - The overlay a project file rebuilt.
///
/// # Errors
///
/// When the overlay states fields of more than [`utypes::TYPES_MAX`]
/// classes, a field or a class's fields are refused, or the request's
/// deadline passed; the message names the offender.
pub fn validate(overlay: &Overlay) -> Result<(), String> {
    /// The pointer width a project's types are sized by, as its user
    /// types are ([`utypes::validate`]).
    const WORD: u64 = 8;
    /// The narrowest pointer an image has, in bytes.
    const NARROW: u64 = 4;
    if overlay.fields.len() > utypes::TYPES_MAX {
        return Err(format!(
            "the project states fields of {} classes; {} are the most",
            overlay.fields.len(),
            utypes::TYPES_MAX
        ));
    }
    let mut wide = utypes::Widths::new(&overlay.types, WORD);
    let mut narrow = utypes::Widths::new(&overlay.types, NARROW);
    for (class, fields) in &overlay.fields {
        crate::cancel::Cancel::whole(())?;
        for (&off, field) in fields {
            sound(&mut wide, off, field)?;
        }
        coherent(overlay, class, fields, &BTreeMap::new())?;
        apart(&mut narrow, fields).map_err(|why| format!("class {class}: {why}"))?;
    }
    Ok(())
}

/// The classes whose stated fields an overlay cannot keep over a binary
/// ([`settled`]), each list in name order.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Unsettled {
    /// The classes no function of the binary belongs to.
    pub absent: Vec<String>,
    /// The classes the binary's code contradicts a stated field of, each
    /// with the refusal a statement of that field would get.
    pub contradicted: Vec<(String, String)>,
    /// Why no class was held to anything, and every field stays as
    /// stated: the engine discovers no function of the binary
    /// ([`Program::refuses`]).
    pub unread: Option<String>,
}

impl Unsettled {
    /// Takes the fields stated of these classes out of an overlay.
    ///
    /// # Arguments
    ///
    /// * `o` - The overlay [`settled`] was asked of.
    ///
    /// # Returns
    ///
    /// How many fields went: those of the classes no function belongs to,
    /// then those of the classes the code contradicts.
    pub fn leave_out(&self, o: &mut Overlay) -> (usize, usize) {
        let mut gone = |class: &String| o.fields.remove(class).map_or(0, |fields| fields.len());
        let absent = self.absent.iter().map(&mut gone).sum();
        let contradicted = self.contradicted.iter().map(|(class, _)| gone(class)).sum();
        (absent, contradicted)
    }
}

/// Holds the fields an overlay states of classes to the binary's code.
///
/// It is the check a project file's fields get once its binary is at
/// hand, as a statement is held when it is made ([`plan_class`]): the
/// file is written by hand as well as by `save_project`, and
/// [`validate`] cannot see the code. Each class of the binary has its
/// stated fields held to the widths its code accesses them at and apart at
/// the binary's pointer width ([`fit`]), and to the names its code gives
/// its other fields ([`coherent`]). A class no function of the binary
/// belongs to has nothing to be held to, and a function named into it
/// later would take its fields unchecked.
///
/// Neither kind refuses the overlay. What a class's code is changes with
/// the names in force, so a project a session saved may state a field
/// that a function named into the class since reads at another width:
/// the classes are handed back for the caller to leave out and say why
/// ([`Unsettled::leave_out`]), as an annotation in no section is, and the
/// rest of the project loads. A check the caller's deadline cut short
/// held nothing, so it fails ([`crate::cancel::Cancel::whole`]).
///
/// A binary the engine discovers no function of has no class at all, by
/// what the engine reads and not by what the file holds: its analysis is
/// empty, and every class would come back as one of no function. There
/// the fields stay as stated and the reason is handed back
/// ([`Unsettled::unread`]); nothing reads them until the binary is loaded
/// so that its code is read, and the project loaded with it.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay a project file rebuilt.
///
/// # Returns
///
/// The classes whose stated fields cannot stay, or why none was held.
///
/// # Errors
///
/// When the request's deadline passed meanwhile.
pub fn settled(p: &Program, a: &Analysis, o: &Overlay) -> Result<Unsettled, String> {
    let mut out = Unsettled::default();
    if let Some(why) = p
        .refuses(Feature::Discover)
        .filter(|_| !o.fields.is_empty())
    {
        out.unread = Some(why);
        return Ok(out);
    }
    for (class, fields) in &o.fields {
        let layout = classes::class_layout(p, a, o, class).filter(|l| l.name == *class);
        let Some(layout) = layout else {
            out.absent.push(class.clone());
            continue;
        };
        let held = fit((p, a, o), &o.types, class, fields, Some(&layout))
            .and_then(|()| coherent(o, class, fields, &layout.labels));
        if let Err(why) = held {
            out.contradicted.push((class.clone(), why));
        }
    }
    crate::cancel::Cancel::whole(out)
}

/// Returns the names the overlay states of a class's fields, as the labels
/// they take ahead of every name the class's code gives.
///
/// # Arguments
///
/// * `overlay` - The overlay.
/// * `class` - The class, as the method index spells it.
///
/// # Returns
///
/// A member label per stated offset, none when nothing is stated of the
/// class.
pub(crate) fn labels(overlay: &Overlay, class: &str) -> BTreeMap<u64, FieldLabel> {
    overlay
        .fields
        .get(class)
        .into_iter()
        .flatten()
        .map(|(off, field)| (*off, FieldLabel::Member(field.name.clone())))
        .collect()
}

/// Returns the notes a class layout's row opens with: where the row's name
/// came from, when the overlay states it.
///
/// # Arguments
///
/// * `overlay` - The overlay.
/// * `class` - The class, as the method index spells it.
/// * `off` - The field's byte offset.
///
/// # Returns
///
/// `stated`, followed by the type when one was stated with the name, or
/// nothing for a field the overlay does not state.
pub(crate) fn notes(overlay: &Overlay, class: &str, off: u64) -> Vec<String> {
    overlay
        .fields
        .get(class)
        .and_then(|fields| fields.get(&off))
        .map(|field| match &field.ty {
            Some(ty) => format!("stated {}", ty.spell()),
            None => "stated".to_owned(),
        })
        .into_iter()
        .collect()
}

/// How a statement meets the fields its name states already.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// The stated fields take their offsets and every other field stays.
    Merge,
    /// The stated fields are all the name states afterwards.
    Replace,
}

impl Mode {
    /// Reads the mode from a statement's `replace` flag.
    ///
    /// # Arguments
    ///
    /// * `replace` - Whether the statement asks to replace.
    ///
    /// # Returns
    ///
    /// [`Mode::Replace`] when asked, else [`Mode::Merge`]: a statement that
    /// says nothing merges.
    #[must_use]
    pub fn asked(replace: bool) -> Self {
        if replace { Self::Replace } else { Self::Merge }
    }
}

/// The fields an agent states of one name.
#[derive(Debug, Clone, Copy)]
pub struct Statement<'a> {
    /// A user struct, a class borer recovered, or a struct to define.
    pub name: &'a str,
    /// The struct's size in bytes, when one is stated.
    pub size: Option<u64>,
    /// The fields by byte offset, in the order stated.
    pub fields: &'a [(u64, Field)],
    /// Whether the fields add to what the name states or take its place.
    pub mode: Mode,
}

/// What a [`Statement`] writes to an overlay.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Edit {
    /// The user struct of this name, as it will be.
    Struct(String, UserType),
    /// The fields stated of this class afterwards.
    Class(String, BTreeMap<u64, Field>),
}

/// A [`Statement`] checked and worked out, ready to be shown and applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    /// What it writes.
    edit: Edit,
    /// What it does, after the verb: the struct or the class, how many
    /// fields stay, change and are new, then each field it touches.
    what: String,
}

impl Plan {
    /// Returns the struct the plan defines, for a caller that sizes a type
    /// against it before the plan is applied.
    ///
    /// # Returns
    ///
    /// The struct's name and type, or `None` when the plan states fields
    /// of a class.
    #[must_use]
    pub fn defined(&self) -> Option<(&str, &UserType)> {
        match &self.edit {
            Edit::Struct(name, ty) => Some((name, ty)),
            Edit::Class(..) => None,
        }
    }

    /// Says what the plan would do, as a dry run words it.
    ///
    /// # Returns
    ///
    /// `define struct S: ...`, or `state 1 field(s) of class C: ...`.
    #[must_use]
    pub fn would(&self) -> String {
        match self.edit {
            Edit::Struct(..) => format!("define {}", self.what),
            Edit::Class(..) => format!("state {}", self.what),
        }
    }

    /// Says what the plan did, once applied.
    ///
    /// # Returns
    ///
    /// `defined struct S: ...`, or `stated 1 field(s) of class C: ...`.
    #[must_use]
    pub fn done(&self) -> String {
        match self.edit {
            Edit::Struct(..) => format!("defined {}", self.what),
            Edit::Class(..) => format!("stated {}", self.what),
        }
    }

    /// Writes the plan into an overlay.
    ///
    /// A class left stating no field leaves the overlay: an entry without
    /// fields would list a class nothing is stated of.
    ///
    /// # Arguments
    ///
    /// * `o` - The overlay.
    pub fn apply(self, o: &mut Overlay) {
        match self.edit {
            Edit::Struct(name, ty) => {
                o.types.insert(name, ty);
            }
            Edit::Class(class, fields) if fields.is_empty() => {
                o.fields.remove(&class);
            }
            Edit::Class(class, fields) => {
                o.fields.insert(class, fields);
            }
        }
    }
}

/// Reads a statement's fields by offset, refusing an offset stated twice.
///
/// # Arguments
///
/// * `fields` - The fields as stated.
///
/// # Errors
///
/// When two fields are stated at one offset; the message names both.
fn by_offset(fields: &[(u64, Field)]) -> Result<BTreeMap<u64, &Field>, String> {
    let mut stated: BTreeMap<u64, &Field> = BTreeMap::new();
    for (off, field) in fields {
        if let Some(first) = stated.insert(*off, field) {
            return Err(format!(
                "{off:#x} is stated twice, as {} and {}",
                crate::text::quoted(&first.name),
                crate::text::quoted(&field.name)
            ));
        }
    }
    Ok(stated)
}

/// Plans what a statement of fields does, checking all of it before
/// anything is written.
///
/// A name that is a user struct takes the fields into the struct; else a
/// name that is exactly a class with methods takes them as that class's
/// stated fields ([`plan_class`]); any other name defines a struct. Under
/// [`Mode::Merge`] a stated field takes its offset and every other field
/// stays; a struct's field stated without a type keeps the type it had,
/// and a class's keeps the width its code accesses it at.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the classes and what their methods access.
/// * `o` - The overlay the statement is made over.
/// * `s` - The statement.
///
/// # Returns
///
/// The plan.
///
/// # Errors
///
/// When an offset is stated twice, a field's name or type is refused, a
/// struct's field has no type to take, fields overlap, a name is already
/// another field's, or a stated type is of a size the class's code never
/// accesses the field at ([`check`]); each message names the offender.
pub fn plan(p: &Program, a: &Analysis, o: &Overlay, s: &Statement<'_>) -> Result<Plan, String> {
    let word: u64 = if p.is_64 { 8 } else { 4 };
    match o.types.get(s.name) {
        Some(UserType::Struct(old)) => structure(o, s, Some(old), word),
        None if !classes::methods_of(a, o, s.name).is_empty() => plan_class(p, a, o, s),
        Some(UserType::Enum(_) | UserType::Alias(_)) | None => structure(o, s, None, word),
    }
}

/// Most fields a plan words one by one before it counts the rest.
const SHOWN: usize = 8;

/// What a statement does to the fields its name had: the counts, and each
/// field it touches as the plan words it.
#[derive(Debug, Default)]
struct Tally {
    /// Fields renamed or retyped.
    changed: usize,
    /// Fields added.
    new: usize,
    /// Fields a replacing statement lets go of.
    dropped: usize,
    /// One wording per field touched, in the order met.
    lines: Vec<String>,
}

impl Tally {
    /// Words the tally after the fields left as they were.
    ///
    /// # Arguments
    ///
    /// * `kept` - Fields the statement leaves as they were.
    ///
    /// # Returns
    ///
    /// `5 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_count`, the
    /// dropped counted when there are any, the first [`SHOWN`] fields
    /// worded and the rest counted.
    fn says(&self, kept: usize) -> String {
        let mut out = format!("{kept} kept, {} changed, {} new", self.changed, self.new);
        if self.dropped > 0 {
            out.push_str(&format!(", {} dropped", self.dropped));
        }
        let mut shown: Vec<String> = self.lines.iter().take(SHOWN).cloned().collect();
        if self.lines.len() > SHOWN {
            shown.push(format!("+{} more", self.lines.len() - SHOWN));
        }
        if !shown.is_empty() {
            out.push_str(&format!(": {}", shown.join(", ")));
        }
        out
    }
}

/// Plans a statement of a user struct's fields: the struct defined afresh,
/// or the stated fields merged into the one there is.
///
/// The fields are laid out in offset order whatever order they were
/// stated in, so an overlap is found between any two of them. A
/// statement that would leave the struct no field is refused: stating
/// none drops what a class states ([`plan_class`]), and a struct of no
/// field is no type to apply.
///
/// # Arguments
///
/// * `o` - The overlay, for the types a field may name.
/// * `s` - The statement.
/// * `old` - The struct the name states already, if any.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Errors
///
/// When the struct would hold no field, an offset is stated twice, a
/// field states no type and has none to keep, or the struct does not
/// build ([`utypes::laid_out`]).
fn structure(
    o: &Overlay,
    s: &Statement<'_>,
    old: Option<&UserStruct>,
    word: u64,
) -> Result<Plan, String> {
    let kept = old.filter(|_| s.mode == Mode::Merge);
    let mut fields: BTreeMap<u64, (String, TypeExpr)> = kept
        .into_iter()
        .flat_map(|k| &k.fields)
        .map(|(off, f)| (*off, (f.name.clone(), f.ty.clone())))
        .collect();
    let mut tally = Tally::default();
    for (off, field) in by_offset(s.fields)? {
        let was = fields.get(&off);
        let Some(ty) = field.ty.clone().or_else(|| was.map(|(_, ty)| ty.clone())) else {
            return Err(format!(
                "field {} at {off:#x} states no type, and {} has no field there whose type it could keep",
                crate::text::quoted(&field.name),
                crate::text::quoted(s.name)
            ));
        };
        let now = format!("{} {}", field.name, ty.spell());
        match was {
            Some((name, old_ty)) if *name == field.name && *old_ty == ty => {}
            Some((name, old_ty)) => {
                tally.changed += 1;
                tally
                    .lines
                    .push(format!("+{off:#x} {name} {} -> {now}", old_ty.spell()));
            }
            None => {
                tally.new += 1;
                tally.lines.push(format!("+{off:#x} {now} (new)"));
            }
        }
        fields.insert(off, (field.name.clone(), ty));
    }
    let list: Vec<(u64, String, TypeExpr)> = fields
        .into_iter()
        .map(|(off, (name, ty))| (off, name, ty))
        .collect();
    if list.is_empty() {
        return Err(format!(
            "{} is no class borer recovered, so it states no fields to drop; a struct keeps at least one field",
            crate::text::quoted(s.name)
        ));
    }
    let mut built =
        utypes::laid_out(s.name, s.size, &list, &o.types, word).map_err(|e| e.to_string())?;
    if let (Some(k), None) = (kept, s.size) {
        built.size = built.size.max(k.size);
    }
    let built = UserType::Struct(built);
    let mut what = built.describe(s.name);
    match (kept, old) {
        (Some(k), _) => {
            what.push_str(&format!("; {}", tally.says(k.fields.len() - tally.changed)));
        }
        (None, Some(k)) => {
            what.push_str(&format!(", in place of the {} it stated", k.fields.len()));
        }
        (None, None) => {}
    }
    Ok(Plan {
        edit: Edit::Struct(s.name.to_owned(), built),
        what,
    })
}

/// Plans a statement of fields of a class borer recovered, whatever else
/// goes by the class's name.
///
/// Each stated field takes its offset among the fields stated of the
/// class before, all of which stay under [`Mode::Merge`]; the layout the
/// class's methods show is not touched, so a field no statement names
/// stays as recovered. A field whose statement a replacing one drops goes
/// by the name the class's code gives it again, so the names are checked
/// against the class's labels with its statements taken away.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
/// * `s` - The statement, its name a class as the method index spells it.
///
/// # Returns
///
/// The plan.
///
/// # Errors
///
/// When no function belongs to the class, an offset is stated twice, a
/// field is refused by itself ([`check`]) or the fields the class would
/// state do not go together ([`coherent`], [`apart`]).
pub fn plan_class(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    s: &Statement<'_>,
) -> Result<Plan, String> {
    let word: u64 = if p.is_64 { 8 } else { 4 };
    let layout = classes::class_layout(p, a, o, s.name)
        .filter(|layout| layout.name == s.name)
        .ok_or_else(|| {
            format!(
                "no function belongs to a class named exactly {}",
                crate::text::quoted(s.name)
            )
        })?;
    let labels = classes::field_labels(p, a, o, s.name);
    let prior = o.fields.get(s.name);
    let before = |off: u64| prior.and_then(|fields| fields.get(&off));
    let mut fields: BTreeMap<u64, Field> = match s.mode {
        Mode::Merge => prior.cloned().unwrap_or_default(),
        Mode::Replace => BTreeMap::new(),
    };
    let mut tally = Tally::default();
    let mut widths = utypes::Widths::new(&o.types, word);
    for (off, field) in by_offset(s.fields)? {
        let recovered = layout.fields.get(&off);
        check((p, a, o), &mut widths, s.name, (off, field), recovered)?;
        fields.insert(off, field.clone());
        if before(off) == Some(field) {
            continue;
        }
        if recovered.is_none() && before(off).is_none() {
            tally.new += 1;
            tally
                .lines
                .push(format!("+{off:#x} {} (new)", field.spell()));
            continue;
        }
        let was = match (before(off), labels.get(&off)) {
            (Some(f), _) => f.spell(),
            (None, Some(FieldLabel::Member(name))) => name.clone(),
            (None, Some(FieldLabel::ReadBy(_)) | None) => format!("field_{off:#x}"),
        };
        let width = recovered
            .filter(|_| field.ty.is_none())
            .and_then(accessed)
            .map(|wide| format!(" (accessed {wide})"))
            .unwrap_or_default();
        tally.changed += 1;
        tally
            .lines
            .push(format!("+{off:#x} {was} -> {}{width}", field.spell()));
    }
    for (off, f) in prior.into_iter().flatten() {
        if !fields.contains_key(off) {
            tally.dropped += 1;
            tally
                .lines
                .push(format!("+{off:#x} {} (dropped)", f.spell()));
        }
    }
    let bare;
    let others = if tally.dropped > 0 {
        let mut unstated = o.clone();
        unstated.fields.remove(s.name);
        bare = classes::field_labels(p, a, &unstated, s.name);
        &bare
    } else {
        &labels
    };
    coherent(o, s.name, &fields, others)?;
    apart(&mut widths, &fields)?;
    let known: BTreeSet<&u64> = layout
        .fields
        .keys()
        .chain(prior.into_iter().flatten().map(|(off, _)| off))
        .collect();
    let mut what = format!(
        "{} field(s) of class {}: {}",
        s.fields.len(),
        s.name,
        tally.says(known.len() - tally.changed - tally.dropped)
    );
    if s.size.is_some() {
        what.push_str("; a class keeps no stated size");
    }
    Ok(Plan {
        edit: Edit::Class(s.name.to_owned(), fields),
        what,
    })
}

/// Holds the fields stated of one class to its code and to each other,
/// under a set of types: each to the widths the class's code accesses it at
/// ([`check`]), and the typed ones apart ([`apart`]).
///
/// # Arguments
///
/// * `(p, a, o)` - The loaded image, its analysis and the overlay.
/// * `types` - The user types the fields' types are read by.
/// * `class` - The class.
/// * `fields` - Everything the class states, by offset.
/// * `layout` - The class's recovered layout, when it has methods here.
///
/// # Errors
///
/// When a field is refused or two typed fields share a byte; the message
/// names the class and the field.
fn fit(
    (p, a, o): (&Program, &Analysis, &Overlay),
    types: &BTreeMap<String, UserType>,
    class: &str,
    fields: &BTreeMap<u64, Field>,
    layout: Option<&classes::ClassLayout>,
) -> Result<(), String> {
    let mut widths = utypes::Widths::new(types, if p.is_64 { 8 } else { 4 });
    for (&off, field) in fields {
        let recovered = layout.and_then(|layout| layout.fields.get(&off));
        check((p, a, o), &mut widths, class, (off, field), recovered)?;
    }
    apart(&mut widths, fields).map_err(|why| format!("class {class}: {why}"))
}

/// Checks that the fields stated with a type still stand once the
/// overlay's types become `types`.
///
/// A type that changes takes the fields stated with it along: a class's
/// field of that type, and a struct's that holds it by value, change size
/// with it. Every such field whose size or kind (an array or a struct, or
/// not: [`aggregate`]) the change moves is held again to what it was
/// checked against when it was stated: a struct must still lay out
/// ([`utypes::laid_out`]), and a class's fields must still fit its code
/// and each other ([`fit`]). A name the overlay did not define changes
/// nothing: no field was stated with it.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay, with its types as they are.
/// * `types` - The types as the change would leave them.
///
/// # Errors
///
/// When a struct or a class's field would no longer stand; the message
/// names it and how to restate it first.
pub fn standing(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    types: &BTreeMap<String, UserType>,
) -> Result<(), String> {
    if o.types
        .iter()
        .all(|(name, was)| types.get(name) == Some(was))
    {
        return Ok(());
    }
    let word: u64 = if p.is_64 { 8 } else { 4 };
    let moved = |ty: &TypeExpr| {
        utypes::width_of(&o.types, ty, word) != utypes::width_of(types, ty, word)
            || aggregate(&o.types, ty) != aggregate(types, ty)
    };
    for (name, ty) in types {
        let UserType::Struct(held) = ty else {
            continue;
        };
        if o.types.get(name) != Some(ty) || !held.fields.values().any(|f| moved(&f.ty)) {
            continue;
        }
        let fields: Vec<(u64, String, TypeExpr)> = held
            .fields
            .iter()
            .map(|(off, f)| (*off, f.name.clone(), f.ty.clone()))
            .collect();
        utypes::laid_out(name, Some(held.size), &fields, types, word).map_err(|why| {
            format!(
                "the type cannot change so: struct {name} holds it by value and would no longer lay out ({why}); restate struct {name} first"
            )
        })?;
    }
    for (class, fields) in &o.fields {
        if fields.values().any(|f| f.ty.as_ref().is_some_and(&moved)) {
            let layout = classes::class_layout(p, a, o, class).filter(|l| l.name == *class);
            fit((p, a, o), types, class, fields, layout.as_ref()).map_err(|why| {
                format!(
                    "the type cannot change so: a field stated with it would no longer stand ({why}); restate that field first"
                )
            })?;
        }
    }
    Ok(())
}

/// Returns the overlay's types with one more defined, as a definition is
/// checked before it is written.
///
/// The types it leaves are held to what a project's are on load
/// ([`utypes::validate`]), so a session never holds a type it could not
/// load again: one holding itself by value, or a chain of typedefs past
/// the cap.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
/// * `fresh` - The type a call defines and its name, if it defines one.
///
/// # Returns
///
/// The types the call would leave.
///
/// # Errors
///
/// When the types it leaves do not validate, or the definition changes a
/// type and a field stated with it would no longer stand ([`standing`]).
pub fn retyped(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    fresh: Option<(&str, &UserType)>,
) -> Result<BTreeMap<String, UserType>, String> {
    let mut types = BTreeMap::clone(&o.types);
    if let Some((name, ty)) = fresh {
        types.insert(name.to_owned(), ty.clone());
        utypes::validate(&types, &o.applied).map_err(|e| e.to_string())?;
        standing(p, a, o, &types)?;
    }
    Ok(types)
}

/// Says why a type that sizes to nothing cannot be applied or read, and
/// what to do first.
///
/// Stating fields under the name of a class borer recovered states that
/// class's fields ([`plan`]) and defines no struct, so the advice that
/// fits any other name would send an agent in a circle there: the message
/// for such a name says to define the struct under another one.
///
/// # Arguments
///
/// * `a` - The analysis, when there is one, for the classes.
/// * `o` - The overlay.
/// * `ty` - The type.
/// * `first` - What defines a type, as the caller's front end spells it.
///
/// # Returns
///
/// That the type names nothing defined, then `first`, or for a class's
/// name why stating its fields defines no struct.
#[must_use]
pub fn undefined(a: Option<&Analysis>, o: &Overlay, ty: &TypeExpr, first: &str) -> String {
    let mut base = ty;
    while let TypeExpr::Ptr(inner) | TypeExpr::Array(inner, _) = base {
        base = inner.as_ref();
    }
    if let (Some(a), TypeExpr::Named(name)) = (a, base)
        && !classes::methods_of(a, o, name).is_empty()
    {
        return format!(
            "the type {} names nothing defined: {name} is a class borer recovered, and fields stated under that name are the class's, not a struct's; define the struct under another name and apply that",
            ty.spell()
        );
    }
    format!("the type {} names nothing defined; {first}", ty.spell())
}

/// Returns the class a function's object is of: the class its name is
/// qualified by, else the class its first parameter is hinted as.
///
/// This is the class a decompile names the function's `this` by, so a
/// field its text prints through `this` is a field of that class.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - The overlay, whose name for the function comes first.
/// * `f` - The function.
///
/// # Returns
///
/// The class, or `None` for a function of no class.
#[must_use]
pub fn object_class(a: &Analysis, o: &Overlay, f: &Function) -> Option<String> {
    classes::class_of(bare_name(&name_of(a, o, f.entry)))
        .map(str::to_owned)
        .or_else(|| f.param_hints.get(&0).cloned())
}

/// Plans a statement of one field of the class a function takes its object
/// as: the field a method's text prints through its object, stated at the
/// method.
///
/// The class is the one the function's text names its object's fields by:
/// the class of its `this` ([`object_class`]) when its signature takes one,
/// else the class its first parameter is hinted as (a method renamed out
/// of its class still takes `Cls *a1`). A function that takes its object
/// untyped (a constructor's `void *a1`) states the field of the class its
/// name is qualified by, and the plan says its own text will not print the
/// name. The field is merged into what the class states ([`plan_class`]),
/// as stating it by the class's name does. The function must access the
/// offset through its own object ([`through`]): an offset it reads through
/// another pointer is a field of what that points at, and one it does not
/// touch is a slip of the hand there; both are refused.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
/// * `entry` - The function's entry address.
/// * `off` - The field's byte offset.
/// * `field` - The field.
///
/// # Returns
///
/// The plan, which ends by naming the function and the class it takes its
/// object as.
///
/// # Errors
///
/// When no function of a class starts at `entry`, or it accesses the
/// offset through another object or not at all, each message saying how to
/// state the field by a class's name, or the field is refused
/// ([`plan_class`]).
pub fn plan_at(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    off: u64,
    field: Field,
) -> Result<Plan, String> {
    let fname = name_of(a, o, entry);
    let f = a.function(entry);
    let own = f.and_then(|f| object_class(a, o, f));
    let this = own.as_ref().filter(|class| {
        super::decompile::decompile_named(p, a, o, entry)
            .is_some_and(|text| text.contains(&format!("{class} *this")))
    });
    let hinted = f.and_then(|f| f.param_hints.get(&0));
    let (class, typed) = match (this.or(hinted), &own) {
        (Some(class), _) => (class, true),
        (None, Some(class)) => (class, false),
        (None, None) => {
            return Err(format!(
                "{fname} belongs to no class borer knows, so a field at {off:#x} has no class to be stated of; state it by its class, set_type(name=<class>, fields=[\"{off:#x}:{}\"]), or type the pointer it is read through (borer://layout/{entry:#x},apply=<Name> plans that)",
                field.name
            ));
        }
    };
    let (bases, on_object) = through(p, a, o, entry, off);
    if !on_object {
        return Err(match bases.as_slice() {
            [] => format!(
                "{fname} ({entry:#x}) accesses nothing at +{off:#x}, so there is no such field to state there; a field the function does not touch is stated by its class, set_type(name={class}, fields=[\"{off:#x}:{}\"])",
                field.name
            ),
            others => format!(
                "{fname} ({entry:#x}) accesses +{off:#x} through {}, not through its own object, so it is a field of what that points at and not one to state of {class} there; state it by that object's class or struct, set_type(name=<its class or struct>, fields=[\"{off:#x}:{}\"])",
                others.join(" and "),
                field.name
            ),
        });
    }
    let fields = [(off, field)];
    let statement = Statement {
        name: class,
        size: None,
        fields: &fields,
        mode: Mode::Merge,
    };
    let mut plan = plan_class(p, a, o, &statement)?;
    plan.what.push_str(&if typed {
        format!("; {fname} ({entry:#x}) takes its object as {class}")
    } else {
        format!(
            "; {fname} ({entry:#x}) is named after {class} and takes its object untyped, so its own text will not print the name: the class's other methods do"
        )
    });
    Ok(plan)
}

/// Lists the pointers a function accesses one offset through
/// ([`classes::field_accesses`]), and tells whether its own object is one.
///
/// The object is `this`, else the first parameter, by the name the text
/// gives it: `a1`, or the name a variable statement or a prototype stated.
/// A class's layout reads a method's accesses off the same object.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
/// * `entry` - The function's entry address.
/// * `off` - The byte offset.
///
/// # Returns
///
/// Each variable the function dereferences at the offset, as its text
/// spells it, and whether the function's object is among them.
fn through(p: &Program, a: &Analysis, o: &Overlay, entry: u64, off: u64) -> (Vec<String>, bool) {
    let accesses = classes::field_accesses(p, a, o, entry).unwrap_or_default();
    let vars = o.vars.get(&entry);
    let named = vars.and_then(|vars| vars.get(&VarKey::Param(0)));
    let declared = o.prototypes.get(&entry).and_then(|d| d.params.first());
    let object = |base: &str| {
        matches!(base, "this" | "a1")
            || named.is_some_and(|var| var.name == base)
            || declared.is_some_and(|param| param.name == base)
    };
    let bases: Vec<String> = accesses
        .into_keys()
        .filter(|(_, at)| *at == off)
        .map(|(base, _)| base)
        .collect();
    let on_object = bases.iter().any(|base| object(base));
    (bases, on_object)
}

/// Returns the widths a class's code accesses a field at, as a plan says
/// them: `4 byte(s) wide`, or `8/16 byte(s) wide` for a field accessed
/// both ways.
///
/// # Arguments
///
/// * `field` - The field as the class's methods use it.
///
/// # Returns
///
/// The widths, or `None` when no access states one (a field only
/// addressed).
fn accessed(field: &FieldUse) -> Option<String> {
    let wide: Vec<String> = field
        .widths
        .iter()
        .map(|bits| (bits / 8).to_string())
        .collect();
    (!wide.is_empty()).then(|| format!("{} byte(s) wide", wide.join("/")))
}

/// Checks one stated field by what it says alone: a name a decompile can
/// print as a member, and a type of a size that fits at the offset.
///
/// # Arguments
///
/// * `widths` - The user types a field's type may name, sized at the
///   image's pointer width.
/// * `off` - The field's byte offset.
/// * `field` - The field.
///
/// # Returns
///
/// The size of the field's type in bytes, `None` for a field stated
/// without one.
///
/// # Errors
///
/// When the name is not an identifier or reads as an unnamed field, or
/// the type resolves to no size or ends past every address.
fn sound(widths: &mut utypes::Widths<'_>, off: u64, field: &Field) -> Result<Option<u64>, String> {
    if !utypes::is_ident(&field.name) {
        return Err(format!(
            "field name {} is not an identifier",
            crate::text::quoted(&field.name)
        ));
    }
    if field.name.starts_with("field_0x") || field.name.starts_with("field_neg0x") {
        return Err(format!(
            "{} is how an unnamed field prints; give the member's own name",
            field.name
        ));
    }
    let Some(ty) = &field.ty else {
        return Ok(None);
    };
    widths
        .of(ty)
        .filter(|size| off.checked_add(*size).is_some())
        .map(Some)
        .ok_or_else(|| {
            format!(
                "field {}'s type {} resolves to no size at {off:#x}",
                field.name,
                ty.spell()
            )
        })
}

/// Checks one stated field of a class by itself ([`sound`]), and the size
/// of its type against the widths the class's code accesses the offset
/// at.
///
/// A type conflicts only by its size: a scalar, a pointer or an enum as
/// wide as no access the class's code makes at the offset states a width
/// the code disproves, and is refused, under a typedef's name as under its
/// own. A type as wide as an access is accepted whatever else it says (a
/// pointer for a 64-bit word, a signed for an unsigned, a float for an
/// integer), and a field accessed at two widths takes either. An array or
/// a struct ([`aggregate`]) starts at the offset and is read an element at
/// a time, so the width of an access says nothing of the whole: it is
/// refused only when every access is wider than all of it, which no
/// element of it can be.
///
/// # Arguments
///
/// * `(p, a, o)` - The loaded image, its analysis and the overlay.
/// * `widths` - The user types the field's type is read by, the
///   overlay's or those a type change would leave, sized at the image's
///   pointer width.
/// * `class` - The class the field is stated of.
/// * `(off, field)` - The field and its byte offset.
/// * `recovered` - The field as the class's methods use it, if they do.
///
/// # Errors
///
/// When the field is refused by itself, or its type's size is none the
/// code accesses the field at: that message names both widths, the
/// instructions, and the statement without a type that keeps the width.
fn check(
    (p, a, o): (&Program, &Analysis, &Overlay),
    widths: &mut utypes::Widths<'_>,
    class: &str,
    (off, field): (u64, &Field),
    recovered: Option<&FieldUse>,
) -> Result<(), String> {
    let (Some(size), Some(ty)) = (sound(widths, off, field)?, &field.ty) else {
        return Ok(());
    };
    let whole = aggregate(widths.known, ty);
    let Some(wide) = recovered
        .filter(|used| {
            let bits = size.saturating_mul(8);
            let fits = |wide: u64| if whole { wide <= bits } else { wide == bits };
            !used.widths.iter().any(|w| fits(u64::from(*w)))
        })
        .and_then(accessed)
    else {
        return Ok(());
    };
    Err(format!(
        "field {} at +{off:#x} of class {class} is stated {}, {size} byte(s) wide, but the class's code accesses it {wide}{}; state a type of that width, or leave the type out ({off:#x}:{}) to keep the width the code uses",
        field.name,
        ty.spell(),
        sites(p, a, o, class, off),
        field.name
    ))
}

/// Tells whether a type is an array or a struct, by its own spelling or
/// through the typedefs that name it: a type no single access reads whole.
///
/// # Arguments
///
/// * `types` - The user types a name may stand for.
/// * `ty` - The type.
///
/// # Returns
///
/// `false` for a scalar, a pointer and an enum, and for a name nothing
/// defines or a chain of typedefs that loops.
fn aggregate(types: &BTreeMap<String, UserType>, ty: &TypeExpr) -> bool {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut current = ty;
    while let TypeExpr::Named(name) = current {
        match types.get(name).filter(|_| seen.insert(name.as_str())) {
            Some(UserType::Alias(inner)) => current = inner,
            Some(UserType::Struct(_)) => return true,
            Some(UserType::Enum(_)) | None => return false,
        }
    }
    matches!(current, TypeExpr::Array(..))
}

/// Most instructions a refused type lists before it counts the rest.
const SITES_SHOWN: usize = 6;

/// Lists the instructions accessing one field of a class through a pointer
/// typed as the class, each with its function
/// ([`classes::typed_field_uses`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
/// * `class` - The class.
/// * `off` - The field's byte offset.
///
/// # Returns
///
/// ` at 0x1040 (C::get), 0x1080 (C::set)`, at most [`SITES_SHOWN`] and a
/// count of the rest; empty when no instruction was found.
fn sites(p: &Program, a: &Analysis, o: &Overlay, class: &str, off: u64) -> String {
    let uses = classes::typed_field_uses(p, a, o, class, off);
    let all: Vec<String> = uses
        .iter()
        .flat_map(|found| &found.uses)
        .flat_map(|u| {
            let name = name_of(a, o, u.entry);
            u.sites.iter().map(move |va| format!("{va:#x} ({name})"))
        })
        .collect();
    if all.is_empty() {
        return String::new();
    }
    let more = match all.len().saturating_sub(SITES_SHOWN) {
        0 => String::new(),
        more => format!(" and {more} more"),
    };
    let shown: Vec<&str> = all.iter().take(SITES_SHOWN).map(String::as_str).collect();
    format!(" at {}{more}", shown.join(", "))
}

/// Checks the fields a class would state together: their count, that no
/// two share a name, and that none takes the name the class's code gives
/// another field.
///
/// # Arguments
///
/// * `o` - The overlay, for the classes stated so far.
/// * `class` - The class.
/// * `fields` - Everything the class would state, by offset.
/// * `labels` - What the class's fields are called where the statement
///   does not name them: by the class's code alone at an offset whose
///   earlier statement it drops, since that name comes back.
///
/// # Errors
///
/// When the class would state more than [`utypes::FIELDS_MAX`] fields or
/// the overlay fields of more than [`utypes::TYPES_MAX`] classes, or a
/// name is taken twice.
fn coherent(
    o: &Overlay,
    class: &str,
    fields: &BTreeMap<u64, Field>,
    labels: &BTreeMap<u64, FieldLabel>,
) -> Result<(), String> {
    let classes = o.fields.len() + usize::from(!o.fields.contains_key(class));
    crowded(class, fields.len(), classes)?;
    let mut names: BTreeMap<&str, u64> = labels
        .iter()
        .filter(|(off, _)| !fields.contains_key(off))
        .filter_map(|(off, label)| match label {
            FieldLabel::Member(name) => Some((name.as_str(), *off)),
            FieldLabel::ReadBy(_) => None,
        })
        .collect();
    for (&off, field) in fields {
        if let Some(other) = names.insert(&field.name, off) {
            return Err(format!(
                "{} already names +{other:#x} of class {class}; pick another name for +{off:#x}",
                field.name
            ));
        }
    }
    Ok(())
}

/// Refuses a class stating more fields than a struct holds, or an overlay
/// stating those of more classes than it holds types.
///
/// # Arguments
///
/// * `class` - The class, escaped to a line.
/// * `fields` - How many fields the class would state.
/// * `classes` - How many classes the overlay would state fields of.
///
/// # Errors
///
/// When the class would state more than [`utypes::FIELDS_MAX`] fields or
/// the overlay those of more than [`utypes::TYPES_MAX`] classes.
pub(crate) fn crowded(class: &str, fields: usize, classes: usize) -> Result<(), String> {
    if fields <= utypes::FIELDS_MAX && classes <= utypes::TYPES_MAX {
        return Ok(());
    }
    Err(format!(
        "class {class} would state {fields} fields, the overlay those of {classes} classes; {} fields of each of {} classes are the most",
        utypes::FIELDS_MAX,
        utypes::TYPES_MAX
    ))
}

/// Checks that no two typed fields a class would state share a byte.
///
/// A field stated without a type has no size of its own, so it is not
/// held against the others: the class's code may well read one word at
/// two widths.
///
/// # Arguments
///
/// * `widths` - The user types a field's type may name, sized at the
///   image's pointer width.
/// * `fields` - Everything the class would state, by offset.
///
/// # Errors
///
/// When a typed field starts before the typed field ahead of it ends.
fn apart(widths: &mut utypes::Widths<'_>, fields: &BTreeMap<u64, Field>) -> Result<(), String> {
    let mut end: Option<(u64, &str)> = None;
    for (&off, field) in fields {
        let Some(size) = field.ty.as_ref().and_then(|ty| widths.of(ty)) else {
            continue;
        };
        if let Some((until, earlier)) = end.filter(|(until, _)| *until > off) {
            return Err(format!(
                "field {} at {off:#x} overlaps {earlier}, which ends at {until:#x}",
                field.name
            ));
        }
        end = Some((off.saturating_add(size), &field.name));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::Field;
    use crate::analysis::Overlay;

    /// The overlay the binary's own name tables are read under keeps the
    /// stated fields, so what is read under it is keyed by them too.
    ///
    /// # Panics
    ///
    /// When the fields are left behind.
    #[test]
    fn the_overlay_without_tables_keeps_the_stated_fields() {
        let mut o = Overlay::default();
        let field = Field {
            name: "m_count".to_owned(),
            ty: None,
        };
        o.fields
            .entry("Cls".to_owned())
            .or_default()
            .insert(8, field);
        assert_eq!(o.without_tables().fields, o.fields);
        assert_ne!(
            o.without_tables().fingerprint(),
            Overlay::default().fingerprint()
        );
    }
}
