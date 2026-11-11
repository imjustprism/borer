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
use super::utypes::{self, TypeExpr, UserStruct, UserType};
use super::{Analysis, Function, Overlay, bare_name, name_of};
use crate::program::Program;

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
/// together ([`coherent`]), under the caps a statement is held to. Fields
/// that overlap are refused only where they are stated, against the
/// loaded binary's pointer width, which a project file does not say.
///
/// # Arguments
///
/// * `overlay` - The overlay a project file rebuilt.
///
/// # Errors
///
/// When the overlay states fields of more than [`utypes::TYPES_MAX`]
/// classes, or a field or a class's fields are refused; the message names
/// the offender.
pub fn validate(overlay: &Overlay) -> Result<(), String> {
    /// The pointer width a project's types are sized by, as its user
    /// types are ([`utypes::validate`]).
    const WORD: u64 = 8;
    if overlay.fields.len() > utypes::TYPES_MAX {
        return Err(format!(
            "the project states fields of {} classes; {} are the most",
            overlay.fields.len(),
            utypes::TYPES_MAX
        ));
    }
    for (class, fields) in &overlay.fields {
        for (&off, field) in fields {
            sound(&overlay.types, off, field, WORD)?;
        }
        coherent(overlay, class, fields, &BTreeMap::new())?;
    }
    Ok(())
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
    /// # Arguments
    ///
    /// * `o` - The overlay.
    pub fn apply(self, o: &mut Overlay) {
        match self.edit {
            Edit::Struct(name, ty) => {
                o.types.insert(name, ty);
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
/// stated in, so an overlap is found between any two of them.
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
/// When an offset is stated twice, a field states no type and has none
/// to keep, or the struct does not build ([`utypes::laid_out`]).
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
    for (off, field) in by_offset(s.fields)? {
        let recovered = layout.fields.get(&off);
        check(p, a, o, s.name, (off, field), recovered, word)?;
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
    apart(&o.types, &fields, word)?;
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
/// as stating it by the class's name does.
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
/// When no function of a class starts at `entry`, the message saying how
/// to state the field by its class's name, or the field is refused
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
/// * `types` - The user types a field's type may name.
/// * `off` - The field's byte offset.
/// * `field` - The field.
/// * `word` - The image's pointer width in bytes (4 or 8).
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
fn sound(
    types: &BTreeMap<String, UserType>,
    off: u64,
    field: &Field,
    word: u64,
) -> Result<Option<u64>, String> {
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
    utypes::width_of(types, ty, word)
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
/// a struct is not held to the accesses ([`aggregate`]): it starts at the
/// offset, and the width its first element is read at says nothing of the
/// whole.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay.
/// * `class` - The class the field is stated of.
/// * `(off, field)` - The field and its byte offset.
/// * `recovered` - The field as the class's methods use it, if they do.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Errors
///
/// When the field is refused by itself, or its type's size is none the
/// code accesses the field at: that message names both widths, the
/// instructions, and the statement without a type that keeps the width.
fn check(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    class: &str,
    (off, field): (u64, &Field),
    recovered: Option<&FieldUse>,
    word: u64,
) -> Result<(), String> {
    let (Some(size), Some(ty)) = (sound(&o.types, off, field, word)?, &field.ty) else {
        return Ok(());
    };
    let Some(wide) = recovered
        .filter(|_| !aggregate(&o.types, ty))
        .filter(|used| {
            let bits = size.saturating_mul(8);
            !used.widths.iter().any(|w| u64::from(*w) == bits)
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
    let prior = o.fields.get(class);
    if fields.len() > utypes::FIELDS_MAX || (prior.is_none() && o.fields.len() >= utypes::TYPES_MAX)
    {
        return Err(format!(
            "class {class} would state {} fields, the overlay those of {} classes; {} fields of each of {} classes are the most",
            fields.len(),
            o.fields.len() + usize::from(prior.is_none()),
            utypes::FIELDS_MAX,
            utypes::TYPES_MAX
        ));
    }
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

/// Checks that no two typed fields a class would state share a byte.
///
/// A field stated without a type has no size of its own, so it is not
/// held against the others: the class's code may well read one word at
/// two widths.
///
/// # Arguments
///
/// * `types` - The user types a field's type may name.
/// * `fields` - Everything the class would state, by offset.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Errors
///
/// When a typed field starts before the typed field ahead of it ends.
fn apart(
    types: &BTreeMap<String, UserType>,
    fields: &BTreeMap<u64, Field>,
    word: u64,
) -> Result<(), String> {
    let mut end: Option<(u64, &str)> = None;
    for (&off, field) in fields {
        let Some(size) = field
            .ty
            .as_ref()
            .and_then(|ty| utypes::width_of(types, ty, word))
        else {
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
