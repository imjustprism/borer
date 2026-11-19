//! A person's edit as the catalog call it is.
//!
//! A form the engine offers a referent ([`edit::offer`]) and the value
//! typed run through the `set_name`, `set_comment` or `set_type` row as a
//! dry run, so a person, an agent and the chat are held to one rule and see
//! one plan.

use std::cell::RefCell;
use std::sync::Arc;

use borer_engine::analysis::edit::{self, Edit, Force, Form, Plan, VarValue};
use borer_engine::analysis::fieldrefs::parse_unsigned;
use borer_engine::analysis::protos::Var;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::answer::Need;
use borer_engine::program::Program;
use borer_engine::script::Query;

use super::params::{SetCommentParams, SetNameParams, SetTypeParams, must_be_a_name};
use super::{Apply, Edited, Failure, Find, Held, Snapshot, View};

/// What an edit row asked of a [`Keeping`] face: the edits, whether a name
/// another address answers to is taken, whether the call asked to apply, and
/// the plan or the plan's refusal.
#[derive(Debug, Clone)]
pub struct Kept {
    /// The edits the row built.
    pub edits: Vec<Edit>,
    /// Whether a taken name is taken.
    pub force: Force,
    /// Whether the call asked to apply: a proposal, or a dry run.
    pub apply: Apply,
    /// The plan, or the plan's refusal.
    pub planned: Result<Plan, edit::Refused>,
}

/// A face over another that plans every edit a row asks for and keeps it
/// for a person to see, committing nothing: the person's inline editor and
/// the chat's proposal cards read their plans through it.
///
/// A name a person could not read whole on screen is refused before it is
/// planned ([`shows_whole`]).
pub struct Keeping<'h> {
    /// The face wrapped.
    held: &'h dyn Held,
    /// What the row's edit asked, once it asked.
    kept: RefCell<Option<Kept>>,
}

impl<'h> Keeping<'h> {
    /// Returns a face keeping the plans of edits asked over `held`.
    ///
    /// # Arguments
    ///
    /// * `held` - The face wrapped.
    #[must_use]
    pub const fn new(held: &'h dyn Held) -> Self {
        Self {
            held,
            kept: RefCell::new(None),
        }
    }

    /// Returns what the last edit asked of this face, `None` when none was.
    #[must_use]
    pub fn into_kept(self) -> Option<Kept> {
        self.kept.into_inner()
    }
}

impl std::fmt::Debug for Keeping<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Keeping")
            .field("kept", &self.kept)
            .finish_non_exhaustive()
    }
}

impl Held for Keeping<'_> {
    fn view(&self, need: Need) -> Option<Result<View, String>> {
        self.held.view(need)
    }

    fn user_overlay(&self) -> Arc<Overlay> {
        self.held.user_overlay()
    }

    fn recover(
        &self,
        program: &Arc<Program>,
        base: Arc<Analysis>,
        find: Find<'_>,
    ) -> Option<(Arc<Analysis>, u64)> {
        self.held.recover(program, base, find)
    }

    fn edit(
        &self,
        s: &Snapshot<'_>,
        edits: &[Edit],
        force: Force,
        apply: Apply,
    ) -> anyhow::Result<Edited> {
        for edit in edits {
            if let Edit::Name { name, .. } = edit {
                shows_whole(name).map_err(anyhow::Error::msg)?;
            }
        }
        let planned = edit::plan(s.program(), s.analysis(), s.overlay(), edits, force);
        let kept = match &planned {
            Ok(plan) => Some(Ok(plan.clone())),
            Err(e) => e.downcast_ref::<edit::Refused>().cloned().map(Err),
        };
        if let Some(planned) = kept {
            *self.kept.borrow_mut() = Some(Kept {
                edits: edits.to_vec(),
                force,
                apply,
                planned,
            });
        }
        Ok((planned?, apply.unwritten()))
    }

    fn querier(&self) -> Query {
        self.held.querier()
    }

    fn read(&self, uri: &str) -> Result<String, Failure> {
        self.held.read(uri)
    }
}

/// Refuses a name a person could not read whole: one holding a character
/// that hides itself or reorders the text around it
/// ([`borer_engine::text::visible`]).
///
/// # Arguments
///
/// * `name` - The name asked for.
///
/// # Errors
///
/// When the name holds one; the message shows the name with each written
/// out.
fn shows_whole(name: &str) -> Result<(), String> {
    match borer_engine::text::visible(name) {
        std::borrow::Cow::Borrowed(_) => Ok(()),
        std::borrow::Cow::Owned(shown) => Err(format!(
            "{} holds characters that do not show; a name a person accepts must show every one",
            borer_engine::text::one_line(&shown)
        )),
    }
}

/// Plans the edit `form` makes of `value` through the catalog row that
/// makes it, as a dry run: the plan any face would show, which the face
/// then commits its own way.
///
/// A name goes through `set_name`, a comment through `set_comment`, and a
/// variable, a prototype, a type applied at a global, a field, C
/// declarations, an enum and a typedef through `set_type`, each with the
/// arguments an agent would pass. Blanks around a name or a type are
/// dropped; a comment is kept as typed. A plan's refusal is its own words
/// ([`edit::Refused::why`]), without how an agent's call takes a name
/// anyway: a person's edit has no `force`.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `form` - The form the engine offered.
/// * `value` - What the person typed, in the form's words ([`Form`]).
///
/// # Errors
///
/// The row's refusal, in its words: the value does not read or is refused,
/// or the plan refuses the edit.
pub fn propose(h: &dyn Held, form: &Form, value: &str) -> Result<Plan, Failure> {
    let keeping = Keeping::new(h);
    let called = call(&keeping, form, value);
    match (keeping.into_kept().map(|k| k.planned), called) {
        (Some(Ok(plan)), Ok(_)) => Ok(plan),
        (Some(Err(refused)), _) => Err(Failure::asked(refused.why)),
        (_, Err(failure)) => Err(failure),
        (None, Ok(_)) => Err(Failure::asked("the edit planned nothing")),
    }
}

/// Runs the row `form` is a call of, with `value`, as a dry run.
///
/// # Arguments
///
/// * `h` - The face the row runs on.
/// * `form` - The form.
/// * `value` - What was typed.
///
/// # Errors
///
/// The row's refusal, or the value's when it does not read as the form
/// asks.
fn call(h: &dyn Held, form: &Form, value: &str) -> Result<String, Failure> {
    let typed = value.trim();
    let hex = |at: &u64| Some(format!("{at:#x}"));
    let ty = |t: &str| Some(t.to_owned());
    let set_type = |p: SetTypeParams| {
        super::set_type(
            h,
            &SetTypeParams {
                dry_run: Some(true),
                ..p
            },
        )
    };
    match form {
        Form::Name { at } => super::set_name(
            h,
            &SetNameParams {
                address: hex(at),
                name: ty(typed),
                names: None,
                force: None,
                dry_run: Some(true),
            },
        ),
        Form::Comment { at } => super::set_comment(
            h,
            &SetCommentParams {
                address: format!("{at:#x}"),
                comment: value.to_owned(),
                dry_run: Some(true),
            },
        ),
        Form::Var { entry, var, value } => set_type(var_params((*entry, var), value, typed)?),
        Form::Proto { entry: at } | Form::Apply { at } => set_type(SetTypeParams {
            address: hex(at),
            r#type: ty(typed),
            ..SetTypeParams::default()
        }),
        Form::Field {
            ty: of,
            offset,
            keep,
        } => set_type(SetTypeParams {
            name: Some(of.clone()),
            fields: Some(vec![field_statement(*offset, keep.as_deref(), typed)?]),
            ..SetTypeParams::default()
        }),
        Form::Declare => set_type(SetTypeParams {
            r#type: Some(value.to_owned()),
            ..SetTypeParams::default()
        }),
        Form::Enum => {
            let (name, values) = enum_values(typed)?;
            set_type(SetTypeParams {
                name: Some(name),
                values: Some(values),
                ..SetTypeParams::default()
            })
        }
        Form::Alias => {
            let (alias, target) = typed.split_once('=').ok_or_else(|| {
                Failure::asked("a typedef is its name, `=`, then its type: `Handle = u64`")
            })?;
            set_type(SetTypeParams {
                name: Some(alias.trim().to_owned()),
                r#type: Some(target.trim().to_owned()),
                ..SetTypeParams::default()
            })
        }
    }
}

/// Returns the `set_type` arguments that name and type a function's variable.
///
/// # Arguments
///
/// * `(entry, var)` - The function's entry and the variable as its text spells it.
/// * `value` - What `typed` is, and what it keeps.
/// * `typed` - What was typed, trimmed.
///
/// # Errors
///
/// When a declaration does not read ([`Var::parse`]).
fn var_params(
    (entry, var): (u64, &str),
    value: &VarValue,
    typed: &str,
) -> Result<SetTypeParams, Failure> {
    let (name, ty) = match value {
        VarValue::Type { kept_name } => (kept_name.clone(), Some(typed.to_owned())),
        VarValue::Declaration { kept_type } => {
            let declared = Var::parse(typed).map_err(|e| Failure::asked(e.to_string()))?;
            let stated = declared.ty.map(|t| t.spell()).or_else(|| kept_type.clone());
            (declared.name, stated)
        }
    };
    Ok(SetTypeParams {
        address: Some(format!("{entry:#x}")),
        var: Some(var.to_owned()),
        name: Some(name),
        r#type: ty,
        ..SetTypeParams::default()
    })
}

/// Returns the `fields` statement of `set_type` that names a field, or types it under the
/// name it keeps.
///
/// # Arguments
///
/// * `offset` - The field's byte offset.
/// * `keep` - The name kept while `typed` is the type; `None` when `typed` is the name.
/// * `typed` - What was typed, trimmed.
///
/// # Errors
///
/// When a new name is no name, or holds the `:` that would end it before a type.
fn field_statement(offset: u64, keep: Option<&str>, typed: &str) -> Result<String, Failure> {
    let Some(name) = keep else {
        must_be_a_name(typed)?;
        if typed.contains(':') {
            return Err(Failure::asked(
                "a field's name holds no `:`, which ends a field's name before its type",
            ));
        }
        return Ok(format!("{offset:#x}:{typed}"));
    };
    Ok(format!("{offset:#x}:{name}:{typed}"))
}

/// Reads an enum as [`Form::Enum`] spells it into its name and the values
/// `set_type` takes, each `name:value`, numbering a value with no number
/// one past the one before.
///
/// # Arguments
///
/// * `typed` - The enum, trimmed.
///
/// # Errors
///
/// When it has no name before a colon; a number that does not read is
/// passed on for `set_type` to refuse in its words.
fn enum_values(typed: &str) -> Result<(String, Vec<String>), Failure> {
    let (name, values) = typed.split_once(':').ok_or_else(|| {
        Failure::asked("an enum is its name, a colon, then its values: `State: Run = 1, Stop`")
    })?;
    let mut next = 0u64;
    let mut stated = Vec::new();
    for value in values.split(',').map(str::trim).filter(|v| !v.is_empty()) {
        let (named, number) = match value.split_once('=') {
            Some((named, number)) => (named.trim(), number.trim().to_owned()),
            None => (value, next.to_string()),
        };
        next = parse_unsigned(&number).map_or(next, |n| n.wrapping_add(1));
        stated.push(format!("{named}:{number}"));
    }
    Ok((name.trim().to_owned(), stated))
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use borer_engine::analysis::edit::{Form, VarValue};
    use borer_engine::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
    use borer_engine::analysis::{Analysis, Overlay};
    use borer_engine::program::{Arch, Program, Section};
    use serde_json::json;

    use super::propose;
    use crate::tools::{Loaded, tool};

    /// Where the caller enters; the callee is 0x10 past it.
    const TEXT: u64 = 0x1000;
    /// The global the caller reads.
    const DATA: u64 = 0x2000;

    /// Returns a face holding a caller that calls a callee and reads a
    /// global, beside a user struct `Player` with `hp` at offset 4.
    fn face() -> Loaded {
        let mut bytes = vec![0u8; 0x200];
        bytes[..12].copy_from_slice(&[
            0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
            0x8b, 0x05, 0xf5, 0x0f, 0x00, 0x00, // ASM: mov eax, [rip+0xff5]
            0xc3, // ASM: ret
        ]);
        bytes[0x10..0x14].copy_from_slice(&[0x8d, 0x41, 0x01, 0xc3]); // ASM: lea eax,[rcx+1]; ret
        let sections = vec![
            Section::mapped(".text", TEXT, 0, 0x100, false, true),
            Section::mapped(".data", DATA, 0x100, 0x100, true, false),
        ];
        let program = Program::raw(bytes, Arch::X86_64, 0, Some(TEXT), sections);
        let mut overlay = Overlay::default();
        let hp = UserField {
            name: "hp".to_owned(),
            ty: TypeExpr::U32,
        };
        let player = UserStruct {
            size: 8,
            fields: BTreeMap::from([(4, hp)]),
        };
        overlay
            .types
            .insert("Player".to_owned(), UserType::Struct(player));
        Loaded {
            analysis: Arc::new(Analysis::compute(&program)),
            program: Arc::new(program),
            overlay: Arc::new(overlay),
        }
    }

    /// Each form plans through the row an agent would call for it: the
    /// row's own dry run, given the same edit, says each line of the plan.
    #[test]
    fn each_form_plans_what_its_rows_dry_run_says() {
        let face = face();
        let callee = TEXT + 0x10;
        let field = |keep: Option<&str>| Form::Field {
            ty: "Player".to_owned(),
            offset: 4,
            keep: keep.map(str::to_owned),
        };
        let a1 = Form::Var {
            entry: callee,
            var: "a1".to_owned(),
            value: VarValue::Declaration { kept_type: None },
        };
        let calls = [
            (
                Form::Name { at: callee },
                " helper ",
                "set_name",
                json!({"address": "0x1010", "name": "helper"}),
            ),
            (
                Form::Comment { at: TEXT },
                "entry",
                "set_comment",
                json!({"address": "0x1000", "comment": "entry"}),
            ),
            (
                Form::Proto { entry: callee },
                "int helper(int a)",
                "set_type",
                json!({"address": "0x1010", "type": "int helper(int a)"}),
            ),
            (
                Form::Apply { at: DATA },
                "u32",
                "set_type",
                json!({"address": "0x2000", "type": "u32"}),
            ),
            (
                field(None),
                "health",
                "set_type",
                json!({"name": "Player", "fields": ["0x4:health"]}),
            ),
            (
                field(Some("hp")),
                "u16",
                "set_type",
                json!({"name": "Player", "fields": ["0x4:hp:u16"]}),
            ),
            (
                a1,
                "int count",
                "set_type",
                json!({"address": "0x1010", "var": "a1", "name": "count", "type": "int"}),
            ),
            (
                Form::Declare,
                "struct Pair { int a; int b; };",
                "set_type",
                json!({"type": "struct Pair { int a; int b; };"}),
            ),
            (
                Form::Enum,
                "State: Run = 1, Stop",
                "set_type",
                json!({"name": "State", "values": ["Run:1", "Stop:2"]}),
            ),
            (
                Form::Alias,
                "Handle = u64",
                "set_type",
                json!({"name": "Handle", "type": "u64"}),
            ),
        ];
        for (form, value, name, args) in calls {
            let plan = propose(&face, &form, value);
            let plan = plan.unwrap_or_else(|e| panic!("{form:?} {value}: {e}"));
            let args = args.as_object().cloned().unwrap_or_default();
            let row = tool(name).expect("a catalog row");
            let said = (row.run)(&face, args).expect("the row plans it");
            assert!(!plan.lines().is_empty(), "{form:?}");
            for line in plan.lines() {
                let (words, _) = line.said(true);
                assert!(
                    said.contains(words.trim()),
                    "{form:?}: {words} not in {said}"
                );
            }
        }
    }

    /// A refused value is the row's refusal, word for word.
    #[test]
    fn a_refusal_is_the_rows_own() {
        let face = face();
        let refused = propose(&face, &Form::Name { at: TEXT }, "1st").expect_err("a digit first");
        let args = json!({"address": "0x1000", "name": "1st"});
        let row = tool("set_name").expect("a catalog row");
        let said = (row.run)(&face, args.as_object().cloned().unwrap_or_default());
        assert_eq!(Err(refused), said);
    }

    /// A taken name is refused in the plan's words, less the agent's way
    /// to take it, which a person has no `force` for.
    #[test]
    fn a_taken_name_is_refused_without_the_agents_force() {
        let face = face();
        let args = json!({"address": "0x1010", "name": "sub_1000"});
        let row = tool("set_name").expect("a catalog row");
        let agent = (row.run)(&face, args.as_object().cloned().unwrap_or_default());
        let agent = agent.expect_err("taken").message;
        let person = propose(&face, &Form::Name { at: TEXT + 0x10 }, "sub_1000");
        let person = person.expect_err("taken").message;
        assert!(
            agent.ends_with(borer_engine::analysis::edit::TAKE_IT),
            "{agent}"
        );
        assert_eq!(
            format!("{person}{}", borer_engine::analysis::edit::TAKE_IT),
            agent
        );
    }

    /// An enum value's number is decimal or 0x-hex, as `set_type` reads
    /// one: a value named after another (`B = A`) is refused, not read as
    /// the number 0xA.
    #[test]
    fn an_enum_value_named_after_another_is_refused() {
        let face = face();
        assert!(propose(&face, &Form::Enum, "State: A = 5, B = A").is_err());
        assert!(propose(&face, &Form::Enum, "State: A = 5, B = 0xA, C = 12").is_ok());
        assert!(propose(&face, &Form::Enum, "Run = 1").is_err());
    }

    /// A field's new name with a `:` is refused before it could be read as
    /// a name and a type.
    #[test]
    fn a_field_name_with_a_colon_is_refused() {
        let face = face();
        let form = Form::Field {
            ty: "Player".to_owned(),
            offset: 4,
            keep: None,
        };
        let refused = propose(&face, &form, "a::b").expect_err("a colon");
        assert!(refused.message.contains("`:`"), "{refused}");
    }
}
