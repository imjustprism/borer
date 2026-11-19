//! The tools that edit the names in force: `class_layout` given `apply`.
//!
//! Each builds its edits and hands them to the face ([`super::Snapshot::edit`]).
//! A dry run, the default, plans them, and every face answers the same plan
//! text. Applied, what happens is the face's: the MCP server commits the
//! plan, and a face that holds proposals for a person keeps it instead
//! ([`Held::edit`]).

use borer_engine::analysis::edit::{Edit, Force, Laid, Plan};
use borer_engine::analysis::{apply, classes, name_of};
use borer_engine::answer::Need;
use borer_engine::program::Feature;

use super::params::ClassLayoutParams;
use super::{Apply, Failure, Held, run};

/// Returns whether a call is a dry run, and what the face is asked to do
/// with its plan.
///
/// # Arguments
///
/// * `dry_run` - The call's `dry_run`; absent is a dry run.
fn asked(dry_run: Option<bool>) -> (bool, Apply) {
    let dry = dry_run.unwrap_or(true);
    (dry, if dry { Apply::Preview } else { Apply::Commit })
}

/// Renders a class layout recovered from its methods' field accesses, or
/// with `apply` plans it as a user struct that types each method's object
/// ([`borer_engine::analysis::apply::from_class`]).
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded, the address is not a class method, nothing
/// belongs to the class, or the struct to apply is refused.
pub fn class_layout(h: &dyn Held, p: &ClassLayoutParams) -> Result<String, Failure> {
    run(h, Need::Code(Feature::Decompile), |s| {
        let (a, o) = (s.analysis(), s.overlay());
        let name = match s.entry(&p.class) {
            Ok(entry) => {
                let n = name_of(a, o, entry);
                classes::class_of(&n)
                    .ok_or_else(|| format!("{n} is not a class method"))?
                    .to_owned()
            }
            Err(_) => p.class.clone(),
        };
        let Some(struct_name) = &p.apply else {
            let layout = apply::class_named(s.program(), a, o, &name)?;
            return Ok(classes::render_layout(&layout, a, o));
        };
        let (dry, apply) = asked(p.dry_run);
        let edits = [Edit::Layout {
            from: Laid::Class(name),
            name: struct_name.clone(),
        }];
        s.edit(&edits, Force::Refuse, apply)
            .map(|plan| listed(&plan, dry))
            .map_err(|e| e.to_string())
    })
}

/// Answers a plan whose lines are blocks of their own (types from C, a
/// layout): the blocks, then, for a dry run, how to apply them.
///
/// # Arguments
///
/// * `plan` - The plan.
/// * `dry` - Whether the plan is a dry run's.
fn listed(plan: &Plan, dry: bool) -> String {
    let mut out: String = plan.lines().iter().map(|l| l.said(dry).0).collect();
    if dry {
        out.push_str("pass dry_run=false to apply.\n");
    }
    out
}
