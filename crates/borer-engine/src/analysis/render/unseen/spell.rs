//! The census as agents read it (`borer://indirect`) and as a person
//! reads it: one spelling of each form, reason and rule for each.

use super::*;
use crate::table::Window;

/// What a `form=` filter names: a [`Form`] without its operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// [`Form::Register`].
    Register,
    /// [`Form::VtableSlot`].
    Vtable,
    /// [`Form::Field`].
    Field,
    /// [`Form::Global`].
    Global,
    /// [`Form::Memory`].
    Memory,
    /// [`Form::IntoTrampoline`].
    Trampoline,
    /// [`Form::Jump`].
    Jump,
}

impl Kind {
    /// Every kind, in the order a refusal lists them.
    const ALL: [Kind; 7] = [
        Kind::Register,
        Kind::Vtable,
        Kind::Field,
        Kind::Global,
        Kind::Trampoline,
        Kind::Jump,
        Kind::Memory,
    ];

    /// Returns the word a `form=` filter and a table cell name it by.
    fn word(self) -> &'static str {
        match self {
            Kind::Register => "register",
            Kind::Vtable => "vtable",
            Kind::Field => "field",
            Kind::Global => "global",
            Kind::Memory => "memory",
            Kind::Trampoline => "trampoline",
            Kind::Jump => "jump",
        }
    }

    /// Returns the kind a word names, `None` for no kind.
    ///
    /// # Arguments
    ///
    /// * `word` - The word, as `form=` gives it.
    fn parse(word: &str) -> Option<Kind> {
        Kind::ALL.into_iter().find(|k| k.word() == word)
    }
}

impl Form {
    /// Returns its kind.
    fn kind(self) -> Kind {
        match self {
            Form::Register => Kind::Register,
            Form::VtableSlot { .. } => Kind::Vtable,
            Form::Field { .. } => Kind::Field,
            Form::Global { .. } => Kind::Global,
            Form::Memory => Kind::Memory,
            Form::IntoTrampoline { .. } => Kind::Trampoline,
            Form::Jump => Kind::Jump,
        }
    }

    /// Returns the word a `form=` filter names it by.
    #[must_use]
    pub fn word(self) -> &'static str {
        self.kind().word()
    }

    /// Returns its cell in an agent's table: `vtable slot 1`, `field
    /// +0xc`, `global 0x402000`.
    #[must_use]
    pub fn spell(self) -> String {
        match self {
            Form::VtableSlot { slot } => format!("vtable slot {slot}"),
            Form::Field { offset } => format!("field {}", signed_hex(offset)),
            Form::Global { slot } => format!("global {slot:#x}"),
            Form::IntoTrampoline { entry } => format!("trampoline {entry:#x}"),
            Form::Register | Form::Memory | Form::Jump => self.word().to_owned(),
        }
    }

    /// Returns it as a sentence for a person.
    #[must_use]
    pub fn person(self) -> String {
        match self {
            Form::Register => "Calls through a register this block does not load.".to_owned(),
            Form::VtableSlot { slot } => {
                format!("Calls slot {slot} of the table an object's first word points at.")
            }
            Form::Field { offset } => format!(
                "Calls the pointer at offset {} of a structure.",
                signed_hex(offset)
            ),
            Form::Global { slot } => format!("Calls the pointer stored at {slot:#x}."),
            Form::Memory => {
                "Goes through a word in memory: a stack slot, an indexed table, or a register loaded from one."
                    .to_owned()
            }
            Form::IntoTrampoline { entry } => {
                format!(
                    "Calls the trampoline at {entry:#x}, which jumps on to an address it reads at run time."
                )
            }
            Form::Jump => "Jumps through a register.".to_owned(),
        }
    }
}

impl Why {
    /// Returns its cell in an agent's table.
    #[must_use]
    pub fn spell(self) -> String {
        match self {
            Why::NoTarget => "no target in the file".to_owned(),
            Why::SlotFilledAtRunTime { slot } => format!("{slot:#x} is filled at run time"),
            Why::Trampoline { through } => format!("through trampoline {through:#x}"),
            Why::NoJumpTable => "no jump table".to_owned(),
        }
    }

    /// Returns it as a sentence for a person.
    #[must_use]
    pub fn person(self) -> String {
        match self {
            Why::NoTarget => "Nothing in the file names where it goes.".to_owned(),
            Why::SlotFilledAtRunTime { slot } => {
                format!(
                    "The slot at {slot:#x} holds no function in the file; it is filled at run time."
                )
            }
            Why::Trampoline { through } => {
                format!(
                    "It goes through the trampoline at {through:#x}, which goes wherever its jump reads at run time."
                )
            }
            Why::NoJumpTable => "No jump table was found for this jump.".to_owned(),
        }
    }
}

impl Rule {
    /// Returns what admitted a candidate, as an agent's table says it.
    ///
    /// # Arguments
    ///
    /// * `form` - The form of the site it is a candidate of.
    #[must_use]
    pub fn spell(&self, form: Form) -> String {
        match self {
            Rule::VtableSlot { class } => match form {
                Form::VtableSlot { slot } => format!("slot {slot} of {class}"),
                Form::Register
                | Form::Field { .. }
                | Form::Global { .. }
                | Form::Memory
                | Form::IntoTrampoline { .. }
                | Form::Jump => format!("a slot of {class}"),
            },
            Rule::StoredSlot { store } => format!("stored at {store:#x}"),
        }
    }
}

/// Returns an offset as signed hex: `+0xc`, `-0x8`.
///
/// # Arguments
///
/// * `k` - The offset.
fn signed_hex(k: i64) -> String {
    let sign = if k < 0 { '-' } else { '+' };
    format!("{sign}{:#x}", k.unsigned_abs())
}

/// What a `borer://indirect` argument asks for.
#[derive(Debug, Default)]
struct Spec<'s> {
    /// The function or address whose sites to list, as written.
    function: Option<&'s str>,
    /// The form to keep.
    form: Option<Kind>,
}

/// Reads a `borer://indirect` argument: `[<function or address>][,form=<word>]`.
///
/// # Arguments
///
/// * `spec` - The argument, empty for none.
///
/// # Errors
///
/// When a word is given twice or a form is not one of [`Kind::ALL`], with the
/// form the argument takes.
fn read_spec(spec: &str) -> Result<Spec<'_>, String> {
    let mut out = Spec::default();
    for word in spec.split(',').map(str::trim).filter(|w| !w.is_empty()) {
        let twice = match word.strip_prefix("form=") {
            Some(f) => {
                let Some(kind) = Kind::parse(f) else {
                    let words: Vec<&str> = Kind::ALL.iter().map(|k| k.word()).collect();
                    return Err(format!(
                        "form={} is no form; give form= one of {}",
                        crate::text::quoted(f),
                        words.join(", ")
                    ));
                };
                out.form.replace(kind).is_some()
            }
            None => out.function.replace(word).is_some(),
        };
        if twice {
            return Err(format!(
                "{} gives a function or form= twice; borer://indirect takes [<function or address>][,form=<word>]",
                crate::text::quoted(spec)
            ));
        }
    }
    Ok(out)
}

/// Refuses a `borer://indirect` argument that does not read, before the
/// program is read.
///
/// # Arguments
///
/// * `spec` - The argument.
///
/// # Returns
///
/// What is wrong, or `None` for an argument that reads.
#[must_use]
pub fn indirect_check(spec: &str) -> Option<String> {
    read_spec(spec).err()
}

/// Lists the calls and jumps discovery resolved to no target, a row per
/// site with its function, form, why and candidates, for
/// `borer://indirect`.
///
/// Candidates are targets a rule admits, never callers: they enter no
/// cross-reference, call tree or call graph.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The names in force.
/// * `spec` - `[<function or address>][,form=<word>]`, empty for every
///   site.
/// * `window` - The page shown.
///
/// # Errors
///
/// When the argument does not read or names no function.
pub fn indirect_tsv(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    spec: &str,
    window: Window<'_>,
) -> Result<String, String> {
    let asked = read_spec(spec)?;
    let entry = match asked.function {
        Some(f) => {
            let va = crate::analysis::resolve_suggesting(p, a, o, f)?;
            Some(crate::analysis::function_entry(p, a, va)?)
        }
        None => None,
    };
    let found = census(p, a);
    let kept: Vec<&Site> = found
        .sites
        .iter()
        .filter(|s| entry.is_none_or(|e| s.function == e))
        .filter(|s| asked.form.is_none_or(|k| s.form.kind() == k))
        .collect();
    let functions = kept.iter().map(|s| s.function).collect::<BTreeSet<_>>();
    let shown: Vec<&&Site> = kept.iter().skip(window.skip).take(window.limit).collect();
    let mut out = format!(
        "# {} unresolved indirect call{} and jump{} in {} function{}{}, showing {} of {} from {}\n",
        kept.len(),
        plural(kept.len()),
        plural(kept.len()),
        functions.len(),
        plural(functions.len()),
        scope(a, o, entry, asked.form),
        shown.len(),
        kept.len(),
        window.skip
    );
    out.push_str(LEGEND);
    let _ = writeln!(
        out,
        "# a candidates cell gives the count first, then at most {CANDIDATES_MAX} in address order, each with its rule"
    );
    if !found.through.is_empty() {
        let _ = writeln!(
            out,
            "# {} trampoline{} (one block that jumps on through a register or a slot) not listed: a call into one is listed where it is made",
            found.through.len(),
            plural(found.through.len())
        );
    }
    out.push_str("site\tfunction\tform\twhy\tcandidates\n");
    let shown_len = shown.len();
    for s in shown {
        let _ = writeln!(
            out,
            "{:#x}\t{}\t{}\t{}\t{}",
            s.at,
            name_of(a, o, s.function),
            s.form.spell(),
            s.why.spell(),
            candidates(a, o, s)
        );
    }
    out.push_str(&window.next_page(kept.len(), shown_len));
    Ok(out)
}

/// The notes under the census's first line: where it comes from, what it
/// does not claim, and what the rules are.
const LEGEND: &str = "# discovery resolved no target for these; the decompiler may still resolve a vtable-shaped call whose receiver's class it knows, and decompile then names the method\n# forms are read from the site's block on x86 and arm64; other instruction sets say register, global or jump; memory is a stack slot, an indexed table or a register loaded from one; a vtable slot is a word of a table read from an object's first word, a word of any other loaded pointer a field\n# candidates: the functions a rule admits, never callers and not complete (classes borer did not recover and stores it did not see add none): vtable slot k admits what each recovered class holds in slot k, a global slot what an x86 store into exactly that slot writes\n";

/// Returns what the census was narrowed to, for its first line.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - The names in force.
/// * `entry` - The function asked for, if any.
/// * `form` - The form asked for, if any.
fn scope(a: &Analysis, o: &Overlay, entry: Option<u64>, form: Option<Kind>) -> String {
    let mut out = String::new();
    if let Some(e) = entry {
        let _ = write!(out, " ({} at {e:#x})", name_of(a, o, e));
    }
    if let Some(f) = form {
        let _ = write!(out, " of form {}", f.word());
    }
    out
}

/// Returns a site's candidates cell: `-` for none, else the count and the
/// kept ones, each with its name and rule.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - The names in force.
/// * `s` - The site.
fn candidates(a: &Analysis, o: &Overlay, s: &Site) -> String {
    if s.candidates_total == 0 {
        return "-".to_owned();
    }
    let listed: Vec<String> = s
        .candidates
        .iter()
        .map(|c| {
            format!(
                "{:#x} {} ({})",
                c.target,
                name_of(a, o, c.target),
                c.rule.spell(s.form)
            )
        })
        .collect();
    let more = s.candidates_total.saturating_sub(s.candidates.len());
    let tail = if more > 0 {
        format!(", {more} more")
    } else {
        String::new()
    };
    format!("{}: {}{tail}", s.candidates_total, listed.join(", "))
}
