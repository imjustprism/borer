//! What a name or comment must be for the annotating tools to set it: the
//! rule an agent's annotations and a project file's are held to alike.

use super::Overlay;
use crate::program::Program;

/// Which annotation a call carries, for the message that refuses one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Annotation {
    /// A name set by `set_name`.
    Name,
    /// A comment set by `set_comment`.
    Comment,
    /// A type applied by `set_type`.
    Type,
}

impl std::fmt::Display for Annotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Name => "name",
            Self::Comment => "comment",
            Self::Type => "type",
        })
    }
}

/// Refuses a name or comment escaped to one line that a row still cannot
/// show.
///
/// It is what a caller's check of unescaped text refuses but for the text
/// escaping takes out ([`crate::text::one_line`]), so text read from a file
/// is not escaped a second time to be checked.
///
/// # Arguments
///
/// * `text` - The annotation.
/// * `what` - Which annotation it is, for the message.
///
/// # Errors
///
/// When the text is empty, blank, holds a control character, or is longer
/// than a row can show.
pub fn must_fit_an_escaped_row(text: &str, what: Annotation) -> Result<(), String> {
    if text.trim().is_empty() {
        return Err(format!("the {what} is empty"));
    }
    if text.chars().any(char::is_control) {
        return Err(format!(
            "the {what} holds a control character; annotations are one line each"
        ));
    }
    let width = text.chars().count();
    if width > crate::text::OUTSIDE_MAX {
        return Err(format!(
            "the {what} is {width} characters; {} is the most a listing row shows",
            crate::text::OUTSIDE_MAX
        ));
    }
    Ok(())
}

/// Refuses an annotation a person or an agent gives that no row shows as given.
///
/// That is one [`must_fit_an_escaped_row`] refuses, or one holding text
/// [`crate::text::one_line`] would escape: a character that reorders or
/// hides what is printed around it.
///
/// # Arguments
///
/// * `text` - The annotation as given.
/// * `what` - Which annotation it is, for the message.
///
/// # Errors
///
/// When the text is empty, blank, longer than a row can show, or holds
/// anything that would end its line or move what is printed around it.
pub fn must_fit_a_row(text: &str, what: Annotation) -> Result<(), String> {
    must_fit_an_escaped_row(text, what)?;
    if crate::text::one_line(text) != text {
        return Err(format!(
            "the {what} holds text that reorders what is printed around it"
        ));
    }
    Ok(())
}

/// Tells whether an annotation at `va` has a place: a section declares
/// it, with or without file bytes ([`Program::declared_at`]).
///
/// Nothing borer lists lives outside the image, so a name or comment there
/// would sit in the overlay and the project file and never be shown; `0x1`
/// is a typo, not a place. A section the file holds no bytes for (`.bss`)
/// is in the image, and the decompiler names its globals, so it is one.
/// The annotating tools and a loaded project file are held to it alike.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The address the annotation is for.
#[must_use]
pub fn placeable(program: &Program, va: u64) -> bool {
    program.declared_at(va).is_some()
}

/// Refuses an annotation at an address that is no place for one
/// ([`placeable`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The address the annotation is for.
/// * `what` - Which annotation it is, for the message.
///
/// # Errors
///
/// When no section declares `va`, listing the sections that exist.
pub fn must_be_in_a_section(program: &Program, va: u64, what: Annotation) -> Result<(), String> {
    if placeable(program, va) {
        return Ok(());
    }
    Err(format!(
        "{va:#x} is in no section, so nothing there can take a {what}; sections: {}",
        program.section_list()
    ))
}

/// Punctuation a name may hold besides letters and digits: C++ scopes,
/// templates and destructors (`::`, `<>`, `~`), MSVC and Itanium mangling
/// (`?`, `@`, `$`), ELF's split parts (`foo.cold`) and `_`.
const NAME_PUNCTUATION: &str = "_:<>~?@$.";

/// Refuses a name the pseudo-C or a later lookup could not carry.
///
/// A name is printed where C expects an identifier and is looked up as
/// one, so a space, a parenthesis or a leading digit would break both.
///
/// # Arguments
///
/// * `name` - The name asked for.
///
/// # Errors
///
/// When the name opens with a digit or holds a character no identifier
/// or mangled name has; the message names the character.
pub fn must_be_a_name(name: &str) -> Result<(), String> {
    if name.starts_with(|c: char| c.is_ascii_digit()) {
        return Err(format!(
            "{} opens with a digit; a name must not, or it reads as a number",
            crate::text::quoted(name)
        ));
    }
    match name
        .chars()
        .find(|&c| !c.is_alphanumeric() && !NAME_PUNCTUATION.contains(c))
    {
        Some(c) => Err(format!(
            "{} holds {c:?}; a name is letters, digits and {NAME_PUNCTUATION}",
            crate::text::quoted(name)
        )),
        None => Ok(()),
    }
}

/// Leaves out of a loaded overlay the names and comments `set_name` and
/// `set_comment` would not set ([`must_fit_an_escaped_row`],
/// [`must_be_a_name`]).
///
/// A project file is text from outside, edited by hand and passed around,
/// so its annotations are held to the rule an agent's are. Each was escaped
/// to a line as the file was read ([`crate::text::one_line`]), so it is
/// held to what the rule refuses of escaped text. One the rule refuses is
/// left out, as one at an address no section holds is
/// ([`super::project::keep_placeable`]); the file's other annotations load.
///
/// # Arguments
///
/// * `o` - The overlay a project file rebuilt; left holding what passes.
/// * `room` - How many of those left out to say.
/// * `said` - Takes a `name at 0x0 (why)` entry for each of the first
///   `room` left out: names, then comments, each in address order.
///
/// # Returns
///
/// How many were left out, said or not.
pub fn keep_settable(o: &mut Overlay, room: usize, said: &mut Vec<String>) -> usize {
    let mut left_out = 0usize;
    let mut held = |what: Annotation, va: u64, text: &str| {
        let refused = must_fit_an_escaped_row(text, what).and_then(|()| match what {
            Annotation::Name => must_be_a_name(text),
            Annotation::Comment | Annotation::Type => Ok(()),
        });
        let Err(e) = refused else {
            return true;
        };
        if left_out < room {
            said.push(format!("{what} at {va:#x} ({e})"));
        }
        left_out = left_out.saturating_add(1);
        false
    };
    o.names
        .retain(|&va, n| held(Annotation::Name, va, n.as_str()));
    o.comments
        .retain(|&va, c| held(Annotation::Comment, va, c.as_str()));
    left_out
}

#[cfg(test)]
mod tests {
    use super::{Annotation, must_be_a_name, must_fit_a_row};

    /// A name that would reorder or hide what is printed around it, or that no row can
    /// show, is refused before it is planned; a plain one passes both checks.
    ///
    /// # Panics
    ///
    /// When a name is let through or refused wrongly.
    #[test]
    fn a_name_that_hides_or_reorders_text_is_refused() {
        assert_eq!(must_fit_a_row("check_license", Annotation::Name), Ok(()));
        assert_eq!(must_be_a_name("check_license"), Ok(()));
        for name in ["check_\u{202e}esnecil", "main\u{200b}", "a\"b\nc"] {
            let refused = must_fit_a_row(name, Annotation::Name).and(must_be_a_name(name));
            assert!(refused.is_err(), "{name:?}");
        }
        assert!(must_fit_a_row(&"a".repeat(100_000), Annotation::Name).is_err());
    }
}
