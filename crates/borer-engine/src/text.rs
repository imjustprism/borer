//! Names and quoted text, made safe to render on one line of output.
//!
//! Every name borer prints comes from somewhere it does not control: the
//! symbol and section tables of the file under analysis, or an argument the
//! caller passed. Borer's output is line-oriented — one symbol, one function,
//! one section to a row — so text holding a newline does not merely look
//! wrong, it forges a row that reads exactly like a real one, and the agent
//! reading the listing has no way to tell the difference. Terminal escapes in
//! the same text colour or erase what surrounds them.
//!
//! So text from outside is escaped before it is rendered, at the point it is
//! adopted rather than at each of the places that print it.

/// Longest run of outside text any single row or message keeps.
///
/// Set above the longest name real binaries carry: a demangled C++ method with
/// its full signature runs to 239 characters, so a legitimate name survives
/// whole and only a crafted or pasted blob is cut. Without a cap a 64 KiB
/// export name makes a 64 KiB row, which is the unbounded output the crate
/// promises not to produce.
pub const OUTSIDE_MAX: usize = 256;

/// Longest path a message quotes back.
///
/// Wider than [`OUTSIDE_MAX`], because a path is legitimately longer than a
/// name: Windows allows 260 characters without asking and far more with the
/// long-path prefix, and a real path cut short is a path nobody can act on.
pub const PATH_MAX: usize = 512;

/// Escapes `text` so it renders as one bounded line.
///
/// Control characters become `\xNN`, and so do the invisible Unicode format
/// characters that reorder or hide text in a terminal — a name carrying
/// `U+202E` would otherwise print the rest of its row backwards. Everything
/// else, including ordinary non-ASCII, is left as it is.
///
/// # Arguments
///
/// * `text` - The outside text: a name from a file, or a caller's argument.
///
/// # Returns
///
/// The text with nothing in it that can end a line or move the cursor, at
/// most [`OUTSIDE_MAX`] characters wide, ending in `...` where it was cut.
#[must_use]
pub fn one_line(text: &str) -> String {
    escaped(text, OUTSIDE_MAX)
}

/// Bounds a path for a message, keeping both of its ends.
///
/// A path is the one kind of outside text whose tail matters most - the file
/// name is what identifies it - so cutting the end the way a name is cut
/// would throw away the useful half. A path longer than a filesystem can hold
/// is a caller's mistake rather than a path, and one of those should not cost
/// an agent its context to read back.
///
/// # Arguments
///
/// * `path` - The path as the caller wrote it.
///
/// # Returns
/// The path, or its two ends around `...`, escaped as [`one_line`] escapes.
#[must_use]
pub fn short_path(path: &str) -> String {
    let n = path.chars().count();
    if n <= PATH_MAX {
        return escaped(path, PATH_MAX);
    }
    let keep = PATH_MAX / 2;
    let head: String = path.chars().take(keep).collect();
    let tail: String = path.chars().skip(n - keep).collect();
    escaped(&format!("{head}...{tail}"), PATH_MAX + 3)
}

/// Escapes `text` to one line of at most `max` characters.
///
/// # Arguments
///
/// * `text` - The outside text.
/// * `max` - Widest result, before the `...` that marks a cut.
fn escaped(text: &str, max: usize) -> String {
    // The common case is a name that needs nothing done to it, and every
    // listing runs this over every row.
    if text.len() <= max && !text.chars().any(needs_escape) {
        return text.to_owned();
    }
    let mut out = String::with_capacity(text.len().min(max) + 4);
    let mut room = max;
    for c in text.chars() {
        let escaped;
        let piece: &str = if needs_escape(c) {
            escaped = format!("\\x{:02x}", c as u32);
            &escaped
        } else {
            escaped = c.to_string();
            &escaped
        };
        let width = piece.chars().count();
        if width > room {
            out.push_str("...");
            break;
        }
        room -= width;
        out.push_str(piece);
    }
    out
}

/// Quotes outside text for an error message, bounded and on one line.
///
/// An error that says which name failed is worth much more than one that does
/// not, but the text came from the caller and has no length of its own: a
/// mistyped paste would otherwise come back in full and cost the agent its
/// context to read.
///
/// # Arguments
///
/// * `text` - What the caller passed.
///
/// # Returns
///
/// The text from [`one_line`], in single quotes.
#[must_use]
pub fn quoted(text: &str) -> String {
    format!("'{}'", one_line(text))
}

/// Tells whether `c` must be escaped to stay on its own line and in place.
///
/// # Arguments
///
/// * `c` - The character.
fn needs_escape(c: char) -> bool {
    // SPEC: U+202A..U+202E are the bidirectional embeddings and overrides and
    // U+2066..U+2069 the isolates; U+200E, U+200F and U+061C are the marks.
    // All of them reorder the text that follows without printing anything.
    c.is_control()
        || matches!(c, '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}')
        || matches!(c, '\u{200e}' | '\u{200f}' | '\u{061c}')
}

#[cfg(test)]
mod tests {
    use super::{OUTSIDE_MAX, PATH_MAX, one_line, quoted, short_path};

    /// A name with nothing wrong with it comes back untouched.
    ///
    /// Escaping is for text that can move the cursor or end a line, and
    /// ordinary non-ASCII does neither: a name is easier to read as the
    /// bytes its author wrote.
    ///
    /// # Panics
    ///
    /// When an ordinary name is changed.
    #[test]
    fn an_ordinary_name_is_left_alone() {
        let name = "public: void __cdecl FMOD::Studio::System::release(void)";
        assert_eq!(one_line(name), name);
        // Non-ASCII is not suspicious in itself and stays readable.
        assert_eq!(one_line("café_init"), "café_init");
    }

    /// A newline in a name cannot end the row it is printed in.
    ///
    /// This is the whole point of the module: borer's listings are one
    /// record to a line, so a name carrying a newline would read as two
    /// records and the second is whatever the file wanted to say.
    ///
    /// # Panics
    ///
    /// When a newline survives into the rendered name.
    #[test]
    fn a_newline_in_a_name_cannot_forge_a_row() {
        let forged = one_line("A\nexport 0xdeadbeef FORGED");
        assert!(!forged.contains('\n'), "{forged}");
        assert_eq!(forged, "A\\x0aexport 0xdeadbeef FORGED");
    }

    /// Escapes and overrides are shown rather than obeyed.
    ///
    /// An ANSI escape colours or erases the text around it, and a
    /// bidirectional override prints the rest of the row backwards; both
    /// change what a reader sees without changing what is there.
    ///
    /// # Panics
    ///
    /// When either reaches the terminal as itself.
    #[test]
    fn terminal_escapes_and_bidi_overrides_are_defused() {
        assert_eq!(one_line("red\u{1b}[31m"), "red\\x1b[31m");
        assert_eq!(one_line("txet\u{202e}"), "txet\\x202e");
        assert_eq!(one_line("a\u{200f}b"), "a\\x200fb");
    }

    /// A name is bounded, and a real one is under the bound.
    ///
    /// # Panics
    ///
    /// When a long name is unbounded, or a real one is cut.
    #[test]
    fn a_long_name_is_cut_to_a_bounded_width() {
        let out = one_line(&"a".repeat(10_000));
        assert_eq!(out.chars().count(), OUTSIDE_MAX + 3);
        assert!(out.ends_with("..."), "{out}");
        // The longest name seen in a real binary is 239 characters and must
        // survive whole, or the cap would be hiding real analysis.
        let real = "b".repeat(239);
        assert_eq!(one_line(&real), real);
    }

    /// The cut counts characters, so it cannot split one in half.
    ///
    /// # Panics
    ///
    /// When the cut lands inside a character.
    #[test]
    fn a_cut_never_splits_a_character() {
        let out = one_line(&"é".repeat(10_000));
        assert_eq!(out.chars().count(), OUTSIDE_MAX + 3);
        assert!(out.starts_with("éé"), "{out}");
    }

    /// A path keeps both ends, because its name is at the far one.
    ///
    /// Cutting a path the way a name is cut would drop the file name, which
    /// is the part that says which file was meant.
    ///
    /// # Panics
    ///
    /// When a real path is cut, or an absurd one is not, or the cut loses the
    /// name at the end of it.
    #[test]
    fn a_path_is_bounded_without_losing_its_name() {
        let real = r"C:\Users\someone\Projects\target\release\borer.exe";
        assert_eq!(short_path(real), real, "a real path is left alone");
        // Windows allows 260 characters without asking for them.
        let deep = format!(r"C:\{}\app.exe", "dir".repeat(80));
        assert_eq!(short_path(&deep), deep, "a legitimately long path survives");

        let absurd = format!(r"C:\{}\target_name.exe", "verylongdir".repeat(400));
        let cut = short_path(&absurd);
        assert!(
            cut.chars().count() <= PATH_MAX + 3,
            "{}",
            cut.chars().count()
        );
        assert!(
            cut.starts_with(r"C:\verylongdir"),
            "the head is kept: {cut}"
        );
        assert!(
            cut.ends_with("target_name.exe"),
            "and the name at the tail: {cut}"
        );
        assert!(cut.contains("..."), "with the cut marked: {cut}");
    }

    /// An error names what failed without repeating all of it.
    ///
    /// # Panics
    ///
    /// When the echo is unbounded.
    #[test]
    fn quoting_bounds_what_an_error_echoes() {
        assert_eq!(quoted("sub_401000"), "'sub_401000'");
        let huge = quoted(&"z".repeat(20_000));
        assert!(huge.chars().count() < OUTSIDE_MAX + 8, "{}", huge.len());
    }
}
