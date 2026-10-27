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
//!
//! A name the caller misspells is answered with the names nearest it
//! ([`nearest`]), so a miss teaches the right name instead of costing a
//! listing to find it.

use std::fmt::Write as _;

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
    if text.len() <= max && !text.chars().any(needs_escape) {
        return text.to_owned();
    }
    let mut out = String::with_capacity(text.len().min(max) + 4);
    let mut room = max;
    for c in text.chars() {
        let escaped;
        let piece: &str = if needs_escape(c) {
            escaped = format!("\\x{:02x}", u32::from(c));
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

/// How near a candidate is to a word nothing matched, nearest first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Near {
    /// The candidate contains the word; the value is the candidate's length
    /// in bytes, so the shortest container comes first.
    Contains(usize),
    /// The candidate, or its last `::` segment, is this many single
    /// character edits from the word.
    Edits(usize),
    /// The candidate, or its last `::` segment, opens with the same
    /// characters as the word, this many, the most first.
    Prefix(std::cmp::Reverse<usize>),
}

/// Returns the candidates nearest a word nothing matched, nearest first.
///
/// A candidate containing the word ranks first, the shortest first; then
/// a candidate a few single-character edits from it, whole or by its last
/// `::` segment, so `chk_serial` finds `crackme::check_serial`; then one
/// opening with the word's first four characters or more, so the
/// abbreviation `disasm` is found for `disassemble`. A word shorter than
/// three characters is in too many names to find containers by, and the
/// edits allowed are a third of the word's length, at least two, so a
/// word nothing resembles finds nothing. Case is ignored, and ties go by
/// the candidate's text, so the answer is deterministic.
///
/// # Arguments
///
/// * `want` - The word that matched nothing.
/// * `candidates` - The names it could have meant; a name given twice is
///   returned once.
/// * `n` - Most candidates returned.
///
/// # Returns
///
/// At most `n` candidates, nearest first; empty for a blank word.
#[must_use]
pub fn nearest<'a>(
    want: &str,
    candidates: impl IntoIterator<Item = &'a str>,
    n: usize,
) -> Vec<&'a str> {
    /// Shortest word a containing candidate is suggested for.
    const CONTAINED_MIN: usize = 3;
    /// The edits allowed are the word's length divided by this.
    const EDITS_PER: usize = 3;
    /// Fewest edits allowed, for a short word.
    const EDITS_MIN: usize = 2;
    /// Fewest opening characters a candidate shares with the word to rank
    /// by them.
    const PREFIX_MIN: usize = 4;
    let want = want.trim().to_lowercase();
    let len = want.chars().count();
    if len == 0 {
        return Vec::new();
    }
    let limit = (len / EDITS_PER).max(EDITS_MIN);
    let mut ranked: Vec<(Near, &str)> = candidates
        .into_iter()
        .filter_map(|c| {
            let lower = c.to_lowercase();
            if len >= CONTAINED_MIN && lower.contains(&want) {
                return Some((Near::Contains(lower.len()), c));
            }
            let tail = lower.rsplit("::").next().unwrap_or(&lower);
            let forms = [lower.as_str(), tail];
            let edits = forms
                .iter()
                .filter_map(|t| edits_within(&want, t, limit))
                .min()
                .map(Near::Edits);
            let shared = forms
                .iter()
                .map(|t| {
                    t.chars()
                        .zip(want.chars())
                        .take_while(|(a, b)| a == b)
                        .count()
                })
                .max()
                .filter(|&shared| shared >= PREFIX_MIN)
                .map(|shared| Near::Prefix(std::cmp::Reverse(shared)));
            edits.or(shared).map(|near| (near, c))
        })
        .collect();
    ranked.sort_unstable();
    ranked.dedup();
    ranked.into_iter().take(n).map(|(_, c)| c).collect()
}

/// Counts the single-character edits (insertions, deletions,
/// substitutions and swaps of two neighbours) that turn `a` into `b`,
/// when there are at most `limit`.
///
/// A swap costs one edit, as a typo makes it (`WinMian` for `WinMain`);
/// no character is edited twice (the optimal string alignment distance).
///
/// # Arguments
///
/// * `a` - One word.
/// * `b` - The other.
/// * `limit` - Most edits worth counting; past it the count stops.
///
/// # Returns
///
/// The edit count, or `None` when it is above `limit`.
fn edits_within(a: &str, b: &str, limit: usize) -> Option<usize> {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    if a.len().abs_diff(b.len()) > limit {
        return None;
    }
    let mut before: Vec<usize> = Vec::new();
    let mut last: Vec<usize> = (0..=b.len()).collect();
    for (i, ca) in a.iter().enumerate() {
        let mut row = Vec::with_capacity(b.len() + 1);
        row.push(i + 1);
        for (j, cb) in b.iter().enumerate() {
            let mut d = (last[j] + usize::from(ca != cb))
                .min(last[j + 1] + 1)
                .min(row[j] + 1);
            if i > 0 && j > 0 && *ca == b[j - 1] && a[i - 1] == *cb {
                d = d.min(before[j - 1] + 1);
            }
            row.push(d);
        }
        if row.iter().min().is_some_and(|&least| least > limit) {
            return None;
        }
        before = std::mem::replace(&mut last, row);
    }
    last.last().copied().filter(|&d| d <= limit)
}

/// Tells whether `c` must be escaped to stay on its own line and in place.
///
/// # Arguments
///
/// * `c` - The character.
fn needs_escape(c: char) -> bool {
    c.is_control()
        || matches!(c, '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}')
        || matches!(c, '\u{200e}' | '\u{200f}' | '\u{061c}')
}

/// A count read for its plural: the widths borer holds counts in, `u64`
/// and `usize`.
pub(crate) trait Count {
    /// The count as a `u64`, lossless from both widths there are.
    fn count(self) -> u64;
}

impl Count for u64 {
    fn count(self) -> u64 {
        self
    }
}

impl Count for usize {
    fn count(self) -> u64 {
        crate::num::from_usize(self)
    }
}

/// `s` when `n` is not one, so a count reads `1 file` and `2 files`.
///
/// # Arguments
///
/// * `n` - The count, held as a `u64` or a `usize`.
#[must_use]
pub(crate) fn plural(n: impl Count) -> &'static str {
    if n.count() == 1 { "" } else { "s" }
}

/// Returns bytes as lowercase hex with no separators.
///
/// # Arguments
///
/// * `bytes` - The bytes.
#[must_use]
pub(crate) fn hex(bytes: &[u8]) -> String {
    bytes
        .iter()
        .fold(String::with_capacity(bytes.len() * 2), |mut s, b| {
            let _ = write!(s, "{b:02x}");
            s
        })
}

/// Reads whitespace-tolerant pairs of hex digits into bytes.
///
/// # Arguments
///
/// * `text` - The hex, with spaces allowed between pairs.
///
/// # Returns
///
/// The bytes, or `None` when a character is not a hex digit or the count of
/// digits is odd.
#[must_use]
pub fn parse_hex_bytes(text: &str) -> Option<Vec<u8>> {
    let clean: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    if clean.is_empty() || !clean.len().is_multiple_of(2) {
        return None;
    }
    (0..clean.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(clean.get(i..i + 2)?, 16).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{
        OUTSIDE_MAX, PATH_MAX, edits_within, nearest, one_line, plural, quoted, short_path,
    };

    /// A count's noun takes its plural from either width a count is held in.
    ///
    /// # Panics
    ///
    /// When one reads `1 files` or `2 file`.
    #[test]
    fn a_count_pluralizes_from_either_width() {
        assert_eq!(plural(1u64), "");
        assert_eq!(plural(2u64), "s");
        assert_eq!(plural(1usize), "");
        assert_eq!(plural(2usize), "s");
    }

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

    /// Edits count insertions, deletions and substitutions, and stop
    /// counting past the limit.
    ///
    /// # Panics
    ///
    /// When a count is wrong or one past the limit is returned.
    #[test]
    fn edits_count_what_turns_one_word_into_the_other() {
        assert_eq!(edits_within("emulat", "emulate", 2), Some(1));
        assert_eq!(edits_within("chk_serial", "check_serial", 2), Some(2));
        assert_eq!(edits_within("kitten", "sitting", 3), Some(3));
        assert_eq!(edits_within("same", "same", 0), Some(0));
        assert_eq!(edits_within("kitten", "sitting", 2), None);
        assert_eq!(edits_within("a", "abcdef", 2), None);
        assert_eq!(edits_within("winmian", "winmain", 2), Some(1));
        assert_eq!(edits_within("winmian", "wwinmain", 2), Some(2));
        assert_eq!(edits_within("xy", "yx", 1), Some(1));
    }

    /// A misspelled name finds the names it meant, nearest first.
    ///
    /// A container comes before an edit, the qualified name is found by its
    /// last segment and an abbreviation by its opening, case ignored, each
    /// once; a word nothing resembles finds nothing.
    ///
    /// # Panics
    ///
    /// When the order, the matching or the cap is wrong.
    #[test]
    fn a_misspelled_name_finds_the_names_nearest_it() {
        let names = [
            "crackme::main",
            "crackme::check_serial",
            "emulate",
            "enums",
            "encode",
            "Emulate",
            "check_serial_twice",
        ];
        assert_eq!(
            nearest("chk_serial", names, 3),
            vec!["crackme::check_serial"]
        );
        assert_eq!(
            nearest("check_serial", names, 3),
            vec!["check_serial_twice", "crackme::check_serial"]
        );
        assert_eq!(nearest("emulat", names, 3), vec!["Emulate", "emulate"]);
        assert_eq!(nearest("EMULATE", names, 1), vec!["Emulate"]);
        assert_eq!(
            nearest("emulate", ["emulate", "emulate", "emulates"], 3),
            vec!["emulate", "emulates"]
        );
        assert_eq!(
            nearest("disassemble", ["dis", "decompile", "disasm"], 3),
            vec!["disasm"]
        );
        assert_eq!(
            nearest("WinMian", ["wWinMain", "WinMainCRTStartup", "main"], 3),
            vec!["wWinMain", "WinMainCRTStartup"]
        );
        assert!(nearest("zzzzqqqq", names, 3).is_empty());
        assert!(nearest("  ", names, 3).is_empty());
    }
}
