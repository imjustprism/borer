//! The variable arguments a `printf` or `scanf` format string asks for.
//!
//! A variadic import's declaration says nothing of the arguments past its
//! fixed ones, so a call renders whatever registers the caller happened to
//! set. Its format string, when the call passes a literal, says exactly
//! how many follow and what each is: one per conversion, one more per `*`
//! width or precision, a `double` for a floating conversion of `printf`,
//! and a pointer for every `scanf` conversion that assigns.

/// What one variable argument is to the machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Arg {
    /// An integer of at most 32 bits, passed widened to a word.
    Int,
    /// A 64-bit integer: two stack words on a 32-bit target.
    Long,
    /// A `double`: a vector register where the convention passes floats,
    /// two stack words on a 32-bit target.
    Double,
    /// A pointer.
    Pointer,
}

impl Arg {
    /// Counts the stack words the argument takes on a 32-bit target.
    pub(super) fn words32(self) -> u8 {
        match self {
            Self::Long | Self::Double => 2,
            Self::Int | Self::Pointer => 1,
        }
    }
}

/// Which family a format string belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Family {
    /// `printf`: each conversion reads a value.
    Print,
    /// `scanf`: each assigning conversion writes through a pointer.
    Scan,
}

impl Family {
    /// Reads the family from a callee's name: `printf` and `scanf` and
    /// their `f`, `s`, `w`, `_s` and `_l` forms (`wsprintfW`, `swscanf_s`).
    ///
    /// # Arguments
    ///
    /// * `name` - The callee's bare name.
    ///
    /// # Returns
    ///
    /// The family, or `None` when the name is neither.
    pub(super) fn of(name: &str) -> Option<Self> {
        let lower = name.to_ascii_lowercase();
        if lower.contains("printf") {
            Some(Self::Print)
        } else if lower.contains("scanf") {
            Some(Self::Scan)
        } else {
            None
        }
    }
}

/// Most variable arguments one format string is read for.
const ARGS_MAX: usize = 64;

/// Reads the variable arguments a format string asks for.
///
/// The Microsoft size prefixes (`I64`, `I32`, `I`, `w`) are read beside the
/// C ones (`hh`, `h`, `l`, `ll`, `j`, `z`, `t`, `L`). A `scanf` `_s`
/// function takes a buffer size after each `%s`, `%c` and `%[`, which
/// `secure` adds.
///
/// # Arguments
///
/// * `format` - The format's characters, the terminator excluded.
/// * `family` - Whether it formats or scans.
/// * `secure` - The callee is a `scanf` `_s` form.
///
/// # Returns
///
/// The arguments in order, or `None` when the format uses positional
/// arguments (`%1$d`), names a conversion it cannot place, or asks for
/// more than [`ARGS_MAX`].
pub(super) fn arguments(format: &[char], family: Family, secure: bool) -> Option<Vec<Arg>> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < format.len() {
        if format.get(i) != Some(&'%') {
            i += 1;
            continue;
        }
        i += 1;
        if format.get(i) == Some(&'%') {
            i += 1;
            continue;
        }
        let mut assigns = true;
        if family == Family::Scan && format.get(i) == Some(&'*') {
            assigns = false;
            i += 1;
        }
        while let Some(c) = format.get(i) {
            match c {
                '-' | '+' | ' ' | '#' | '0' if family == Family::Print => i += 1,
                _ => break,
            }
        }
        let mut stars = 0usize;
        let mut digits_then_dollar = false;
        for _ in 0..2 {
            if format.get(i) == Some(&'*') {
                stars += 1;
                i += 1;
            } else {
                let start = i;
                while format.get(i).is_some_and(char::is_ascii_digit) {
                    i += 1;
                }
                if i > start && format.get(i) == Some(&'$') {
                    digits_then_dollar = true;
                }
            }
            if format.get(i) == Some(&'.') && family == Family::Print {
                i += 1;
                continue;
            }
            break;
        }
        if digits_then_dollar {
            return None;
        }
        if family == Family::Print {
            out.extend(std::iter::repeat_n(Arg::Int, stars));
        } else if stars > 0 {
            return None;
        }
        let mut long = false;
        loop {
            let rest = format.get(i..).unwrap_or(&[]);
            if rest.starts_with(&['I', '6', '4']) || rest.starts_with(&['l', 'l']) {
                long = true;
                i += if rest.first() == Some(&'I') { 3 } else { 2 };
            } else if rest.starts_with(&['I', '3', '2']) {
                i += 3;
            } else if let Some(c) = rest.first().filter(|c| matches!(c, 'h' | 'l' | 'L' | 'w')) {
                i += 1;
                if *c == 'L' {
                    long = true;
                }
            } else if let Some(c) = rest
                .first()
                .filter(|c| matches!(c, 'I' | 'j' | 'z' | 't' | 'q'))
            {
                i += 1;
                long |= matches!(c, 'j' | 'q');
            } else {
                break;
            }
        }
        let conv = *format.get(i)?;
        i += 1;
        if conv == '[' {
            if format.get(i) == Some(&'^') {
                i += 1;
            }
            if format.get(i) == Some(&']') {
                i += 1;
            }
            while format.get(i).is_some_and(|c| *c != ']') {
                i += 1;
            }
            i += 1;
        }
        let arg = match (family, conv) {
            (Family::Scan, _) if !assigns => None,
            (
                Family::Scan,
                'd' | 'i' | 'u' | 'o' | 'x' | 'X' | 'n' | 'p' | 'a' | 'A' | 'e' | 'E' | 'f' | 'F'
                | 'g' | 'G',
            ) => Some(Arg::Pointer),
            (Family::Scan, 's' | 'S' | 'c' | 'C' | '[') => {
                out.push(Arg::Pointer);
                secure.then_some(Arg::Int)
            }
            (Family::Print, 'd' | 'i' | 'u' | 'o' | 'x' | 'X' | 'c' | 'C') => {
                Some(if long { Arg::Long } else { Arg::Int })
            }
            (Family::Print, 'e' | 'E' | 'f' | 'F' | 'g' | 'G' | 'a' | 'A') => Some(Arg::Double),
            (Family::Print, 's' | 'S' | 'p' | 'n' | 'Z') => Some(Arg::Pointer),
            (Family::Print | Family::Scan, _) => return None,
        };
        out.extend(arg);
        if out.len() > ARGS_MAX {
            return None;
        }
    }
    Some(out)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Arg, Family, arguments};

    /// Reads a format's arguments from text.
    ///
    /// # Arguments
    ///
    /// * `f` - The format.
    /// * `family` - Print or scan.
    /// * `secure` - A scan `_s` form.
    fn read(f: &str, family: Family, secure: bool) -> Option<Vec<Arg>> {
        arguments(&f.chars().collect::<Vec<_>>(), family, secure)
    }

    /// Each conversion reads one argument of its class; `%%` reads none,
    /// a `*` width or precision reads an `int` first.
    #[test]
    fn print_conversions_read_their_arguments() {
        use Arg::{Double, Int, Long, Pointer};
        assert_eq!(
            read("%s: %d (%5.2f) %% %llx %I64u %p\n", Family::Print, false),
            Some(vec![Pointer, Int, Double, Long, Long, Pointer])
        );
        assert_eq!(
            read("%-*.*s|%c", Family::Print, false),
            Some(vec![Int, Int, Pointer, Int])
        );
        assert_eq!(
            read("%ls %hs %Iu %zu", Family::Print, false),
            Some(vec![Pointer, Pointer, Int, Int])
        );
        assert_eq!(read("no conversions", Family::Print, false), Some(vec![]));
        assert_eq!(read("%1$d", Family::Print, false), None);
        assert_eq!(read("%k", Family::Print, false), None);
        assert_eq!(read("100%", Family::Print, false), None);
    }

    /// A scan conversion writes through a pointer, a suppressed one takes
    /// nothing, and an `_s` form takes a size after each buffer.
    #[test]
    fn scan_conversions_take_pointers() {
        use Arg::{Int, Pointer};
        assert_eq!(
            read("%d %*d %s", Family::Scan, false),
            Some(vec![Pointer, Pointer])
        );
        assert_eq!(
            read("%d %[^,],%c", Family::Scan, true),
            Some(vec![Pointer, Pointer, Int, Pointer, Int])
        );
        assert_eq!(Family::of("swscanf_s"), Some(Family::Scan));
        assert_eq!(Family::of("wsprintfW"), Some(Family::Print));
        assert_eq!(Family::of("strtol"), None);
    }
}
