//! How the tools and the app word a plan's lines.

use super::Line;

impl Line {
    /// Spells one line of a plan as the tools word it, without the `would`
    /// a dry run opens with: the line, and the note that follows the answer.
    ///
    /// # Arguments
    ///
    /// * `dry` - Whether the plan is a dry run's.
    ///
    /// # Returns
    ///
    /// The line's words, and its note, empty when it has none.
    #[must_use]
    pub fn said(&self, dry: bool) -> (String, String) {
        match self {
            Self::Named {
                target,
                function,
                old,
                new,
                number,
            } => {
                let what = if *function { "function" } else { "data" };
                let numeric = number.map_or_else(String::new, |_| self.noted());
                let line = if dry {
                    format!("set name of {what} {target:#x} ({old}) to '{new}'")
                } else {
                    format!("renamed {what} {target:#x}: {old} -> {new}")
                };
                (line, numeric)
            }
            Self::Commented { at } if dry => (format!("set comment at {at:#x}"), String::new()),
            Self::Commented { at } => (format!("comment set at {at:#x}"), String::new()),
            Self::Declared { types, abi, lines } => {
                /// Types a reply describes before it counts the rest.
                const SHOWN: usize = 64;
                let verb = if dry {
                    "dry-run: would define"
                } else {
                    "defined"
                };
                let mut out = format!("{verb} {types} type(s) from C, laid out for {abi}:\n");
                for line in lines.iter().take(SHOWN) {
                    out.push_str(line);
                    out.push('\n');
                }
                if lines.len() > SHOWN {
                    out.push_str(&format!(
                        "# showing {SHOWN} of {} lines; `types` lists every type\n",
                        lines.len()
                    ));
                }
                (out, String::new())
            }
            Self::Laid {
                name,
                prototypes,
                lines,
            } => {
                let (define, state) = if dry {
                    ("dry-run: would define", "state")
                } else {
                    ("defined", "stated")
                };
                let mut out = format!(
                    "{define} struct {name} and {state} {prototypes} prototype(s); decompile then names the fields:\n"
                );
                for line in lines {
                    out.push_str(line);
                    out.push('\n');
                }
                (out, String::new())
            }
            Self::Stated { would, .. } if dry => (would.clone(), String::new()),
            Self::Stated { done, .. } => (done.clone(), String::new()),
            Self::Unknown(_) => (String::new(), self.noted()),
        }
    }

    /// Returns the note a line carries, as a sentence: a name that also
    /// reads as a number, or a type no word borer knows names; `None` for
    /// a line with none.
    #[must_use]
    pub fn note(&self) -> Option<String> {
        match self {
            Self::Named {
                new,
                number: Some(n),
                ..
            } => Some(format!(
                "'{new}' also reads as the number {n:#x}; an address argument finds the name first, and 0x-prefixed text is always an address"
            )),
            Self::Unknown(types) => Some(format!(
                "{} names no user type or C type word borer knows, so it passes as a word",
                types.join(", ")
            )),
            Self::Named { number: None, .. }
            | Self::Commented { .. }
            | Self::Declared { .. }
            | Self::Laid { .. }
            | Self::Stated { .. } => None,
        }
    }

    /// Returns the note as the tools append it to an answer: on a line of
    /// its own after `# note: `, empty for a line with none.
    fn noted(&self) -> String {
        self.note()
            .map_or_else(String::new, |note| format!("\n# note: {note}"))
    }
}
