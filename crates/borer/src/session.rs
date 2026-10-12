//! The session ledger behind `borer://session`: what this session loaded,
//! named, commented and typed, and the answers it was given.
//!
//! An agent's context does not outlive a compaction or a new chat, and the
//! session does: after either, the agent re-ran the triage and decompiled
//! again what it had already read. The ledger answers "where was I" in one
//! read. It holds the last [`KEPT`] changes and the last [`KEPT`] distinct
//! requests in the order they came, and nothing else, so the same calls
//! give the same text: no clock, no randomness.

use std::collections::VecDeque;
use std::fmt::Write as _;

/// Most changes, and most requests, the ledger keeps; the oldest go first.
const KEPT: usize = 64;

/// Longest line the ledger keeps for one change or request, in characters.
const LINE_MAX: usize = 200;

/// The tools whose applied call changes what the session holds. A
/// dry-run call (every one but the loads and the save, unless
/// `dry_run=false`) changes nothing and is not a change.
const CHANGING: [&str; 7] = [
    "load_binary",
    "load_project",
    "save_project",
    "set_name",
    "set_comment",
    "set_type",
    "script",
];

/// The tools that change what the session holds whether or not they are
/// told `dry_run=false`.
const ALWAYS_APPLIED: [&str; 3] = ["load_binary", "load_project", "save_project"];

/// One request the session answered.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Request {
    /// The request as the answer memory keys it: `tool:<name>:<args>` or
    /// the URI with its page.
    key: String,
    /// Whether its answer showed fewer rows than it had, or was cut to the
    /// byte budget.
    capped: bool,
    /// Whether it asked for an offset or a limit.
    paged: bool,
}

/// What this session changed and asked, for `borer://session`.
#[derive(Debug, Default)]
pub(crate) struct Ledger {
    /// The last [`KEPT`] changes, oldest first, each `<tool> <arguments>`.
    changes: VecDeque<String>,
    /// Changes made in all, kept or not.
    changed: usize,
    /// The last [`KEPT`] distinct requests, each where it was last asked.
    requests: VecDeque<Request>,
    /// Answers given in all, a repeat counted again.
    answered: usize,
    /// The overlay's fingerprint when the session last saved or loaded a
    /// project; `None` before either, and after `load_binary`.
    saved: Option<u64>,
}

/// Whether a tool call with these arguments changes what the session holds.
///
/// # Arguments
///
/// * `tool` - The tool's name.
/// * `dry_run` - Its `dry_run` argument, when it has one.
pub(crate) fn changes(tool: &str, dry_run: Option<bool>) -> bool {
    ALWAYS_APPLIED.contains(&tool) || (CHANGING.contains(&tool) && dry_run == Some(false))
}

/// Whether an answer showed fewer rows than it had: a `showing N of M`
/// with `N` below `M`, or a line naming the next page
/// ([`borer_engine::table::next_page`]).
///
/// # Arguments
///
/// * `text` - The answer.
pub(crate) fn shows_fewer(text: &str) -> bool {
    let number = |s: &str| -> Option<(usize, usize)> {
        let digits = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
        Some((s.get(..digits)?.parse().ok()?, digits))
    };
    text.contains(" for the next page\n")
        || text.match_indices("showing ").any(|(at, word)| {
            let rest = &text[at + word.len()..];
            number(rest).is_some_and(|(shown, len)| {
                rest[len..]
                    .strip_prefix(" of ")
                    .and_then(number)
                    .is_some_and(|(total, _)| shown < total)
            })
        })
}

/// A line cut to [`LINE_MAX`] characters, `...` where it was cut.
///
/// # Arguments
///
/// * `line` - The line.
fn kept(line: &str) -> String {
    let line = borer_engine::text::one_line(line);
    match line.char_indices().nth(LINE_MAX) {
        Some((cut, _)) => format!("{}...", &line[..cut]),
        None => line,
    }
}

impl Ledger {
    /// Records a change: a load, a save, or an applied name, comment, type
    /// or script.
    ///
    /// # Arguments
    ///
    /// * `tool` - The tool's name.
    /// * `args` - Its arguments as JSON.
    pub(crate) fn changed(&mut self, tool: &str, args: &str) {
        self.changed += 1;
        if self.changes.len() == KEPT {
            self.changes.pop_front();
        }
        self.changes.push_back(kept(&format!("{tool} {args}")));
    }

    /// Records an answer the session gave.
    ///
    /// # Arguments
    ///
    /// * `key` - The request as the answer memory keys it.
    /// * `capped` - Whether the answer showed less than it had.
    /// * `paged` - Whether the request asked for an offset or a limit.
    pub(crate) fn answered(&mut self, key: &str, capped: bool, paged: bool) {
        self.answered += 1;
        self.requests.retain(|r| r.key != key);
        if self.requests.len() == KEPT {
            self.requests.pop_front();
        }
        self.requests.push_back(Request {
            key: key.to_owned(),
            capped,
            paged,
        });
    }

    /// Records the overlay a project was saved or loaded with, or that a
    /// fresh binary has none saved.
    ///
    /// # Arguments
    ///
    /// * `fingerprint` - The overlay's fingerprint, `None` after a load.
    pub(crate) fn saved(&mut self, fingerprint: Option<u64>) {
        self.saved = fingerprint;
    }

    /// Renders the ledger.
    ///
    /// # Arguments
    ///
    /// * `loaded` - What is loaded, a line: the file, its format, its
    ///   functions and packs; `None` before `load_binary`.
    /// * `overlay` - The overlay's counts, a line, and its fingerprint;
    ///   `None` for an empty overlay, which has nothing to save.
    /// * `held` - Whether the answer memory still keeps a request's text.
    ///
    /// # Returns
    ///
    /// The `borer://session` text.
    pub(crate) fn render(
        &self,
        loaded: Option<&str>,
        overlay: (&str, Option<u64>),
        held: impl Fn(&str) -> bool,
    ) -> String {
        let (counts, fingerprint) = overlay;
        let mut out = match loaded {
            Some(what) => format!("# session: {what}\n"),
            None => "# session: no binary loaded; load_binary starts one\n".to_owned(),
        };
        let saved = match (fingerprint, self.saved) {
            (None, _) => "nothing to save",
            (Some(now), Some(then)) if now == then => "as last saved or loaded with a project",
            (Some(_), Some(_)) => "changed since the last save_project or load_project",
            (Some(_), None) => "not saved: save_project keeps it",
        };
        let _ = writeln!(out, "# overlay: {counts}; {saved}");
        let _ = writeln!(
            out,
            "# {} change{} this session, the last {} here, oldest first",
            self.changed,
            if self.changed == 1 { "" } else { "s" },
            self.changes.len()
        );
        for change in &self.changes {
            let _ = writeln!(out, "{change}");
        }
        let _ = writeln!(
            out,
            "# {} answer{} this session, {} distinct requests here, oldest first: held (its text is kept, so since=<tag> answers what changed), capped (it showed less than it had), paged (it asked for an offset or a limit)",
            self.answered,
            if self.answered == 1 { "" } else { "s" },
            self.requests.len()
        );
        for r in &self.requests {
            let request = match r.key.strip_prefix("tool:") {
                Some(call) => call.replacen(':', " ", 1),
                None => r.key.clone(),
            };
            let _ = writeln!(
                out,
                "{:<6} {:<6} {:<5}  {}",
                if held(&r.key) { "held" } else { "-" },
                if r.capped { "capped" } else { "-" },
                if r.paged { "paged" } else { "-" },
                kept(&request)
            );
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::{KEPT, Ledger, changes, shows_fewer};

    /// The ledger lists changes and requests in order, a repeat at its
    /// latest place, the oldest let go past the cap, with the flags each
    /// earned and whether the overlay was saved.
    ///
    /// # Panics
    ///
    /// When a line or a flag differs.
    #[test]
    fn the_ledger_lists_what_the_session_did() {
        let mut l = Ledger::default();
        l.changed("load_binary", r#"{"path":"a.exe"}"#);
        l.answered("tool:decompile:{\"address\":\"f\"}", false, false);
        l.answered("borer://attrs!limit=5", true, true);
        l.answered("tool:decompile:{\"address\":\"f\"}", false, false);
        let text = l.render(Some("a.exe"), ("1 name", Some(7)), |k| {
            k.starts_with("tool:")
        });
        assert!(
            text.starts_with("# session: a.exe\n# overlay: 1 name; not saved"),
            "{text}"
        );
        assert!(
            text.contains("\nload_binary {\"path\":\"a.exe\"}\n"),
            "{text}"
        );
        let rows: Vec<&str> = text.lines().rev().take(2).collect();
        assert_eq!(
            rows[0], "held   -      -      decompile {\"address\":\"f\"}",
            "{text}"
        );
        assert_eq!(
            rows[1], "-      capped paged  borer://attrs!limit=5",
            "{text}"
        );
        assert!(
            text.contains("# 3 answers this session, 2 distinct requests"),
            "{text}"
        );
        l.saved(Some(7));
        assert!(
            l.render(None, ("", Some(7)), |_| false)
                .contains("as last saved")
        );
        assert!(
            l.render(None, ("", Some(8)), |_| false)
                .contains("changed since")
        );
        assert!(
            l.render(None, ("", None), |_| false)
                .contains("nothing to save")
        );
        for n in 0..=KEPT {
            l.answered(&format!("borer://x/{n}"), false, false);
        }
        let text = l.render(None, ("", None), |_| false);
        assert!(
            !text.contains("borer://x/0\n") && text.contains("borer://x/64\n"),
            "{text}"
        );
    }

    /// A dry run changes nothing, a load always does, and `showing N of M`
    /// is capped only when `N` is below `M`.
    ///
    /// # Panics
    ///
    /// When a call or an answer is misjudged.
    #[test]
    fn changes_and_caps_are_told_apart() {
        assert!(changes("load_binary", None));
        assert!(changes("set_name", Some(false)));
        assert!(!changes("set_name", None));
        assert!(!changes("set_name", Some(true)));
        assert!(!changes("decompile", Some(false)));
        assert!(shows_fewer("# showing 5 of 459 functions"));
        assert!(!shows_fewer("# showing 7 of 7 from 0"));
        assert!(!shows_fewer("# 351 sites, showing 351 from 0"));
        assert!(shows_fewer(
            "# 351 sites, showing 2 from 0\n# 349 more; borer://x!offset=2 for the next page\n"
        ));
    }
}
