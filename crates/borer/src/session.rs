//! The session ledger behind `borer://session`: what this session loaded,
//! named, commented and typed, and the answers it was given.
//!
//! An agent's context does not outlive a compaction or a new chat, and the
//! session does: after either, the agent re-ran the triage and decompiled
//! again what it had already read. The ledger answers "where was I" in one
//! read. It holds the last [`KEPT`] changes, the last [`KEPT`] distinct
//! requests and the last [`EVIDENCE_KEPT`] answers in the order they came,
//! and nothing else, so the same calls give the same text: no clock, no
//! randomness.

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

/// The answers this session gave, kept by the evidence id each carries, so
/// `borer://session/evidence/<id>` answers with the text an agent cites.
///
/// Only the id travels with an answer (one line, whatever the answer's
/// size); the text stays here, the last [`EVIDENCE_KEPT`] of it, oldest
/// out first.
#[derive(Debug, Default)]
pub(crate) struct Evidence {
    /// The last [`EVIDENCE_KEPT`] answers, oldest first: id → text as sent.
    kept: VecDeque<(String, String)>,
    /// Evidence minted in all, kept or not.
    minted: u64,
}

/// What an evidence id names.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Answer {
    /// The answer as sent, its evidence line last.
    Kept(String),
    /// An answer this session gave and let go past [`EVIDENCE_KEPT`].
    LetGo,
}

/// Most answers the evidence keeps; the oldest go first.
pub(crate) const EVIDENCE_KEPT: usize = 256;

/// A number in base 36, digits `0-9` then `a-z`, as an evidence id spells
/// its counter.
///
/// # Arguments
///
/// * `n` - The number.
fn base36(n: u64) -> String {
    /// The digits in order.
    const DIGITS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";
    let mut digits: Vec<char> = Vec::new();
    let mut n = n;
    loop {
        digits.push(char::from(
            DIGITS[borer_engine::num::saturating_usize(n % 36)],
        ));
        n /= 36;
        if n == 0 {
            break;
        }
    }
    digits.reverse();
    digits.into_iter().collect()
}

/// The counter half of an evidence id, when the id reads as one: base 36
/// digits, a dash, then eight hex digits.
///
/// # Arguments
///
/// * `id` - The id as a `# evidence:` line words it.
///
/// # Returns
///
/// The counter the id's first half spells; `None` for any other shape.
fn parse_id(id: &str) -> Option<u64> {
    let (counter, digest) = id.split_once('-')?;
    u64::from_str_radix(counter, 36)
        .ok()
        .filter(|_| digest.len() == 8 && digest.chars().all(|d| d.is_ascii_hexdigit()))
}

impl Evidence {
    /// Returns the evidence line naming this answer, and keeps the answer
    /// behind its id.
    ///
    /// The id is `<n>-<digest>`: this session's emission count in base 36,
    /// then the low 32 bits of the answer's FNV-1a hash as eight hex
    /// digits. The counter says which emission, the digest which text, so
    /// an identical answer minted again takes the same digest under a new
    /// counter; a reader cites the whole id. The line carries the mark a
    /// mermaid graph needs to keep parsing ([`crate::recall::mermaid`]).
    ///
    /// # Arguments
    ///
    /// * `text` - The answer as sent, ending in a newline, its evidence
    ///   line the only thing left to add.
    fn line(&mut self, text: &str) -> String {
        self.minted += 1;
        let digest =
            borer_engine::num::lo32(borer::index::fnv1a(borer::index::FNV_SEED, text.as_bytes()));
        let id = format!("{}-{:08x}", base36(self.minted), digest);
        if self.kept.len() == EVIDENCE_KEPT {
            self.kept.pop_front();
        }
        let line = format!(
            "{} evidence: {id}\n",
            if crate::recall::mermaid(text) {
                "%%"
            } else {
                "#"
            }
        );
        self.kept.push_back((id, format!("{text}{line}")));
        line
    }

    /// Returns what an evidence id names.
    ///
    /// # Arguments
    ///
    /// * `id` - The id from a `# evidence:` line.
    ///
    /// # Returns
    ///
    /// `Ok` with the answer as sent, or [`Answer::LetGo`] when it was let
    /// go past [`EVIDENCE_KEPT`].
    ///
    /// # Errors
    ///
    /// When the id is not `<n>-<8 hex digits>`, or names an emission the
    /// session never made; the message says the form an id takes.
    fn answer(&self, id: &str) -> Result<Answer, String> {
        let Some(counter) = parse_id(id) else {
            return Err(format!(
                "evidence {} is not an id; pass the <n>-<8 hex digits> a `# evidence:` line carries",
                borer_engine::text::quoted(id)
            ));
        };
        if let Some((_, text)) = self.kept.iter().find(|(kept, _)| kept == id) {
            return Ok(Answer::Kept(text.clone()));
        }
        if counter <= self.minted {
            return Ok(Answer::LetGo);
        }
        Err(format!(
            "evidence {} names no answer this session gave; the newest is {}",
            borer_engine::text::quoted(id),
            base36(self.minted)
        ))
    }
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
    /// The answers this session gave, by the evidence id each carries.
    evidence: Evidence,
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

    /// Returns the evidence line for an answer on its way out, and keeps
    /// the answer behind its id for `borer://session/evidence/<id>`.
    ///
    /// # Arguments
    ///
    /// * `text` - The answer as sent, ending in a newline.
    pub(crate) fn evidence_line(&mut self, text: &str) -> String {
        self.evidence.line(text)
    }

    /// Returns what an evidence id names: the answer as sent, notice that
    /// it was let go, or `Err` when no `# evidence:` line ever carried the
    /// id.
    ///
    /// # Arguments
    ///
    /// * `id` - The id from a `# evidence:` line.
    ///
    /// # Errors
    ///
    /// When the id is not `<n>-<8 hex digits>`, or names an emission the
    /// session never made; the message says the form an id takes.
    pub(crate) fn evidence(&self, id: &str) -> Result<Answer, String> {
        self.evidence.answer(id)
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
    use super::{EVIDENCE_KEPT, KEPT, Ledger, changes, shows_fewer};

    /// The digest half of an evidence id, as [`Evidence::line`] computes it.
    fn digest(text: &str) -> String {
        format!(
            "{:08x}",
            borer_engine::num::lo32(borer::index::fnv1a(borer::index::FNV_SEED, text.as_bytes(),))
        )
    }

    /// The evidence line names each answer: the counter per emission, the
    /// digest per text.
    ///
    /// So the same text minted again differs only in its counter; the id
    /// returns the answer as it was sent, past the cap the oldest is let
    /// go, and an id the session never minted is refused.
    ///
    /// # Panics
    ///
    /// When a line, an id or an answer differs.
    #[test]
    fn evidence_names_each_answer_and_returns_it() {
        let mut l = Ledger::default();
        let one = l.evidence_line("one\n");
        assert_eq!(one, format!("# evidence: 1-{}\n", digest("one\n")));
        let again = l.evidence_line("one\n");
        assert_eq!(
            again,
            format!("# evidence: 2-{}\n", digest("one\n")),
            "the same text keeps its digest under a new counter"
        );
        let id = format!("2-{}", digest("one\n"));
        assert_eq!(
            l.evidence(&id),
            Ok(super::Answer::Kept(format!("one\n{again}"))),
            "the id returns the answer as it was sent"
        );
        assert_eq!(
            l.evidence("x"),
            Err("evidence 'x' is not an id; pass the <n>-<8 hex digits> a `# evidence:` line carries".to_owned())
        );
        assert_eq!(
            l.evidence("9-00000000"),
            Err(
                "evidence '9-00000000' names no answer this session gave; the newest is 2"
                    .to_owned()
            )
        );
        assert_eq!(l.evidence("2-0000000z"), Err("evidence '2-0000000z' is not an id; pass the <n>-<8 hex digits> a `# evidence:` line carries".to_owned()));
    }

    /// Past the cap the oldest answer is let go, and its id says so rather
    /// than returning a text the session no longer has.
    ///
    /// # Panics
    ///
    /// When the wrong answer is let go, or one kept.
    #[test]
    fn evidence_lets_the_oldest_answer_go_past_the_cap() {
        let mut l = Ledger::default();
        let first = l.evidence_line("first\n");
        let id = format!("1-{}", digest("first\n"));
        assert_eq!(
            l.evidence(&id),
            Ok(super::Answer::Kept(format!("first\n{first}")))
        );
        for n in 0..EVIDENCE_KEPT {
            l.evidence_line(&format!("answer {n}\n"));
        }
        assert_eq!(l.evidence(&id), Ok(super::Answer::LetGo));
        let last = format!(
            "{}-{}",
            super::base36(u64::try_from(EVIDENCE_KEPT).expect("fits a u64") + 1),
            digest("answer 255\n")
        );
        assert_eq!(
            l.evidence(&last),
            Ok(super::Answer::Kept(format!(
                "answer 255\n# evidence: {last}\n"
            )))
        );
    }

    /// A mermaid answer carries its evidence as a `%%` comment, so the
    /// whole answer still parses as a diagram, and base 36 spells past nine.
    ///
    /// # Panics
    ///
    /// When a line is not a comment or a number is misspelled.
    #[test]
    fn a_mermaid_answer_and_base_36() {
        let mut l = Ledger::default();
        let graph = "graph TD\n  a\n".to_owned();
        let line = l.evidence_line(&graph);
        assert!(line.starts_with("%% evidence: 1-"), "{line}");
        assert_eq!(super::base36(0), "0");
        assert_eq!(super::base36(9), "9");
        assert_eq!(super::base36(10), "a");
        assert_eq!(super::base36(35), "z");
        assert_eq!(super::base36(36), "10");
    }

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
