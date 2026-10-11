//! The tag a long answer carries, what a reader holding it is sent
//! instead of the text, and the byte budget every answer is cut to.
//!
//! An agent re-reads: after a detour it asks for the function it already
//! has, and a decompile or a table costs it thousands of tokens each time.
//! A long answer ends with a `# since=<tag>` line (`%% since=<tag>` after
//! a mermaid graph, so it stays one); the same request with
//! the tag passed back ([`SINCE_ARG`] on a tool call, [`SINCE_SUFFIX`] on a
//! resource URI) is answered by a one-line note when nothing changed, or by
//! the lines that differ ([`Recall`]). [`budgeted`] caps what goes out.

use std::collections::HashMap;
use std::fmt::Write as _;

/// Answers shorter than this carry no tag and are sent whole every time: a
/// note in their place would save nothing.
const RECALL_MIN: usize = 512;
/// Environment variable capping every answer at this many bytes, cut at a
/// line with a note saying how to get the rest; unset for no cap.
const BUDGET_ENV: &str = "BORER_BUDGET";
/// The tool argument that passes back the tag of the answer the reader
/// holds; the server takes it off before the tool sees its arguments.
pub(crate) const SINCE_ARG: &str = "since";
/// What a resource URI ends with, before a tag, to pass back the tag of the
/// answer the reader holds.
pub(crate) const SINCE_SUFFIX: &str = "!since=";
/// The suffix of a resource URI that asks for the text whole, as a URI
/// without a tag gets it.
pub(crate) const FRESH_SUFFIX: &str = "!fresh";

/// The tag of an answer: the low 32 bits of its FNV-1a hash, printed as
/// eight hex digits.
///
/// A reader passes it back to say which text it holds; a different text of
/// the same request takes the tag with odds of one in four billion, and the
/// tag costs a reader a few tokens on every long answer, so 32 bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Tag(u32);

impl Tag {
    /// Returns the tag of `text`.
    ///
    /// # Arguments
    ///
    /// * `text` - The whole answer, without its tag line.
    fn of(text: &str) -> Self {
        Self(borer_engine::num::lo32(borer::index::fnv1a(
            borer::index::FNV_SEED,
            text.as_bytes(),
        )))
    }

    /// Reads a tag a reader passed back, as the `# since=` line prints it.
    ///
    /// # Arguments
    ///
    /// * `text` - The tag: up to eight hex digits.
    ///
    /// # Errors
    ///
    /// When the text is not one to eight hex digits, with the form it must
    /// take.
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        let digits = text.trim();
        (1..=8)
            .contains(&digits.len())
            .then(|| u32::from_str_radix(digits, 16).ok())
            .flatten()
            .map(Self)
            .ok_or_else(|| {
                format!(
                    "since={text:?} is not a tag; pass the eight hex digits of a `# since=` line, or leave it out for the whole answer"
                )
            })
    }
}

impl std::fmt::Display for Tag {
    /// Writes the tag as eight hex digits.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter.
    ///
    /// # Errors
    ///
    /// When the formatter does.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:08x}", self.0)
    }
}

/// Puts a tag on a resource URI where a URI reader takes it off.
///
/// The tag goes before a trailing [`FRESH_SUFFIX`], and in place of a
/// [`SINCE_SUFFIX`] tag the URI already carries, so the tag passed beside
/// the URI is the one read. Appended after either suffix, the tag left the
/// suffix inside the URI, which then named no resource.
///
/// # Arguments
///
/// * `uri` - The URI as the reader wrote it, with or without either suffix.
/// * `tag` - The tag of the answer the reader holds.
///
/// # Returns
///
/// The URI with the tag in the place a URI's own tag goes.
pub(crate) fn tagged_uri(uri: &str, tag: Tag) -> String {
    let (core, fresh) = uri
        .strip_suffix(FRESH_SUFFIX)
        .map_or((uri, ""), |core| (core, FRESH_SUFFIX));
    let core = core
        .rsplit_once(SINCE_SUFFIX)
        .map_or(core, |(core, _)| core);
    format!("{core}{SINCE_SUFFIX}{tag}{fresh}")
}

/// The text a reader may hold for each request, so a reader that says it
/// holds it can be sent a note or the lines that changed instead.
///
/// Only the reader knows what its context still holds. A second agent
/// sharing the session, or one whose context was summarized, asks again for
/// a text the session sent before and no longer has it, and a note in its
/// place hides the text from it. So the server never decides that a reader
/// has a text: every answer goes out whole with its [`Tag`], and only a
/// request that passes a tag back gets less. A reader without the text has
/// no tag to pass. A tag equal to the answer's own needs no memory at all
/// (the note survives a reload); the lines that changed need the text the
/// tag names, kept here per request: the last one sent whole, which a delta
/// leaves in place, so a reader holding it can be sent the delta again.
/// The texts kept stay within [`TEXTS_BUDGET`], the least recently asked
/// let go first; a reader passing the tag of a text let go is sent the
/// answer whole, as a reader without a tag is, so nothing is lost but the
/// saving.
#[derive(Debug, Default)]
pub(crate) struct Recall {
    /// Per request: the last answer sent whole, when short enough to diff
    /// the next one against.
    texts: HashMap<String, Held>,
    /// Bytes of text in `texts`.
    bytes: usize,
    /// Answers given so far: the order `texts` were last asked in.
    asked: u64,
}

/// One answer kept to diff the next one against.
#[derive(Debug)]
struct Held {
    /// Its tag.
    tag: Tag,
    /// The answer as sent whole.
    text: String,
    /// When it was last asked, as [`Recall::asked`] counts.
    used: u64,
}

/// Most bytes of answers [`Recall`] keeps. A session sweeping a whole
/// binary once held 83 MB of answers it would never diff against; a reader
/// passes back tags of what it read lately.
const TEXTS_BUDGET: usize = 32 << 20;

/// Longest answer kept to diff the next one against.
const DELTA_TEXT_MAX: usize = 1 << 20;
/// Most edits a delta is computed for; past that the answer goes whole.
const DELTA_EDITS_MAX: usize = 1_000;
/// A delta goes out only when it is at most this share of the whole
/// answer, as `num / den`.
const DELTA_SHARE: (usize, usize) = (1, 2);

/// The lines of `new` that differ from `old`, as `@@ -a,n +b,m @@` hunks.
///
/// The hunks come from the shortest edit script (Myers); `None` when it
/// takes more than [`DELTA_EDITS_MAX`] edits. They are numbered as a
/// unified diff numbers them: a range of lines by its first line, an empty
/// range by the line before it, so a line added after old line 4 is
/// `-4,0`, where it read `-5,0` and a reader applying the hunk the way
/// `patch` does put it one line late.
///
/// # Arguments
///
/// * `old` - The answer sent last time.
/// * `new` - The answer now.
fn line_delta(old: &str, new: &str) -> Option<String> {
    let a: Vec<&str> = old.lines().collect();
    let b: Vec<&str> = new.lines().collect();
    let (n, m) = (a.len(), b.len());
    let n_i = isize::try_from(n).ok()?;
    let m_i = isize::try_from(m).ok()?;
    let reach = isize::try_from(DELTA_EDITS_MAX).ok()? + 1;
    let width = usize::try_from(2 * reach + 1).ok()?;
    let index = |k: isize| usize::try_from(k + reach).ok();
    let mut v = vec![0isize; width];
    let mut trace: Vec<Vec<isize>> = Vec::new();
    let mut done = false;
    for d in 0..=isize::try_from(DELTA_EDITS_MAX).ok()? {
        trace.push(v.clone());
        let mut k = -d;
        while k <= d {
            let down = k == -d || (k != d && v[index(k - 1)?] < v[index(k + 1)?]);
            let mut x = if down {
                v[index(k + 1)?]
            } else {
                v[index(k - 1)?] + 1
            };
            let mut y = x - k;
            while x < n_i && y < m_i && a[usize::try_from(x).ok()?] == b[usize::try_from(y).ok()?] {
                x += 1;
                y += 1;
            }
            v[index(k)?] = x;
            if x >= n_i && y >= m_i {
                done = true;
                break;
            }
            k += 2;
        }
        if done {
            break;
        }
    }
    if !done {
        return None;
    }
    let mut edits: Vec<(bool, usize, usize)> = Vec::new();
    let (mut x, mut y) = (n_i, m_i);
    for (d, vd) in trace.iter().enumerate().rev() {
        let d = isize::try_from(d).ok()?;
        let k = x - y;
        let down = k == -d || (k != d && vd[index(k - 1)?] < vd[index(k + 1)?]);
        let prev_k = if down { k + 1 } else { k - 1 };
        let prev_x = vd[index(prev_k)?];
        let prev_y = prev_x - prev_k;
        while x > prev_x && y > prev_y {
            x -= 1;
            y -= 1;
        }
        if d > 0 {
            edits.push((
                x == prev_x,
                usize::try_from(prev_x).ok()?,
                usize::try_from(prev_y).ok()?,
            ));
        }
        x = prev_x;
        y = prev_y;
    }
    edits.reverse();
    let mut out = String::new();
    let mut i = 0;
    while i < edits.len() {
        let (_, x0, y0) = edits[i];
        let (mut cx, mut cy) = (x0, y0);
        let mut removed: Vec<&str> = Vec::new();
        let mut added: Vec<&str> = Vec::new();
        while i < edits.len() && (edits[i].1, edits[i].2) == (cx, cy) {
            let (insert, ex, ey) = edits[i];
            if insert {
                added.push(b.get(ey)?);
                cy += 1;
            } else {
                removed.push(a.get(ex)?);
                cx += 1;
            }
            i += 1;
        }
        // SPEC: GNU diffutils manual, "Detailed Unified": an empty range names the line before it.
        let start = |at: usize, lines: &[&str]| if lines.is_empty() { at } else { at + 1 };
        let _ = writeln!(
            out,
            "@@ -{},{} +{},{} @@",
            start(x0, &removed),
            removed.len(),
            start(y0, &added),
            added.len()
        );
        for line in removed {
            let _ = writeln!(out, "-{line}");
        }
        for line in added {
            let _ = writeln!(out, "+{line}");
        }
    }
    Some(out)
}

impl Recall {
    /// The answer to send for `request`: `text` with its tag line, a note
    /// when `since` is the tag of `text`, or the lines that changed when
    /// `since` is the tag of the text last sent whole and the two differ by
    /// little.
    ///
    /// A note or a delta stands in for the text, so it names the way to get
    /// the text whole: `again`, the request without the tag.
    ///
    /// # Arguments
    ///
    /// * `request` - The request without the tag, as a stable key.
    /// * `since` - The tag the reader passed back, if any.
    /// * `again` - How to ask for the text whole, as the note words it:
    ///   `calling decompile {"address":"f"}`.
    /// * `text` - The full answer.
    pub(crate) fn answer(
        &mut self,
        request: &str,
        since: Option<Tag>,
        again: &str,
        mut text: String,
    ) -> String {
        if text.len() < RECALL_MIN {
            return text;
        }
        let tag = Tag::of(&text);
        if since == Some(tag) {
            return format!(
                "# unchanged since the answer tagged {tag}: {} lines, {} bytes; this note stands in for that text, and {again} returns it in full\n",
                text.lines().count(),
                text.len()
            );
        }
        self.asked += 1;
        let asked = self.asked;
        if let Some(held) = self.texts.get_mut(request)
            && since == Some(held.tag)
            && let Some(d) = line_delta(&held.text, &text)
                .filter(|d| d.len() * DELTA_SHARE.1 <= text.len() * DELTA_SHARE.0)
        {
            held.used = asked;
            return format!(
                "# changed since the answer tagged {}: {} lines, {} bytes now; the lines that differ from that answer follow, and {again} returns it in full\n{d}",
                held.tag,
                text.lines().count(),
                text.len()
            );
        }
        if let Some(old) = self.texts.remove(request) {
            self.bytes -= old.text.len();
        }
        if text.len() <= DELTA_TEXT_MAX {
            self.bytes += text.len();
            self.texts.insert(
                request.to_owned(),
                Held {
                    tag,
                    text: text.clone(),
                    used: asked,
                },
            );
            self.keep_within(TEXTS_BUDGET);
        }
        if !text.ends_with('\n') {
            text.push('\n');
        }
        let mark = if mermaid(&text) { "%%" } else { "#" };
        let _ = writeln!(text, "{mark} {SINCE_ARG}={tag}");
        text
    }
}

/// Whether an answer is a mermaid graph, whose tag line must be a `%%`
/// comment for the answer to parse as a diagram.
///
/// # Arguments
///
/// * `text` - The answer.
///
/// # Returns
///
/// `true` when its first line that is not a `%%` comment opens a `graph`.
fn mermaid(text: &str) -> bool {
    text.lines()
        .find(|l| !l.starts_with("%%"))
        .is_some_and(|l| l.starts_with("graph "))
}

impl Recall {
    /// Lets go of the least recently asked texts until those kept fit in
    /// three quarters of `budget`, once they no longer fit in all of it.
    ///
    /// # Arguments
    ///
    /// * `budget` - Most bytes of text to keep.
    fn keep_within(&mut self, budget: usize) {
        if self.bytes <= budget {
            return;
        }
        let mut by_use: Vec<(u64, String)> = self
            .texts
            .iter()
            .map(|(request, held)| (held.used, request.clone()))
            .collect();
        by_use.sort_unstable();
        let target = budget / 4 * 3;
        for (_, request) in by_use {
            if self.bytes <= target {
                break;
            }
            if let Some(held) = self.texts.remove(&request) {
                self.bytes -= held.text.len();
            }
        }
    }
}

/// How the reader of an answer asks for less of it, for the note under a
/// cut.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Narrow {
    /// A tool call, which takes a filter, an offset and a limit.
    Tool,
    /// A resource URI, which takes no paging: only what the URI names.
    Uri,
}

/// Caps an answer at the byte budget `BORER_BUDGET` sets, cut at the last
/// line that fits, with a note on what was left out ([`cut_to`]).
///
/// # Arguments
///
/// * `text` - The answer.
/// * `narrow` - How its reader asks for less.
pub(crate) fn budgeted(text: String, narrow: Narrow) -> String {
    match std::env::var(BUDGET_ENV)
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&b| b > 0)
    {
        Some(budget) => cut_to(text, budget, narrow),
        None => text,
    }
}

/// Cuts an answer to `budget` bytes at the last whole line, with a note on
/// what was left out; an answer within the budget is kept whole.
///
/// The answer's `# since=` (or `%% since=`) line stays last, since the
/// reader passes it back to be told nothing changed: the cut took it with
/// the rest of the tail. The note says how this reader narrows: a URI has
/// no offset to page with, and the note told a resource reader to use one.
///
/// # Arguments
///
/// * `text` - The answer.
/// * `budget` - Most bytes kept, the tag line included.
/// * `narrow` - How its reader asks for less.
fn cut_to(text: String, budget: usize, narrow: Narrow) -> String {
    if text.len() <= budget {
        return text;
    }
    let last_at = text.trim_end_matches('\n').rfind('\n').map_or(0, |i| i + 1);
    let last = &text[last_at..];
    let (body, tag, mark) = if last.starts_with("# since=") {
        (&text[..last_at], last, "#")
    } else if last.starts_with("%% since=") {
        (&text[..last_at], last, "%%")
    } else {
        (text.as_str(), "", "#")
    };
    let mut end = budget.saturating_sub(tag.len()).min(body.len());
    while !body.is_char_boundary(end) {
        end -= 1;
    }
    let cut = body[..end].rfind('\n').map_or(0, |i| i + 1);
    let kept = body[..cut].lines().count();
    let total = body.lines().count();
    let how = match narrow {
        Narrow::Tool => "narrow with a filter or page with an offset",
        Narrow::Uri => "narrow the URI, by its filter where the resource takes one",
    };
    format!(
        "{}{mark} cut at {cut} of {} bytes ({kept} of {total} lines) by {BUDGET_ENV}; {how}\n{tag}",
        &body[..cut],
        text.len()
    )
}

#[cfg(test)]
mod tests {
    use super::{Narrow, Recall, Tag};

    /// How the tests word the request that returns a text whole.
    const AGAIN: &str = "calling f {}";

    /// The tag on the last line of a whole answer.
    ///
    /// # Arguments
    ///
    /// * `whole` - An answer sent whole.
    ///
    /// # Panics
    ///
    /// When the answer does not end with a tag line.
    fn tag_line(whole: &str) -> Tag {
        let line = whole.lines().last().expect("an answer has lines");
        let digits = line.strip_prefix("# since=").expect("a tag line ends it");
        Tag::parse(digits).expect("the tag line reads back")
    }

    /// A long mermaid graph carries its tag as a `%%` comment, so the
    /// whole answer still parses as a diagram; other answers keep `#`.
    ///
    /// # Panics
    ///
    /// When a graph's tag line is not a mermaid comment.
    #[test]
    fn a_mermaid_answer_carries_its_tag_as_a_comment() {
        let mut r = Recall::default();
        let graph: String = std::iter::once("graph TD\n".to_owned())
            .chain((0..60).map(|i| format!("  n{i}[\"sub_{i:x}\"]\n")))
            .collect();
        let sent = r.answer("g", None, AGAIN, graph);
        let last = sent.lines().last().unwrap_or_default();
        assert!(last.starts_with("%% since="), "{sent}");
        let capped = format!(
            "%% max_nodes 200 capped at 100\n{}",
            "graph TD\n".repeat(60)
        );
        assert!(
            r.answer("h", None, AGAIN, capped)
                .lines()
                .last()
                .unwrap_or_default()
                .starts_with("%% since=")
        );
        let table = "# rows\n".repeat(100);
        assert!(tag_line(&r.answer("t", None, AGAIN, table)) != Tag::of(""));
    }

    /// A long answer goes out whole with its tag to every request passing
    /// no tag, however often the session sent it before.
    ///
    /// A second agent sharing the session, or one whose context was
    /// summarized, is never handed a note for a text it no longer holds.
    /// Only the reader passing the answer's own tag back gets the note,
    /// which says it stands in for that text and names the request that
    /// returns it; a stale or foreign tag gets the text. A short answer is
    /// whole and untagged whatever is passed.
    ///
    /// # Panics
    ///
    /// When an answer differs.
    #[test]
    fn only_a_reader_holding_the_tag_gets_a_note() {
        let mut r = Recall::default();
        let long = "x\n".repeat(400);
        let whole = format!("{long}# since=e33afea5\n");
        assert_eq!(r.answer("k", None, AGAIN, long.clone()), whole);
        assert_eq!(
            r.answer("k", None, AGAIN, long.clone()),
            whole,
            "a reader passing no tag gets the text again"
        );
        let tag = tag_line(&whole);
        assert_eq!(
            r.answer("k", Some(tag), AGAIN, long.clone()),
            "# unchanged since the answer tagged e33afea5: 400 lines, 800 bytes; this note stands in for that text, and calling f {} returns it in full\n"
        );
        let foreign = Tag::parse("1234").expect("a tag");
        assert_eq!(r.answer("k", Some(foreign), AGAIN, long.clone()), whole);
        let mut fresh = Recall::default();
        assert!(
            fresh
                .answer("k", Some(tag), AGAIN, long)
                .starts_with("# unchanged since the answer tagged e33afea5"),
            "the tag alone says the text is unchanged, with nothing remembered"
        );
        assert_eq!(r.answer("short", Some(tag), AGAIN, "a".to_owned()), "a");
        assert!(Tag::parse("").is_err() && Tag::parse("123456789").is_err());
        assert!(Tag::parse("e33afeg5").is_err());
    }

    /// A changed answer goes to the reader holding the old one's tag as the
    /// lines that differ, placed where they sit.
    ///
    /// It does as often as the reader asks with that tag; once a whole text
    /// has gone out since, the old tag gets the text and the new one the
    /// note.
    ///
    /// # Panics
    ///
    /// When a delta differs from the change, or an answer is not the one
    /// the tag passed calls for.
    #[test]
    fn a_changed_answer_is_sent_as_its_delta() {
        let old = "a\nb\nc\nd\n";
        let new = "a\nB\nc\nd\ne\n";
        assert_eq!(
            super::line_delta(old, new).as_deref(),
            Some("@@ -2,1 +2,1 @@\n-b\n+B\n@@ -4,0 +5,1 @@\n+e\n")
        );
        assert_eq!(
            super::line_delta(old, "a\nc\nd\n").as_deref(),
            Some("@@ -2,1 +1,0 @@\n-b\n"),
            "an empty range is named by the line before it, as in a unified diff"
        );
        assert_eq!(super::line_delta(old, old).as_deref(), Some(""));
        let mut r = Recall::default();
        let body: String = (0..300).map(|i| format!("line {i}\n")).collect();
        let held = tag_line(&r.answer("k", None, AGAIN, body.clone()));
        let renamed = body.replace("line 150", "renamed 150");
        let sent = r.answer("k", Some(held), AGAIN, renamed.clone());
        assert!(
            sent.starts_with(&format!("# changed since the answer tagged {held}: ")),
            "{sent}"
        );
        assert!(
            sent.contains("; the lines that differ from that answer follow, and calling f {} returns it in full\n"),
            "{sent}"
        );
        assert!(sent.contains("-line 150\n+renamed 150\n"), "{sent}");
        assert_eq!(r.answer("k", Some(held), AGAIN, renamed.clone()), sent);
        let whole = r.answer("k", None, AGAIN, renamed.clone());
        assert!(whole.starts_with("line 0\n"), "{whole}");
        let now = tag_line(&whole);
        assert!(
            r.answer("k", Some(now), AGAIN, renamed.clone())
                .starts_with("# unchanged since")
        );
        assert_eq!(r.answer("k", Some(held), AGAIN, renamed), whole);
    }

    /// The texts kept to diff against stay within a byte budget, least
    /// recently asked first out.
    ///
    /// A reader passing the tag of a text let go is sent the answer whole:
    /// the saving goes, never the answer.
    ///
    /// # Panics
    ///
    /// When the budget is passed, the wrong text is let go, or a request
    /// whose text was let go gets anything but the whole answer.
    #[test]
    fn the_texts_kept_stay_within_a_budget() {
        let mut r = Recall::default();
        let body = |k: usize| -> String { (0..100).map(|i| format!("line {k} {i}\n")).collect() };
        let first = tag_line(&r.answer("a", None, AGAIN, body(0)));
        let b_tag = tag_line(&r.answer("b", None, AGAIN, body(1)));
        let one = r.bytes / 2;
        let _ = r.answer("c", None, AGAIN, body(2));
        // Three texts over a budget of just under three: down to three
        // quarters of it lets go of exactly one, the least recently asked.
        let budget = 3 * one - 1;
        r.keep_within(budget);
        assert!(r.bytes <= budget / 4 * 3, "{} > {budget}", r.bytes);
        assert_eq!(r.texts.len(), 2, "only one text goes");
        assert!(
            !r.texts.contains_key("a"),
            "the least recently asked goes first"
        );
        let whole = r.answer(
            "a",
            Some(first),
            AGAIN,
            body(0).replace("line 0 50\n", "renamed\n"),
        );
        assert!(whole.starts_with("line 0 0\n"), "{whole}");
        let delta = r.answer(
            "b",
            Some(b_tag),
            AGAIN,
            body(1).replace("line 1 50\n", "renamed\n"),
        );
        assert!(delta.starts_with("# changed since"), "{delta}");
    }

    /// An answer over the budget is cut at its last whole line with a note;
    /// one within it is kept.
    ///
    /// # Panics
    ///
    /// When the cut differs.
    #[test]
    fn an_answer_is_cut_at_a_line_within_the_budget() {
        let text = "one\ntwo\nthree\n".to_owned();
        assert_eq!(super::cut_to(text.clone(), 100, Narrow::Tool), text);
        let cut = super::cut_to(text, 9, Narrow::Tool);
        assert!(
            cut.starts_with("one\ntwo\n# cut at 8 of 14 bytes (2 of 3 lines)"),
            "{cut}"
        );
    }

    /// A cut keeps the answer's tag line last, so the reader can still pass
    /// it back, and tells a resource reader to narrow the URI: a URI takes
    /// no offset.
    ///
    /// # Panics
    ///
    /// When the tag line is lost or a URI reader is told to page.
    #[test]
    fn a_cut_keeps_the_tag_and_words_its_note_for_the_reader() {
        let text = "one\ntwo\nthree\n# since=0000beef\n".to_owned();
        let cut = super::cut_to(text, 30, Narrow::Uri);
        assert_eq!(
            cut,
            "one\ntwo\n# cut at 8 of 31 bytes (2 of 3 lines) by BORER_BUDGET; narrow the URI, by its filter where the resource takes one\n# since=0000beef\n"
        );
        let graph = "graph TD\n  a\n  b\n%% since=0000beef\n".to_owned();
        let cut = super::cut_to(graph, 30, Narrow::Tool);
        assert!(cut.starts_with("graph TD\n%% cut at 9 of "), "{cut}");
        assert!(cut.ends_with("\n%% since=0000beef\n"), "{cut}");
    }

    /// A `since` passed beside a `query` URI goes where a URI's own tag
    /// goes: before `!fresh`, and in place of a tag the URI carries.
    ///
    /// Appended after either, it left `!fresh` or the first tag inside the
    /// URI, which then named no resource.
    ///
    /// # Panics
    ///
    /// When a tagged URI differs.
    #[test]
    fn a_tag_goes_where_a_uri_reader_takes_it_off() {
        let tag = Tag::parse("1234abcd").expect("a tag");
        for (uri, tagged) in [
            ("borer://qt", "borer://qt!since=1234abcd"),
            ("borer://qt!fresh", "borer://qt!since=1234abcd!fresh"),
            ("borer://qt!since=0000beef", "borer://qt!since=1234abcd"),
            (
                "borer://qt!since=0000beef!fresh",
                "borer://qt!since=1234abcd!fresh",
            ),
        ] {
            assert_eq!(super::tagged_uri(uri, tag), tagged, "{uri}");
        }
    }
}
