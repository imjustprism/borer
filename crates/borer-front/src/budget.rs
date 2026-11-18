//! The byte budget every answer is cut to, shared by the MCP server and the app's chat so an
//! agent and a model in the chat get the same cut, with the same note on how to page.
//!
//! The budget is read from the environment (`BORER_BUDGET`) the same way by both.

/// Environment variable capping every answer at this many bytes, cut at a
/// line with a note saying how to get the rest; unset for
/// [`BUDGET_DEFAULT`], `0` for no cap.
const BUDGET_ENV: &str = "BORER_BUDGET";
/// The byte budget when `BORER_BUDGET` sets none.
///
/// It is under the 25,000 tokens Claude Code takes from one MCP answer,
/// at about three bytes a token of pseudo-C, so a whole `decompile` of a
/// huge function is cut with a note rather than refused whole by the host.
pub const BUDGET_DEFAULT: usize = 72_000;

/// How the reader of an answer asks for less of it, for the note under a
/// cut.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Narrow {
    /// A tool call, which takes a filter, an offset and a limit.
    Tool,
    /// A resource URI, which pages a listing by `!offset=` and `!limit=`
    /// and narrows by its filter where the resource takes one.
    Uri,
}

/// Caps an answer at the byte budget `BORER_BUDGET` sets, cut at the last
/// line that fits, with a note on what was left out ([`cut_to`]).
///
/// # Arguments
///
/// * `text` - The answer.
/// * `narrow` - How its reader asks for less.
pub fn budgeted(text: String, narrow: Narrow) -> String {
    match budget() {
        Some(budget) => cut_to(text, budget, narrow),
        None => text,
    }
}

/// Returns the byte budget `BORER_BUDGET` sets ([`budget_of`]), `None` for no cap.
#[must_use]
pub fn budget() -> Option<usize> {
    budget_of(std::env::var(BUDGET_ENV).ok().as_deref())
}

/// Reads a `BORER_BUDGET` value.
///
/// # Arguments
///
/// * `value` - The variable's value, `None` when it is unset.
///
/// # Returns
///
/// [`BUDGET_DEFAULT`] when unset or not a number, `None` (no cap) at `0`,
/// else the number.
#[must_use]
pub fn budget_of(value: Option<&str>) -> Option<usize> {
    match value.map(|v| v.trim().parse::<usize>()) {
        Some(Ok(0)) => None,
        Some(Ok(bytes)) => Some(bytes),
        Some(Err(_)) | None => Some(BUDGET_DEFAULT),
    }
}

/// Whether an answer of `len` bytes is past the byte budget, and so cut
/// ([`budgeted`]).
///
/// # Arguments
///
/// * `len` - The answer's length in bytes.
pub fn over_budget(len: usize) -> bool {
    budget().is_some_and(|b| len > b)
}

/// Cuts an answer to `budget` bytes at the last whole line, with a note on
/// what was left out; an answer within the budget is kept whole.
///
/// The answer's `# since=` (or `%% since=`) line stays last, since the
/// reader passes it back to be told nothing changed: the cut took it with
/// the rest of the tail. The note says how this reader narrows: a tool by
/// its parameters, a URI by its suffixes and its filter.
///
/// # Arguments
///
/// * `text` - The answer.
/// * `budget` - Most bytes kept, the tag line included.
/// * `narrow` - How its reader asks for less.
pub fn cut_to(text: String, budget: usize, narrow: Narrow) -> String {
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
        Narrow::Uri => {
            "page with !offset=<n> and !limit=<n> on the URI, or narrow it by its filter where the resource takes one"
        }
    };
    format!(
        "{}{mark} cut at {cut} of {} bytes ({kept} of {total} lines) by {BUDGET_ENV}; {how}\n{tag}",
        &body[..cut],
        text.len()
    )
}
