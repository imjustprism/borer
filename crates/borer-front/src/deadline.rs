//! The deadline a request stops at, shared by the MCP server and the app's chat so an agent
//! and a model in the chat get the same time per request and the same note when it runs out.
//!
//! It is read from the environment (`BORER_DEADLINE_SECS`) the same way by both.

use std::time::Duration;

/// The environment variable naming the per-request deadline, in seconds.
pub const DEADLINE_ENV: &str = "BORER_DEADLINE_SECS";

/// The deadline when the environment names none.
pub const DEADLINE_DEFAULT: Duration = Duration::from_mins(5);

/// Returns the deadline a value of `BORER_DEADLINE_SECS` names.
///
/// # Arguments
///
/// * `text` - The variable's value, `None` when it is unset.
///
/// # Returns
///
/// [`DEADLINE_DEFAULT`] when unset, `None` (no limit) for `0`, else that many seconds.
///
/// # Errors
///
/// When the value is not a number of seconds, saying the default is used instead.
pub fn deadline_of(text: Option<&str>) -> Result<Option<Duration>, String> {
    let Some(text) = text else {
        return Ok(Some(DEADLINE_DEFAULT));
    };
    match text.trim().parse::<u64>() {
        Ok(0) => Ok(None),
        Ok(secs) => Ok(Some(Duration::from_secs(secs))),
        Err(_) => Err(format!(
            "{DEADLINE_ENV}={} is not a number of seconds; using {}",
            borer_engine::text::one_line(text),
            DEADLINE_DEFAULT.as_secs()
        )),
    }
}

/// Returns the deadline the environment names ([`deadline_of`]), the default when its value
/// does not read.
#[must_use]
pub fn deadline() -> Option<Duration> {
    deadline_of(std::env::var(DEADLINE_ENV).ok().as_deref()).unwrap_or(Some(DEADLINE_DEFAULT))
}

/// Returns the note a request its deadline stopped ends with.
///
/// # Arguments
///
/// * `deadline` - The deadline it ran past, `None` for none.
#[must_use]
pub fn note(deadline: Option<Duration>) -> String {
    let secs = deadline.map_or(0, |d| d.as_secs());
    format!(
        "# stopped: time limit: the request ran past {secs}s and stopped there, so the answer above is partial; ask for less (one function, a filter, a page) or raise {DEADLINE_ENV}"
    )
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::{DEADLINE_DEFAULT, deadline_of};

    /// Unset is the default, `0` no limit, a number that many seconds, anything else the
    /// default with why.
    ///
    /// # Panics
    ///
    /// When a value reads otherwise.
    #[test]
    fn the_deadline_reads_as_the_server_read_it() {
        assert_eq!(deadline_of(None), Ok(Some(DEADLINE_DEFAULT)));
        assert_eq!(deadline_of(Some("0")), Ok(None));
        assert_eq!(deadline_of(Some(" 7 ")), Ok(Some(Duration::from_secs(7))));
        let refused = deadline_of(Some("soon")).expect_err("not seconds");
        assert!(refused.contains("is not a number of seconds"), "{refused}");
    }
}
