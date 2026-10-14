//! The server's integration tests as one binary: every file here is a
//! module, so the server is linked once for all of them.
mod cli;
mod contract;
mod evidence;
mod project;
mod reload;
mod resources;

/// An answer with its evidence line taken off, so two emissions of one
/// answer compare: the id names the emission, so that is the one line that
/// differs between them.
///
/// # Arguments
///
/// * `sent` - An answer as sent.
pub(crate) fn without_evidence(sent: &str) -> &str {
    let at = sent.trim_end_matches('\n').rfind('\n').map_or(0, |i| i + 1);
    let last = &sent[at..];
    if last.starts_with("# evidence:") || last.starts_with("%% evidence:") {
        &sent[..at]
    } else {
        sent
    }
}
