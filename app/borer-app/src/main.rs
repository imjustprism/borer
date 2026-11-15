//! Binary entry point for `borer-app`.

use std::io::Write as _;
use std::process::ExitCode;

/// Runs `borer-app` and maps errors to a non-zero exit status: 1 with the error on
/// stderr, 2 when stderr cannot take it either.
fn main() -> ExitCode {
    match borer_app::run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) if writeln!(std::io::stderr().lock(), "borer-app: {err:#}").is_ok() => {
            ExitCode::FAILURE
        }
        Err(_) => ExitCode::from(2),
    }
}
