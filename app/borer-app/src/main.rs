//! Binary entry point for `borer-app`.
//!
//! A GUI-subsystem binary on Windows, so a person launching it gets no console beside
//! its window; the measurement modes still write their reports to the stdout and stderr
//! pipes a caller such as `scripts/run/app_measure.py` hands it.

#![windows_subsystem = "windows"]

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
