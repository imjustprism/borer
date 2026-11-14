//! Binary entry point for `borer-app`.

use std::io::Write as _;
use std::process::ExitCode;

/// Runs `borer-app` and maps errors to a non-zero exit status.
fn main() -> ExitCode {
    if let Err(err) = borer_app::run() {
        let _ = writeln!(std::io::stderr().lock(), "borer-app: {err:#}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
