//! Servers and answer helpers the server's unit tests share.

/// An answer with its evidence line taken off, so two emissions of one
/// answer compare: the id names the emission, so that is the one line
/// that differs between them.
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

/// A server with a small raw image loaded: 0x100 bytes of `ret` mapped
/// as `.text` at 0x1000, enough for the tools that read bytes and quick
/// to analyze.
pub(crate) fn raw_server() -> crate::BorerServer {
    use borer_engine::program::{Arch, Program, Section};
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    let program = Program::raw(vec![0xc3; 0x100], Arch::X86_64, 0, Some(0x1000), vec![text]);
    crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    }
}

/// The rows of a listing's URI read whole, its page suffixes taken off.
///
/// # Arguments
///
/// * `text` - A listing.
pub(crate) fn listed_rows(text: &str) -> Vec<String> {
    borer_engine::table::classify(text)
        .into_iter()
        .filter(|(kind, _)| *kind == borer_engine::table::Line::Row)
        .map(|(_, line)| line.to_owned())
        .collect()
}

/// Loads a file into a server as raw x86-64 code mapped at `base`, without
/// a PDB, through `load_binary`.
///
/// # Arguments
///
/// * `server` - The server.
/// * `path` - The file.
/// * `base` - Where its bytes map, as `load_binary` reads it.
///
/// # Errors
///
/// As `load_binary` refuses the file.
pub(crate) fn load_raw(
    server: &crate::BorerServer,
    path: &std::path::Path,
    base: &str,
) -> Result<String, rmcp::ErrorData> {
    server.load_binary(rmcp::handler::server::wrapper::Parameters(
        crate::params::LoadBinaryParams {
            path: path.display().to_string(),
            entry_file_offset: None,
            pdb: Some(false),
            arch: Some(crate::params::RawArch::X64),
            base: Some(base.to_owned()),
            entry: None,
            regions: None,
        },
    ))
}

/// A server with a one-instruction program loaded, for a handler test
/// that needs an analysis but not a real binary.
pub(crate) fn tiny_server() -> crate::BorerServer {
    use borer_engine::program::{Arch, Program, Section};
    let text = Section::mapped(".text", 0x1000, 0, 1, false, true);
    let program = Program::raw(vec![0xc3], Arch::X86_64, 0, Some(0x1000), vec![text]);
    crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    }
}
