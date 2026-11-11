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

/// A server with a program loaded, as `load_binary` leaves one that has
/// no PDB to look for.
///
/// # Arguments
///
/// * `program` - The program.
pub(crate) fn server_with(program: borer_engine::program::Program) -> crate::BorerServer {
    crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    }
}

/// A server with machine code loaded as a raw image: one executable
/// section `.text` at 0x1000 holding `code`, entered at its first byte.
///
/// # Arguments
///
/// * `arch` - The instruction set the code is written in.
/// * `code` - The section's bytes.
pub(crate) fn code_server(arch: borer_engine::program::Arch, code: &[u8]) -> crate::BorerServer {
    use borer_engine::program::{Program, Section};
    let size = borer_engine::num::from_usize(code.len());
    let text = Section::mapped(".text", 0x1000, 0, size, false, true);
    server_with(Program::raw(
        code.to_vec(),
        arch,
        0,
        Some(0x1000),
        vec![text],
    ))
}

/// A server with a small raw image loaded: 0x100 bytes of `ret` mapped
/// as `.text` at 0x1000, enough for the tools that read bytes and quick
/// to analyze.
pub(crate) fn raw_server() -> crate::BorerServer {
    code_server(borer_engine::program::Arch::X86_64, &[0xc3; 0x100])
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
    code_server(borer_engine::program::Arch::X86_64, &[0xc3])
}
