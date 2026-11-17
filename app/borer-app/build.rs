//! Embeds the app icon in `borer-app.exe` when building for Windows.
//!
//! `borer-app.rc` makes `packaging/borer-app/icons/borer-app.ico` icon resource 1, the one
//! GPUI loads for every window and Explorer, the taskbar and the installer's shortcut show.
//! Other targets embed nothing.

/// Compiles `borer-app.rc` and links it into the `borer-app` binary.
///
/// # Errors
///
/// Returns the resource compiler's failure, or its absence when building for Windows.
fn main() -> Result<(), embed_resource::CompilationResult> {
    println!("cargo:rerun-if-changed=borer-app.rc");
    println!("cargo:rerun-if-changed=../../packaging/borer-app/icons/borer-app.ico");
    embed_resource::compile("borer-app.rc", embed_resource::NONE).manifest_required()
}
