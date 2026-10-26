//! What every index read works out again, kept once per analysis in
//! [`Analysis::derived`]: the key the program's index is stored under, and
//! the index file read back.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::SystemTime;

use borer_engine::analysis::Analysis;
use borer_engine::program::Program;

use super::{CodeIndex, IndexKey, index_key, load_from};

/// Returns the key the program's index is stored under ([`index_key`]),
/// worked out once per analysis.
///
/// The key hashes every byte of the program and renders its whole symbol
/// and section tables, which every `grep` paid for again.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis, whose packs are part of the key.
fn key(program: &Program, analysis: &Analysis) -> IndexKey {
    *analysis
        .derived
        .get_or_build("index_key", (), || index_key(program, &analysis.packs))
}

/// A version of an index file: its length and modification time.
type Version = (u64, Option<SystemTime>);

/// The one index kept for a file: the version it was read at, and what
/// that version held.
type Slot = Mutex<Option<(Version, Option<Arc<CodeIndex>>)>>;

/// Returns the program's index stored in `dir`, read from the file once
/// per version of it.
///
/// Every `grep` read the whole file again, tens of megabytes for a DLL;
/// the file's length and modification time stand for its version, so an
/// index rewritten or removed since is read again or found missing. The
/// memo holds one slot per file, and a new version replaces the one read
/// before it, so a rebuilt index never leaves an older copy loaded.
///
/// # Arguments
///
/// * `dir` - The index directory.
/// * `program` - The loaded image.
/// * `analysis` - Its analysis, whose memo keeps the index.
///
/// # Returns
///
/// The index and its path, or `None` when the file is absent, unreadable
/// or holds another key.
pub(super) fn held(
    dir: &Path,
    program: &Program,
    analysis: &Analysis,
) -> Option<(Arc<CodeIndex>, PathBuf)> {
    let key = key(program, analysis);
    let path = dir.join(key.file_name());
    let slot: Arc<Slot> = analysis
        .derived
        .get_or_build("code_index", path.clone(), || Mutex::new(None));
    let mut slot = slot.lock().unwrap_or_else(PoisonError::into_inner);
    let Ok(meta) = std::fs::metadata(&path) else {
        *slot = None;
        return None;
    };
    let version = (meta.len(), meta.modified().ok());
    let index = match slot.as_ref() {
        Some((seen, index)) if *seen == version => index.clone(),
        _ => {
            let index = load_from(&path)
                .filter(|index| index.key == key)
                .map(Arc::new);
            *slot = Some((version, index.clone()));
            index
        }
    }?;
    Some((index, path))
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::{Analysis, Overlay};
    use borer_engine::program::{Arch, Program, Section};

    use super::held;
    use crate::index::{IndexedFunction, build, save_to};

    /// A file is read once per version, and a rewritten file replaces the
    /// copy read before it rather than joining it; a removed file is found
    /// missing and lets its copy go.
    ///
    /// # Panics
    ///
    /// When a read of an unchanged file reads it again, a rewrite is not
    /// seen, an older copy stays held, or a removed file is still found.
    #[test]
    fn a_rewritten_index_replaces_the_copy_held() {
        let dir = std::env::temp_dir().join(format!("borer_memo_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("creates");
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let analysis = Analysis::default();
        let index = build(&program, &analysis, &Overlay::default());
        let path = dir.join(index.key.file_name());
        save_to(&index, &path).expect("writes");

        let (first, at) = held(&dir, &program, &analysis).expect("reads");
        assert_eq!(at, path);
        let (again, _) = held(&dir, &program, &analysis).expect("reads");
        assert!(
            Arc::ptr_eq(&first, &again),
            "an unchanged file is read once"
        );
        drop(again);

        let mut other = index;
        other.functions.push(IndexedFunction {
            entry: 0x1000,
            name: "longer".to_owned(),
            text: "return;\n".to_owned(),
        });
        save_to(&other, &path).expect("rewrites");
        let (second, _) = held(&dir, &program, &analysis).expect("reads the rewrite");
        assert_eq!(*second, other);
        assert_eq!(Arc::strong_count(&first), 1, "the older copy is let go");

        std::fs::remove_file(&path).expect("removes");
        assert!(held(&dir, &program, &analysis).is_none());
        assert_eq!(
            Arc::strong_count(&second),
            1,
            "a removed file's copy is let go"
        );
        std::fs::remove_dir_all(&dir).expect("cleans up");
    }
}
