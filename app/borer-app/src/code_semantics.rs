//! What Zed's editor asks a language server, answered from one [`View`].
//!
//! The hover says what the token under the pointer is and links to, the document highlights
//! are the view's uses of the referent under the cursor, read in the background, and a
//! definition is the line of the same view the referent goes to, so Zed's go to definition
//! and its ctrl-click move there. Everything else has no answer.

use std::ops::Range;
use std::sync::Arc;

use anyhow::Result;
use borer_engine::view::View;
use collections::{FxHashMap, FxHashSet};
use editor::{GotoDefinitionKind, RenameTarget, SemanticsProvider};
use futures::future::Shared;
use gpui::{App, Entity, Task};
use language::{
    Anchor, Buffer, BufferId, BufferRow, BufferSnapshot, LanguageServerId, Point, ToPoint as _,
};
use project::lsp_store::{BufferSemanticTokens, CacheInlayHints};
use project::{
    DocumentHighlight, Hover, HoverBlock, HoverBlockKind, InlayHint, InvalidationStrategy,
    Location, LocationLink, ProjectTransaction,
};

use crate::code_view::{ClickOutcome, CodeLines, Token, describe, resolve_ref_click};
use crate::worker::spawn_engine;

/// Answers Zed's editor about the one view a code tab shows, row for row.
#[derive(Debug)]
pub struct ViewSemantics {
    /// The tab's lines: one view, its line `i` the buffer's row `i`.
    pub code: Arc<CodeLines>,
}

impl ViewSemantics {
    /// Returns the token at `position` of `buffer`: its row, its bytes in the row, and the
    /// view and line it comes from.
    ///
    /// # Arguments
    ///
    /// * `buffer` - The tab's buffer.
    /// * `position` - Where the pointer or the cursor is.
    /// * `cx` - Application context reading the buffer.
    fn token(
        &self,
        buffer: &Entity<Buffer>,
        position: Anchor,
        cx: &App,
    ) -> Option<(Point, Range<usize>, String)> {
        let snapshot = buffer.read(cx).snapshot();
        let at = position.to_point(&snapshot);
        let (view, line, (span, kind, link)) = token_under(&self.code, at)?;
        let text = view.line(line)?.get(span.clone())?;
        Some((at, span, describe(text, kind, link)))
    }
}

/// Returns the token a buffer point of a one-view tab stands on, with its view and line.
///
/// # Arguments
///
/// * `code` - The tab's lines.
/// * `at` - The point.
fn token_under(code: &CodeLines, at: Point) -> Option<(&Arc<View>, usize, Token<'_>)> {
    code.token_at(
        usize::try_from(at.row).ok()?,
        usize::try_from(at.column).ok()?,
    )
}

/// Returns the anchors of bytes `span` of row `row` of a buffer.
///
/// # Arguments
///
/// * `snapshot` - The buffer's snapshot.
/// * `row` - Zero-based row.
/// * `span` - Bytes in the row.
fn anchors(snapshot: &BufferSnapshot, row: u32, span: &Range<usize>) -> Range<Anchor> {
    let col = |c: usize| u32::try_from(c).unwrap_or(u32::MAX);
    snapshot.anchor_after(Point::new(row, col(span.start)))
        ..snapshot.anchor_before(Point::new(row, col(span.end)))
}

impl SemanticsProvider for ViewSemantics {
    fn hover(
        &self,
        buffer: &Entity<Buffer>,
        position: Anchor,
        cx: &mut App,
    ) -> Option<Task<Option<Vec<Hover>>>> {
        let (at, span, text) = self.token(buffer, position, cx)?;
        let hover = Hover {
            contents: vec![HoverBlock {
                text,
                kind: HoverBlockKind::PlainText,
            }],
            range: Some(anchors(&buffer.read(cx).snapshot(), at.row, &span)),
            language: None,
        };
        Some(Task::ready(Some(vec![hover])))
    }

    fn inline_values(
        &self,
        _buffer_handle: Entity<Buffer>,
        _range: Range<Anchor>,
        _cx: &mut App,
    ) -> Option<Task<Result<Vec<InlayHint>>>> {
        None
    }

    fn applicable_inlay_chunks(
        &self,
        _buffer: &Entity<Buffer>,
        _ranges: &[Range<Anchor>],
        _cx: &mut App,
    ) -> Vec<Range<BufferRow>> {
        Vec::new()
    }

    fn invalidate_inlay_hints(&self, _for_buffers: &FxHashSet<BufferId>, _cx: &mut App) {}

    fn inlay_hints(
        &self,
        _invalidate: InvalidationStrategy,
        _buffer: Entity<Buffer>,
        _ranges: Vec<Range<Anchor>>,
        _known_chunks: Option<(clock::Global, FxHashSet<Range<BufferRow>>)>,
        _cx: &mut App,
    ) -> Option<FxHashMap<Range<BufferRow>, Task<Result<CacheInlayHints>>>> {
        None
    }

    fn semantic_tokens(
        &self,
        _buffer: Entity<Buffer>,
        _cx: &mut App,
    ) -> Option<Shared<Task<std::result::Result<BufferSemanticTokens, Arc<anyhow::Error>>>>> {
        None
    }

    fn supports_inlay_hints(&self, _buffer: &Entity<Buffer>, _cx: &mut App) -> bool {
        false
    }

    fn supports_semantic_tokens(&self, _buffer: &Entity<Buffer>, _cx: &mut App) -> bool {
        false
    }

    fn document_highlights(
        &self,
        buffer: &Entity<Buffer>,
        position: Anchor,
        cx: &mut App,
    ) -> Option<Task<Result<Vec<DocumentHighlight>>>> {
        let snapshot = buffer.read(cx).snapshot();
        let at = position.to_point(&snapshot);
        let code = self.code.clone();
        let uses = spawn_engine("Finding uses", cx, move || {
            let Some((view, _, (_, _, Some(link)))) = token_under(&code, at) else {
                return Ok(Vec::new());
            };
            let (uses, _) = view.uses(link);
            Ok(uses
                .iter()
                .filter_map(|(line, span)| {
                    Some(DocumentHighlight {
                        range: anchors(&snapshot, u32::try_from(*line).ok()?, span),
                        kind: lsp::DocumentHighlightKind::READ,
                    })
                })
                .collect())
        });
        Some(cx.spawn(async move |_| uses.await.unwrap_or_else(|| Ok(Vec::new()))))
    }

    fn definitions(
        &self,
        buffer: &Entity<Buffer>,
        position: Anchor,
        _kind: GotoDefinitionKind,
        cx: &mut App,
    ) -> Option<Task<Result<Option<Vec<LocationLink>>>>> {
        let snapshot = buffer.read(cx).snapshot();
        let (view, _, (_, _, link)) = token_under(&self.code, position.to_point(&snapshot))?;
        let ClickOutcome::ScrollToLine(line) = resolve_ref_click(view, link?) else {
            return None;
        };
        let start = snapshot.anchor_before(Point::new(u32::try_from(line).ok()?, 0));
        let target = Location {
            buffer: buffer.clone(),
            range: start..start,
        };
        let links = vec![LocationLink {
            origin: None,
            target,
        }];
        Some(Task::ready(Ok(Some(links))))
    }

    fn range_for_rename(
        &self,
        _buffer: &Entity<Buffer>,
        _position: Anchor,
        _cx: &mut App,
    ) -> Task<Result<Option<RenameTarget>>> {
        Task::ready(Ok(None))
    }

    fn perform_rename(
        &self,
        _buffer: &Entity<Buffer>,
        _position: Anchor,
        _new_name: String,
        _language_server_id: Option<LanguageServerId>,
        _cx: &mut App,
    ) -> Option<Task<Result<ProjectTransaction>>> {
        None
    }
}

/// Returns the provider of a tab's lines when they come from one view.
///
/// Every row of such a tab is a line of that view, so [`View::uses`] maps onto the rows; a
/// tab of many views (the measured lines) gets none.
///
/// # Arguments
///
/// * `code` - The tab's lines.
#[must_use]
pub fn for_one_view(code: &Arc<CodeLines>) -> Option<ViewSemantics> {
    (code.views() == 1).then(|| ViewSemantics { code: code.clone() })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::decompile::view::view;

    use super::for_one_view;
    use crate::code_view::CodeLines;
    use crate::code_view::tests::sample_program;

    /// A provider answers about one view only, never a tab of many.
    ///
    /// # Panics
    ///
    /// Panics if a tab of two views gets a provider or a tab of one does not.
    #[test]
    fn only_a_one_view_tab_gets_answers() {
        let (program, analysis, overlay) = sample_program();
        let one = view(&program, &analysis, &overlay, 0x1000).expect("decompiles");
        let single = Arc::new(CodeLines::new(vec![one.clone()]));
        assert!(for_one_view(&single).is_some());
        let double = Arc::new(CodeLines::new(vec![one.clone(), one]));
        assert!(for_one_view(&double).is_none());
    }
}
