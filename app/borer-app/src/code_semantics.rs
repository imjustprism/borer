//! What Zed's editor asks a language server, answered from one [`View`].
//!
//! The hover says what the token under the pointer is and links to in its first frame, then
//! peeks at what it links to ([`Peeker`]). The document highlights are the uses in its view
//! of the referent under the cursor, read in the background, and a definition is the line of
//! the same view the referent goes to, so Zed's go to definition and its ctrl-click move
//! there. Everything else has no answer.

use std::ops::Range;
use std::sync::Arc;

use anyhow::Result;
use borer_engine::view::{Ref, View};
use collections::{FxHashMap, FxHashSet};
use editor::{Editor, GotoDefinitionKind, RenameTarget, SemanticsProvider};
use futures::future::Shared;
use gpui::{App, Entity, Task};
use language::{
    Anchor, Buffer, BufferId, BufferRow, BufferSnapshot, LanguageServerId, Point, ToPoint as _,
};
use markdown::Markdown;
use project::lsp_store::{BufferSemanticTokens, CacheInlayHints};
use project::{
    DocumentHighlight, Hover, HoverBlock, HoverBlockKind, InlayHint, InvalidationStrategy,
    Location, LocationLink, ProjectTransaction,
};

use crate::binary::Binary;
use crate::code_view::{ClickOutcome, CodeLines, Token, describe, resolve_ref_click};
use crate::hover_peek::Peeker;
use crate::worker::{LoadedBinary, spawn_engine};

/// Answers Zed's editor about the views a code tab shows, each view's lines on the rows it
/// is shown on.
#[derive(Debug)]
pub struct ViewSemantics {
    /// The tab's lines: row `i` of the buffer is shown line `i`.
    pub code: Arc<CodeLines>,
    /// The hover's peeks into the binary the lines come from.
    peek: Peeker,
}

/// The token under a point of a tab's buffer.
#[derive(Debug)]
struct Under {
    /// The point's row.
    row: u32,
    /// The token's bytes in the row.
    span: Range<usize>,
    /// The token's text, from the file.
    text: String,
    /// What the view says of the token.
    said: String,
    /// What the token links to.
    link: Option<Ref>,
}

impl ViewSemantics {
    /// Returns the provider of `code`'s lines shown in `editor`, peeking into `loaded`.
    ///
    /// # Arguments
    ///
    /// * `code` - The tab's lines.
    /// * `loaded` - The binary state they come from.
    /// * `binary` - The window's binary, whose rechecks a peek's counts read.
    /// * `editor` - The editor showing them.
    /// * `cx` - Application context the editor and the binary are watched in.
    pub fn new(
        code: Arc<CodeLines>,
        loaded: Arc<LoadedBinary>,
        binary: &Entity<Binary>,
        editor: &Entity<Editor>,
        cx: &mut App,
    ) -> Self {
        let peek = Peeker::new(loaded, binary, editor, cx);
        Self { code, peek }
    }

    /// Returns the token at `position` of `buffer`.
    ///
    /// # Arguments
    ///
    /// * `buffer` - The tab's buffer.
    /// * `position` - Where the pointer or the cursor is.
    /// * `cx` - Application context reading the buffer.
    fn token(&self, buffer: &Entity<Buffer>, position: Anchor, cx: &App) -> Option<Under> {
        let snapshot = buffer.read(cx).snapshot();
        let at = position.to_point(&snapshot);
        let (view, line, (span, kind, link)) = token_under(&self.code, at)?;
        let text = view.line(line)?.get(span.clone())?;
        Some(Under {
            row: at.row,
            said: describe(text, kind, link),
            text: text.to_owned(),
            span,
            link: link.cloned(),
        })
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
        let Some(under) = self.token(buffer, position, cx) else {
            self.peek.drop_peek();
            return None;
        };
        let said = Markdown::escape(&under.said).into_owned();
        let more = self.peek.block(&under.text, &said, under.link, cx);
        let said = HoverBlock {
            text: said,
            kind: HoverBlockKind::Markdown,
        };
        let more = HoverBlock {
            text: more,
            kind: HoverBlockKind::Markdown,
        };
        let hover = Hover {
            contents: std::iter::once(said)
                .chain(Some(more).filter(|more| !more.text.is_empty()))
                .collect(),
            range: Some(anchors(&buffer.read(cx).snapshot(), under.row, &under.span)),
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
            let Some((view, line, (_, _, Some(link)))) = token_under(&code, at) else {
                return Ok(Vec::new());
            };
            let first = at
                .row
                .saturating_sub(u32::try_from(line).unwrap_or(u32::MAX));
            let (uses, _) = view.uses(link);
            Ok(uses
                .iter()
                .filter_map(|(line, span)| {
                    let row = first.checked_add(u32::try_from(*line).ok()?)?;
                    Some(DocumentHighlight {
                        range: anchors(&snapshot, row, span),
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
        let at = position.to_point(&snapshot);
        let (view, line, (_, _, link)) = token_under(&self.code, at)?;
        let ClickOutcome::ScrollToLine(to) = resolve_ref_click(view, link?) else {
            return None;
        };
        let row = at.row.checked_sub(u32::try_from(line).ok()?)?;
        let row = row.checked_add(u32::try_from(to).ok()?)?;
        let start = snapshot.anchor_before(Point::new(row, 0));
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
/// * `loaded` - The binary state they come from.
/// * `binary` - The window's binary.
/// * `editor` - The editor showing them.
/// * `cx` - Application context the editor and the binary are watched in.
#[must_use]
pub fn for_one_view(
    code: &Arc<CodeLines>,
    loaded: &Arc<LoadedBinary>,
    binary: &Entity<Binary>,
    editor: &Entity<Editor>,
    cx: &mut App,
) -> Option<ViewSemantics> {
    let new = || ViewSemantics::new(code.clone(), loaded.clone(), binary, editor, cx);
    (code.views() == 1).then(new)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::decompile::view::view;
    use gpui::TestAppContext;

    use super::for_one_view;
    use crate::app_view::tests::{CALLER, sample};
    use crate::code_view::CodeLines;
    use crate::code_view::tests::sample_program;
    use crate::hover_peek::tests::Tab;

    /// A provider answers about one view only, never a tab of many.
    #[gpui::test]
    fn only_a_one_view_tab_gets_answers(cx: &mut TestAppContext) {
        let (program, analysis, overlay) = sample_program();
        let one = view(&program, &analysis, &overlay, 0x1000).expect("decompiles");
        let loaded = sample();
        let (tab, cx) = Tab::open(&loaded, CALLER, cx);
        let single = Arc::new(CodeLines::new(vec![one.clone()]));
        let double = Arc::new(CodeLines::new(vec![one.clone(), one]));
        let (binary, editor) = (tab.binary.clone(), tab.editor(cx));
        cx.update(|_, cx| {
            assert!(for_one_view(&single, &loaded, &binary, &editor, cx).is_some());
            assert!(for_one_view(&double, &loaded, &binary, &editor, cx).is_none());
        });
    }
}
