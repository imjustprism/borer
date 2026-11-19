//! A code tab's inline editor: renaming, commenting or typing what the cursor is on, in a
//! block under its line.

use std::sync::{Arc, Mutex};

use borer_engine::analysis::edit::Offer;
use borer_engine::text;
use borer_engine::view::{Kind, Ref};
use editor::display_map::{BlockContext, BlockPlacement, BlockProperties, BlockStyle};
use editor::scroll::Autoscroll;
use gpui::{
    AppContext as _, Context, Entity, Focusable as _, InteractiveElement as _, IntoElement as _,
    ParentElement as _, Pixels, Styled as _, Window, canvas, div, px,
};
use language::Point;

use super::{DecompileItem, Form};
use crate::annotate::{Annotated, Annotator, Ask, INPUT_MIN_REMS};

/// Space in logical pixels kept between the inline editor and its host's right edge.
const EDGE_PX: f32 = 8.0;

/// Returns where the inline editor sits under its anchor in a host `host` wide: its left
/// padding and its least width.
///
/// It is at least `least` wide, or the host's width when narrower, never past the host's
/// right edge, and shifts left of its anchor as far as it must to fit.
///
/// # Arguments
///
/// * `anchor` - The anchor's distance from the host's left edge.
/// * `host` - The host's width.
/// * `least` - The narrowest the editor draws when the host has room.
fn placed(anchor: Pixels, host: Pixels, least: Pixels) -> (Pixels, Pixels) {
    let room = (host - px(EDGE_PX)).max(px(0.0));
    let least = least.min(room);
    (anchor.min(room - least).max(px(0.0)), least)
}

impl DecompileItem {
    /// Opens the inline editor for `ask` under the cursor's line, once the engine says what
    /// the referent takes: the token under the cursor for a name or a type, else the tab's
    /// function; for a comment, the comment under the cursor, else the line's instruction in
    /// a listing, and in a decompile the block the line comes from, else the function's
    /// entry, which the editor then says. A refusal is the status line's, in the engine's
    /// words.
    ///
    /// # Arguments
    ///
    /// * `ask` - What is asked.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn annotate(&mut self, ask: Ask, window: &mut Window, cx: &mut Context<'_, Self>) {
        let (Some(code), Some((row, col))) = (self.code.clone(), self.cursor(cx)) else {
            return;
        };
        let token = code
            .token_at(row, col)
            .and_then(|(_, _, (_, _, link))| link.cloned());
        let line = code.get(row);
        let at = line.and_then(|(view, line)| view.address(line));
        let origin = line.and_then(|(view, line)| view.origin(line));
        let function = self.entry.map(Ref::Function);
        let (referent, note) = match (ask, self.form, origin, self.entry) {
            (Ask::Comment | Ask::Question, ..) if matches!(token, Some(Ref::Comment(_))) => {
                (token, None)
            }
            (Ask::Comment | Ask::Question, Form::Listing, ..) => (at.map(Ref::Address), None),
            (Ask::Comment | Ask::Question, Form::Decompile, Some(block), _) => {
                let note = format!("goes at {block:#x}, the block this line comes from");
                (Some(Ref::Address(block)), Some(note))
            }
            (Ask::Comment | Ask::Question, Form::Decompile, None, Some(entry)) => {
                let name = text::visible(self.name.as_deref().unwrap_or_default()).into_owned();
                let note = format!(
                    "goes at {name}'s entry {entry:#x}: no block is known to write this line"
                );
                (function, Some(note))
            }
            (Ask::Rename | Ask::Type, ..) => (token.or(function), None),
            (Ask::Comment | Ask::Question, Form::Decompile, None, None)
            | (Ask::Declare | Ask::Enum | Ask::Typedef, ..) => (None, None),
        };
        let loaded = self.binary.read(cx).loaded().cloned();
        let loaded = loaded.unwrap_or_else(|| self.loaded.clone());
        let work = move || ask.offered(&loaded, referent.as_ref());
        let label = format!("Asking what takes {}", ask.title());
        self.offer_job
            .run_in(
                label,
                window,
                cx,
                work,
                move |item, offered, window, cx| match offered {
                    Ok(offer) => item.open_inline((ask, offer), note, window, cx),
                    Err(why) => item.say(text::visible(&why).into_owned(), cx),
                },
            );
    }

    /// Opens an inline editor for `offer` in a block under the cursor's line, or, for an ask
    /// that edits no referent, above the first line that opens with no comment, under the
    /// header comments; in place of any open, and focuses it. It plans over the binary's
    /// state now.
    ///
    /// # Arguments
    ///
    /// * `(ask, offer)` - What is asked and the engine's form for it.
    /// * `note` - Where the edit lands, when not where the cursor is.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn open_inline(
        &mut self,
        (ask, offer): (Ask, Offer),
        note: Option<String>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.close_inline(window, cx);
        let binary = self.binary.clone();
        let loaded = binary.read(cx).loaded().cloned();
        let loaded = loaded.unwrap_or_else(|| self.loaded.clone());
        let annotator = cx.new(|cx| Annotator::new(binary, loaded, (ask, offer), note, window, cx));
        let rows = annotator.read(cx).rows();
        let below_header = self.code.as_ref().and_then(|code| {
            let first = (0..code.len()).find(|&row| {
                code.get(row).is_some_and(|(view, line)| {
                    view.token_at(line, 0).is_some_and(|t| t.1 != Kind::Comment)
                })
            })?;
            u32::try_from(first).ok()
        });
        let shown = annotator.clone();
        let host = Arc::new(Mutex::new(None::<Pixels>));
        let render = Arc::new(move |cx: &mut BlockContext<'_, '_>| {
            let least = cx.window.rem_size() * INPUT_MIN_REMS;
            let known = host.lock().ok().and_then(|host| *host);
            let (left, least) = known.map_or((cx.anchor_x, least), |host| {
                placed(cx.anchor_x, host, least)
            });
            let measured = host.clone();
            let watch = canvas(
                move |bounds, window, cx| {
                    let width = Some(bounds.size.width);
                    let moved = measured
                        .lock()
                        .is_ok_and(|mut host| std::mem::replace(&mut *host, width) != width);
                    if moved {
                        window.defer(cx, |window, _| window.refresh());
                    }
                },
                |_, (), _, _| {},
            )
            .absolute()
            .size_full();
            div()
                .block_mouse_except_scroll()
                .relative()
                .pl(left)
                .pr(px(EDGE_PX))
                .w_full()
                .flex()
                .child(watch)
                .child(div().min_w(least).max_w_full().child(shown.clone()))
                .into_any_element()
        });
        let block = self.editor.update(cx, |editor, cx| {
            let placement = match below_header {
                Some(row) if ask.kind().is_none() => {
                    let first = Point::new(row, 0);
                    BlockPlacement::Above(
                        editor.buffer().read(cx).snapshot(cx).anchor_before(first),
                    )
                }
                Some(_) | None => BlockPlacement::Below(editor.selections.newest_anchor().head()),
            };
            let block = BlockProperties {
                placement,
                height: Some(rows),
                style: BlockStyle::Sticky,
                render,
                priority: 0,
            };
            editor.insert_blocks([block], Some(Autoscroll::fit()), cx)
        });
        let Some(&block) = block.first() else {
            return;
        };
        let events =
            cx.subscribe_in(
                &annotator,
                window,
                move |item, _, event, window, cx| match *event {
                    Annotated::Closed => item.close_inline(window, cx),
                },
            );
        window.focus(&annotator.focus_handle(cx), cx);
        self.inline = Some((annotator, block, events));
    }

    /// Returns the inline editor open in the tab, if any.
    #[must_use]
    pub fn inline(&self) -> Option<&Entity<Annotator>> {
        self.inline.as_ref().map(|(annotator, ..)| annotator)
    }

    /// Closes the inline editor, if one is open, and gives the focus back to the code.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn close_inline(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let Some((_, block, _)) = self.inline.take() else {
            return;
        };
        self.editor.update(cx, |editor, cx| {
            editor.remove_blocks([block].into_iter().collect(), None, cx);
        });
        window.focus(&self.editor.focus_handle(cx), cx);
        cx.notify();
    }
}

#[cfg(test)]
mod tests {
    use gpui::px;

    use super::{EDGE_PX, placed};

    /// The inline editor sits under its anchor when there is room, shifts left to stay
    /// inside a narrow host, and is never wider than the host.
    ///
    /// # Panics
    ///
    /// Panics if it reaches past the host's right edge or is narrower than it must be.
    #[test]
    fn the_inline_editor_stays_inside_a_narrow_host() {
        let least = px(448.0);
        assert_eq!(placed(px(100.0), px(1200.0), least), (px(100.0), least));
        let (left, width) = placed(px(500.0), px(800.0), least);
        assert_eq!(width, least);
        assert_eq!(left + width, px(800.0 - EDGE_PX));
        assert_eq!(
            placed(px(300.0), px(300.0), least),
            (px(0.0), px(300.0 - EDGE_PX))
        );
        assert_eq!(placed(px(10.0), px(0.0), least), (px(0.0), px(0.0)));
    }
}
