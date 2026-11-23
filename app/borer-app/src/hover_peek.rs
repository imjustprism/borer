//! The second block of a code tab's hover: what the engine shows of the hovered token's
//! referent ([`peek_blocking`]), read in the background and formatted here.
//!
//! The hover paints at once with a reading line, and the landed peek replaces the shown
//! popover's text. A function shows its counts as the status bar counts them, rechecks
//! first. What the file names and what the engine says are escaped or fenced, so no text
//! of the file is read as Markdown. Each peek read is kept until a recheck of its function,
//! and the tab's provider is built again on every edit, which drops them all.
//!
//! Zed paints a hover only when its provider's task resolves and cannot stream one, so the
//! fill reads and replaces the hover's text through Zed's hover state at the pinned
//! revision ([`hover_texts`]).

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use borer_engine::view::Ref;
use collections::FxHashMap;
use editor::Editor;
use gpui::{App, Entity, Subscription, WeakEntity};
use markdown::Markdown;

use crate::binary::{Binary, BinaryEvent};
use crate::status::grades_text;
use crate::worker::{
    Certainty, GradeCounts, Head, Job, LoadedBinary, Peek, peek_blocking, peeks,
    shown_counts_blocking,
};

/// Most peeks a tab keeps; past it the kept ones are dropped.
const PEEKED_MAX: usize = 512;

/// The hover a peek read fills.
#[derive(Debug)]
struct Peeking {
    /// The read; dropping it raises its flag.
    _job: Job,
    /// What the read peeks at.
    link: Ref,
    /// The hover's text while it reads: the token's words and the reading line.
    shown: String,
    /// The hover's text with the peek, `None` until the read lands.
    filled: Option<String>,
    /// Whether the landed peek is kept: a recheck of the function since the read began
    /// makes its counts old.
    keep: bool,
}

/// The peeks of one code tab's hover: the read going and the peeks read before.
#[derive(Debug)]
pub struct Peeker {
    /// The window's binary, whose rechecks the counts read.
    binary: Entity<Binary>,
    /// The state the tab's lines come from, which a peek reads.
    loaded: Arc<LoadedBinary>,
    /// The editor showing the lines, whose hover a landed peek fills.
    editor: WeakEntity<Editor>,
    /// The newest hover's read, dropped when the next hover asks or the hover closes.
    going: Rc<RefCell<Option<Peeking>>>,
    /// The Markdown of every peek read before, so its next hover shows it at once.
    peeked: Rc<RefCell<FxHashMap<Ref, String>>>,
    /// Fills the hover when its peek lands and drops the read when the hover closes.
    _hover: Subscription,
    /// Drops the peek of a function a recheck changed.
    _rechecks: Subscription,
}

impl Peeker {
    /// Returns the peeks of the hover of `editor`, reading `loaded`.
    ///
    /// # Arguments
    ///
    /// * `loaded` - The state the tab's lines come from.
    /// * `binary` - The window's binary.
    /// * `editor` - The editor showing the lines.
    /// * `cx` - Application context the editor and the binary are watched in.
    pub fn new(
        loaded: Arc<LoadedBinary>,
        binary: &Entity<Binary>,
        editor: &Entity<Editor>,
        cx: &mut App,
    ) -> Self {
        let going: Rc<RefCell<Option<Peeking>>> = Rc::default();
        let peeked: Rc<RefCell<FxHashMap<Ref, String>>> = Rc::default();
        let held = going.clone();
        let hover = cx.observe(editor, move |editor, cx| fill(&editor, &held, cx));
        let (held, kept, state) = (going.clone(), peeked.clone(), loaded.clone());
        let rechecks = cx.subscribe(binary, move |_, event, _| {
            let BinaryEvent::Rechecked {
                state: at,
                function,
            } = event
            else {
                return;
            };
            if state.is_state(at) {
                let link = Ref::Function(*function);
                kept.borrow_mut().remove(&link);
                if let Some(going) = held.borrow_mut().as_mut().filter(|g| g.link == link) {
                    going.keep = false;
                }
            }
        });
        Self {
            binary: binary.clone(),
            loaded,
            editor: editor.downgrade(),
            going,
            peeked,
            _hover: hover,
            _rechecks: rechecks,
        }
    }

    /// Drops the read going and the hover it would fill.
    pub fn drop_peek(&self) {
        self.going.replace(None);
    }

    /// Returns the second block of the hover over a token linking to `link`: the peek read
    /// before, else a reading line while a new read runs, else nothing.
    ///
    /// # Arguments
    ///
    /// * `name` - The token's text, from the file.
    /// * `said` - The hover's first block: what the view says of the token, escaped.
    /// * `link` - What the token links to.
    /// * `cx` - Application context the read is spawned in.
    ///
    /// # Returns
    ///
    /// The block's Markdown, empty for none.
    pub fn block(&self, name: &str, said: &str, link: Option<Ref>, cx: &mut App) -> String {
        self.drop_peek();
        let Some(link) = link.filter(peeks) else {
            return String::new();
        };
        if let Some(text) = self.peeked.borrow().get(&link) {
            return text.clone();
        }
        let Some(editor) = self.editor.upgrade() else {
            return String::new();
        };
        let rechecked = match link {
            Ref::Function(entry) => self.binary.read(cx).rechecked(&self.loaded.state(), entry),
            _ => None,
        };
        let (loaded, key) = (self.loaded.clone(), link.clone());
        let read = move || {
            let found = peek_blocking(&loaded, &key);
            let counts = match key {
                Ref::Function(entry) => shown_counts_blocking(&loaded, entry, rechecked.as_deref()),
                _ => None,
            };
            found.map(|found| (found, counts))
        };
        let (going, peeked, said_now, key) = (
            self.going.clone(),
            self.peeked.clone(),
            said.to_owned(),
            link.clone(),
        );
        let mut job = Job::default();
        editor.update(cx, |_, cx| {
            job.run(format!("Peeking {name}"), cx, read, move |_, found, cx| {
                let text = found.map_or_else(String::new, |(found, counts)| {
                    markdown_of(&found, counts.as_ref())
                });
                let mut going = going.borrow_mut();
                let keep = going.as_ref().is_none_or(|g| g.keep);
                if let Some(going) = going.as_mut() {
                    going.filled = Some(hover_text(&said_now, &text));
                }
                let mut peeked = peeked.borrow_mut();
                if keep && !text.is_empty() {
                    if peeked.len() >= PEEKED_MAX {
                        peeked.clear();
                    }
                    peeked.insert(key, text);
                }
                cx.notify();
            });
        });
        let reading = format!("Reading {}…", Markdown::escape(name));
        self.going.replace(Some(Peeking {
            _job: job,
            link,
            shown: hover_text(said, &reading),
            filled: None,
            keep: true,
        }));
        reading
    }
}

/// Fills the hover of `editor` a landed peek waits for, and drops the read once the hover
/// closed.
///
/// Zed drops the editor's hover task when the hover closes, and when the pointer leaves
/// before the hover shows, without telling the editor's observers; a read is then dropped at
/// the editor's next notify, at the latest when the read lands and notifies it, and its peek
/// is kept for the next hover.
///
/// # Arguments
///
/// * `editor` - The editor showing the lines.
/// * `going` - The read and the hover it fills.
/// * `cx` - Application context.
fn fill(editor: &Entity<Editor>, going: &RefCell<Option<Peeking>>, cx: &mut App) {
    if editor.read(cx).hover_state.info_task.is_none() {
        going.replace(None);
        return;
    }
    let Some((shown, filled)) = going.borrow().as_ref().and_then(|going| {
        let filled = going.filled.clone()?;
        Some((going.shown.clone(), filled))
    }) else {
        return;
    };
    let texts: Vec<_> = hover_texts(editor.read(cx)).cloned().collect();
    let mut done = false;
    for text in texts {
        if text.read(cx).source().as_ref() == shown {
            text.update(cx, |text, cx| text.replace(filled.clone(), cx));
            done = true;
        }
    }
    if done {
        going.replace(None);
    }
}

/// Returns the Markdown of each hover popover `editor` shows.
///
/// This reads Zed's hover state, which is not a stable interface: it holds at the Zed
/// revision the app pins, and a new revision may move it.
///
/// # Arguments
///
/// * `editor` - The editor.
pub fn hover_texts(editor: &Editor) -> impl Iterator<Item = &Entity<Markdown>> {
    let popovers = editor.hover_state.info_popovers.iter();
    popovers.filter_map(|popover| popover.parsed_content.as_ref())
}

/// Returns the text Zed's hover shows of the blocks `said` and `more`: each trimmed, joined
/// by a blank line, an empty one left out, as Zed joins a hover's blocks.
///
/// # Arguments
///
/// * `said` - The first block.
/// * `more` - The second block, empty for none.
#[must_use]
pub fn hover_text(said: &str, more: &str) -> String {
    match more.trim() {
        "" => said.trim().to_owned(),
        more => format!("{}\n\n{more}", said.trim()),
    }
}

/// Returns `lines` in a Markdown code block, fenced longer than any backtick run in them.
///
/// # Arguments
///
/// * `lines` - The engine's lines.
#[must_use]
pub fn fenced(lines: &[String]) -> String {
    let text = lines.join("\n");
    let run = text.split(|c| c != '`').map(str::len).max().unwrap_or(0);
    let fence = "`".repeat(run.max(2).saturating_add(1));
    format!("{fence}\n{text}\n{fence}")
}

/// Returns `head` as code, with a line saying how many lines it leaves out.
///
/// # Arguments
///
/// * `head` - The engine's first lines of a text.
#[must_use]
pub fn head_markdown(head: &Head) -> String {
    match head.more() {
        0 => fenced(&head.lines),
        1 => format!("{}\n\n1 more line", fenced(&head.lines)),
        n => format!("{}\n\n{n} more lines", fenced(&head.lines)),
    }
}

/// Returns the Markdown of the hover's second block for `found`.
///
/// A head shows as code, a function's counts in the status bar's words, an import's
/// declaration as code under what is known of its name, and the engine's reason escaped.
///
/// # Arguments
///
/// * `found` - What the engine shows of the referent.
/// * `counts` - A function's counts as the status bar counts them.
#[must_use]
pub fn markdown_of(found: &Peek, counts: Option<&GradeCounts>) -> String {
    match found {
        Peek::Function(head) => match counts {
            Some(counts) => format!("{}\n\n{}", head_markdown(head), grades_text(counts)),
            None => head_markdown(head),
        },
        Peek::Global(_, head) => head_markdown(head),
        Peek::Import {
            name,
            certainty,
            decl,
        } => {
            let name = name.as_deref().map(Markdown::escape);
            match (certainty, name, decl) {
                (Certainty::Unresolved, Some(name), _) => {
                    format!("Unresolved import {name}: no one name is known for this slot.")
                }
                (Certainty::Unresolved, None, _) => {
                    "Unresolved import: no one name is known for this slot.".to_owned()
                }
                (Certainty::Resolved, _, Some(decl)) => head_markdown(decl),
                (Certainty::Inferred, Some(name), Some(decl)) => format!(
                    "{name} is inferred from the import's ordinal.\n\n{}",
                    head_markdown(decl)
                ),
                (Certainty::Inferred, None, Some(decl)) => format!(
                    "The name is inferred from the import's ordinal.\n\n{}",
                    head_markdown(decl)
                ),
                (Certainty::Resolved | Certainty::Inferred, Some(name), None) => {
                    format!("The type library declares no {name}.")
                }
                (Certainty::Resolved | Certainty::Inferred, None, None) => {
                    "The type library declares no such import.".to_owned()
                }
            }
        }
        Peek::Unknown(why) => Markdown::escape(why).into_owned(),
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
pub(crate) mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::render::typed_tsv;
    use borer_engine::analysis::utypes::TypeExpr;
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::cancel::Cancel;
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use borer_engine::view::Ref;
    use editor::actions::Hover as HoverAction;
    use editor::hover_popover::{hide_hover, hover, hover_at};
    use editor::{Editor, SelectionEffects};
    use futures::FutureExt as _;
    use gpui::{Entity, SharedString, Task, TestAppContext, VisualTestContext};
    use language::Point;
    use markdown::Markdown;
    use project::Hover;

    use super::{hover_text, hover_texts, markdown_of};
    use crate::app_view::tests::{CALLEE, CALLER, init, loaded_of, open, sample};
    use crate::binary::{Binary, BinaryEvent};
    use crate::check_marks::tests::wrong_at;
    use crate::code_view::{CodeLines, describe};
    use crate::decompile_item::tests::open_tab;
    use crate::decompile_item::{DecompileItem, Form};
    use crate::status::grades_text;
    use crate::worker::{
        Certainty, GradeCounts, Head, Jobs, LoadedBinary, Peek, Read, check_blocking,
        grade_counts_blocking, peek_blocking, run_engine,
    };
    use crate::xrefs::tests::imported;

    /// Address of the global [`global_reader`] reads.
    const GLOBAL: u64 = 0x1100;

    /// A decompile tab in a window over the window's binary.
    pub(crate) struct Tab {
        /// The tab.
        item: Entity<DecompileItem>,
        /// The window's binary.
        pub(crate) binary: Entity<Binary>,
    }

    impl Tab {
        /// Opens a window over `loaded` with the decompile tab of `entry`.
        pub(crate) fn open<'a>(
            loaded: &Arc<LoadedBinary>,
            entry: u64,
            cx: &'a mut TestAppContext,
        ) -> (Self, &'a mut VisualTestContext) {
            let app_state = init(cx);
            let (app, cx) = open(&app_state, cx);
            let item = open_tab(&app.workspace, loaded, (entry, Form::Decompile), cx);
            let tab = Self {
                item,
                binary: app.binary,
            };
            (tab, cx)
        }

        /// Returns the editor the tab shows its lines in now.
        pub(crate) fn editor(&self, cx: &mut VisualTestContext) -> Entity<Editor> {
            self.item.read_with(cx, |item, _| item.editor().clone())
        }

        /// Returns the shown line and byte of the first token linking to `link`, and what
        /// the view says of it.
        fn find(&self, link: &Ref, cx: &mut VisualTestContext) -> (Point, String) {
            let code = self
                .item
                .read_with(cx, |item, _| item.code().unwrap().clone());
            token_of(&code, link)
        }

        /// Asks the editor's provider for the hover over the first token linking to `link`.
        fn ask(&self, link: &Ref, cx: &mut VisualTestContext) -> Task<Option<Vec<Hover>>> {
            let (at, _) = self.find(link, cx);
            let editor = self.editor(cx);
            cx.update(|_, cx| {
                let editor = editor.read(cx);
                let buffer = editor.buffer().read(cx).as_singleton().unwrap();
                let anchor = buffer.read(cx).snapshot().anchor_after(at);
                let provider = editor.semantics_provider().unwrap();
                provider.hover(&buffer, anchor, cx).unwrap()
            })
        }

        /// Closes the hover, puts the cursor on the first token linking to `link` and hovers
        /// it as Zed's hover action does, then lets the work settle.
        fn hover(&self, link: &Ref, cx: &mut VisualTestContext) {
            let (at, _) = self.find(link, cx);
            self.editor(cx).update_in(cx, |editor, window, cx| {
                hide_hover(editor, cx);
                editor.change_selections(SelectionEffects::no_scroll(), window, cx, |s| {
                    s.select_ranges([at..at]);
                });
                hover(editor, &HoverAction, window, cx);
            });
            cx.run_until_parked();
        }

        /// Returns the text of every hover popover the editor shows.
        fn shown(&self, cx: &mut VisualTestContext) -> Vec<String> {
            self.editor(cx).read_with(cx, |editor, cx| {
                let texts = hover_texts(editor);
                texts.map(|t| t.read(cx).source().to_string()).collect()
            })
        }

        /// Returns the hover text the editor shows once a peek of `found` with `counts`
        /// landed over the first token linking to `link`.
        fn filled(
            &self,
            link: &Ref,
            found: &Peek,
            counts: Option<&GradeCounts>,
            cx: &mut VisualTestContext,
        ) -> String {
            let (_, said) = self.find(link, cx);
            hover_text(&Markdown::escape(&said), &markdown_of(found, counts))
        }
    }

    /// Returns the shown line and byte of the first token of `code` linking to `link`, and
    /// what the view says of it.
    pub(crate) fn token_of(code: &CodeLines, link: &Ref) -> (Point, String) {
        let (row, col, said) = (0..code.len())
            .find_map(|row| {
                let (view, line) = code.get(row)?;
                let text = view.line(line)?;
                view.tokens(line).find_map(|(span, kind, at)| {
                    let said = describe(text.get(span.clone())?, kind, at);
                    (at == Some(link)).then_some((row, span.start, said))
                })
            })
            .unwrap();
        let at = Point::new(u32::try_from(row).unwrap(), u32::try_from(col).unwrap());
        (at, said)
    }

    /// Returns the texts of a hover's blocks.
    fn texts(hover: Option<Vec<Hover>>) -> Vec<String> {
        let hover = hover.unwrap().remove(0);
        hover.contents.into_iter().map(|block| block.text).collect()
    }

    /// Returns the label and flag of every running request.
    fn running(cx: &mut VisualTestContext) -> Vec<(SharedString, Cancel)> {
        let jobs = cx.update(|_, cx| Jobs::running(cx));
        jobs.into_iter()
            .map(|(_, label, flag)| (label, flag))
            .collect()
    }

    /// Returns the engine's peek at `r` in `loaded`.
    fn engine(loaded: &LoadedBinary, r: &Ref) -> Peek {
        run_engine(|| peek_blocking(loaded, r)).unwrap()
    }

    /// A cold hover over a call paints what the view says of it and a reading line at once,
    /// before the engine reads the callee, and lists the read under the callee's name.
    #[gpui::test]
    fn a_cold_hover_paints_the_token_first(cx: &mut TestAppContext) {
        let loaded = sample();
        let (tab, cx) = Tab::open(&loaded, CALLER, cx);
        let callee = Ref::Function(CALLEE);
        let first = tab.ask(&callee, cx).now_or_never();
        let (_, said) = tab.find(&callee, cx);
        let reading = format!("Reading {}…", Markdown::escape("sub_1030"));
        let said = Markdown::escape(&said).into_owned();
        assert_eq!(texts(first.unwrap()), [said, reading]);
        let labels: Vec<_> = running(cx).into_iter().map(|(label, _)| label).collect();
        assert_eq!(labels, ["Peeking sub_1030"]);
    }

    /// A hover over a call fills, when its read lands, with the engine's head of the
    /// callee and the counts of its check in the status bar's words; the next hover over it
    /// shows them at once, with no read.
    #[gpui::test]
    fn a_call_peeks_at_the_callees_head_and_counts(cx: &mut TestAppContext) {
        let loaded = sample();
        let (tab, cx) = Tab::open(&loaded, CALLER, cx);
        let callee = Ref::Function(CALLEE);
        tab.hover(&callee, cx);
        let counts = run_engine(|| grade_counts_blocking(&loaded, CALLEE)).unwrap();
        let found = engine(&loaded, &callee);
        assert!(matches!(found, Peek::Function(_)), "{found:?}");
        let want = tab.filled(&callee, &found, Some(&counts), cx);
        assert!(want.contains(&grades_text(&counts)));
        assert_eq!(tab.shown(cx), std::slice::from_ref(&want));
        let warm = texts(tab.ask(&callee, cx).now_or_never().unwrap());
        assert_eq!(hover_text(&warm[0], &warm[1]), want);
        assert!(running(cx).is_empty());
    }

    /// A recheck of a function drops its kept peek, and the next hover over it shows the
    /// counts the status bar shows, the recheck's.
    #[gpui::test]
    fn a_recheck_shows_in_the_next_peek(cx: &mut TestAppContext) {
        let loaded = sample();
        let (tab, cx) = Tab::open(&loaded, CALLER, cx);
        let caller = Ref::Function(CALLER);
        tab.hover(&caller, cx);
        let before = run_engine(|| grade_counts_blocking(&loaded, CALLER)).unwrap();
        assert!(tab.shown(cx)[0].contains(&grades_text(&before)));
        let check = run_engine(|| check_blocking(&loaded, CALLER));
        let at = (loaded.state(), CALLER);
        tab.binary
            .update(cx, |b, cx| b.put_recheck(at, &check, wrong_at(CALLER), cx));
        cx.run_until_parked();
        let rechecked = tab
            .binary
            .read_with(cx, |b, _| b.rechecked(&loaded.state(), CALLER));
        let after = GradeCounts::of(rechecked.unwrap().as_ref().as_ref().unwrap());
        assert_eq!(after.disagree, before.disagree + 1);
        tab.hover(&caller, cx);
        let found = engine(&loaded, &caller);
        let want = tab.filled(&caller, &found, Some(&after), cx);
        assert_eq!(tab.shown(cx), [want]);
    }

    /// A new hover raises the flag of the read before it at once. A pointer that leaves
    /// before the hover shows makes Zed drop its hover task without telling the editor's
    /// observers: the read runs on until it lands, then is dropped with no hover filled,
    /// and its peek is kept.
    #[gpui::test]
    fn leaving_the_token_drops_the_peek_when_it_lands(cx: &mut TestAppContext) {
        let loaded = sample();
        let (tab, cx) = Tab::open(&loaded, CALLER, cx);
        let first = tab.ask(&Ref::Function(CALLEE), cx);
        let flag = running(cx).remove(0).1;
        let second = tab.ask(&Ref::Function(CALLER), cx);
        assert!(flag.is_raised());
        tab.editor(cx).update_in(cx, |editor, window, cx| {
            hover_at(editor, None, None, window, cx);
        });
        assert_eq!(running(cx).len(), 1, "the read runs until it lands");
        drop((first, second));
        cx.run_until_parked();
        assert!(running(cx).is_empty());
        assert!(tab.shown(cx).is_empty());
        let kept = texts(tab.ask(&Ref::Function(CALLER), cx).now_or_never().unwrap());
        assert!(running(cx).is_empty(), "a kept peek reads nothing");
        assert!(!kept[1].starts_with("Reading"), "{kept:?}");
    }

    /// Returns a program whose function at `0x1000` reads the 32-bit global at [`GLOBAL`],
    /// in a writable section holding the bytes 1 to 32, with `ty` applied there.
    fn global_reader(ty: Option<TypeExpr>) -> Arc<LoadedBinary> {
        let mut bytes = vec![0u8; 0x200];
        bytes[..0x100].fill(0xcc);
        // ASM: mov eax, dword ptr [rip+0xfa] ; ret
        bytes[..7].copy_from_slice(&[0x8b, 0x05, 0xfa, 0x00, 0x00, 0x00, 0xc3]);
        for (byte, value) in bytes[0x100..0x120].iter_mut().zip(1u8..) {
            *byte = value;
        }
        let sections = vec![
            Section::mapped(".text", 0x1000, 0, 0x100, false, true),
            Section::mapped(".data", GLOBAL, 0x100, 0x100, true, false),
        ];
        let mut program = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), sections);
        program.format = BinaryFormat::Pe;
        let analysis = Analysis::compute(&program);
        loaded_of(program, analysis, typed(ty))
    }

    /// Returns a load's overlay with `ty` applied at [`GLOBAL`].
    fn typed(ty: Option<TypeExpr>) -> Overlay {
        let mut overlay = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        overlay.applied.extend(ty.map(|ty| (GLOBAL, ty)));
        overlay
    }

    /// A hover over an untyped global fills with the engine's hexdump row of it; after an
    /// edit applies a type there, the tab's next hover fills with the engine's read of the
    /// type over its bytes.
    #[gpui::test]
    fn a_retyped_global_peeks_as_its_new_type(cx: &mut TestAppContext) {
        let untyped = global_reader(None);
        let (tab, cx) = Tab::open(&untyped, 0x1000, cx);
        let global = Ref::Global(GLOBAL);
        tab.hover(&global, cx);
        let found = engine(&untyped, &global);
        assert!(matches!(found, Peek::Global(Read::Bytes, _)), "{found:?}");
        assert_eq!(tab.shown(cx), [tab.filled(&global, &found, None, cx)]);
        let ty = TypeExpr::Array(Box::new(TypeExpr::U32), 4);
        let retyped = untyped.with_overlay(typed(Some(ty.clone())));
        tab.binary.update(cx, |binary, cx| {
            binary.show_loaded(retyped.clone(), cx);
            cx.emit(BinaryEvent::Revised(retyped.clone()));
        });
        cx.run_until_parked();
        tab.hover(&global, cx);
        let (p, a, o) = (&*retyped.program, &*retyped.analysis, &*retyped.overlay);
        let read = typed_tsv(p, Some(a), o, GLOBAL, &ty).unwrap();
        let found = engine(&retyped, &global);
        assert!(matches!(found, Peek::Global(Read::Typed, _)), "{found:?}");
        let shown = tab.shown(cx);
        assert_eq!(shown, [tab.filled(&global, &found, None, cx)]);
        assert!(shown[0].contains(read.lines().nth(1).unwrap()), "{shown:?}");
    }

    /// A hover over an import fills with what the engine knows of it: its declaration
    /// under a name the file states.
    #[gpui::test]
    fn an_import_peeks_as_its_declaration(cx: &mut TestAppContext) {
        let loaded = imported();
        let (tab, cx) = Tab::open(&loaded, 0x1000, cx);
        let import = Ref::Import(0x2000);
        tab.hover(&import, cx);
        let found = engine(&loaded, &import);
        let Peek::Import { decl, .. } = &found else {
            panic!("an import peek: {found:?}");
        };
        let want = tab.filled(&import, &found, None, cx);
        if let Some(decl) = decl {
            assert!(want.contains(&decl.lines.join("\n")));
        }
        assert_eq!(tab.shown(cx), [want]);
    }

    /// Returns a head of `lines` of a text of `total` lines.
    fn head(lines: &[&str], total: usize) -> Head {
        Head {
            lines: lines.iter().map(|&l| l.to_owned()).collect(),
            total,
        }
    }

    /// An inferred import's declaration says its name is inferred; an unresolved import
    /// shows no declaration and says it is unresolved; a cut head says how many lines it
    /// leaves out.
    #[test]
    fn a_peek_says_what_it_does_not_know_and_what_it_left_out() {
        let decl = head(&["void Sleep(DWORD ms);"], 1);
        let inferred = Peek::Import {
            name: Some("Sleep".to_owned()),
            certainty: Certainty::Inferred,
            decl: Some(decl.clone()),
        };
        let text = markdown_of(&inferred, None);
        assert!(
            text.contains("inferred") && text.contains(&decl.lines[0]),
            "{text}"
        );
        let unresolved = Peek::Import {
            name: Some("KERNEL32_ord5".to_owned()),
            certainty: Certainty::Unresolved,
            decl: None,
        };
        let text = markdown_of(&unresolved, None);
        let name = Markdown::escape("KERNEL32_ord5");
        let want = format!("Unresolved import {name}: no one name is known for this slot.");
        assert_eq!(text, want);
        let nameless = Peek::Import {
            name: None,
            certainty: Certainty::Unresolved,
            decl: None,
        };
        let text = markdown_of(&nameless, None);
        assert_eq!(
            text,
            "Unresolved import: no one name is known for this slot."
        );
        let cut = markdown_of(&Peek::Function(head(&["int f(void)", "{"], 30)), None);
        assert!(cut.ends_with("28 more lines"), "{cut}");
        let one = markdown_of(&Peek::Function(head(&["int f(void)"], 2)), None);
        assert!(one.ends_with("1 more line"), "{one}");
        let whole = markdown_of(&Peek::Function(head(&["int f(void)"], 1)), None);
        assert!(!whole.contains("more line"), "{whole}");
    }

    /// Names and reasons from the file are escaped, never read as Markdown, and a line
    /// holding a backtick fence is fenced longer.
    #[test]
    fn the_files_text_is_never_markdown() {
        let link = "[x](https://example.com)";
        let why = markdown_of(&Peek::Unknown(link.to_owned()), None);
        assert_eq!(why, Markdown::escape(link));
        assert_ne!(why, link);
        let named = Peek::Import {
            name: Some(link.to_owned()),
            certainty: Certainty::Unresolved,
            decl: None,
        };
        assert!(!markdown_of(&named, None).contains(link));
        let bytes = Peek::Global(Read::Bytes, head(&["a ``` b"], 1));
        let fenced = markdown_of(&bytes, None);
        assert!(
            fenced.starts_with("````\n") && fenced.ends_with("\n````"),
            "{fenced}"
        );
    }
}
