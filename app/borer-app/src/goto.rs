//! Go to: Zed's picker over what the person types, found everywhere.
//!
//! The engine finds the text in every name table it holds, in the background, ranked into
//! one list: the place it spells as an address first, then functions, imports, exports,
//! symbols, strings, types, classes, user names and comments; a kind prefix (`@`, `"`,
//! `t:`, `#`) narrows it. Enter opens the function holding a hit, a listing at the hit when
//! a listing is the active view; a string, a type, a class or a hit in no function is named
//! in the status line. A miss shows the engine's own words, nearest names and all.

use std::sync::Arc;

use borer_engine::analysis::find::{Hit, HitKind};
use gpui::{App, Context, DismissEvent, Entity, Task, WeakEntity, Window};
use picker::{Picker, PickerDelegate};
use ui::{
    Color, HighlightedLabel, Label, LabelCommon as _, LabelSize, ListItem, ListItemSpacing,
    prelude::*,
};
use workspace::Workspace;

use crate::binary::Binary;
use crate::commands;
use crate::decompile_item::{DecompileItem, Form, TabMode};
use crate::places::{Opening, Place, open};
use crate::worker::{FindAnswer, LoadedBinary, find_blocking, spawn_engine};

gpui::actions!(
    borer,
    [
        /// Opens the go-to picker: an address or a name opens the function holding it, and
        /// every function, symbol, string, type and note whose text holds it is listed.
        GoTo,
        /// Opens the go-to picker to find a text in every function, symbol, string, type
        /// and note; `@`, `"`, `t:` and `#` narrow it to one kind.
        FindEverywhere,
    ]
);

/// Registers go to and find everywhere on `workspace`, each opening the one picker.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary, which the picker searches.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let (go, find) = (binary.clone(), binary.clone());
    commands::register(workspace, binary, move |workspace, _: &GoTo, window, cx| {
        toggle(workspace, &go, window, cx);
    });
    commands::register(
        workspace,
        binary,
        move |workspace, _: &FindEverywhere, window, cx| {
            toggle(workspace, &find, window, cx);
        },
    );
}

/// One line of the picker.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Match {
    /// One hit of the find: the engine's hit, the entry of the function holding its
    /// address, and the byte offsets of the characters of its text the needle matched.
    Hit {
        /// The engine's hit.
        hit: Hit,
        /// Entry of the function holding the hit's address, if any.
        entry: Option<u64>,
        /// Byte offsets of the matched characters of the hit's text.
        marks: Vec<usize>,
    },
    /// The engine's words for a text that matched nothing.
    Miss(String),
    /// A kind the find capped: what it is, how many of it are listed, and how many matched.
    Capped(HitKind, usize, usize),
    /// How many hits are listed, and how many matched in all.
    Count(usize, usize),
}

impl Match {
    /// Returns the entry this line opens and the address to show in it, `None` for a line
    /// that opens no code: a string (whose uses the xrefs panel lists), a type or a class
    /// (the types panel's), a hit in no function, or a line that is no hit.
    fn opens(&self) -> Option<(u64, Option<u64>)> {
        let Self::Hit {
            hit,
            entry: Some(entry),
            ..
        } = self
        else {
            return None;
        };
        match hit.kind() {
            HitKind::Address
            | HitKind::Function
            | HitKind::Import
            | HitKind::Export
            | HitKind::Symbol
            | HitKind::Name
            | HitKind::Comment => Some((*entry, hit.addr)),
            HitKind::String | HitKind::Type | HitKind::Class => None,
        }
    }

    /// Returns what Enter on this line opens from a tab showing `form`: the function in
    /// that view, a listing at the hit's address; `None` for a line that opens nothing.
    ///
    /// # Arguments
    ///
    /// * `form` - The view of the active code tab.
    fn place(&self, form: Form) -> Option<Place> {
        let (entry, at) = self.opens()?;
        let at = match form {
            Form::Listing => at,
            Form::Decompile => None,
        };
        Some(Place::Code { entry, form, at })
    }
}

/// Returns the status line naming a hit Enter opens no code for: its kind, its text and its
/// address when it has one.
///
/// # Arguments
///
/// * `hit` - The engine's hit.
fn named(hit: &Hit) -> String {
    let at = hit
        .addr
        .map_or_else(String::new, |va| format!(" at {va:#x}"));
    format!("{} {}{at}", hit.kind().word(), hit.text)
}

/// Returns the byte offsets of the characters of `text` that the first case-folded match
/// of `needle` covers; none when the needle is empty or matched elsewhere (an import's
/// module, a mangled name).
///
/// # Arguments
///
/// * `text` - A hit's text.
/// * `needle` - The needle, lowered as the engine matched it.
fn marks(text: &str, needle: &str) -> Vec<usize> {
    if needle.is_empty() {
        return Vec::new();
    }
    let from = |start: usize| {
        let mut lowered = String::new();
        let mut at = Vec::new();
        for (i, c) in text.get(start..)?.char_indices() {
            if lowered.len() >= needle.len() {
                break;
            }
            at.push(start + i);
            lowered.extend(c.to_lowercase());
        }
        lowered.starts_with(needle).then_some(at)
    };
    text.char_indices()
        .find_map(|(start, _)| from(start))
        .unwrap_or_default()
}

/// Returns the picker's lines for an answer: the miss when nothing matched, the hits best
/// first, a line for each capped kind, then how many of how many they are when the needle
/// is not empty.
///
/// # Arguments
///
/// * `answer` - What the engine found.
fn lines(answer: FindAnswer) -> Vec<Match> {
    let FindAnswer {
        found,
        entries,
        needle,
        miss,
    } = answer;
    let total = found.counted.iter().map(|&(_, count)| count).sum();
    let count = (!needle.is_empty()).then_some(Match::Count(found.hits.len(), total));
    let capped: Vec<_> = found
        .counted
        .iter()
        .filter_map(|&(kind, count)| {
            let kept = found.hits.iter().filter(|h| h.kind() == kind).count();
            (kept < count).then_some(Match::Capped(kind, kept, count))
        })
        .collect();
    let hits = found.hits.into_iter().zip(entries).map(|(hit, entry)| {
        let marks = marks(&hit.text, &needle);
        Match::Hit { hit, entry, marks }
    });
    miss.map(Match::Miss)
        .into_iter()
        .chain(hits)
        .chain(capped)
        .chain(count)
        .collect()
}

/// The go-to picker's state: the binary it searches and the lines of the latest answer.
#[derive(Debug)]
pub struct GoToDelegate {
    /// Workspace a confirmed line opens its function in.
    workspace: WeakEntity<Workspace>,
    /// The window's binary, which the opened tab holds.
    binary: Entity<Binary>,
    /// Binary the text is resolved in.
    loaded: Arc<LoadedBinary>,
    /// The view of the active code tab, which a confirmed line opens.
    form: Form,
    /// The lines of the latest answer.
    matches: Vec<Match>,
    /// The selected line.
    selected: usize,
}

/// Opens the go-to picker, empty, over the binary of the active code tab, else the
/// window's binary; nothing opens before a binary is loaded.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
fn toggle(
    workspace: &mut Workspace,
    binary: &Entity<Binary>,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    let tab = workspace.active_item_as::<DecompileItem>(cx);
    let form = tab
        .as_ref()
        .map_or(Form::Decompile, |item| item.read(cx).form());
    let tab = tab.map(|item| item.read(cx).loaded().clone());
    let binary = binary.clone();
    let Some(loaded) = tab.or_else(|| binary.read(cx).loaded().cloned()) else {
        return;
    };
    let delegate = GoToDelegate {
        workspace: workspace.weak_handle(),
        binary,
        loaded,
        form,
        matches: Vec::new(),
        selected: 0,
    };
    workspace.toggle_modal(window, cx, |window, cx| {
        Picker::uniform_list(delegate, window, cx)
    });
}

impl PickerDelegate for GoToDelegate {
    type ListItem = ListItem;

    fn name() -> &'static str {
        "borer go to"
    }

    fn match_count(&self) -> usize {
        self.matches.len()
    }

    fn selected_index(&self) -> usize {
        self.selected
    }

    fn set_selected_index(
        &mut self,
        ix: usize,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) {
        self.selected = ix;
    }

    fn can_select(
        &self,
        ix: usize,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> bool {
        self.matches
            .get(ix)
            .is_some_and(|m| matches!(m, Match::Hit { .. }))
    }

    fn placeholder_text(&self, _window: &mut Window, _cx: &mut App) -> Arc<str> {
        "Go to an address or a name; @ functions, \" strings, t: types, # notes".into()
    }

    fn update_matches(
        &mut self,
        query: String,
        _window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) -> Task<()> {
        let loaded = self.loaded.clone();
        let label = format!("Going to {}", query.trim());
        let answer = spawn_engine(label, cx, move || {
            lines(find_blocking(&loaded, query.trim()))
        });
        cx.spawn(async move |picker, cx| {
            let (Some(matches), Some(picker)) = (answer.await, picker.upgrade()) else {
                return;
            };
            picker.update(cx, |picker, cx| {
                let delegate = &mut picker.delegate;
                delegate.selected = matches
                    .iter()
                    .position(|m| matches!(m, Match::Hit { .. }))
                    .unwrap_or(0);
                delegate.matches = matches;
                cx.notify();
            });
        })
    }

    fn confirm(
        &mut self,
        _secondary: bool,
        window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) {
        let Some(line) = self.matches.get(self.selected) else {
            return;
        };
        let Some(place) = line.place(self.form) else {
            if let Match::Hit { hit, .. } = line {
                let status = named(hit);
                self.binary
                    .update(cx, |binary, cx| binary.set_status(status, cx));
                cx.emit(DismissEvent);
            }
            return;
        };
        let mode = match self.form {
            Form::Listing => TabMode::Preview,
            Form::Decompile => TabMode::Permanent,
        };
        let (workspace, binary, loaded) = (
            self.workspace.clone(),
            self.binary.clone(),
            self.loaded.clone(),
        );
        cx.emit(DismissEvent);
        window.defer(cx, move |window, cx| {
            let Some(workspace) = workspace.upgrade() else {
                return;
            };
            workspace.update(cx, |workspace, cx| {
                let how = Opening { mode, focus: true };
                open(workspace, &binary, &loaded, place, how, window, cx);
            });
        });
    }

    fn dismissed(&mut self, _window: &mut Window, cx: &mut Context<'_, Picker<Self>>) {
        cx.emit(DismissEvent);
    }

    fn render_match(
        &self,
        ix: usize,
        selected: bool,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> Option<Self::ListItem> {
        let line = match self.matches.get(ix)? {
            Match::Hit { hit, marks, .. } => hit_line(hit, marks),
            Match::Miss(miss) => muted(miss.clone()),
            Match::Capped(kind, kept, count) => {
                muted(format!("{}: showing {kept} of {count}", kind.word()))
            }
            Match::Count(shown, total) => muted(format!("showing {shown} of {total}")),
        };
        Some(
            ListItem::new(ix)
                .inset(true)
                .spacing(ListItemSpacing::Sparse)
                .toggle_state(selected)
                .child(line),
        )
    }
}

/// Returns a line of muted text.
///
/// # Arguments
///
/// * `text` - What it says.
fn muted(text: String) -> AnyElement {
    Label::new(text).color(Color::Muted).into_any_element()
}

/// Returns a hit's line: its kind, its text with the needle's characters highlighted, its
/// address, and how borer knows it, muted.
///
/// # Arguments
///
/// * `hit` - The engine's hit.
/// * `marks` - Byte offsets of the matched characters of its text.
fn hit_line(hit: &Hit, marks: &[usize]) -> AnyElement {
    let small = |text: String| Label::new(text).size(LabelSize::Small).color(Color::Muted);
    let addr = hit.addr.map_or_else(String::new, |va| format!("{va:#x}"));
    h_flex()
        .w_full()
        .gap_2()
        .child(
            div()
                .w(rems(4.5))
                .child(small(hit.kind().word().to_owned())),
        )
        .child(HighlightedLabel::new(hit.text.to_string(), marks.to_vec()))
        .child(small(addr))
        .child(small(hit.source.code()))
        .into_any_element()
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::find::{Hit, HitKind, KIND_MAX, Rank, Source};
    use borer_engine::analysis::resolve_suggesting;
    use borer_engine::strings::Encoding;
    use borer_engine::view::Ref;
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use picker::Picker;
    use workspace::Workspace;

    use super::{FindEverywhere, GoTo, GoToDelegate, Match, marks};
    use crate::app_view::tests::{CALLEE, CALLER, init, open, sample, take_status};
    use crate::decompile_item::tests::{active as tab, fourth_instruction, open_tab};
    use crate::decompile_item::{DecompileItem, Form, link_place};
    use crate::functions_panel::{Functions, FunctionsPanel};
    use crate::places::Place;
    use crate::rows_panel::RowKind as _;
    use crate::worker::{Jobs, LoadedBinary, decompile_blocking};

    /// Returns the sample with the user's `names` over it.
    fn named(names: impl IntoIterator<Item = (u64, String)>) -> Arc<LoadedBinary> {
        let plain = sample();
        let mut overlay = (*plain.overlay).clone();
        for (va, name) in names {
            overlay.names.insert(va, name);
        }
        Arc::new(LoadedBinary {
            path: plain.path.clone(),
            program: plain.program.clone(),
            analysis: plain.analysis.clone(),
            overlay: Arc::new(overlay),
            initial_rows: plain.initial_rows.clone(),
        })
    }

    /// Returns the sample with its caller and callee named `caller_fn` and `callee_fn`.
    fn named_calls() -> Arc<LoadedBinary> {
        named([
            (CALLER, "caller_fn".to_owned()),
            (CALLEE, "callee_fn".to_owned()),
        ])
    }

    /// Opens go to with its key from the focused code tab, types `query` and waits for the
    /// engine's answer.
    ///
    /// # Panics
    ///
    /// Panics if the picker does not open.
    fn ask(
        workspace: &Entity<Workspace>,
        query: &str,
        cx: &mut VisualTestContext,
    ) -> Entity<Picker<GoToDelegate>> {
        cx.simulate_keystrokes("g");
        cx.run_until_parked();
        let picker = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_modal::<Picker<GoToDelegate>>(cx)
            })
            .unwrap();
        picker.update_in(cx, |picker, window, cx| picker.set_query(query, window, cx));
        cx.run_until_parked();
        picker
    }

    /// Returns the lines the picker shows.
    fn shown(picker: &Entity<Picker<GoToDelegate>>, cx: &mut VisualTestContext) -> Vec<Match> {
        picker.read_with(cx, |picker, _| picker.delegate.matches.clone())
    }

    /// Returns the hits among `lines`.
    fn hits(lines: &[Match]) -> Vec<&Hit> {
        lines
            .iter()
            .filter_map(|line| match line {
                Match::Hit { hit, .. } => Some(hit),
                Match::Miss(_) | Match::Capped(..) | Match::Count(..) => None,
            })
            .collect()
    }

    /// Returns the entry of the active code tab.
    fn active(workspace: &Entity<Workspace>, cx: &mut VisualTestContext) -> Option<u64> {
        workspace.read_with(cx, |workspace, cx| {
            workspace
                .active_item_as::<DecompileItem>(cx)?
                .read(cx)
                .entry()
        })
    }

    /// Going to an address and to a name opens the function, and a near miss shows the
    /// engine's answer, nearest name and all, and opens nothing.
    ///
    /// # Panics
    ///
    /// Panics if go to opens the wrong function or says other than the engine.
    #[gpui::test]
    fn go_to_opens_what_the_engine_resolves(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = named_calls();
        open_tab(&workspace, &loaded, (CALLER, Form::Decompile), cx);
        for (query, want) in [
            (format!("{CALLEE:#x}"), CALLEE),
            ("caller_fn".to_owned(), CALLER),
        ] {
            ask(&workspace, &query, cx);
            cx.dispatch_action(menu::Confirm);
            cx.run_until_parked();
            assert_eq!(active(&workspace, cx), Some(want), "{query}");
        }
        let picker = ask(&workspace, "calee_fn", cx);
        let said = resolve_suggesting(
            &loaded.program,
            &loaded.analysis,
            &loaded.overlay,
            "calee_fn",
        );
        let miss = said.unwrap_err();
        assert!(miss.contains("callee_fn"), "{miss}");
        let lines = shown(&picker, cx);
        assert_eq!(lines.first().cloned(), Some(Match::Miss(miss)));
        assert_eq!(lines.last().cloned(), Some(Match::Count(0, 0)));
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        assert_eq!(active(&workspace, cx), Some(CALLER));
    }

    /// A query naming a string the program holds lists it as a string hit, at its address,
    /// with the needle's characters marked.
    ///
    /// # Panics
    ///
    /// Panics if the string is not listed.
    #[gpui::test]
    fn a_string_of_the_program_is_found(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        open_tab(&workspace, &sample(), (CALLER, Form::Decompile), cx);
        let picker = ask(&workspace, "world", cx);
        let lines = shown(&picker, cx);
        let string = lines.iter().find_map(|line| match line {
            Match::Hit { hit, marks, .. } if hit.kind() == HitKind::String => Some((hit, marks)),
            Match::Hit { .. } | Match::Miss(_) | Match::Capped(..) | Match::Count(..) => None,
        });
        let (hit, marks) = string.unwrap();
        assert_eq!((&*hit.text, hit.addr), ("hello world", Some(0x1100)));
        assert_eq!(marks, &[6, 7, 8, 9, 10]);
        let at = lines.iter().position(
            |line| matches!(line, Match::Hit { hit, .. } if hit.kind() == HitKind::String),
        );
        picker.update_in(cx, |picker, window, cx| {
            picker.set_selected_index(at.unwrap(), None, false, window, cx);
        });
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        assert_eq!(take_status(&app, cx), "string hello world at 0x1100");
        assert_eq!(active(&workspace, cx), Some(CALLER));
    }

    /// `@` and a function's name lists only functions, and Enter opens the function.
    ///
    /// # Panics
    ///
    /// Panics if another kind is listed or Enter opens another function.
    #[gpui::test]
    fn a_function_prefix_lists_only_functions(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = named_calls();
        open_tab(&workspace, &loaded, (CALLER, Form::Decompile), cx);
        let picker = ask(&workspace, "@callee", cx);
        let lines = shown(&picker, cx);
        let kinds: Vec<_> = hits(&lines).iter().map(|hit| hit.kind()).collect();
        assert_eq!(kinds, [HitKind::Function]);
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        assert_eq!(active(&workspace, cx), Some(CALLEE));
    }

    /// A kind with more matches than the engine keeps says how many it lists of how many
    /// matched, the engine's own total.
    ///
    /// # Panics
    ///
    /// Panics if the capped kind or the total is missing.
    #[gpui::test]
    fn a_capped_kind_shows_the_engines_total(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let many = KIND_MAX + 10;
        let names = (0..many).map(|i| (0x1110 + u64::try_from(i).unwrap(), format!("note_{i}")));
        open_tab(&workspace, &named(names), (CALLER, Form::Decompile), cx);
        let picker = ask(&workspace, "#note_", cx);
        let lines = shown(&picker, cx);
        assert!(lines.contains(&Match::Capped(HitKind::Name, KIND_MAX, many)));
        assert_eq!(lines.last().cloned(), Some(Match::Count(KIND_MAX, many)));
    }

    /// The matched characters of a hit's text are found in any case, by byte offset, and
    /// none are for an empty needle or a text that does not hold it.
    #[test]
    fn marks_cover_the_needle_in_any_case() {
        assert_eq!(marks("Hello World", "world"), [6, 7, 8, 9, 10]);
        assert_eq!(marks("\u{c4}bc", "\u{e4}b"), [0, 2]);
        assert!(marks("hello", "").is_empty());
        assert!(marks("kernel32", "createfile").is_empty());
    }

    /// What Enter opens is a place, named without a window.
    ///
    /// A functions row names its decompile view, a call's link the callee in the same view,
    /// a hit inside a function that function (a listing at the hit), and lines that open
    /// nothing name none.
    #[test]
    fn rows_links_and_go_to_lines_name_their_places() {
        let loaded = sample();
        let code = |entry, form, at| Place::Code { entry, form, at };
        let row = &loaded.initial_rows.rows[0];
        assert_eq!(
            Functions::place(row),
            Some(code(row.entry, Form::Decompile, None))
        );
        let view = decompile_blocking(&loaded, CALLER).unwrap();
        let call = Ref::Function(CALLEE);
        let link = |form| link_place(&view, &call, form);
        assert_eq!(link(Form::Listing), Some(code(CALLEE, Form::Listing, None)));
        assert_eq!(
            link(Form::Decompile),
            Some(code(CALLEE, Form::Decompile, None))
        );
        assert_eq!(
            link_place(&view, &Ref::Address(CALLER), Form::Decompile),
            None
        );
        let hit = |addr, entry, source| Match::Hit {
            hit: Hit {
                addr: Some(addr),
                text: "f".into(),
                cut: false,
                source,
                rank: Rank::Exact,
            },
            entry,
            marks: Vec::new(),
        };
        let va = CALLEE + 1;
        let inside = hit(va, Some(CALLEE), Source::User);
        assert_eq!(
            inside.place(Form::Listing),
            Some(code(CALLEE, Form::Listing, Some(va)))
        );
        assert_eq!(
            inside.place(Form::Decompile),
            Some(code(CALLEE, Form::Decompile, None))
        );
        assert_eq!(hit(0x1100, None, Source::User).place(Form::Listing), None);
        let string = Source::String {
            off: 0x100,
            section: None,
            encoding: Encoding::Ascii,
        };
        assert_eq!(hit(va, Some(CALLEE), string).place(Form::Listing), None);
        assert_eq!(Match::Miss("no".to_owned()).place(Form::Listing), None);
        assert_eq!(Match::Count(0, 0).place(Form::Listing), None);
    }

    /// Queries typed over one another before the engine answered list only the last
    /// query's answer; each query runs as a listed request.
    #[gpui::test]
    fn a_go_to_query_typed_over_lists_the_newest_answer(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        open_tab(&workspace, &sample(), (CALLER, Form::Decompile), cx);
        let picker = ask(&workspace, "", cx);
        let query = |text: &str, cx: &mut VisualTestContext| {
            picker.update_in(cx, |picker, window, cx| picker.set_query(text, window, cx));
            let jobs = cx.update(|_, cx| Jobs::running(cx));
            let label = format!("Going to {text}");
            let mut flags = jobs.into_iter().filter(|(_, l, _)| *l == label);
            flags.next().map(|(_, _, flag)| flag)
        };
        assert!(query("world", cx).is_some());
        query("0x1", cx);
        query(&format!("{CALLEE:#x}"), cx);
        cx.run_until_parked();
        let lines = shown(&picker, cx);
        assert_eq!(
            lines.first().and_then(Match::opens),
            Some((CALLEE, Some(CALLEE)))
        );
        let kinds: Vec<_> = hits(&lines).iter().map(|hit| hit.kind()).collect();
        assert!(!kinds.contains(&HitKind::String), "{kinds:?}");
    }

    /// Go to and find everywhere each have a key, and find everywhere's opens the picker
    /// empty from anywhere in the workspace.
    ///
    /// # Panics
    ///
    /// Panics if an action has no key or the picker does not open.
    #[gpui::test]
    fn find_everywhere_has_a_key_and_opens_the_picker(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        open_tab(&workspace, &sample(), (CALLER, Form::Decompile), cx);
        let keyed = cx.update(|_, cx| {
            let keymap = cx.key_bindings();
            let keymap = keymap.borrow();
            let actions: [&dyn gpui::Action; 2] = [&GoTo, &FindEverywhere];
            actions.map(|action| keymap.bindings_for_action(action).next().is_some())
        });
        assert_eq!(keyed, [true, true]);
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        cx.simulate_keystrokes("secondary-p");
        cx.run_until_parked();
        let picker = workspace.read_with(cx, |workspace, cx| {
            workspace.active_modal::<Picker<GoToDelegate>>(cx)
        });
        let query = picker.map(|picker| picker.read_with(cx, |picker, cx| picker.query(cx)));
        assert_eq!(query.as_deref(), Some(""));
    }

    /// ctrl-p in the open picker selects the line above, as in every Zed picker, and leaves
    /// the picker open: find everywhere's key does not take it there.
    ///
    /// # Panics
    ///
    /// Panics if the picker closes or the selection does not move up.
    #[gpui::test]
    fn ctrl_p_in_the_picker_selects_the_line_above(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        open_tab(&workspace, &named_calls(), (CALLER, Form::Decompile), cx);
        let picker = ask(&workspace, "@_fn", cx);
        let hits: Vec<usize> = shown(&picker, cx)
            .iter()
            .enumerate()
            .filter_map(|(ix, line)| matches!(line, Match::Hit { .. }).then_some(ix))
            .collect();
        let [above, below] = hits[..] else {
            panic!("two functions listed: {hits:?}");
        };
        picker.update_in(cx, |picker, window, cx| {
            picker.set_selected_index(below, None, false, window, cx);
        });
        cx.simulate_keystrokes("ctrl-p");
        cx.run_until_parked();
        let open = workspace.read_with(cx, |workspace, cx| {
            workspace.active_modal::<Picker<GoToDelegate>>(cx).is_some()
        });
        assert!(open, "ctrl-p closed the picker");
        let selected = picker.read_with(cx, |picker, _| picker.delegate.selected);
        assert_eq!(selected, above);
    }

    /// From a listing tab, going to an address inside a function opens that function's
    /// listing at the line of the instruction, and the picker counts the hits it shows.
    ///
    /// # Panics
    ///
    /// Panics if the listing opens elsewhere or the count is missing.
    #[gpui::test]
    fn go_to_from_a_listing_opens_the_instruction(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let (va, line) = fourth_instruction(&loaded);
        open_tab(&workspace, &loaded, (CALLER, Form::Listing), cx);
        let picker = ask(&workspace, &format!("{va:#x}"), cx);
        let last = shown(&picker, cx).last().cloned();
        assert!(matches!(last, Some(Match::Count(..))));
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        let shown = tab(&workspace, cx);
        assert_eq!(shown, Some((CALLER, Form::Listing, line)));
    }
}
