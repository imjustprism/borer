//! The window's root: the app's title bar over the full width, then the rail beside Zed's
//! workspace; the rail runs to the window's foot and the status bar starts right of it.
//!
//! Zed's [`Workspace`] draws its own docks, panes and status bar and has no slot left of
//! them, and its title bar slot sits inside its client-side decorations, so the app's
//! chrome that spans the window lives here, around Zed's [`MultiWorkspace`]. The root also
//! carries the workspace's key context and actions, as Zed's own root does, so a key
//! pressed while nothing has focus still reaches them.

use anyhow::Context as _;
use gpui::{
    App, AppContext as _, Context, Entity, InteractiveElement as _, IntoElement,
    ParentElement as _, Render, SharedString, Styled as _, Task, TaskExt as _, Window,
    WindowHandle, div,
};
use workspace::notifications::simple_message_notification::MessageNotification;
use workspace::notifications::{NotificationId, dismiss_app_notification, show_app_notification};
use workspace::{CloseIntent, CloseWindow, MultiWorkspace, Workspace};

use crate::actions::OpenMenuBar;
use crate::app_view::AppWindow;
use crate::binary::Binary;
use crate::rail::Rail;
use crate::title_bar::TitleBar;

/// The window's root view.
pub struct Shell {
    /// The window's workspace and binary.
    app: AppWindow,
    /// Zed's root over the workspace, drawn below the title bar.
    root: Entity<MultiWorkspace>,
    /// The app's title bar.
    title_bar: Entity<TitleBar>,
    /// The rail left of the docks.
    rail: Entity<Rail>,
}

impl std::fmt::Debug for Shell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Shell").finish_non_exhaustive()
    }
}

impl Shell {
    /// Returns the root over `app`'s workspace; the binary asks its questions in this
    /// window, and the system's close of the window goes through [`Self::close`], as Zed's
    /// own root's does.
    ///
    /// # Arguments
    ///
    /// * `app` - The window's workspace and binary, from [`crate::app_view::new_workspace`].
    /// * `window` - The window.
    /// * `cx` - Shell context.
    #[must_use]
    pub fn new(app: AppWindow, window: &mut Window, cx: &mut Context<'_, Self>) -> Self {
        let root = cx.new(|cx| MultiWorkspace::new(app.workspace.clone(), window, cx));
        let title_bar = cx.new(|cx| TitleBar::new(app.binary.clone(), window, cx));
        let rail = cx.new(|cx| Rail::new(&app.workspace, app.binary.clone(), cx));
        let handle = window.window_handle();
        app.binary.update(cx, |binary, _| binary.set_window(handle));
        let shell = cx.weak_entity();
        window.on_window_should_close(cx, move |window, cx| {
            shell
                .update(cx, |shell, cx| shell.close(window, cx))
                .is_err()
        });
        Self {
            app,
            root,
            title_bar,
            rail,
        }
    }

    /// Returns the window's workspace.
    #[must_use]
    pub const fn workspace(&self) -> &Entity<Workspace> {
        &self.app.workspace
    }

    /// Returns the window's binary.
    #[must_use]
    pub const fn binary(&self) -> &Entity<Binary> {
        &self.app.binary
    }

    /// Returns the rail.
    #[must_use]
    pub const fn rail(&self) -> &Entity<Rail> {
        &self.rail
    }

    /// Returns the title bar.
    #[must_use]
    pub const fn title_bar(&self) -> &Entity<TitleBar> {
        &self.title_bar
    }
}

impl Shell {
    /// Asks whether the binary's edits no project file holds may go as `doing` drops them
    /// ([`Binary::settled`]).
    ///
    /// # Arguments
    ///
    /// * `doing` - What drops them, as the question words it.
    /// * `cx` - Application context.
    ///
    /// # Returns
    ///
    /// Whether to go on.
    pub fn settled(&self, doing: &str, cx: &mut App) -> Task<bool> {
        self.app
            .binary
            .update(cx, |binary, cx| binary.settled(doing, cx))
    }

    /// Returns the flushes of everything the window's root has yet to save, as Zed's own
    /// root gives them.
    ///
    /// # Arguments
    ///
    /// * `window` - The window.
    /// * `cx` - Shell context.
    fn flushes(&self, window: &mut Window, cx: &mut Context<'_, Self>) -> Vec<Task<()>> {
        self.root
            .update(cx, |root, cx| root.flush_pending_serialization(window, cx))
    }

    /// Closes the window as Zed's root closes one whose root it is: asks whether the
    /// binary's unsaved edits may go ([`Binary::settled`]), asks the workspace to prepare
    /// (unsaved work may keep it open), saves what is pending, then removes it.
    ///
    /// # Arguments
    ///
    /// * `window` - The window.
    /// * `cx` - Shell context.
    fn close(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let settled = self.settled("closing the window", cx);
        cx.spawn_in(window, async move |this, cx| {
            if !settled.await {
                return anyhow::Ok(());
            }
            let prepare = this.update_in(cx, |shell, window, cx| {
                shell.app.workspace.update(cx, |workspace, cx| {
                    workspace.prepare_to_close(CloseIntent::CloseWindow, window, cx)
                })
            })?;
            if !prepare.await.context("preparing the window to close")? {
                return anyhow::Ok(());
            }
            let flushes = this.update_in(cx, |shell, window, cx| shell.flushes(window, cx))?;
            for flush in flushes {
                flush.await;
            }
            cx.update(|window, _| window.remove_window())
                .context("removing the closed window")
        })
        .detach_and_log_err(cx);
    }
}

/// Quits the app once no window's binary holds edits that no project file holds.
///
/// Each window, one after another, asks to save or discard such edits
/// ([`Binary::settled`]); a Cancel in any window keeps the app running.
///
/// # Arguments
///
/// * `cx` - Application context listing the windows.
pub fn quit(cx: &mut App) {
    let shells: Vec<WindowHandle<Shell>> = cx
        .windows()
        .into_iter()
        .filter_map(|window| window.downcast::<Shell>())
        .collect();
    cx.spawn(async move |cx| {
        for shell in shells {
            let settled = shell.update(cx, |shell, _, cx| shell.settled("quitting", cx));
            if let Ok(settled) = settled
                && !settled.await
            {
                return;
            }
        }
        cx.update(|cx| cx.quit());
    })
    .detach();
}

/// Returns a flush of every app window's pending layout to Zed's database, as Zed's own
/// workspace init does on quit for windows whose root is its [`MultiWorkspace`].
///
/// # Arguments
///
/// * `cx` - Application context listing the windows.
pub fn flush_windows(cx: &mut App) -> impl Future<Output = ()> + use<> {
    let flushes: Vec<Task<()>> = cx
        .windows()
        .into_iter()
        .filter_map(|window| window.downcast::<Shell>())
        .filter_map(|window| {
            window
                .update(cx, |shell, window, cx| shell.flushes(window, cx))
                .ok()
        })
        .flatten()
        .collect();
    async move {
        for flush in flushes {
            flush.await;
        }
    }
}

impl Render for Shell {
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let menu_bar = self.title_bar.read(cx).menu_bar().clone();
        let ui_font = theme_settings::setup_ui_font(window, cx);
        let workspace = self.app.workspace.clone();
        let key_context = workspace.read(cx).key_context(cx);
        let actions = workspace.update(cx, |workspace, cx| workspace.actions(div(), window, cx));
        actions
            .key_context(key_context)
            .font(ui_font)
            .size_full()
            .flex()
            .flex_col()
            .on_action(move |_: &OpenMenuBar, window, cx| {
                menu_bar.update(cx, |bar, cx| bar.open_first(window, cx));
            })
            .capture_action(cx.listener(|shell, _: &CloseWindow, window, cx| {
                cx.stop_propagation();
                shell.close(window, cx);
            }))
            .child(self.title_bar.clone())
            .child(
                div()
                    .flex_1()
                    .min_h_0()
                    .flex()
                    .flex_row()
                    .child(self.rail.clone())
                    .child(div().flex_1().min_w_0().h_full().child(self.root.clone())),
            )
    }
}

/// Shows the app-wide notice `id` saying `text` in every window's workspace, and in each
/// workspace opened after, until [`dismiss_app_notice`] takes it back.
///
/// Zed's own app notifications reach only the windows whose root is its
/// [`MultiWorkspace`]; the app's root is its [`Shell`], so each shell's workspace is shown
/// the notice too, once the current update ends.
///
/// # Arguments
///
/// * `id` - The notice's id; showing it again replaces it.
/// * `text` - What it says.
/// * `cx` - Application context.
pub fn show_app_notice(id: NotificationId, text: SharedString, cx: &mut App) {
    let shown = text.clone();
    show_app_notification(id.clone(), cx, move |cx| {
        cx.new(|cx| MessageNotification::new(shown.clone(), cx))
    });
    each_workspace(cx, move |workspace, cx| {
        let text = text.clone();
        workspace.show_notification(id.clone(), cx, |cx| {
            cx.new(|cx| MessageNotification::new(text, cx))
        });
    });
}

/// Takes back the app-wide notice `id` from every window's workspace.
///
/// # Arguments
///
/// * `id` - The notice's id.
/// * `cx` - Application context.
pub fn dismiss_app_notice(id: &NotificationId, cx: &mut App) {
    dismiss_app_notification(id, cx);
    let id = id.clone();
    each_workspace(cx, move |workspace, cx| {
        workspace.dismiss_notification(&id, cx);
    });
}

/// Runs `f` on the workspace of every shell window, once the current update ends, so no
/// window being updated is reached.
///
/// # Arguments
///
/// * `cx` - Application context listing the windows.
/// * `f` - What to do in each workspace.
fn each_workspace(cx: &mut App, f: impl Fn(&mut Workspace, &mut Context<'_, Workspace>) + 'static) {
    cx.defer(move |cx| {
        let shells = cx
            .windows()
            .into_iter()
            .filter_map(|window| window.downcast::<Shell>());
        let workspaces: Vec<_> = shells
            .filter_map(|shell| {
                shell
                    .read_with(cx, |shell, _| shell.workspace().clone())
                    .ok()
            })
            .collect();
        for workspace in workspaces {
            workspace.update(cx, |workspace, cx| f(workspace, cx));
        }
    });
}

#[cfg(test)]
mod tests {
    use borer_engine::analysis::edit::Edit;
    use gpui::{TestAppContext, VisualTestContext};

    use workspace::notifications::NotificationId;

    use super::{Shell, dismiss_app_notice, show_app_notice};
    use crate::actions::{CloseBinary, OpenMenuBar};
    use crate::app_view::tests::{CALLEE, init, load_sample, open};

    /// Returns the window's root.
    ///
    /// # Panics
    ///
    /// Panics if the root is not the app's [`Shell`].
    fn shell(cx: &mut VisualTestContext) -> gpui::Entity<Shell> {
        cx.update(|window, _| window.root::<Shell>())
            .flatten()
            .unwrap()
    }

    /// The root holds the window's workspace and binary under the title bar, and the menu
    /// bar's key opens its first menu from wherever focus is, nothing focused included.
    ///
    /// # Panics
    ///
    /// Panics if the root holds another workspace or the key opens nothing.
    #[gpui::test]
    fn the_menu_bar_key_opens_the_first_menu(cx: &mut TestAppContext) {
        the_menu_bar_key_opens_the_first_menu_steps(cx);
    }

    /// Runs the steps of [`the_menu_bar_key_opens_the_first_menu`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_menu_bar_key_opens_the_first_menu`] says.
    fn the_menu_bar_key_opens_the_first_menu_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let shell = shell(cx);
        shell.read_with(cx, |shell, _| {
            assert_eq!(shell.workspace(), &app.workspace);
            assert_eq!(shell.binary(), &app.binary);
        });
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
        cx.dispatch_action(OpenMenuBar);
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
        let bar = shell.read_with(cx, |shell, cx| {
            shell.title_bar().read(cx).menu_bar().clone()
        });
        let open = bar.read_with(cx, |bar, _| bar.open_menu());
        let want = if cfg!(target_os = "macos") {
            None
        } else {
            Some(0)
        };
        assert_eq!(open, want);
    }

    /// Zed's close window action closes the app's window, its root being the shell.
    ///
    /// # Panics
    ///
    /// Panics if the window stays.
    #[gpui::test]
    fn close_window_closes_the_window(cx: &mut TestAppContext) {
        close_window_closes_the_window_steps(cx);
    }

    /// Runs the steps of [`close_window_closes_the_window`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`close_window_closes_the_window`] says.
    fn close_window_closes_the_window_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (_, cx) = open(&app_state, cx);
        cx.run_until_parked();
        cx.dispatch_action(workspace::CloseWindow);
        cx.run_until_parked();
        assert!(cx.cx.update(|cx| cx.windows()).is_empty());
    }

    /// Close Binary, Quit and closing the window, over edits no project file holds, each
    /// ask first and do nothing on Cancel; the window closes on Discard.
    ///
    /// # Panics
    ///
    /// Panics if one goes unasked, or Cancel drops the binary or the window.
    #[gpui::test]
    fn closing_over_unsaved_edits_asks_first(cx: &mut TestAppContext) {
        closing_over_unsaved_edits_asks_first_steps(cx);
    }

    /// Runs the steps of [`closing_over_unsaved_edits_asks_first`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`closing_over_unsaved_edits_asks_first`] says.
    fn closing_over_unsaved_edits_asks_first_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        load_sample(&app, cx);
        let rename = Edit::Name {
            at: CALLEE,
            name: "unsaved".to_owned(),
        };
        app.binary
            .update(cx, |binary, cx| binary.edit(vec![rename], cx));
        cx.run_until_parked();
        assert!(app.binary.read_with(cx, |binary, _| binary.is_unsaved()));
        let asks: [Box<dyn gpui::Action>; 3] = [
            Box::new(CloseBinary),
            Box::new(zed_actions::Quit),
            Box::new(workspace::CloseWindow),
        ];
        for action in asks {
            let name = action.name();
            cx.update(|window, cx| window.dispatch_action(action, cx));
            cx.run_until_parked();
            assert!(cx.has_pending_prompt(), "{name}");
            cx.simulate_prompt_answer("Cancel");
            cx.run_until_parked();
            assert!(
                app.binary
                    .read_with(cx, |binary, _| binary.loaded().is_some())
            );
            assert_eq!(cx.cx.update(|cx| cx.windows()).len(), 1, "{name}");
        }
        cx.dispatch_action(workspace::CloseWindow);
        cx.run_until_parked();
        cx.simulate_prompt_answer("Discard");
        cx.run_until_parked();
        assert!(cx.cx.update(|cx| cx.windows()).is_empty());
    }

    /// An app-wide notice reaches the workspace of every shell window, each of two, and is
    /// taken back from both.
    ///
    /// # Panics
    ///
    /// Panics if a window misses the notice or keeps it.
    #[gpui::test]
    fn an_app_notice_reaches_every_shell_window(cx: &mut TestAppContext) {
        an_app_notice_reaches_every_shell_window_steps(cx);
    }

    /// Runs the steps of [`an_app_notice_reaches_every_shell_window`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`an_app_notice_reaches_every_shell_window`] says.
    fn an_app_notice_reaches_every_shell_window_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (one, _) = open(&app_state, cx);
        let (two, cx) = open(&app_state, cx);
        let id = NotificationId::named("borer test notice".into());
        let shown = |cx: &mut VisualTestContext| {
            [&one, &two].map(|app| {
                app.workspace
                    .read_with(cx, |workspace, _| workspace.has_notification(&id))
            })
        };
        cx.update(|_, cx| show_app_notice(id.clone(), "a notice".into(), cx));
        cx.run_until_parked();
        assert_eq!(shown(cx), [true, true]);
        cx.update(|_, cx| dismiss_app_notice(&id, cx));
        cx.run_until_parked();
        assert_eq!(shown(cx), [false, false]);
    }
}
