//! The window's root: the app's title bar over the full width, then Zed's workspace.
//!
//! Zed's [`Workspace`] draws its own docks, panes and status bar and has no slot left of
//! them, and its title bar slot sits inside its client-side decorations, so the app's
//! chrome that spans the window lives here, around Zed's [`MultiWorkspace`]. The root also
//! carries the workspace's key context and actions, as Zed's own root does, so a key
//! pressed while nothing has focus still reaches them.

use anyhow::Context as _;
use gpui::{
    App, AppContext as _, Context, Entity, InteractiveElement as _, IntoElement,
    ParentElement as _, Render, Styled as _, Task, TaskExt as _, Window, div,
};
use workspace::{CloseIntent, CloseWindow, MultiWorkspace, Workspace};

use crate::actions::OpenMenuBar;
use crate::app_view::AppWindow;
use crate::binary::Binary;
use crate::title_bar::TitleBar;

/// The window's root view.
pub struct Shell {
    /// The window's workspace and binary.
    app: AppWindow,
    /// Zed's root over the workspace, drawn below the title bar.
    root: Entity<MultiWorkspace>,
    /// The app's title bar.
    title_bar: Entity<TitleBar>,
}

impl std::fmt::Debug for Shell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Shell").finish_non_exhaustive()
    }
}

impl Shell {
    /// Returns the root over `app`'s workspace.
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
        Self {
            app,
            root,
            title_bar,
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

    /// Returns the title bar.
    #[must_use]
    pub const fn title_bar(&self) -> &Entity<TitleBar> {
        &self.title_bar
    }
}

impl Shell {
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

    /// Closes the window as Zed's root closes one whose root it is: asks the workspace to
    /// prepare (unsaved work may keep it open), saves what is pending, then removes it.
    ///
    /// # Arguments
    ///
    /// * `window` - The window.
    /// * `cx` - Shell context.
    fn close(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let prepare = self.app.workspace.update(cx, |workspace, cx| {
            workspace.prepare_to_close(CloseIntent::CloseWindow, window, cx)
        });
        cx.spawn_in(window, async move |this, cx| {
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
            .child(div().flex_1().min_h_0().child(self.root.clone()))
    }
}

#[cfg(test)]
mod tests {
    use gpui::{TestAppContext, VisualTestContext};

    use super::Shell;
    use crate::actions::OpenMenuBar;
    use crate::app_view::tests::{init, open};

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
}
