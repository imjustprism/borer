//! The person's settings file lives in the app's config directory, apart from the config
//! directory Zed's own writer uses, and Zed's actions that change a setting write the
//! app's file.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_app::app_dirs::{set_config_dir, settings_file};
use borer_app::app_view::{configure, new_workspace, set_data_dir};
use borer_app::shell::Shell;
use fs::Fs as _;
use gpui::TestAppContext;
use workspace::AppState;

/// Zed's theme-mode toggle writes the mode into the app's settings file, and Zed's own
/// settings file under the data directory stays unwritten.
#[gpui::test]
async fn zeds_theme_mode_toggle_writes_the_apps_settings_file(cx: &mut TestAppContext) {
    let root = std::env::temp_dir().join("borer-app-settings-home");
    set_config_dir(root.join("config-home"));
    set_data_dir(&root.join("data")).expect("the data dir");
    let app_state = cx.update(|cx| {
        cx.set_global(db::AppDatabase::test_new());
        AppState::test(cx)
    });
    let file = settings_file();
    let fs = app_state.fs.clone();
    let folder = file.parent().expect("the file sits in a folder");
    fs.as_fake()
        .create_dir(folder)
        .await
        .expect("the folder is made");
    cx.update(configure).expect("the app configures Zed");
    let (_, cx) = cx.add_window_view(|window, cx| {
        Shell::new(new_workspace(&app_state, None, window, cx), window, cx)
    });
    cx.run_until_parked();
    cx.dispatch_action(zed_actions::theme::ToggleMode);
    cx.run_until_parked();
    let written = fs.load(&file).await.expect("the app's file is there");
    assert!(written.contains("\"mode\""), "{written}");
    assert!(
        fs.metadata(paths::settings_file())
            .await
            .expect("stated")
            .is_none()
    );
}
