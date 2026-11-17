//! The app state the app's integration tests start from.

use std::sync::Arc;

use borer_app::app_view::{configure, set_data_dir};
use gpui::App;
use theme::{Appearance, SystemAppearance};
use workspace::AppState;

/// Points Zed's paths at one data directory of the tests, once per process, so no test
/// resolves the person's own Zed settings.
pub(crate) fn use_test_data_dir() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        set_data_dir(&std::env::temp_dir().join("borer-app-tests")).expect("the data dir");
    });
}

/// Starts Zed's test app state over a fresh in-memory database and file system, under a
/// dark system appearance, not yet configured.
pub(crate) fn start(cx: &mut App) -> Arc<AppState> {
    use_test_data_dir();
    cx.set_global(db::AppDatabase::test_new());
    let app_state = AppState::test(cx);
    *SystemAppearance::global_mut(cx) = SystemAppearance(Appearance::Dark);
    app_state
}

/// Starts Zed's test app state, configured as the app configures Zed.
pub(crate) fn boot(cx: &mut App) {
    start(cx);
    configure(cx).expect("the app configures Zed");
}
