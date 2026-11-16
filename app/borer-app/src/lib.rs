//! Desktop GPUI application over [`borer_engine`], hosted in Zed's workspace.

pub mod actions;
pub mod app_assets;
pub mod app_settings;
pub mod app_view;
pub mod binary;
pub mod code_semantics;
pub mod code_view;
pub mod decompile_item;
pub mod function_columns;
pub mod functions_panel;
pub mod goto;
pub mod measure;
pub mod menus;
pub mod rail;
pub mod recent;
pub mod shell;
pub mod start_item;
pub mod status;
pub mod title_bar;
pub mod worker;

use gpui::{App, AppContext as _};

use crate::measure::{CliMode, Harness, new_cli_exit_slot, parse_cli_args, run_headless};
use crate::worker::mark_ui_thread;

/// Boots the GPUI platform (or `--headless` mode) according to CLI flags.
///
/// `borer-app [binary]` opens a window whose root is Zed's workspace; a measurement flag
/// opens a [`Harness`] around that workspace instead.
///
/// # Errors
///
/// Returns an error if CLI flags are invalid, the data directory cannot be set up, Zed's
/// fonts or keymaps do not load, opening the window fails, or a non-interactive CLI mode
/// (`--headless`, `--report-open`, `--measure-memory`, `--measure`) fails to load or
/// measure its target binary.
pub fn run() -> anyhow::Result<()> {
    let (mode, given_dir) = parse_cli_args()?;
    if let CliMode::Headless(path) = mode {
        return run_headless(path);
    }
    app_view::set_data_dir(&app_view::data_dir(&mode, given_dir)?)?;
    let exit_slot = new_cli_exit_slot();
    let app_slot = exit_slot.clone();
    gpui_platform::application()
        .with_assets(app_assets::AppAssets)
        .run(move |cx: &mut App| {
            mark_ui_thread();
            let opened = app_view::init(cx).and_then(|app_state| {
                let options = app_view::window_options(cx);
                let harness_slot = app_slot.clone();
                match mode {
                    CliMode::Interactive(path) => {
                        app_view::open_window(&app_state, path, cx).map(drop)
                    }
                    measured @ (CliMode::FirstFrame
                    | CliMode::ReportOpen(_)
                    | CliMode::Headless(_)
                    | CliMode::MeasureMemory(_)
                    | CliMode::Measure(_)
                    | CliMode::MeasureDrop(..)) => cx
                        .open_window(options, |window, cx| {
                            cx.new(|cx| {
                                Harness::new(measured, harness_slot, &app_state, window, cx)
                            })
                        })
                        .and_then(|window| app_view::activate(window.into(), cx)),
                }
            });
            if let Err(err) = opened {
                *app_slot.borrow_mut() = Some(err);
                cx.quit();
            }
        });
    exit_slot.borrow_mut().take().map_or(Ok(()), Err)
}
