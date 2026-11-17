//! borer's theme as a tested contract: the brand's surfaces, a color for every token the
//! engine draws, contrast floors, a check-grade ramp that survives color-vision deficiency,
//! no stock Zed color in a slot the app shows, and the app booting into it.
//!
//! The color maths are the app's own, in [`borer_app::theme_contract`], which a person's
//! theme is checked by too.

#![expect(
    clippy::expect_used,
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::path::{Path, PathBuf};
use std::sync::Arc;

use borer_app::actions::{FollowSystemTheme, SelectTheme, ToggleTheme};
use borer_app::app_dirs::Dirs;
use borer_app::app_settings::BORER_THEME;
use borer_app::app_view::{configure, new_workspace};
use borer_app::binary::{Binary, SettingsNotice, StatusLine};
use borer_app::code_view::{CodePalette, Role};
use borer_app::decompile_item::code_row_height;
use borer_app::functions_panel::FunctionsPanel;
use borer_app::shell::Shell;
use borer_app::theme_contract::{
    Failure, GRADES, TEXT_FLOOR, check, contrast, grade_rules, syntax_color, text_floors,
};
use borer_app::theme_import::{ImportReport, Origin, import, read_candidate, read_from};
use borer_app::theme_picker::ThemePicker;
use borer_app::user_themes::{MAX_FAMILY_THEMES, MAX_THEME_BYTES, MAX_THEME_ENTRIES, notice_id};
use borer_app::zed_import::zed_themes;
use borer_engine::program::checked_metadata;
use fs::Fs as _;
use futures::StreamExt as _;
use gpui::{
    AppContext as _, BorrowAppContext as _, Entity, ExternalPaths, FileDropEvent, Hsla,
    ReadGlobal as _, Refineable as _, Rgba, TestAppContext, VisualTestContext, px,
};
use project::DisableAiSettings;
use settings::{BufferLineHeight, Settings as _, SettingsStore, ThemeAppearanceMode, ThemeColor};
use theme::{
    ActiveTheme as _, Appearance, AppearanceContent, SystemAppearance, Theme, ThemeColors,
    ThemeColorsRefinement, ThemeRegistry,
};
use theme_settings::{
    ThemeContent, ThemeSettings, deserialize_user_theme, refine_theme, status_colors_refinement,
    theme_colors_refinement,
};
use workspace::{AppState, Workspace};

mod support;

use support::{boot, start, use_test_data_dir};

/// Slots of [`ThemeColors`] the borer theme leaves to Zed's defaults, each because the app
/// never draws it.
const UNDRAWN: [&str; 20] = [
    "editor_code_lens_foreground",
    "terminal_bright_foreground",
    "terminal_dim_foreground",
    "terminal_ansi_background",
    "terminal_ansi_bright_black",
    "terminal_ansi_dim_black",
    "terminal_ansi_bright_red",
    "terminal_ansi_dim_red",
    "terminal_ansi_bright_green",
    "terminal_ansi_dim_green",
    "terminal_ansi_bright_yellow",
    "terminal_ansi_dim_yellow",
    "terminal_ansi_bright_blue",
    "terminal_ansi_dim_blue",
    "terminal_ansi_bright_magenta",
    "terminal_ansi_dim_magenta",
    "terminal_ansi_bright_cyan",
    "terminal_ansi_dim_cyan",
    "terminal_ansi_bright_white",
    "terminal_ansi_dim_white",
];

/// Returns each theme of the bundled family as written and as Zed refines it.
fn themes() -> Vec<(ThemeContent, Theme)> {
    let family = deserialize_user_theme(BORER_THEME).expect("the bundled theme parses");
    assert_eq!(family.themes.len(), 2);
    family
        .themes
        .into_iter()
        .map(|content| {
            let refined = refine_theme(&content);
            (content, refined)
        })
        .collect()
}

/// Returns whether `color` is the opaque `0xRRGGBB` color `rgb`, to within rounding.
fn is(color: Hsla, rgb: u32) -> bool {
    let (got, want) = (Rgba::from(color), gpui::rgb(rgb));
    let channels = [
        (got.r, want.r),
        (got.g, want.g),
        (got.b, want.b),
        (got.a, 1.0),
    ];
    channels.iter().all(|(a, b)| (a - b).abs() < 1e-3)
}

/// Returns Zed's config directory under the tests' data directory, which it points Zed at
/// first, so no test resolves Zed's paths before the data directory is set.
fn config_dir() -> &'static PathBuf {
    use_test_data_dir();
    paths::config_dir()
}

/// Returns the settings file under the tests' data directory.
fn settings_file() -> &'static PathBuf {
    use_test_data_dir();
    paths::settings_file()
}

/// Returns the themes folder under the tests' data directory.
fn themes_dir() -> &'static PathBuf {
    use_test_data_dir();
    paths::themes_dir()
}

/// Starts Zed's test app state with `text` as its settings file, then configures
/// it as the app does.
async fn boot_with(text: Option<&str>, cx: &mut TestAppContext) -> Arc<AppState> {
    let app_state = cx.update(start);
    let path = settings_file();
    let fake = app_state.fs.as_fake();
    let parent = path.parent().expect("the settings file sits in a folder");
    fake.create_dir(parent).await.expect("the folder is made");
    match text {
        Some(text) => fake.insert_file(path, text.as_bytes().to_vec()).await,
        None => fake.create_dir(path).await.expect("the directory is made"),
    }
    cx.update(configure)
        .expect("the app configures Zed even so");
    app_state
}

/// Returns the theme shown.
fn shown(cx: &TestAppContext) -> String {
    cx.update(|cx| cx.theme().name.to_string())
}

/// Returns the theme mode the person's settings layer holds, if it holds a pair.
fn saved(cx: &TestAppContext) -> Option<ThemeAppearanceMode> {
    cx.update(|cx| {
        let user = cx.global::<SettingsStore>().raw_user_settings()?;
        match user.content.theme.theme.clone()? {
            settings::ThemeSelection::Dynamic { mode, .. } => Some(mode),
            settings::ThemeSelection::Static(_) => None,
        }
    })
}

/// Returns the settings notice the status lines show.
fn notice(cx: &TestAppContext) -> Option<String> {
    cx.update(|cx| {
        let notice = cx.try_global::<SettingsNotice>()?;
        notice.0.as_ref().map(ToString::to_string)
    })
}

/// Dispatches `action` and lets every write it starts land.
fn run(action: &dyn gpui::Action, cx: &mut TestAppContext) {
    cx.update(|cx| cx.dispatch_action(action));
    cx.run_until_parked();
}

/// The surfaces, hairline and both text grays of each theme are the brand's tokens, and
/// `border.variant`, which Zed draws the table header's hairline in, is that same hairline.
#[test]
fn brand_tokens_pin_the_surfaces() {
    for (content, theme) in themes() {
        let colors = theme.colors();
        let want: [u32; 6] = match content.appearance {
            AppearanceContent::Dark => [0x0B0C0E, 0x121316, 0x202227, 0x202227, 0xEEEDE8, 0xA7A8AE],
            AppearanceContent::Light => {
                [0xF1F0EB, 0xE9E8E2, 0xD6D5CF, 0xD6D5CF, 0x0B0C0E, 0x4F5056]
            }
        };
        let got = [
            ("background", colors.background),
            ("panel.background", colors.panel_background),
            ("border", colors.border),
            ("border.variant", colors.border_variant),
            ("text", colors.text),
            ("text.muted", colors.text_muted),
        ];
        for ((slot, color), rgb) in got.into_iter().zip(want) {
            assert!(is(color, rgb), "{} {slot} is {color:?}", content.name);
        }
    }
}

/// Every role takes its own key of the theme, in both themes, with no fallback taken, and
/// an import is colored apart from a function of the binary.
#[test]
fn every_token_kind_resolves_to_its_own_key() {
    for (content, theme) in themes() {
        let palette = CodePalette::from_theme(&theme);
        for role in Role::ALL {
            let key = role.keys()[0];
            let color = syntax_color(&theme, key);
            assert!(color.is_some(), "{} sets no color for {key}", content.name);
            assert_eq!(color, Some(palette.color(role)), "{role:?}");
        }
        let (import, function) = (palette.color(Role::Import), palette.color(Role::Function));
        assert_ne!(import, function, "{}", content.name);
    }
}

/// Every text role reads at 4.5:1 on the editor and on a panel; the de-emphasized ones
/// (zero bytes, placeholders, muted icons) at 3:1.
#[test]
fn text_roles_meet_their_contrast_floors() {
    for (content, theme) in themes() {
        let failures = text_floors(&content, &theme);
        assert!(failures.is_empty(), "{}: {failures:?}", content.name);
    }
}

/// The check grades darken (or lighten) with evidence, stay apart in normal vision and
/// under each simulated color-vision deficiency, and a refuted block tints its row.
#[test]
fn check_grades_rise_with_evidence_and_stay_apart() {
    for (content, theme) in themes() {
        let failures = grade_rules(&theme);
        assert!(failures.is_empty(), "{}: {failures:?}", content.name);
    }
}

/// Returns `borer dark` with `edit` made to its written form, and as Zed refines that.
fn dark_with(edit: impl FnOnce(&mut ThemeContent)) -> (ThemeContent, Theme) {
    let (mut content, _) = themes().remove(0);
    edit(&mut content);
    let theme = refine_theme(&content);
    (content, theme)
}

/// Sets the color of the syntax `key` of `content` to `color`.
fn set_color(content: &mut ThemeContent, key: &str, color: Option<ThemeColor>) {
    content.style.syntax.get_mut(key).expect(key).color = color;
}

/// Both of borer's themes keep the whole contract a person's theme is checked by.
#[test]
fn borer_themes_keep_the_contract() {
    for (content, _) in themes() {
        let failures = check(&content);
        assert!(failures.is_empty(), "{}: {failures:?}", content.name);
    }
}

/// A theme with the tested and proved grades swapped is reported by the ramp rule, with
/// the contrast of each.
#[test]
fn swapped_grades_are_reported_with_both_contrasts() {
    let (content, theme) = dark_with(|content| {
        let syntax = &content.style.syntax;
        let (tested, proved) = (
            syntax[GRADES[1]].color.clone(),
            syntax[GRADES[2]].color.clone(),
        );
        set_color(content, GRADES[1], proved);
        set_color(content, GRADES[2], tested);
    });
    let editor = theme.colors().editor_background;
    let ratio = |key| contrast(syntax_color(&theme, key).expect(key), editor);
    let ramp = Failure::Ramp {
        lower: GRADES[1],
        higher: GRADES[2],
        lower_ratio: ratio(GRADES[1]),
        higher_ratio: ratio(GRADES[2]),
    };
    let failures = check(&content);
    assert!(failures.contains(&ramp), "{failures:?}");
    assert!(ratio(GRADES[1]) > ratio(GRADES[2]));
}

/// A theme whose registers are the editor's background color is reported by that role,
/// with its ratio, in one line.
#[test]
fn an_unreadable_register_is_reported_with_its_ratio() {
    let (content, _) = dark_with(|content| {
        let background = content.style.colors.editor_background.clone();
        set_color(content, "borer.register", background);
    });
    let unreadable = Failure::Contrast {
        role: "borer.register".to_owned(),
        background: "editor.background",
        ratio: 1.0,
        floor: TEXT_FLOOR,
    };
    let failures = check(&content);
    assert!(failures.contains(&unreadable), "{failures:?}");
    let line = unreadable.to_string();
    assert_eq!(
        line,
        "borer.register on editor.background: 1.00:1, floor 4.5:1"
    );
}

/// A proved grade that only a deuteranope cannot tell from a wrong one is reported under
/// deuteranopia, and under no other vision.
#[test]
fn grades_merged_only_under_deuteranopia_are_reported() {
    let (_, theme) = dark_with(|content| set_color(content, GRADES[2], Some("#00B040".into())));
    let failures = grade_rules(&theme);
    let merged = |vision: &str| {
        failures.iter().any(|failure| {
            matches!(failure, Failure::Close { a, b, vision: seen, .. }
                if *a == GRADES[2] && *b == GRADES[3] && *seen == vision)
        })
    };
    assert!(merged("deuteranopia"), "{failures:?}");
    assert!(!merged("normal vision"), "{failures:?}");
    assert!(
        failures.iter().all(|failure| matches!(
            failure,
            Failure::Close {
                vision: "deuteranopia",
                ..
            }
        )),
        "{failures:?}"
    );
}

/// A theme that leaves a `borer.*` key unset is reported by it, with the key the app paints
/// it with instead.
#[test]
fn an_unset_borer_key_names_its_fallback() {
    let (content, _) = dark_with(|content| {
        content.style.syntax.shift_remove("borer.register");
    });
    let failures = check(&content);
    let unset = Failure::Unset {
        role: "borer.register".to_owned(),
        fallback: Some("variable.special"),
    };
    assert!(failures.contains(&unset), "{failures:?}");
    assert_eq!(
        unset.to_string(),
        "borer.register is unset; falls back to variable.special"
    );
}

/// Every slot of [`ThemeColors`] the app may draw is one the borer theme sets, so no stock
/// Zed color reaches the screen; only the [`UNDRAWN`] slots are left to Zed.
#[test]
fn no_stock_color_leaks_into_a_drawn_slot() {
    let sentinel = 0x123456;
    let every_slot: serde_json::Map<_, _> = ThemeColors::dark()
        .iter()
        .map(|(field, _)| (AsRef::<str>::as_ref(&field).to_owned(), "#123456".into()))
        .collect();
    let fill: ThemeColorsRefinement =
        serde_json::from_value(every_slot.into()).expect("every slot takes the sentinel");
    for (content, _) in themes() {
        let mut colors = ThemeColors::dark();
        colors.refine(&fill);
        assert!(colors.iter().all(|(_, color)| is(color, sentinel)));
        let style = &content.style;
        let light = content.appearance == AppearanceContent::Light;
        let status = status_colors_refinement(&style.status);
        colors.refine(&theme_colors_refinement(&style.colors, &status, light));
        for (field, color) in colors.iter() {
            let slot = AsRef::<str>::as_ref(&field);
            if !UNDRAWN.contains(&slot) {
                assert!(
                    !is(color, sentinel),
                    "{} leaves {slot} to Zed",
                    content.name
                );
            }
        }
    }
}

/// On a first run under a dark system the app shows `borer dark`, its settings file is
/// created empty, and the config directory a write needs exists.
#[gpui::test]
async fn a_first_run_shows_borer_dark(cx: &mut TestAppContext) {
    let app_state = cx.update(start);
    cx.update(configure).expect("the app configures Zed");
    assert_eq!(shown(cx), "borer dark");
    assert_eq!(notice(cx), None);
    let written = app_state.fs.load(settings_file()).await;
    assert_eq!(written.expect("the file is created").trim(), "");
    let config = checked_metadata(config_dir()).expect("the path is usable");
    assert!(config.is_some_and(|meta| meta.is_dir()));
}

/// [`ToggleTheme`] flips the stored mode, so two toggles in a row come back where they
/// started, and [`FollowSystemTheme`] brings the system's appearance back; each choice is
/// written to the settings file.
#[gpui::test]
fn the_theme_toggles_and_follows_the_system_again(cx: &mut TestAppContext) {
    cx.update(boot);
    run(&ToggleTheme, cx);
    assert_eq!(shown(cx), "borer light");
    assert_eq!(saved(cx), Some(ThemeAppearanceMode::Light));
    cx.update(|cx| {
        cx.dispatch_action(&ToggleTheme);
        cx.dispatch_action(&ToggleTheme);
    });
    cx.run_until_parked();
    assert_eq!(shown(cx), "borer light");
    assert_eq!(saved(cx), Some(ThemeAppearanceMode::Light));
    run(&ToggleTheme, cx);
    assert_eq!(saved(cx), Some(ThemeAppearanceMode::Dark));
    run(&FollowSystemTheme, cx);
    assert_eq!(shown(cx), "borer dark");
    assert_eq!(saved(cx), Some(ThemeAppearanceMode::System));
    assert_eq!(notice(cx), None);
}

/// A toggle keeps what else the person's settings file holds, its comments among it.
#[gpui::test]
async fn a_toggle_keeps_the_rest_of_the_settings_file(cx: &mut TestAppContext) {
    let text = "// mine\n{\n  \"cursor_blink\": true\n}\n";
    let app_state = boot_with(Some(text), cx).await;
    run(&ToggleTheme, cx);
    let written = app_state
        .fs
        .load(settings_file())
        .await
        .expect("the file reads");
    assert!(written.contains("// mine"), "{written}");
    assert!(written.contains("\"cursor_blink\": true"), "{written}");
    assert_eq!(saved(cx), Some(ThemeAppearanceMode::Light));
}

/// Boots over a settings file holding `text`, or a directory where it should be, and
/// asserts startup goes on under the app's settings and every status line says `how` the
/// file was taken.
async fn assert_reported_not_fatal(text: Option<&str>, how: &str, cx: &mut TestAppContext) {
    let _app_state = boot_with(text, cx).await;
    assert_eq!(shown(cx), "borer dark", "{text:?}");
    let said = notice(cx).expect("the problem is reported");
    assert!(said.starts_with(&format!("settings file {how}")), "{said}");
    let binary = cx.new(|cx| Binary::new(cx));
    let line = cx.new(|cx| StatusLine::new(binary, cx));
    let text_shown = line.read_with(cx, |line, cx| line.text(cx));
    assert!(text_shown.starts_with(&said), "{text_shown}");
}

/// A settings file that does not parse never stops startup.
#[gpui::test]
async fn a_settings_file_that_does_not_parse_is_reported(cx: &mut TestAppContext) {
    assert_reported_not_fatal(Some("{"), "not applied", cx).await;
}

/// A settings file holding a wrong type applies its good fields and quotes the bad value;
/// a toggle over it writes and reports the file, not a failed toggle.
#[gpui::test]
async fn a_settings_file_with_a_wrong_type_is_partly_applied(cx: &mut TestAppContext) {
    let text = "{\"ui_font_size\": \"big\", \"buffer_font_size\": 20}";
    assert_reported_not_fatal(Some(text), "partly applied", cx).await;
    let said = notice(cx).expect("the bad field is named");
    assert!(said.contains("invalid type: string \"big\""), "{said}");
    let size = cx.update(|cx| ThemeSettings::get_global(cx).buffer_font_size(cx));
    assert_eq!(size, px(20.0));
    run(&ToggleTheme, cx);
    assert_eq!(shown(cx), "borer light");
    let said = notice(cx).expect("the file is still reported");
    assert!(said.starts_with("settings file partly applied"), "{said}");
}

/// A directory where the settings file should be never stops startup.
#[gpui::test]
async fn a_settings_directory_is_reported(cx: &mut TestAppContext) {
    assert_reported_not_fatal(None, "not applied", cx).await;
}

/// A person's settings file cannot turn AI back on or start a context server.
#[gpui::test]
async fn a_hostile_settings_file_keeps_ai_off_and_starts_no_server(cx: &mut TestAppContext) {
    let text = "{\"disable_ai\": false, \"context_servers\": {\"x\": {\"command\": \"calc.exe\"}}}";
    let app_state = boot_with(Some(text), cx).await;
    assert!(cx.update(|cx| DisableAiSettings::get_global(cx).disable_ai));
    let (root, cx) = cx.add_window_view(|window, cx| {
        let app = new_workspace(&app_state, None, window, cx);
        Shell::new(app, window, cx)
    });
    cx.run_until_parked();
    cx.update(|window, cx| window.draw(cx).clear(cx));
    let running = root.read_with(cx, |root, cx| {
        let project = root.workspace().read(cx).project().read(cx);
        project
            .context_server_store()
            .read(cx)
            .running_servers()
            .len()
    });
    assert_eq!(running, 0);
    assert!(cx.update(|_, cx| DisableAiSettings::get_global(cx).disable_ai));
}

/// A toggle that cannot write its file says why on the status line.
#[gpui::test]
async fn a_toggle_that_cannot_write_says_why(cx: &mut TestAppContext) {
    let _app_state = boot_with(None, cx).await;
    run(&ToggleTheme, cx);
    let said = notice(cx).expect("the failure is reported");
    assert!(said.starts_with("theme not saved"), "{said}");
}

/// A toggle over a single named theme, with no dark and light pair, changes nothing and
/// says so on the status line.
#[gpui::test]
async fn a_toggle_over_one_named_theme_says_so(cx: &mut TestAppContext) {
    let single = "{\"theme\": \"borer light\"}";
    let _app_state = boot_with(Some(single), cx).await;
    assert_eq!(shown(cx), "borer light");
    run(&ToggleTheme, cx);
    assert_eq!(shown(cx), "borer light");
    let said = notice(cx).expect("the no-op is reported");
    assert!(said.contains("nothing to switch"), "{said}");
}

/// A decompile row is the buffer font size times its line height, whole: 13 px at 1.4.
#[gpui::test]
fn code_rows_follow_the_buffer_font(cx: &mut TestAppContext) {
    cx.update(boot);
    assert_eq!(cx.update(|cx| code_row_height(cx)), px(18.0));
    for (height, rows) in [(1e30, px(64.0)), (1.0, px(13.0))] {
        cx.update(|cx| {
            cx.update_global(|store: &mut SettingsStore, cx| {
                store.update_user_settings(cx, |content| {
                    content.theme.buffer_line_height = Some(BufferLineHeight::Custom(height));
                });
            });
        });
        assert_eq!(cx.update(|cx| code_row_height(cx)), rows, "{height}");
    }
}

/// Returns the text of a theme family file named `family`, holding one theme `name` of
/// `appearance` whose `style` object is `style`.
fn family(family: &str, name: &str, appearance: &str, style: &str) -> Vec<u8> {
    let theme = format!(r#"{{"name": "{name}", "appearance": "{appearance}", "style": {style}}}"#);
    format!(r#"{{"name": "{family}", "author": "a person", "themes": [{theme}]}}"#).into_bytes()
}

/// Returns whether a theme named `name` is registered.
fn registered(name: &str, cx: &TestAppContext) -> bool {
    cx.update(|cx| ThemeRegistry::global(cx).get(name).is_ok())
}

/// Starts Zed's test app state with each of `files` in its file system, its bytes or a
/// folder, then configures it as the app does and lets the background reads land.
async fn boot_with_files(
    files: &[(&Path, Option<Vec<u8>>)],
    cx: &mut TestAppContext,
) -> Arc<AppState> {
    let app_state = cx.update(start);
    let fake = app_state.fs.as_fake();
    fake.create_dir(themes_dir())
        .await
        .expect("the themes folder is made");
    for (path, bytes) in files {
        match bytes {
            Some(bytes) => fake.insert_file(path, bytes.clone()).await,
            None => fake.create_dir(path).await.expect("the folder is made"),
        }
    }
    cx.update(configure).expect("the app configures Zed");
    cx.run_until_parked();
    app_state
}

/// Opens a window over the app's workspace and returns that workspace and the window's
/// context.
fn open_window<'a>(
    app_state: &Arc<AppState>,
    cx: &'a mut TestAppContext,
) -> (Entity<Workspace>, &'a mut VisualTestContext) {
    let (root, cx) = cx.add_window_view(|window, cx| {
        Shell::new(new_workspace(app_state, None, window, cx), window, cx)
    });
    (root.read_with(cx, |root, _| root.workspace().clone()), cx)
}

/// Returns whether `workspace` shows the notification of the theme file or folder `path`.
fn noticed(workspace: &Entity<Workspace>, path: &Path, cx: &mut VisualTestContext) -> bool {
    workspace.read_with(cx, |workspace, _| {
        workspace.has_notification(&notice_id(path))
    })
}

/// A theme file in the themes folder at start is registered and shown when the settings
/// name it; one written while the app runs is registered without a restart, and an edit
/// of the shown one repaints it.
#[gpui::test]
async fn the_themes_folder_loads_at_start_and_on_change(cx: &mut TestAppContext) {
    let mine = themes_dir().join("mine.json");
    let settings = r#"{"theme": {"mode": "dark", "dark": "mine dark", "light": "borer light"}}"#;
    let files = [
        (
            mine.as_path(),
            Some(family("mine", "mine dark", "dark", "{}")),
        ),
        (settings_file().as_path(), Some(settings.into())),
    ];
    let app_state = boot_with_files(&files, cx).await;
    assert_eq!(shown(cx), "mine dark");
    let fake = app_state.fs.as_fake();
    let later = themes_dir().join("later.json");
    fake.insert_file(&later, family("later", "later light", "light", "{}"))
        .await;
    cx.run_until_parked();
    assert!(registered("later light", cx));
    let edited = family(
        "mine",
        "mine dark",
        "dark",
        r##"{"background": "#102030"}"##,
    );
    fake.insert_file(&mine, edited).await;
    cx.run_until_parked();
    let background = cx.update(|cx| cx.theme().colors().background);
    assert!(is(background, 0x102030), "{background:?}");
}

/// A theme file that does not parse, one over the size cap and a folder named like a
/// theme are each a notification naming the path and why; startup goes on, the other
/// themes load, and fixing the file takes its notification back.
#[gpui::test]
async fn a_bad_theme_file_is_a_notification_not_a_stop(cx: &mut TestAppContext) {
    let dir = themes_dir();
    let (bad, huge, good) = (
        dir.join("bad.json"),
        dir.join("huge.json"),
        dir.join("good.json"),
    );
    let folder = dir.join("folder.json");
    let len = usize::try_from(MAX_THEME_BYTES).expect("fits") + 1;
    let files = [
        (bad.as_path(), Some(b"{".to_vec())),
        (huge.as_path(), Some(vec![b' '; len])),
        (
            good.as_path(),
            Some(family("good", "good dark", "dark", "{}")),
        ),
        (folder.as_path(), None),
    ];
    let app_state = boot_with_files(&files, cx).await;
    assert_eq!(shown(cx), "borer dark");
    assert!(registered("good dark", cx));
    let (workspace, cx) = open_window(&app_state, cx);
    cx.run_until_parked();
    assert!(noticed(&workspace, &bad, cx));
    assert!(noticed(&workspace, &huge, cx));
    assert!(noticed(&workspace, &folder, cx));
    assert!(!noticed(&workspace, &good, cx));
    let fixed = family("bad", "bad dark", "dark", "{}");
    app_state.fs.as_fake().insert_file(&bad, fixed).await;
    cx.run_until_parked();
    assert!(!noticed(&workspace, &bad, cx));
    assert!(cx.update(|_, cx| ThemeRegistry::global(cx).get("bad dark").is_ok()));
}

/// A themes folder holding more entries than the app reads is a notification naming the
/// folder, and none of its themes is read.
#[gpui::test]
async fn a_crowded_themes_folder_reads_no_theme(cx: &mut TestAppContext) {
    let dir = themes_dir();
    let names: Vec<_> = (0..=MAX_THEME_ENTRIES)
        .map(|i| dir.join(format!("t{i}.json")))
        .collect();
    let files: Vec<_> = names
        .iter()
        .map(|path| {
            (
                path.as_path(),
                Some(family("t", "crowded dark", "dark", "{}")),
            )
        })
        .collect();
    let app_state = boot_with_files(&files, cx).await;
    assert!(!registered("crowded dark", cx));
    let (workspace, cx) = open_window(&app_state, cx);
    cx.run_until_parked();
    assert!(noticed(&workspace, dir, cx));
}

/// A theme file naming one of the app's own themes, or a theme an earlier file holds, is
/// refused with a notification and the held theme stays; deleting a theme file drops its
/// themes.
#[gpui::test]
async fn a_theme_name_has_one_file_and_leaves_with_it(cx: &mut TestAppContext) {
    let dir = themes_dir();
    let (first, twin, own) = (dir.join("a.json"), dir.join("b.json"), dir.join("c.json"));
    let style = r##"{"background": "#102030"}"##;
    let files = [
        (
            first.as_path(),
            Some(family("a", "mine dark", "dark", "{}")),
        ),
        (
            twin.as_path(),
            Some(family("b", "mine dark", "dark", style)),
        ),
        (
            own.as_path(),
            Some(family("c", "borer dark", "dark", style)),
        ),
    ];
    let app_state = boot_with_files(&files, cx).await;
    assert!(registered("mine dark", cx));
    assert!(is(cx.update(|cx| cx.theme().colors().background), 0x0B0C0E));
    let mine = cx.update(|cx| ThemeRegistry::global(cx).get("mine dark").expect("there"));
    assert!(!is(mine.colors().background, 0x102030));
    let (workspace, cx) = open_window(&app_state, cx);
    cx.run_until_parked();
    assert!(!noticed(&workspace, &first, cx));
    assert!(noticed(&workspace, &twin, cx));
    assert!(noticed(&workspace, &own, cx));
    (app_state.fs)
        .remove_file(&first, fs::RemoveOptions::default())
        .await
        .expect("removed");
    cx.run_until_parked();
    assert!(cx.update(|_, cx| ThemeRegistry::global(cx).get("mine dark").is_err()));
}

/// A theme file renamed while the app runs keeps its themes: the new name is read after the
/// old one is dropped, whatever their order, with no notification.
#[gpui::test]
async fn a_renamed_theme_file_keeps_its_themes(cx: &mut TestAppContext) {
    let dir = themes_dir();
    let (old, new) = (dir.join("zz.json"), dir.join("aa.json"));
    let files = [(old.as_path(), Some(family("zz", "mine dark", "dark", "{}")))];
    let app_state = boot_with_files(&files, cx).await;
    assert!(registered("mine dark", cx));
    let (workspace, cx) = open_window(&app_state, cx);
    (app_state.fs)
        .rename(&old, &new, fs::RenameOptions::default())
        .await
        .expect("renamed");
    cx.run_until_parked();
    assert!(cx.update(|_, cx| ThemeRegistry::global(cx).get("mine dark").is_ok()));
    assert!(!noticed(&workspace, &new, cx));
}

/// Opens the theme picker over `workspace` with [`SelectTheme`], types `query` into it and
/// lets the preview land.
fn pick(workspace: &Entity<Workspace>, query: &str, cx: &mut VisualTestContext) {
    workspace.update_in(cx, |workspace, window, cx| {
        workspace.focus_panel::<FunctionsPanel>(window, cx);
    });
    cx.dispatch_action(SelectTheme);
    cx.run_until_parked();
    let modal = workspace.read_with(cx, |workspace, cx| {
        workspace.active_modal::<ThemePicker>(cx)
    });
    let picker = modal
        .expect("the picker opens")
        .read_with(cx, |modal, _| modal.picker().clone());
    picker.update_in(cx, |picker, window, cx| picker.set_query(query, window, cx));
    cx.run_until_parked();
}

/// The theme picker shows the theme a query selects at once; Enter keeps it in the dark
/// slot of the settings file, the light slot and the mode kept; a picker left with escape
/// puts back the theme shown before it.
#[gpui::test]
async fn the_theme_picker_previews_keeps_and_puts_back(cx: &mut TestAppContext) {
    let mine = themes_dir().join("mine.json");
    let files = [(
        mine.as_path(),
        Some(family("mine", "mine dark", "dark", "{}")),
    )];
    let app_state = boot_with_files(&files, cx).await;
    let (workspace, cx) = open_window(&app_state, cx);
    cx.update(|_, cx| *SystemAppearance::global_mut(cx) = SystemAppearance(Appearance::Dark));
    pick(&workspace, "mine", cx);
    assert_eq!(shown(cx), "mine dark");
    cx.dispatch_action(menu::Confirm);
    cx.run_until_parked();
    let kept = cx.update(|_, cx| {
        let user = SettingsStore::global(cx).raw_user_settings()?;
        user.content.theme.theme.clone()
    });
    assert!(
        matches!(&kept, Some(settings::ThemeSelection::Dynamic { mode, light, dark })
            if *mode == ThemeAppearanceMode::System
                && &*light.0 == "borer light"
                && &*dark.0 == "mine dark"),
        "{kept:?}"
    );
    pick(&workspace, "borer light", cx);
    assert_eq!(shown(cx), "borer light");
    cx.dispatch_action(menu::Cancel);
    cx.run_until_parked();
    assert_eq!(shown(cx), "mine dark");
    let open = workspace.read_with(cx, |workspace, cx| {
        workspace.active_modal::<ThemePicker>(cx).is_some()
    });
    assert!(!open);
}

/// Returns the names in the themes folder, sorted.
async fn themes_folder(app_state: &AppState) -> Vec<String> {
    let entries = app_state.fs.read_dir(themes_dir()).await;
    let entries: Vec<_> = entries.expect("the folder lists").collect().await;
    let mut names: Vec<String> = entries
        .into_iter()
        .map(|entry| {
            entry
                .expect("an entry")
                .file_name()
                .expect("named")
                .to_string_lossy()
                .into()
        })
        .collect();
    names.sort();
    names
}

/// A theme file imports byte for byte into the themes folder and is registered, its source
/// untouched; a file name already in the folder is refused with that file's path, a theme
/// name another file holds with that file, and one of the app's own theme names as such; a
/// file over the size cap and a JSON file that is not a theme family are refused with
/// their reasons; a refusal writes nothing.
#[gpui::test]
async fn an_import_copies_a_theme_file_and_refuses_the_rest(cx: &mut TestAppContext) {
    let app_state = boot_with_files(&[], cx).await;
    let fs = app_state.fs.clone();
    let fake = fs.as_fake();
    let elsewhere = std::env::temp_dir().join("borer-app-import");
    fake.create_dir(&elsewhere).await.expect("made");
    let source = elsewhere.join("pretty.json");
    let mut bytes = family("pretty", "pretty dark", "dark", "{}");
    bytes.extend_from_slice(b"\r\n  ");
    fake.insert_file(&source, bytes.clone()).await;
    let registry = cx.update(|cx| ThemeRegistry::global(cx));
    let read = |path: &Path, cx: &mut TestAppContext| {
        cx.update(|cx| read_candidate(fs.clone(), path.to_owned(), cx))
    };
    let candidate = read(&source, cx).await.expect("reads");
    let names: Vec<_> = candidate
        .reports
        .iter()
        .map(|(name, ..)| name.to_string())
        .collect();
    assert_eq!(names, ["pretty dark"]);
    let dest = import(fs.as_ref(), candidate, &mut cx.to_async())
        .await
        .expect("imports");
    assert_eq!(dest, themes_dir().join("pretty.json"));
    assert_eq!(fs.load_bytes(&dest).await.expect("copied"), bytes);
    assert_eq!(fs.load_bytes(&source).await.expect("kept"), bytes);
    assert!(registry.get("pretty dark").is_ok());
    let again = read(&source, cx).await.expect("reads");
    let clash = import(fs.as_ref(), again, &mut cx.to_async())
        .await
        .expect_err("a clash");
    let said = format!("{clash:#}");
    assert!(said.contains(&dest.display().to_string()), "{said}");
    let big = elsewhere.join("big.json");
    let len = usize::try_from(MAX_THEME_BYTES).expect("fits") + (1 << 20);
    fake.insert_file(&big, vec![b' '; len]).await;
    let said = format!("{:#}", read(&big, cx).await.expect_err("too big"));
    assert!(
        said.contains("big.json holds") && said.contains("over the"),
        "{said}"
    );
    let other = elsewhere.join("other.json");
    fake.insert_file(&other, br#"{"hello": 1}"#.to_vec()).await;
    let said = format!("{:#}", read(&other, cx).await.expect_err("no theme"));
    assert!(said.contains("other.json is not a theme family"), "{said}");
    let twin = elsewhere.join("twin.json");
    fake.insert_file(&twin, family("twin", "pretty dark", "dark", "{}"))
        .await;
    let twin = read(&twin, cx).await.expect("reads");
    let clash = import(fs.as_ref(), twin, &mut cx.to_async())
        .await
        .expect_err("a name clash");
    let said = format!("{clash:#}");
    assert!(
        said.contains("a theme named pretty dark is already in"),
        "{said}"
    );
    let own = elsewhere.join("own.json");
    fake.insert_file(&own, family("own", "borer light", "light", "{}"))
        .await;
    let own = read(&own, cx).await.expect("reads");
    let clash = import(fs.as_ref(), own, &mut cx.to_async())
        .await
        .expect_err("the app's own name");
    let said = format!("{clash:#}");
    assert!(
        said.contains("borer light is one of the app's own"),
        "{said}"
    );
    assert_eq!(themes_folder(&app_state).await, ["pretty.json"]);
}

/// Returns a theme family of `count` dark themes with nothing set, `t0 dark` onward.
fn family_of(count: usize) -> Vec<u8> {
    let themes: Vec<String> = (0..count)
        .map(|i| format!(r#"{{"name": "t{i} dark", "appearance": "dark", "style": {{}}}}"#))
        .collect();
    let themes = themes.join(", ");
    format!(r#"{{"name": "many", "author": "a person", "themes": [{themes}]}}"#).into_bytes()
}

/// A theme family of more themes than the app reads is refused naming the cap, before its
/// themes are parsed; one of exactly the cap reads, every theme in its report.
#[gpui::test]
async fn a_family_of_too_many_themes_is_refused(cx: &mut TestAppContext) {
    let app_state = boot_with_files(&[], cx).await;
    let fs = app_state.fs.clone();
    let fake = fs.as_fake();
    let elsewhere = std::env::temp_dir().join("borer-app-many");
    fake.create_dir(&elsewhere).await.expect("made");
    let (over, full) = (elsewhere.join("over.json"), elsewhere.join("full.json"));
    fake.insert_file(&over, family_of(MAX_FAMILY_THEMES + 1))
        .await;
    fake.insert_file(&full, family_of(MAX_FAMILY_THEMES)).await;
    let read = |path: &Path, cx: &mut TestAppContext| {
        cx.update(|cx| read_candidate(fs.clone(), path.to_owned(), cx))
    };
    let said = format!("{:#}", read(&over, cx).await.expect_err("too many"));
    let cap = format!("over the {MAX_FAMILY_THEMES} the app reads");
    assert!(
        said.contains("over.json holds") && said.contains(&cap),
        "{said}"
    );
    let candidate = read(&full, cx).await.expect("reads");
    assert_eq!(candidate.reports.len(), MAX_FAMILY_THEMES);
}

/// A theme file dropped on a tab opens its report, each theme with the rules it breaks;
/// import and use copies it and shows its theme. A JSON file with a `themes` key that does
/// not parse opens the report with why; other JSON opens as a binary.
#[gpui::test]
async fn a_dropped_theme_file_opens_its_report(cx: &mut TestAppContext) {
    let app_state = boot_with_files(&[], cx).await;
    let fake = app_state.fs.as_fake();
    let elsewhere = std::env::temp_dir().join("borer-app-drop");
    fake.create_dir(&elsewhere).await.expect("made");
    let (source, other) = (elsewhere.join("dropped.json"), elsewhere.join("other.json"));
    let broken = elsewhere.join("broken.json");
    fake.insert_file(&broken, br#"{"themes": 1}"#.to_vec())
        .await;
    let style = r##"{"syntax": {"borer.register": {"color": "#0B0C0E"}}}"##;
    fake.insert_file(&source, family("dropped", "dropped dark", "dark", style))
        .await;
    fake.insert_file(&other, br#"{"hello": 1}"#.to_vec()).await;
    let (workspace, cx) = open_window(&app_state, cx);
    let drop_file = |path: &Path, cx: &mut VisualTestContext| {
        cx.update(|window, cx| window.draw(cx).clear(cx));
        let size = cx.update(|window, _| window.viewport_size());
        let position = gpui::point(size.width * 0.5, size.height * 0.5);
        let paths = ExternalPaths([path.to_path_buf()].into_iter().collect());
        cx.simulate_event(FileDropEvent::Entered { position, paths });
        cx.simulate_event(FileDropEvent::Submit { position });
        cx.run_until_parked();
    };
    let report = |cx: &mut VisualTestContext| {
        workspace.read_with(cx, |workspace, cx| {
            workspace.active_modal::<ImportReport>(cx)
        })
    };
    drop_file(&other, cx);
    assert!(report(cx).is_none());
    let status = cx.update(|window, cx| {
        let shell = window.root::<Shell>().flatten().expect("the shell");
        shell.read(cx).binary().read(cx).status().to_owned()
    });
    assert!(status.contains("other.json"), "{status}");
    drop_file(&broken, cx);
    let modal = report(cx).expect("a theme-like file opens its report");
    let why = modal.read_with(cx, |modal, _| modal.refusal().map(ToOwned::to_owned));
    let why = why.expect("the parse error");
    assert!(why.contains("broken.json is not a theme family"), "{why}");
    cx.dispatch_action(menu::Cancel);
    cx.run_until_parked();
    assert!(report(cx).is_none());
    drop_file(&source, cx);
    let modal = report(cx).expect("the report opens");
    let register = modal.read_with(cx, |modal, _| {
        let (_, _, failures) = modal.reports().first().expect("one theme").clone();
        failures.into_iter().find(
            |failure| matches!(failure, Failure::Contrast { role, .. } if role == "borer.register"),
        )
    });
    assert!(register.is_some());
    modal.update(cx, |modal, cx| modal.import(true, cx));
    cx.run_until_parked();
    assert!(report(cx).is_none());
    assert_eq!(shown(cx), "dropped dark");
    let copied = app_state
        .fs
        .load_bytes(&themes_dir().join("dropped.json"))
        .await;
    assert_eq!(
        copied.expect("copied"),
        family("dropped", "dropped dark", "dark", style)
    );
}

/// Zed's themes folder and each installed extension's themes folder are listed, other
/// files left out; a Zed theme imports with borer's value for every `borer.*` key it
/// leaves unset, keeps the ones it sets, and its report names the keys it took.
#[gpui::test]
async fn a_zed_theme_imports_with_borers_keys(cx: &mut TestAppContext) {
    let app_state = boot_with_files(&[], cx).await;
    let fs = app_state.fs.clone();
    let fake = fs.as_fake();
    let root = std::env::temp_dir().join("borer-app-zed");
    let zed = Dirs {
        config: root.join("config"),
        data: root.join("data"),
    };
    let (own_dir, ext_dir) = (
        zed.config.join("themes"),
        zed.data.join("extensions/installed/nice/themes"),
    );
    for dir in [&own_dir, &ext_dir] {
        fake.create_dir(dir).await.expect("made");
    }
    let (own, ext) = (own_dir.join("mine.json"), ext_dir.join("nice.json"));
    fake.insert_file(&own, family("mine", "mine dark", "dark", "{}"))
        .await;
    fake.insert_file(&own_dir.join("notes.txt"), b"x".to_vec())
        .await;
    let style = r##"{"syntax": {"borer.register": {"color": "#123456"}}}"##;
    fake.insert_file(&ext, family("nice", "nice light", "light", style))
        .await;
    let found = zed_themes(fs.as_ref(), &zed).await;
    let listed: Vec<_> = (found.iter())
        .map(|theme| (theme.path.clone(), theme.from.to_string()))
        .collect();
    let want = [
        (own, "themes folder".to_owned()),
        (ext.clone(), "nice".to_owned()),
    ];
    assert_eq!(listed, want);
    let read = cx.update(|cx| read_from(fs.clone(), ext, Origin::Zed, cx));
    let candidate = read.await.expect("reads");
    let (theme, taken) = candidate.borrowed.first().expect("one theme");
    assert_eq!(theme, "nice light");
    assert!(taken.iter().any(|key| key == "borer.address"), "{taken:?}");
    assert!(
        !taken.iter().any(|key| key == "borer.register"),
        "{taken:?}"
    );
    let (_, _, failures) = candidate.reports.first().expect("one theme");
    let unset = failures.iter().any(|f| matches!(f, Failure::Unset { .. }));
    assert!(!unset, "{failures:?}");
    import(fs.as_ref(), candidate, &mut cx.to_async())
        .await
        .expect("imports");
    let get = |name: &str, cx: &TestAppContext| {
        cx.update(|cx| ThemeRegistry::global(cx).get(name).expect("registered"))
    };
    let (nice, light) = (get("nice light", cx), get("borer light", cx));
    let address = |theme: &Theme| syntax_color(theme, "borer.address");
    assert_eq!(address(&nice), address(&light));
    let register = syntax_color(&nice, "borer.register").expect("kept");
    assert!(is(register, 0x123456), "{register:?}");
}
