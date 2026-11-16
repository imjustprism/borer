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

use std::path::Path;
use std::sync::Arc;

use borer_app::actions::{FollowSystemTheme, SelectTheme, ToggleTheme};
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
use borer_app::theme_picker::ThemePicker;
use borer_app::user_themes::{MAX_THEME_BYTES, MAX_THEME_ENTRIES, notice_id};
use borer_engine::program::checked_metadata;
use fs::Fs as _;
use gpui::{
    AppContext as _, BorrowAppContext as _, Entity, Hsla, ReadGlobal as _, Refineable as _, Rgba,
    TestAppContext, VisualTestContext, px,
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

use support::{boot, start};

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

/// Starts Zed's test app state with `text` as its settings file, then configures
/// it as the app does.
async fn boot_with(text: Option<&str>, cx: &mut TestAppContext) -> Arc<AppState> {
    let app_state = cx.update(start);
    let path = paths::settings_file();
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
    let written = app_state.fs.load(paths::settings_file()).await;
    assert_eq!(written.expect("the file is created").trim(), "");
    let config = checked_metadata(paths::config_dir()).expect("the path is usable");
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
        .load(paths::settings_file())
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
    fake.create_dir(paths::themes_dir())
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
    let mine = paths::themes_dir().join("mine.json");
    let settings = r#"{"theme": {"mode": "dark", "dark": "mine dark", "light": "borer light"}}"#;
    let files = [
        (
            mine.as_path(),
            Some(family("mine", "mine dark", "dark", "{}")),
        ),
        (paths::settings_file().as_path(), Some(settings.into())),
    ];
    let app_state = boot_with_files(&files, cx).await;
    assert_eq!(shown(cx), "mine dark");
    let fake = app_state.fs.as_fake();
    let later = paths::themes_dir().join("later.json");
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
    let dir = paths::themes_dir();
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
    let dir = paths::themes_dir();
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
    let dir = paths::themes_dir();
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
    let mine = paths::themes_dir().join("mine.json");
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
