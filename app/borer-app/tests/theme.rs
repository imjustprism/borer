//! borer's theme as a tested contract: the brand's surfaces, a color for every token the
//! engine draws, contrast floors, a check-grade ramp that survives color-vision deficiency,
//! no stock Zed color in a slot the app shows, and the app booting into it.
//!
//! The color maths are written out here: WCAG 2 contrast, `OKLab` distance, and the Machado
//! (2009) simulation of deuteranopia, protanopia and tritanopia at severity 1.0.

#![expect(
    clippy::expect_used,
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::sync::Arc;

use borer_app::actions::{FollowSystemTheme, ToggleTheme};
use borer_app::app_settings::BORER_THEME;
use borer_app::app_view::{configure, new_workspace, set_data_dir};
use borer_app::binary::{Binary, SettingsNotice, StatusLine};
use borer_app::code_view::{CodePalette, Role};
use borer_app::decompile_item::code_row_height;
use borer_engine::program::checked_metadata;
use fs::Fs as _;
use gpui::{
    App, AppContext as _, AssetSource as _, BorrowAppContext as _, Hsla, Refineable as _, Rgba,
    TestAppContext, TestDispatcher, TextRun, WindowTextSystem, px,
};
use project::DisableAiSettings;
use settings::{BufferLineHeight, Settings as _, SettingsStore, ThemeAppearanceMode};
use theme::{
    ActiveTheme as _, Appearance, AppearanceContent, SystemAppearance, Theme, ThemeColors,
    ThemeColorsRefinement,
};
use theme_settings::{
    ThemeContent, ThemeSettings, deserialize_user_theme, refine_theme, status_colors_refinement,
    theme_colors_refinement,
};
use workspace::{AppState, MultiWorkspace};

/// Grade keys from least to most evidence, then the refuted grade.
const GRADES: [&str; 4] = [
    "borer.grade.unchecked",
    "borer.grade.tested",
    "borer.grade.proved",
    "borer.grade.wrong",
];

/// Machado (2009) simulation matrices at severity 1.0 over linear sRGB, by deficiency.
const MACHADO: [(&str, [[f64; 3]; 3]); 3] = [
    (
        "deuteranopia",
        [
            [0.367322, 0.860646, -0.227968],
            [0.280085, 0.672501, 0.047413],
            [-0.011820, 0.042940, 0.968881],
        ],
    ),
    (
        "protanopia",
        [
            [0.152286, 1.052583, -0.204868],
            [0.114503, 0.786281, 0.099216],
            [-0.003882, -0.048116, 1.051998],
        ],
    ),
    (
        "tritanopia",
        [
            [1.255528, -0.076749, -0.178779],
            [-0.078411, 0.930809, 0.147602],
            [0.004733, 0.691367, 0.303900],
        ],
    ),
];

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

/// Returns the color the theme's syntax sets for `key`, if it sets one.
fn syntax_color(theme: &Theme, key: &str) -> Option<Hsla> {
    theme
        .syntax()
        .style_for_name(key)
        .and_then(|style| style.color)
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

/// Returns `color`'s linear sRGB channels.
fn linear(color: Hsla) -> [f64; 3] {
    let rgba = Rgba::from(color);
    assert!((rgba.a - 1.0).abs() < 1e-6, "a measured color is opaque");
    [rgba.r, rgba.g, rgba.b].map(|c| {
        let c = f64::from(c);
        if c <= 0.04045 {
            c / 12.92
        } else {
            ((c + 0.055) / 1.055).powf(2.4)
        }
    })
}

/// Returns the WCAG 2 contrast ratio of `a` against `b`.
fn contrast(a: Hsla, b: Hsla) -> f64 {
    let luminance = |c| {
        let [r, g, b] = linear(c);
        0.0722f64.mul_add(b, 0.2126f64.mul_add(r, 0.7152 * g))
    };
    let (x, y) = (luminance(a), luminance(b));
    (x.max(y) + 0.05) / (x.min(y) + 0.05)
}

/// Returns linear sRGB `[r, g, b]` in `OKLab`.
fn oklab([r, g, b]: [f64; 3]) -> [f64; 3] {
    let dot = |m: [f64; 3]| m[0].mul_add(r, m[1].mul_add(g, m[2] * b)).cbrt();
    let l = dot([0.4122214708, 0.5363325363, 0.0514459929]);
    let m = dot([0.2119034982, 0.6806995451, 0.1073969566]);
    let s = dot([0.0883024619, 0.2817188376, 0.6299787005]);
    let mix = |k: [f64; 3]| k[0].mul_add(l, k[1].mul_add(m, k[2] * s));
    [
        mix([0.2104542553, 0.7936177850, -0.0040720468]),
        mix([1.9779984951, -2.4285922050, 0.4505937099]),
        mix([0.0259040371, 0.7827717662, -0.8086757660]),
    ]
}

/// Returns linear sRGB `rgb` as seen through `matrix`, clamped to the gamut.
fn simulate(rgb: [f64; 3], matrix: [[f64; 3]; 3]) -> [f64; 3] {
    matrix.map(|row| {
        row[0]
            .mul_add(rgb[0], row[1].mul_add(rgb[1], row[2] * rgb[2]))
            .clamp(0.0, 1.0)
    })
}

/// Returns the Euclidean distance of two `OKLab` colors.
fn distance(a: [f64; 3], b: [f64; 3]) -> f64 {
    a.iter()
        .zip(b)
        .map(|(x, y)| (x - y).powi(2))
        .sum::<f64>()
        .sqrt()
}

/// Points Zed's paths at one data directory of the tests, once per process, so no test
/// resolves the person's own Zed settings.
fn use_test_data_dir() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        set_data_dir(&std::env::temp_dir().join("borer-app-tests")).expect("the data dir");
    });
}

/// Starts Zed's test app state over a fresh in-memory database and file system, under a
/// dark system appearance, not yet configured.
fn start(cx: &mut App) -> Arc<AppState> {
    use_test_data_dir();
    cx.set_global(db::AppDatabase::test_new());
    let app_state = AppState::test(cx);
    *SystemAppearance::global_mut(cx) = SystemAppearance(Appearance::Dark);
    app_state
}

/// Starts Zed's test app state, configured as the app configures Zed.
fn boot(cx: &mut App) {
    start(cx);
    configure(cx).expect("the app configures Zed");
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
        let colors = theme.colors();
        let backgrounds = [colors.editor_background, colors.panel_background];
        let floor = |what: &str, color: Hsla, ratio: f64| {
            for background in backgrounds {
                let got = contrast(color, background);
                assert!(got >= ratio, "{} {what}: {got:.2} < {ratio}", content.name);
            }
        };
        let quiet = "borer.byte.zero";
        for key in content.style.syntax.keys() {
            if GRADES.contains(&key.as_str()) || key == quiet {
                continue;
            }
            if let Some(color) = syntax_color(&theme, key) {
                floor(key, color, 4.5);
            }
        }
        floor("text", colors.text, 4.5);
        floor("text.muted", colors.text_muted, 4.5);
        floor("text.accent", colors.text_accent, 4.5);
        floor("editor.foreground", colors.editor_foreground, 4.5);
        floor(quiet, syntax_color(&theme, quiet).expect("zero bytes"), 3.0);
        floor("text.placeholder", colors.text_placeholder, 3.0);
        floor("icon.muted", colors.icon_muted, 3.0);
    }
}

/// The check grades darken (or lighten) with evidence, stay apart in normal vision and
/// under each simulated color-vision deficiency, and a refuted block tints its row.
#[test]
fn check_grades_rise_with_evidence_and_stay_apart() {
    for (content, theme) in themes() {
        let editor = theme.colors().editor_background;
        let grades = GRADES.map(|key| syntax_color(&theme, key).expect(key));
        let ramp = grades[..3].iter().map(|&c| contrast(c, editor));
        let ramp: Vec<f64> = ramp.collect();
        assert!(
            ramp.windows(2).all(|w| w[0] < w[1]),
            "{}: {ramp:?}",
            content.name
        );
        let visions = std::iter::once(("normal vision", 0.12, None))
            .chain(MACHADO.map(|(name, matrix)| (name, 0.08, Some(matrix))));
        for (vision, floor, matrix) in visions {
            let seen = |c| oklab(matrix.map_or_else(|| linear(c), |m| simulate(linear(c), m)));
            for (i, &a) in grades.iter().enumerate() {
                for (j, &b) in grades.iter().enumerate().skip(i + 1) {
                    let apart = distance(seen(a), seen(b));
                    assert!(
                        apart >= floor,
                        "{} {vision}: {} and {} are {apart:.3} apart",
                        content.name,
                        GRADES[i],
                        GRADES[j]
                    );
                }
            }
        }
        let wrong = theme.syntax().style_for_name(GRADES[3]);
        assert!(wrong.and_then(|s| s.background_color).is_some());
    }
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
        MultiWorkspace::new(app.workspace, window, cx)
    });
    cx.run_until_parked();
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

/// With the app's fonts and its buffer font, `!=`, `->` and `==` each shape to the two
/// glyphs their characters shape to alone: no ligature.
///
/// Lilex keeps two glyphs when its ligatures are on and swaps both for joined halves, so the
/// glyphs are compared, not counted. Windows' headless platform shapes nothing, so there the
/// test takes the windowed one; `!` and `=` shaping apart proves the shaper is real.
#[test]
fn the_buffer_font_draws_no_ligature() {
    let text_system = gpui_platform::current_platform(cfg!(not(windows))).text_system();
    let cx = TestAppContext::build_with_text_system(TestDispatcher::new(0), None, text_system);
    cx.update(|cx| {
        boot(cx);
        let fonts = assets::Assets
            .list("fonts")
            .expect("the bundled fonts list")
            .into_iter()
            .filter(|path| path.ends_with(".ttf"))
            .map(|path| {
                assets::Assets
                    .load(&path)
                    .expect("loads")
                    .expect("is there")
            })
            .collect();
        cx.text_system().add_fonts(fonts).expect("the fonts load");
        let settings = ThemeSettings::get_global(cx);
        let (font, size) = (settings.buffer_font.clone(), settings.buffer_font_size(cx));
        let shaper = WindowTextSystem::new(cx.text_system().clone());
        let glyphs = |text: &str| {
            let run = TextRun {
                len: text.len(),
                font: font.clone(),
                color: gpui::black(),
                background_color: None,
                underline: None,
                strikethrough: None,
            };
            let line = shaper.layout_line(text, size, &[run], None);
            let ids = line.runs.iter().flat_map(|run| run.glyphs.iter());
            ids.map(|glyph| glyph.id).collect::<Vec<_>>()
        };
        for pair in ["!=", "->", "=="] {
            let alone: Vec<_> = pair.chars().flat_map(|c| glyphs(&c.to_string())).collect();
            assert_eq!(alone.len(), 2, "{pair}");
            assert!(
                pair == "==" || alone[0] != alone[1],
                "{pair}: the shaper is a stand-in"
            );
            assert_eq!(glyphs(pair), alone, "{pair} shapes as a ligature");
        }
    });
}
