//! The theme contract, held by borer's own themes and checked on any theme a person imports.
//!
//! Text roles read on the editor and on a panel, the chrome's text also on the status bar,
//! the title bar and a popover; the check grades rise with evidence and stay apart under
//! color-vision deficiency; and every `borer.*` key is set.
//!
//! The one copy of the color maths: WCAG 2 contrast, `OKLab` distance, and the Machado
//! (2009) simulation of deuteranopia, protanopia and tritanopia at severity 1.0.

use std::fmt;
use std::sync::OnceLock;

use gpui::{Hsla, Rgba};
use theme::Theme;
use theme_settings::{ThemeContent, refine_theme};

use crate::app_settings::BORER_THEME;
use crate::code_view::Role;

/// Grade keys from least to most evidence, then the refuted grade.
pub const GRADES: [&str; 4] = [
    "borer.grade.unchecked",
    "borer.grade.tested",
    "borer.grade.proved",
    "borer.grade.wrong",
];

/// The syntax key of zero bytes, the one de-emphasized syntax role.
pub const ZERO_BYTE: &str = "borer.byte.zero";

/// Least contrast of a text role on the editor and on a panel, as a ratio to 1.
pub const TEXT_FLOOR: f64 = 4.5;

/// Least contrast of a de-emphasized role (zero bytes, placeholders, muted icons).
pub const QUIET_FLOOR: f64 = 3.0;

/// Least `OKLab` distance of two grades in normal vision.
pub const GRADE_APART: f64 = 0.12;

/// Least `OKLab` distance of two grades under each simulated deficiency.
pub const GRADE_APART_SIMULATED: f64 = 0.08;

/// Machado (2009) simulation matrices at severity 1.0 over linear sRGB, by deficiency.
pub const MACHADO: [(&str, [[f64; 3]; 3]); 3] = [
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

/// One rule a theme breaks, with the numbers that break it; its `Display` is one line.
#[derive(Debug, Clone, PartialEq)]
pub enum Failure {
    /// `role` reads at `ratio` to 1 on `background`, under its `floor`.
    Contrast {
        /// The foreground role.
        role: String,
        /// The background slot measured against.
        background: &'static str,
        /// The measured WCAG 2 contrast ratio.
        ratio: f64,
        /// The least ratio the role needs.
        floor: f64,
    },
    /// The grade `lower` contrasts with the editor at least as much as `higher`, which
    /// holds more evidence.
    Ramp {
        /// The grade with less evidence.
        lower: &'static str,
        /// The grade with more evidence.
        higher: &'static str,
        /// `lower`'s contrast with the editor background.
        lower_ratio: f64,
        /// `higher`'s contrast with the editor background.
        higher_ratio: f64,
    },
    /// Grades `a` and `b` are `distance` apart in `OKLab` under `vision`, under `floor`.
    Close {
        /// One grade key.
        a: &'static str,
        /// The other grade key.
        b: &'static str,
        /// `normal vision` or the simulated deficiency.
        vision: &'static str,
        /// The measured distance.
        distance: f64,
        /// The least distance the grades need.
        floor: f64,
    },
    /// The refuted grade sets no background, so a wrong row is not tinted.
    UntintedWrong,
    /// The theme does not set `role`; the app paints it with `fallback`'s color when the
    /// theme sets that key, else with the text color.
    Unset {
        /// The key the theme leaves unset.
        role: String,
        /// The key the app falls back to, if the role has one.
        fallback: Option<&'static str>,
    },
    /// `role` is not opaque, and contrast is measured on opaque colors only.
    Translucent {
        /// The role with transparency.
        role: String,
    },
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Contrast {
                role,
                background,
                ratio,
                floor,
            } => write!(f, "{role} on {background}: {ratio:.2}:1, floor {floor}:1"),
            Self::Ramp {
                lower,
                higher,
                lower_ratio,
                higher_ratio,
            } => write!(
                f,
                "{lower} ({lower_ratio:.2}:1) must contrast less than {higher} \
                 ({higher_ratio:.2}:1) on editor.background"
            ),
            Self::Close {
                a,
                b,
                vision,
                distance,
                floor,
            } => write!(
                f,
                "{a} and {b} under {vision}: {distance:.3} apart, floor {floor}"
            ),
            Self::UntintedWrong => write!(f, "{} sets no background to tint its row", GRADES[3]),
            Self::Unset {
                role,
                fallback: Some(key),
            } => write!(f, "{role} is unset; falls back to {key}"),
            Self::Unset {
                role,
                fallback: None,
            } => write!(f, "{role} is unset; falls back to the text color"),
            Self::Translucent { role } => {
                write!(
                    f,
                    "{role} is translucent; contrast is measured on opaque colors"
                )
            }
        }
    }
}

/// Returns every rule the theme `content` describes breaks: [`text_floors`], then
/// [`grade_rules`], then [`unset_keys`]; empty when it keeps the contract.
///
/// # Arguments
///
/// * `content` - The theme as its file writes it.
#[must_use]
pub fn check(content: &ThemeContent) -> Vec<Failure> {
    let theme = refine_theme(content);
    let mut failures = text_floors(content, &theme);
    failures.extend(grade_rules(&theme));
    failures.extend(unset_keys(&theme));
    failures
}

/// Returns the contrast rules `theme` breaks.
///
/// Every syntax color but the grades and zero bytes, and the editor foreground, are held to
/// [`TEXT_FLOOR`] on the editor and on a panel. The text, muted and accent colors are held
/// to it on every surface of the chrome too (the status bar, the title bar and a popover),
/// and placeholders and muted icons to [`QUIET_FLOOR`] there; zero bytes to
/// [`QUIET_FLOOR`] on the editor and a panel. A see-through color is measured as drawn,
/// over the surface.
///
/// The syntax keys are walked once, in the order `content` writes them.
///
/// # Arguments
///
/// * `content` - The theme as its file writes it, for its syntax keys.
/// * `theme` - `content` as Zed refines it, for its colors.
#[must_use]
pub fn text_floors(content: &ThemeContent, theme: &Theme) -> Vec<Failure> {
    let colors = theme.colors();
    let mut failures = Vec::new();
    let surfaces: Vec<_> = [
        ("editor.background", colors.editor_background),
        ("panel.background", colors.panel_background),
        ("status_bar.background", colors.status_bar_background),
        ("title_bar.background", colors.title_bar_background),
        (
            "elevated_surface.background",
            colors.elevated_surface_background,
        ),
    ]
    .into_iter()
    .filter(|&(role, color)| opaque(role, color, &mut failures).is_some())
    .collect();
    let code = |background: &str| matches!(background, "editor.background" | "panel.background");
    let syntax = content.style.syntax.keys().filter_map(|key| {
        let text = !GRADES.contains(&key.as_str()) && key != ZERO_BYTE;
        Some((
            key.as_str(),
            syntax_color(theme, key).filter(|_| text)?,
            TEXT_FLOOR,
            true,
        ))
    });
    let mut roles: Vec<_> = syntax.collect();
    roles.extend([
        ("text", colors.text, TEXT_FLOOR, false),
        ("text.muted", colors.text_muted, TEXT_FLOOR, false),
        ("text.accent", colors.text_accent, TEXT_FLOOR, false),
        (
            "editor.foreground",
            colors.editor_foreground,
            TEXT_FLOOR,
            true,
        ),
    ]);
    match syntax_color(theme, ZERO_BYTE) {
        Some(color) => roles.push((ZERO_BYTE, color, QUIET_FLOOR, true)),
        None => failures.push(unset(ZERO_BYTE)),
    }
    roles.extend([
        (
            "text.placeholder",
            colors.text_placeholder,
            QUIET_FLOOR,
            false,
        ),
        ("icon.muted", colors.icon_muted, QUIET_FLOOR, false),
    ]);
    for (role, color, floor, code_only) in roles {
        for &(background, behind) in surfaces.iter().filter(|(b, _)| !code_only || code(b)) {
            let ratio = contrast(color, behind);
            if ratio < floor {
                failures.push(Failure::Contrast {
                    role: role.to_owned(),
                    background,
                    ratio,
                    floor,
                });
            }
        }
    }
    failures
}
/// Returns the grade rules `theme` breaks.
///
/// The unchecked, tested and proved grades contrast more with the editor as evidence
/// rises; every pair of the four grades stays [`GRADE_APART`] apart in `OKLab`, and
/// [`GRADE_APART_SIMULATED`] under each [`MACHADO`] simulation; and the refuted grade tints
/// its row.
///
/// # Arguments
///
/// * `theme` - The theme as Zed refines it.
#[must_use]
pub fn grade_rules(theme: &Theme) -> Vec<Failure> {
    let mut failures = Vec::new();
    let editor = theme.colors().editor_background;
    let found = GRADES.map(|key| syntax_color(theme, key));
    let missing = GRADES
        .iter()
        .zip(found)
        .filter(|(_, color)| color.is_none());
    failures.extend(missing.map(|(key, _)| unset(key)));
    let editor = opaque("editor.background", editor, &mut failures);
    let seen: Vec<_> = GRADES
        .iter()
        .zip(found)
        .filter_map(|(key, color)| Some((*key, opaque(key, color?, &mut failures)?)))
        .collect();
    let (Some(editor), Some(ramp)) = (
        editor,
        seen.get(..GRADES.len() - 1)
            .filter(|_| seen.len() == GRADES.len()),
    ) else {
        return failures;
    };
    for pair in ramp.windows(2) {
        let &[(lower, x), (higher, y)] = pair else {
            continue;
        };
        let (lower_ratio, higher_ratio) = (contrast_linear(x, editor), contrast_linear(y, editor));
        if lower_ratio >= higher_ratio {
            failures.push(Failure::Ramp {
                lower,
                higher,
                lower_ratio,
                higher_ratio,
            });
        }
    }
    let visions = std::iter::once(("normal vision", GRADE_APART, None))
        .chain(MACHADO.map(|(name, matrix)| (name, GRADE_APART_SIMULATED, Some(matrix))));
    for (vision, floor, matrix) in visions {
        let at = |rgb| oklab(matrix.map_or(rgb, |m| simulate(rgb, m)));
        for (i, &(a, x)) in seen.iter().enumerate() {
            for &(b, y) in seen.iter().skip(i + 1) {
                let apart = distance(at(x), at(y));
                if apart < floor {
                    failures.push(Failure::Close {
                        a,
                        b,
                        vision,
                        distance: apart,
                        floor,
                    });
                }
            }
        }
    }
    let wrong = theme.syntax().style_for_name(GRADES[3]);
    if wrong.and_then(|style| style.background_color).is_none() {
        failures.push(Failure::UntintedWrong);
    }
    failures
}

/// Returns a [`Failure::Unset`] for every `borer.*` key borer's own themes set that
/// `theme` does not, past the grades and zero bytes, whose rules say so themselves.
///
/// # Arguments
///
/// * `theme` - The theme as Zed refines it.
#[must_use]
pub fn unset_keys(theme: &Theme) -> Vec<Failure> {
    borer_keys()
        .iter()
        .map(String::as_str)
        .filter(|key| !GRADES.contains(key) && *key != ZERO_BYTE)
        .filter(|key| theme.syntax().style_for_name(key).is_none())
        .map(unset)
        .collect()
}

/// Returns the `borer.*` syntax keys of borer's own dark theme, in the file's order, read
/// once; none when the bundled family does not parse, which a test rules out.
fn borer_keys() -> &'static [String] {
    static KEYS: OnceLock<Vec<String>> = OnceLock::new();
    KEYS.get_or_init(|| {
        let Ok(family) = theme_settings::deserialize_user_theme(BORER_THEME) else {
            return Vec::new();
        };
        let syntax = family.themes.into_iter().next().map(|t| t.style.syntax);
        let keys = syntax.into_iter().flat_map(|syntax| syntax.into_keys());
        keys.filter(|key| key.starts_with("borer.")).collect()
    })
}

/// Returns a [`Failure::Unset`] for `role`, with the key the app paints it with instead.
///
/// That is `comment` for zero bytes, as the hex tab does, the muted text color for a grade,
/// as the status bar does, else the next of its [`Role::keys`], if it is the first of them.
///
/// # Arguments
///
/// * `role` - The unset key.
fn unset(role: &str) -> Failure {
    let fallback = match role {
        ZERO_BYTE => Some("comment"),
        grade if GRADES.contains(&grade) => Some("text.muted"),
        _ => Role::ALL
            .iter()
            .map(|r| r.keys())
            .find(|keys| keys.first() == Some(&role))
            .and_then(|keys| keys.get(1).copied()),
    };
    Failure::Unset {
        role: role.to_owned(),
        fallback,
    }
}

/// Returns the color `theme`'s syntax sets for `key`, if it sets one.
///
/// # Arguments
///
/// * `theme` - The theme.
/// * `key` - The syntax key.
#[must_use]
pub fn syntax_color(theme: &Theme, key: &str) -> Option<Hsla> {
    theme.syntax().style_for_name(key)?.color
}

/// Returns `color`'s linear sRGB channels when it is opaque, else records `role` as
/// [`Failure::Translucent`] in `failures` and returns `None`.
///
/// # Arguments
///
/// * `role` - The role the color is for, to name in a failure.
/// * `color` - The color.
/// * `failures` - Where a translucent color is recorded.
fn opaque(role: &str, color: Hsla, failures: &mut Vec<Failure>) -> Option<[f64; 3]> {
    let linear = linear(color);
    if linear.is_none() {
        failures.push(Failure::Translucent {
            role: role.to_owned(),
        });
    }
    linear
}

/// Returns `color`'s linear sRGB channels, or `None` when it is not opaque.
///
/// # Arguments
///
/// * `color` - The color.
#[must_use]
pub fn linear(color: Hsla) -> Option<[f64; 3]> {
    let rgba = Rgba::from(color);
    if (rgba.a - 1.0).abs() >= 1e-6 {
        return None;
    }
    Some([rgba.r, rgba.g, rgba.b].map(|c| {
        let c = f64::from(c);
        if c <= 0.04045 {
            c / 12.92
        } else {
            ((c + 0.055) / 1.055).powf(2.4)
        }
    }))
}

/// Returns the WCAG 2 contrast ratio of `a` drawn over `b`: a see-through `a` is blended
/// over `b` first; a see-through `b` counts as black.
///
/// # Arguments
///
/// * `a` - The color drawn, such as text.
/// * `b` - The surface it is drawn on.
#[must_use]
pub fn contrast(a: Hsla, b: Hsla) -> f64 {
    let (fg, bg) = (Rgba::from(a), Rgba::from(b));
    let blend = |f: f32, b: f32| f.mul_add(fg.a, b * (1.0 - fg.a));
    let drawn = Rgba {
        r: blend(fg.r, bg.r),
        g: blend(fg.g, bg.g),
        b: blend(fg.b, bg.b),
        a: 1.0,
    };
    contrast_linear(
        linear(drawn.into()).unwrap_or_default(),
        linear(b).unwrap_or_default(),
    )
}

/// Returns the WCAG 2 contrast ratio of two linear sRGB colors.
///
/// # Arguments
///
/// * `a` - One color.
/// * `b` - The other color.
fn contrast_linear(a: [f64; 3], b: [f64; 3]) -> f64 {
    let luminance = |[r, g, b]: [f64; 3]| 0.0722f64.mul_add(b, 0.2126f64.mul_add(r, 0.7152 * g));
    let (x, y) = (luminance(a), luminance(b));
    (x.max(y) + 0.05) / (x.min(y) + 0.05)
}

/// Returns linear sRGB `[r, g, b]` in `OKLab`.
///
/// # Arguments
///
/// * `rgb` - Linear sRGB channels.
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
///
/// # Arguments
///
/// * `rgb` - Linear sRGB channels.
/// * `matrix` - A [`MACHADO`] simulation matrix.
fn simulate(rgb: [f64; 3], matrix: [[f64; 3]; 3]) -> [f64; 3] {
    matrix.map(|row| {
        row[0]
            .mul_add(rgb[0], row[1].mul_add(rgb[1], row[2] * rgb[2]))
            .clamp(0.0, 1.0)
    })
}

/// Returns the Euclidean distance of two `OKLab` colors.
///
/// # Arguments
///
/// * `a` - One color.
/// * `b` - The other color.
fn distance(a: [f64; 3], b: [f64; 3]) -> f64 {
    a.iter()
        .zip(b)
        .map(|(x, y)| (x - y).powi(2))
        .sum::<f64>()
        .sqrt()
}
