//! Token-to-`TextRun` styling and clickable reference mapping for [`View`].

use std::ops::Range;

use borer_engine::view::{Kind, Ref, View};
use gpui::{App, Font, Hsla, SharedString, TextRun, UnderlineStyle, px};
use theme::ActiveTheme as _;

/// Resolved colors for every [`Kind`] token produced by [`borer_engine::view`].
#[derive(Debug, Clone, Copy)]
pub struct CodePalette {
    /// Default text and whitespace color.
    pub text: Hsla,
    /// Comment color.
    pub comment: Hsla,
    /// C keyword or assembly prefix color.
    pub keyword: Hsla,
    /// Instruction mnemonic color.
    pub mnemonic: Hsla,
    /// Machine register color.
    pub register: Hsla,
    /// Type name color.
    pub ty: Hsla,
    /// Function or import callee color.
    pub function: Hsla,
    /// Parameter or local variable color.
    pub variable: Hsla,
    /// Global or named data color.
    pub global: Hsla,
    /// Named constant or enum-member color.
    pub constant: Hsla,
    /// Struct or class field color.
    pub field: Hsla,
    /// Block label color.
    pub label: Hsla,
    /// Code or target address color.
    pub address: Hsla,
    /// String or character literal color.
    pub string: Hsla,
    /// Numeric literal color.
    pub number: Hsla,
    /// Operator and punctuation color.
    pub punct: Hsla,
}

impl CodePalette {
    /// Builds a [`CodePalette`] from the active Zed theme's syntax and UI colors.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context holding the active theme.
    ///
    /// # Returns
    ///
    /// Resolved token color palette.
    #[must_use]
    pub fn from_theme(cx: &App) -> Self {
        let theme = cx.theme();
        let colors = theme.colors();
        let syntax = theme.syntax();
        let pick = |name: &str, fallback: Hsla| {
            syntax
                .style_for_name(name)
                .and_then(|s| s.color)
                .unwrap_or(fallback)
        };
        Self {
            text: colors.text,
            comment: pick("comment", colors.text_muted),
            keyword: pick("keyword", colors.text_accent),
            mnemonic: pick("keyword", colors.text_accent),
            register: pick("variable.special", colors.text),
            ty: pick("type", colors.text_accent),
            function: pick("function", colors.text_accent),
            variable: pick("variable", colors.text),
            global: pick("constant", colors.text_accent),
            constant: pick("constant", colors.text_accent),
            field: pick("property", colors.text),
            label: pick("label", colors.text_accent),
            address: pick("link_uri", colors.text_accent),
            string: pick("string", colors.text),
            number: pick("number", colors.text),
            punct: pick("punctuation", colors.text_muted),
        }
    }

    /// Maps an engine token [`Kind`] exhaustively to its foreground color.
    ///
    /// # Arguments
    ///
    /// * `kind` - Token kind from [`View::tokens`].
    ///
    /// # Returns
    ///
    /// Foreground [`Hsla`] color for `kind`.
    #[must_use]
    pub const fn color_of(&self, kind: Kind) -> Hsla {
        match kind {
            Kind::Space | Kind::Text => self.text,
            Kind::Comment => self.comment,
            Kind::Keyword => self.keyword,
            Kind::Mnemonic => self.mnemonic,
            Kind::Register => self.register,
            Kind::Type => self.ty,
            Kind::Function => self.function,
            Kind::Variable => self.variable,
            Kind::Global => self.global,
            Kind::Constant => self.constant,
            Kind::Field => self.field,
            Kind::Label => self.label,
            Kind::Address => self.address,
            Kind::String => self.string,
            Kind::Number => self.number,
            Kind::Punct => self.punct,
        }
    }
}

/// Styled runs and ordered clickable token ranges for one line of a [`View`].
#[derive(Debug, Clone)]
pub struct StyledLine {
    /// Line text without its trailing newline.
    pub text: SharedString,
    /// Contiguous [`TextRun`] slices tiling [`Self::text`] byte for byte.
    pub runs: Vec<TextRun>,
    /// Byte ranges within [`Self::text`] of every token carrying a [`Ref`], in line order.
    pub click_ranges: Vec<Range<usize>>,
    /// Referent corresponding 1:1 with each entry in [`Self::click_ranges`].
    pub click_refs: Vec<Ref>,
}

/// Navigation action triggered when the user clicks a linked token [`Ref`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClickOutcome {
    /// Opens the function at the given entry virtual address, pushing history.
    OpenFunction(u64),
    /// Scrolls the current view to the 0-based line where the referent is defined.
    ScrollToLine(usize),
    /// Token link has no click navigation in the spike.
    None,
}

/// Resolves clicking `target` inside `view` into a [`ClickOutcome`].
///
/// # Arguments
///
/// * `view` - Active [`View`] supplying intra-function definition lines.
/// * `target` - Engine referent attached to the clicked token.
///
/// # Returns
///
/// Resulting [`ClickOutcome`] without parsing any text.
#[must_use]
pub fn resolve_ref_click(view: &View, target: &Ref) -> ClickOutcome {
    match target {
        Ref::Function(entry) => ClickOutcome::OpenFunction(*entry),
        Ref::Address(_) => view
            .definition(target)
            .map_or(ClickOutcome::None, ClickOutcome::ScrollToLine),
        Ref::Import(_)
        | Ref::Global(_)
        | Ref::Variable { .. }
        | Ref::Type(_)
        | Ref::String(_)
        | Ref::Field { .. } => ClickOutcome::None,
    }
}

/// Builds contiguous [`TextRun`]s and clickable ranges for `line_ix` of `view`.
///
/// Every run boundary is checked against UTF-8 character boundaries on the line
/// so `StyledText::with_runs` never panics even on hostile or empty lines.
///
/// # Arguments
///
/// * `view` - Tokenized engine [`View`].
/// * `line_ix` - Zero-based line index in `view`.
/// * `font` - Monospace buffer font applied to every run.
/// * `palette` - Syntax color table.
///
/// # Returns
///
/// [`StyledLine`] whose `runs` tile `text` and whose `click_ranges` match linked tokens.
#[must_use]
pub fn style_view_line(
    view: &View,
    line_ix: usize,
    font: &Font,
    palette: &CodePalette,
) -> StyledLine {
    let raw = view.line(line_ix).unwrap_or_default();
    let mut runs = Vec::new();
    let mut click_ranges = Vec::new();
    let mut click_refs = Vec::new();
    let mut cursor = 0usize;

    for (span, kind, link) in view.tokens(line_ix) {
        let start = clamp_char_boundary(raw, span.start.max(cursor));
        let end = clamp_char_boundary(raw, span.end.max(start));
        if start > cursor {
            runs.push(plain_run(start - cursor, font, palette.text, false));
            cursor = start;
        }
        if end > cursor {
            let color = palette.color_of(kind);
            runs.push(plain_run(end - cursor, font, color, link.is_some()));
            if let Some(referent) = link {
                click_ranges.push(cursor..end);
                click_refs.push(referent.clone());
            }
            cursor = end;
        }
    }

    if cursor < raw.len() {
        runs.push(plain_run(raw.len() - cursor, font, palette.text, false));
    }

    StyledLine {
        text: SharedString::from(raw.to_owned()),
        runs,
        click_ranges,
        click_refs,
    }
}

/// Clamps `idx` to `text.len()` and walks back to a valid UTF-8 char boundary.
///
/// # Arguments
///
/// * `text` - UTF-8 line slice.
/// * `idx` - Candidate byte offset.
///
/// # Returns
///
/// Largest valid char boundary in `text` at or below `idx`.
fn clamp_char_boundary(text: &str, idx: usize) -> usize {
    let mut pos = idx.min(text.len());
    while pos > 0 && !text.is_char_boundary(pos) {
        pos -= 1;
    }
    pos
}

/// Constructs a single [`TextRun`] of `len` bytes with optional link underline.
///
/// # Arguments
///
/// * `len` - Byte length of the run.
/// * `font` - Monospace font.
/// * `color` - Foreground color.
/// * `underlined` - Whether to underline the token as a clickable link.
///
/// # Returns
///
/// Configured [`TextRun`].
fn plain_run(len: usize, font: &Font, color: Hsla, underlined: bool) -> TextRun {
    TextRun {
        len,
        font: font.clone(),
        color,
        background_color: None,
        underline: underlined.then_some(UnderlineStyle {
            thickness: px(1.0),
            color: Some(color),
            wavy: false,
        }),
        strikethrough: None,
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use borer_engine::analysis::decompile::view::{view, view_of};
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use borer_engine::view::Ref;
    use gpui::{Font, Hsla};

    use super::{ClickOutcome, CodePalette, resolve_ref_click, style_view_line};

    /// Builds a deterministic test palette without requiring a GPUI window.
    fn sample_palette() -> CodePalette {
        let base = Hsla {
            h: 0.0,
            s: 0.0,
            l: 0.85,
            a: 1.0,
        };
        CodePalette {
            text: base,
            comment: base,
            keyword: base,
            mnemonic: base,
            register: base,
            ty: base,
            function: base,
            variable: base,
            global: base,
            constant: base,
            field: base,
            label: base,
            address: base,
            string: base,
            number: base,
            punct: base,
        }
    }

    /// Builds a small multi-function x86-64 program exercising calls, branches,
    /// labels, strings, and globals.
    fn sample_program() -> (Program, Analysis, Overlay) {
        let mut bytes = vec![0u8; 0x200];
        bytes[..0x100].fill(0xcc);
        // ASM: sub rsp, 0x28 ; test ecx, ecx ; jz +0x7 ; call 0x1030 ; jmp +0xc ; lea rcx, [rip+0xea] ; call 0x1030 ; add rsp, 0x28 ; ret
        let caller: &[u8] = &[
            0x48, 0x83, 0xec, 0x28, 0x85, 0xc9, 0x74, 0x07, 0xe8, 0x23, 0x00, 0x00, 0x00, 0xeb,
            0x0c, 0x48, 0x8d, 0x0d, 0xea, 0x00, 0x00, 0x00, 0xe8, 0x15, 0x00, 0x00, 0x00, 0x48,
            0x83, 0xc4, 0x28, 0xc3,
        ];
        // ASM: mov eax, dword ptr [rcx] ; add eax, 1 ; ret
        let callee: &[u8] = &[0x8b, 0x01, 0x83, 0xc0, 0x01, 0xc3];
        bytes[0..caller.len()].copy_from_slice(caller);
        bytes[0x30..0x30 + callee.len()].copy_from_slice(callee);
        let greeting = b"hello world\0";
        bytes[0x100..0x100 + greeting.len()].copy_from_slice(greeting);
        let sections = vec![
            Section::mapped(".text", 0x1000, 0, 0x100, false, true),
            Section::mapped(".rdata", 0x1100, 0x100, 0x100, false, false),
        ];
        let mut program = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), sections);
        program.format = BinaryFormat::Pe;
        let analysis = Analysis::compute(&program);
        let overlay = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        (program, analysis, overlay)
    }

    /// Run lengths sum to each line's byte length and land on UTF-8 boundaries.
    ///
    /// # Panics
    ///
    /// Panics if any line's runs fail to tile the line or split a UTF-8 codepoint.
    #[test]
    fn runs_tile_every_line_on_char_boundaries() {
        let (program, analysis, overlay) = sample_program();
        let font: Font = gpui::font("Cascadia Mono");
        let palette = sample_palette();
        assert!(analysis.functions.len() >= 2);

        for func in &analysis.functions {
            let built = view(&program, &analysis, &overlay, func.entry).expect("decompiles");
            for line_ix in 0..built.lines() {
                let styled = style_view_line(&built, line_ix, &font, &palette);
                let mut offset = 0usize;
                for run in &styled.runs {
                    offset += run.len;
                    assert!(
                        styled.text.is_char_boundary(offset),
                        "non-char boundary at {offset} in {:?}",
                        styled.text
                    );
                }
                assert_eq!(offset, styled.text.len());
            }
        }

        let utf8_text = "// café — λ\nint sub_1000(void) {\n    goto L_1000;\nL_1000:\n    return sub_1030();\n}\n";
        let extra = view_of(&program, &analysis, &overlay, 0x1000, utf8_text).expect("utf8 view");
        for line_ix in 0..extra.lines() {
            let styled = style_view_line(&extra, line_ix, &font, &palette);
            let mut offset = 0usize;
            for run in &styled.runs {
                offset += run.len;
                assert!(styled.text.is_char_boundary(offset));
            }
            assert_eq!(offset, styled.text.len());
        }

        if let Ok(real_prog) = Program::load(Path::new(r"C:\Windows\System32\whoami.exe")) {
            let real_analysis = Analysis::compute(&real_prog);
            assert!(!real_analysis.functions.is_empty());
            for func in &real_analysis.functions {
                if let Some(built) = view(&real_prog, &real_analysis, &overlay, func.entry) {
                    for line_ix in 0..built.lines() {
                        let styled = style_view_line(&built, line_ix, &font, &palette);
                        let mut offset = 0usize;
                        for run in &styled.runs {
                            offset += run.len;
                            assert!(styled.text.is_char_boundary(offset));
                        }
                        assert_eq!(offset, styled.text.len());
                    }
                }
            }
        }
    }

    /// Clickable ranges match every linked token in line order and map back to its [`Ref`].
    ///
    /// # Panics
    ///
    /// Panics if clickable ranges differ from linked tokens or resolve to the wrong target.
    #[test]
    fn click_ranges_match_linked_tokens_in_order() {
        let (program, analysis, overlay) = sample_program();
        let font: Font = gpui::font("Cascadia Mono");
        let palette = sample_palette();
        let mut total_links = 0usize;
        let mut saw_callee = false;

        for func in &analysis.functions {
            let built = view(&program, &analysis, &overlay, func.entry).expect("decompiles");
            for line_ix in 0..built.lines() {
                let expected: Vec<_> = built
                    .tokens(line_ix)
                    .filter_map(|(span, _, link)| Some((span, link?.clone())))
                    .collect();
                let styled = style_view_line(&built, line_ix, &font, &palette);
                assert_eq!(styled.click_ranges.len(), expected.len());
                assert_eq!(styled.click_refs.len(), expected.len());
                for (range_ix, (want_span, want_ref)) in expected.iter().enumerate() {
                    assert_eq!(&styled.click_ranges[range_ix], want_span);
                    assert_eq!(&styled.click_refs[range_ix], want_ref);
                    if want_ref == &Ref::Function(0x1030) {
                        saw_callee = true;
                        assert_eq!(
                            resolve_ref_click(&built, &styled.click_refs[range_ix]),
                            ClickOutcome::OpenFunction(0x1030)
                        );
                    }
                    total_links += 1;
                }
            }
        }
        assert!(total_links >= 2);
        assert!(saw_callee);

        let goto_text = "void sub_1000(void) {\n    goto L_1000;\nL_1000:\n    return;\n}\n";
        let goto_view =
            view_of(&program, &analysis, &overlay, 0x1000, goto_text).expect("goto view");
        let line1 = style_view_line(&goto_view, 1, &font, &palette);
        assert_eq!(line1.click_refs, vec![Ref::Address(0x1000)]);
        assert_eq!(
            resolve_ref_click(&goto_view, &line1.click_refs[0]),
            ClickOutcome::ScrollToLine(2)
        );
    }
}
