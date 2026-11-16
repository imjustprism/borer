//! Token-to-`TextRun` styling and clickable reference mapping for [`View`].

use std::ops::Range;
use std::sync::Arc;

use borer_engine::view::{Kind, Ref, View};
use gpui::{Font, Hsla, SharedString, TextRun};
use theme::Theme;

/// Theme keys of an import's name, the callee outside the binary: borer's own key, then
/// Zed's name for a function.
pub const IMPORT_KEYS: &[&str] = &["borer.import", "function"];

/// Returns the theme keys a token of `kind` takes its color from, in the order they are
/// tried: borer's own key where Zed has no word for the role, then Zed's syntax name.
///
/// # Arguments
///
/// * `kind` - Token kind from [`View::tokens`].
#[must_use]
pub const fn theme_keys(kind: Kind) -> &'static [&'static str] {
    match kind {
        Kind::Space | Kind::Text => &["borer.text"],
        Kind::Comment => &["comment"],
        Kind::Keyword => &["keyword"],
        Kind::Mnemonic => &["borer.mnemonic", "keyword"],
        Kind::Register => &["borer.register", "variable.special"],
        Kind::Type => &["type"],
        Kind::Function => &["function"],
        Kind::Variable => &["variable"],
        Kind::Global => &["borer.global", "constant"],
        Kind::Constant => &["constant"],
        Kind::Field => &["borer.field", "property"],
        Kind::Label => &["label"],
        Kind::Address => &["borer.address", "comment"],
        Kind::String => &["string"],
        Kind::Number => &["number"],
        Kind::Punct => &["punctuation"],
    }
}

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
    /// Function color.
    pub function: Hsla,
    /// Import color: a function token whose link is [`Ref::Import`].
    pub import: Hsla,
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
    /// Builds a [`CodePalette`] from `theme`: each role takes the color of the first of its
    /// keys ([`theme_keys`], [`IMPORT_KEYS`]) the theme's syntax sets, else the theme's text
    /// color.
    ///
    /// # Arguments
    ///
    /// * `theme` - The Zed theme to paint with, normally the active one.
    #[must_use]
    pub fn from_theme(theme: &Theme) -> Self {
        let pick = |keys: &[&str]| {
            keys.iter()
                .find_map(|key| theme.syntax().style_for_name(key).and_then(|s| s.color))
                .unwrap_or(theme.colors().text)
        };
        let of = |kind| pick(theme_keys(kind));
        Self {
            text: of(Kind::Text),
            comment: of(Kind::Comment),
            keyword: of(Kind::Keyword),
            mnemonic: of(Kind::Mnemonic),
            register: of(Kind::Register),
            ty: of(Kind::Type),
            function: of(Kind::Function),
            import: pick(IMPORT_KEYS),
            variable: of(Kind::Variable),
            global: of(Kind::Global),
            constant: of(Kind::Constant),
            field: of(Kind::Field),
            label: of(Kind::Label),
            address: of(Kind::Address),
            string: of(Kind::String),
            number: of(Kind::Number),
            punct: of(Kind::Punct),
        }
    }

    /// Maps an engine token [`Kind`] exhaustively to its foreground color; a function whose
    /// link is an import takes the import color.
    ///
    /// # Arguments
    ///
    /// * `kind` - Token kind from [`View::tokens`].
    /// * `link` - The token's referent, if it has one.
    ///
    /// # Returns
    ///
    /// Foreground [`Hsla`] color for the token.
    #[must_use]
    pub const fn color_of(&self, kind: Kind, link: Option<&Ref>) -> Hsla {
        match kind {
            Kind::Function if matches!(link, Some(Ref::Import(_))) => self.import,
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

/// The lines the code pane shows: each one a line of one of its views.
#[derive(Debug, Clone)]
pub struct CodeLines {
    /// The views the lines come from.
    views: Vec<Arc<View>>,
    /// Every shown line in order, as an index into [`Self::views`] and a line of that view.
    lines: Vec<(usize, usize)>,
}

impl CodeLines {
    /// Returns every line of `views`, each view's lines in order, one view after another.
    ///
    /// # Arguments
    ///
    /// * `views` - The decompile views to show, in order.
    #[must_use]
    pub fn new(views: Vec<Arc<View>>) -> Self {
        let lines = views
            .iter()
            .enumerate()
            .flat_map(|(v, view)| (0..view.lines()).map(move |l| (v, l)))
            .collect();
        Self { views, lines }
    }

    /// Returns these lines repeated until there are `len` of them; line `i` is line `i mod N`.
    ///
    /// # Arguments
    ///
    /// * `len` - How many lines to show; empty lines stay empty.
    #[must_use]
    pub fn cycled(mut self, len: usize) -> Self {
        self.lines = self.lines.iter().copied().cycle().take(len).collect();
        self
    }

    /// Returns how many lines there are to show.
    #[must_use]
    pub fn len(&self) -> usize {
        self.lines.len()
    }

    /// Returns whether there is no line to show.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }

    /// Returns how many views the lines come from.
    #[must_use]
    pub fn views(&self) -> usize {
        self.views.len()
    }

    /// Returns shown line `ix` as its view and its line in that view.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based index of the shown line.
    ///
    /// # Returns
    ///
    /// The view and line, or `None` past the last line.
    #[must_use]
    pub fn get(&self, ix: usize) -> Option<(&Arc<View>, usize)> {
        let &(v, l) = self.lines.get(ix)?;
        Some((self.views.get(v)?, l))
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
            runs.push(plain_run(start - cursor, font, palette.text));
            cursor = start;
        }
        if end > cursor {
            runs.push(plain_run(end - cursor, font, palette.color_of(kind, link)));
            if let Some(referent) = link {
                click_ranges.push(cursor..end);
                click_refs.push(referent.clone());
            }
            cursor = end;
        }
    }

    if cursor < raw.len() {
        runs.push(plain_run(raw.len() - cursor, font, palette.text));
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

/// Constructs a single undecorated [`TextRun`] of `len` bytes: a link is not underlined
/// at rest, and hovering one shows the pointer only.
///
/// # Arguments
///
/// * `len` - Byte length of the run.
/// * `font` - Monospace font.
/// * `color` - Foreground color.
///
/// # Returns
///
/// Configured [`TextRun`].
fn plain_run(len: usize, font: &Font, color: Hsla) -> TextRun {
    TextRun {
        len,
        font: font.clone(),
        color,
        background_color: None,
        underline: None,
        strikethrough: None,
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use borer_engine::analysis::decompile::view::{view, view_of};
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use borer_engine::view::{Ref, View};
    use gpui::{Font, Hsla};

    use super::{ClickOutcome, CodeLines, CodePalette, resolve_ref_click, style_view_line};

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
            import: base,
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
    pub(crate) fn sample_program() -> (Program, Analysis, Overlay) {
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

    /// Builds an x86-64 program whose code is every byte value in turn, four times over,
    /// so the decoder meets odd and invalid code without a file from the machine.
    fn every_byte_program() -> (Program, Analysis) {
        let bytes: Vec<u8> = (0..=u8::MAX).cycle().take(0x400).collect();
        let sections = vec![Section::mapped(".text", 0x1000, 0, 0x400, false, true)];
        let mut program = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), sections);
        program.format = BinaryFormat::Pe;
        let analysis = Analysis::compute(&program);
        (program, analysis)
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
            assert_runs_tile(&built, &font, &palette);
        }

        let utf8_text = "// café — λ\nint sub_1000(void) {\n    goto L_1000;\nL_1000:\n    return sub_1030();\n}\n";
        let extra = view_of(&program, &analysis, &overlay, 0x1000, utf8_text).expect("utf8 view");
        assert_runs_tile(&extra, &font, &palette);

        let (noise, noise_analysis) = every_byte_program();
        for func in &noise_analysis.functions {
            if let Some(built) = view(&noise, &noise_analysis, &overlay, func.entry) {
                assert_runs_tile(&built, &font, &palette);
            }
        }
    }

    /// Asserts every line's runs of `built` sum to its length on UTF-8 boundaries.
    ///
    /// # Panics
    ///
    /// Panics if a line's runs fail to tile it or split a UTF-8 codepoint.
    fn assert_runs_tile(built: &View, font: &Font, palette: &CodePalette) {
        for line_ix in 0..built.lines() {
            let styled = style_view_line(built, line_ix, font, palette);
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

    /// Code lines list each view's lines in order, and cycled ones show line `i mod N`.
    ///
    /// # Panics
    ///
    /// Panics if a shown line maps to the wrong view or line.
    #[test]
    fn code_lines_follow_their_views_and_cycle_by_index() {
        let (program, analysis, overlay) = sample_program();
        let views: Vec<_> = analysis
            .functions
            .iter()
            .filter_map(|f| view(&program, &analysis, &overlay, f.entry))
            .collect();
        let want: Vec<(usize, usize)> = views
            .iter()
            .enumerate()
            .flat_map(|(v, built)| (0..built.lines()).map(move |l| (v, l)))
            .collect();
        let code = CodeLines::new(views.clone());
        assert_eq!(code.len(), want.len());
        assert_eq!(code.views(), views.len());
        let cycled = code.cycled(want.len() * 3 + 1);
        assert_eq!(cycled.len(), want.len() * 3 + 1);
        for ix in 0..cycled.len() {
            let (v, l) = want[ix % want.len()];
            let (shown, line) = cycled.get(ix).unwrap();
            assert!(std::sync::Arc::ptr_eq(shown, &views[v]));
            assert_eq!(line, l);
        }
        assert!(cycled.get(cycled.len()).is_none());
        assert!(CodeLines::new(Vec::new()).cycled(5).is_empty());
    }
}
