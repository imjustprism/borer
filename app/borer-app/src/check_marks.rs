//! The machine's grade of each code line: a mark in the gutter of the decompile, listing
//! and linear tabs, one glyph and one color per [`Grade`].
//!
//! A decompile line takes the grade of the block it stands for ([`View::origin`], known
//! from the line origins through the text passes); a listing or linear line shows an
//! instruction, and takes the grade of the block holding it ([`Analysis::block_at`]). The
//! grade is the record of that block start in its function's check
//! ([`text_check`](borer_engine::analysis::decompile::text_check)), as the graph looks it
//! up. A line with no origin and no instruction has no mark.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;
use std::sync::Arc;

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::replay::{BlockCheck, Grade, TextCheck};
use borer_engine::view::View;
use editor::{Anchor, Editor};
use gpui::{
    App, Bounds, Context, Entity, Hsla, IntoElement, Pixels, Styled as _, TextAlign, TextRun,
    canvas, point, px,
};
use language::Point;
use theme::ActiveTheme as _;

use crate::code_view::CodeLines;
use crate::decompile_item::{buffer_row, whole_rows};
use crate::status::grade_color;

/// A line's block: the entry of the function whose check grades it, and the block's start.
pub type LineBlock = (u64, u64);

/// Every grade, each at its [`grade_index`].
pub const GRADES: [Grade; 4] = [Grade::Proved, Grade::Tested, Grade::Wrong, Grade::Unchecked];

/// Returns the place of `grade` in [`GRADES`].
///
/// # Arguments
///
/// * `grade` - The engine's grade.
#[must_use]
pub const fn grade_index(grade: Grade) -> usize {
    match grade {
        Grade::Proved => 0,
        Grade::Tested => 1,
        Grade::Wrong => 2,
        Grade::Unchecked => 3,
    }
}

/// Returns the glyph a line of `grade` is marked with, so a mark reads without its color.
///
/// # Arguments
///
/// * `grade` - The engine's grade.
#[must_use]
pub const fn glyph(grade: Grade) -> &'static str {
    match grade {
        Grade::Proved => "\u{2713}",
        Grade::Tested => "\u{2248}",
        Grade::Wrong => "\u{2717}",
        Grade::Unchecked => "?",
    }
}

/// Returns the block line `line` of `view` stands for, with the function whose check grades
/// it.
///
/// The block is the line's origin in a decompiled text, else the block holding the
/// instruction it shows; the check is `entry`'s, else that of the function owning the block.
///
/// # Arguments
///
/// * `analysis` - The binary's functions and blocks.
/// * `entry` - The tab's function, `None` for lines of no one function.
/// * `view` - The line's view.
/// * `line` - The line in `view`.
///
/// # Returns
///
/// The block, `None` for a line with no origin that shows no instruction of a known block.
#[must_use]
pub fn line_block(
    analysis: &Analysis,
    entry: Option<u64>,
    view: &View,
    line: usize,
) -> Option<LineBlock> {
    let start = match view.origin(line) {
        Some(origin) => origin,
        None => analysis.block_at(view.address(line)?)?.1.start,
    };
    let owner = match entry {
        Some(entry) => entry,
        None => analysis.block_at(start)?.0.entry,
    };
    Some((owner, start))
}

/// The grade of every shown line of a code tab, from the check of each function its lines
/// stand for.
#[derive(Debug, Default)]
pub struct Marks {
    /// Each view's lines' blocks, by view then line.
    blocks: Vec<Vec<Option<LineBlock>>>,
    /// The check of each function the lines stand for, by entry; `None` inside when the
    /// function does not decompile or the image has no emulator.
    checks: BTreeMap<u64, Arc<Option<TextCheck>>>,
}

impl Marks {
    /// Returns the marks of `code`, each function's check from `check`; runs in the
    /// background.
    ///
    /// # Arguments
    ///
    /// * `analysis` - The binary's functions and blocks.
    /// * `code` - The tab's lines.
    /// * `entry` - The tab's function, `None` for lines of no one function.
    /// * `check` - The check of the function at an entry.
    #[must_use]
    pub fn new(
        analysis: &Analysis,
        code: &CodeLines,
        entry: Option<u64>,
        mut check: impl FnMut(u64) -> Arc<Option<TextCheck>>,
    ) -> Self {
        let blocks: Vec<Vec<_>> = code
            .each_view()
            .iter()
            .map(|view| {
                (0..view.lines())
                    .map(|line| line_block(analysis, entry, view, line))
                    .collect()
            })
            .collect();
        let mut checks = BTreeMap::new();
        for &(owner, _) in blocks.iter().flatten().flatten() {
            checks.entry(owner).or_insert_with(|| check(owner));
        }
        Self { blocks, checks }
    }

    /// Returns the block shown line `row` of `code` stands for, `None` for a line with no
    /// mark.
    ///
    /// # Arguments
    ///
    /// * `code` - The lines the marks were made for.
    /// * `row` - Zero-based shown line.
    #[must_use]
    pub fn block(&self, code: &CodeLines, row: usize) -> Option<LineBlock> {
        let (v, line) = code.slot(row)?;
        *self.blocks.get(v)?.get(line)?
    }

    /// Returns the check's record of `block`, `None` when the check has none.
    ///
    /// # Arguments
    ///
    /// * `(entry, start)` - The block, with the function whose check grades it.
    #[must_use]
    pub fn record(&self, (entry, start): LineBlock) -> Option<&BlockCheck> {
        let check = self.checks.get(&entry)?.as_ref().as_ref()?;
        let ix = check
            .blocks
            .binary_search_by_key(&start, BlockCheck::start)
            .ok()?;
        check.blocks.get(ix)
    }

    /// Returns the grade shown line `row` is marked with: its block's, unchecked when the
    /// check holds no record of it; `None` for a line with no block.
    ///
    /// # Arguments
    ///
    /// * `code` - The lines the marks were made for.
    /// * `row` - Zero-based shown line.
    #[must_use]
    pub fn grade(&self, code: &CodeLines, row: usize) -> Option<Grade> {
        let block = self.block(code, row)?;
        Some(
            self.record(block)
                .map_or(Grade::Unchecked, BlockCheck::grade),
        )
    }
}

/// The key of the gutter highlight of the lines one grade marks: Zed keys a gutter
/// highlight by type, so each grade, by [`grade_index`], is a type of its own.
struct GradeMark<const G: usize>;

/// Returns the theme's color of the grade at `G` in [`GRADES`].
///
/// # Arguments
///
/// * `cx` - Application context holding the theme.
fn mark_color<const G: usize>(cx: &App) -> Hsla {
    let grade = GRADES.get(G).copied().unwrap_or_default();
    grade_color(grade, cx.theme())
}

/// Marks shown lines `rows` of `code` in the gutter of `editor`, each in its grade's color,
/// and clears the marks of every other line.
///
/// # Arguments
///
/// * `editor` - The tab's editor, over `code`'s text.
/// * `marks` - The lines' grades.
/// * `code` - The tab's lines.
/// * `rows` - Shown lines to mark; those past the last are left out.
/// * `cx` - Editor context.
pub fn paint_gutter(
    editor: &mut Editor,
    (marks, code): (&Marks, &CodeLines),
    rows: Range<usize>,
    cx: &mut Context<'_, Editor>,
) {
    let snapshot = editor.buffer().read(cx).snapshot(cx);
    let mut ranges: [Vec<Range<Anchor>>; 4] = Default::default();
    for row in rows.start..rows.end.min(code.len()) {
        let (Some(grade), Ok(at)) = (marks.grade(code, row), u32::try_from(row)) else {
            continue;
        };
        if let Some(spans) = ranges.get_mut(grade_index(grade)) {
            let start = snapshot.anchor_before(Point::new(at, 0));
            spans.push(start..start);
        }
    }
    let [proved, tested, wrong, unchecked] = ranges;
    editor.highlight_gutter::<GradeMark<0>>(proved, mark_color::<0>, cx);
    editor.highlight_gutter::<GradeMark<1>>(tested, mark_color::<1>, cx);
    editor.highlight_gutter::<GradeMark<2>>(wrong, mark_color::<2>, cx);
    editor.highlight_gutter::<GradeMark<3>>(unchecked, mark_color::<3>, cx);
}

/// Where the glyph layer last drew each mark: its bounds and its shown line, for a click.
pub type MarkHits = Rc<RefCell<Vec<(Bounds<Pixels>, usize)>>>;

/// How far right of the gutter's edge a glyph is drawn, in rows' heights: past Zed's
/// gutter highlight strip, which is 0.275 of a row wide.
const GLYPH_INSET: f32 = 0.35;

/// Returns the part of a row a scroll position of `y` rows hides above the top, in pixels.
///
/// # Arguments
///
/// * `y` - The editor's vertical scroll position, in rows.
/// * `line_height` - Height of one row.
#[expect(
    clippy::cast_possible_truncation,
    reason = "a fraction of one row, well inside f32"
)]
fn hidden_part(y: f64, line_height: Pixels) -> Pixels {
    let frac = if y.is_finite() { y - y.floor() } else { 0.0 };
    line_height * frac as f32
}

/// Returns a layer over a code tab that draws the glyph of each shown line's mark in the
/// editor's gutter, beside the gutter highlight [`paint_gutter`] draws in its color.
///
/// Zed's gutter highlight is a color strip only, so the glyph is drawn here, on the rows
/// the editor shows as it paints, through its display map so folds count.
///
/// # Arguments
///
/// * `editor` - The tab's editor.
/// * `grade_of` - The grade of a shown line, `None` for a line with no mark.
/// * `hits` - Filled with where each glyph was drawn.
pub fn glyph_layer(
    editor: Entity<Editor>,
    grade_of: impl Fn(usize, &App) -> Option<Grade> + 'static,
    hits: MarkHits,
) -> impl IntoElement {
    canvas(
        |_, _, _| {},
        move |_, (), window, cx| {
            hits.borrow_mut().clear();
            let Some(bounds) = editor.read(cx).last_bounds().copied() else {
                return;
            };
            let (font, size, height, y, map) = editor.update(cx, |editor, cx| {
                let text = editor.style(cx).text.clone();
                let rem = window.rem_size();
                let y = editor.scroll_position(cx).y;
                let height = text.line_height_in_pixels(rem);
                let size = text.font_size.to_pixels(rem);
                (text.font(), size, height, y, editor.display_snapshot(cx))
            });
            let (mut top, mut shown) = (bounds.top() - hidden_part(y, height), None);
            let mut display = whole_rows(y);
            while top < bounds.bottom() && height > px(0.0) {
                let row = buffer_row(&map, display);
                if shown != Some(row)
                    && let Some(grade) = grade_of(row, cx)
                {
                    let mark = glyph(grade);
                    let run = TextRun {
                        len: mark.len(),
                        font: font.clone(),
                        color: grade_color(grade, cx.theme()),
                        background_color: None,
                        underline: None,
                        strikethrough: None,
                    };
                    let line = window
                        .text_system()
                        .shape_line(mark.into(), size, &[run], None);
                    let at = point(bounds.left() + height * GLYPH_INSET, top);
                    line.paint(at, height, TextAlign::Left, None, window, cx)
                        .unwrap_or(());
                    let hit = Bounds::new(at, gpui::size(height, height));
                    hits.borrow_mut().push((hit, row));
                }
                shown = Some(row);
                top += height;
                display = display.saturating_add(1);
            }
        },
    )
    .absolute()
    .inset_0()
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
pub(crate) mod tests {
    use std::collections::BTreeSet;
    use std::sync::Arc;

    use borer_engine::analysis::decompile::replay::{
        BlockCheck, Claim, Disagreement, Grade, TextCheck,
    };
    use borer_engine::analysis::decompile::text_check;
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use borer_engine::view::View;
    use gpui::{Entity, TestAppContext, VisualTestContext};

    use super::{GRADES, Marks, glyph, grade_index};
    use crate::app_view::tests::{init, loaded_of, open, sample};
    use crate::code_view::CodeLines;
    use crate::decompile_item::tests::open_tab;
    use crate::decompile_item::{DecompileItem, Form};
    use crate::linear_item::tests::{open_linear, settle};
    use crate::worker::{LoadedBinary, decompile_blocking, listing_blocking, load_binary_blocking};

    /// Three blocks the check grades proved, unchecked and proved.
    ///
    /// `test ecx, ecx; je` goes to a block with a packed float multiply the replay leaves
    /// out, or to a `return 1`, so a line graded by its neighbor's block shows.
    const FLOAT_BETWEEN: [u8; 16] = [
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x06, // ASM: je 0x100a
        0x0f, 0x59, 0xc1, // ASM: mulps xmm0, xmm1
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];

    /// Most functions of the test executable whose tabs are checked.
    const TABS: usize = 12;

    /// Returns a raw x86-64 image of one function at `0x1000` holding `code`.
    pub(crate) fn one_function(code: &[u8]) -> Arc<LoadedBinary> {
        let overlay = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        let mut bytes = vec![0xcc; 0x100];
        bytes[..code.len()].copy_from_slice(code);
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let mut program = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), vec![text]);
        program.format = BinaryFormat::Pe;
        let analysis = Analysis::compute(&program);
        loaded_of(program, analysis, overlay)
    }

    /// Returns the grade line `line` of `view` should be marked with, apart from the marks.
    ///
    /// That is the record of the block it stands for (its origin, else the block holding
    /// its instruction) in the check of `entry`, else of the block's function, unchecked
    /// without one; `None` for a line with neither.
    pub(crate) fn want_grade(
        loaded: &LoadedBinary,
        entry: Option<u64>,
        view: &View,
        line: usize,
    ) -> Option<Grade> {
        let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
        let start = match view.origin(line) {
            Some(origin) => origin,
            None => a.block_at(view.address(line)?)?.1.start,
        };
        let owner = entry.unwrap_or_else(|| a.block_at(start).unwrap().0.entry);
        let check = text_check(p, a, o, owner);
        let records = check.as_ref().as_ref().map_or(&[][..], |c| &*c.blocks);
        let record = records.iter().find(|r| r.start() == start);
        Some(record.map_or(Grade::Unchecked, BlockCheck::grade))
    }

    /// Asserts every shown line of `tab` is marked as [`want_grade`] says, and returns the
    /// grades seen.
    fn assert_marked(
        tab: &Entity<DecompileItem>,
        loaded: &LoadedBinary,
        cx: &mut VisualTestContext,
    ) -> BTreeSet<usize> {
        tab.read_with(cx, |item, _| {
            let code = item.code().unwrap();
            let mut seen = BTreeSet::new();
            for row in 0..code.len() {
                let (view, line) = code.get(row).unwrap();
                let want = want_grade(loaded, item.entry(), view, line);
                assert_eq!(item.grade(row), want, "{:?} row {row}", item.entry());
                seen.extend(want.map(grade_index));
            }
            seen
        })
    }

    /// Every decompile line is marked with its origin block's grade and every instruction
    /// line of a listing tab and of the linear listing with its block's, and a line with
    /// neither has no mark, for every function of the samples and the first of the test
    /// executable.
    #[gpui::test]
    fn every_line_takes_its_block_grade(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let exe = std::env::current_exe().unwrap();
        let sources = crate::worker::Sources::default();
        let mut seen = BTreeSet::new();
        for loaded in [
            sample(),
            one_function(&FLOAT_BETWEEN),
            load_binary_blocking(exe, &sources, Vec::new()).unwrap(),
        ] {
            let entries: Vec<u64> = loaded.analysis.functions.iter().map(|f| f.entry).collect();
            for entry in entries.into_iter().take(TABS) {
                for form in [Form::Decompile, Form::Listing] {
                    let tab = open_tab(&workspace, &loaded, (entry, form), cx);
                    seen.extend(assert_marked(&tab, &loaded, cx));
                }
            }
        }
        let loaded = sample();
        let linear = open_linear(&workspace, &loaded, None, cx);
        settle(&linear, cx);
        let code = linear.read_with(cx, |item, _| item.code().clone());
        seen.extend(assert_marked(&code, &loaded, cx));
        assert!(seen.len() >= 2, "{seen:?}");
    }

    /// One block storing `rcx` whole through `rdx`.
    const STORE: [u8; 4] = [
        0x48, 0x89, 0x0a, // ASM: mov [rdx], rcx
        0xc3, // ASM: ret
    ];

    /// Returns a check of the function at `0x1000` that found its one block wrong: the text
    /// stores zero where the machine stores `rcx`.
    pub(crate) fn wrong_check() -> Arc<Option<TextCheck>> {
        let found = Disagreement {
            function: 0x1000,
            block: 0x1000,
            at: 0x1000,
            claim: Claim::Memory,
            place: "[rdx]".to_owned(),
            text: 0,
            machine: 0x1234,
            bits: 64,
            lane: false,
            expr: "0".to_owned(),
        };
        let record = BlockCheck::new(0x1000, Ok(Some("differed")), (8, 1), vec![found]);
        Arc::new(Some(TextCheck {
            blocks: vec![record],
            disagree: vec![0x1000],
        }))
    }

    /// A check that finds a block wrong marks the listing line of the disagreeing
    /// instruction and every decompile line whose origin is that block wrong, and no other.
    #[test]
    fn a_disagreeing_block_marks_its_lines_wrong() {
        let loaded = one_function(&STORE);
        let a = &*loaded.analysis;
        let listing = listing_blocking(&loaded, 0x1000).unwrap();
        let decompile = decompile_blocking(&loaded, 0x1000).unwrap();
        let mut wrong = 0;
        for view in [listing, decompile] {
            let code = CodeLines::new(vec![view.clone()]);
            let marks = Marks::new(a, &code, Some(0x1000), |_| wrong_check());
            for line in 0..view.lines() {
                let ours = view.origin(line).or(view.address(line)).is_some();
                let want = ours.then_some(Grade::Wrong);
                assert_eq!(marks.grade(&code, line), want, "{:?}", view.line(line));
                wrong += usize::from(ours);
            }
        }
        assert!(wrong >= 3, "{wrong}");
    }

    /// Each grade has a glyph of its own, so marks are told apart with their colors
    /// removed, and each sits at its own place.
    #[test]
    fn each_grade_has_its_own_glyph() {
        let glyphs: BTreeSet<_> = GRADES.iter().map(|g| glyph(*g)).collect();
        assert_eq!(glyphs.len(), GRADES.len());
        for (ix, grade) in GRADES.into_iter().enumerate() {
            assert_eq!(grade_index(grade), ix);
        }
    }
}
