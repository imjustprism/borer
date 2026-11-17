//! The machine's grade of each code line: a mark in the gutter of the decompile, listing
//! and linear tabs, one glyph and one color per [`Grade`].
//!
//! A decompile line takes the grade of the block it stands for ([`View::origin`], known
//! from the line origins through the text passes); a listing or linear line shows an
//! instruction, and takes the grade of the block holding it ([`Analysis::block_at`]). The
//! grade is the record of that block start in its function's check, the one the graph and
//! the status bar read ([`check_blocking`](crate::worker::check_blocking)). A line with no
//! origin and no instruction has no mark.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;
use std::sync::Arc;

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::replay::{BlockCheck, Grade, TextCheck};
use borer_engine::view::View;
use editor::display_map::{
    BlockContext, BlockPlacement, BlockProperties, BlockStyle, CustomBlockId, RenderBlock,
};
use editor::{Anchor, Editor};
use gpui::{
    App, Bounds, Context, Entity, Hsla, IntoElement, ParentElement as _, Pixels, SharedString,
    Styled as _, TextAlign, TextRun, canvas, div, point, px,
};
use language::Point;
use theme::ActiveTheme as _;
use ui::{Color, Label, LabelCommon as _};

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
    /// The records rechecks gave, which stand in for the check's.
    rechecked: BTreeMap<LineBlock, BlockCheck>,
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
        Self {
            blocks,
            checks,
            rechecked: BTreeMap::new(),
        }
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

    /// Puts `record`, what a recheck of `block` gave, in place of the check's record of it.
    ///
    /// # Arguments
    ///
    /// * `block` - The block, with the function whose check graded it.
    /// * `record` - The recheck's record.
    pub fn set_recheck(&mut self, block: LineBlock, record: BlockCheck) {
        self.rechecked.insert(block, record);
    }

    /// Returns the record of `block`: the last recheck's, else the check's; `None` when
    /// neither has one.
    ///
    /// # Arguments
    ///
    /// * `(entry, start)` - The block, with the function whose check grades it.
    #[must_use]
    pub fn record(&self, (entry, start): LineBlock) -> Option<&BlockCheck> {
        if let Some(record) = self.rechecked.get(&(entry, start)) {
            return Some(record);
        }
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

    /// Returns the evidence behind shown line `row`'s mark: its block's record as the
    /// engine spells it, and for a decompile line how its block is known.
    ///
    /// # Arguments
    ///
    /// * `code` - The lines the marks were made for.
    /// * `row` - Zero-based shown line.
    ///
    /// # Returns
    ///
    /// The evidence, `None` for a line with no mark.
    #[must_use]
    pub fn evidence(&self, code: &CodeLines, row: usize) -> Option<String> {
        let block @ (_, start) = self.block(code, row)?;
        let mut said = self.record(block).map_or_else(
            || format!("block {start:#x}: unchecked: the check holds no record of it"),
            BlockCheck::spell,
        );
        let (view, line) = code.get(row)?;
        if view.origin(line).is_some() {
            said.push_str(&format!(
                "\nthis line stands for block {start:#x}, known from the line origins through the text passes"
            ));
        }
        Some(said)
    }

    /// Returns the next shown line after `from` marked wrong, or the one before it when
    /// `back`, going round past either end; `from` itself is the last tried.
    ///
    /// # Arguments
    ///
    /// * `code` - The lines the marks were made for.
    /// * `from` - Zero-based shown line to start from.
    /// * `back` - Whether to look upward.
    ///
    /// # Returns
    ///
    /// The line, `None` when no line is marked wrong.
    #[must_use]
    pub fn next_wrong(&self, code: &CodeLines, from: usize, back: bool) -> Option<usize> {
        let n = code.len();
        let from = from.min(n.saturating_sub(1));
        (1..=n)
            .map(|k| {
                if back {
                    (from + n - k) % n
                } else {
                    (from + k) % n
                }
            })
            .find(|&row| self.grade(code, row) == Some(Grade::Wrong))
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

/// Shows `said`, the evidence behind a line's mark, in a block under shown line `row` of
/// `editor`, one row of the editor per line of it.
///
/// # Arguments
///
/// * `editor` - The tab's editor.
/// * `row` - Zero-based shown line.
/// * `said` - The evidence.
/// * `cx` - Editor context.
///
/// # Returns
///
/// The block, to remove it by.
pub fn insert_evidence(
    editor: &mut Editor,
    row: usize,
    said: &str,
    cx: &mut Context<'_, Editor>,
) -> Option<CustomBlockId> {
    let lines: Vec<SharedString> = said.lines().map(|l| l.to_owned().into()).collect();
    let height = u32::try_from(lines.len()).ok()?;
    let at = Point::new(u32::try_from(row).ok()?, 0);
    let anchor = editor.buffer().read(cx).snapshot(cx).anchor_after(at);
    let render: RenderBlock = Arc::new(move |block: &mut BlockContext<'_, '_>| {
        let rows = lines.iter().map(|line| {
            let label = Label::new(line.clone())
                .buffer_font(block.app)
                .color(Color::Muted);
            div().h(block.line_height).child(label)
        });
        div()
            .pl(block.margins.gutter.full_width())
            .children(rows)
            .into_any_element()
    });
    let properties = BlockProperties {
        placement: BlockPlacement::Below(anchor),
        height: Some(height),
        style: BlockStyle::Fixed,
        render,
        priority: 0,
    };
    editor.insert_blocks([properties], None, cx).pop()
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

    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use borer_engine::view::View;
    use gpui::{Entity, TestAppContext, VisualTestContext};

    use super::{GRADES, Marks, glyph, grade_index};
    use crate::app_view::tests::{CALLEE, CALLER, init, loaded_of, open, sample};
    use crate::code_view::CodeLines;
    use crate::decompile_item::tests::{open_tab, put_cursor};
    use crate::decompile_item::{DecompileItem, Form};
    use crate::linear_item::tests::{open_linear, settle};
    use crate::worker::{
        LoadedBinary, check_blocking, decompile_blocking, listing_blocking, load_binary_blocking,
    };

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
        let a = &*loaded.analysis;
        let start = match view.origin(line) {
            Some(origin) => origin,
            None => a.block_at(view.address(line)?)?.1.start,
        };
        let owner = entry.unwrap_or_else(|| a.block_at(start).unwrap().0.entry);
        let check = check_blocking(loaded, owner);
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

    /// Returns the evidence line `line` of `view` should show, apart from the marks: its
    /// block's record as the engine spells it, and the origins sentence on a decompile line.
    fn want_evidence(loaded: &LoadedBinary, entry: u64, view: &View, line: usize) -> String {
        let a = &*loaded.analysis;
        let start = view
            .origin(line)
            .unwrap_or_else(|| a.block_at(view.address(line).unwrap()).unwrap().1.start);
        let check = check_blocking(loaded, entry);
        let record = check.as_ref().as_ref().unwrap();
        let record = record.blocks.iter().find(|r| r.start() == start).unwrap();
        let mut want = record.spell();
        if view.origin(line).is_some() {
            want.push_str(&format!(
                "\nthis line stands for block {start:#x}, known from the line origins through the text passes"
            ));
        }
        want
    }

    /// The evidence under a marked line is its block's record as the engine spells it, with
    /// one more sentence on a decompile line; a line with no mark shows none, and asking
    /// again on the same line hides it.
    #[gpui::test]
    fn the_evidence_is_the_engine_spelling_of_the_line_block(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let mut shown = [0; 2];
        let tabs = [
            (sample(), CALLER),
            (sample(), CALLEE),
            (one_function(&FLOAT_BETWEEN), 0x1000),
        ];
        for ((loaded, entry), form) in tabs
            .into_iter()
            .flat_map(|tab| [(tab.clone(), Form::Decompile), (tab, Form::Listing)])
        {
            let tab = open_tab(&workspace, &loaded, (entry, form), cx);
            let code = tab.read_with(cx, |item, _| item.code().unwrap().clone());
            for row in 0..code.len() {
                let (view, line) = code.get(row).unwrap();
                tab.update(cx, |item, cx| item.show_check(Some(row), cx));
                let said = tab.read_with(cx, |item, _| item.evidence().map(str::to_owned));
                let marked = view.origin(line).or(view.address(line)).is_some();
                let want = marked.then(|| want_evidence(&loaded, entry, view, line));
                assert_eq!(said, want, "{form:?} row {row}");
                shown[usize::from(view.origin(line).is_some())] += usize::from(marked);
                tab.update(cx, |item, cx| item.show_check(Some(row), cx));
                assert!(tab.read_with(cx, |item, _| item.evidence().is_none()));
            }
        }
        assert!(shown.iter().all(|&n| n > 1), "{shown:?}");
    }

    /// A recheck from the answer's seed gives the same record twice, which stands in for the
    /// check's: it tried the states asked for, and the evidence says it is a recheck.
    #[gpui::test]
    fn a_recheck_is_deterministic_and_updates_the_record(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let tab = open_tab(&workspace, &sample(), (CALLER, Form::Listing), cx);
        let row = tab.read_with(cx, |item, _| {
            let code = item.code().unwrap();
            (0..code.len()).find(|&r| item.marks().unwrap().block(code, r).is_some())
        });
        let row = row.unwrap();
        put_cursor(&tab, (row, 0), cx);
        let mut records = Vec::new();
        for _ in 0..2 {
            tab.update(cx, |item, cx| item.recheck(64, cx));
            cx.run_until_parked();
            records.push(tab.read_with(cx, |item, _| {
                let (marks, code) = (item.marks().unwrap(), item.code().unwrap());
                marks
                    .record(marks.block(code, row).unwrap())
                    .cloned()
                    .unwrap()
            }));
        }
        assert_eq!(records[0], records[1]);
        assert_eq!(records[0].states(), 64, "{:?}", records[0]);
        tab.update(cx, |item, cx| item.show_check(Some(row), cx));
        let said = tab.read_with(cx, |item, _| item.evidence().unwrap().to_owned());
        assert!(said.contains("rechecked from up to 64 states"), "{said}");
    }

    /// Next and previous wrong go round to the lines a wrong block marks, from any line, and
    /// find none in a function whose check finds nothing wrong.
    #[test]
    fn next_and_previous_wrong_go_round() {
        let loaded = one_function(&STORE);
        let a = &*loaded.analysis;
        let view = decompile_blocking(&loaded, 0x1000).unwrap();
        let code = CodeLines::new(vec![view.clone()]);
        let marks = Marks::new(a, &code, Some(0x1000), |_| wrong_check());
        let wrong: Vec<usize> = (0..code.len())
            .filter(|&row| view.origin(row).is_some())
            .collect();
        let (first, last) = (wrong[0], *wrong.last().unwrap());
        for from in 0..code.len() {
            let next = wrong.iter().copied().find(|&r| r > from).unwrap_or(first);
            let prev = wrong
                .iter()
                .rev()
                .copied()
                .find(|&r| r < from)
                .unwrap_or(last);
            assert_eq!(marks.next_wrong(&code, from, false), Some(next), "{from}");
            assert_eq!(marks.next_wrong(&code, from, true), Some(prev), "{from}");
        }
        let clean = Marks::new(a, &code, Some(0x1000), |_| Arc::new(None));
        assert_eq!(clean.next_wrong(&code, 0, false), None);
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
