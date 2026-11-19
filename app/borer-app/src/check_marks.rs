//! The machine's grade of each code line: a mark in the gutter of the decompile, listing
//! and linear tabs, one glyph and one color per [`Grade`].
//!
//! A line's block is the one its view says it was written from
//! ([`View::block`](borer_engine::view::View::block)): a
//! decompile line's origin, a listing or linear instruction line's block under its own
//! function. Its grade and evidence are what the engine answers for that block in that
//! function's check ([`BlockAnswer`]), the answer the graph and the status bar read; the
//! checks are the session's ([`Binary::rechecked`](crate::binary::Binary::rechecked)
//! before [`check_blocking`](crate::worker::check_blocking)), so a recheck shows in every
//! view. A line written from no block has no mark.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;
use std::sync::Arc;

use borer_engine::analysis::decompile::replay::{BlockAnswer, Grade, TextCheck};
use borer_engine::view::LineBlock;
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

use crate::binary::Digest;
use crate::code_view::CodeLines;
use crate::decompile_item::{buffer_row, whole_rows};
use crate::status::grade_color;
use crate::worker::State;

/// Returns how many grades there are: a grade added to the engine fails this match until
/// it is counted, and the count then fails every array of [`GRADE_COUNT`] grades.
const fn grade_count() -> usize {
    match Grade::Unchecked {
        Grade::Proved | Grade::Tested | Grade::Wrong | Grade::Unchecked => 4,
    }
}

/// How many grades there are.
pub const GRADE_COUNT: usize = grade_count();

/// Every grade, each at its [`grade_index`].
pub const GRADES: [Grade; GRADE_COUNT] =
    [Grade::Proved, Grade::Tested, Grade::Wrong, Grade::Unchecked];

/// Every grade sits at its own [`grade_index`] in [`GRADES`].
const _: () = {
    let mut ix = 0;
    while ix < GRADE_COUNT {
        assert!(grade_index(GRADES[ix]) == ix);
        ix += 1;
    }
};

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

/// Returns the word the status line names `grade` by.
///
/// # Arguments
///
/// * `grade` - The engine's grade.
#[must_use]
pub const fn grade_word(grade: Grade) -> &'static str {
    match grade {
        Grade::Proved => "proved",
        Grade::Tested => "tested",
        Grade::Wrong => "wrong",
        Grade::Unchecked => "unchecked",
    }
}

/// Which way a step between wrong blocks goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Toward {
    /// To the lines below, going round past the last.
    Down,
    /// To the lines above, going round past the first.
    Up,
}

/// Returns the block shown line `row` of `code` was written from, `None` for a line
/// written from no block.
///
/// # Arguments
///
/// * `code` - The tab's lines.
/// * `row` - Zero-based shown line.
#[must_use]
pub fn line_block(code: &CodeLines, row: usize) -> Option<LineBlock> {
    let (view, line) = code.get(row)?;
    view.block(line)
}

/// The checks the shown lines of a code tab are graded by, and where their wrong blocks
/// start.
#[derive(Debug)]
pub struct Marks {
    /// The lines the marks were made for, whose rows [`Marks::wrong`] counts.
    code: Arc<CodeLines>,
    /// The program and overlay state the checks are of.
    state: State,
    /// The check of each function the lines are written from, by entry; `None` inside
    /// when no check ran.
    checks: BTreeMap<u64, Arc<Option<TextCheck>>>,
    /// The first shown line of each run of lines one wrong block marks, ascending.
    wrong: Vec<usize>,
}

impl Marks {
    /// Returns the marks of `code` under state `revision`, each function's check from
    /// `check`; runs in the background.
    ///
    /// # Arguments
    ///
    /// * `state` - The program and overlay state the checks are of.
    /// * `code` - The tab's lines.
    /// * `check` - The check of the function at an entry.
    #[must_use]
    pub fn new(
        state: State,
        code: &Arc<CodeLines>,
        mut check: impl FnMut(u64) -> Arc<Option<TextCheck>>,
    ) -> Self {
        let mut checks = BTreeMap::new();
        for view in code.each_view() {
            for line in 0..view.lines() {
                if let Some(b) = view.block(line) {
                    checks
                        .entry(b.function)
                        .or_insert_with(|| check(b.function));
                }
            }
        }
        let mut marks = Self {
            code: code.clone(),
            state,
            checks,
            wrong: Vec::new(),
        };
        let mut last = None;
        for row in 0..code.len() {
            let block = line_block(code, row);
            let wrong = marks.grade(code, row) == Some(Grade::Wrong);
            if wrong && block != last {
                marks.wrong.push(row);
            }
            last = block.filter(|_| wrong);
        }
        marks
    }

    /// Returns whether the marks were made for `code`, so their wrong blocks are its rows.
    ///
    /// # Arguments
    ///
    /// * `code` - A tab's lines.
    #[must_use]
    pub fn is_for(&self, code: &Arc<CodeLines>) -> bool {
        Arc::ptr_eq(&self.code, code)
    }

    /// Returns the program and overlay state the checks are of.
    #[must_use]
    pub const fn state(&self) -> &State {
        &self.state
    }

    /// Returns the checks the marks hold, by function entry.
    #[must_use]
    pub const fn checks(&self) -> &BTreeMap<u64, Arc<Option<TextCheck>>> {
        &self.checks
    }

    /// Returns what the engine answers for the block shown line `row` was written from.
    ///
    /// # Arguments
    ///
    /// * `code` - The lines the marks were made for.
    /// * `row` - Zero-based shown line.
    ///
    /// # Returns
    ///
    /// The answer, `None` for a line written from no block or of a function whose check
    /// the marks do not hold yet.
    #[must_use]
    pub fn answer(&self, code: &CodeLines, row: usize) -> Option<BlockAnswer<'_>> {
        let b = line_block(code, row)?;
        let check = self.checks.get(&b.function)?;
        Some(BlockAnswer::of(check.as_ref().as_ref(), b.start))
    }

    /// Returns the grade shown line `row` is marked with, `None` for a line with no mark.
    ///
    /// # Arguments
    ///
    /// * `code` - The lines the marks were made for.
    /// * `row` - Zero-based shown line.
    #[must_use]
    pub fn grade(&self, code: &CodeLines, row: usize) -> Option<Grade> {
        self.answer(code, row).map(|a| a.grade())
    }

    /// Returns the evidence behind shown line `row`'s mark: the engine's answer for its
    /// block, and for a decompile line how its block is known.
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
        let mut said = self.answer(code, row)?.spell();
        let (view, line) = code.get(row)?;
        if let Some(start) = view.origin(line) {
            said.push_str(&format!(
                "\nthis line stands for block {start:#x}, known from the line origins through the text passes"
            ));
        }
        Some(said)
    }

    /// Returns the first line of the next wrong block after line `from`, going round past
    /// either end; `from`'s own block is the last tried.
    ///
    /// # Arguments
    ///
    /// * `from` - Zero-based shown line to start from.
    /// * `toward` - Which way to look.
    ///
    /// # Returns
    ///
    /// The line, `None` when no line is marked wrong.
    #[must_use]
    pub fn next_wrong(&self, from: usize, toward: Toward) -> Option<usize> {
        let (first, last) = (*self.wrong.first()?, *self.wrong.last()?);
        Some(match toward {
            Toward::Down => {
                let after = self.wrong.partition_point(|&row| row <= from);
                self.wrong.get(after).copied().unwrap_or(first)
            }
            Toward::Up => {
                let before = self.wrong.partition_point(|&row| row < from);
                let prior = before.checked_sub(1).and_then(|k| self.wrong.get(k));
                prior.copied().unwrap_or(last)
            }
        })
    }

    /// Returns `digest` with the grade of every shown line of `code` folded in, a line
    /// with no mark as none.
    ///
    /// # Arguments
    ///
    /// * `code` - The lines the marks were made for.
    /// * `digest` - The fold so far.
    #[must_use]
    pub fn digest(&self, code: &CodeLines, digest: Digest) -> Digest {
        (0..code.len()).fold(digest, |d, row| {
            d.text(self.grade(code, row).map_or("", glyph))
        })
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
    let mut ranges: [Vec<Range<Anchor>>; GRADE_COUNT] = Default::default();
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
    use borer_engine::analysis::render::{Dir, linear};
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use borer_engine::view::View;

    use super::{GRADES, Marks, Toward, glyph, grade_index};
    use crate::app_view::tests::loaded_of;
    use crate::code_view::CodeLines;
    use crate::worker::{LoadedBinary, State, decompile_blocking, listing_blocking};

    /// `jmp 0x1001` into its own second byte: blocks `0x1000` (`jmp`) and `0x1001`
    /// (`inc eax; ret`) overlap, and `inc eax` sits under `L_1001:`.
    // ASM: jmp 0x1001 (eb ff) ; from 0x1001: inc eax (ff c0) ; ret
    pub(crate) const OVERLAP: [u8; 4] = [0xeb, 0xff, 0xc0, 0xc3];

    /// Returns a raw x86-64 image of `code` at `0x1000`.
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

    /// Returns `F` at `0x1000` calling `G` at `0x1010` and running on into it, so
    /// `0x1010..0x1020` is `F`'s block `0x1005` and `G`'s block `0x1010`.
    fn shared() -> Arc<LoadedBinary> {
        let mut code = vec![0xe8, 0x0b, 0x00, 0x00, 0x00]; // ASM: call 0x1010
        code.resize(0x1f, 0x90); // ASM: nop up to 0x101f
        code.push(0xc3); // ASM: ret
        one_function(&code)
    }

    /// One block storing `rcx` whole through `rdx`.
    // ASM: mov [rdx], rcx ; ret
    pub(crate) const STORE: [u8; 4] = [0x48, 0x89, 0x0a, 0xc3];

    /// Three blocks the check grades proved, unchecked and proved: `test ecx, ecx; je`
    /// goes to a block with a packed float multiply the replay leaves out, or to a
    /// `return 1`.
    pub(crate) const FLOAT_BETWEEN: [u8; 16] = [
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x06, // ASM: je 0x100a
        0x0f, 0x59, 0xc1, // ASM: mulps xmm0, xmm1
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];

    /// Returns a record of the block at `start` found wrong from 64 states: its text
    /// stores zero where the machine stores `0x1234`.
    pub(crate) fn wrong_at(start: u64) -> BlockCheck {
        let found = Disagreement {
            function: 0x1000,
            block: start,
            at: start,
            claim: Claim::Memory,
            place: "[rdx]".to_owned(),
            text: 0,
            machine: 0x1234,
            bits: 64,
            lane: false,
            expr: "0".to_owned(),
        };
        BlockCheck::new(start, Ok(Some("differed")), (64, 1), vec![found])
    }

    /// Returns a check of the blocks at `starts`, each wrong when `wrong` holds it, else
    /// proved.
    fn check(starts: &[u64], wrong: &[u64]) -> Arc<Option<TextCheck>> {
        let blocks = starts
            .iter()
            .map(|&start| {
                if wrong.contains(&start) {
                    wrong_at(start)
                } else {
                    BlockCheck::new(start, Ok(None), (3, 1), Vec::new())
                }
            })
            .collect();
        Arc::new(Some(TextCheck::new(blocks)))
    }

    /// Returns the marks of `view` with each function's check from `checks`.
    fn marks_of(
        view: Arc<View>,
        checks: &[(u64, Arc<Option<TextCheck>>)],
    ) -> (Marks, Arc<CodeLines>) {
        let code = Arc::new(CodeLines::new(vec![view]));
        let state = State {
            identity: String::new(),
            revision: 0,
        };
        let marks = Marks::new(state, &code, |at| {
            let found = checks.iter().find(|(f, _)| *f == at);
            found.map_or_else(|| Arc::new(None), |(_, c)| c.clone())
        });
        (marks, code)
    }

    /// Returns the grade of each line of `code` holding `needle`.
    fn grades(marks: &Marks, code: &CodeLines, needle: &str) -> Vec<Option<Grade>> {
        (0..code.len())
            .filter(|&row| {
                let line = code.get(row).and_then(|(v, l)| v.line(l));
                line.is_some_and(|l| l.contains(needle))
            })
            .map(|row| marks.grade(code, row))
            .collect()
    }

    /// `inc eax` takes the grade of `L_1001`, the block it sits under, in the listing and
    /// in the linear listing; the header, label, function and section lines have none.
    #[test]
    fn a_line_under_a_label_takes_that_block_grade() {
        let loaded = one_function(&OVERLAP);
        let checks = [(0x1000, check(&[0x1000, 0x1001], &[0x1001]))];
        let listing = listing_blocking(&loaded, 0x1000).unwrap();
        let (marks, code) = marks_of(listing, &checks);
        assert_eq!(grades(&marks, &code, "jmp"), [Some(Grade::Proved)]);
        assert_eq!(grades(&marks, &code, "inc"), [Some(Grade::Wrong)]);
        assert_eq!(grades(&marks, &code, "ret"), [Some(Grade::Wrong)]);
        assert_eq!(grades(&marks, &code, "L_1001:"), [None]);
        assert_eq!(marks.grade(&code, 0), None, "the header");
        let (p, a, o) = (&loaded.program, &loaded.analysis, &loaded.overlay);
        let page = linear(p, a, o, 0x1000, Dir::Next, 16).unwrap();
        let (marks, code) = marks_of(Arc::new(page.view), &checks);
        assert_eq!(grades(&marks, &code, "inc"), [Some(Grade::Wrong)]);
        assert_eq!(grades(&marks, &code, "jmp"), [Some(Grade::Proved)]);
        for none in ["; function", "L_1001:", "; section"] {
            assert_eq!(grades(&marks, &code, none), [None], "{none}");
        }
    }

    /// Code two functions share takes each function's own grade in its own listing, the
    /// evidence is that function's record, and next wrong stops on it in `F`'s listing.
    #[test]
    fn shared_code_takes_each_function_own_grade() {
        let loaded = shared();
        let checks = [
            (0x1000, check(&[0x1000, 0x1005], &[0x1005])),
            (0x1010, check(&[0x1010], &[])),
        ];
        let f = listing_blocking(&loaded, 0x1000).unwrap();
        let g = listing_blocking(&loaded, 0x1010).unwrap();
        let (f_row, g_row) = (f.line_of(0x1014).unwrap(), g.line_of(0x1014).unwrap());
        let first_wrong = f.line_of(0x1005).unwrap();
        let (fm, fc) = marks_of(f.clone(), &checks);
        let (gm, gc) = marks_of(g, &checks);
        assert_eq!(fm.grade(&fc, f_row), Some(Grade::Wrong));
        assert_eq!(gm.grade(&gc, g_row), Some(Grade::Proved));
        let said = fm.evidence(&fc, f_row).unwrap();
        assert!(said.starts_with("block 0x1005: wrong:"), "{said}");
        let said = gm.evidence(&gc, g_row).unwrap();
        assert!(said.starts_with("block 0x1010: proved"), "{said}");
        assert_eq!(fm.next_wrong(0, Toward::Down), Some(first_wrong));
        assert_eq!(fm.next_wrong(f_row, Toward::Down), Some(first_wrong));
        assert_eq!(gm.next_wrong(0, Toward::Down), None);
        let (none, nc) = marks_of(f, &[]);
        let said = none.evidence(&nc, f_row).unwrap();
        assert!(said.contains("no check ran"), "{said}");
        assert_eq!(none.grade(&nc, f_row), Some(Grade::Unchecked));
    }

    /// Next and previous wrong step block by block, from any line, and go round past
    /// either end.
    #[test]
    fn next_and_previous_wrong_step_by_block_and_go_round() {
        let loaded = one_function(&OVERLAP);
        let listing = listing_blocking(&loaded, 0x1000).unwrap();
        let (jmp, inc) = (
            listing.line_of(0x1000).unwrap(),
            listing.line_of(0x1001).unwrap(),
        );
        let ret = listing.line_of(0x1003).unwrap();
        let checks = [(0x1000, check(&[0x1000, 0x1001], &[0x1000, 0x1001]))];
        let (marks, _) = marks_of(listing, &checks);
        assert_eq!(marks.next_wrong(jmp, Toward::Down), Some(inc));
        assert_eq!(
            marks.next_wrong(inc, Toward::Down),
            Some(jmp),
            "round past the end"
        );
        assert_eq!(
            marks.next_wrong(ret, Toward::Down),
            Some(jmp),
            "past inc's own block"
        );
        assert_eq!(
            marks.next_wrong(jmp, Toward::Up),
            Some(inc),
            "round past the start"
        );
        assert_eq!(marks.next_wrong(ret, Toward::Up), Some(inc));
        assert_eq!(marks.next_wrong(0, Toward::Down), Some(jmp));
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

    /// Returns the grade of the first line of `code` holding `needle`, and its evidence.
    fn first(marks: &Marks, code: &CodeLines, needle: &str) -> (Option<Grade>, Option<String>) {
        let row = (0..code.len()).find(|&row| {
            let line = code.get(row).and_then(|(v, l)| v.line(l));
            line.is_some_and(|l| l.contains(needle))
        });
        let row = row.unwrap();
        (marks.grade(code, row), marks.evidence(code, row))
    }

    /// A check that finds a block wrong marks the listing lines of its instructions and the
    /// decompile line of its store wrong, and neither header.
    #[test]
    fn a_disagreeing_block_marks_its_lines_wrong() {
        let loaded = one_function(&STORE);
        let checks = [(0x1000, check(&[0x1000], &[0x1000]))];
        let listing = listing_blocking(&loaded, 0x1000).unwrap();
        let (marks, code) = marks_of(listing, &checks);
        assert_eq!(grades(&marks, &code, "mov"), [Some(Grade::Wrong)]);
        assert_eq!(grades(&marks, &code, "ret"), [Some(Grade::Wrong)]);
        assert_eq!(marks.grade(&code, 0), None, "the listing's header");
        let decompile = decompile_blocking(&loaded, 0x1000).unwrap();
        let (marks, code) = marks_of(decompile, &checks);
        assert_eq!(first(&marks, &code, "= a").0, Some(Grade::Wrong));
        assert_eq!(marks.grade(&code, 0), None, "the decompile's header");
        assert_eq!(marks.next_wrong(0, Toward::Down).map(|r| r > 0), Some(true));
    }

    /// The evidence under a marked line is the engine's spelling of its block's record; a
    /// decompile line adds how its block is known, a listing line does not.
    #[test]
    fn the_evidence_is_the_engine_spelling_of_the_line_block() {
        let loaded = one_function(&STORE);
        let checks = [(0x1000, check(&[0x1000], &[0x1000]))];
        let origins = "this line stands for block 0x1000, known from the line origins";
        let listing = listing_blocking(&loaded, 0x1000).unwrap();
        let (marks, code) = marks_of(listing, &checks);
        let said = first(&marks, &code, "mov").1.unwrap();
        assert!(said.starts_with(
            "block 0x1000: wrong: the machine does not bear out the text
"
        ));
        assert!(
            said.contains("memory [rdx] at 0x1000: text 0x0, machine 0x1234"),
            "{said}"
        );
        assert!(!said.contains(origins), "{said}");
        let decompile = decompile_blocking(&loaded, 0x1000).unwrap();
        let (marks, code) = marks_of(decompile, &checks);
        let said = first(&marks, &code, "= a").1.unwrap();
        assert!(said.starts_with("block 0x1000: wrong:"), "{said}");
        assert!(said.contains(origins), "{said}");
        assert_eq!(marks.evidence(&code, 0), None, "the header has none");
    }
}
