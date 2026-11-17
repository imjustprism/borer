//! What the code editor shows of a [`View`]: the lines, the role of each token, where a
//! link goes and what a token is, all read from the view's tokens.

use std::ops::Range;
use std::sync::Arc;

use borer_engine::view::{Kind, Ref, View};

use crate::binary::Digest;
use gpui::Hsla;
use theme::Theme;

/// The role a token plays on screen, each one color: its kind, with a function that names
/// an import apart from one of the binary's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// A name nothing resolves, and default text.
    Text,
    /// A comment.
    Comment,
    /// A C keyword or an assembly prefix.
    Keyword,
    /// An instruction mnemonic.
    Mnemonic,
    /// A machine register.
    Register,
    /// A type's name.
    Type,
    /// A function of the binary.
    Function,
    /// A function outside the binary: a [`Ref::Import`].
    Import,
    /// A parameter or a local.
    Variable,
    /// A global.
    Global,
    /// A named constant or an enum member.
    Constant,
    /// A struct or class field.
    Field,
    /// A block label.
    Label,
    /// A code or target address.
    Address,
    /// A string or character literal.
    String,
    /// A numeric literal.
    Number,
    /// An operator or punctuation.
    Punct,
}

/// How many roles there are.
pub const ROLES: usize = 17;

impl Role {
    /// Every role, in declaration order: `Role::ALL[r as usize] == r`.
    pub const ALL: [Self; ROLES] = [
        Self::Text,
        Self::Comment,
        Self::Keyword,
        Self::Mnemonic,
        Self::Register,
        Self::Type,
        Self::Function,
        Self::Import,
        Self::Variable,
        Self::Global,
        Self::Constant,
        Self::Field,
        Self::Label,
        Self::Address,
        Self::String,
        Self::Number,
        Self::Punct,
    ];

    /// Returns the role of a token.
    ///
    /// # Arguments
    ///
    /// * `kind` - The token's kind.
    /// * `link` - What the token links to.
    ///
    /// # Returns
    ///
    /// The role; `None` for whitespace, which keeps the editor's text color.
    #[must_use]
    pub const fn of(kind: Kind, link: Option<&Ref>) -> Option<Self> {
        Some(match kind {
            Kind::Space => return None,
            Kind::Function if matches!(link, Some(Ref::Import(_))) => Self::Import,
            Kind::Text => Self::Text,
            Kind::Comment | Kind::Note | Kind::Question => Self::Comment,
            Kind::Keyword => Self::Keyword,
            Kind::Mnemonic => Self::Mnemonic,
            Kind::Register => Self::Register,
            Kind::Type => Self::Type,
            Kind::Function => Self::Function,
            Kind::Variable => Self::Variable,
            Kind::Global => Self::Global,
            Kind::Constant => Self::Constant,
            Kind::Field => Self::Field,
            Kind::Label => Self::Label,
            Kind::Address => Self::Address,
            Kind::String => Self::String,
            Kind::Number => Self::Number,
            Kind::Punct => Self::Punct,
        })
    }

    /// Returns the theme keys the role takes its color from, in the order they are tried:
    /// borer's own key where Zed has no word for the role, then Zed's syntax name.
    #[must_use]
    pub const fn keys(self) -> &'static [&'static str] {
        match self {
            Self::Text => &["borer.text"],
            Self::Comment => &["comment"],
            Self::Keyword => &["keyword"],
            Self::Mnemonic => &["borer.mnemonic", "keyword"],
            Self::Register => &["borer.register", "variable.special"],
            Self::Type => &["type"],
            Self::Function => &["function"],
            Self::Import => &["borer.import", "function"],
            Self::Variable => &["variable"],
            Self::Global => &["borer.global", "constant"],
            Self::Constant => &["constant"],
            Self::Field => &["borer.field", "property"],
            Self::Label => &["label"],
            Self::Address => &["borer.address", "comment"],
            Self::String => &["string"],
            Self::Number => &["number"],
            Self::Punct => &["punctuation"],
        }
    }

    /// Returns the role's place in [`Role::ALL`] and in a [`CodePalette`].
    #[must_use]
    pub const fn index(self) -> usize {
        self as usize
    }
}

/// Returns the color of the first of `keys` the theme's syntax sets, else the theme's text
/// color.
///
/// # Arguments
///
/// * `theme` - The Zed theme to paint with.
/// * `keys` - Theme keys, borer's own first.
#[must_use]
pub fn theme_color(theme: &Theme, keys: &[&str]) -> Hsla {
    keys.iter()
        .find_map(|key| theme.syntax().style_for_name(key).and_then(|s| s.color))
        .unwrap_or(theme.colors().text)
}

/// The color of every [`Role`], by [`Role::index`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct CodePalette(pub [Hsla; ROLES]);

impl CodePalette {
    /// Builds a [`CodePalette`] from `theme`: each role takes the color of the first of its
    /// keys ([`Role::keys`]) the theme's syntax sets, else the theme's text color.
    ///
    /// # Arguments
    ///
    /// * `theme` - The Zed theme to paint with, normally the active one.
    #[must_use]
    pub fn from_theme(theme: &Theme) -> Self {
        Self(Role::ALL.map(|role| theme_color(theme, role.keys())))
    }

    /// Returns the color of `role`.
    ///
    /// # Arguments
    ///
    /// * `role` - The role.
    #[must_use]
    pub const fn color(&self, role: Role) -> Hsla {
        self.0[role.index()]
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
    /// * `views` - The views to show, in order.
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

    /// Returns the views the lines come from, in order.
    #[must_use]
    pub fn each_view(&self) -> &[Arc<View>] {
        &self.views
    }

    /// Returns shown line `ix` as the place of its view in [`Self::each_view`] and its line
    /// in that view, `None` past the last line.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based index of the shown line.
    #[must_use]
    pub fn slot(&self, ix: usize) -> Option<(usize, usize)> {
        self.lines.get(ix).copied()
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
        let (v, l) = self.slot(ix)?;
        Some((self.views.get(v)?, l))
    }

    /// Returns `digest` with every shown line folded in, in order ([`Digest::line`]).
    ///
    /// # Arguments
    ///
    /// * `digest` - The fold so far.
    #[must_use]
    pub fn digest(&self, digest: Digest) -> Digest {
        (0..self.len())
            .filter_map(|ix| self.get(ix))
            .fold(digest, |d, (view, line)| d.line(view, line))
    }

    /// Returns the text the editor holds: the shown lines joined by newlines, so row `i` of
    /// the text is shown line `i`, and one view's text is its [`View::spell`] byte for byte.
    #[must_use]
    pub fn text(&self) -> String {
        let mut out = String::new();
        for ix in 0..self.len() {
            if ix > 0 {
                out.push('\n');
            }
            if let Some((view, line)) = self.get(ix) {
                out.push_str(view.line(line).unwrap_or_default());
            }
        }
        out
    }

    /// Returns the token of shown line `row` that holds byte `col`, or the one ending there.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based shown line.
    /// * `col` - Byte in the line, as a cursor stands before it.
    ///
    /// # Returns
    ///
    /// The view, its line, and the token as [`View::token_at`] gives it; the token before
    /// a cursor at its end when the one after the cursor links nowhere.
    #[must_use]
    pub fn token_at(&self, row: usize, col: usize) -> Option<(&Arc<View>, usize, Token<'_>)> {
        let (view, line) = self.get(row)?;
        let after = view.token_at(line, col);
        let before = col.checked_sub(1).and_then(|c| view.token_at(line, c));
        let token = match after {
            Some(t) if t.2.is_some() => t,
            _ => before.filter(|t| t.2.is_some()).or(after)?,
        };
        Some((view, line, token))
    }

    /// Returns where each role paints in shown lines `rows`: per role, by [`Role::index`],
    /// each token's shown line and its bytes in that line, in line order.
    ///
    /// # Arguments
    ///
    /// * `rows` - Shown lines; those past the last are left out.
    #[must_use]
    pub fn highlights(&self, rows: Range<usize>) -> Vec<Vec<(usize, Range<usize>)>> {
        let mut out = vec![Vec::new(); ROLES];
        for row in rows.start..rows.end.min(self.len()) {
            let Some((view, line)) = self.get(row) else {
                break;
            };
            for (span, kind, link) in view.tokens(line) {
                if let Some(spans) = Role::of(kind, link).and_then(|r| out.get_mut(r.index())) {
                    spans.push((row, span));
                }
            }
        }
        out
    }
}

/// One token as [`View::token_at`] gives it: its bytes in the line, its kind and its link.
pub type Token<'a> = (Range<usize>, Kind, Option<&'a Ref>);

/// Navigation that following a linked token [`Ref`] leads to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClickOutcome {
    /// Opens the function at the given entry virtual address, pushing history.
    OpenFunction(u64),
    /// Moves to the 0-based line of the view that the engine places the referent on.
    ScrollToLine(usize),
    /// Names the import with this first slot: there is no imports panel to open yet.
    Import(u64),
    /// The view places the referent on no line.
    None,
}

/// Resolves following `target` inside `view` into a [`ClickOutcome`].
///
/// A function opens; an address goes to the line that shows its instruction in a listing
/// ([`View::line_of`]), else to the line that defines it ([`View::definition`]), as every
/// other referent does.
///
/// # Arguments
///
/// * `view` - Active [`View`] supplying its lines.
/// * `target` - Engine referent attached to the token.
///
/// # Returns
///
/// Resulting [`ClickOutcome`] without parsing any text.
#[must_use]
pub fn resolve_ref_click(view: &View, target: &Ref) -> ClickOutcome {
    let line = match target {
        Ref::Function(entry) => return ClickOutcome::OpenFunction(*entry),
        Ref::Import(slot) => return ClickOutcome::Import(*slot),
        Ref::Address(va) => view.line_of(*va).or_else(|| view.definition(target)),
        Ref::Global(_)
        | Ref::Variable { .. }
        | Ref::Type(_)
        | Ref::String(_)
        | Ref::Field { .. } => view.definition(target),
        Ref::Comment(_) => return ClickOutcome::None,
    };
    line.map_or(ClickOutcome::None, ClickOutcome::ScrollToLine)
}

/// Returns what a token is and what it links to, as the view says: its text and kind, then
/// its referent, else that the engine links it to nothing.
///
/// # Arguments
///
/// * `text` - The token's text.
/// * `kind` - Its kind.
/// * `link` - What it links to.
#[must_use]
pub fn describe(text: &str, kind: Kind, link: Option<&Ref>) -> String {
    let what = match kind {
        Kind::Space => "whitespace",
        Kind::Comment => "comment",
        Kind::Note => "note",
        Kind::Question => "open question",
        Kind::Keyword => "keyword",
        Kind::Mnemonic => "mnemonic",
        Kind::Register => "register",
        Kind::Type => "type",
        Kind::Function => "function",
        Kind::Variable => "variable",
        Kind::Global => "global",
        Kind::Field => "field",
        Kind::Label => "label",
        Kind::Address => "address",
        Kind::String => "string literal",
        Kind::Number => "number",
        Kind::Constant => "constant",
        Kind::Punct => "punctuation",
        Kind::Text => "name the engine does not resolve",
    };
    let to = match link {
        None => return format!("{text}: {what}, linked to nothing"),
        Some(Ref::Address(va)) => format!("the code at {va:#x}"),
        Some(Ref::Function(va)) => format!("the function at {va:#x}"),
        Some(Ref::Import(slot)) => format!("the import at slot {slot:#x}"),
        Some(Ref::Global(va)) => format!("the global at {va:#x}"),
        Some(Ref::String(va)) => format!("the string at {va:#x}"),
        Some(Ref::Field { ty, offset }) => format!("the field at {offset:#x} of {ty}"),
        Some(Ref::Variable { function, name, .. }) => {
            format!("the variable {name} of the function at {function:#x}")
        }
        Some(Ref::Type(name)) => format!("the type {name}"),
        Some(Ref::Comment(va)) => format!("the comment at {va:#x}"),
    };
    format!("{text}: {what}, links to {to}")
}

#[cfg(test)]
pub(crate) mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::decompile::view::{view, view_of};
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    use borer_engine::view::{Kind, Ref};

    use super::{ClickOutcome, CodeLines, CodePalette, ROLES, Role, describe, resolve_ref_click};

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

    /// Every role sits at its own index, a function naming an import takes the import's
    /// role, and only whitespace has none.
    ///
    /// # Panics
    ///
    /// Panics if two roles share an index or a token's role is wrong.
    #[test]
    fn every_role_has_its_own_index() {
        for (ix, role) in Role::ALL.into_iter().enumerate() {
            assert_eq!(role.index(), ix);
        }
        let import = Ref::Import(0x2000);
        assert_eq!(Role::of(Kind::Function, Some(&import)), Some(Role::Import));
        assert_eq!(Role::of(Kind::Function, None), Some(Role::Function));
        assert_eq!(Role::of(Kind::Space, None), None);
        let hue = |n: u16| gpui::hsla(f32::from(n) / 32.0, 0.5, 0.5, 1.0);
        let mut colors = [hue(0); ROLES];
        for (n, color) in (0..).zip(colors.iter_mut()) {
            *color = hue(n);
        }
        let palette = CodePalette(colors);
        assert_eq!(palette.color(Role::Import), hue(7));
    }

    /// Every highlight starts and ends on a character boundary of its line, for text with
    /// multi-byte characters and for code of every byte value.
    ///
    /// # Panics
    ///
    /// Panics if a highlight would split a UTF-8 character.
    #[test]
    fn highlights_land_on_char_boundaries() {
        let (program, analysis, overlay) = sample_program();
        let utf8 = "// d\u{e9}j\u{e0} \u{2014} \u{3bb}\nint sub_1000(void) {\n    goto L_1000;\nL_1000:\n    return sub_1030();\n}\n";
        let mut views = vec![Arc::new(
            view_of(&program, &analysis, &overlay, 0x1000, utf8).expect("utf8 view"),
        )];
        let bytes: Vec<u8> = (0..=u8::MAX).cycle().take(0x400).collect();
        let sections = vec![Section::mapped(".text", 0x1000, 0, 0x400, false, true)];
        let mut noise = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), sections);
        noise.format = BinaryFormat::Pe;
        let noise_analysis = Analysis::compute(&noise);
        views.extend(
            noise_analysis
                .functions
                .iter()
                .filter_map(|f| view(&noise, &noise_analysis, &overlay, f.entry)),
        );
        let code = CodeLines::new(views);
        for (row, span) in code.highlights(0..code.len()).into_iter().flatten() {
            let (shown, line) = code.get(row).unwrap();
            let text = shown.line(line).unwrap();
            assert!(text.is_char_boundary(span.start) && text.is_char_boundary(span.end));
            assert!(span.start < span.end && span.end <= text.len());
        }
    }

    /// The editor's text is the views' lines joined by newlines, one view's text its
    /// spelling byte for byte, and its highlights are exactly the tokens of the asked rows.
    ///
    /// # Panics
    ///
    /// Panics if the text or a highlight differs from the view's tokens.
    #[test]
    fn the_text_and_highlights_follow_the_tokens() {
        let (program, analysis, overlay) = sample_program();
        for func in &analysis.functions {
            let built = view(&program, &analysis, &overlay, func.entry).expect("decompiles");
            let code = CodeLines::new(vec![built.clone()]);
            assert_eq!(code.text(), built.spell());
            let groups = code.highlights(0..usize::MAX);
            let mut got: Vec<_> = groups
                .iter()
                .enumerate()
                .flat_map(|(s, spans)| spans.iter().map(move |(r, span)| (*r, span.clone(), s)))
                .collect();
            let mut want: Vec<_> = (0..built.lines())
                .flat_map(|line| {
                    built.tokens(line).filter_map(move |(span, kind, link)| {
                        Some((line, span, Role::of(kind, link)?.index()))
                    })
                })
                .collect();
            got.sort_by_key(|(r, span, _)| (*r, span.start));
            want.sort_by_key(|(r, span, _)| (*r, span.start));
            assert_eq!(got, want);
            assert!(
                code.highlights(built.lines()..usize::MAX)
                    .iter()
                    .all(Vec::is_empty)
            );
        }
    }

    /// A call opens its callee, a label goes to the line it is defined on, an import is
    /// named, and the token at a cursor standing at a link's end is that link.
    ///
    /// # Panics
    ///
    /// Panics if a link resolves anywhere else.
    #[test]
    fn links_resolve_to_what_the_view_says() {
        let (program, analysis, overlay) = sample_program();
        let caller = view(&program, &analysis, &overlay, 0x1000).expect("decompiles");
        let call = (0..caller.lines())
            .find_map(|line| {
                caller
                    .tokens(line)
                    .find(|(_, _, link)| *link == Some(&Ref::Function(0x1030)))
                    .map(|(span, _, _)| (line, span))
            })
            .expect("the caller calls its callee");
        let code = CodeLines::new(vec![caller.clone()]);
        let (_, _, (_, _, link)) = code.token_at(call.0, call.1.end).expect("a token");
        assert_eq!(link, Some(&Ref::Function(0x1030)));
        assert_eq!(
            resolve_ref_click(&caller, &Ref::Function(0x1030)),
            ClickOutcome::OpenFunction(0x1030)
        );
        let goto_text = "void sub_1000(void) {\n    goto L_1000;\nL_1000:\n    return;\n}\n";
        let goto_view =
            view_of(&program, &analysis, &overlay, 0x1000, goto_text).expect("goto view");
        assert_eq!(
            resolve_ref_click(&goto_view, &Ref::Address(0x1000)),
            ClickOutcome::ScrollToLine(2)
        );
        assert_eq!(
            resolve_ref_click(&goto_view, &Ref::Import(0x2000)),
            ClickOutcome::Import(0x2000)
        );
        assert_eq!(
            resolve_ref_click(&goto_view, &Ref::Address(0x9999)),
            ClickOutcome::None
        );
    }

    /// A description names the token, its kind and its referent, and says when the engine
    /// links it to nothing.
    ///
    /// # Panics
    ///
    /// Panics if a description says more or less than the token.
    #[test]
    fn a_description_says_only_what_the_token_carries() {
        assert_eq!(
            describe("sub_1030", Kind::Function, Some(&Ref::Function(0x1030))),
            "sub_1030: function, links to the function at 0x1030"
        );
        assert_eq!(
            describe("x", Kind::Text, None),
            "x: name the engine does not resolve, linked to nothing"
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
            assert!(Arc::ptr_eq(shown, &views[v]));
            assert_eq!(line, l);
        }
        assert!(cycled.get(cycled.len()).is_none());
        assert!(CodeLines::new(Vec::new()).cycled(5).is_empty());
    }
}
