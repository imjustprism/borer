//! What one exported C definition says of itself, for a reader that
//! scores or maps it without parsing it: each variable it declares with
//! where it lives, and the block each of its lines stands for.
//!
//! A record is read off the text the export splits into a definition
//! ([`super::Hoisted::add`]), by the same rule that split takes, and off
//! the engine's own facts about that text: the origins carried onto every
//! written line ([`Origins`]), the function's ABI ([`abi::of`]) and the key
//! each variable name stands for ([`VarKey`]). Lines are numbered from the
//! definition's head, the signature line being 1 ([`DefLine`]), the form a
//! reader that cuts the file at each definition sees.
//!
//! A variable is a parameter of the head or a local the text declares.
//! Where it lives is what the engine states and no more: a parameter where
//! its convention passes it ([`abi::of`]), when that is one register or one
//! stack word; a local whose key is a stack slot ([`VarKey::Slot`], an
//! agent's name for it included) at that slot; a local named after a
//! register of the program's instruction set, which the lifter keeps only
//! for a value living in that register, in it; anything else
//! [`Home::Unknown`]. A line stands for the one block whose lifted code
//! spells it, or for none; each block a line names is listed once per
//! record with its instruction starts, so a line came from some of them,
//! not necessarily all.

use std::collections::{BTreeMap, BTreeSet};

use super::super::abi::{self, function::Loc};
use super::super::lexer::{Lex, lex};
use super::super::line::{is_ident, is_register_name, is_temp_name};
use super::super::{Analysis, Origins, Program};
use crate::analysis::Overlay;
use crate::analysis::protos::{VarKey, frame_base, slot_words};
use crate::analysis::render::isa_is_register;
use crate::isa::{Isa, a64};

/// Most instruction starts one record lists over all its blocks.
///
/// A block past them lists the starts left, or none, and says it was cut
/// ([`Block::cut`]), so a record holds at most this many addresses however
/// many instructions the function holds.
pub const RECORD_STARTS_MAX: usize = 4096;

/// Returns the most instruction starts an export's records list in all.
///
/// That is the file's bytes, which hold every instruction once whatever
/// the program, plus one record's worth. Functions that overlap (a table
/// of calls into successive bytes of one sled) list their shared
/// instructions once each, so this bounds the records by the file's size
/// rather than the square of it.
///
/// # Arguments
///
/// * `program` - The loaded image.
#[must_use]
pub fn starts_budget(program: &Program) -> usize {
    program.bytes.len().saturating_add(RECORD_STARTS_MAX)
}

/// A line of one definition, from 1, the head (the signature line) being 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefLine(pub usize);

/// A line among the definitions an export handed its sink, from 0: the
/// file's line is that plus the lines of [`super::Hoisted::head`], plus 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SinkLine(pub usize);

/// Where a variable lives, as far as the engine states it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Home {
    /// The machine register it lives in, by its full name at the
    /// program's word size (`rcx`, `ecx` on 32-bit x86, `x0`, `r0`, `a0`).
    Register(String),
    /// A stack slot: its offset in bytes from the canonical frame address,
    /// negative below it. The canonical frame address is the stack pointer
    /// just before the call ran: at the function's entry, plus the return
    /// address an x86 call pushes ([`frame_base`]), the entry stack pointer
    /// itself on arm64, ARM32 and RISC-V.
    Cfa(i64),
    /// No single home the engine states.
    Unknown,
}

/// Whether a variable is a parameter or a local.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// The parameter at this position of the head, from 0.
    Param(usize),
    /// A local the body declares.
    Local,
}

/// One variable the definition declares.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variable {
    /// Its name as printed.
    pub name: String,
    /// Its C type as printed, pointer stars and an array's extent included.
    pub ty: String,
    /// Parameter or local.
    pub role: Role,
    /// Where it lives.
    pub home: Home,
    /// The definition's lines naming it as an identifier.
    pub lines: Vec<DefLine>,
}

/// One block a line stands for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    /// Its instruction starts, as virtual addresses, in address order.
    pub starts: Vec<u64>,
    /// Whether `starts` lists only some of them: the block's bytes could
    /// not all be decoded, it is no block of the function, or the record
    /// reached [`RECORD_STARTS_MAX`] or the export its [`starts_budget`].
    pub cut: bool,
}

/// What one definition says of itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Record {
    /// The function's entry.
    pub entry: u64,
    /// Its name as the C file spells it.
    pub name: String,
    /// The definition's variables: the head's parameters in order, then
    /// the locals in declaration order.
    pub variables: Vec<Variable>,
    /// Each line that stands for a block, with that block's start.
    pub lines: BTreeMap<DefLine, u64>,
    /// Every block a line stands for, by its start.
    pub blocks: BTreeMap<u64, Block>,
}

/// What [`record`] reads one definition from.
#[derive(Debug, Clone, Copy)]
pub struct Written<'a> {
    /// The function's entry.
    pub entry: u64,
    /// Its name as the C file spells it.
    pub name: &'a str,
    /// The local declarations the export kept in the definition, in order.
    pub locals: &'a [&'a str],
    /// The head line, the signature the definition opens with.
    pub head: &'a str,
    /// The definition from its head line through its closing brace.
    pub definition: &'a str,
    /// The block each line of `definition` stands for.
    pub origins: &'a Origins,
    /// The stack offsets the lift addressed through a realigned stack
    /// pointer, whose true place it does not know: a local at one has no
    /// stated home.
    pub realigned: &'a BTreeSet<i64>,
}

/// Returns the record of one exported definition.
///
/// # Arguments
///
/// * `program` - The loaded image, whose bytes the block starts are
///   decoded from.
/// * `analysis` - Its analysis, holding the function.
/// * `overlay` - Names in force, whose variable names map to their keys.
/// * `w` - The definition and what it was split from.
/// * `budget` - The starts the export may still list ([`starts_budget`]),
///   less what this record lists.
#[must_use]
pub fn record(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    w: Written<'_>,
    budget: &mut usize,
) -> Record {
    let lines: BTreeMap<DefLine, u64> = (0..w.origins.len())
        .filter_map(|i| Some((DefLine(i.checked_add(1)?), w.origins.line(i)?)))
        .collect();
    let ends: BTreeMap<u64, u64> = analysis
        .function(w.entry)
        .map(|f| f.blocks.iter().map(|b| (b.start, b.end)).collect())
        .unwrap_or_default();
    let mut left = RECORD_STARTS_MAX.min(*budget);
    let mut blocks = BTreeMap::new();
    for &start in lines.values() {
        if blocks.contains_key(&start) {
            continue;
        }
        let none = Block {
            starts: Vec::new(),
            cut: true,
        };
        let b = ends
            .get(&start)
            .map_or(none, |&end| block(program, start, end, left));
        left = left.saturating_sub(b.starts.len());
        *budget = budget.saturating_sub(b.starts.len());
        blocks.insert(start, b);
    }
    Record {
        entry: w.entry,
        name: w.name.to_owned(),
        variables: variables(program, analysis, overlay, w),
        lines,
        blocks,
    }
}

/// Returns the instruction starts of the block `start..end`, at most
/// `most`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `start` - The block's first instruction.
/// * `end` - One past its last byte.
/// * `most` - Most starts to list.
fn block(program: &Program, start: u64, end: u64, most: usize) -> Block {
    let mut starts = Vec::new();
    let mut after = start;
    let len = usize::try_from(end.saturating_sub(start)).unwrap_or(usize::MAX);
    let code = program.read_va_upto(start, len.max(1));
    if let (Some(code), Some(isa)) = (code, program.arch.isa()) {
        let reach = most.saturating_add(1);
        crate::disasm::lengths(program, code, start, isa, end, reach, |va, n| {
            starts.push(va);
            after = va.saturating_add(crate::num::from_usize(n.max(1)));
        });
    }
    let cut = starts.len() > most || after < end;
    starts.truncate(most);
    Block { starts, cut }
}

/// Returns the variables a definition declares: its head's parameters,
/// then the locals the export kept in it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `w` - The definition.
fn variables(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    w: Written<'_>,
) -> Vec<Variable> {
    let params = super::super::types::signature_params(&format!("// signature: {}", w.head));
    let homes = param_homes(program, analysis, overlay, w.entry, params.len());
    let named = naming_lines(w.definition);
    let lines = |name: &str| named.get(name).cloned().unwrap_or_default();
    let mut out: Vec<Variable> = Vec::new();
    for (i, (name, ty)) in params.into_iter().enumerate() {
        out.push(Variable {
            lines: lines(&name),
            home: homes.get(i).cloned().unwrap_or(Home::Unknown),
            name,
            ty,
            role: Role::Param(i),
        });
    }
    let home = local_homes(program, overlay, w.entry, w.realigned);
    for (name, ty) in w.locals.iter().flat_map(|l| declared(l.trim())) {
        out.push(Variable {
            lines: lines(&name),
            home: home(&name),
            name,
            ty,
            role: Role::Local,
        });
    }
    out
}

/// Returns where each of a function's `count` printed parameters arrives.
///
/// The place is its convention's ([`abi::of`]): none when the ABI lists
/// another number of parameters than the head prints, and
/// [`Home::Unknown`] for one that travels in more than one piece.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and prototypes in force.
/// * `entry` - The function's entry.
/// * `count` - The parameters the head prints.
fn param_homes(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    count: usize,
) -> Vec<Home> {
    let Some(f) = abi::of(program, analysis, overlay, entry) else {
        return Vec::new();
    };
    let mut values: Vec<&abi::function::Value> = f.params.iter().collect();
    if let Some(r) = f.indirect_result.as_ref() {
        let at = abi::indirect_result_position(f.this).min(values.len());
        values.insert(at, r);
    }
    if values.len() != count {
        return Vec::new();
    }
    let word = frame_base(program);
    values
        .iter()
        .map(|v| match v.locs.as_slice() {
            [loc] => loc_home(*loc, word),
            _ => Home::Unknown,
        })
        .collect()
}

/// Returns the home one ABI location is.
///
/// # Arguments
///
/// * `loc` - The location.
/// * `word` - The return address's bytes a call pushes ([`frame_base`]).
fn loc_home(loc: Loc, word: i64) -> Home {
    match loc {
        Loc::X86(r) => Home::Register(format!("{r:?}").to_ascii_lowercase()),
        Loc::A64(a64::Reg::X(n)) => Home::Register(format!("x{n}")),
        Loc::A64(a64::Reg::V(n)) => Home::Register(format!("v{n}")),
        Loc::A64(a64::Reg::Sp | a64::Reg::Zr) => Home::Unknown,
        Loc::A32(r) => Home::Register(crate::isa::a32::name(r)),
        Loc::Rv(r) => Home::Register(crate::isa::rv::name(r).to_owned()),
        Loc::Stack(off) => i64::try_from(off)
            .ok()
            .and_then(|off| off.checked_sub(word))
            .map_or(Home::Unknown, Home::Cfa),
    }
}

/// Returns how a function's locals map to their homes.
///
/// A home follows the key each printed name stands for: an agent's name
/// for a key first ([`Overlay::vars`]), then the engine's own spelling of
/// a key no agent renamed ([`VarKey::parse`]), then a register of the
/// program's instruction set.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `realigned` - The stack offsets the lift addressed through a realigned
///   stack pointer: a slot at one has no home the engine states.
fn local_homes<'o>(
    program: &Program,
    overlay: &'o Overlay,
    entry: u64,
    realigned: &'o BTreeSet<i64>,
) -> impl Fn(&str) -> Home + 'o {
    let (word, _, frame) = slot_words(program, entry);
    let stated: BTreeMap<&'o str, VarKey> = overlay
        .vars
        .get(&entry)
        .map(|vars| vars.iter().map(|(k, v)| (v.name.as_str(), *k)).collect())
        .unwrap_or_default();
    let isa = program.arch.isa();
    move |name: &str| {
        let renamed = |k: &VarKey| stated.values().any(|s| s == k);
        let key = stated.get(name).copied().or_else(|| {
            VarKey::parse(name, word, frame)
                .ok()
                .filter(|k| !renamed(k))
        });
        match key {
            Some(VarKey::Slot(off)) if realigned.contains(&off) => Home::Unknown,
            Some(VarKey::Slot(off)) => off.checked_sub(frame).map_or(Home::Unknown, Home::Cfa),
            Some(VarKey::Param(_)) => Home::Unknown,
            None if isa.is_some_and(|isa| names_register(isa, name)) => {
                Home::Register(name.to_owned())
            }
            None => Home::Unknown,
        }
    }
}

/// Tells whether the lifter of `isa` names a register `name`: x86's
/// registers by the lifter's own list (its temporaries are no register),
/// the others by their disassembler's.
///
/// # Arguments
///
/// * `isa` - The instruction set.
/// * `name` - A printed variable name.
fn names_register(isa: Isa, name: &str) -> bool {
    match isa {
        Isa::X86 { .. } => is_register_name(name) && !is_temp_name(name),
        Isa::A64 | Isa::A32 | Isa::Rv(_) => isa_is_register(isa, name),
    }
}

/// Returns the locals one declaration line declares, each its name and
/// its C type: `T a, *b;` as `T` and `T *`, and `T a[N];` as `T[N]`.
///
/// # Arguments
///
/// * `line` - One declaration line, trimmed.
///
/// # Returns
///
/// The locals, none for a line that declares none this reads.
fn declared(line: &str) -> Vec<(String, String)> {
    if let Some((ty, items)) = super::super::vars::declaration(line) {
        return items
            .into_iter()
            .map(|(stars, name)| {
                let full = if stars.is_empty() {
                    ty.to_owned()
                } else {
                    format!("{ty} {stars}")
                };
                (name.to_owned(), full)
            })
            .collect();
    }
    let array = || {
        let (head, extent) = line.strip_suffix("];")?.split_once('[')?;
        let (ty, item) = head.rsplit_once(' ')?;
        let name = item.trim_start_matches('*');
        let stars = item.get(..item.len() - name.len())?;
        let digits = !extent.is_empty() && extent.bytes().all(|b| b.is_ascii_digit());
        let ty = if stars.is_empty() {
            format!("{ty}[{extent}]")
        } else {
            format!("{ty} {stars}[{extent}]")
        };
        (is_ident(name) && digits).then(|| (name.to_owned(), ty))
    };
    array().into_iter().collect()
}

/// Returns, for each identifier a definition's code names, the lines
/// naming it; comments, literals and the `extern` prototypes a body
/// declares (whose parameter names are their own) name nothing.
///
/// # Arguments
///
/// * `definition` - The definition, head line first.
fn naming_lines(definition: &str) -> BTreeMap<&str, Vec<DefLine>> {
    let mut out: BTreeMap<&str, Vec<DefLine>> = BTreeMap::new();
    let code = definition.lines().enumerate();
    for (i, line) in code.filter(|(_, l)| !l.trim_start().starts_with("extern ")) {
        let n = DefLine(i.saturating_add(1));
        for tok in lex(line).into_iter().filter(|t| t.lex == Lex::Name) {
            let Some(word) = line.get(tok.at..tok.end) else {
                continue;
            };
            let at = out.entry(word).or_default();
            if at.last() != Some(&n) {
                at.push(n);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::super::tests::ring;
    use super::super::{Library, Sink, cores, export, export_with};
    use super::{
        DefLine, Home, RECORD_STARTS_MAX, Record, Role, SinkLine, block, declared, local_homes,
        naming_lines,
    };
    use crate::analysis::protos::{Var, VarKey};
    use crate::analysis::{Analysis, Overlay};
    use crate::isa::a32::{Mode, Modes};
    use crate::program::{Arch, Program, Section};
    use std::collections::{BTreeMap, BTreeSet};

    /// Returns a raw image of `code` for `arch`, mapped and entered at
    /// 0x1000.
    ///
    /// # Arguments
    ///
    /// * `code` - The bytes.
    /// * `arch` - The architecture.
    ///
    /// # Panics
    ///
    /// When `code` is longer than an address can count.
    fn image(code: Vec<u8>, arch: Arch) -> Program {
        let len = u64::try_from(code.len()).expect("a small image");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        Program::raw(code, arch, 0, Some(0x1000), vec![text])
    }

    /// Returns the definitions an export recording on `cores` workers
    /// writes for `p` and each record with its head's line among them,
    /// checking the file is the one [`export`] writes.
    ///
    /// # Arguments
    ///
    /// * `p` - The image.
    /// * `o` - Names in force.
    /// * `cores` - Most workers.
    ///
    /// # Panics
    ///
    /// When a sink refuses, which these never do, or the files differ.
    fn recorded_on(p: &Program, o: &Overlay, cores: usize) -> (String, Vec<(SinkLine, Record)>) {
        let a = Analysis::compute(p);
        let (mut text, mut records) = (String::new(), Vec::new());
        let mut run = |t: &str| {
            text.push_str(t);
            Ok(())
        };
        let mut each = |line, r| {
            records.push((line, r));
            Ok(())
        };
        let sink = Sink::Recorded(&mut run, &mut each);
        let h = export_with(cores, p, &a, o, Library::Include, None, sink).expect("taken");
        let mut plain = String::new();
        let g = export(p, &a, o, Library::Include, None, &mut |t| {
            plain.push_str(t);
            Ok(())
        })
        .expect("the sink takes everything");
        assert_eq!(h.head("t") + text.as_str(), g.head("t") + plain.as_str());
        (text, records)
    }

    /// Returns what [`super::super::export_recorded`] hands its sinks for `p`
    /// ([`recorded_on`] on every core).
    ///
    /// # Arguments
    ///
    /// * `p` - The image.
    /// * `o` - Names in force.
    fn recorded(p: &Program, o: &Overlay) -> (String, Vec<(SinkLine, Record)>) {
        recorded_on(p, o, cores())
    }

    /// A recorded export writes the same records at one worker and many
    /// ([`ring`]), every function's lines placed.
    ///
    /// # Panics
    ///
    /// When the records differ between worker counts or a function
    /// places no line.
    #[test]
    fn records_do_not_depend_on_the_workers() {
        let p = ring();
        let o = Overlay::default();
        let one = recorded_on(&p, &o, 1);
        let placed = one.1.iter().filter(|(_, r)| !r.lines.is_empty()).count();
        assert_eq!(placed, 24, "{:?}", one.1);
        for _ in 0..3 {
            assert_eq!(recorded_on(&p, &o, 8), one);
        }
    }

    /// Returns the one record of `p`, and checks every line it places is a
    /// line of the definition that is neither blank nor a brace, and every
    /// block a line names is listed.
    ///
    /// # Arguments
    ///
    /// * `p` - The image.
    ///
    /// # Panics
    ///
    /// When there is not exactly one record or a check fails.
    fn only(p: &Program) -> Record {
        let (text, records) = recorded(p, &Overlay::default());
        let [(SinkLine(head), r)] = records.as_slice() else {
            panic!("one record: {records:?}\n{text}");
        };
        let lines: Vec<&str> = text.lines().collect();
        assert!(
            lines
                .get(*head)
                .is_some_and(|l| l.contains(&format!("{}(", r.name)))
        );
        for (DefLine(n), b) in &r.lines {
            let line = lines.get(head + n - 1).map_or("", |l| l.trim());
            assert!(
                !line.is_empty() && line != "{" && line != "}",
                "{n}: {line}\n{text}"
            );
            assert!(r.blocks.contains_key(b), "{b:#x} unlisted: {r:?}");
        }
        r.clone()
    }

    /// An x86-64 record: the parameter arrives in `rcx` (Microsoft x64, a
    /// raw image's convention), the body declares no locals, and its one
    /// block lists its four instructions.
    ///
    /// # Panics
    ///
    /// When the record says otherwise.
    #[test]
    fn an_x64_record_places_its_parameter_and_lines() {
        // ASM: cmp ecx, 0x1337abcd ; sete al ; movzx eax, al ; ret
        let code = vec![
            0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, 0x0f, 0x94, 0xc0, 0x0f, 0xb6, 0xc0, 0xc3,
        ];
        let r = only(&image(code, Arch::X86_64));
        assert_eq!((r.entry, r.name.as_str()), (0x1000, "sub_1000"));
        let [a1] = r.variables.as_slice() else {
            panic!("the parameter alone, no local: {r:?}");
        };
        let rcx = Home::Register("rcx".to_owned());
        assert_eq!(
            (a1.name.as_str(), a1.role, &a1.home),
            ("a1", Role::Param(0), &rcx)
        );
        let b = r.blocks.get(&0x1000).map(|b| (b.starts.clone(), b.cut));
        assert_eq!(b, Some((vec![0x1000, 0x1006, 0x1009, 0x100c], false)));
    }

    /// A 32-bit cdecl function's parameters arrive in the stack words just
    /// above the canonical frame address, 0 and 4 bytes from it.
    ///
    /// # Panics
    ///
    /// When a parameter reads another home.
    #[test]
    fn x86_cdecl_parameters_arrive_on_the_stack_above_the_cfa() {
        // ASM: mov eax, [esp+4] ; add eax, [esp+8] ; ret
        let code = vec![0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0xc3];
        let r = only(&image(code, Arch::X86));
        let homes: Vec<&Home> = r.variables.iter().map(|v| &v.home).collect();
        assert_eq!(homes, [&Home::Cfa(0), &Home::Cfa(4)], "{r:?}");
    }

    /// An arm64, an A32 and a Thumb record each place the parameter in the
    /// convention's first register and list the block's starts, a Thumb
    /// one at even addresses.
    ///
    /// # Panics
    ///
    /// When a record says otherwise.
    #[test]
    fn arm_records_place_their_parameter_in_the_first_register() {
        let words = |w: &[u32]| w.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>();
        // ASM: add w0, w0, #1 ; ret
        let a64 = image(words(&[0x1100_0400, 0xd65f_03c0]), Arch::Arm64);
        // ASM: add r0, r0, #1 ; bx lr
        let mut a32 = image(words(&[0xe280_0001, 0xe12f_ff1e]), Arch::Arm);
        a32.modes = Modes::from_marks(vec![(0x1000, Mode::Arm)]);
        // ASM: adds r0, #1 ; bx lr
        let mut thumb = image(vec![0x01, 0x30, 0x70, 0x47], Arch::Arm);
        thumb.modes = Modes::from_marks(vec![(0x1000, Mode::Thumb)]);
        for (p, reg, starts) in [
            (a64, "x0", vec![0x1000, 0x1004]),
            (a32, "r0", vec![0x1000, 0x1004]),
            (thumb, "r0", vec![0x1000, 0x1002]),
        ] {
            let r = only(&p);
            let a1 = r.variables.first().expect("a parameter");
            assert_eq!(
                (a1.role, &a1.home),
                (Role::Param(0), &Home::Register(reg.to_owned()))
            );
            assert!(!r.lines.is_empty(), "{r:?}");
            let b = r.blocks.get(&0x1000).map(|b| b.starts.clone());
            assert_eq!(b, Some(starts), "{r:?}");
        }
    }

    /// A loop's lines name only blocks of the function.
    ///
    /// The structurer and the text passes rewrite them (the webs renamed,
    /// the loop made a `do`); every block a line names is listed, and a
    /// line the rewrites leave unknown is absent, never guessed.
    ///
    /// # Panics
    ///
    /// When a line names a block of no function block or one the record
    /// leaves out.
    #[test]
    fn a_loop_places_its_lines_on_its_blocks() {
        // ASM: xor eax, eax ; L: add eax, ecx ; dec ecx ; jnz L ; ret
        let code = vec![0x31, 0xc0, 0x01, 0xc8, 0xff, 0xc9, 0x75, 0xfa, 0xc3];
        let r = only(&image(code, Arch::X86_64));
        let blocks = [0x1000, 0x1002, 0x1008];
        assert!(r.lines.values().all(|b| blocks.contains(b)), "{r:?}");
    }

    /// A function of thousands of statements places no line it cannot.
    ///
    /// Its rewrites pass the edit script's bounds and leave its lines
    /// unknown; each placed line is a line of the definition naming its
    /// one block, and the record's starts stay within the cap.
    ///
    /// # Panics
    ///
    /// When a placed line is blank or a brace, or the starts pass the cap.
    #[test]
    fn a_long_function_places_lines_it_can_and_stays_capped() {
        let mut code = Vec::new();
        for n in 0u32..5000 {
            // ASM: mov dword [rcx + n*8], n
            code.extend_from_slice(&[0xc7, 0x81]);
            code.extend_from_slice(&(n * 8).to_le_bytes());
            code.extend_from_slice(&n.to_le_bytes());
        }
        code.push(0xc3); // ASM: ret
        let r = only(&image(code, Arch::X86_64));
        let starts: usize = r.blocks.values().map(|b| b.starts.len()).sum();
        assert!(starts <= RECORD_STARTS_MAX);
        assert!(r.lines.values().all(|&b| b == 0x1000), "{:?}", r.lines);
    }

    /// A record names the function as the C file spells it: a clone's
    /// `.part.0` turned to `_part_0`, as its head and comment print it.
    ///
    /// # Panics
    ///
    /// When the record's name is not the head's.
    #[test]
    fn a_record_names_the_function_as_the_head_spells_it() {
        let p = image(vec![0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3], Arch::X86_64); // ASM: mov eax, 1; ret
        let mut o = Overlay::default();
        o.names.insert(0x1000, "Foo.part.0".to_owned());
        let (text, records) = recorded(&p, &o);
        let [(SinkLine(head), r)] = records.as_slice() else {
            panic!("one record: {records:?}");
        };
        assert_eq!(r.name, "Foo_part_0");
        let line = text.lines().nth(*head).unwrap_or_default();
        assert!(line.contains("Foo_part_0("), "{text}");
    }

    /// A local's home comes from its key, never from its name.
    ///
    /// A slot an agent renamed `count` or `rbx` is still that slot, the old
    /// name stands for nothing, and an `arg_N` or `home_N` slot is its
    /// offset; every offset is from the canonical frame address (x64:
    /// `local_10` under `push rbp` is 32 bytes below it; arm64: `local_8`
    /// is 8).
    ///
    /// # Panics
    ///
    /// When a name reads another home.
    #[test]
    fn a_local_lives_where_its_key_says() {
        let p = image(vec![0xc3], Arch::X86_64);
        let none = BTreeSet::new();
        let named = |name: &str| {
            let mut o = Overlay::default();
            let var = Var {
                name: name.to_owned(),
                ty: None,
            };
            o.vars
                .insert(0x1000, BTreeMap::from([(VarKey::Slot(-0x18), var)]));
            o
        };
        let count = named("count");
        let home = local_homes(&p, &count, 0x1000, &none);
        assert_eq!(home("count"), Home::Cfa(-0x20));
        assert_eq!(home("local_10"), Home::Unknown);
        assert_eq!(home("local_20"), Home::Cfa(-0x30));
        let rbx = named("rbx");
        assert_eq!(
            local_homes(&p, &rbx, 0x1000, &none)("rbx"),
            Home::Cfa(-0x20)
        );
        let plain = Overlay::default();
        let home = local_homes(&p, &plain, 0x1000, &none);
        assert_eq!(home("local_10"), Home::Cfa(-0x20));
        assert_eq!(home("home_8"), Home::Cfa(0x8));
        assert_eq!(home("arg_28"), Home::Cfa(0x28));
        let a64 = image(vec![0xc0, 0x03, 0x5f, 0xd6], Arch::Arm64); // ASM: ret
        assert_eq!(
            local_homes(&a64, &plain, 0x1000, &none)("local_8"),
            Home::Cfa(-0x8)
        );
        assert_eq!(home("rax"), Home::Register("rax".to_owned()));
        assert_eq!(home("var1"), Home::Unknown);
        assert_eq!(home("tmp_1"), Home::Unknown);
    }

    /// A declaration line declares its locals at their types, an array
    /// with its extent, and a line no plain declaration declares nothing.
    ///
    /// # Panics
    ///
    /// When a line reads otherwise.
    #[test]
    fn declarations_read_with_their_types() {
        let pair = |n: &str, t: &str| (n.to_owned(), t.to_owned());
        let both = [pair("a", "uint32_t"), pair("b", "uint32_t *")];
        assert_eq!(declared("uint32_t a, *b;"), both);
        let array = [pair("local_30", "uint8_t[48]")];
        assert_eq!(declared("uint8_t local_30[48];"), array);
        assert_eq!(declared("char *names[4];"), [pair("names", "char *[4]")]);
        assert!(declared("uint8_t x[n];").is_empty());
        assert!(declared("int32_t g; // @ 0x1000").is_empty());
    }

    /// A name in a comment, a literal or an `extern` prototype names
    /// nothing, and a line naming a word twice is listed once.
    ///
    /// # Panics
    ///
    /// When the lines differ.
    #[test]
    fn comments_and_literals_name_nothing() {
        let d =
            "int f(int a)\n{\n  extern int g(int a);\n  // a\n  puts(\"a\");\n  return a + a;\n}\n";
        assert_eq!(
            naming_lines(d).get("a"),
            Some(&vec![DefLine(1), DefLine(6)])
        );
    }

    /// A block longer than what is left of the cap lists that many starts
    /// and says it was cut; one whose bytes are not mapped lists none and
    /// says so too.
    ///
    /// # Panics
    ///
    /// When the starts are not capped or the cut is not said.
    #[test]
    fn a_block_past_the_cap_or_the_bytes_says_it_was_cut() {
        let mut code = vec![0x90; 64]; // ASM: nop
        code.push(0xc3); // ASM: ret
        let p = image(code, Arch::X86_64);
        let b = block(&p, 0x1000, 0x1041, 10);
        assert!(b.cut);
        assert_eq!(b.starts.len(), 10);
        assert_eq!(b.starts.get(1), Some(&0x1001));
        assert!(!block(&p, 0x1000, 0x1003, 10).cut);
        let gone = block(&p, 0x9000, 0x9010, 10);
        assert!(gone.cut && gone.starts.is_empty());
    }
}
