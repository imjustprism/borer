//! Objective-C metadata: the classes, categories and protocols a Mach-O
//! image describes, the methods they name, and the messages its code
//! sends.
//!
//! clang writes the runtime's view of every class into the image.
//! `__objc_classlist` points at each class (`class_t`), whose data word,
//! its low bits the Swift and fast flags, points at the read-only part
//! (`class_ro_t`) holding the name and the instance methods; the class's
//! `isa` points at its metaclass, whose read-only part lists the class
//! methods. A method list holds three pointers per method (selector name,
//! types, implementation) or, from iOS 14 and macOS 11, three 32-bit
//! offsets each from its own field (a selector reference, the types, the
//! implementation). `__objc_catlist` points at each category, naming the
//! class it extends (a bind when that class is another image's) and its
//! two method lists; `__objc_protolist` at each protocol;
//! `__objc_selrefs` holds the selector every message names and
//! `__objc_classrefs` the class a message is sent to. Every pointer is
//! read through the image's fixups ([`crate::dyld`]), so a chained image
//! reads as dyld leaves it.
//!
//! [`infer`] names each method's implementation `-[Class sel]`, `+[Class
//! sel]` for a class method and `-[Class(Category) sel]` for a category's
//! ([`NameSource::ObjC`]), never over a symbol, and each `__objc_stubs`
//! entry `objc_msgSend$sel` after the selector it loads. At each call to
//! `objc_msgSend` (its super and struct-return forms too, or a stub) whose
//! selector register was loaded from a selector reference (`x1` on arm64,
//! `rsi` on x86-64, the next one for a struct-return form), the message is
//! recovered as `[recv sel]`: the receiver is the class a class reference
//! names, `super`, the message whose result it is, `self` in a method that
//! has not written it (`a1` elsewhere), or `?`. A summary, a listing and a
//! decompile's `// messages:` header line show them ([`sent_by`]), and the
//! decompiler reads a selector reference as `@selector(sel)` and a class
//! reference as its class. A pointer that maps nothing, a list past the
//! cap or a name that is no C string is refused and counted, never
//! followed.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::functions::decode_block;
use super::{Analysis, Function, NameSource, RefKind, read_u32, read_word, unique_name};
use crate::isa::Isa;
use crate::isa::a64::{self, Mnemonic as A64Mnemonic, Mode, Op, Opnd, Reg, Width};
use crate::isa::x86::{FlowControl, InstructionInfoFactory, Mnemonic, OpAccess, OpKind};
use crate::program::{BinaryFormat, Program, SymbolKind};
use crate::table::Window;

/// The bits of a class's data word that hold its `class_ro_t`: the low
/// three are the Swift and fast flags.
const FAST_DATA_MASK: u64 = 0x0000_7fff_ffff_fff8;
/// `method_list_t`'s flag for a list of 32-bit offsets.
const SMALL_METHODS: u32 = 0x8000_0000;
/// A small list whose name offsets reach the selector itself rather than
/// a selector reference (the shared cache's).
const DIRECT_SELECTORS: u32 = 0x4000_0000;
/// The entry size bits of a method list's first word.
const ENTSIZE_MASK: u32 = 0x0000_fffc;
/// Bytes of one small method: three 32-bit offsets.
const SMALL_METHOD: u64 = 12;
/// Bytes of one method of pointers: name, types and implementation.
const BIG_METHOD: u64 = 24;
/// Most methods read from one list.
const METHODS_MAX: u32 = 4096;
/// Most entries read from one metadata section.
const LIST_MAX: usize = 1 << 16;
/// Longest class, category or selector name read.
const NAME_MAX: usize = 1024;
/// Longest receiver a nested message keeps; past it the receiver is `?`.
const RECEIVER_MAX: usize = 160;
/// What a class's symbol starts with, the C underscore dropped.
const CLASS_PREFIX: &str = "OBJC_CLASS_$_";
/// Most rows one read of [`objc_tsv`] lists.
const PAGE: usize = 200;
/// Most protocol names [`objc_tsv`] lists.
const PROTOCOLS_SHOWN: usize = 20;

/// One method a class or category lists.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjcMethod {
    /// Its selector.
    pub selector: String,
    /// Sent to the class rather than an instance (`+`).
    pub class_method: bool,
    /// Its implementation's address, `None` where the list states none.
    pub imp: Option<u64>,
}

/// One class the image defines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjcClass {
    /// Its name.
    pub name: String,
    /// The class it inherits from, `None` for a root class.
    pub superclass: Option<String>,
    /// Its `class_t`'s address.
    pub address: u64,
    /// Its instance methods, then its class methods.
    pub methods: Vec<ObjcMethod>,
}

/// One category the image defines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjcCategory {
    /// Its name.
    pub name: String,
    /// The class it extends.
    pub class: String,
    /// Its instance methods, then its class methods.
    pub methods: Vec<ObjcMethod>,
}

/// One message a call sends.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message {
    /// The receiver: a class, `super`, `self`, `a1`, a nested message or
    /// `?`.
    pub receiver: String,
    /// The selector.
    pub selector: String,
}

impl Message {
    /// Renders the message as `[recv sel]`.
    #[must_use]
    pub fn text(&self) -> String {
        format!("[{} {}]", self.receiver, self.selector)
    }
}

/// What a Mach-O image's Objective-C metadata says.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ObjcFacts {
    /// The classes `__objc_classlist` names, in its order.
    pub classes: Vec<ObjcClass>,
    /// The categories `__objc_catlist` names, in its order.
    pub categories: Vec<ObjcCategory>,
    /// The protocols `__objc_protolist` names, in its order.
    pub protocols: Vec<String>,
    /// Each selector reference's address to its selector.
    pub selrefs: BTreeMap<u64, String>,
    /// Each class reference's address to its class.
    pub classrefs: BTreeMap<u64, String>,
    /// Each message send's call site to the message.
    pub messages: BTreeMap<u64, Message>,
    /// Entries refused: a pointer that maps nothing, a name that is no C
    /// string, a malformed method list, or one past the cap.
    pub refused: usize,
}

/// Lists the messages a function sends, in address order.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `f` - The function.
///
/// # Returns
///
/// Each message as `[recv sel]`, its call site inside one of the
/// function's blocks.
pub(crate) fn sent_by(a: &Analysis, f: &Function) -> Vec<String> {
    a.objc
        .messages
        .range(f.start..f.end)
        .filter(|(site, _)| f.blocks.iter().any(|b| (b.start..b.end).contains(*site)))
        .map(|(_, m)| m.text())
        .collect()
}

/// Where a call's argument register got its value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Arg {
    /// Loaded from this constant address.
    Slot(u64),
    /// The result of the call at this address.
    Result(u64),
    /// Not written since the function's entry: what its caller passed.
    Entry,
    /// Anything else.
    Unknown,
}

/// What a call calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Callee {
    /// A direct call's target.
    Direct(u64),
    /// The slot an indirect call reads its target from.
    Slot(u64),
}

/// One call and where its first three argument registers got their
/// values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Call {
    /// The call's address.
    pub(crate) site: u64,
    /// What it calls.
    pub(crate) callee: Callee,
    /// `x0`..`x2` on arm64, `rdi`, `rsi` and `rdx` on x86-64.
    pub(crate) args: [Arg; 3],
}

/// Tells, for each block, whether its one way in is falling through from
/// the block right before it, as the block after a call is entered: what
/// the registers held there carries over.
///
/// # Arguments
///
/// * `blocks` - A function's blocks, in address order.
///
/// # Returns
///
/// One flag per block.
pub(crate) fn falls_through(blocks: &[super::BasicBlock]) -> Vec<bool> {
    let mut ins: BTreeMap<u64, usize> = BTreeMap::new();
    for b in blocks {
        for &s in &b.successors {
            *ins.entry(s).or_default() += 1;
        }
    }
    blocks
        .iter()
        .enumerate()
        .map(|(k, b)| {
            k.checked_sub(1)
                .and_then(|p| blocks.get(p))
                .is_some_and(|prev| {
                    prev.end == b.start
                        && prev.successors.contains(&b.start)
                        && ins.get(&b.start) == Some(&1)
                })
        })
        .collect()
}

/// How a message send passes its receiver and selector.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Send {
    /// `objc_msgSend` and its float-return forms: receiver, selector.
    Plain,
    /// `objc_msgSendSuper` and `objc_msgSendSuper2`: an `objc_super`,
    /// selector.
    Super,
    /// `objc_msgSend_stret`: the result's address, receiver, selector.
    Stret,
    /// The super forms of `objc_msgSend_stret`.
    SuperStret,
    /// An `__objc_stubs` entry, which loads its own selector: receiver.
    Stub(String),
}

impl Send {
    /// Says which arguments carry the receiver and the selector.
    ///
    /// # Returns
    ///
    /// The receiver's argument index (`None` for a super send, whose
    /// receiver is `super`) and the selector's, `None` for a stub, which
    /// carries its own.
    fn roles(&self) -> (Option<usize>, Option<usize>) {
        match self {
            Send::Plain => (Some(0), Some(1)),
            Send::Super => (None, Some(1)),
            Send::Stret => (Some(1), Some(2)),
            Send::SuperStret => (None, Some(2)),
            Send::Stub(_) => (Some(0), None),
        }
    }
}

/// Reads which send a runtime function or `__objc_stubs` entry is.
///
/// # Arguments
///
/// * `name` - The function's bare name.
///
/// # Returns
///
/// The send, or `None` for any other function.
fn send_of(name: &str) -> Option<Send> {
    if let Some(sel) = name.strip_prefix("objc_msgSend$") {
        return Some(Send::Stub(sel.to_owned()));
    }
    match name {
        "objc_msgSend" | "objc_msgSend_fpret" | "objc_msgSend_fp2ret" => Some(Send::Plain),
        "objc_msgSendSuper" | "objc_msgSendSuper2" => Some(Send::Super),
        "objc_msgSend_stret" => Some(Send::Stret),
        "objc_msgSendSuper_stret" | "objc_msgSendSuper2_stret" => Some(Send::SuperStret),
        _ => None,
    }
}

/// Reads the pointer at `va`, zero meaning none.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `va` - The pointer's address.
fn ptr(p: &Program, va: u64) -> Option<u64> {
    read_word(p, va).filter(|&v| v != 0)
}

/// Reads the C string at `va` as a name: printable ASCII without spaces,
/// NUL-terminated within [`NAME_MAX`] bytes.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `va` - The string's address.
fn name_at(p: &Program, va: u64) -> Option<String> {
    let raw = p.read_va_upto(va, NAME_MAX)?;
    let len = raw.iter().position(|&b| b == 0)?;
    let name = raw
        .get(..len)
        .filter(|n| !n.is_empty() && n.iter().all(u8::is_ascii_graphic))?;
    Some(String::from_utf8_lossy(name).into_owned())
}

/// Reads the words of every section whose name is `name`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `name` - The section's name without its segment (`__objc_selrefs`).
///
/// # Returns
///
/// `(address, word)` pairs, at most [`LIST_MAX`] a section.
fn words(p: &Program, name: &str) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    for s in p
        .sections
        .iter()
        .filter(|s| s.name.rsplit(',').next() == Some(name))
    {
        let Some(bytes) = p.section_bytes(s) else {
            continue;
        };
        for (k, w) in bytes.chunks_exact(8).enumerate().take(LIST_MAX) {
            let mut le = [0u8; 8];
            le.copy_from_slice(w);
            let at = crate::num::from_usize(k * 8);
            out.push((s.va.0.wrapping_add(at), u64::from_le_bytes(le)));
        }
    }
    out
}

/// Reads a class's name.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `cls` - The `class_t`'s address.
fn class_name(p: &Program, cls: u64) -> Option<String> {
    let ro = ptr(p, cls.wrapping_add(32))? & FAST_DATA_MASK;
    name_at(p, ptr(p, ro.wrapping_add(24))?)
}

/// Reads the class a slot names: the import a bind fills it with, its
/// `OBJC_CLASS_$_` prefix dropped, or the class it points at.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `slot` - The slot's address.
fn class_at_slot(p: &Program, slot: u64) -> Option<String> {
    if let Some(import) = p.relocs.bound_at(slot) {
        let name = import.name.strip_prefix('_').unwrap_or(&import.name);
        return Some(name.strip_prefix(CLASS_PREFIX).unwrap_or(name).to_owned());
    }
    class_name(p, ptr(p, slot)?)
}

/// Reads one method list.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `list` - The list's address, `None` for no list.
/// * `class_method` - Whether its methods are class methods.
/// * `out` - Receives the methods.
/// * `refused` - Counts what does not read.
fn methods(
    p: &Program,
    list: Option<u64>,
    class_method: bool,
    out: &mut Vec<ObjcMethod>,
    refused: &mut usize,
) {
    let Some(list) = list else {
        return;
    };
    let (Some(head), Some(count)) = (read_u32(p, list), read_u32(p, list.wrapping_add(4))) else {
        *refused += 1;
        return;
    };
    let small = head & SMALL_METHODS != 0;
    let size = u64::from(head & ENTSIZE_MASK);
    if (small && size != SMALL_METHOD) || (!small && size < BIG_METHOD) {
        *refused += 1;
        return;
    }
    *refused += usize::from(count > METHODS_MAX);
    let relative = |field: u64| {
        read_u32(p, field)
            .filter(|&o| o != 0)
            .map(|o| field.wrapping_add_signed(i64::from(o.cast_signed())))
    };
    for k in 0..u64::from(count.min(METHODS_MAX)) {
        let e = list.wrapping_add(8).wrapping_add(k * size);
        let (selector, imp) = if small {
            let name = relative(e).and_then(|at| {
                if head & DIRECT_SELECTORS != 0 {
                    Some(at)
                } else {
                    ptr(p, at)
                }
            });
            (
                name.and_then(|at| name_at(p, at)),
                relative(e.wrapping_add(8)),
            )
        } else {
            (
                ptr(p, e).and_then(|at| name_at(p, at)),
                ptr(p, e.wrapping_add(16)),
            )
        };
        match selector {
            Some(selector) => out.push(ObjcMethod {
                selector,
                class_method,
                imp,
            }),
            None => *refused += 1,
        }
    }
}

/// Reads one class: its name, superclass and both method lists.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `cls` - The `class_t`'s address.
/// * `refused` - Counts what does not read.
///
/// # Returns
///
/// The class, or `None` when its read-only part or name does not read.
fn class(p: &Program, cls: u64, refused: &mut usize) -> Option<ObjcClass> {
    let ro = ptr(p, cls.wrapping_add(32))? & FAST_DATA_MASK;
    let name = name_at(p, ptr(p, ro.wrapping_add(24))?)?;
    let mut list = Vec::new();
    methods(p, ptr(p, ro.wrapping_add(32)), false, &mut list, refused);
    let meta = ptr(p, cls)
        .filter(|&m| m != cls)
        .and_then(|m| ptr(p, m.wrapping_add(32)))
        .map(|d| d & FAST_DATA_MASK);
    if let Some(meta) = meta {
        methods(p, ptr(p, meta.wrapping_add(32)), true, &mut list, refused);
    }
    Some(ObjcClass {
        name,
        superclass: class_at_slot(p, cls.wrapping_add(8)),
        address: cls,
        methods: list,
    })
}

/// Reads one category: its name, its class and both method lists.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `cat` - The `category_t`'s address.
/// * `refused` - Counts what does not read.
///
/// # Returns
///
/// The category, or `None` when its name or class does not read.
fn category(p: &Program, cat: u64, refused: &mut usize) -> Option<ObjcCategory> {
    let name = name_at(p, ptr(p, cat)?)?;
    let class = class_at_slot(p, cat.wrapping_add(8))?;
    let mut list = Vec::new();
    methods(p, ptr(p, cat.wrapping_add(16)), false, &mut list, refused);
    methods(p, ptr(p, cat.wrapping_add(24)), true, &mut list, refused);
    Some(ObjcCategory {
        name,
        class,
        methods: list,
    })
}

/// Reads the selector an arm64 `__objc_stubs` entry loads into `x1`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `entry` - The stub's address.
/// * `selrefs` - The selector references.
///
/// # Returns
///
/// The selector, or `None` when the stub does not open with `adrp x1,
/// page; ldr x1, [x1, #off]` loading a selector reference.
fn stub_selector<'s>(
    p: &Program,
    entry: u64,
    selrefs: &'s BTreeMap<u64, String>,
) -> Option<&'s String> {
    let decode = |va: u64| Some(a64::decode(read_u32(p, va)?, va));
    let (first, second) = (decode(entry)?, decode(entry.wrapping_add(4))?);
    let x1 = |o: &Opnd| {
        matches!(
            o,
            Opnd::Reg {
                reg: Reg::X(1),
                bits: 64
            }
        )
    };
    let (Op::Adrp, true, Opnd::PcRel(page)) = (first.op, x1(&first.operands[0]), first.operands[1])
    else {
        return None;
    };
    let m = second.operands.iter().find_map(|o| match *o {
        Opnd::Mem(m) => Some(m),
        Opnd::None
        | Opnd::Reg { .. }
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Cond(_)
        | Opnd::Other => None,
    })?;
    let load = second.mnemonic == A64Mnemonic::Ldr(Width::Reg)
        && x1(&second.operands[0])
        && m.base == Reg::X(1)
        && m.index.is_none()
        && m.mode == Mode::Offset;
    load.then(|| selrefs.get(&page.wrapping_add_signed(m.disp)))
        .flatten()
}

/// Reads where an x86-64 function's calls take their first three
/// arguments from, block by block.
///
/// A `mov` from a RIP-relative address loads a slot, a `mov` between
/// registers copies what the source held, a call leaves its result in
/// `rax` and changes what the System V convention lets a callee change,
/// and every other write forgets the register. The entry block's
/// registers start as the caller's, and a block entered only by falling
/// through from the one before it, as the block after a call is, keeps
/// what they held there ([`falls_through`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The function.
///
/// # Returns
///
/// The direct calls and the calls through a RIP-relative slot, with
/// `rdi`, `rsi` and `rdx`.
fn x86_calls(p: &Program, f: &Function) -> Vec<Call> {
    /// `rax`, `rcx`, `rdx`, `rsi`, `rdi` and `r8` to `r11` by bank slot:
    /// what a System V callee may change.
    const CLOBBERS: [usize; 9] = [0, 1, 2, 6, 7, 8, 9, 10, 11];
    /// `rdi`, `rsi` and `rdx` by bank slot: the first three arguments.
    const ARGS: [usize; 3] = [7, 6, 2];
    /// General-purpose registers banked.
    const GPRS: usize = 16;
    let gpr = |r: crate::isa::x86::Register| {
        (r.size() == 8)
            .then(|| crate::isa::x86::gpr_bank_index(r))
            .flatten()
            .filter(|&k| k < GPRS)
    };
    let mut factory = InstructionInfoFactory::new();
    let mut out = Vec::new();
    let carried = falls_through(&f.blocks);
    let mut regs = [Arg::Unknown; GPRS];
    for (b, carry) in f.blocks.iter().zip(carried) {
        if !carry {
            regs = [if b.start == f.entry {
                Arg::Entry
            } else {
                Arg::Unknown
            }; GPRS];
        }
        for i in decode_block(p, 64, b) {
            if matches!(
                i.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                let callee = match i.op0_kind() {
                    OpKind::NearBranch64 => Some(Callee::Direct(i.near_branch64())),
                    OpKind::Memory if i.is_ip_rel_memory_operand() => {
                        Some(Callee::Slot(i.memory_displacement64()))
                    }
                    _ => None,
                };
                if let Some(callee) = callee {
                    out.push(Call {
                        site: i.ip(),
                        callee,
                        args: ARGS.map(|k| regs.get(k).copied().unwrap_or(Arg::Unknown)),
                    });
                }
                for k in CLOBBERS {
                    if let Some(r) = regs.get_mut(k) {
                        *r = Arg::Unknown;
                    }
                }
                regs[0] = Arg::Result(i.ip());
                continue;
            }
            if i.mnemonic() == Mnemonic::Mov
                && i.op_count() == 2
                && i.op0_kind() == OpKind::Register
                && let Some(d) = gpr(i.op0_register())
            {
                let value = match i.op1_kind() {
                    OpKind::Memory if i.is_ip_rel_memory_operand() => {
                        Some(Arg::Slot(i.memory_displacement64()))
                    }
                    OpKind::Register => gpr(i.op1_register()).and_then(|s| regs.get(s).copied()),
                    _ => None,
                };
                if let (Some(v), Some(r)) = (value, regs.get_mut(d)) {
                    *r = v;
                    continue;
                }
            }
            for ur in factory.info(&i).used_registers() {
                let written = matches!(
                    ur.access(),
                    OpAccess::Write
                        | OpAccess::ReadWrite
                        | OpAccess::CondWrite
                        | OpAccess::ReadCondWrite
                );
                if written
                    && let Some(r) = crate::isa::x86::gpr_bank_index(ur.register().full_register())
                        .and_then(|k| regs.get_mut(k))
                {
                    *r = Arg::Unknown;
                }
            }
        }
    }
    out
}

/// Reads an image's Objective-C metadata, names the methods and stubs it
/// describes, and recovers the messages its code sends.
///
/// # Arguments
///
/// * `program` - The loaded image; anything but a 64-bit Mach-O has
///   nothing to read.
/// * `analysis` - The analysis, its functions renamed and its
///   [`Analysis::objc`] filled.
pub(crate) fn infer(program: &Program, analysis: &mut Analysis) {
    if program.format != BinaryFormat::MachO || !program.is_64 {
        return;
    }
    let mut facts = ObjcFacts::default();
    for (slot, at) in words(program, "__objc_selrefs") {
        match name_at(program, at) {
            Some(sel) => {
                facts.selrefs.insert(slot, sel);
            }
            None => facts.refused += 1,
        }
    }
    for (slot, _) in words(program, "__objc_classrefs")
        .into_iter()
        .chain(words(program, "__objc_superrefs"))
    {
        match class_at_slot(program, slot) {
            Some(name) => {
                facts.classrefs.insert(slot, name);
            }
            None => facts.refused += 1,
        }
    }
    let mut refused = 0usize;
    for (_, cls) in words(program, "__objc_classlist") {
        match class(program, cls, &mut refused) {
            Some(c) => facts.classes.push(c),
            None => refused += 1,
        }
    }
    for (_, cat) in words(program, "__objc_catlist") {
        match category(program, cat, &mut refused) {
            Some(c) => facts.categories.push(c),
            None => refused += 1,
        }
    }
    let mut seen = BTreeSet::new();
    for (_, proto) in words(program, "__objc_protolist") {
        match ptr(program, proto.wrapping_add(8)).and_then(|at| name_at(program, at)) {
            Some(name) if seen.insert(name.clone()) => facts.protocols.push(name),
            Some(_) => {}
            None => refused += 1,
        }
    }
    facts.refused += refused;
    if facts == ObjcFacts::default() {
        return;
    }
    let stubs = stubs(program, analysis, &facts.selrefs);
    let methods = name_methods(analysis, &facts, &stubs);
    facts.messages = messages(program, analysis, &facts, &stubs, &methods);
    analysis.objc = facts;
}

/// Finds the arm64 `__objc_stubs` entries the functions start at.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `selrefs` - The selector references.
///
/// # Returns
///
/// Each stub's entry to the selector it sends.
fn stubs(p: &Program, a: &Analysis, selrefs: &BTreeMap<u64, String>) -> BTreeMap<u64, String> {
    let mut out = BTreeMap::new();
    if p.arch.isa() != Some(Isa::A64) {
        return out;
    }
    for s in p
        .sections
        .iter()
        .filter(|s| s.name.rsplit(',').next() == Some("__objc_stubs"))
    {
        let end = s.va.0.saturating_add(s.vsize);
        let start = a.functions.partition_point(|f| f.entry < s.va.0);
        for f in a.functions.iter().skip(start).take_while(|f| f.entry < end) {
            if let Some(sel) = stub_selector(p, f.entry, selrefs) {
                out.insert(f.entry, sel.clone());
            }
        }
    }
    out
}

/// Names each method's implementation and each stub
/// ([`NameSource::ObjC`]), never over a name the program's symbols gave.
///
/// # Arguments
///
/// * `a` - The analysis, its functions renamed.
/// * `facts` - The classes and categories.
/// * `stubs` - Each stub's entry to its selector.
///
/// # Returns
///
/// The entries of the methods' implementations.
fn name_methods(
    a: &mut Analysis,
    facts: &ObjcFacts,
    stubs: &BTreeMap<u64, String>,
) -> BTreeSet<u64> {
    let sign = |m: &ObjcMethod| if m.class_method { '+' } else { '-' };
    let mut names: BTreeMap<u64, String> = BTreeMap::new();
    for c in &facts.classes {
        for m in &c.methods {
            if let Some(imp) = m.imp {
                names
                    .entry(imp)
                    .or_insert_with(|| format!("{}[{} {}]", sign(m), c.name, m.selector));
            }
        }
    }
    for c in &facts.categories {
        for m in &c.methods {
            if let Some(imp) = m.imp {
                names.entry(imp).or_insert_with(|| {
                    format!("{}[{}({}) {}]", sign(m), c.class, c.name, m.selector)
                });
            }
        }
    }
    let methods: BTreeSet<u64> = names.keys().copied().collect();
    for (entry, sel) in stubs {
        names
            .entry(*entry)
            .or_insert_with(|| format!("objc_msgSend${sel}"));
    }
    let mut taken: BTreeSet<String> = a
        .functions
        .iter()
        .filter(|f| !f.name_inferred)
        .filter_map(|f| f.name.clone())
        .collect();
    for f in &mut a.functions {
        let Some(base) = names.get(&f.entry) else {
            continue;
        };
        if f.name.is_some() && !f.name_inferred {
            continue;
        }
        f.name = Some(unique_name(&mut taken, base));
        f.name_inferred = true;
        f.name_source = NameSource::ObjC;
    }
    methods
}

/// Recovers the message each send sends.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `facts` - The selector and class references.
/// * `stubs` - Each stub's entry to its selector.
/// * `methods` - The entries of the methods' implementations, where an
///   unwritten first argument is `self`.
///
/// # Returns
///
/// Each send's call site to its message.
fn messages(
    p: &Program,
    a: &Analysis,
    facts: &ObjcFacts,
    stubs: &BTreeMap<u64, String>,
    methods: &BTreeSet<u64>,
) -> BTreeMap<u64, Message> {
    let mut sends: BTreeMap<u64, Send> = BTreeMap::new();
    for s in &p.symbols {
        if s.kind == SymbolKind::Import
            && s.addr != 0
            && let Some(send) = send_of(super::bare_name(&s.name))
        {
            sends.entry(s.addr).or_insert(send);
        }
    }
    for f in &a.functions {
        let send = stubs
            .get(&f.entry)
            .map(|sel| Send::Stub(sel.clone()))
            .or_else(|| {
                f.thunk
                    .and_then(|slot| sends.get(&slot).cloned())
                    .or_else(|| f.name.as_deref().and_then(send_of))
            });
        if let Some(send) = send {
            sends.insert(f.entry, send);
        }
    }
    let senders: BTreeSet<u64> = sends
        .keys()
        .filter_map(|t| a.xrefs.get(t))
        .flatten()
        .filter(|s| s.kind == RefKind::Call)
        .filter_map(|s| s.from_entry)
        .filter(|e| !sends.contains_key(e))
        .collect();
    let senders: Vec<&Function> = senders.iter().filter_map(|&e| a.function(e)).collect();
    let calls_of = |f: &&Function| match p.arch.isa() {
        Some(Isa::A64) => super::a64::calls(p, f),
        Some(Isa::X86 { bits: 64 }) => x86_calls(p, f),
        Some(Isa::X86 { .. } | Isa::A32) | None => Vec::new(),
    };
    let found = super::striped(&senders, calls_of);
    let mut out = BTreeMap::new();
    for (f, calls) in senders.iter().zip(found) {
        for c in calls.unwrap_or_else(|| calls_of(f)) {
            let (Callee::Direct(target) | Callee::Slot(target)) = c.callee;
            let Some(send) = sends.get(&target) else {
                continue;
            };
            let (receiver, selector) = send.roles();
            let selector = match send {
                Send::Stub(sel) => Some(sel.clone()),
                Send::Plain | Send::Super | Send::Stret | Send::SuperStret => {
                    match selector.and_then(|k| c.args.get(k)) {
                        Some(Arg::Slot(slot)) => facts.selrefs.get(slot).cloned(),
                        Some(Arg::Result(_) | Arg::Entry | Arg::Unknown) | None => None,
                    }
                }
            };
            let Some(selector) = selector else {
                continue;
            };
            let receiver = match receiver.map(|k| c.args.get(k).copied().unwrap_or(Arg::Unknown)) {
                None => "super".to_owned(),
                Some(Arg::Slot(slot)) => facts
                    .classrefs
                    .get(&slot)
                    .cloned()
                    .unwrap_or_else(|| "?".to_owned()),
                Some(Arg::Result(site)) => out
                    .get(&site)
                    .map(Message::text)
                    .filter(|t| t.len() <= RECEIVER_MAX)
                    .unwrap_or_else(|| "?".to_owned()),
                Some(Arg::Entry) if methods.contains(&f.entry) => "self".to_owned(),
                Some(Arg::Entry) => "a1".to_owned(),
                Some(Arg::Unknown) => "?".to_owned(),
            };
            out.insert(c.site, Message { receiver, selector });
        }
    }
    out
}

/// Renders the classes and categories the metadata describes, one row
/// per method.
///
/// The header counts the methods, classes, categories, protocols,
/// selector references and recovered messages; a `# protocols:` line
/// names the first [`PROTOCOLS_SHOWN`]; each row is the class (`Class` or
/// `Class(Category)`), its superclass, `-` or `+`, the selector and the
/// implementation's address, and a class with no method has one row with
/// neither. An answer lists [`PAGE`] rows at most.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `filter` - Case-insensitive substring of the class or selector;
///   empty for all.
/// * `window` - The rows shown and the URI naming the next page.
#[must_use]
pub fn objc_tsv(a: &Analysis, filter: &str, window: Window<'_>) -> String {
    let objc = &a.objc;
    let q = filter.to_lowercase();
    let mut rows: Vec<String> = Vec::new();
    let mut add = |owner: &str, superclass: &str, list: &[ObjcMethod]| {
        let matches = |sel: &str| {
            q.is_empty() || owner.to_lowercase().contains(&q) || sel.to_lowercase().contains(&q)
        };
        if list.is_empty() && matches("") {
            rows.push(format!("{owner}\t{superclass}\t\t\t"));
        }
        for m in list.iter().filter(|m| matches(&m.selector)) {
            rows.push(format!(
                "{owner}\t{superclass}\t{}\t{}\t{}",
                if m.class_method { '+' } else { '-' },
                m.selector,
                m.imp.map_or_else(String::new, |i| format!("{i:#x}"))
            ));
        }
    };
    for c in &objc.classes {
        add(&c.name, c.superclass.as_deref().unwrap_or(""), &c.methods);
    }
    for c in &objc.categories {
        add(&format!("{}({})", c.class, c.name), "", &c.methods);
    }
    let total = rows.len();
    let shown = total
        .saturating_sub(window.skip)
        .min(window.limit)
        .min(PAGE);
    let methods: usize = objc
        .classes
        .iter()
        .map(|c| c.methods.len())
        .chain(objc.categories.iter().map(|c| c.methods.len()))
        .sum();
    let mut out = format!(
        "# {methods} Objective-C methods in {} classes and {} categories, {} protocols, {} selector references, {} messages recovered",
        objc.classes.len(),
        objc.categories.len(),
        objc.protocols.len(),
        objc.selrefs.len(),
        objc.messages.len()
    );
    if objc.refused > 0 {
        let _ = write!(
            out,
            "; {} entries refused (a pointer that maps nothing, a name that is no C string, a malformed method list, or past the cap)",
            objc.refused
        );
    }
    let _ = writeln!(out, "\n# showing {shown} of {total} rows");
    if !objc.protocols.is_empty() {
        let names: Vec<&str> = objc
            .protocols
            .iter()
            .take(PROTOCOLS_SHOWN)
            .map(String::as_str)
            .collect();
        let more = objc.protocols.len().saturating_sub(PROTOCOLS_SHOWN);
        let tail = if more > 0 {
            format!(" (+{more} more)")
        } else {
            String::new()
        };
        let _ = writeln!(out, "# protocols: {}{tail}", names.join(", "));
    }
    out.push_str("class\tsuperclass\tkind\tselector\timp\n");
    for row in rows.iter().skip(window.skip).take(shown) {
        out.push_str(row);
        out.push('\n');
    }
    out.push_str(&window.next_page(total, shown));
    out
}
