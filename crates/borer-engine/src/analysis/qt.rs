//! Qt `moc` metadata: the class, signals, slots and properties every
//! `QObject` subclass carries, and the functions they name.
//!
//! `moc` writes three things per class into the image: a string table
//! (`qt_meta_stringdata_<Class>`, an array of `QByteArrayData` headers
//! followed by the strings), a table of integers (`qt_meta_data_<Class>`: a
//! revision, then counts and offsets, then five words per method: name,
//! argument count, parameter offset, tag, flags), and a `QMetaObject`
//! naming both together with `qt_static_metacall`, the function that
//! dispatches a method index to its implementation. The string table is
//! found by its shape: headers whose reference count is -1 and whose offset
//! lands on a string of the stated length, the first of them the class
//! name and the strings starting right after the last header. The
//! meta-object is the record that points at the table, and its dispatcher
//! calls the methods in index order, so the calls it makes, in address
//! order, name them: a direct call names its target, a call through a
//! vtable slot names the function in that slot of the class's table.

use std::collections::{BTreeMap, BTreeSet};

use crate::isa::x86::{FlowControl, Mnemonic, OpKind, Register};

use super::{Analysis, NameSource, RefKind, pointer_size, read_u32, read_word, unique_name};
use crate::num::from_usize;
use crate::program::Program;

/// Most headers one string table may hold.
const ENTRIES_MAX: usize = 4096;
/// Longest string a header may name.
const STRING_MAX: u32 = 1024;
/// Most instructions in the lambda a literal macro expands to: a frame,
/// the result pointer's load, the temporary's zeroing, the store and the
/// epilogue.
const LAMBDA_INSTRS_MAX: usize = 12;
/// Longest run of the literal's text kept in the lambda's name.
const LAMBDA_NAME_MAX: usize = 40;
/// The virtuals `Q_OBJECT` declares, in vtable order after `QObject`'s.
const QOBJECT_VIRTUALS: [&str; 3] = ["metaObject", "qt_metacast", "qt_metacall"];
/// Most methods read from one meta-data table.
const METHODS_MAX: u32 = 2048;
/// Words the meta-data header holds before the tables it describes.
const HEADER_WORDS: u64 = 14;
/// Meta-data revisions written by Qt 5's `moc`.
const REVISIONS: std::ops::RangeInclusive<u32> = 6..=9;

/// One `QObject` subclass as `moc` describes it.
#[derive(Debug, Clone, Default)]
pub struct QtClass {
    /// The class name the string table opens with.
    pub name: String,
    /// The base class, when its meta-object is in this image too.
    pub parent: Option<String>,
    /// Signals, slots and invocable methods in index order.
    pub methods: Vec<QtMethod>,
    /// Property names in index order.
    pub properties: Vec<String>,
    /// Entry of `qt_static_metacall`, the dispatcher, when it is a function.
    pub metacall: Option<u64>,
    /// Address of the class's `staticMetaObject`, the record `metaObject()`
    /// returns and `tr()` and `qt_metacast` are handed.
    pub meta_object: u64,
}

/// One entry of a class's method table.
#[derive(Debug, Clone)]
pub struct QtMethod {
    /// The method's name.
    pub name: String,
    /// What the method is, from the flags.
    pub kind: QtMethodKind,
    /// The function the dispatcher calls for it, when found.
    pub entry: Option<u64>,
}

/// What a method-table entry declares, from its flags' method-type bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QtMethodKind {
    /// A signal (`MethodSignal`).
    Signal,
    /// A slot (`MethodSlot`).
    Slot,
    /// A `Q_INVOKABLE` method that is neither (`MethodMethod`).
    Method,
    /// A `Q_INVOKABLE` constructor (`MethodConstructor`).
    Constructor,
}

impl QtMethodKind {
    /// Every kind, in the order a class's listing groups them.
    pub const ALL: [QtMethodKind; 4] = [
        QtMethodKind::Signal,
        QtMethodKind::Slot,
        QtMethodKind::Method,
        QtMethodKind::Constructor,
    ];

    /// Returns the word a listing prints for the kind: `signal`, `slot`,
    /// `method` or `constructor`.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            QtMethodKind::Signal => "signal",
            QtMethodKind::Slot => "slot",
            QtMethodKind::Method => "method",
            QtMethodKind::Constructor => "constructor",
        }
    }
}

/// Reads every class `moc` described and names the functions it maps.
///
/// The string-table walk covers each data section's bytes as the file
/// holds them, never the size its header states: a damaged header states
/// sizes no file holds, and a walk of those reads nothing for hours.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Functions, classes and references, updated in place.
pub(super) fn infer(program: &Program, analysis: &mut Analysis) {
    let Some(bitness) = program.arch.bitness() else {
        return;
    };
    let word = pointer_size(program);
    let mut tables: Vec<(u64, Vec<String>)> = Vec::new();
    for s in &program.sections {
        if s.executable {
            continue;
        }
        let Some(held) = program.section_bytes(s).filter(|b| b.len() >= 16) else {
            continue;
        };
        let end = s.va.saturating_add(from_usize(held.len()));
        let mut va = s.va;
        while va.saturating_add(16) <= end {
            match string_table(program, va, word) {
                Some(names) => {
                    let span = names.len() as u64 * entry_size(word);
                    tables.push((va, names));
                    va += span;
                }
                None => va += 4,
            }
        }
    }
    let by_table: BTreeMap<u64, usize> = tables
        .iter()
        .enumerate()
        .map(|(i, (a, _))| (*a, i))
        .collect();
    let mut classes: Vec<QtClass> = Vec::new();
    let mut renames: BTreeMap<u64, String> = BTreeMap::new();
    for (table, names) in &tables {
        let Some(meta) = meta_object(program, analysis, *table, word) else {
            continue;
        };
        let Some(class) = names.first().filter(|n| is_identifier(n)).cloned() else {
            continue;
        };
        let data = read_word(program, meta + 2 * word).unwrap_or(0);
        let Some((mut methods, properties)) = meta_data(program, data, names) else {
            continue;
        };
        let metacall =
            read_word(program, meta + 3 * word).filter(|m| analysis.function(*m).is_some());
        if let Some(entry) = metacall {
            let callees =
                dispatch_targets(program, analysis, bitness, entry, &class, methods.len());
            for (m, callee) in methods.iter_mut().zip(callees) {
                m.entry = callee;
                if let Some(e) = callee {
                    renames
                        .entry(e)
                        .or_insert_with(|| format!("{class}::{}", m.name));
                }
            }
        }
        let parent = read_word(program, meta)
            .and_then(|sup| read_word(program, sup + word))
            .and_then(|t| by_table.get(&t))
            .and_then(|i| tables.get(*i))
            .and_then(|(_, n)| n.first().cloned());
        classes.push(QtClass {
            name: class,
            parent,
            methods,
            properties,
            metacall,
            meta_object: meta,
        });
    }
    // INVARIANT: a QObject's first three virtuals are `metaObject`,
    // `qt_metacast` and `qt_metacall`, in that order, in every Qt 5 build;
    // a class's table is trusted to have that layout only when the
    // function in its first slot is the one returning the class's own
    // meta-object.
    for class in &classes {
        let Some(info) = analysis.classes.by_name.get(&class.name) else {
            continue;
        };
        let Some(&first) = info.slots.first() else {
            continue;
        };
        if !analysis
            .xrefs_to(class.meta_object)
            .iter()
            .any(|s| s.from_entry == Some(first))
        {
            continue;
        }
        for (k, method) in QOBJECT_VIRTUALS.iter().enumerate() {
            if let Some(&f) = info.slots.get(k) {
                renames
                    .entry(f)
                    .or_insert_with(|| format!("{}::{method}", class.name));
            }
        }
    }
    for f in &analysis.functions {
        if f.blocks.len() != 1 || f.instr_count > LAMBDA_INSTRS_MAX {
            continue;
        }
        if let Some(name) = literal_lambda(program, bitness, f.entry) {
            renames.entry(f.entry).or_insert(name);
        }
    }
    let mut taken: BTreeSet<String> = analysis
        .functions
        .iter()
        .filter(|f| !f.name_inferred)
        .filter_map(|f| f.name.clone())
        .collect();
    for f in &mut analysis.functions {
        let Some(base) = renames.get(&f.entry) else {
            continue;
        };
        // INVARIANT: a name `moc` wrote beats one the vtable pass inferred
        // (`Class::vfunc_11`), and never a symbol the program carries.
        if f.name.is_some() && !f.name_inferred {
            continue;
        }
        f.name = Some(unique_name(&mut taken, base));
        f.name_inferred = true;
        f.name_source = NameSource::Qt;
    }
    classes.sort_by(|l, r| l.name.cmp(&r.name));
    analysis.qt = classes;
}

/// Size of one `QByteArrayData` header for the word width.
///
/// # Arguments
///
/// * `word` - Pointer width in bytes.
fn entry_size(word: u64) -> u64 {
    if word == 8 { 24 } else { 16 }
}

/// Reads a string table at `va`: consecutive headers whose strings start
/// right after the last of them.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The candidate's first header.
/// * `word` - Pointer width in bytes.
///
/// # Returns
///
/// The strings in header order, or `None` when the shape does not hold.
fn string_table(program: &Program, va: u64, word: u64) -> Option<Vec<String>> {
    let size = entry_size(word);
    let mut names = Vec::new();
    let mut at = va;
    while names.len() < ENTRIES_MAX {
        let Some((len, offset)) = header(program, at, word) else {
            break;
        };
        let text = program.read_va(at + offset, len as usize + 1)?;
        if text.last() != Some(&0)
            || text[..len as usize]
                .iter()
                .any(|b| *b == 0 || (*b < 0x20 && *b != b'\t'))
        {
            break;
        }
        names.push(String::from_utf8_lossy(&text[..len as usize]).into_owned());
        at += size;
    }
    let (Some(first), Some((_, first_offset))) = (names.first(), header(program, va, word)) else {
        return None;
    };
    // INVARIANT: the class name comes first and the strings begin where the
    // headers end, which is what tells a table from two stray headers. A
    // class with nothing to declare has a table of its name alone, which
    // only the meta-object that points at it tells from a lone literal.
    (is_identifier(first) && first_offset == names.len() as u64 * size).then_some(names)
}

/// Reads one `QByteArrayData` header.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - The header's address.
/// * `word` - Pointer width in bytes.
///
/// # Returns
///
/// `(length, offset)` when the reference count is -1, the allocation zero
/// and the length and offset plausible.
fn header(program: &Program, at: u64, word: u64) -> Option<(u32, u64)> {
    let ref_count = read_u32(program, at)?;
    let len = read_u32(program, at + 4)?;
    let alloc = read_u32(program, at + 8)?;
    let offset = if word == 8 {
        read_word(program, at + 16)?
    } else {
        u64::from(read_u32(program, at + 12)?)
    };
    (ref_count == 0xffff_ffff && alloc == 0 && len < STRING_MAX && offset > 0 && offset < 1 << 20)
        .then_some((len, offset))
}

/// Finds the `QMetaObject` whose string-data field points at a table.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The reference index.
/// * `table` - The string table's address.
/// * `word` - Pointer width in bytes.
///
/// # Returns
///
/// The meta-object's address: the record one word before the pointer,
/// whose data field leads to a table with a `moc` revision.
fn meta_object(program: &Program, analysis: &Analysis, table: u64, word: u64) -> Option<u64> {
    analysis
        .xrefs_to(table)
        .iter()
        .filter(|s| s.kind == RefKind::Ptr)
        .filter_map(|s| s.va.checked_sub(word))
        .find(|meta| {
            read_word(program, meta + 2 * word)
                .and_then(|data| read_u32(program, data))
                .is_some_and(|rev| REVISIONS.contains(&rev))
        })
}

/// Reads the method and property tables of a meta-data array.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `data` - The array's address.
/// * `names` - The class's string table.
///
/// # Returns
///
/// The methods in index order and the property names, or `None` when the
/// counts are not plausible.
fn meta_data(
    program: &Program,
    data: u64,
    names: &[String],
) -> Option<(Vec<QtMethod>, Vec<String>)> {
    let at = |k: u64| read_u32(program, data + 4 * k);
    let methods = at(4)?;
    let methods_at = u64::from(at(5)?);
    let properties = at(6)?;
    let properties_at = u64::from(at(7)?);
    // INVARIANT: a class with no methods has no method table and an offset
    // of zero for it; the offset is checked only when there is something
    // at it.
    if methods > METHODS_MAX
        || properties > METHODS_MAX
        || (methods > 0 && methods_at < HEADER_WORDS)
    {
        return None;
    }
    let name = |idx: u32| names.get(idx as usize).cloned();
    let mut out = Vec::new();
    for i in 0..u64::from(methods) {
        let row = methods_at + 5 * i;
        let kind = match at(row + 4)? & 0x0c {
            0x04 => QtMethodKind::Signal,
            0x08 => QtMethodKind::Slot,
            0x0c => QtMethodKind::Constructor,
            _ => QtMethodKind::Method,
        };
        out.push(QtMethod {
            name: name(at(row)?)?,
            kind,
            entry: None,
        });
    }
    let mut props = Vec::new();
    for i in 0..u64::from(properties) {
        props.push(name(at(properties_at + 3 * i)?)?);
    }
    Some((out, props))
}

/// Lists what a dispatcher calls, one entry per method index.
///
/// `moc` writes `switch (_id)` for the `InvokeMetaMethod` command, and the
/// compiler keeps it as a jump table when there are enough cases: the
/// first table in the function with a case per method is that switch, and
/// case `i` leads to the block that calls method `i`. With too few cases
/// for a table the compiler writes a compare ladder, whose cases it lays
/// out in an order of its own; the calls are then read in address order
/// and trusted only when there is exactly one per method, since a wrong
/// name is worse than none. A call to a frame helper is the dispatcher's
/// own prologue, not a method.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Functions, classes and jump tables.
/// * `bitness` - Decoder bitness.
/// * `entry` - The dispatcher's entry.
/// * `class` - The class, whose vtable resolves a slot call.
/// * `count` - How many methods the class declares.
///
/// # Returns
///
/// The entry each call reaches: a near target as itself, a call through
/// `[reg+K]` as slot `K/word` of the class's vtable, an unresolved call as
/// `None` so the indices stay aligned; empty when nothing lines up.
fn dispatch_targets(
    program: &Program,
    analysis: &Analysis,
    bitness: u32,
    entry: u64,
    class: &str,
    count: usize,
) -> Vec<Option<u64>> {
    let Some(f) = analysis.function(entry) else {
        return Vec::new();
    };
    let table = analysis
        .jump_tables
        .iter()
        .find(|(site, targets)| {
            targets.len() >= count && f.blocks.iter().any(|b| **site >= b.start && **site < b.end)
        })
        .map(|(_, targets)| targets);
    match table {
        Some(targets) => targets
            .iter()
            .take(count)
            .map(|t| first_call(program, analysis, bitness, f, *t, class))
            .collect(),
        None => {
            let cases = ladder_targets(program, analysis, bitness, f, class, count);
            if cases.iter().any(Option::is_some) {
                return cases;
            }
            let calls: Vec<Option<u64>> = f
                .blocks
                .iter()
                .flat_map(|b| calls_in(program, analysis, bitness, f.entry, b.start, b.end, class))
                .collect();
            if calls.len() == count {
                calls
            } else {
                Vec::new()
            }
        }
    }
}

/// Follows the compare ladder a small `switch (_id)` compiles to.
///
/// The index is loaded from the third argument (`[ebp+10h]` behind a
/// frame, `[esp+0Ch]` without one) and then counted down: `sub eax, k`
/// and `dec eax` raise the case the next `je` selects, a `jne` past the
/// last compare leaves the fall-through as the case after it, and the
/// order the compiler laid the case blocks out in no longer matters.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Functions and classes.
/// * `bitness` - Decoder bitness.
/// * `f` - The dispatcher.
/// * `class` - The class, whose vtable resolves a slot call.
/// * `count` - How many methods the class declares.
///
/// # Returns
///
/// One entry per method index, `None` where the ladder names no case;
/// all `None` when no ladder is found.
fn ladder_targets(
    program: &Program,
    analysis: &Analysis,
    bitness: u32,
    f: &super::Function,
    class: &str,
    count: usize,
) -> Vec<Option<u64>> {
    let mut cases: Vec<Option<u64>> = vec![None; count];
    let loads_index = |i: &crate::isa::x86::Instruction| {
        i.mnemonic() == Mnemonic::Mov
            && i.op0_kind() == OpKind::Register
            && i.op1_kind() == OpKind::Memory
            && i.memory_index() == Register::None
            && matches!(
                (i.memory_base(), crate::disasm::displacement(i, bitness)),
                (Register::EBP, 0x10) | (Register::ESP, 0xc)
            )
    };
    let Some(start) = f.blocks.iter().position(|b| {
        let mut va = b.start;
        while va < b.end {
            let Some(i) = super::functions::decode_at(program, bitness, va) else {
                break;
            };
            if loads_index(&i) {
                return true;
            }
            va = i.next_ip();
        }
        false
    }) else {
        return cases;
    };
    let mut reg = None;
    let mut index: i64 = 0;
    let record = |case: i64, target: u64, cases: &mut Vec<Option<u64>>| {
        if let Some(slot) = usize::try_from(case).ok().and_then(|c| cases.get_mut(c)) {
            *slot = first_call(program, analysis, bitness, f, target, class);
        }
    };
    'blocks: for b in &f.blocks[start..] {
        let mut va = b.start;
        while va < b.end {
            let Some(i) = super::functions::decode_at(program, bitness, va) else {
                break 'blocks;
            };
            va = i.next_ip();
            if reg.is_none() {
                if loads_index(&i) {
                    reg = Some(i.op0_register());
                }
                continue;
            }
            let on_reg = i.op0_kind() == OpKind::Register && Some(i.op0_register()) == reg;
            match i.mnemonic() {
                Mnemonic::Sub if on_reg => {
                    index += match i.op1_kind() {
                        OpKind::Register => 0,
                        _ => i64::try_from(i.immediate(1)).unwrap_or(0),
                    };
                }
                Mnemonic::Dec if on_reg => index += 1,
                Mnemonic::Cmp | Mnemonic::Test if on_reg => {}
                Mnemonic::Je => record(index, i.near_branch_target(), &mut cases),
                Mnemonic::Jne => {
                    record(index, va, &mut cases);
                    break 'blocks;
                }
                Mnemonic::Jmp | Mnemonic::Ret => break 'blocks,
                _ => {}
            }
        }
    }
    cases
}

/// Finds the first method call a case block reaches, following the
/// fall-through into the next block once.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Functions and classes.
/// * `bitness` - Decoder bitness.
/// * `f` - The dispatcher.
/// * `start` - The case's first instruction.
/// * `class` - The class, whose vtable resolves a slot call.
fn first_call(
    program: &Program,
    analysis: &Analysis,
    bitness: u32,
    f: &super::Function,
    start: u64,
    class: &str,
) -> Option<u64> {
    let mut at = start;
    for _ in 0..2 {
        let b = f.blocks.iter().find(|b| b.start == at)?;
        if let Some(call) = calls_in(program, analysis, bitness, f.entry, b.start, b.end, class)
            .into_iter()
            .next()
        {
            return call;
        }
        // INVARIANT: only a block that runs on into the next one is followed
        // there; past a jump or a return the next block is another case's.
        if !matches!(
            b.term,
            super::BlockTerm::Fall | super::BlockTerm::Cond | super::BlockTerm::Call
        ) {
            return None;
        }
        at = b.end;
    }
    None
}

/// Lists the method calls in one run of instructions, in address order.
///
/// A method is reached by a near call, by a tail jump to another
/// function, or through the class's vtable: `call [eax+2Ch]`, `jmp dword
/// [eax+2Ch]`, or `mov eax,[eax+2Ch]; call eax`, which all name slot 11.
/// A call through a register loaded from anything else, an import slot
/// say, is not a method and adds no entry.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Functions and classes.
/// * `bitness` - Decoder bitness.
/// * `own` - The dispatcher's entry, so a jump within it is not a call.
/// * `start` - First address.
/// * `end` - End of the run (exclusive).
/// * `class` - The class, whose vtable resolves a slot call.
///
/// # Returns
///
/// One entry per method call that is not a frame helper's: the function
/// reached, or `None` when it could not be resolved.
fn calls_in(
    program: &Program,
    analysis: &Analysis,
    bitness: u32,
    own: u64,
    start: u64,
    end: u64,
    class: &str,
) -> Vec<Option<u64>> {
    let word = i64::from(bitness / 8);
    let slots = analysis
        .classes
        .by_name
        .get(class)
        .map_or(&[][..], |c| c.slots.as_slice());
    let overlay = super::Overlay::default();
    // INVARIANT: the offset each register was last loaded from through a
    // base register names the slot: `mov eax,[eax+2Ch]; call eax` calls
    // slot 11 as `call [eax+2Ch]` does.
    let mut loads: BTreeMap<Register, i64> = BTreeMap::new();
    // INVARIANT: a slot holding an import thunk (`_purecall` in a pure
    // virtual's slot) names no method of this image.
    let own_code = |e: u64| analysis.function(e).is_some_and(|g| g.thunk.is_none());
    let slot_of = |k: i64| {
        (k >= 0 && k % word == 0)
            .then(|| usize::try_from(k / word).ok())
            .flatten()
            .and_then(|s| slots.get(s).copied())
            .filter(|e| own_code(*e))
    };
    let mut out = Vec::new();
    let mut va = start;
    while va < end {
        let Some(i) = super::functions::decode_at(program, bitness, va) else {
            break;
        };
        va = i.next_ip();
        let through_memory = i.op1_kind() == OpKind::Memory
            && i.memory_base() != Register::None
            && i.memory_index() == Register::None;
        if i.mnemonic() == Mnemonic::Mov && i.op0_kind() == OpKind::Register {
            if through_memory {
                loads.insert(i.op0_register(), crate::disasm::displacement(&i, bitness));
            } else {
                loads.remove(&i.op0_register());
            }
        }
        match i.flow_control() {
            FlowControl::Call => {
                if super::render::frame_helper(analysis, &overlay, &i) {
                    continue;
                }
                let t = i.near_branch_target();
                out.push(
                    analysis
                        .function(t)
                        .map(|g| g.entry)
                        .filter(|e| own_code(*e)),
                );
            }
            FlowControl::UnconditionalBranch => {
                if let Some(g) = analysis
                    .function(i.near_branch_target())
                    .filter(|g| g.entry != own)
                {
                    out.push(Some(g.entry).filter(|e| own_code(*e)));
                }
            }
            FlowControl::IndirectCall | FlowControl::IndirectBranch => match i.op0_kind() {
                OpKind::Memory
                    if i.memory_base() != Register::None && i.memory_index() == Register::None =>
                {
                    out.push(slot_of(crate::disasm::displacement(&i, bitness)));
                }
                OpKind::Register => {
                    if let Some(k) = loads.get(&i.op0_register()) {
                        out.push(slot_of(*k));
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    out
}

/// Tells whether a string is a C++ identifier, possibly qualified.
///
/// # Arguments
///
/// * `s` - The string.
fn is_identifier(s: &str) -> bool {
    !s.is_empty()
        && !s.starts_with(|c: char| c.is_ascii_digit())
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == ':')
}

/// Renders the static data behind a `QStringLiteral` or `QByteArrayLiteral`.
///
/// Both macros lay a `QArrayData` header with reference count -1, no
/// allocation and an offset equal to the header's own size right before
/// the text, and code that builds the string stores the header's address
/// as the `d` pointer; a constant pointing at such a header reads better
/// as the literal than as the address of its data.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - The header's address.
///
/// # Returns
///
/// `QStringLiteral("…")` for UTF-16 text, `QByteArrayLiteral("…")` for
/// bytes, or `None` when no such header is there or what follows is not
/// text.
pub(crate) fn literal(program: &Program, at: u64) -> Option<String> {
    let (kind, text) = literal_parts(program, at)?;
    Some(format!(
        "{kind}(\"{}\")",
        crate::strings::escape_text(&text)
    ))
}

/// Reads the macro and text behind a Qt literal's static data.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - The header's address.
///
/// # Returns
///
/// `("QStringLiteral", text)` for UTF-16 text and `("QByteArrayLiteral",
/// text)` for bytes, the text cut at a reading length, or `None` when no
/// such header is there or what follows is not text.
fn literal_parts(program: &Program, at: u64) -> Option<(&'static str, String)> {
    /// Longest text rendered.
    const CAP: usize = 120;
    if program.section_at(at)?.executable {
        return None;
    }
    let word = pointer_size(program);
    let (len, offset) = header(program, at, word)?;
    if offset != if word == 8 { 24 } else { 16 } {
        return None;
    }
    let len = usize::try_from(len).ok()?;
    let text = at.checked_add(offset)?;
    let printable = |c: u32| (0x20..0x7f).contains(&c) || matches!(c, 9 | 10 | 13);
    let quoted = |kind: &'static str, chars: &mut dyn Iterator<Item = char>| {
        (kind, chars.take(CAP).collect::<String>())
    };
    let wide = program
        .read_va(text, len.checked_mul(2)?.checked_add(2)?)
        .and_then(|bytes| {
            bytes
                .chunks_exact(2)
                .map(|pair| pair.try_into().map(u16::from_le_bytes))
                .collect::<Result<Vec<u16>, _>>()
                .ok()
        });
    // INVARIANT: ASCII in UTF-16 is unmistakable, every other byte zero,
    // and is tried first; a run of bytes ending in a zero is then the byte
    // array it says it is, printable or not, so that text in some other
    // encoding is never read as pairs.
    if let Some(units) = &wide
        && let Some((&0, body)) = units.split_last()
        && body.iter().all(|&u| printable(u32::from(u)))
    {
        return Some(quoted(
            "QStringLiteral",
            &mut body.iter().filter_map(|&u| char::from_u32(u32::from(u))),
        ));
    }
    if let Some(bytes) = program.read_va(text, len.checked_add(1)?)
        && let Some((&0, body)) = bytes.split_last()
    {
        return body.iter().all(|&b| printable(u32::from(b))).then(|| {
            quoted(
                "QByteArrayLiteral",
                &mut body.iter().map(|&b| char::from(b)),
            )
        });
    }
    let units = wide?;
    let (&0, body) = units.split_last()? else {
        return None;
    };
    let chars: Option<Vec<char>> = body
        .iter()
        .map(|&u| char::from_u32(u32::from(u)).filter(|c| !c.is_control()))
        .collect();
    Some(quoted("QStringLiteral", &mut chars?.into_iter()))
}

/// Names the lambda a `QStringLiteral` or `QByteArrayLiteral` expands to.
///
/// The macro's lambda builds the string in the object it is handed, and
/// stores the literal's static data as the `d` pointer, `mov dword [eax],
/// offset data`, in a body of one block and a dozen instructions at most.
/// A function of that shape is named after the macro and the text, so a
/// caller reads `QStringLiteral_about_blank(&local_14)` where it read
/// `sub_40edc6`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// `QStringLiteral_<text>` or `QByteArrayLiteral_<text>`, the text made an
/// identifier, or `None` when the function makes no such store before
/// its flow leaves the straight line.
fn literal_lambda(program: &Program, bitness: u32, entry: u64) -> Option<String> {
    let mut va = entry;
    let mut found = None;
    for _ in 0..LAMBDA_INSTRS_MAX {
        let i = super::functions::decode_at(program, bitness, va)?;
        if i.mnemonic() == Mnemonic::Mov
            && i.op0_kind() == OpKind::Memory
            && i.memory_base() != Register::None
            && i.memory_index() == Register::None
            && i.memory_displacement64() == 0
            && matches!(i.op1_kind(), OpKind::Immediate32 | OpKind::Immediate32to64)
            && let Some(parts) = literal_parts(program, i.immediate(1))
        {
            found = Some(parts);
            break;
        }
        if i.flow_control() != FlowControl::Next {
            return None;
        }
        va = i.next_ip();
    }
    let (kind, text) = found?;
    let mut ident = String::new();
    for c in text.chars().take(LAMBDA_NAME_MAX) {
        if c.is_ascii_alphanumeric() {
            ident.push(c);
        } else if !ident.ends_with('_') {
            ident.push('_');
        }
    }
    let ident = ident.trim_matches('_');
    Some(if ident.is_empty() {
        format!("{kind}_empty")
    } else {
        format!("{kind}_{ident}")
    })
}
