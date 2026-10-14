//! Classes, vtables and the class hierarchy recovered from constructors.
//!
//! Without RTTI (this client keeps 164 type descriptors for 81,014
//! functions) the constructors and destructors named from their assert
//! signatures tell what RTTI would: the pointer a constructor stores at
//! `[this]` once the base constructor has returned is the class's vtable,
//! the base constructor it calls first with `this` names the parent (the
//! class of the table that constructor stores last) unless the class's
//! descriptor names one ([`super::descriptors`]), which is exact where a
//! store the compiler kept may be a grandparent's, and every other
//! function storing that table, and no other, at `[this]` is a constructor
//! or destructor of the same class, which names it. A function storing two
//! tables has its base's constructor (or destructor) inlined: a derived
//! table is longer than its base's, so the longer is its own class's and
//! the shorter the parent's, whichever order they are stored in; equal
//! lengths leave both unknown; more tables in strictly growing or shrinking
//! order name the longest as the class's own and the next as its parent's.
//! A function that constructs an instance in place, storing the tables
//! through the allocation it just made rather than through `this`, stores
//! a class's tables like a constructor does; when it references exactly
//! the descriptor of that class it is the class's factory, its `create`.
//! The vtable's slots, read
//! until a word that is not code
//! or the start of another referenced table, are the class's virtual
//! methods; a word of data between them does not end the table when the
//! methods visibly resume after it, and the datum keeps its slot, so the
//! methods after it stay at the indexes their byte offsets give them. A table no named constructor stores is named by the methods it
//! introduces: a method already in the table the class's base constructor
//! stores is inherited; one introduced by several unrelated tables belongs
//! to the shortest (derived tables are at least as long) or, on a tie, votes
//! nowhere; when every introduced named method of a table shares a class,
//! the table is that class's. A table that stays unnamed but that some
//! function stores at `[this]`, alone or as the base's before its own, is
//! still a class, named after the
//! class descriptor its creators allocate from ([`super::descriptors`]) or
//! `class_<table address>`, so its constructors, methods, parent and slots
//! get everything a named class gets. Virtual method names travel along the slot
//! index through the hierarchy: a named override names the unnamed function
//! its ancestors hold in that slot, and a named ancestor method names an
//! unnamed override. A method passing its own `this` to an undeclared
//! function types that function's parameter with its class, which the
//! decompiler shows in the header and uses for virtual calls; a call
//! result or a field of `this` passed as another method's `this` types that
//! result or field the same way ([`value_hints`]). A function held in a
//! class's vtable is a method of that class, which types its first
//! parameter as well. Every class a parameter is shown to hold by what is
//! handed in (a caller's `this`, a caller's own parameter of a known class,
//! the tables holding the function, a singleton's slot) votes, and the
//! parameter is the nearest common ancestor of the votes, or nothing when
//! they have none; a parameter nothing is handed in for takes the most
//! derived of the classes the callees it hands it on to accept there, or
//! nothing when two of those lie on separate lines. A function typed that
//! way passes its own `this` on in the next round, and each round types
//! every parameter afresh from all the evidence, so a vote a later round
//! finds widens or withdraws a class an earlier round chose rather than
//! losing to it. A constructor
//! storing `this` into the module's TLS block (`gs:[0x58]`, indexed by
//! `_tls_index`) registers a singleton: that slot holds the class, a word
//! loaded from it passed to a callee types the callee's parameter, and a
//! function returning it is a getter whose result has that class. A
//! constructor storing `this` into a global registers a global singleton
//! the same way.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::isa::x86::{
    Decoder, DecoderOptions, FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess,
    OpKind, Register,
};

use super::classes::class_of;
use super::descriptors::unanimous;
use super::functions::{decode_block, string_at};
use super::naming::in_data;
use super::{
    Analysis, Function, NameSource, RefKind, is_executable_va, read_word, single, striped,
    striped_with, unique_name,
};
use crate::fxmap::FxHashMap;
use crate::program::{BinaryFormat, Program};

/// Most slots read from one vtable.
const SLOTS_MAX: usize = 1024;
/// Fewest slots a table named by its slots alone must have (a single code
/// pointer is a callback variable, not a vtable).
const SLOTS_MIN: usize = 2;
/// Base-constructor links followed when asking whether a table inherits a method.
const ANCESTORS_MAX: usize = 16;
/// Most words of data one table's slots are read across.
///
/// A non-zero word of data between a table's methods (an offset or an id
/// the class keeps beside them) is skipped while the table visibly
/// resumes; a zero is not — it is the padding a linker leaves between
/// tables, the common end of one — and a table that needs more skips
/// than this to stay readable is data that only looks like a table of
/// functions, and the reading ends.
const DATA_SLOTS_MAX: usize = 8;
/// Most rounds of parameter hinting: a hinted function's own `this` calls
/// vote in the next round, which types every parameter again from all its
/// votes, until no class changes.
const HINT_ROUNDS: usize = 8;
/// Links of a chain of functions handing an argument on untouched followed
/// when asking whether the last one reads it ([`read_counts`]).
const READ_LINKS_MAX: usize = 4;
/// Rounds of return summaries: creator, its storing caller, the global's
/// or field's getter, the getter's wrapper, one more.
const SUMMARY_ROUNDS: usize = 5;
/// Most instructions of a prologue read for the homing of a variable
/// argument list, as many as the decompiler's prologue scan reads.
const PROLOGUE_MAX: usize = 64;
/// Fewest classes worth a worker each when a protocol table is built.
const SLOT_ROWS_MIN: usize = 8;
/// Registers a call may change under the Microsoft x64 convention.
const MS_VOLATILE: [Register; 7] = [
    Register::RAX,
    Register::RCX,
    Register::RDX,
    Register::R8,
    Register::R9,
    Register::R10,
    Register::R11,
];
/// Registers a call may change under the System V x64 convention.
const SYSV_VOLATILE: [Register; 9] = [
    Register::RAX,
    Register::RCX,
    Register::RDX,
    Register::RSI,
    Register::RDI,
    Register::R8,
    Register::R9,
    Register::R10,
    Register::R11,
];
/// Registers a call may change in 32-bit code.
const X86_VOLATILE: [Register; 3] = [Register::EAX, Register::ECX, Register::EDX];
/// Argument registers of the Microsoft x64 convention.
const MS_ARGS: [Register; 4] = [Register::RCX, Register::RDX, Register::R8, Register::R9];
/// Argument registers of the System V x64 convention.
const SYSV_ARGS: [Register; 6] = [
    Register::RDI,
    Register::RSI,
    Register::RDX,
    Register::RCX,
    Register::R8,
    Register::R9,
];
/// Argument registers of 32-bit code: `ecx`, where a `thiscall` method
/// takes `this`; the other arguments travel on the stack.
const X86_ARGS: [Register; 1] = [Register::ECX];

/// The registers of the calling convention, as the scans read them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Conv {
    /// The register `this` arrives in.
    this: Register,
    /// The registers a call may change.
    volatile: &'static [Register],
    /// The argument registers, in order.
    args: &'static [Register],
}

/// What the constructors of one class tell about it.
#[derive(Debug, Clone, Default)]
pub struct ClassInfo {
    /// Qualified class name.
    pub name: String,
    /// Address of the primary vtable (the pointer stored at `[this]`);
    /// `None` for a class known only from its descriptor.
    pub vtable: Option<u64>,
    /// The vtable's slots: the entry each virtual method's word holds,
    /// `0` where the word is data the reading skipped, so a method's
    /// index is the byte offset of its word divided by the word size.
    pub slots: Vec<u64>,
    /// The class whose constructor a constructor calls first with `this`.
    pub parent: Option<String>,
    /// Constructors and destructors: every function storing the vtable at
    /// `[this]`, sorted.
    pub ctors: Vec<u64>,
    /// Factories constructing an instance in place in the allocation they
    /// just made from the class's descriptor (`Create`), sorted.
    pub creators: Vec<u64>,
}

/// A value a register holds during a scan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tracked {
    /// A data address loaded with `lea` or an immediate (a table candidate).
    Table(u64),
    /// The result of a direct call to this entry.
    Result(u64),
    /// The word loaded from this offset of `this`.
    Field(u64),
    /// The address of this offset of `this` (an embedded object).
    FieldAddr(u64),
    /// The thread's TLS array (`gs:[0x58]`).
    TlsArray,
    /// This module's TLS block (the array indexed by `_tls_index`).
    TlsBlock,
    /// The word loaded from this offset of the TLS block (a singleton).
    TlsSlot(u64),
    /// A constant loaded with an immediate (an offset hoisted into a register).
    Const(u64),
    /// The value an argument register still holds from the call that
    /// entered the function: parameter `n`.
    Param(u8),
    /// The word loaded from this data address (a global).
    Global(u64),
    /// An address in the function's own frame (a local), by its offset from
    /// the stack pointer the frame is addressed from.
    Frame(u64),
    /// The word or vector loaded from this offset of what parameter `n`
    /// points at: part of a copy of that object.
    Copied(u8, u64),
}

/// What one function does with `this` and the tables it points at.
#[derive(Debug, Clone, Default)]
struct Scan {
    /// Table addresses stored at `[this]`, in instruction order.
    stores: Vec<u64>,
    /// Table addresses stored at `[r]` where `r` holds a call's result (a
    /// creator constructing the instance it allocated), in instruction
    /// order.
    result_stores: Vec<u64>,
    /// Table addresses stored into the frame (an object constructed on the
    /// stack), in instruction order.
    local_stores: Vec<u64>,
    /// Locals handed to a callee by a call: the callee, the position, the
    /// local's offset in the frame and the block of the call.
    frame_args: Vec<(u64, u8, u64, u64)>,
    /// Locals filled with a copy of what a parameter points at: the local's
    /// offset in the frame, the parameter and the block of the copy.
    frame_copies: Vec<(u64, u8, u64)>,
    /// Target of the first direct call made with `this` in the argument
    /// register before any store (the base constructor).
    first_this_call: Option<u64>,
    /// Direct calls made with `this` in an argument register, with the
    /// argument's position.
    this_calls: Vec<(u64, u8)>,
    /// Direct calls made with a call result or a field of `this` in an
    /// argument register: target, position and the value.
    calls: Vec<(u64, u8, Tracked)>,
    /// Tail jumps made with `this` in an argument register, as
    /// [`Scan::this_calls`] has them, until [`settle_tails`] keeps the ones
    /// whose target reads that register.
    tail_this_calls: Vec<(u64, u8)>,
    /// Tail jumps made with a tracked value in an argument register, as
    /// [`Scan::calls`] has them, until [`settle_tails`] keeps the ones whose
    /// target reads that register.
    tail_calls: Vec<(u64, u8, Tracked)>,
    /// Direct calls and tail jumps made with a data address in an argument
    /// register the call's own block loaded it into: target, position and
    /// the address. The scan reads the blocks in address order, so a value
    /// an earlier block left in a register may be another path's.
    data_args: Vec<(u64, u8, u64)>,
    /// TLS block offsets `this` was stored at (a singleton registering).
    tls_stores: Vec<u64>,
    /// The TLS block offset whose word a `ret` hands back (a singleton getter).
    returns_tls: Option<u64>,
    /// Data addresses `this` was stored at (a global singleton registering).
    global_stores: Vec<u64>,
    /// Data addresses a call result was stored at, with the callee.
    global_result_stores: Vec<(u64, u64)>,
    /// Offsets of `this` a call result was stored at, with the callee.
    field_result_stores: Vec<(u64, u64)>,
    /// Tables stored at `[this+off]` with a nonzero `off` (an embedded base
    /// subobject the constructor initializes in place), as `(offset, table)`
    /// in instruction order.
    field_stores: Vec<(u64, u64)>,
    /// The callee whose result a `ret` hands back (a creator or a wrapper).
    returns_result: Option<u64>,
    /// The data address whose word a `ret` hands back (a global getter).
    returns_global: Option<u64>,
    /// The offset of `this` whose word a `ret` hands back (a field getter).
    returns_field: Option<u64>,
    /// One past the highest argument register position read before being
    /// written (how many arguments the function itself uses), on some path
    /// from the entry ([`entry_reads`]).
    args_read: usize,
    /// How many arguments are fixed when the function takes a variable
    /// list ([`super::decompile::lift::vararg_fixed`]); the rest are no
    /// typed slots.
    vararg_fixed: Option<usize>,
}

/// Fills the class tables (`analysis.classes`) from the named
/// constructors and destructors, names the unnamed ones, and hints the
/// parameter classes of functions called with a method's `this`.
///
/// # Arguments
///
/// * `program` - The image the tables are read from.
/// * `analysis` - Functions, names and cross-references; classes, vtables
///   and constructor names are written in place.
pub(crate) fn infer(program: &Program, analysis: &mut Analysis) {
    let Some(bitness) = program.arch.bitness() else {
        return;
    };
    let mut phases = crate::timing::Phases::new();
    let conv = conv_of(program, bitness);
    let mut votes: BTreeMap<String, BTreeMap<u64, usize>> = BTreeMap::new();
    let mut scans: BTreeMap<u64, Scan> = BTreeMap::new();
    for f in &analysis.functions {
        let Some((class, dtor)) = f.name.as_deref().and_then(ctor_class) else {
            continue;
        };
        let scan = scan_function(program, f, bitness, &conv);
        let own = if dtor {
            scan.stores.first()
        } else {
            scan.stores.last()
        };
        if let Some(&v) = own {
            *votes
                .entry(class.to_owned())
                .or_default()
                .entry(v)
                .or_insert(0) += 1;
        }
        scans.insert(f.entry, scan);
    }
    phases.mark("vtables ctor scans");
    let mut classes: BTreeMap<String, ClassInfo> = BTreeMap::new();
    let mut vtables: BTreeMap<u64, String> = BTreeMap::new();
    for (class, by_table) in votes {
        let top = by_table.values().max().copied().unwrap_or(0);
        let vtable = single(by_table.iter().filter(|(_, n)| **n == top).map(|(v, _)| *v))
            .filter(|v| !vtables.contains_key(v));
        if let Some(v) = vtable {
            vtables.insert(v, class.clone());
        }
        classes.insert(
            class.clone(),
            ClassInfo {
                name: class,
                vtable,
                ..ClassInfo::default()
            },
        );
    }
    for info in classes.values_mut() {
        if let Some(v) = info.vtable {
            info.slots = read_slots(program, analysis, &vtables, v, bitness);
        }
    }
    let mut tables: BTreeMap<u64, Vec<u64>> = classes
        .values()
        .filter_map(|c| c.vtable.map(|v| (v, c.slots.clone())))
        .collect();
    // INVARIANT: a class with one virtual method, a destructor as a rule,
    // has a one-slot table, which a lone function pointer in data looks
    // like; it is a table once a constructor or a stack object stores it.
    let mut singles: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for &target in analysis.xrefs.keys() {
        if tables.contains_key(&target)
            || analysis.jump_tables.contains_key(&target)
            || !in_data(program, target)
        {
            continue;
        }
        let slots = read_slots(program, analysis, &vtables, target, bitness);
        if slots.len() >= SLOTS_MIN {
            tables.insert(target, slots);
        } else if !slots.is_empty() {
            singles.insert(target, slots);
        }
    }
    let referencing: BTreeSet<u64> = tables
        .keys()
        .chain(singles.keys())
        .filter_map(|t| analysis.xrefs.get(t))
        .flatten()
        .filter_map(|s| s.from_entry)
        .collect();
    phases.mark("vtables singles");
    let todo: Vec<&Function> = referencing
        .iter()
        .filter(|e| !scans.contains_key(e))
        .filter_map(|e| analysis.function(*e))
        .collect();
    scans.extend(scan_all(program, &todo, bitness, &conv));
    phases.mark("vtables referencing scans");
    let mut table_parent: BTreeMap<u64, u64> = BTreeMap::new();
    for scan in scans.values() {
        let Some((own, inline_base)) = own_and_base(&scan.stores, &tables) else {
            continue;
        };
        let Some(base) = inline_base.or_else(|| {
            let called = scans.get(&scan.first_this_call?)?;
            own_and_base(&called.stores, &tables).map(|(o, _)| o)
        }) else {
            continue;
        };
        if base != own && tables.contains_key(&base) {
            table_parent.entry(own).or_insert(base);
        }
    }
    for scan in scans.values().filter(|s| s.stores.is_empty()) {
        if let Some((own, Some(base))) = own_and_base(&scan.result_stores, &tables)
            && tables.contains_key(&base)
        {
            table_parent.entry(own).or_insert(base);
        }
    }
    let mut ctors_of: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    let mut creators_of: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for (&entry, scan) in &scans {
        if let Some((table, _)) = own_and_base(&scan.stores, &tables) {
            ctors_of.entry(table).or_default().push(entry);
        } else if scan.stores.is_empty()
            && let Some((table, _)) = own_and_base(&scan.result_stores, &tables)
        {
            creators_of.entry(table).or_default().push(entry);
        }
    }
    let on_stack: BTreeSet<u64> = scans
        .values()
        .flat_map(|s| s.local_stores.iter().copied())
        .collect();
    // INVARIANT: a one-slot table a constructor, a creator or a stack
    // object stores is promoted before the locators are read, so a class
    // with one virtual method is named by its locator as a longer table
    // is, not by its address; its methods and callers then carry the
    // compiler's own name for the class everywhere a name reaches.
    for (table, slots) in singles {
        if ctors_of.contains_key(&table)
            || creators_of.contains_key(&table)
            || on_stack.contains(&table)
        {
            tables.insert(table, slots);
        }
    }
    // INVARIANT: a locator is the compiler's own word on a table's class,
    // so it names the table before any inference from methods or
    // constructors gets a vote; the first table by address keeps a name
    // two tables share.
    for (&table, slots) in &tables {
        let Some(name) = super::rtti::class_name(program, table) else {
            continue;
        };
        if classes.contains_key(&name) {
            continue;
        }
        vtables.insert(table, name.clone());
        classes.insert(
            name.clone(),
            ClassInfo {
                name,
                vtable: Some(table),
                slots: slots.clone(),
                ..ClassInfo::default()
            },
        );
    }
    phases.mark("vtables rtti names");
    // INVARIANT: a further base's table under multiple inheritance carries
    // the class's locator with the subobject's offset; it is stored at
    // `[this+offset]`, which the scan does not follow, so it is found by the
    // immediates that name it and kept apart from the class's own table.
    let mut secondary: BTreeMap<u64, String> = BTreeMap::new();
    let stored: BTreeSet<u64> = analysis
        .xrefs
        .iter()
        .filter(|(_, sites)| sites.iter().any(|s| s.kind == RefKind::Data))
        .map(|(&target, _)| target)
        .chain(tables.keys().copied())
        .collect();
    for target in stored {
        if vtables.contains_key(&target) {
            continue;
        }
        if let Some((class, base)) = super::rtti::secondary(program, target) {
            secondary.insert(target, format!("{class}::vftable_{base}"));
            // INVARIANT: the subobject's table holds the base's own
            // virtuals, so its slots are the base's methods wherever the
            // base's primary table is, and they carry the base's class
            // into the methods' names and their callers' hints; a base
            // whose own table this image also holds keeps that one.
            let slots = tables.remove(&target);
            let info = classes.entry(base.clone()).or_insert_with(|| ClassInfo {
                name: base.clone(),
                ..ClassInfo::default()
            });
            if info.slots.is_empty() {
                info.slots = slots.unwrap_or_default();
            }
        }
    }
    classify_tables(analysis, &tables, &table_parent, &mut vtables, &mut classes);
    let descriptors = super::descriptors::find(program, analysis);
    let described = super::descriptors::objects_by_function(analysis, &descriptors.names);
    let is_ctor = |e: u64| scans.get(&e).is_some_and(|s| !s.stores.is_empty());
    let inline_bases: BTreeSet<u64> = table_parent.values().copied().collect();
    let accessed = accessed_descriptors(program, bitness, &descriptors.names, &tables);
    for (&table, slots) in &tables {
        if vtables.contains_key(&table) {
            continue;
        }
        let creators: &[u64] = creators_of.get(&table).map_or(&[], Vec::as_slice);
        let ctors: &[u64] = match ctors_of.get(&table) {
            Some(c) => c,
            None if inline_bases.contains(&table)
                || !creators.is_empty()
                || on_stack.contains(&table) =>
            {
                &[]
            }
            None => continue,
        };
        let name = super::descriptors::class_name(
            analysis,
            &descriptors.names,
            &descriptors.parents,
            &described,
            ctors,
            &is_ctor,
        )
        .or_else(|| super::descriptors::creator_name(&descriptors.names, &described, creators))
        .or_else(|| accessed.get(&table).cloned())
        .filter(|n| !classes.contains_key(n))
        .unwrap_or_else(|| format!("class_{table:x}"));
        vtables.insert(table, name.clone());
        classes.insert(
            name.clone(),
            ClassInfo {
                name,
                vtable: Some(table),
                slots: slots.clone(),
                ..ClassInfo::default()
            },
        );
    }
    let mut member: BTreeMap<u64, String> = BTreeMap::new();
    for (&entry, scan) in &scans {
        let Some(f) = analysis.function(entry) else {
            continue;
        };
        let class = match f.name.as_deref().and_then(ctor_class) {
            Some((c, _)) if classes.contains_key(c) => Some(c.to_owned()),
            Some(_) => None,
            None => own_and_base(&scan.stores, &tables).and_then(|(v, _)| vtables.get(&v).cloned()),
        };
        if let Some(c) = class {
            member.insert(entry, c);
        }
    }
    for (&entry, class) in &member {
        if let Some(info) = classes.get_mut(class) {
            info.ctors.push(entry);
        }
    }
    let mut created: BTreeMap<u64, String> = BTreeMap::new();
    for (table, creators) in &creators_of {
        let Some(class) = vtables.get(table) else {
            continue;
        };
        for &c in creators {
            let own = super::descriptors::creator_name(&descriptors.names, &described, &[c]);
            if own.as_deref() == Some(class.as_str()) {
                created.insert(c, class.clone());
            }
        }
    }
    for (&entry, class) in &created {
        if let Some(info) = classes.get_mut(class) {
            info.creators.push(entry);
        }
    }
    let statics: BTreeSet<u64> = created.keys().copied().collect();
    for info in classes.values_mut() {
        let parent = info.ctors.iter().find_map(|e| {
            let scan = scans.get(e)?;
            if let Some((_, Some(base))) = own_and_base(&scan.stores, &tables) {
                return vtables.get(&base).cloned();
            }
            let callee = scan.first_this_call?;
            let f = analysis.function(callee)?;
            let own = match scans.get(&callee) {
                Some(s) => own_and_base(&s.stores, &tables),
                None => own_and_base(&scan_function(program, f, bitness, &conv).stores, &tables),
            }
            .map(|(o, _)| o);
            own.and_then(|v| vtables.get(&v).cloned()).or_else(|| {
                f.name
                    .as_deref()
                    .map(super::bare_name)
                    .and_then(ctor_class)
                    .map(|(c, _)| c.to_owned())
            })
        });
        let creator_parent = info.creators.iter().find_map(|e| {
            let (_, base) = own_and_base(&scans.get(e)?.result_stores, &tables)?;
            vtables.get(&base?).cloned()
        });
        info.parent = descriptors
            .parents
            .get(&info.name)
            .cloned()
            .or_else(|| info.vtable.and_then(|v| super::rtti::parent(program, v)))
            .or_else(|| parent.or(creator_parent).filter(|p| *p != info.name));
    }
    for name in descriptors.names.values() {
        if !classes.contains_key(name) {
            classes.insert(
                name.clone(),
                ClassInfo {
                    name: name.clone(),
                    vtable: None,
                    slots: Vec::new(),
                    parent: descriptors.parents.get(name).cloned(),
                    ctors: Vec::new(),
                    creators: Vec::new(),
                },
            );
        }
    }
    unname_foreign_signatures(&classes, &mut analysis.functions);
    unname_inlined_signatures(&mut analysis.functions);
    let mut renames: BTreeMap<u64, String> = BTreeMap::new();
    for (&entry, class) in &member {
        if analysis.function(entry).is_some_and(|f| f.name.is_none()) {
            renames.insert(entry, format!("{class}::ctor_or_dtor"));
        }
    }
    for (&entry, class) in &created {
        if analysis.function(entry).is_some_and(|f| f.name.is_none()) {
            renames.insert(entry, format!("{class}::create"));
        }
    }
    /// Most instructions in a factory that installs no vtable of its own.
    ///
    /// The rule above misses such a factory: it takes memory from a pool
    /// and hands it to the constructor, which installs the table. Its
    /// whole body is those two calls and a null check, which is the shape
    /// to insist on: a deleting destructor also calls one member of one
    /// class and returns the object, and naming that `create` would say
    /// the opposite of what it does.
    const CREATE_INSTRS_MAX: usize = 16;
    /// The calls such a factory makes: the allocator and the constructor.
    const CREATE_CALLEES: usize = 2;
    for f in &analysis.functions {
        if f.name.is_some()
            || renames.contains_key(&f.entry)
            || f.instr_count > CREATE_INSTRS_MAX
            || f.callees.len() != CREATE_CALLEES
            || f.returns_value == Some(false)
        {
            continue;
        }
        if let Some(class) = single(f.callees.iter().filter_map(|c| member.get(c))) {
            renames.insert(f.entry, format!("{class}::create"));
        }
    }
    /// Fewest factories that must agree on a callee for it to be the
    /// allocator.
    ///
    /// Every factory's other call is the allocator it takes the memory
    /// from: one function shared by thousands of them and named by none of
    /// them, the callee they agree on that is nobody's constructor.
    const ALLOC_FACTORIES_MIN: usize = 50;
    let mut votes: BTreeMap<u64, usize> = BTreeMap::new();
    for (entry, name) in &renames {
        if !name.ends_with("::create") {
            continue;
        }
        let Some(f) = analysis.function(*entry) else {
            continue;
        };
        for c in f.callees.iter().filter(|c| !member.contains_key(c)) {
            *votes.entry(*c).or_default() += 1;
        }
    }
    let allocator = votes
        .iter()
        .max_by_key(|(_, n)| **n)
        .filter(|(_, n)| **n >= ALLOC_FACTORIES_MIN)
        .map(|(a, _)| *a);
    if let Some(a) = allocator
        && analysis.function(a).is_some_and(|f| f.name.is_none())
        && !renames.contains_key(&a)
    {
        renames.insert(a, "pool_alloc".to_owned());
    }
    propagate_slot_names(analysis, &classes, &mut renames);
    let ctor_classes: Vec<(u64, String)> = analysis
        .functions
        .iter()
        .filter_map(|f| {
            let class = member.get(&f.entry).cloned().or_else(|| {
                f.name
                    .as_deref()
                    .and_then(ctor_class)
                    .map(|(c, _)| c.to_owned())
            })?;
            Some((f.entry, class))
        })
        .collect();
    let mut tls_votes: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    let mut global_votes: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for (entry, class) in &ctor_classes {
        let Some(scan) = scans.get(entry) else {
            continue;
        };
        for off in &scan.tls_stores {
            tls_votes.entry(*off).or_default().insert(class.clone());
        }
        for addr in &scan.global_stores {
            global_votes.entry(*addr).or_default().insert(class.clone());
        }
    }
    phases.mark("vtables tail before rescan");
    let tls_slots: BTreeMap<u64, String> = unanimous(tls_votes);
    let mut global_hints: BTreeMap<u64, String> = unanimous(global_votes);
    let todo: Vec<&Function> = analysis
        .functions
        .iter()
        .filter(|f| {
            !scans.contains_key(&f.entry)
                && renames
                    .get(&f.entry)
                    .cloned()
                    .or_else(|| f.name.clone())
                    .is_some_and(|n| class_of(&n).is_some())
        })
        .collect();
    scans.extend(scan_all(program, &todo, bitness, &conv));
    let unscanned: Vec<&Function> = analysis
        .functions
        .iter()
        .filter(|f| f.signature.is_none() && !scans.contains_key(&f.entry))
        .collect();
    scans.extend(scan_all(program, &unscanned, bitness, &conv));
    phases.mark("vtables rescan all");
    let reads = read_counts(&scans);
    settle_tails(&mut scans, &reads);
    let varargs: BTreeMap<u64, usize> = scans
        .iter()
        .filter_map(|(e, s)| Some((*e, s.vararg_fixed?)))
        .collect();
    let literals: BTreeSet<(u64, u8)> = scans
        .values()
        .flat_map(|s| &s.data_args)
        .filter(|&&(_, _, addr)| string_at(program, addr))
        .map(|&(target, p, _)| (target, p))
        .collect();
    // INVARIANT: a variadic function's arguments past its fixed ones are
    // whatever each caller set, read through the list as its format says,
    // and a parameter some caller hands a string literal (an assertion
    // reporter's file name) holds text, so neither is a typed slot for its
    // callers: a class one caller hands there types nothing, and a caller
    // passing a register on takes no class from one. The tables holding a
    // function still type its `this`: a body the linker folded is one
    // class's method and another caller's function at once.
    let fixed_slot = |target: u64, p: u8| varargs.get(&target).is_none_or(|&k| usize::from(p) < k);
    let typed_slot = |target: u64, p: u8| !literals.contains(&(target, p)) && fixed_slot(target, p);
    // The parameters some caller hands constant data that is neither text
    // nor a class's table: bytes, no object.
    let raw: BTreeSet<(u64, u8)> = scans
        .values()
        .flat_map(|s| &s.data_args)
        .filter(|&&(_, _, addr)| {
            program.section_at(addr).is_some_and(|s| !s.writable)
                && !string_at(program, addr)
                && !tables.contains_key(&addr)
        })
        .map(|&(target, p, _)| (target, p))
        .collect();
    let mut holders: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for info in classes.values() {
        for &f in &info.slots {
            holders.entry(f).or_default().insert(info.name.clone());
        }
    }
    holders.retain(|f, _| analysis.function(*f).is_some_and(|x| x.signature.is_none()));
    // INVARIANT: a member's name says which class it belongs to, so the
    // `this` it reads is that class or one derived from it: votes that only
    // reach an ancestor, or none, leave it the class its name gives, and so
    // do callers of an unrelated class unless a table holds the function
    // (a destructor a derived class's table holds stores its base's table
    // and is named after it). A function that never reads its first
    // argument (a factory, an import's thunk) has no `this` to type.
    let named: BTreeMap<u64, String> = analysis
        .functions
        .iter()
        .filter(|f| {
            f.signature.is_none()
                && !statics.contains(&f.entry)
                && reads.get(&f.entry).is_some_and(|&k| k > 0)
        })
        .filter_map(|f| {
            let name = renames.get(&f.entry).or(f.name.as_ref())?;
            Some((f.entry, class_of(name)?.to_owned()))
        })
        .collect();
    // A named function's scan is in hand from the first round on: its `this`
    // votes as its name says.
    for f in &analysis.functions {
        let named_class = renames
            .get(&f.entry)
            .cloned()
            .or_else(|| f.name.clone())
            .is_some_and(|n| class_of(&n).is_some());
        if named_class && !scans.contains_key(&f.entry) {
            scans.insert(f.entry, scan_function(program, f, bitness, &conv));
        }
    }
    let held = FirstMembers::gather(analysis, &scans, &renames, &statics, &reads, &classes);
    let locals = Locals::gather(analysis, &scans);
    phases.mark("vtables gather held+locals");
    // INVARIANT: a class one caller hands on second-hand (its own parameter's,
    // declared or hinted) weighs below a first-hand vote: it settles on a
    // callee another caller contradicts only when a second caller hands on a
    // class too. A caller contradicts it by handing the callee data of no
    // class (constant bytes) or of an unrelated one (a local copy of its own
    // parameter of another class): a blob sink such as `sqlite3_bind_blob`,
    // handed a `matrix44` by one binder and a copied `float4` by another, is
    // no member of either class.
    let related = |a: &String, b: &String| {
        a == b
            || ancestry(&classes, a).contains(b)
            || ancestry(&classes, b).contains(a)
            || held.holds(a, b)
            || held.holds(b, a)
    };
    let contradicts = |key: (u64, u8), handed: &BTreeSet<String>| {
        raw.contains(&key)
            || locals.args.get(&key).into_iter().flatten().any(|local| {
                locals.copies.get(local).is_some_and(|copied| {
                    copied.iter().all(|c| handed.iter().all(|h| !related(c, h)))
                })
            })
    };
    let mut inputs = Inputs::default();
    // INVARIANT: the classes whose tables hold a function vote for its
    // `this` beside its callers, so a derived override handing its own
    // `this` to the base method it overrides leaves that method its base
    // class, the ancestor the two share.
    for (f, set) in &holders {
        inputs
            .firsthand
            .entry((*f, 0))
            .or_default()
            .extend(set.iter().cloned());
    }
    for f in &analysis.functions {
        if let Some(scan) = scans.get(&f.entry) {
            inputs.add_caller(f, scan, member_class(f, &renames, &statics, scan));
        }
    }
    for scan in scans.values() {
        inputs.add_slots(scan, &tls_slots);
    }
    phases.mark("vtables inputs");
    // INVARIANT: a parameter a function hands on as a callee's `this`, or
    // for a callee parameter of a known class, is that class: the callee
    // dereferences it as one. A member's own `this` is typed by its name, a
    // virtual's by the tables holding it (a derived class's override hands
    // its `this` to its base's methods), and a declared parameter by its
    // signature. It is the weakest evidence, a class the callee accepts
    // rather than one a caller hands in, so it types only a parameter no
    // caller and no table votes for, and every callee bounds the class: the
    // parameter is the most derived of them, which must descend from all
    // the others. A callee that never reads the register ([`read_counts`])
    // bounds it only by its declared signature: neither a class its callers
    // gave it nor the class its name gives (a factory ignores what its first
    // register holds) says what the register holds.
    for f in analysis.functions.iter().filter(|f| f.signature.is_none()) {
        let Some(scan) = scans.get(&f.entry) else {
            continue;
        };
        let member = holders.contains_key(&f.entry)
            || (!statics.contains(&f.entry)
                && renames
                    .get(&f.entry)
                    .cloned()
                    .or_else(|| f.name.clone())
                    .is_some_and(|n| class_of(&n).is_some()));
        let passed =
            scan.this_calls
                .iter()
                .map(|&(t, p)| (t, p, 0u8))
                .chain(scan.calls.iter().filter_map(|&(t, p, ref v)| match v {
                    Tracked::Param(n) => Some((t, p, *n)),
                    _ => None,
                }));
        for (target, p, n) in passed {
            if n == 0 && member {
                continue;
            }
            let Some(callee) = analysis.function(target).filter(|_| typed_slot(target, p)) else {
                continue;
            };
            let read = reads.get(&target).is_none_or(|&k| usize::from(p) < k);
            let own = if p == 0 && read {
                receiver_class(callee, &renames, &statics, &scans).map(str::to_owned)
            } else {
                None
            }
            .or_else(|| param_class(callee, &BTreeMap::new(), p));
            let bound = match own {
                Some(class) => Bounded::Used(class),
                None if read && callee.signature.is_none() => {
                    inputs
                        .readers
                        .entry((target, p))
                        .or_default()
                        .insert((f.entry, n));
                    Bounded::Given((target, p))
                }
                None => continue,
            };
            inputs.bounds.entry((f.entry, n)).or_default().push(bound);
        }
    }
    phases.mark("vtables bounds");
    // One parameter's class from the classes the others had the round
    // before: its votes, or the bounds of its callees when nothing votes.
    let resolve = |key: (u64, u8),
                   inputs: &Inputs,
                   hints: &BTreeMap<u64, BTreeMap<u8, String>>,
                   widened: &BTreeSet<(u64, u8)>|
     -> Option<(String, bool)> {
        let (target, p) = key;
        let hint = |k: &(u64, u8)| hints.get(&k.0).and_then(|h| h.get(&k.1));
        let firsthand = inputs.firsthand.get(&key);
        let mut voters: BTreeSet<String> = BTreeSet::new();
        let mut relayers: BTreeSet<u64> = BTreeSet::new();
        for (caller, class) in inputs.relayed.get(&key).into_iter().flatten() {
            voters.insert(class.clone());
            relayers.insert(*caller);
        }
        for (caller, from) in inputs.hinted.get(&key).into_iter().flatten() {
            if let Some(class) = hint(from) {
                voters.insert(class.clone());
                relayers.insert(*caller);
            }
        }
        if relayers.len() < 2 && contradicts(key, &voters) {
            voters.clear();
            relayers.clear();
        }
        voters.extend(firsthand.into_iter().flatten().cloned());
        let mut bounds: BTreeMap<String, Bound> = BTreeMap::new();
        for bounded in inputs.bounds.get(&key).into_iter().flatten() {
            let (class, wide, used) = match bounded {
                Bounded::Used(class) => (class.clone(), false, true),
                Bounded::Given(from) => match hint(from) {
                    Some(class) => (class.clone(), widened.contains(from), false),
                    None => continue,
                },
            };
            let bound = bounds.entry(class).or_insert(Bound {
                wide: true,
                used: false,
            });
            bound.wide &= wide;
            bound.used |= used;
        }
        if firsthand.is_none() && relayers.is_empty() {
            if !typed_slot(target, p) {
                return None;
            }
            let class = deepest_class(&classes, &held.outermost(bounds.keys().cloned().collect()))?;
            let wide = bounds.get(&class).is_some_and(|b| b.wide);
            return Some((class, wide));
        }
        // INVARIANT: a register a function never reads ([`read_counts`])
        // holds nothing it uses, so whatever its callers leave there types
        // nothing (a factory called with its caller's `this` still in
        // `rcx`); the tables holding it still type its `this`.
        let unread = reads.get(&target).is_some_and(|&k| usize::from(p) >= k);
        let voters = held.outermost(if unread || literals.contains(&key) {
            holders
                .get(&target)
                .filter(|_| p == 0)
                .cloned()
                .unwrap_or_default()
        } else {
            voters
        });
        // INVARIANT: a callee's own use of a parameter (handing it to a
        // member of a class, or to a parameter a signature declares)
        // outranks the class a single caller casts only from its own hint:
        // unless that class is the one used or derives from it, or the two
        // are one object seen at two depths (one names the other among its
        // template arguments, as a key-value pair does the pointer it starts
        // with, or holds the other at offset 0), the parameter is the class
        // used. Of an object and the member it starts with, the parameter is
        // the object whenever anything names it ([`FirstMembers`]).
        let used = (firsthand.is_none() && relayers.len() == 1)
            .then(|| {
                let used: BTreeSet<String> = bounds
                    .iter()
                    .filter(|(_, b)| b.used)
                    .map(|(c, _)| c.clone())
                    .collect();
                deepest_class(&classes, &held.outermost(used))
            })
            .flatten();
        let voted = common_class(&classes, &voters);
        let joined = match (&voted, &used) {
            (Some(v), Some(u)) if held.holds(u, v) => used.clone(),
            (Some(v), Some(u))
                if !held.holds(v, u)
                    && !ancestry(&classes, v).contains(u)
                    && type_parts(v).is_disjoint(&type_parts(u)) =>
            {
                used.clone()
            }
            _ => voted,
        };
        let own = named.get(&target).filter(|own| {
            p == 0
                && joined.as_ref().is_none_or(|c| {
                    c != *own
                        && (ancestry(&classes, own).contains(c)
                            || (!ancestry(&classes, c).contains(own)
                                && !holders.contains_key(&target)))
                })
        });
        let class = own.cloned().or(joined).filter(|_| fixed_slot(target, p))?;
        let wide = own.is_none() && !voters.contains(&class) && used.as_ref() != Some(&class);
        Some((class, wide))
    };
    let mut hints: BTreeMap<u64, BTreeMap<u8, String>> = BTreeMap::new();
    // INVARIANT: a class only the common ancestor of a parameter's votes
    // reaches, wider than every one of them, is true of the parameter but
    // says nothing a vote said; a handler takes no class prefix from it,
    // nor from a callee's class of that kind.
    let mut widened: BTreeSet<(u64, u8)> = BTreeSet::new();
    // INVARIANT: the rounds run until no class changes, each round typing
    // every parameter again from the classes the round before gave, so only
    // a parameter some of whose inputs changed can change: the round types
    // those again (`dirty`), by function and position. A parameter whose
    // class still flips when the rounds stop, back to what it was two rounds
    // before, is held up only by votes that feed each other (a caller typed
    // by the callee it then votes for): it has no class, never whichever one
    // the last round happened to give it.
    let mut dirty = inputs.params();
    let mut last: BTreeMap<(u64, u8), Option<String>> = BTreeMap::new();
    let mut before_last: BTreeMap<(u64, u8), Option<String>> = BTreeMap::new();
    let mut settled = false;
    for round in 0..HINT_ROUNDS {
        if round > 0 {
            // A function only its new class makes vote for its callees is
            // scanned now, as the round before typed it.
            for &(entry, p) in last.keys() {
                if p != 0
                    || scans.contains_key(&entry)
                    || hints.get(&entry).is_none_or(|h| !h.contains_key(&0))
                {
                    continue;
                }
                let Some(f) = analysis.function(entry) else {
                    continue;
                };
                let scan = scan_function(program, f, bitness, &conv);
                inputs.add_caller(f, &scan, None);
                inputs.add_slots(&scan, &tls_slots);
                dirty.extend(scan.this_calls.iter().copied());
                dirty.extend(scan.calls.iter().map(|&(t, p, _)| (t, p)));
                scans.insert(entry, scan);
            }
        }
        let typed: Vec<_> = dirty
            .iter()
            .map(|&key| (key, resolve(key, &inputs, &hints, &widened)))
            .collect();
        let mut changed: BTreeMap<(u64, u8), Option<String>> = BTreeMap::new();
        let mut moved: BTreeSet<(u64, u8)> = BTreeSet::new();
        for ((entry, p), new) in typed {
            let (class, wide) = new.map_or((None, false), |(c, w)| (Some(c), w));
            let old = hints.get(&entry).and_then(|h| h.get(&p)).cloned();
            if class != old {
                changed.insert((entry, p), old);
                match class {
                    Some(c) => {
                        hints.entry(entry).or_default().insert(p, c);
                    }
                    None => {
                        if let Some(h) = hints.get_mut(&entry) {
                            h.remove(&p);
                            if h.is_empty() {
                                hints.remove(&entry);
                            }
                        }
                    }
                }
                moved.insert((entry, p));
            }
            if wide != widened.contains(&(entry, p)) {
                if wide {
                    widened.insert((entry, p));
                } else {
                    widened.remove(&(entry, p));
                }
                moved.insert((entry, p));
            }
        }
        if moved.is_empty() {
            settled = true;
            break;
        }
        dirty = moved
            .iter()
            .filter_map(|k| inputs.readers.get(k))
            .flatten()
            .copied()
            .collect();
        before_last = std::mem::replace(&mut last, changed);
    }
    if !settled {
        for &(entry, p) in last.keys() {
            let now = hints.get(&entry).and_then(|h| h.get(&p)).cloned();
            if now.is_some() && before_last.get(&(entry, p)) == Some(&now) {
                if let Some(h) = hints.get_mut(&entry) {
                    h.remove(&p);
                    if h.is_empty() {
                        hints.remove(&entry);
                    }
                }
                widened.remove(&(entry, p));
            }
        }
    }
    phases.mark("vtables rounds");
    let callees: BTreeSet<u64> = scans
        .values()
        .flat_map(|s| {
            s.this_calls
                .iter()
                .map(|(t, _)| *t)
                .chain(s.calls.iter().map(|(t, _, _)| *t))
        })
        .collect();
    let todo: Vec<&Function> = callees
        .iter()
        .filter(|e| !scans.contains_key(e))
        .filter_map(|e| analysis.function(*e))
        .collect();
    scans.extend(scan_all(program, &todo, bitness, &conv));
    let ValueHints {
        results: mut ret_hints,
        fields: mut field_hints,
        types: mut field_types,
    } = value_hints(
        analysis, &classes, &scans, &renames, &hints, &statics, &held,
    );
    // INVARIANT: a constructor storing a base's table at `[this+off]`
    // initializes an embedded subobject of that table's class in place (an
    // inlined base constructor under multiple inheritance), so the field at
    // `off` holds an object of the class the table belongs to: the class's
    // own table names it, and a further base's table names the base its
    // locator places at that offset. A table the analysis cannot give a
    // class that holds slots types nothing.
    for (entry, class) in &ctor_classes {
        let Some(scan) = scans.get(entry) else {
            continue;
        };
        for &(off, table) in &scan.field_stores {
            let embedded = vtables
                .get(&table)
                .cloned()
                .or_else(|| super::rtti::secondary(program, table).map(|(_, base)| base))
                .filter(|c| classes.get(c).is_some_and(|i| !i.slots.is_empty()));
            if let Some(c) = embedded {
                field_types.entry((class.clone(), off)).or_insert(c);
            }
        }
    }
    let address_votes = {
        let member_class = |entry: u64| named_class(analysis, &renames, &statics, &hints, entry);
        let mut votes: BTreeMap<(u64, u8), BTreeSet<String>> = BTreeMap::new();
        for (&entry, scan) in &scans {
            let Some(class) = member_class(entry) else {
                continue;
            };
            for (target, p, val) in &scan.calls {
                if let Tracked::FieldAddr(off) = val
                    && analysis
                        .function(*target)
                        .is_some_and(|f| f.signature.is_none())
                    && let Some(t) = field_types.get(&(class.clone(), *off))
                {
                    votes.entry((*target, *p)).or_default().insert(t.clone());
                }
            }
        }
        votes
    };
    for ((target, p), voters) in address_votes {
        if typed_slot(target, p)
            && let Some(t) = single(held.outermost(voters))
        {
            let slot = hints
                .entry(target)
                .or_default()
                .entry(p)
                .or_insert_with(|| t.clone());
            if held.holds(&t, slot) {
                *slot = t;
            }
        }
    }
    for (&entry, scan) in &scans {
        if let Some(class) = scan.returns_tls.and_then(|off| tls_slots.get(&off)) {
            ret_hints.entry(entry).or_insert_with(|| class.clone());
        }
    }
    let mut frontier: BTreeSet<u64> = scans
        .iter()
        .filter(|(_, s)| !s.stores.is_empty())
        .filter_map(|(e, _)| analysis.function(*e))
        .flat_map(|f| f.callers.iter().copied())
        .collect();
    for _ in 0..SUMMARY_ROUNDS {
        let todo: Vec<&Function> = frontier
            .iter()
            .filter(|e| !scans.contains_key(e))
            .filter_map(|e| analysis.function(*e))
            .collect();
        scans.extend(scan_all(program, &todo, bitness, &conv));
        let this_class = |entry: u64| named_class(analysis, &renames, &statics, &hints, entry);
        let found = return_summaries(
            analysis,
            &scans,
            &vtables,
            &ret_hints,
            &global_hints,
            &field_hints,
            &this_class,
        );
        if found.results.is_empty() && found.globals.is_empty() && found.fields.is_empty() {
            break;
        }
        frontier.clear();
        for (entry, class) in found.results {
            if let Some(f) = analysis.function(entry) {
                frontier.extend(f.callers.iter().copied());
            }
            ret_hints.insert(entry, class);
        }
        for (addr, class) in found.globals {
            frontier.extend(analysis.xrefs_to(addr).iter().filter_map(|s| s.from_entry));
            global_hints.insert(addr, class);
        }
        for ((class, off), pointee) in found.fields {
            if let Some(info) = classes.get(&class) {
                frontier.extend(info.slots.iter().copied());
            }
            field_hints.insert((class, off), pointee);
        }
    }
    for f in &mut analysis.functions {
        if f.signature.is_some() {
            continue;
        }
        if let Some(h) = hints.get(&f.entry) {
            f.param_hints = h.clone();
        }
        // INVARIANT: a handler's type check names only what it handles; the
        // object it was handed first is the class it is a method of.
        if f.name_source == NameSource::Handler
            && !widened.contains(&(f.entry, 0))
            && let Some(name) = f.name.as_deref().filter(|n| !n.contains("::"))
            && let Some(class) = f.param_hints.get(&0)
        {
            f.name = Some(format!("{class}::{name}"));
        }
        if let Some(c) = ret_hints.get(&f.entry) {
            f.ret_hint = Some(c.clone());
        }
    }
    analysis.classes.field_hints = field_hints;
    analysis.classes.field_types = field_types;
    analysis.classes.tls_slots = tls_slots;
    analysis.classes.global_hints = global_hints;
    let mut taken: BTreeSet<String> = analysis
        .functions
        .iter()
        .filter_map(|f| f.name.clone())
        .collect();
    for f in &mut analysis.functions {
        let Some(base) = renames.get(&f.entry) else {
            continue;
        };
        if f.name.is_some() {
            continue;
        }
        f.name = Some(unique_name(&mut taken, base));
        f.name_inferred = true;
        f.name_source = NameSource::Slot;
    }
    share_slot_verdicts(&classes, &mut analysis.functions);
    name_vtable_slots(&classes, &mut analysis.functions);
    analysis.classes.dtor_slots = destructor_slots(program, &classes, &analysis.functions);
    let accessor = analysis.packs.name_for("class_info_accessor").to_owned();
    name_descriptor_accessors(
        program,
        bitness,
        &descriptors.names,
        &accessor,
        &mut analysis.functions,
    );
    analysis.classes.descriptors.clone_from(&descriptors.names);
    analysis.classes.by_name = classes;
    analysis.classes.secondary_vtables = secondary;
    analysis.classes.vtables = vtables;
    phases.mark("vtables typing+names");
}

/// The class that introduces slot `k`: the topmost ancestor whose own table
/// reaches that far.
///
/// A class known only from its descriptor, without a table of its own, is
/// walked through.
///
/// # Arguments
///
/// * `classes` - Classes with their slots and parents.
/// * `class` - Where to start.
/// * `k` - The slot index.
fn introducer(classes: &BTreeMap<String, ClassInfo>, class: &str, k: usize) -> String {
    let mut cur = class.to_owned();
    let mut at = class.to_owned();
    for _ in 0..ANCESTORS_MAX {
        let Some(parent) = classes.get(&at).and_then(|c| c.parent.clone()) else {
            break;
        };
        let Some(p) = classes.get(&parent).filter(|_| parent != at) else {
            break;
        };
        if p.vtable.is_some() {
            if p.slots.len() <= k {
                break;
            }
            cur.clone_from(&parent);
        }
        at = parent;
    }
    cur
}

/// Names the virtual methods no signature string named.
///
/// A function that sits at slot `k` of a class's table is that class's `k`th
/// virtual method, so it takes the name `Class::vfunc_k` when nothing else
/// named it. The class is the one that introduces the slot ([`introducer`]),
/// since an inherited entry belongs to the ancestor that declared it; a
/// function several unrelated tables share, such as an empty method reused
/// as a slot filler, has no one class to belong to and keeps its address
/// name. The name is marked inferred.
///
/// # Arguments
///
/// * `classes` - Classes with their slots and parents.
/// * `functions` - Functions, named in place.
fn name_vtable_slots(classes: &BTreeMap<String, ClassInfo>, functions: &mut [Function]) {
    let mut owners: BTreeMap<u64, BTreeSet<(String, usize)>> = BTreeMap::new();
    for (name, info) in classes {
        for (k, &entry) in info.slots.iter().enumerate() {
            owners
                .entry(entry)
                .or_default()
                .insert((introducer(classes, name, k), k));
        }
    }
    let chosen: BTreeMap<u64, (String, usize)> = owners
        .into_iter()
        .filter_map(|(entry, set)| single(set).map(|one| (entry, one)))
        .collect();
    let mut taken: BTreeSet<String> = functions.iter().filter_map(|f| f.name.clone()).collect();
    for f in functions.iter_mut() {
        if f.name.is_some() {
            continue;
        }
        let Some((class, k)) = chosen.get(&f.entry) else {
            continue;
        };
        f.name = Some(unique_name(&mut taken, &format!("{class}::vfunc_{k}")));
        f.name_inferred = true;
        f.name_source = NameSource::Slot;
    }
}

/// Shares return verdicts along vtable slots.
///
/// The overrides of one virtual method sit at one slot index in a class and
/// its descendants and share a signature, so a slot function without a
/// call-site verdict takes the verdict its siblings agree on. Siblings are
/// the functions at slot `k` of every class that shares an [`introducer`]
/// for it; a declared signature counts as a verdict.
///
/// # Arguments
///
/// * `classes` - Classes with their slots and parents.
/// * `functions` - Functions, their verdicts filled in place.
fn share_slot_verdicts(classes: &BTreeMap<String, ClassInfo>, functions: &mut [Function]) {
    let mut groups: BTreeMap<(String, usize), BTreeSet<u64>> = BTreeMap::new();
    for (name, info) in classes {
        for (k, &entry) in info.slots.iter().enumerate() {
            groups
                .entry((introducer(classes, name, k), k))
                .or_default()
                .insert(entry);
        }
    }
    let index: BTreeMap<u64, usize> = functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.entry, i))
        .collect();
    let verdict = |f: &Function| -> Option<bool> {
        match &f.signature {
            Some(sig) => Some(sig.ret != "void"),
            None => f.returns_value,
        }
    };
    let mut fills: Vec<(usize, bool)> = Vec::new();
    for members in groups.values() {
        let mut agreed: BTreeSet<bool> = BTreeSet::new();
        let mut lacking: Vec<usize> = Vec::new();
        for entry in members {
            let Some(&i) = index.get(entry) else {
                continue;
            };
            match functions.get(i).and_then(verdict) {
                Some(v) => {
                    agreed.insert(v);
                }
                None => lacking.push(i),
            }
        }
        if let Some(&v) = single(&agreed) {
            fills.extend(lacking.into_iter().map(|i| (i, v)));
        }
    }
    for (i, v) in fills {
        if let Some(f) = functions.get_mut(i) {
            f.returns_value = Some(v);
        }
    }
}

/// The table a constructor or destructor stores for its own class, and the
/// one it stores for its base.
///
/// One stored table is the class's own. Several distinct tables are the
/// bases' and the class's own: a constructor with its base constructors
/// inlined stores the bases' tables first and its own last, a destructor
/// the reverse (it restores each base's before that base's destructor
/// runs), and a derived table is longer than its base's, so when the
/// lengths strictly grow or strictly shrink along the stores the longest is
/// the class's own and the next longest its parent's. Any other order (a
/// tie, a table of unknown length) cannot be told apart and counts as
/// nothing.
///
/// # Arguments
///
/// * `stores` - Tables stored through one object, in instruction order.
/// * `tables` - Slot lists per table.
///
/// # Returns
///
/// The own table, with the parent's when the function stores one.
fn own_and_base(stores: &[u64], tables: &BTreeMap<u64, Vec<u64>>) -> Option<(u64, Option<u64>)> {
    let mut distinct: Vec<u64> = Vec::new();
    for &t in stores {
        if !distinct.contains(&t) {
            distinct.push(t);
        }
    }
    if distinct.len() < 2 {
        return distinct.first().map(|&own| (own, None));
    }
    let lengths: Vec<usize> = distinct
        .iter()
        .map(|t| tables.get(t).map(Vec::len))
        .collect::<Option<_>>()?;
    let order = lengths.windows(2).try_fold(Ordering::Equal, |acc, w| {
        let step = match w {
            [a, b] => a.cmp(b),
            _ => Ordering::Equal,
        };
        match (acc, step) {
            (_, Ordering::Equal) => None,
            (Ordering::Equal, s) => Some(s),
            (a, s) if a == s => Some(s),
            _ => None,
        }
    })?;
    let mut ordered = distinct.clone();
    if order == Ordering::Greater {
        ordered.reverse();
    }
    let own = *ordered.last()?;
    let parent = ordered.get(ordered.len().wrapping_sub(2)).copied();
    Some((own, parent))
}

/// Names the tables no named constructor stores by the methods they introduce.
///
/// A method is introduced by a table when no ancestor table (following the
/// base-constructor links) holds it. A named method introduced by one table
/// votes for that table with its class; introduced by several, it votes for
/// the shortest when that is unique (derived tables are at least as long)
/// and nowhere otherwise. A table whose votes name one class is that
/// class's; the class gets it as primary vtable when it has none.
///
/// # Arguments
///
/// * `analysis` - Function names.
/// * `tables` - Every table found, with its slots.
/// * `parent` - Table to the table its class's base constructor stores.
/// * `vtables` - Tables already named; extended here.
/// * `classes` - Classes; extended here.
fn classify_tables(
    analysis: &Analysis,
    tables: &BTreeMap<u64, Vec<u64>>,
    parent: &BTreeMap<u64, u64>,
    vtables: &mut BTreeMap<u64, String>,
    classes: &mut BTreeMap<String, ClassInfo>,
) {
    let inherited = |table: u64, f: u64| -> bool {
        let mut at = table;
        for _ in 0..ANCESTORS_MAX {
            let Some(&p) = parent.get(&at) else {
                return false;
            };
            if tables.get(&p).is_some_and(|s| s.contains(&f)) {
                return true;
            }
            at = p;
        }
        false
    };
    let mut intro: BTreeMap<u64, Vec<(usize, u64)>> = BTreeMap::new();
    for (&table, slots) in tables {
        for f in slots.iter().collect::<BTreeSet<_>>() {
            if !inherited(table, *f) {
                intro.entry(*f).or_default().push((slots.len(), table));
            }
        }
    }
    let mut owning: BTreeMap<u64, BTreeSet<&str>> = BTreeMap::new();
    for (f, mut at) in intro {
        at.sort_unstable();
        let table = match at.as_slice() {
            [(_, t)] => *t,
            [(a, t), (b, _), ..] if a < b => *t,
            _ => continue,
        };
        if vtables.contains_key(&table) {
            continue;
        }
        // INVARIANT: a slot holding an import thunk is an inherited method
        // of a class another module defines; that class's table is in that
        // module, so its name is no vote for a table in this one.
        if let Some(class) = analysis
            .function(f)
            .and_then(|x| x.name.as_deref())
            .filter(|n| !n.contains('!'))
            .and_then(class_of)
        {
            owning.entry(table).or_default().insert(class);
        }
    }
    for (table, voters) in owning {
        let Some(class) = single(voters) else {
            continue;
        };
        let Some(slots) = tables.get(&table) else {
            continue;
        };
        vtables.insert(table, class.to_owned());
        let info = classes
            .entry(class.to_owned())
            .or_insert_with(|| ClassInfo {
                name: class.to_owned(),
                ..ClassInfo::default()
            });
        if info.vtable.is_none() {
            info.vtable = Some(table);
            info.slots = slots.clone();
        }
    }
}

/// Names each function whose whole body hands out a named descriptor's
/// address `Class::GetRtti`, where only its vtable slot named it.
///
/// A virtual call through that slot asks the object for its type
/// (`rax->Core::RefCounted::vfunc_0_1978()`), and the name says so:
/// `rax->GetRtti()`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `names` - Descriptor address to class name.
/// * `functions` - Functions, renamed in place.
fn name_descriptor_accessors(
    program: &Program,
    bitness: u32,
    names: &BTreeMap<u64, String>,
    accessor: &str,
    functions: &mut [Function],
) {
    for f in functions.iter_mut() {
        if f.instr_count != 2 || !(f.name.is_none() || f.name_source == NameSource::Slot) {
            continue;
        }
        if let Some(class) =
            super::messages::returned_global(program, f.entry, bitness).and_then(|g| names.get(&g))
        {
            f.name = Some(format!("{class}::{accessor}"));
            f.name_inferred = true;
            f.name_source = NameSource::Helper;
        }
    }
}

/// The class name each table's type accessor gives it: a slot whose whole
/// body hands out a named descriptor's address (`lea rax, [RTTI]; ret`,
/// Nebula's `GetRtti`).
///
/// An abstract base whose constructor every derived class inlines has no
/// constructor or creator of its own to name it, but its table still hands
/// out its descriptor. A descriptor more than one table hands out is
/// inherited by a class that did not override the accessor, so it names
/// none of them; a table handing out two named descriptors names nothing.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `names` - Descriptor address to class name.
/// * `tables` - Table address to its slot functions.
fn accessed_descriptors(
    program: &Program,
    bitness: u32,
    names: &BTreeMap<u64, String>,
    tables: &BTreeMap<u64, Vec<u64>>,
) -> BTreeMap<u64, String> {
    let mut by_descriptor: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
    let mut by_table: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
    let mut returned: FxHashMap<u64, Option<u64>> = FxHashMap::default();
    for (&table, slots) in tables {
        for &f in slots {
            let g = *returned
                .entry(f)
                .or_insert_with(|| super::messages::returned_global(program, f, bitness));
            if let Some(g) = g.filter(|g| names.contains_key(g)) {
                by_descriptor.entry(g).or_default().insert(table);
                by_table.entry(table).or_default().insert(g);
            }
        }
    }
    by_table
        .into_iter()
        .filter_map(|(table, descs)| {
            let d = single(descs)?;
            let sole = by_descriptor.get(&d).is_some_and(|t| t.len() == 1);
            sole.then(|| names.get(&d).cloned())
                .flatten()
                .map(|n| (table, n))
        })
        .collect()
}

/// Drops the signature names that belong to a method some virtual inlined.
///
/// A function sitting in the tables of classes `H` took its name from the
/// `__FUNCSIG__` string it carries; when that string names a method of a
/// class that is none of `H` nor any ancestor of theirs, the string came in
/// with an inlined method of another class: the game's path-engine
/// property's message handler inlined a message's `SetActor` and was named
/// `GetPathengineEntity::SetActor`. The name is dropped, so the slot passes
/// name the function after the slot it fills.
///
/// # Arguments
///
/// * `classes` - Classes with their tables and parents.
/// * `functions` - Functions, unnamed in place.
fn unname_foreign_signatures(classes: &BTreeMap<String, ClassInfo>, functions: &mut [Function]) {
    let mut holders: BTreeMap<u64, BTreeSet<&str>> = BTreeMap::new();
    for (name, info) in classes {
        for &f in &info.slots {
            holders.entry(f).or_default().insert(name.as_str());
        }
    }
    let lineage = |class: &str| -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        let mut at = Some(class.to_owned());
        for _ in 0..ANCESTORS_MAX {
            let Some(c) = at.take() else {
                break;
            };
            at = classes.get(&c).and_then(|i| i.parent.clone());
            out.insert(c);
        }
        out
    };
    for f in functions.iter_mut() {
        if f.name_source != NameSource::Signature {
            continue;
        }
        let Some(held) = holders.get(&f.entry) else {
            continue;
        };
        let Some(claimed) = f.name.as_deref().and_then(class_of) else {
            continue;
        };
        if !classes.contains_key(claimed) {
            continue;
        }
        let related = held
            .iter()
            .any(|h| lineage(h).contains(claimed) || lineage(claimed).contains(*h));
        if !related {
            f.name = None;
            f.name_inferred = false;
            f.name_source = NameSource::None;
            f.signature = None;
        }
    }
}

/// Drops the signature names a function took from a method of a class it
/// reaches through a smart pointer.
///
/// A function that calls a smart pointer's dereference (`Core::Ptr<C>::operator
/// ->`, `std::shared_ptr<C>::operator ->`) holds a `C` it was not handed as
/// `this`; when the signature string it was named by is a method
/// of `C`, that method was inlined into it. A component's handler that
/// fills a `Messaging::DeleteItem` and sends it carries `SetItem`'s
/// assertion and was named `Messaging::DeleteItem::SetItem`. A method whose
/// declared parameters mention `C` may dereference another `C` of its own,
/// and keeps its name.
///
/// # Arguments
///
/// * `functions` - Functions, unnamed in place.
fn unname_inlined_signatures(functions: &mut [Function]) {
    let reached: FxHashMap<u64, String> = functions
        .iter()
        .filter_map(|f| {
            let pointer = f.name.as_deref()?.strip_suffix("::operator ->")?;
            let class = super::classes::smart_pointee(pointer)?;
            Some((f.entry, class.to_owned()))
        })
        .collect();
    let inlined: Vec<usize> = functions
        .iter()
        .enumerate()
        .filter(|(_, f)| f.name_source == NameSource::Signature)
        .filter_map(|(i, f)| {
            let class = f.name.as_deref().and_then(class_of)?;
            let reaches = f
                .callees
                .iter()
                .any(|c| reached.get(c).is_some_and(|r| r == class));
            let declared = f
                .signature
                .as_ref()
                .is_some_and(|s| s.params.iter().any(|p| p.contains(class)));
            (reaches && !declared).then_some(i)
        })
        .collect();
    for i in inlined {
        if let Some(f) = functions.get_mut(i) {
            f.name = None;
            f.name_inferred = false;
            f.name_source = NameSource::None;
            f.signature = None;
        }
    }
}

/// Fewest classes whose destructor sits at one slot before the slot is a
/// destructor slot.
const DTOR_CLASSES_MIN: usize = 32;

/// Most instructions read from a function's entry looking for the test of
/// its deleting destructor's flag.
const FLAG_SCAN_MAX: usize = 32;

/// Tells whether a function tests bit 0 of its second argument within its
/// first instructions: the MSVC deleting destructor, which runs the
/// destructor and frees the object only when that bit is set.
///
/// The argument is followed through register copies, and across calls in
/// the registers a call keeps.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function's entry.
/// * `flag` - The register the second argument arrives in.
/// * `volatile` - The registers a call may change.
fn tests_flag_bit(program: &Program, entry: u64, flag: Register, volatile: &[Register]) -> bool {
    /// Longest x86 instruction, in bytes.
    const INSTR_MAX: usize = 15;
    let Some(bytes) = program.read_va(entry, FLAG_SCAN_MAX * INSTR_MAX) else {
        return false;
    };
    let mut decoder = Decoder::with_ip(64, bytes, entry, DecoderOptions::NONE);
    let mut holders: Vec<Register> = vec![flag];
    let mut ins = Instruction::default();
    for _ in 0..FLAG_SCAN_MAX {
        if !decoder.can_decode() {
            return false;
        }
        decoder.decode_out(&mut ins);
        if ins.is_invalid() {
            return false;
        }
        let dst = (ins.op_count() > 0 && ins.op0_kind() == OpKind::Register)
            .then(|| ins.op0_register().full_register());
        let src_held = ins.op_count() > 1
            && ins.op1_kind() == OpKind::Register
            && holders.contains(&ins.op1_register().full_register());
        match ins.mnemonic() {
            Mnemonic::Test | Mnemonic::And | Mnemonic::Bt
                if dst.is_some_and(|d| holders.contains(&d))
                    && ins.op_count() > 1
                    && ins.try_immediate(1).ok()
                        == Some(u64::from(ins.mnemonic() != Mnemonic::Bt)) =>
            {
                return true;
            }
            Mnemonic::Ret | Mnemonic::Jmp | Mnemonic::Int3 => return false,
            Mnemonic::Call => holders.retain(|r| !volatile.contains(r)),
            Mnemonic::Mov | Mnemonic::Movzx if src_held => {
                if let Some(d) = dst {
                    holders.push(d);
                }
            }
            _ => {
                if let Some(d) = dst
                    && !matches!(
                        ins.mnemonic(),
                        Mnemonic::Test | Mnemonic::Cmp | Mnemonic::Push
                    )
                {
                    holders.retain(|r| *r != d);
                }
            }
        }
    }
    false
}

/// The slot indexes at which many classes keep their destructor.
///
/// A class's function at a slot is a destructor when it is named one (a
/// `~` name, or the `ctor_or_dtor` given to a function that stores the
/// class's table at `[this]`) or, on 64-bit Windows, when it tests bit 0
/// of its second argument like MSVC's deleting destructor does. Where at
/// least [`DTOR_CLASSES_MIN`] classes' functions at one index are that, the
/// index is where some hierarchy put its virtual destructor, and a call
/// through it with `1` alone deletes the object: no other virtual is
/// handed exactly that. They need not be most of the classes at the index:
/// the game client's engine keeps its type accessor at slot 0, where 315
/// classes of other libraries keep their destructor.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `classes` - Classes with their tables.
/// * `functions` - Functions with their names.
fn destructor_slots(
    program: &Program,
    classes: &BTreeMap<String, ClassInfo>,
    functions: &[Function],
) -> BTreeSet<usize> {
    let named: FxHashMap<u64, &str> = functions
        .iter()
        .filter_map(|f| f.name.as_deref().map(|n| (f.entry, n)))
        .collect();
    let flag = (program.arch.bitness() == Some(64) && program.format == BinaryFormat::Pe)
        .then_some(Register::RDX);
    let mut shaped: FxHashMap<u64, bool> = FxHashMap::default();
    let mut dtors: BTreeMap<usize, usize> = BTreeMap::new();
    for info in classes.values() {
        for (k, f) in info.slots.iter().enumerate() {
            let is_dtor = named
                .get(f)
                .and_then(|n| n.rsplit("::").next())
                .is_some_and(|m| m.starts_with("ctor_or_dtor") || m.starts_with('~'))
                || flag.is_some_and(|reg| {
                    *shaped
                        .entry(*f)
                        .or_insert_with(|| tests_flag_bit(program, *f, reg, &MS_VOLATILE))
                });
            if is_dtor {
                *dtors.entry(k).or_default() += 1;
            }
        }
    }
    dtors
        .into_iter()
        .filter(|&(_, n)| n >= DTOR_CLASSES_MIN)
        .map(|(k, _)| k)
        .collect()
}

/// Fewest distinct functions at one slot of one hierarchy before their
/// common shape outweighs a single override's name.
const FAMILY_MIN: usize = 8;
/// Share of a slot family one shape must hold, as `num / den`, to be the
/// family's shape.
const DOMINANT: (usize, usize) = (3, 4);

/// The shape most functions at each slot of each hierarchy share, where one
/// does: the id getters behind every message class's slot 3 are all
/// `lea rax, [Id]; ret`.
///
/// # Arguments
///
/// * `analysis` - The functions with their shape hashes.
/// * `classes` - Classes with their tables and parents.
///
/// # Returns
///
/// The dominant shape by `(introducing class, slot)`.
fn dominant_shapes(
    analysis: &Analysis,
    classes: &BTreeMap<String, ClassInfo>,
) -> BTreeMap<(String, usize), u64> {
    let mut families: BTreeMap<(String, usize), BTreeSet<u64>> = BTreeMap::new();
    for (name, info) in classes {
        for (i, &f) in info.slots.iter().enumerate() {
            families
                .entry((introducer(classes, name, i), i))
                .or_default()
                .insert(f);
        }
    }
    families
        .into_iter()
        .filter_map(|(key, fns)| {
            if fns.len() < FAMILY_MIN {
                return None;
            }
            let mut counts: BTreeMap<u64, usize> = BTreeMap::new();
            for f in &fns {
                if let Some(func) = analysis.function(*f) {
                    *counts.entry(func.shape_hash).or_default() += 1;
                }
            }
            let (shape, n) = counts.into_iter().max_by_key(|&(_, n)| n)?;
            (n * DOMINANT.1 >= fns.len() * DOMINANT.0).then_some((key, shape))
        })
        .collect()
}

/// Carries virtual method names along the slot index through the class
/// hierarchy.
///
/// Slot `i` of a class's table and slot `i` of an ancestor's table are the
/// same virtual method, so a named override names the unnamed function an
/// ancestor holds there (at the topmost ancestor holding that function) and
/// a named ancestor method names an unnamed override. Proposals repeat
/// until nothing new is named; a function proposed two different names gets
/// none. Constructor, destructor and `ctor_or_dtor` names do not travel, and
/// neither does a method name that an ancestor holds at a different slot
/// (the function that inlined that method took its signature string), nor
/// one whose function differs in shape from what nearly every function at
/// that slot of the hierarchy is: one message class's slot 3 that inlined
/// a setter's assert does not name the id getter of all 645.
///
/// # Arguments
///
/// * `analysis` - Function names as found so far.
/// * `classes` - Classes with their tables and parents.
/// * `renames` - Names chosen by this pass; extended here.
fn propagate_slot_names(
    analysis: &Analysis,
    classes: &BTreeMap<String, ClassInfo>,
    renames: &mut BTreeMap<u64, String>,
) {
    let dominant = dominant_shapes(analysis, classes);
    loop {
        let name_of = |e: u64| -> Option<String> {
            renames
                .get(&e)
                .cloned()
                .or_else(|| analysis.function(e)?.name.clone())
        };
        let mut proposals: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
        for info in classes.values() {
            let mut ancestors: Vec<&ClassInfo> = Vec::new();
            let mut at = info.parent.as_deref();
            for _ in 0..ANCESTORS_MAX {
                let Some(a) = at.and_then(|p| classes.get(p)) else {
                    break;
                };
                ancestors.push(a);
                at = a.parent.as_deref();
            }
            for (i, &f) in info.slots.iter().enumerate() {
                let chain: Vec<(&ClassInfo, u64)> = ancestors
                    .iter()
                    .filter_map(|a| a.slots.get(i).map(|&g| (*a, g)))
                    .filter(|(_, g)| *g != f)
                    .collect();
                if let Some(m) = method_part(name_of(f).as_deref()) {
                    let odd_one = dominant
                        .get(&(introducer(classes, &info.name, i), i))
                        .is_some_and(|&shape| {
                            analysis.function(f).is_some_and(|x| x.shape_hash != shape)
                        });
                    if odd_one {
                        continue;
                    }
                    let elsewhere = ancestors.iter().any(|a| {
                        a.slots.iter().enumerate().any(|(j, &h)| {
                            j != i
                                && method_part(name_of(h).as_deref()).as_deref() == Some(m.as_str())
                        })
                    });
                    if elsewhere {
                        continue;
                    }
                    let mut done: BTreeSet<u64> = BTreeSet::new();
                    for (k, (_, g)) in chain.iter().enumerate() {
                        if !done.insert(*g) || method_part(name_of(*g).as_deref()).is_some() {
                            continue;
                        }
                        let top = chain
                            .iter()
                            .skip(k)
                            .rfind(|(_, h)| h == g)
                            .map_or(info, |(a, _)| *a);
                        proposals
                            .entry(*g)
                            .or_default()
                            .insert(format!("{}::{m}", top.name));
                    }
                } else if let Some(mg) = chain
                    .iter()
                    .find_map(|(_, g)| method_part(name_of(*g).as_deref()))
                {
                    let taken = info.slots.iter().enumerate().any(|(j, &h)| {
                        j != i && method_part(name_of(h).as_deref()).as_deref() == Some(mg.as_str())
                    });
                    if !taken {
                        proposals
                            .entry(f)
                            .or_default()
                            .insert(format!("{}::{mg}", info.name));
                    }
                }
            }
        }
        let mut changed = false;
        for (entry, names) in proposals {
            if names.len() != 1
                || renames.contains_key(&entry)
                || analysis.function(entry).is_none_or(|f| f.name.is_some())
            {
                continue;
            }
            if let Some(n) = names.into_iter().next() {
                renames.insert(entry, n);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Returns the method part of a qualified method name (`Foo` for `A::B::Foo`).
///
/// `None` for a name without a class, a constructor or destructor, a
/// `ctor_or_dtor` placeholder, or a `_2`-style disambiguated name (which
/// may not be the function's own).
///
/// # Arguments
///
/// * `name` - The function name, if any.
fn method_part(name: Option<&str>) -> Option<String> {
    let name = name?;
    let class = class_of(name)?;
    let method = name.get(class.len() + 2..)?;
    let deduped = method
        .rsplit_once('_')
        .is_some_and(|(_, n)| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()));
    if method.is_empty()
        || method.starts_with('~')
        || method.starts_with("ctor_or_dtor")
        || deduped
        || ctor_class(name).is_some()
    {
        return None;
    }
    Some(method.to_owned())
}

/// Classes found by [`return_summaries`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Summaries {
    /// Function entry to the class its result points at.
    results: Vec<(u64, String)>,
    /// Global address to the class the word there points at.
    globals: Vec<(u64, String)>,
    /// `(class, offset)` to the class the pointer field there points at.
    fields: Vec<((String, u64), String)>,
}

/// Types results, globals and fields by what a function hands back or
/// stores.
///
/// A function that stores no table and returns the result of a call to a
/// constructor of class `C`, to a function declared or hinted to return a
/// `C`, the word of a global hinted `C` or the word of a field of its own
/// class hinted `C`, returns a `C` (a creator, a wrapper, a singleton
/// getter, a field getter); a global or a field of the storing function's
/// class that only ever receives results of class `C` holds a `C`.
///
/// # Arguments
///
/// * `analysis` - Functions with their signatures.
/// * `scans` - Scans of the functions examined so far.
/// * `vtables` - Table address to class name.
/// * `ret_hints` - Result classes known so far.
/// * `global_hints` - Global classes known so far.
/// * `field_hints` - Pointer field classes known so far.
/// * `this_class` - The class a function's `this` belongs to, when known.
///
/// # Returns
///
/// The new result, global and field classes.
fn return_summaries(
    analysis: &Analysis,
    scans: &BTreeMap<u64, Scan>,
    vtables: &BTreeMap<u64, String>,
    ret_hints: &BTreeMap<u64, String>,
    global_hints: &BTreeMap<u64, String>,
    field_hints: &BTreeMap<(String, u64), String>,
    this_class: &dyn Fn(u64) -> Option<String>,
) -> Summaries {
    let result_class = |callee: u64| -> Option<String> {
        if let Some(c) = ret_hints.get(&callee) {
            return Some(c.clone());
        }
        let f = analysis.function(callee)?;
        if let Some(sig) = &f.signature {
            return super::decompile::pointee_class(&sig.ret).map(str::to_owned);
        }
        let stored: BTreeSet<u64> = scans.get(&callee)?.stores.iter().copied().collect();
        vtables.get(&single(stored)?).cloned()
    };
    let results: Vec<(u64, String)> = scans
        .iter()
        .filter(|(e, s)| {
            s.stores.is_empty()
                && !ret_hints.contains_key(e)
                && analysis
                    .function(**e)
                    .is_some_and(|f| f.signature.is_none())
        })
        .filter_map(|(&e, s)| {
            let class = s
                .returns_result
                .and_then(result_class)
                .or_else(|| s.returns_global.and_then(|g| global_hints.get(&g).cloned()))
                .or_else(|| {
                    let off = s.returns_field?;
                    field_hints.get(&(this_class(e)?, off)).cloned()
                })?;
            Some((e, class))
        })
        .collect();
    let mut votes: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for (addr, callee) in scans.values().flat_map(|s| s.global_result_stores.iter()) {
        if global_hints.contains_key(addr) {
            continue;
        }
        if let Some(c) = result_class(*callee) {
            votes.entry(*addr).or_default().insert(c);
        }
    }
    let globals: Vec<(u64, String)> = unanimous(votes).into_iter().collect();
    let mut field_votes: BTreeMap<(String, u64), BTreeSet<String>> = BTreeMap::new();
    for (&entry, scan) in scans {
        if scan.field_result_stores.is_empty() {
            continue;
        }
        let Some(class) = this_class(entry) else {
            continue;
        };
        for &(off, callee) in &scan.field_result_stores {
            let key = (class.clone(), off);
            if field_hints.contains_key(&key) {
                continue;
            }
            if let Some(c) = result_class(callee) {
                field_votes.entry(key).or_default().insert(c);
            }
        }
    }
    Summaries {
        results,
        globals,
        fields: unanimous(field_votes).into_iter().collect(),
    }
}

/// Types call results and fields by the calls they are passed to.
///
/// In a member method of class `K`, every direct call argument that is the
/// result of an earlier call `F`, the word loaded from `[this + off]` or the
/// address `this + off` casts a vote: passed as the callee's `this`, the
/// value is the callee's receiver class (its own class when it is a member,
/// else its hinted first parameter); passed for a declared parameter, a
/// result or loaded field is the class the parameter type points at and a
/// field address is the parameter's object type. Votes resolve like
/// parameter hints: classes to the nearest common ancestor, object types
/// when unanimous, and of an object and the member it starts with, the
/// object ([`FirstMembers`]).
///
/// # Arguments
///
/// * `analysis` - Functions, names and signatures.
/// * `classes` - Classes with their parents.
/// * `scans` - Scans of every class-named function.
/// * `renames` - Names chosen by this pass.
/// * `hints` - Parameter hints chosen by this pass.
/// * `statics` - Class-named functions whose first argument is not `this`
///   (creators).
/// * `held` - The classes others hold at offset 0.
///
/// # Returns
///
/// The result, pointer-field and embedded-object classes the votes agree
/// on.
fn value_hints(
    analysis: &Analysis,
    classes: &BTreeMap<String, ClassInfo>,
    scans: &BTreeMap<u64, Scan>,
    renames: &BTreeMap<u64, String>,
    hints: &BTreeMap<u64, BTreeMap<u8, String>>,
    statics: &BTreeSet<u64>,
    held: &FirstMembers,
) -> ValueHints {
    let member_of = |entry: u64| -> Option<String> {
        let f = analysis.function(entry)?;
        if statics.contains(&entry) {
            return None;
        }
        let name = renames.get(&entry).cloned().or_else(|| f.name.clone())?;
        let class = class_of(&name)?;
        let member = match (&f.signature, scans.get(&entry)) {
            (Some(sig), Some(scan)) => {
                sig.is_const || scan.args_read > sig.params.len() + usize::from(sig.by_pointer)
            }
            (Some(_), None) => false,
            (None, _) => true,
        };
        member.then(|| class.to_owned())
    };
    let receiver_class = |entry: u64| -> Option<String> {
        member_of(entry).or_else(|| hints.get(&entry)?.get(&0).cloned())
    };
    let mut ret_votes: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    let mut field_votes: BTreeMap<(String, u64), BTreeSet<String>> = BTreeMap::new();
    let mut type_votes: BTreeMap<(String, u64), BTreeSet<String>> = BTreeMap::new();
    for f in &analysis.functions {
        let Some(class) = member_of(f.entry) else {
            continue;
        };
        let Some(scan) = scans.get(&f.entry) else {
            continue;
        };
        for (target, pos, val) in &scan.calls {
            let pos = usize::from(*pos);
            let callee = analysis.function(*target);
            let lead = usize::from(member_of(*target).is_some())
                + usize::from(
                    callee
                        .and_then(|c| c.signature.as_ref())
                        .is_some_and(|s| s.by_pointer),
                );
            let declared = callee
                .and_then(|c| c.signature.as_ref())
                .and_then(|s| pos.checked_sub(lead).and_then(|i| s.params.get(i)));
            let (points_at, embedded) = if pos == 0 {
                let recv = receiver_class(*target);
                (recv.clone(), recv)
            } else if let Some(ty) = declared {
                (
                    super::decompile::pointee_class(ty).map(str::to_owned),
                    Some(object_type(ty)).filter(|t| !t.is_empty()),
                )
            } else {
                (None, None)
            };
            match (val, points_at, embedded) {
                (Tracked::Result(callee), Some(c), _) => {
                    ret_votes.entry(*callee).or_default().insert(c);
                }
                (Tracked::Field(off), Some(c), _) => {
                    field_votes
                        .entry((class.clone(), *off))
                        .or_default()
                        .insert(c);
                }
                (Tracked::FieldAddr(off), _, Some(t)) => {
                    type_votes
                        .entry((class.clone(), *off))
                        .or_default()
                        .insert(t);
                }
                _ => {}
            }
        }
    }
    ValueHints {
        results: ret_votes
            .into_iter()
            .filter_map(|(e, v)| common_class(classes, &held.outermost(v)).map(|c| (e, c)))
            .collect(),
        fields: field_votes
            .into_iter()
            .filter_map(|(k, v)| common_class(classes, &held.outermost(v)).map(|c| (k, c)))
            .collect(),
        types: unanimous(
            type_votes
                .into_iter()
                .map(|(k, v)| (k, held.outermost(v)))
                .collect(),
        ),
    }
}

/// What [`value_hints`] returns.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ValueHints {
    /// Function entry to the class its result points at.
    results: BTreeMap<u64, String>,
    /// `(class, offset)` to the class the pointer field there points at.
    fields: BTreeMap<(String, u64), String>,
    /// `(class, offset)` to the type of the object embedded at the field.
    types: BTreeMap<(String, u64), String>,
}

/// Returns the object type a declared parameter type denotes: `const Foo &`,
/// `Foo &`, `Foo *` and `Foo` all give `Foo`.
///
/// # Arguments
///
/// * `ty` - The declared type text.
pub(in crate::analysis) fn object_type(ty: &str) -> String {
    ty.trim_start_matches("const ")
        .trim_end_matches(['&', '*', ' '])
        .to_owned()
}

/// The class a member function's `this` belongs to: the class its name
/// qualifies it with, unless it is a creator or its signature declares
/// every argument it reads (a static).
///
/// # Arguments
///
/// * `target` - The function.
/// * `renames` - Names chosen by this pass.
/// * `statics` - Class-named functions whose first argument is not `this`.
/// * `scans` - Scans, for how many arguments the function reads.
fn receiver_class<'a>(
    target: &'a Function,
    renames: &'a BTreeMap<u64, String>,
    statics: &'a BTreeSet<u64>,
    scans: &BTreeMap<u64, Scan>,
) -> Option<&'a str> {
    let name = match renames.get(&target.entry) {
        Some(renamed) => renamed.as_str(),
        None => target.name.as_deref()?,
    };
    let class = class_of(name)?;
    if statics.contains(&target.entry) {
        return None;
    }
    match &target.signature {
        None => Some(class),
        Some(sig) => {
            let reads_this = sig.is_const
                || scans
                    .get(&target.entry)
                    .is_some_and(|s| s.args_read > sig.params.len() + usize::from(sig.by_pointer));
            reads_this.then_some(class)
        }
    }
}

/// Returns the class a function's own name gives it, else the class its
/// first parameter was hinted, without asking whether it is a member of
/// the class ([`receiver_class`] does).
///
/// # Arguments
///
/// * `analysis` - The functions.
/// * `renames` - Names chosen by this pass.
/// * `statics` - Class-named functions whose first argument is not `this`.
/// * `hints` - Parameter classes chosen by this pass.
/// * `entry` - The function's entry.
fn named_class(
    analysis: &Analysis,
    renames: &BTreeMap<u64, String>,
    statics: &BTreeSet<u64>,
    hints: &BTreeMap<u64, BTreeMap<u8, String>>,
    entry: u64,
) -> Option<String> {
    let f = analysis.function(entry)?;
    if statics.contains(&entry) {
        return None;
    }
    // PERF: the class substring is cloned straight out of the name;
    // cloning the whole qualified name per scan was pure churn.
    renames
        .get(&entry)
        .map_or(f.name.as_deref(), |n| Some(n.as_str()))
        .and_then(class_of)
        .map(str::to_owned)
        .or_else(|| hints.get(&entry)?.get(&0).cloned())
}

/// The class a function's parameter `n` is known to point at.
///
/// A declared signature names it; otherwise a hint an earlier round
/// established does. The hidden `this` and return-pointer parameters come
/// before the declared ones, so the signature is indexed past them.
///
/// # Arguments
///
/// * `f` - The function the parameter belongs to.
/// * `hints` - Parameter classes established so far.
/// * `n` - The parameter's position among the argument registers.
fn param_class(f: &Function, hints: &BTreeMap<u64, BTreeMap<u8, String>>, n: u8) -> Option<String> {
    if let Some(sig) = &f.signature {
        let lead = usize::from(class_of(&sig.name).is_some()) + usize::from(sig.by_pointer);
        let at = usize::from(n).checked_sub(lead)?;
        return sig
            .params
            .get(at)
            .and_then(|t| super::decompile::pointee_class(t))
            .filter(|c| c.contains("::"))
            .map(str::to_owned);
    }
    hints.get(&f.entry)?.get(&n).cloned()
}

/// Returns the class every voter is or derives from: the single voter, or
/// the nearest ancestor (following parent links) common to all of them.
///
/// # Arguments
///
/// * `classes` - Classes with their parents.
/// * `voters` - The classes of the callers.
fn common_class(
    classes: &BTreeMap<String, ClassInfo>,
    voters: &BTreeSet<String>,
) -> Option<String> {
    let mut it = voters.iter();
    let mut common = ancestry(classes, it.next()?);
    for v in it {
        let theirs = ancestry(classes, v);
        common.retain(|c| theirs.contains(c));
    }
    common.into_iter().next()
}

/// Returns the voter every other voter is or is an ancestor of: the most
/// derived class when all of them lie on one line of descent.
///
/// # Arguments
///
/// * `classes` - Classes with their parents.
/// * `voters` - The classes the callees accept.
///
/// # Returns
///
/// That class, or `None` when two voters lie on separate lines.
fn deepest_class(
    classes: &BTreeMap<String, ClassInfo>,
    voters: &BTreeSet<String>,
) -> Option<String> {
    voters
        .iter()
        .find(|v| {
            let line = ancestry(classes, v);
            voters.iter().all(|w| line.contains(w))
        })
        .cloned()
}

/// Returns a type and every type its template arguments name, at any
/// depth, keeping the qualified ones: `A::B<C::D,int>` gives itself and
/// `C::D`.
///
/// # Arguments
///
/// * `name` - The type's name.
fn type_parts(name: &str) -> BTreeSet<String> {
    let mut parts = BTreeSet::new();
    let mut todo = vec![name.trim()];
    while let Some(n) = todo.pop() {
        if n.contains("::") {
            parts.insert(n.to_owned());
        }
        let (Some(open), Some(close)) = (n.find('<'), n.rfind('>')) else {
            continue;
        };
        let Some(inner) = n.get(open + 1..close) else {
            continue;
        };
        let mut depth = 0usize;
        let mut start = 0;
        for (i, ch) in inner.char_indices() {
            match ch {
                '<' => depth += 1,
                '>' => depth = depth.saturating_sub(1),
                ',' if depth == 0 => {
                    todo.extend(inner.get(start..i).map(str::trim));
                    start = i + 1;
                }
                _ => {}
            }
        }
        todo.extend(inner.get(start..).map(str::trim));
    }
    parts
}

/// A class the callees a parameter is handed to bound it by.
#[derive(Clone, Copy)]
struct Bound {
    /// Every callee giving it was only given it as the common ancestor of
    /// its votes.
    wide: bool,
    /// Some callee's name or declared signature gives it: the callee uses
    /// the parameter as one.
    used: bool,
}

/// Marks a template's arguments in the type it holds at offset 0.
const ARGS_MARK: &str = "\u{0}";
/// Most classes followed when asking what a class holds at offset 0.
const HELD_MAX: usize = 16;

/// The classes others hold at offset 0, as their own code shows.
///
/// A method of a class hands its own `this` to a method of another,
/// neither of them a class with a table (a class with a table starts with
/// it, so what it holds at offset 0 is a base). A template's
/// instantiations hold the same kind of member, so one instantiation seen
/// holding a type built of its arguments (`Util::Dictionary<K,V>` its
/// `Util::Array<Util::KeyValuePair<K,V> >`) makes each instantiation hold
/// its own.
#[derive(Default)]
struct FirstMembers {
    /// Class to the classes its code shows it holding at offset 0.
    direct: BTreeMap<String, BTreeSet<String>>,
    /// Template to the type it holds at offset 0, its arguments marked
    /// ([`ARGS_MARK`]); one with instantiations that disagree has none.
    patterns: BTreeMap<String, Option<String>>,
}

impl FirstMembers {
    /// Gathers the relation from the named members' scans.
    ///
    /// # Arguments
    ///
    /// * `analysis` - Functions and their names.
    /// * `scans` - Scans by entry.
    /// * `renames` - Names chosen by this pass.
    /// * `statics` - Class-named functions whose first argument is not `this`.
    /// * `reads` - How many arguments each function reads ([`read_counts`]).
    /// * `classes` - The classes the tables and descriptors name.
    fn gather(
        analysis: &Analysis,
        scans: &BTreeMap<u64, Scan>,
        renames: &BTreeMap<u64, String>,
        statics: &BTreeSet<u64>,
        reads: &BTreeMap<u64, usize>,
        classes: &BTreeMap<String, ClassInfo>,
    ) -> Self {
        let mut held = Self::default();
        for f in &analysis.functions {
            let Some(scan) = scans.get(&f.entry) else {
                continue;
            };
            let Some((outer, true)) = member_class(f, renames, statics, scan) else {
                continue;
            };
            if classes.contains_key(outer) {
                continue;
            }
            for &(target, p) in &scan.this_calls {
                let Some(callee) = analysis.function(target) else {
                    continue;
                };
                if p != 0 || reads.get(&target).is_none_or(|&k| k == 0) {
                    continue;
                }
                let Some(inner) = receiver_class(callee, renames, statics, scans) else {
                    continue;
                };
                if inner == outer || classes.contains_key(inner) {
                    continue;
                }
                held.direct
                    .entry(outer.to_owned())
                    .or_default()
                    .insert(inner.to_owned());
            }
        }
        for (outer, inners) in &held.direct {
            let Some((template, args)) = template_args(outer) else {
                continue;
            };
            for inner in inners.iter().filter(|i| i.contains(args)) {
                let pattern = inner.replace(args, ARGS_MARK);
                held.patterns
                    .entry(template.to_owned())
                    .and_modify(|known| {
                        if known.as_ref() != Some(&pattern) {
                            *known = None;
                        }
                    })
                    .or_insert(Some(pattern));
            }
        }
        held
    }

    /// Returns the classes `outer` holds at offset 0, directly or through
    /// what those hold in turn.
    ///
    /// # Arguments
    ///
    /// * `outer` - The class.
    fn inside(&self, outer: &str) -> BTreeSet<String> {
        let mut found = BTreeSet::new();
        let mut todo = vec![outer.to_owned()];
        while let Some(class) = todo.pop() {
            let built = template_args(&class).and_then(|(template, args)| {
                self.patterns
                    .get(template)
                    .cloned()
                    .flatten()
                    .map(|p| p.replace(ARGS_MARK, args))
            });
            let next = self
                .direct
                .get(&class)
                .into_iter()
                .flatten()
                .cloned()
                .chain(built);
            for inner in next {
                if found.len() < HELD_MAX && inner != outer && found.insert(inner.clone()) {
                    todo.push(inner);
                }
            }
        }
        found
    }

    /// Returns whether `outer` holds `inner` at offset 0.
    ///
    /// # Arguments
    ///
    /// * `outer` - The class that may hold the other.
    /// * `inner` - The class it may hold.
    fn holds(&self, outer: &str, inner: &str) -> bool {
        outer != inner && self.inside(outer).contains(inner)
    }

    /// Drops from `candidates` each class another of them holds at offset
    /// 0: of an object and the member it starts with, the object.
    ///
    /// # Arguments
    ///
    /// * `candidates` - Classes voted for a parameter or bounding it.
    fn outermost(&self, candidates: BTreeSet<String>) -> BTreeSet<String> {
        if candidates.len() < 2 || self.direct.is_empty() {
            return candidates;
        }
        let held: BTreeSet<String> = candidates.iter().flat_map(|c| self.inside(c)).collect();
        let outer: BTreeSet<String> = candidates
            .iter()
            .filter(|c| !held.contains(*c))
            .cloned()
            .collect();
        if outer.is_empty() { candidates } else { outer }
    }
}

/// Splits a template instantiation into its template and its argument
/// text: `A::B<C,D>` gives `A::B` and `C,D`.
///
/// # Arguments
///
/// * `name` - The type's name.
fn template_args(name: &str) -> Option<(&str, &str)> {
    let open = name.find('<')?;
    let inner = name.strip_suffix('>')?;
    Some((name.get(..open)?, inner.get(open + 1..)?))
}

/// A parameter: its function's entry and its argument position.
type ParamKey = (u64, u8);

/// Where a parameter's votes and bounds come from, gathered once before
/// the rounds of [`infer`] type the parameters, by function entry and
/// argument position.
#[derive(Default)]
struct Inputs {
    /// First-hand votes: the tables holding a function, a named member
    /// handing on its `this`, a singleton's slot.
    firsthand: BTreeMap<ParamKey, BTreeSet<String>>,
    /// Second-hand votes of a fixed class: a caller handing on a parameter
    /// its signature declares, with the caller.
    relayed: BTreeMap<ParamKey, Vec<(u64, String)>>,
    /// Second-hand votes of whatever class a caller's own parameter has,
    /// with the caller and that parameter.
    hinted: BTreeMap<ParamKey, Vec<(u64, ParamKey)>>,
    /// Bounds from the callees a parameter is handed to.
    bounds: BTreeMap<ParamKey, Vec<Bounded>>,
    /// The parameters whose class each parameter's class goes into.
    readers: BTreeMap<ParamKey, BTreeSet<ParamKey>>,
}

impl Inputs {
    /// Adds what `f` hands its callees: its `this`, first-hand when its name
    /// makes it a member of a class, else the class it has itself; and the
    /// parameters it passes on untouched.
    ///
    /// # Arguments
    ///
    /// * `f` - The caller.
    /// * `scan` - Its scan.
    /// * `named` - The class its name gives, and whether it is a member of
    ///   it ([`member_class`]); `None` for a function its name gives none.
    fn add_caller(&mut self, f: &Function, scan: &Scan, named: Option<(&str, bool)>) {
        match named {
            Some((class, true)) => {
                for &(target, p) in &scan.this_calls {
                    self.firsthand
                        .entry((target, p))
                        .or_default()
                        .insert(class.to_owned());
                }
            }
            Some((_, false)) => {}
            None => {
                for &(target, p) in &scan.this_calls {
                    self.hinted
                        .entry((target, p))
                        .or_default()
                        .push((f.entry, (f.entry, 0)));
                    self.readers
                        .entry((f.entry, 0))
                        .or_default()
                        .insert((target, p));
                }
            }
        }
        for (target, p, val) in &scan.calls {
            let Tracked::Param(n) = val else {
                continue;
            };
            if f.signature.is_some() {
                if let Some(class) = param_class(f, &BTreeMap::new(), *n) {
                    self.relayed
                        .entry((*target, *p))
                        .or_default()
                        .push((f.entry, class));
                }
            } else {
                self.hinted
                    .entry((*target, *p))
                    .or_default()
                    .push((f.entry, (f.entry, *n)));
                self.readers
                    .entry((f.entry, *n))
                    .or_default()
                    .insert((*target, *p));
            }
        }
    }

    /// Adds the votes of the singletons whose slots a scan hands its callees.
    ///
    /// # Arguments
    ///
    /// * `scan` - The caller's scan.
    /// * `tls_slots` - Singleton classes by TLS slot.
    fn add_slots(&mut self, scan: &Scan, tls_slots: &BTreeMap<u64, String>) {
        for (target, p, val) in &scan.calls {
            if let Tracked::TlsSlot(off) = val
                && let Some(class) = tls_slots.get(off)
            {
                self.firsthand
                    .entry((*target, *p))
                    .or_default()
                    .insert(class.clone());
            }
        }
    }

    /// Returns every parameter something votes for or bounds.
    fn params(&self) -> BTreeSet<ParamKey> {
        self.firsthand
            .keys()
            .chain(self.relayed.keys())
            .chain(self.hinted.keys())
            .chain(self.bounds.keys())
            .copied()
            .collect()
    }
}

/// A caller's local: its entry, the block it is filled and handed on in,
/// and its offset in the frame.
type Local = (u64, u64, u64);

/// The locals callers hand their callees, gathered once before the rounds
/// of [`infer`].
#[derive(Default)]
struct Locals {
    /// The locals handed to each parameter.
    args: BTreeMap<ParamKey, Vec<Local>>,
    /// The classes a local holds a copy of: the classes the caller's own
    /// signature declares for the parameters it copied from.
    copies: BTreeMap<Local, BTreeSet<String>>,
}

impl Locals {
    /// Gathers the locals every scanned caller hands its callees, and the
    /// parameters each holds a copy of.
    ///
    /// # Arguments
    ///
    /// * `analysis` - The functions.
    /// * `scans` - Scans, with the locals each hands on and fills.
    fn gather(analysis: &Analysis, scans: &BTreeMap<u64, Scan>) -> Self {
        let mut out = Self::default();
        for (&entry, scan) in scans {
            for &(target, p, at, block) in &scan.frame_args {
                out.args
                    .entry((target, p))
                    .or_default()
                    .push((entry, block, at));
            }
            let Some(f) = analysis.function(entry) else {
                continue;
            };
            for &(at, n, block) in &scan.frame_copies {
                if let Some(class) = param_class(f, &BTreeMap::new(), n) {
                    out.copies
                        .entry((entry, block, at))
                        .or_default()
                        .insert(class);
                }
            }
        }
        out
    }
}

/// A callee's bound on a parameter handed to it.
enum Bounded {
    /// The class the callee's name or declared signature gives.
    Used(String),
    /// Whatever class the callee's parameter has.
    Given(ParamKey),
}

/// Returns the class a function's name gives and whether it is a member of
/// it, taking `this` first: not a static, and a declared signature leaves an
/// argument it reads undeclared, or is `const`.
///
/// PERF: the class is borrowed from the name; the rounds ask it of every
/// scan, and cloning each whole qualified name was a pass of its own.
///
/// # Arguments
///
/// * `f` - The function.
/// * `renames` - Names chosen by this pass.
/// * `statics` - Class-named functions whose first argument is not `this`.
/// * `scan` - Its scan.
///
/// # Returns
///
/// The class name and the member verdict, or `None` when the name gives no
/// class.
fn member_class<'a>(
    f: &'a Function,
    renames: &'a BTreeMap<u64, String>,
    statics: &'a BTreeSet<u64>,
    scan: &Scan,
) -> Option<(&'a str, bool)> {
    // INVARIANT: a rename wins over the symbol name even where the symbol
    // table gave none, so the None case is only reached without one.
    let name = match renames.get(&f.entry) {
        Some(renamed) => renamed.as_str(),
        None => f.name.as_deref()?,
    };
    let class = class_of(name)?;
    let member = !statics.contains(&f.entry)
        && match &f.signature {
            Some(sig) => {
                sig.is_const || scan.args_read > sig.params.len() + usize::from(sig.by_pointer)
            }
            None => true,
        };
    Some((class, member))
}

/// Returns a class and its ancestors, nearest first, up to
/// [`ANCESTORS_MAX`] parent links.
///
/// # Arguments
///
/// * `classes` - Classes with their parents.
/// * `class` - The class to start from.
fn ancestry(classes: &BTreeMap<String, ClassInfo>, class: &str) -> Vec<String> {
    let mut out = vec![class.to_owned()];
    let mut at = classes.get(class).and_then(|i| i.parent.clone());
    for _ in 0..ANCESTORS_MAX {
        let Some(p) = at else {
            break;
        };
        out.push(p.clone());
        at = classes.get(&p).and_then(|i| i.parent.clone());
    }
    out
}

/// Picks the calling convention's registers: where `this` arrives, what a
/// call may change and where the arguments travel.
///
/// # Arguments
///
/// * `program` - Its format selects the convention.
/// * `bitness` - 32 or 64.
fn conv_of(program: &Program, bitness: u32) -> Conv {
    if bitness == 32 {
        return Conv {
            this: Register::ECX,
            volatile: &X86_VOLATILE,
            args: &X86_ARGS,
        };
    }
    match program.format {
        BinaryFormat::Elf | BinaryFormat::MachO => Conv {
            this: Register::RDI,
            volatile: &SYSV_VOLATILE,
            args: &SYSV_ARGS,
        },
        BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => Conv {
            this: Register::RCX,
            volatile: &MS_VOLATILE,
            args: &MS_ARGS,
        },
    }
}

/// Splits a constructor or destructor name into its class and kind.
///
/// `A::B::B` and `A::B<T>::B` are constructors (a `_2` disambiguation
/// suffix from naming allowed), `A::B::~B` a destructor.
///
/// # Arguments
///
/// * `name` - A qualified function name.
///
/// # Returns
///
/// `(class, is_destructor)`, or `None` for any other method.
fn ctor_class(name: &str) -> Option<(&str, bool)> {
    let class = class_of(name)?;
    let method = name.get(class.len() + 2..)?;
    let last = last_component(class);
    let base = last.split('<').next().unwrap_or(last);
    if base.is_empty() {
        return None;
    }
    if let Some(rest) = method.strip_prefix('~') {
        return (rest == base).then_some((class, true));
    }
    let plain = method
        .rsplit_once('_')
        .filter(|(_, n)| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
        .map_or(method, |(m, _)| m);
    (method == base || plain == base).then_some((class, false))
}

/// Returns the last `::`-separated component of a qualified name, template
/// arguments kept with their component.
///
/// # Arguments
///
/// * `name` - The qualified name.
fn last_component(name: &str) -> &str {
    let mut depth = 0i32;
    let mut start = 0;
    let bytes = name.as_bytes();
    for (i, &c) in bytes.iter().enumerate() {
        match c {
            b'<' => depth += 1,
            b'>' if bytes.get(i.wrapping_sub(1)) != Some(&b'-') => depth -= 1,
            b':' if depth == 0 && i > 0 && bytes.get(i - 1) == Some(&b':') => start = i + 1,
            _ => {}
        }
    }
    name.get(start..).unwrap_or(name)
}

/// Scans functions across the cores ([`striped`]), each with
/// [`scan_function`]; the results are keyed by entry, so the order they
/// come in changes nothing.
///
/// # Arguments
///
/// * `program` - Bytes and sections.
/// * `functions` - The functions to scan.
/// * `bitness` - 32 or 64.
/// * `conv` - The calling convention's registers.
fn scan_all(
    program: &Program,
    functions: &[&Function],
    bitness: u32,
    conv: &Conv,
) -> Vec<(u64, Scan)> {
    striped(functions, |f| {
        (f.entry, scan_function(program, f, bitness, conv))
    })
    .into_iter()
    .flatten()
    .collect()
}

/// The register `r` stands for at `bitness`: its 64-bit self on 64-bit
/// code, the 32-bit one it aliases on 32-bit code.
///
/// # Arguments
///
/// * `r` - Any register.
/// * `bitness` - 32 or 64.
fn full_reg(r: Register, bitness: u32) -> Register {
    if bitness == 64 {
        r.full_register()
    } else {
        r.full_register32()
    }
}

/// Follows `this`, the incoming arguments and the table addresses loaded
/// into registers through a function's instructions in address order.
///
/// Each argument register starts as the parameter it carries, so a call
/// that passes a parameter straight on records which one, and a class
/// known for that parameter reaches the callee. The register `this` arrives
/// in is left to the `this` tracking, and a class that arrives by flow votes
/// beside the classes `this` carries.
/// A tail jump ([`tail_target`]) hands the argument registers to its target
/// as they stand, so it records them as a call does, apart until
/// [`settle_tails`] knows which ones the target reads.
///
/// # Arguments
///
/// * `program` - Bytes and sections.
/// * `f` - The function.
/// * `bitness` - 32 or 64.
/// * `conv` - The calling convention's registers.
fn scan_function(program: &Program, f: &Function, bitness: u32, conv: &Conv) -> Scan {
    let mut this: BTreeSet<Register> = BTreeSet::from([conv.this]);
    let mut vals: BTreeMap<Register, Tracked> = conv
        .args
        .iter()
        .enumerate()
        .filter(|(_, r)| **r != conv.this)
        .filter_map(|(i, r)| u8::try_from(i).ok().map(|n| (*r, Tracked::Param(n))))
        .collect();
    let blocks: Vec<Vec<Instruction>> = f
        .blocks
        .iter()
        .map(|b| decode_block(program, bitness, b))
        .collect();
    let mut scan = Scan {
        vararg_fixed: super::decompile::lift::vararg_fixed(
            program,
            bitness,
            blocks
                .iter()
                .flatten()
                .take(PROLOGUE_MAX)
                .take_while(|i| !matches!(i.flow_control(), FlowControl::Call)),
        ),
        ..Scan::default()
    };
    let mut info = InstructionInfoFactory::new();
    scan.args_read = entry_reads(f, &blocks, bitness, conv, &mut info);
    for (start, block) in f.blocks.iter().map(|b| b.start).zip(blocks) {
        // INVARIANT: a block laid out before the entry (code the function
        // shares with another, which it jumps back to) is reached with
        // registers the address-ordered scan did not follow there, so what
        // it hands its callees votes for no class and reads no argument.
        let early = start < f.entry;
        let marks = (
            scan.this_calls.len(),
            scan.calls.len(),
            scan.tail_this_calls.len(),
            scan.tail_calls.len(),
            scan.data_args.len(),
            scan.frame_args.len(),
            scan.frame_copies.len(),
        );
        let mut loaded: BTreeSet<Register> = BTreeSet::new();
        for instr in block {
            let before = scan.data_args.len();
            if let Some(target) = tail_target(f, &instr) {
                pass_args(target, conv.args, (&this, &vals), &mut scan, true);
            }
            step(
                program, &instr, bitness, conv, &mut this, &mut vals, &mut scan, &mut info,
            );
            let passed = scan.data_args.split_off(before);
            scan.data_args
                .extend(passed.into_iter().filter(|&(_, p, _)| {
                    conv.args
                        .get(usize::from(p))
                        .is_some_and(|r| loaded.contains(r))
                }));
            if instr.op0_kind() == OpKind::Register {
                let dst = full_reg(instr.op0_register(), bitness);
                let loads = match (instr.mnemonic(), instr.op1_kind()) {
                    (Mnemonic::Lea, OpKind::Memory) => instr.memory_base() == Register::RIP,
                    (Mnemonic::Mov, OpKind::Register) => {
                        loaded.contains(&full_reg(instr.op1_register(), bitness))
                    }
                    (
                        Mnemonic::Mov,
                        OpKind::Immediate64 | OpKind::Immediate32to64 | OpKind::Immediate32,
                    ) => true,
                    _ => false,
                };
                if loads {
                    loaded.insert(dst);
                } else {
                    loaded.remove(&dst);
                }
            }
        }
        if early {
            scan.this_calls.truncate(marks.0);
            scan.calls.truncate(marks.1);
            scan.tail_this_calls.truncate(marks.2);
            scan.tail_calls.truncate(marks.3);
            scan.data_args.truncate(marks.4);
            scan.frame_args.truncate(marks.5);
            scan.frame_copies.truncate(marks.6);
        }
        // INVARIANT: a frame slot holds one local within the block that
        // fills it and hands it on; another block may keep another one there.
        for arg in &mut scan.frame_args[marks.5..] {
            arg.3 = start;
        }
        for copy in &mut scan.frame_copies[marks.6..] {
            copy.2 = start;
        }
    }
    scan
}

/// Returns one past the highest argument position a function reads before
/// writing it, on some path from its entry.
///
/// The paths follow the blocks' successors from the entry block, so a block
/// laid out before the entry (code the function shares with another, which
/// it reaches after setting the register itself) is read in its place on
/// the path, and an instruction that reads a register it also writes
/// (`mov rcx, [rcx+10h]`) reads it first.
///
/// # Arguments
///
/// * `f` - The function.
/// * `blocks` - Its blocks' instructions, in the order of `f.blocks`.
/// * `bitness` - 32 or 64.
/// * `conv` - The calling convention's registers.
/// * `info` - Register-access facts.
fn entry_reads(
    f: &Function,
    blocks: &[Vec<Instruction>],
    bitness: u32,
    conv: &Conv,
    info: &mut InstructionInfoFactory,
) -> usize {
    let index: BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let Some(&first) = index.get(&f.entry) else {
        return 0;
    };
    let bit = |r: Register| {
        conv.args
            .iter()
            .position(|a| *a == r)
            .map(|pos| (pos, 1u32 << pos))
    };
    let mut read = 0;
    let mut seen: BTreeSet<(usize, u32)> = BTreeSet::new();
    let mut work = vec![(first, 0u32)];
    while let Some((b, mut written)) = work.pop() {
        if !seen.insert((b, written)) {
            continue;
        }
        for instr in blocks.get(b).into_iter().flatten() {
            // INVARIANT: MSVC reserves a word of 32-bit frame with `push
            // ecx`, in a function that takes no `this` as much as in one
            // that does, so pushing a whole register reads no argument.
            let makes_room = bitness == 32
                && instr.mnemonic() == Mnemonic::Push
                && instr.op0_kind() == OpKind::Register;
            let mut writes = 0u32;
            for ur in info.info(instr).used_registers() {
                let Some((pos, b)) = bit(full_reg(ur.register(), bitness)) else {
                    continue;
                };
                if matches!(
                    ur.access(),
                    OpAccess::Read
                        | OpAccess::CondRead
                        | OpAccess::ReadWrite
                        | OpAccess::ReadCondWrite
                ) && written & b == 0
                    && !makes_room
                {
                    read = read.max(pos + 1);
                }
                if matches!(
                    ur.access(),
                    OpAccess::Write
                        | OpAccess::ReadWrite
                        | OpAccess::CondWrite
                        | OpAccess::ReadCondWrite
                ) {
                    writes |= b;
                }
            }
            written |= writes;
        }
        let succs = f.blocks.get(b).map(|blk| blk.successors.as_slice());
        for s in succs.unwrap_or_default() {
            if let Some(&i) = index.get(s) {
                work.push((i, written));
            }
        }
    }
    read
}

/// Returns the function a jump leaves `f` for: a direct `jmp` or `jcc` to
/// one of its callees that starts none of its own blocks (a tail call,
/// which discovery records as a callee and does not follow).
///
/// # Arguments
///
/// * `f` - The function the jump belongs to.
/// * `instr` - The instruction.
///
/// # Returns
///
/// The target's entry, or `None` for any other instruction.
fn tail_target(f: &Function, instr: &Instruction) -> Option<u64> {
    if !matches!(
        instr.flow_control(),
        FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch
    ) || !matches!(
        instr.op0_kind(),
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
    ) {
        return None;
    }
    let target = instr.near_branch_target();
    (f.callees.binary_search(&target).is_ok()
        && f.blocks.binary_search_by_key(&target, |b| b.start).is_err())
    .then_some(target)
}

/// Records what the argument registers hold as a call or a tail jump to
/// `target` passes them.
///
/// `this` is recorded by position, a data address with its position
/// ([`Scan::data_args`]), a local a call hands on with its position
/// ([`Scan::frame_args`]; a tail jump leaves the frame), and any other
/// tracked value but part of a parameter's object with its position.
///
/// # Arguments
///
/// * `target` - The callee's entry.
/// * `args` - The argument registers, in order.
/// * `(this, vals)` - Registers holding `this`, and registers holding a
///   tracked value.
/// * `scan` - The facts collected so far.
/// * `tail` - A tail jump passes them, kept apart until [`settle_tails`].
fn pass_args(
    target: u64,
    args: &[Register],
    (this, vals): (&BTreeSet<Register>, &BTreeMap<Register, Tracked>),
    scan: &mut Scan,
    tail: bool,
) {
    for (p, r) in args.iter().enumerate() {
        let Ok(p) = u8::try_from(p) else {
            continue;
        };
        if this.contains(r) {
            let this_calls = if tail {
                &mut scan.tail_this_calls
            } else {
                &mut scan.this_calls
            };
            this_calls.push((target, p));
            continue;
        }
        match vals.get(r) {
            Some(Tracked::Table(addr)) => scan.data_args.push((target, p, *addr)),
            Some(Tracked::Frame(at)) => {
                if !tail {
                    scan.frame_args.push((target, p, *at, 0));
                }
            }
            Some(Tracked::Copied(..)) => {}
            Some(v) => {
                let calls = if tail {
                    &mut scan.tail_calls
                } else {
                    &mut scan.calls
                };
                calls.push((target, p, *v));
            }
            None => {}
        }
    }
}

/// Returns how many argument positions each scanned function reads.
///
/// They are the ones it reads itself before writing them
/// ([`Scan::args_read`]), and the ones it hands on untouched, by a call or
/// a tail jump, to a position its callee reads, over [`READ_LINKS_MAX`]
/// links.
///
/// A function that hands an argument on to a base method reads it as
/// surely as one that dereferences it; one that only leaves it in its
/// register while it calls something else does not.
///
/// # Arguments
///
/// * `scans` - Every scan, tail arguments not yet settled.
///
/// # Returns
///
/// One past the highest position read, by entry.
fn read_counts(scans: &BTreeMap<u64, Scan>) -> BTreeMap<u64, usize> {
    let mut reads: BTreeMap<u64, usize> = scans.iter().map(|(e, s)| (*e, s.args_read)).collect();
    for _ in 0..READ_LINKS_MAX {
        let mut grew = false;
        for (entry, scan) in scans {
            let passed = scan
                .this_calls
                .iter()
                .chain(&scan.tail_this_calls)
                .map(|&(t, p)| (t, p, 0u8))
                .chain(scan.calls.iter().chain(&scan.tail_calls).filter_map(
                    |&(t, p, ref v)| match v {
                        Tracked::Param(n) => Some((t, p, *n)),
                        _ => None,
                    },
                ));
            let mut count = reads.get(entry).copied().unwrap_or(0);
            for (target, p, n) in passed {
                if reads.get(&target).is_some_and(|&k| usize::from(p) < k) {
                    count = count.max(usize::from(n) + 1);
                }
            }
            if reads.get(entry).is_some_and(|&k| count > k) {
                reads.insert(*entry, count);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    reads
}

/// Keeps the arguments a tail jump passes where its target reads them,
/// moving them in with the calls.
///
/// A call sets the registers it passes, but a tail jump hands on whatever
/// they hold, `this` included when the caller never wrote over it, so a
/// register the target never reads ([`read_counts`]) passes nothing: a
/// class's static factory reached through a `jmp` thunk would otherwise
/// take the class of whoever jumped there. A target without a scan reads
/// nothing known and keeps nothing.
///
/// # Arguments
///
/// * `scans` - Every scan so far; each one's tail arguments are settled.
/// * `reads` - How many argument positions each function reads.
fn settle_tails(scans: &mut BTreeMap<u64, Scan>, reads: &BTreeMap<u64, usize>) {
    let reads = |target: u64, p: u8| reads.get(&target).is_some_and(|&n| usize::from(p) < n);
    for scan in scans.values_mut() {
        let this_calls = std::mem::take(&mut scan.tail_this_calls);
        scan.this_calls
            .extend(this_calls.into_iter().filter(|&(t, p)| reads(t, p)));
        let calls = std::mem::take(&mut scan.tail_calls);
        scan.calls
            .extend(calls.into_iter().filter(|&(t, p, _)| reads(t, p)));
    }
}

/// Advances the scan over one instruction.
///
/// A register copy carries `this` or a tracked value along; `lea` from
/// `rip` and a 64-bit immediate load a table address; `lea` from `this`
/// tracks the address of a field (an alias of `this` at offset 0); a word
/// load from a field of `this` tracks the field; a word store of a table register
/// through `this` with no displacement records the table; the stack pointer
/// and `lea` from it track a local, and a load through a parameter stored
/// into the frame records the local as a copy of what the parameter points
/// at; a call records the base constructor, the arguments holding `this`,
/// a call result, a field or a local, forgets the volatile registers and
/// tracks its own result in rax; any other write to a register forgets what
/// it held.
///
/// # Arguments
///
/// * `program` - Sections, to tell data addresses.
/// * `instr` - The instruction.
/// * `bitness` - 32 or 64.
/// * `conv` - The calling convention's registers.
/// * `this` - Registers holding `this`.
/// * `vals` - Registers holding a tracked value: a table address, a call
///   result, a word loaded from a field of `this`, a local or part of a
///   parameter's object.
/// * `scan` - The facts collected so far.
/// * `info` - Register-access facts.
#[expect(
    clippy::too_many_arguments,
    reason = "one scan state split into its parts"
)]
fn step(
    program: &Program,
    instr: &Instruction,
    bitness: u32,
    conv: &Conv,
    this: &mut BTreeSet<Register>,
    vals: &mut BTreeMap<Register, Tracked>,
    scan: &mut Scan,
    info: &mut InstructionInfoFactory,
) {
    let Conv {
        this: this_reg,
        volatile,
        args,
    } = *conv;
    let word = if bitness == 64 { 8 } else { 4 };
    if matches!(instr.flow_control(), FlowControl::Return) {
        let rax = full_reg(Register::RAX, bitness);
        match vals.get(&rax) {
            Some(Tracked::TlsSlot(off)) => scan.returns_tls = Some(*off),
            Some(Tracked::Result(callee)) => scan.returns_result = Some(*callee),
            Some(Tracked::Global(addr)) => scan.returns_global = Some(*addr),
            Some(Tracked::Field(off)) => scan.returns_field = Some(*off),
            _ => {}
        }
        return;
    }
    if matches!(
        instr.flow_control(),
        FlowControl::Call | FlowControl::IndirectCall
    ) {
        let direct = matches!(
            instr.op0_kind(),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
        );
        if scan.stores.is_empty()
            && scan.first_this_call.is_none()
            && this.contains(&this_reg)
            && direct
        {
            scan.first_this_call = Some(instr.near_branch_target());
        }
        if direct {
            pass_args(instr.near_branch_target(), args, (this, vals), scan, false);
        }
        for r in volatile {
            this.remove(r);
            vals.remove(r);
        }
        if direct {
            let rax = full_reg(Register::RAX, bitness);
            vals.insert(rax, Tracked::Result(instr.near_branch_target()));
        }
        return;
    }
    let is_mov = instr.mnemonic() == Mnemonic::Mov;
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && instr.segment_prefix() == Register::GS
        && instr.memory_base() == Register::None
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0x58
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::TlsArray);
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && vals.get(&instr.memory_base()) == Some(&Tracked::TlsArray)
        && instr.memory_index() != Register::None
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::TlsBlock);
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && vals.get(&instr.memory_base()) == Some(&Tracked::TlsBlock)
        && let Some(off) = memory_offset(instr, vals)
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::TlsSlot(off));
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && vals.get(&instr.memory_base()) == Some(&Tracked::TlsBlock)
        && let Some(off) = memory_offset(instr, vals)
    {
        if this.contains(&instr.op1_register()) {
            scan.tls_stores.push(off);
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && matches!(instr.memory_base(), Register::RIP | Register::None)
        && instr.memory_index() == Register::None
    {
        let target = global_target(instr);
        let src = instr.op1_register();
        if in_data(program, target) {
            if this.contains(&src) {
                scan.global_stores.push(target);
            } else if let Some(Tracked::Result(callee)) = vals.get(&src) {
                scan.global_result_stores.push((target, *callee));
            }
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && matches!(instr.memory_base(), Register::RIP | Register::None)
        && instr.memory_index() == Register::None
        && in_data(program, global_target(instr))
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::Global(global_target(instr)));
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Register
        && instr.op0_register().size() == word
    {
        let (dst, src) = (instr.op0_register(), instr.op1_register());
        if this.contains(&src) {
            this.insert(dst);
        } else {
            this.remove(&dst);
        }
        if matches!(src, Register::RSP | Register::ESP) {
            vals.insert(dst, Tracked::Frame(0));
            return;
        }
        match vals.get(&src).copied() {
            Some(v) => {
                vals.insert(dst, v);
            }
            None => {
                vals.remove(&dst);
            }
        }
        return;
    }
    if instr.mnemonic() == Mnemonic::Lea
        && instr.op0_kind() == OpKind::Register
        && instr.memory_index() == Register::None
    {
        let dst = instr.op0_register();
        let base = instr.memory_base();
        let tracked = if base == Register::RIP {
            let target = instr.ip_rel_memory_address();
            in_data(program, target).then_some(Tracked::Table(target))
        } else if this.contains(&base) {
            Some(Tracked::FieldAddr(instr.memory_displacement64()))
        } else if matches!(base, Register::RSP | Register::ESP) {
            Some(Tracked::Frame(instr.memory_displacement64()))
        } else if let Some(Tracked::Frame(at)) = vals.get(&base) {
            Some(Tracked::Frame(
                at.wrapping_add(instr.memory_displacement64()),
            ))
        } else {
            None
        };
        this.remove(&dst);
        match tracked {
            Some(Tracked::FieldAddr(0)) => {
                this.insert(dst);
                vals.remove(&dst);
            }
            Some(v) => {
                vals.insert(dst, v);
            }
            None => {
                vals.remove(&dst);
            }
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && matches!(
            instr.op1_kind(),
            OpKind::Immediate64 | OpKind::Immediate32to64 | OpKind::Immediate32
        )
    {
        let dst = full_reg(instr.op0_register(), bitness);
        this.remove(&dst);
        let imm = instr.immediate64();
        if in_data(program, imm) {
            vals.insert(dst, Tracked::Table(imm));
        } else {
            vals.insert(dst, Tracked::Const(imm));
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && instr.memory_index() == Register::None
        && instr.memory_base() != Register::RIP
        && this.contains(&instr.memory_base())
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::Field(instr.memory_displacement64()));
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0
        && this.contains(&instr.memory_base())
    {
        if let Some(Tracked::Table(p)) = vals.get(&instr.op1_register()) {
            scan.stores.push(*p);
        }
        return;
    }
    // INVARIANT: a constructor that inlines a base's initializing store
    // writes that base's table at `[this+off]`, an embedded subobject under
    // multiple inheritance, so the field at `off` holds an object of the
    // table's class; the store at offset 0 above is the class's own table.
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() != 0
        && this.contains(&instr.memory_base())
        && let Some(Tracked::Table(p)) = vals.get(&instr.op1_register())
    {
        scan.field_stores.push((instr.memory_displacement64(), *p));
        return;
    }
    // INVARIANT: 32-bit code stores the table without a register,
    // `mov dword [ecx], offset vtable`, which no 64-bit encoding can do;
    // the immediate is the table when it lies in data.
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && matches!(
            instr.op1_kind(),
            OpKind::Immediate32 | OpKind::Immediate32to64
        )
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0
        && this.contains(&instr.memory_base())
    {
        let imm = instr.immediate64();
        if in_data(program, imm) {
            scan.stores.push(imm);
        }
        return;
    }
    // INVARIANT: the 32-bit immediate form of an embedded base's store,
    // `mov dword [ecx+8], offset vtable`, as the register form above.
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && matches!(
            instr.op1_kind(),
            OpKind::Immediate32 | OpKind::Immediate32to64
        )
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() != 0
        && this.contains(&instr.memory_base())
    {
        // INVARIANT: `immediate64` leaves the memory displacement in the
        // bits above a 32-bit immediate, so the value is read through the
        // operand accessor, which goes by the operand's own kind.
        let imm = instr.immediate(1);
        if in_data(program, imm) {
            scan.field_stores.push((instr.memory_displacement64(), imm));
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0
        && matches!(vals.get(&instr.memory_base()), Some(Tracked::Result(_)))
    {
        if let Some(Tracked::Table(p)) = vals.get(&instr.op1_register()) {
            scan.result_stores.push(*p);
        }
        return;
    }
    // INVARIANT: a word or a vector loaded through a parameter and stored
    // into the frame copies the object the parameter points at into a
    // local, a temporary of that object's class.
    let moves = matches!(
        instr.mnemonic(),
        Mnemonic::Mov | Mnemonic::Movaps | Mnemonic::Movups | Mnemonic::Movdqa | Mnemonic::Movdqu
    );
    if moves
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.memory_index() == Register::None
        && let Some(Tracked::Param(n)) = vals.get(&instr.memory_base()).copied()
    {
        let dst = full_reg(instr.op0_register(), bitness);
        this.remove(&dst);
        vals.insert(dst, Tracked::Copied(n, instr.memory_displacement64()));
        return;
    }
    if moves
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && let Some(Tracked::Copied(n, from)) =
            vals.get(&full_reg(instr.op1_register(), bitness)).copied()
        && let Some(at) = match instr.memory_base() {
            Register::RSP | Register::ESP => Some(0),
            base => match vals.get(&base) {
                Some(Tracked::Frame(at)) => Some(*at),
                _ => None,
            },
        }
    {
        let local = at
            .wrapping_add(instr.memory_displacement64())
            .wrapping_sub(from);
        scan.frame_copies.push((local, n, 0));
        return;
    }
    // INVARIANT: an object built on the stack takes its table through the
    // frame, `mov [rsp+K], rax` after `lea rax, [table]`, or the immediate
    // itself on 32-bit; `this` is never the frame register, so the store
    // is nobody's field.
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.memory_index() == Register::None
        && matches!(
            instr.memory_base().full_register(),
            Register::RSP | Register::RBP
        )
        && !this.contains(&instr.memory_base())
    {
        let table = match instr.op1_kind() {
            OpKind::Register => match vals.get(&instr.op1_register()) {
                Some(Tracked::Table(p)) => Some(*p),
                _ => None,
            },
            OpKind::Immediate32 | OpKind::Immediate32to64 => {
                Some(instr.immediate64()).filter(|&imm| in_data(program, imm))
            }
            _ => None,
        };
        if let Some(p) = table {
            scan.local_stores.push(p);
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && this.contains(&instr.memory_base())
        && let Some(Tracked::Result(callee)) = vals.get(&instr.op1_register())
    {
        scan.field_result_stores
            .push((instr.memory_displacement64(), *callee));
        return;
    }
    for ur in info.info(instr).used_registers() {
        if matches!(
            ur.access(),
            OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite | OpAccess::ReadCondWrite
        ) {
            let r = full_reg(ur.register(), bitness);
            this.remove(&r);
            vals.remove(&r);
        }
    }
}

/// Returns the constant offset of a memory operand from its base: the
/// displacement plus an index register holding a tracked constant with
/// scale 1, or the displacement alone without an index.
///
/// # Arguments
///
/// * `instr` - The instruction with the memory operand.
/// * `vals` - Registers holding tracked values.
fn memory_offset(instr: &Instruction, vals: &BTreeMap<Register, Tracked>) -> Option<u64> {
    let disp = instr.memory_displacement64();
    let index = instr.memory_index();
    if index == Register::None {
        return Some(disp);
    }
    if instr.memory_index_scale() != 1 {
        return None;
    }
    match vals.get(&index) {
        Some(Tracked::Const(c)) => Some(disp.wrapping_add(*c)),
        _ => None,
    }
}

/// Returns the address a global-addressing memory operand names.
///
/// INVARIANT: with neither a base nor an index, the displacement is the
/// whole address, the only global-addressing form 32-bit code has
/// (`mov [0x403000], ecx`); 64-bit code addresses globals rip-relative.
///
/// # Arguments
///
/// * `instr` - The instruction with the memory operand.
fn global_target(instr: &Instruction) -> u64 {
    if instr.memory_base() == Register::RIP {
        instr.ip_rel_memory_address()
    } else {
        instr.memory_displacement64()
    }
}

/// Reads a vtable's slots.
///
/// Slots are consecutive words pointing into executable memory; the table
/// ends at the first word that is not, or (after the first slot) at a word
/// something references or another class's table starts at. A non-zero
/// word that is not code once the table is under way does not end it when
/// the table visibly resumes after it — the next word is code that nothing
/// else names — and the skipped word is kept as a `0` slot, so the byte
/// offsets of the methods after it stay their slot indexes; a zero is the
/// padding between tables, never a datum, and a first word that is not
/// code ends the table before it starts, because a run of data is no
/// vtable however it continues.
///
/// # Arguments
///
/// * `program` - Bytes and sections.
/// * `analysis` - Cross-references, which mark the next table's start.
/// * `vtables` - Known table starts.
/// * `va` - The table's address.
/// * `bitness` - 32 or 64.
///
/// # Returns
///
/// The slot words, `0` for every word of data read through; empty when the
/// first word is not code.
fn read_slots(
    program: &Program,
    analysis: &Analysis,
    vtables: &BTreeMap<u64, String>,
    va: u64,
    bitness: u32,
) -> Vec<u64> {
    let word = u64::from(bitness / 8);
    let mut slots = Vec::new();
    let mut data = 0;
    let mut at = va;
    while slots.len() < SLOTS_MAX {
        let Some(ptr) = read_word(program, at) else {
            break;
        };
        if !is_executable_va(program, ptr) {
            // INVARIANT: the word the table resumes at must be code and
            // must start nothing of its own, and the datum itself must be
            // unreferenced and carry a value, or the reading is eating a
            // neighbour, not a slot of this table.
            let next = at + word;
            let resumes = data < DATA_SLOTS_MAX
                && ptr != 0
                && !slots.is_empty()
                && !analysis.xrefs.contains_key(&at)
                && !analysis.xrefs.contains_key(&next)
                && !vtables.contains_key(&next)
                && read_word(program, next).is_some_and(|f| is_executable_va(program, f));
            if !resumes {
                break;
            }
            // INVARIANT: the datum keeps its slot as `0`, never a function
            // entry, so every index a byte offset names finds its method.
            slots.push(0);
            data += 1;
            at = next;
            continue;
        }
        if at != va && (analysis.xrefs.contains_key(&at) || vtables.contains_key(&at)) {
            break;
        }
        slots.push(ptr);
        at += word;
    }
    slots
}

/// One class whose virtual at a slot answers with a constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SlotConstant {
    /// Qualified class name.
    pub class: String,
    /// The function in the slot.
    pub entry: u64,
    /// The constant it returns.
    pub value: u64,
}

/// The constant a function returns when it is nothing but `mov eax, imm; ret`,
/// or `xor eax, eax; ret` for a zero.
///
/// A virtual that answers a class's fixed property compiles to exactly that;
/// anything longer is a computation and is not reported.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function's entry.
/// * `bitness` - Decoder bitness, `32` or `64`.
fn returned_constant(program: &Program, entry: u64, bitness: u32) -> Option<u64> {
    /// Longest encoding of the two instructions: `mov rax, imm64` and `ret`.
    const MAX_BYTES: usize = 11;
    let bytes = program
        .read_va(entry, MAX_BYTES)
        .or_else(|| program.read_va(entry, 6))?;
    let mut decoder = Decoder::with_ip(bitness, bytes, entry, DecoderOptions::NONE);
    let mut first = Instruction::default();
    let mut second = Instruction::default();
    decoder.decode_out(&mut first);
    decoder.decode_out(&mut second);
    if first.is_invalid() || second.is_invalid() || second.mnemonic() != Mnemonic::Ret {
        return None;
    }
    let to_rax = first.op0_kind() == OpKind::Register
        && first.op0_register().full_register() == Register::RAX;
    if !to_rax {
        return None;
    }
    match first.mnemonic() {
        Mnemonic::Mov
            if matches!(
                first.op1_kind(),
                OpKind::Immediate8
                    | OpKind::Immediate16
                    | OpKind::Immediate32
                    | OpKind::Immediate64
                    | OpKind::Immediate32to64
            ) =>
        {
            first.try_immediate(1).ok()
        }
        Mnemonic::Xor
            if first.op1_kind() == OpKind::Register
                && first.op1_register() == first.op0_register() =>
        {
            Some(0)
        }
        _ => None,
    }
}

/// Every recovered class whose virtual at `slot` returns a constant, with it.
///
/// A registry that maps an id to a class at start-up (the wire id a command
/// answers through one virtual, the type tag a message answers) is a table
/// no static read of the registry recovers cheaply, while the class itself
/// keeps the answer in the one virtual that returns a literal. Read across
/// every recovered class, that slot is the registry's table.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `slot` - The vtable index, zero-based.
///
/// # Returns
///
/// The classes in name order; empty when no class has such a virtual, or on
/// an architecture the decoder does not cover.
#[must_use]
pub fn slot_constants(program: &Program, analysis: &Analysis, slot: usize) -> Vec<SlotConstant> {
    let Some(bitness) = program.arch.bitness() else {
        return Vec::new();
    };
    analysis
        .classes
        .by_name
        .values()
        .filter_map(|c| {
            let entry = *c.slots.get(slot)?;
            let value = returned_constant(program, entry, bitness)?;
            Some(SlotConstant {
                class: c.name.clone(),
                entry,
                value,
            })
        })
        .collect()
}

/// One row of a protocol table: a class answering the slot with `value`,
/// and what the table's pass found for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SlotRow<T> {
    /// The constant the class answers the slot with.
    pub value: u64,
    /// The class.
    pub class: String,
    /// What the pass found for the class, when it found anything.
    pub found: Option<T>,
}

/// The classes answering `slot` with a constant whose name contains
/// `filter`, each with what `per` finds for it, worked out across the
/// cores and ordered by value, then class.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `slot` - The vtable index the constant sits in, zero-based.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `init` - Makes one worker's state.
/// * `per` - What the table shows for one class, over the worker's state.
pub(crate) fn slot_rows<S, T: Send>(
    program: &Program,
    analysis: &Analysis,
    slot: usize,
    filter: &str,
    init: impl Fn() -> S + Sync,
    per: impl Fn(&S, &SlotConstant) -> Option<T> + Sync,
) -> Vec<SlotRow<T>> {
    let q = filter.to_lowercase();
    let picked: Vec<SlotConstant> = slot_constants(program, analysis, slot)
        .into_iter()
        .filter(|c| q.is_empty() || c.class.to_lowercase().contains(&q))
        .collect();
    let found = striped_with(&picked, SLOT_ROWS_MIN, init, per);
    let mut rows: Vec<SlotRow<T>> = picked
        .into_iter()
        .zip(found)
        .map(|(c, found)| SlotRow {
            value: c.value,
            class: c.class,
            found: found.flatten(),
        })
        .collect();
    rows.sort_by(|a, b| a.value.cmp(&b.value).then_with(|| a.class.cmp(&b.class)));
    rows
}

/// Renders the classes answering `slot` with a constant as a `#`-headed
/// table, ordered by value, filtered by class name.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `slot` - The vtable index, zero-based.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn slot_constants_tsv(
    program: &Program,
    analysis: &Analysis,
    slot: usize,
    filter: &str,
    limit: usize,
) -> String {
    let q = filter.to_lowercase();
    let mut rows: Vec<SlotConstant> = slot_constants(program, analysis, slot)
        .into_iter()
        .filter(|r| q.is_empty() || r.class.to_lowercase().contains(&q))
        .collect();
    rows.sort_by(|a, b| a.value.cmp(&b.value).then_with(|| a.class.cmp(&b.class)));
    let total = rows.len();
    let shown = total.min(limit);
    let mut out =
        format!("# {total} classes answer virtual {slot} with a constant, showing {shown}\n");
    out.push_str("value\tclass\tfunction\n");
    for r in rows.into_iter().take(limit) {
        let _ = writeln!(out, "{:#x}\t{}\t{:#x}", r.value, r.class, r.entry);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{
        MS_VOLATILE, accessed_descriptors, ctor_class, returned_constant, tests_flag_bit,
        unname_inlined_signatures,
    };
    use crate::analysis::{Function, NameSource, Signature};
    use std::collections::BTreeMap;

    /// A function at `entry` named `name` by `source`, calling `callees`,
    /// declaring `params` when it has a signature.
    ///
    /// # Arguments
    ///
    /// * `entry` - Its entry.
    /// * `name` - Its name.
    /// * `source` - Where the name came from.
    /// * `callees` - What it calls.
    /// * `params` - Its declared parameters.
    fn named(
        entry: u64,
        name: &str,
        source: NameSource,
        callees: Vec<u64>,
        params: &[&str],
    ) -> Function {
        Function {
            entry,
            start: entry,
            end: entry + 1,
            instr_count: 1,
            blocks: Vec::new(),
            callees,
            callers: Vec::new(),
            name: Some(name.to_owned()),
            name_inferred: false,
            name_source: source,
            thunk: None,
            funclet: None,
            signature: Some(Signature {
                ret: "void".to_owned(),
                name: name.to_owned(),
                params: params.iter().map(|p| (*p).to_owned()).collect(),
                is_const: false,
                by_pointer: false,
            }),
            body_hash: 0,
            shape_hash: 0,
            returns_value: None,
            ret_width: None,
            ret_partial: None,
            ret_float: None,
            preserves_rax: false,
            hands_back_rdx: false,
            param_hints: BTreeMap::new(),
            ret_hint: None,
            stack_args: 0,
            stack_pop: 0,
        }
    }

    /// A table whose accessor alone hands out a named descriptor takes its
    /// name; two tables handing out one descriptor share an inherited
    /// accessor and neither does.
    ///
    /// # Panics
    ///
    /// When a table is named against the rule.
    #[test]
    fn a_descriptor_accessor_names_its_table() {
        let p = Program::raw_x64(&[
            0x48, 0x8d, 0x05, 0x00, 0x01, 0x00, 0x00, // ASM: lea rax, [rip+0x100] -> 0x1107
            0xc3, // ASM: ret
            0x48, 0x8d, 0x05, 0x00, 0x02, 0x00, 0x00, // ASM: lea rax, [rip+0x200] -> 0x120f
            0xc3, // ASM: ret
            0x48, 0x8d, 0x05, 0xf0, 0x00, 0x00, 0x00, // ASM: lea rax, [rip+0xf0] -> 0x1107
            0xc3, // ASM: ret
        ]);
        let names: BTreeMap<u64, String> =
            [(0x1107, "A".to_owned()), (0x120f, "B".to_owned())].into();
        let tables: BTreeMap<u64, Vec<u64>> = [
            (0x9000, vec![0x1000]),
            (0x9100, vec![0x1008]),
            (0x9200, vec![0x1010]),
        ]
        .into();
        let named = accessed_descriptors(&p, 64, &names, &tables);
        assert_eq!(named, [(0x9100, "B".to_owned())].into());
    }

    /// A signature name whose class the function reaches through a smart
    /// pointer came from an inlined method and is dropped; one whose
    /// parameters mention the class, or that no smart pointer reaches, stays.
    ///
    /// # Panics
    ///
    /// When a name is kept or dropped against the rule.
    #[test]
    fn signatures_of_methods_reached_through_a_pointer_are_dropped() {
        let ptr = "Core::Ptr<Messaging::DeleteItem>::operator ->";
        let mut fs = vec![
            named(0x10, ptr, NameSource::Signature, Vec::new(), &[]),
            named(
                0x20,
                "Messaging::DeleteItem::SetItem",
                NameSource::Signature,
                vec![0x10],
                &["const Util::Id<Game::GameItem> &"],
            ),
            named(
                0x30,
                "Messaging::DeleteItem::CopyFrom",
                NameSource::Signature,
                vec![0x10],
                &["const Core::Ptr<Messaging::DeleteItem> &"],
            ),
            named(
                0x40,
                "Messaging::DeleteItem::GetItem",
                NameSource::Signature,
                Vec::new(),
                &[],
            ),
        ];
        unname_inlined_signatures(&mut fs);
        let names: Vec<Option<&str>> = fs.iter().map(|f| f.name.as_deref()).collect();
        assert_eq!(
            names,
            vec![
                Some(ptr),
                None,
                Some("Messaging::DeleteItem::CopyFrom"),
                Some("Messaging::DeleteItem::GetItem"),
            ]
        );
        assert!(fs[1].signature.is_none());
    }
    use crate::isa::x86::Register;
    use crate::program::Program;

    /// A deleting destructor's test of its flag is found, also after the
    /// flag moved into a register a call keeps; a test of `this` or of a
    /// flag a call clobbered is not.
    ///
    /// # Panics
    ///
    /// When a verdict disagrees with the hand-assembled bytes.
    #[test]
    fn deleting_destructors_test_their_flag() {
        let p = Program::raw_x64(&[
            0x53, // ASM: push rbx
            0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
            0x8b, 0xda, // ASM: mov ebx, edx
            0xe8, 0x00, 0x00, 0x00, 0x00, // ASM: call next
            0xf6, 0xc3, 0x01, // ASM: test bl, 1
            0xc3, // ASM: ret
            0xe8, 0x00, 0x00, 0x00, 0x00, // ASM: call next
            0xf6, 0xc2, 0x01, // ASM: test dl, 1
            0xc3, // ASM: ret
            0xf6, 0xc1, 0x01, // ASM: test cl, 1
            0xc3, // ASM: ret
            0xf6, 0xc2, 0x01, // ASM: test dl, 1
            0xc3, // ASM: ret
        ]);
        assert!(tests_flag_bit(&p, 0x1000, Register::RDX, &MS_VOLATILE));
        assert!(!tests_flag_bit(&p, 0x1010, Register::RDX, &MS_VOLATILE));
        assert!(!tests_flag_bit(&p, 0x1019, Register::RDX, &MS_VOLATILE));
        assert!(tests_flag_bit(&p, 0x101d, Register::RDX, &MS_VOLATILE));
    }

    /// A two-instruction literal return is read; a zeroing xor is a zero;
    /// anything longer or loading memory is not a constant.
    ///
    /// # Panics
    ///
    /// When a reading disagrees with the hand-assembled bytes.
    #[test]
    fn constant_returns_are_read_and_computations_are_not() {
        let p = Program::raw_x64(&[
            0xb8, 0x60, 0x00, 0x00, 0x00, 0xc3, // ASM: mov eax, 0x60; ret
            0x31, 0xc0, 0xc3, // ASM: xor eax, eax; ret
            0x48, 0x8b, 0x01, 0xc3, // ASM: mov rax, [rcx]; ret
            0xb8, 0x60, 0x00, 0x00, 0x00, 0x90, 0xc3, // ASM: mov eax, 0x60; nop; ret
            0x48, 0xb8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11,
            0xc3, // ASM: mov rax, imm64; ret
        ]);
        assert_eq!(returned_constant(&p, 0x1000, 64), Some(0x60));
        assert_eq!(returned_constant(&p, 0x1006, 64), Some(0));
        assert_eq!(returned_constant(&p, 0x1009, 64), None);
        assert_eq!(returned_constant(&p, 0x100d, 64), None);
        assert_eq!(
            returned_constant(&p, 0x1014, 64),
            Some(0x1122_3344_5566_7788)
        );
    }

    /// Constructor and destructor names split into class and kind; other
    /// methods do not.
    ///
    /// # Panics
    ///
    /// When a split disagrees with its expectation.
    #[test]
    fn constructor_names_are_recognized() {
        assert_eq!(
            ctor_class("UI::BankWidget::BankWidget"),
            Some(("UI::BankWidget", false))
        );
        assert_eq!(
            ctor_class("UI::BankWidget::~BankWidget"),
            Some(("UI::BankWidget", true))
        );
        assert_eq!(
            ctor_class("Util::Dictionary<Util::String,Math::float4>::Dictionary"),
            Some(("Util::Dictionary<Util::String,Math::float4>", false))
        );
        assert_eq!(
            ctor_class("Math::vector3::vector3_2"),
            Some(("Math::vector3", false))
        );
        assert_eq!(ctor_class("UI::BankWidget::OnFrame"), None);
        assert_eq!(ctor_class("main"), None);
    }
}
