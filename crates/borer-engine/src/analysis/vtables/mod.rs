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

use std::collections::{BTreeMap, BTreeSet};

use crate::isa::x86::Register;

use super::classes::class_of;
use super::descriptors::unanimous;
use super::functions::string_at;
use super::naming::in_data;
use super::{Analysis, Function, NameSource, RefKind, single, unique_name};
use crate::program::Program;

mod constants;
mod hints;
mod members;
mod names;
mod scan;

use constants::read_slots;
pub(crate) use constants::slot_rows;
pub use constants::{SlotConstant, slot_constants, slot_constants_tsv};
pub(in crate::analysis) use hints::object_type;
use hints::{
    Bound, ValueHints, common_class, deepest_class, named_class, param_class, receiver_class,
    return_summaries, type_parts, value_hints,
};
use members::FirstMembers;
use names::{
    accessed_descriptors, classify_tables, destructor_slots, name_descriptor_accessors,
    name_vtable_slots, own_and_base, propagate_slot_names, share_slot_verdicts,
    unname_foreign_signatures, unname_inlined_signatures,
};
use scan::{
    Bounded, Inputs, Locals, ancestry, conv_of, ctor_class, member_class, read_counts, scan_all,
    scan_function, settle_tails,
};
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
    /// from the entry ([`entry_reads`](scan::entry_reads)).
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
    for (table, slots) in singles {
        if ctors_of.contains_key(&table)
            || creators_of.contains_key(&table)
            || on_stack.contains(&table)
        {
            tables.insert(table, slots);
        }
    }
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
    let fixed_slot = |target: u64, p: u8| varargs.get(&target).is_none_or(|&k| usize::from(p) < k);
    let typed_slot = |target: u64, p: u8| !literals.contains(&(target, p)) && fixed_slot(target, p);
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
    let mut widened: BTreeSet<(u64, u8)> = BTreeSet::new();
    let mut dirty = inputs.params();
    let mut last: BTreeMap<(u64, u8), Option<String>> = BTreeMap::new();
    let mut before_last: BTreeMap<(u64, u8), Option<String>> = BTreeMap::new();
    let mut settled = false;
    for round in 0..HINT_ROUNDS {
        if round > 0 {
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

#[cfg(test)]
mod tests {
    use super::MS_VOLATILE;
    use super::constants::returned_constant;
    use super::names::{accessed_descriptors, tests_flag_bit, unname_inlined_signatures};
    use super::scan::ctor_class;
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
            bound: None,
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
