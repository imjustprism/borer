//! Naming from the tables: the methods each table introduces, the verdicts
//! tables share, own and base tables, descriptor accessors, and the names
//! a slot carries to every class that inherits it.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use super::scan::ctor_class;
use super::{ANCESTORS_MAX, ClassInfo, MS_VOLATILE};
use crate::analysis::classes::class_of;
use crate::analysis::{Analysis, Function, NameSource, single, unique_name};
use crate::fxmap::FxHashMap;
use crate::isa::x86::{Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register};
use crate::program::{BinaryFormat, Program};

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
pub(super) fn introducer(classes: &BTreeMap<String, ClassInfo>, class: &str, k: usize) -> String {
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
pub(super) fn name_vtable_slots(classes: &BTreeMap<String, ClassInfo>, functions: &mut [Function]) {
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
pub(super) fn share_slot_verdicts(
    classes: &BTreeMap<String, ClassInfo>,
    functions: &mut [Function],
) {
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
pub(super) fn own_and_base(
    stores: &[u64],
    tables: &BTreeMap<u64, Vec<u64>>,
) -> Option<(u64, Option<u64>)> {
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
pub(super) fn classify_tables(
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
/// (`rax->Base::vfunc_0()`), and the name says so:
/// `rax->GetRtti()`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `names` - Descriptor address to class name.
/// * `functions` - Functions, renamed in place.
pub(super) fn name_descriptor_accessors(
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
        if let Some(class) = crate::analysis::messages::returned_global(program, f.entry, bitness)
            .and_then(|g| names.get(&g))
        {
            f.name = Some(format!("{class}::{accessor}"));
            f.name_inferred = true;
            f.name_source = NameSource::Helper;
        }
    }
}

/// The class name each table's type accessor gives it: a slot whose whole
/// body hands out a named descriptor's address (`lea rax, [RTTI]; ret`).
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
pub(super) fn accessed_descriptors(
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
                .or_insert_with(|| crate::analysis::messages::returned_global(program, f, bitness));
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
/// with an inlined method of another class: a handler inlined `SetActor`
/// and was named `Other::SetActor`. The name is dropped, so the slot passes
/// name the function after the slot it fills.
///
/// # Arguments
///
/// * `classes` - Classes with their tables and parents.
/// * `functions` - Functions, unnamed in place.
pub(super) fn unname_foreign_signatures(
    classes: &BTreeMap<String, ClassInfo>,
    functions: &mut [Function],
) {
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
pub(super) fn unname_inlined_signatures(functions: &mut [Function]) {
    let reached: FxHashMap<u64, String> = functions
        .iter()
        .filter_map(|f| {
            let pointer = f.name.as_deref()?.strip_suffix("::operator ->")?;
            let class = crate::analysis::classes::smart_pointee(pointer)?;
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
pub(super) fn tests_flag_bit(
    program: &Program,
    entry: u64,
    flag: Register,
    volatile: &[Register],
) -> bool {
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
pub(super) fn destructor_slots(
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
pub(super) fn propagate_slot_names(
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
