//! Candidate targets of an unresolved call, each admitted by a rule over
//! facts the analysis already holds; a candidate is never a caller.

use super::*;

/// Most bytes of code the stored-slot rule decodes for one census, over
/// every slot; stores past it are not read and admit no candidate.
const STORE_CODE_MAX: usize = 1 << 20;

/// Most instructions before a store searched for the one loading the
/// address it writes.
const STORE_WINDOW: usize = 16;

/// Fills each site's candidates and their total, kept to
/// [`CANDIDATES_MAX`] in address order.
///
/// A vtable slot's candidates are the functions every recovered class
/// holds in that slot; a global slot's are the
/// functions whose address a store into exactly that slot writes.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `sites` - The census's sites.
pub(super) fn fill(p: &Program, a: &Analysis, sites: &mut [Site]) {
    let slots: BTreeMap<usize, Admitted> = by_slot(a, sites)
        .into_iter()
        .map(|(slot, m)| {
            let rule = |class: &Arc<str>| Rule::VtableSlot {
                class: Arc::clone(class),
            };
            (slot, (m.len(), kept(&m, rule)))
        })
        .collect();
    let mut stored: BTreeMap<u64, Admitted> = BTreeMap::new();
    let mut fuel = STORE_CODE_MAX;
    for site in sites.iter_mut() {
        let admitted = match site.form {
            Form::VtableSlot { slot } => slots.get(&slot),
            Form::Global { slot } => Some(&*stored.entry(slot).or_insert_with(|| {
                let m = stores_into(p, a, slot, &mut fuel);
                (m.len(), kept(&m, |&store| Rule::StoredSlot { store }))
            })),
            Form::Register
            | Form::Field { .. }
            | Form::Memory
            | Form::IntoTrampoline { .. }
            | Form::Jump => None,
        };
        if let Some((total, kept)) = admitted {
            site.candidates_total = *total;
            site.candidates = Arc::clone(kept);
        }
    }
}

/// How many targets a rule admits at one slot, and the first
/// [`CANDIDATES_MAX`] of them, one list shared by every site calling
/// through that slot.
type Admitted = (usize, Arc<[Candidate]>);

/// Returns the first [`CANDIDATES_MAX`] targets a rule admitted, in
/// address order, each with its rule.
///
/// # Arguments
///
/// * `admitted` - Each target with what admitted it.
/// * `rule` - Spells what admitted a target as its rule.
fn kept<T>(admitted: &BTreeMap<u64, T>, rule: impl Fn(&T) -> Rule) -> Arc<[Candidate]> {
    admitted
        .iter()
        .take(CANDIDATES_MAX)
        .map(|(&target, why)| Candidate {
            target,
            rule: rule(why),
        })
        .collect()
}

/// Returns, for each vtable slot a site calls through, the functions the
/// recovered classes hold there, each with the first class by name that
/// holds it.
///
/// Each class's name is allocated once, however many sites name it.
///
/// # Arguments
///
/// * `a` - The analysis, for its classes and functions.
/// * `sites` - The census's sites.
fn by_slot(a: &Analysis, sites: &[Site]) -> BTreeMap<usize, BTreeMap<u64, Arc<str>>> {
    let wanted: BTreeSet<usize> = sites
        .iter()
        .filter_map(|s| match s.form {
            Form::VtableSlot { slot } => Some(slot),
            Form::Register
            | Form::Field { .. }
            | Form::Global { .. }
            | Form::Memory
            | Form::IntoTrampoline { .. }
            | Form::Jump => None,
        })
        .collect();
    let mut out: BTreeMap<usize, BTreeMap<u64, Arc<str>>> = BTreeMap::new();
    if wanted.is_empty() {
        return out;
    }
    for (class, info) in &a.classes.by_name {
        let mut name: Option<Arc<str>> = None;
        for (slot, &entry) in info.slots.iter().enumerate() {
            if wanted.contains(&slot) && a.function(entry).is_some() {
                out.entry(slot)
                    .or_default()
                    .entry(entry)
                    .or_insert_with(|| {
                        Arc::clone(name.get_or_insert_with(|| class.as_str().into()))
                    });
            }
        }
    }
    out
}

/// Returns the functions whose address a store into exactly `slot`
/// writes, each with its first store.
///
/// A store counts when its own block loads the address it writes, within
/// [`STORE_WINDOW`] instructions: `lea r, [f]` or `mov r, f` before `mov
/// [slot], r`, or `mov [slot], f` itself. Only x86 stores are read, each
/// block once per slot, while `fuel` (bytes of code) lasts.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `slot` - The slot's address.
/// * `fuel` - Bytes of code left to decode, spent here.
fn stores_into(p: &Program, a: &Analysis, slot: u64, fuel: &mut usize) -> BTreeMap<u64, u64> {
    let mut out = BTreeMap::new();
    let Some(crate::isa::Isa::X86 { bits }) = p.arch.isa() else {
        return out;
    };
    let mut at: Vec<(u64, u64)> = a
        .xrefs
        .get(&slot)
        .map_or(&[][..], Vec::as_slice)
        .iter()
        .filter(|s| s.kind == RefKind::Data)
        .filter_map(|s| Some((a.block_at(s.va)?.1.start, s.va)))
        .collect();
    at.sort_unstable();
    for run in at.chunk_by(|x, y| x.0 == y.0) {
        let Some((_, b)) = run.first().and_then(|&(_, va)| a.block_at(va)) else {
            continue;
        };
        let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(usize::MAX);
        let Some(left) = fuel.checked_sub(len) else {
            break;
        };
        *fuel = left;
        let insns = crate::analysis::functions::decode_block(p, bits, b);
        for &(_, va) in run {
            let Ok(i) = insns.binary_search_by_key(&va, Instruction::ip) else {
                continue;
            };
            let before = &insns[i.saturating_sub(STORE_WINDOW)..i];
            if let Some(f) = stored(before, &insns[i], slot)
                && a.function(f).is_some()
            {
                out.entry(f).or_insert(va);
            }
        }
    }
    out
}

/// Returns the address an x86 store into `slot` writes, when its block
/// shows it.
///
/// # Arguments
///
/// * `before` - The instructions before the store in its block, in order.
/// * `i` - The store.
/// * `slot` - The slot's address.
fn stored(before: &[Instruction], i: &Instruction, slot: u64) -> Option<u64> {
    let into = i.mnemonic() == Mnemonic::Mov
        && i.op0_kind() == OpKind::Memory
        && i.memory_index() == Register::None
        && if i.is_ip_rel_memory_operand() {
            i.ip_rel_memory_address() == slot
        } else {
            i.memory_base() == Register::None && i.memory_displacement64() == slot
        };
    if !into {
        return None;
    }
    if crate::analysis::is_imm(i.op1_kind()) {
        return Some(i.immediate(1));
    }
    if i.op1_kind() != OpKind::Register {
        return None;
    }
    let r = i.op1_register().full_register();
    let mut factory = InstructionInfoFactory::new();
    let w = before.iter().rfind(|n| reg_touch(&mut factory, n, r).1)?;
    match (w.mnemonic(), w.op1_kind()) {
        (Mnemonic::Lea, OpKind::Memory) if w.is_ip_rel_memory_operand() => {
            Some(w.ip_rel_memory_address())
        }
        (Mnemonic::Lea, OpKind::Memory)
            if w.memory_base() == Register::None && w.memory_index() == Register::None =>
        {
            Some(w.memory_displacement64())
        }
        (Mnemonic::Mov, kind) if crate::analysis::is_imm(kind) => Some(w.immediate(1)),
        _ => None,
    }
}
