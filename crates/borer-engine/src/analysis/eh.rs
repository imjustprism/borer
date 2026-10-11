//! C++ exception-handling metadata: the handler thunk a function registers,
//! its `FuncInfo`, and the funclets the runtime runs on the function's frame.
//!
//! A 32-bit MSVC function with destructors to run or a `catch` to enter
//! registers `__ehhandler$f`, a thunk of two instructions, `mov eax, offset
//! FuncInfo; jmp __CxxFrameHandler3`. The `FuncInfo` names an unwind map,
//! one action per state, and a try-block map whose handlers are the catch
//! clauses. Every action and handler is a funclet: code the runtime calls
//! with `ebp` set to the function's own frame, which the discovery walk
//! lists as a function of its own since a table points at it.

use std::collections::BTreeMap;

use crate::isa::{FlowControl, Mnemonic, OpKind, Register};

use super::{Analysis, Funclet, FuncletRole, NameSource, RefKind, bare_name, read_u32};
use crate::program::{Program, SymbolKind};

/// Lowest `FuncInfo` magic number `__CxxFrameHandler` accepts.
const MAGIC_MIN: u32 = 0x1993_0520;
/// Highest `FuncInfo` magic number written for 32-bit code.
const MAGIC_MAX: u32 = 0x1993_0522;
/// Most unwind states read from one function.
const STATES_MAX: u32 = 4096;
/// Most try blocks read from one function.
const TRY_BLOCKS_MAX: u32 = 1024;
/// Most catch clauses read from one try block.
const CATCHES_MAX: u32 = 64;
/// The frame handlers a thunk may jump to, by bare import name.
const HANDLERS: [&str; 4] = [
    "__CxxFrameHandler3",
    "___CxxFrameHandler3",
    "__CxxFrameHandler2",
    "__CxxFrameHandler",
];

/// Marks and names every funclet the exception metadata describes.
///
/// Each handler thunk names its `FuncInfo`, and the function whose
/// prologue takes the thunk's address is the parent. The thunk, the unwind
/// actions and the catch handlers become [`Function::funclet`]s of that
/// parent and are named after it: `parent::__ehhandler`,
/// `parent::__unwind_N`, `parent::__catch_T_K`, unless the program
/// carries a name for them.
///
/// A 64-bit function registers its handler in the unwind tables instead,
/// and the handler's data names the same funclets and the `__try` scopes'
/// as well; [`crate::unwind`] reads those, and they are marked and named
/// the same way: `parent::__filter_N`, `parent::__finally_N`,
/// `parent::__except_N`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The analysis to mark.
///
/// [`Function::funclet`]: super::Function::funclet
pub(super) fn infer(program: &Program, analysis: &mut Analysis) {
    let Some(bitness) = program.arch.bitness() else {
        return;
    };
    let mut phases = crate::timing::Phases::new();
    let found = match bitness {
        32 => found_x86(program, analysis, bitness),
        64 => found_x64(program, analysis),
        _ => return,
    };
    phases.mark("eh found");
    apply(analysis, &found);
    phases.mark("eh apply");
}

/// Lists the funclets the x64 unwind tables name, by entry.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The analysis, for which entries are functions.
fn found_x64(program: &Program, analysis: &Analysis) -> BTreeMap<u64, Funclet> {
    let mut found: BTreeMap<u64, Funclet> = BTreeMap::new();
    for f in crate::unwind::funclets(program) {
        if f.entry != f.parent
            && analysis.function(f.entry).is_some()
            && analysis.function(f.parent).is_some()
        {
            found.entry(f.entry).or_insert(Funclet {
                parent: f.parent,
                role: f.role,
            });
        }
    }
    found
}

/// Lists the funclets the 32-bit handler thunks name, by entry.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The analysis, for which entries are functions.
/// * `bitness` - Decoder bitness.
fn found_x86(program: &Program, analysis: &Analysis, bitness: u32) -> BTreeMap<u64, Funclet> {
    let mut found: BTreeMap<u64, Funclet> = BTreeMap::new();
    let entries: Vec<u64> = analysis.functions.iter().map(|f| f.entry).collect();
    for &entry in &entries {
        let Some(info) = handler_thunk(program, analysis, bitness, entry) else {
            continue;
        };
        let Some(parent) = analysis
            .xrefs_to(entry)
            .iter()
            .filter(|s| s.kind == RefKind::Data)
            .find_map(|s| s.from_entry)
            .filter(|&p| p != entry)
        else {
            continue;
        };
        found.entry(entry).or_insert(Funclet {
            parent,
            role: FuncletRole::Handler,
        });
        for (state, action) in unwind_actions(program, info) {
            if action != parent && analysis.function(action).is_some() {
                found.entry(action).or_insert(Funclet {
                    parent,
                    role: FuncletRole::Unwind(state),
                });
            }
        }
        for (block, clause, handler) in catch_handlers(program, info) {
            if handler != parent && analysis.function(handler).is_some() {
                found.entry(handler).or_insert(Funclet {
                    parent,
                    role: FuncletRole::Catch(block, clause),
                });
            }
        }
    }
    found
}

/// Marks and names the funclets found.
///
/// # Arguments
///
/// * `analysis` - The analysis to mark.
/// * `found` - Funclet entries and what they are.
fn apply(analysis: &mut Analysis, found: &BTreeMap<u64, Funclet>) {
    let names: BTreeMap<u64, String> = analysis
        .functions
        .iter()
        .map(|f| {
            (
                f.entry,
                f.name
                    .clone()
                    .unwrap_or_else(|| format!("sub_{:x}", f.entry)),
            )
        })
        .collect();
    for f in &mut analysis.functions {
        let Some(funclet) = found.get(&f.entry) else {
            continue;
        };
        f.funclet = Some(*funclet);
        // INVARIANT: a name the program carries wins; a number the vtable
        // pass or discovery gave loses to the parent's name.
        if f.name.is_some() && !f.name_inferred {
            continue;
        }
        let parent = names
            .get(&funclet.parent)
            .cloned()
            .unwrap_or_else(|| format!("sub_{:x}", funclet.parent));
        let suffix = match funclet.role {
            FuncletRole::Handler => "__ehhandler".to_owned(),
            FuncletRole::Unwind(state) => format!("__unwind_{state}"),
            FuncletRole::Catch(block, clause) => format!("__catch_{block}_{clause}"),
            FuncletRole::Filter(scope) => format!("__filter_{scope}"),
            FuncletRole::Finally(scope) => format!("__finally_{scope}"),
            FuncletRole::Except(scope) => format!("__except_{scope}"),
        };
        f.name = Some(format!("{parent}::{suffix}"));
        f.name_inferred = true;
        f.name_source = NameSource::Funclet;
    }
}

/// Reads the `FuncInfo` a handler thunk names.
///
/// The thunk is `mov eax, imm32; jmp handler`, the jump direct to an
/// import thunk of a frame handler or through its import slot, or to a
/// frame handler the program links in and so carries no name of, and the
/// record it names opens with a magic number the handler accepts. A jump
/// to anything named other than a frame handler is no such thunk.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The analysis, for the jump target's name.
/// * `bitness` - Decoder bitness.
/// * `entry` - The candidate thunk's entry.
///
/// # Returns
///
/// The `FuncInfo` address, or `None` when the function is not such a thunk.
fn handler_thunk(program: &Program, analysis: &Analysis, bitness: u32, entry: u64) -> Option<u64> {
    let load = super::functions::decode_at(program, bitness, entry)?;
    if load.mnemonic() != Mnemonic::Mov
        || load.op0_kind() != OpKind::Register
        || load.op0_register() != Register::EAX
        || load.op1_kind() != OpKind::Immediate32
    {
        return None;
    }
    let jump = super::functions::decode_at(program, bitness, load.next_ip())?;
    if !matches!(
        jump.flow_control(),
        FlowControl::UnconditionalBranch | FlowControl::IndirectBranch
    ) {
        return None;
    }
    // INVARIANT: the jump lands on the frame handler's import thunk, which
    // the walk may have folded into this one when nothing else reaches it,
    // so the thunk's own jump through the import slot is read as well.
    let handler = match jump.op0_kind() {
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
            let target = jump.near_branch_target();
            analysis
                .function(target)
                .and_then(|f| f.name.clone())
                .or_else(|| import_jump(program, bitness, target))
        }
        OpKind::Memory => import_jump(program, bitness, jump.ip()),
        _ => return None,
    };
    if handler.is_some_and(|h| !HANDLERS.contains(&bare_name(&h))) {
        return None;
    }
    let info = u64::from(load.immediate32());
    let magic = read_u32(program, info)? & 0x1fff_ffff;
    (MAGIC_MIN..=MAGIC_MAX).contains(&magic).then_some(info)
}

/// Names the import a `jmp [slot]` at `va` goes through.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The jump's address.
///
/// # Returns
///
/// The import's raw symbol name, or `None` when the instruction is not a
/// jump through an import slot.
fn import_jump(program: &Program, bitness: u32, va: u64) -> Option<String> {
    let jump = super::functions::decode_at(program, bitness, va)?;
    if jump.flow_control() != FlowControl::IndirectBranch
        || jump.op0_kind() != OpKind::Memory
        || jump.memory_base() != Register::None
        || jump.memory_index() != Register::None
    {
        return None;
    }
    let slot = jump.memory_displacement64();
    program
        .symbols
        .iter()
        .find(|s| s.kind == SymbolKind::Import && s.addr == slot)
        .map(|s| s.name.clone())
}

/// Lists the unwind map's actions: `(state, funclet)` for each state that
/// has one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `info` - The `FuncInfo` address.
fn unwind_actions(program: &Program, info: u64) -> Vec<(u32, u64)> {
    let Some(states) = read_u32(program, info.wrapping_add(4)) else {
        return Vec::new();
    };
    let Some(map) = read_u32(program, info.wrapping_add(8)).map(u64::from) else {
        return Vec::new();
    };
    (0..states.min(STATES_MAX))
        .filter_map(|state| {
            let entry = map.checked_add(u64::from(state) * 8)?;
            let action = read_u32(program, entry.checked_add(4)?)?;
            (action != 0).then_some((state, u64::from(action)))
        })
        .collect()
}

/// Lists the try-block map's catch handlers: `(try block, clause, funclet)`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `info` - The `FuncInfo` address.
fn catch_handlers(program: &Program, info: u64) -> Vec<(u32, u32, u64)> {
    let Some(blocks) = read_u32(program, info.wrapping_add(12)) else {
        return Vec::new();
    };
    let Some(map) = read_u32(program, info.wrapping_add(16)).map(u64::from) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for block in 0..blocks.min(TRY_BLOCKS_MAX) {
        let Some(entry) = map.checked_add(u64::from(block) * 20) else {
            break;
        };
        let (Some(catches), Some(handlers)) = (
            read_u32(program, entry.wrapping_add(12)),
            read_u32(program, entry.wrapping_add(16)).map(u64::from),
        ) else {
            continue;
        };
        for clause in 0..catches.min(CATCHES_MAX) {
            let Some(handler) = handlers
                .checked_add(u64::from(clause) * 16 + 12)
                .and_then(|at| read_u32(program, at))
            else {
                break;
            };
            if handler != 0 {
                out.push((block, clause, u64::from(handler)));
            }
        }
    }
    out
}
