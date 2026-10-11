//! The message catalog: every class that registered a four-character wire
//! id, with the fields it carries and the functions that test for its id.
//!
//! A message system dispatches on a class code: a sender fills a message
//! object and posts it, a handler compares the code it receives against the
//! one it wants. The classes and their codes come from the registrations the
//! analysis already found ([`ClassFacts::ids`](super::ClassFacts::ids));
//! the handlers are the functions whose code carries that four-byte
//! constant, found in one pass over the executable bytes; the fields are
//! the class's labelled ones ([`field_labels`]), which the setters inlined
//! into senders name.
//!
//! The functions carrying the constant are the registration and the id's
//! own accessors. The handlers are found through the id's home: a message
//! class answers its id from a virtual that returns a global's address
//! (`lea rax, [id]; ret`), a handler compares what it received against that
//! global, so the global's readers, the class's own methods left out, are
//! the functions that accept or handle the message.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::isa::{Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register};

use super::classes::{class_of, field_labels, fourcc};
use super::render::Legend;
use super::{Analysis, Overlay, dedup_sorted, name_of, single};
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::program::Program;

/// Fewest classes worth a worker each when the catalog is built.
const PAR_MIN: usize = 8;
/// Functions named per cell at most.
const HANDLERS_MAX: usize = 8;
/// Rows one answer lists at most; a filter narrows a catalog beyond it.
const PAGE: usize = 200;

/// What one cell of the catalog names: up to [`HANDLERS_MAX`] functions,
/// and how many more it left out.
type Named = (Vec<String>, usize);

/// One registered message class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MessageEntry {
    /// The four-character code, as registered.
    pub code: u32,
    /// The class.
    pub class: String,
    /// The class's labelled fields, by offset: a member's name, or the
    /// getter reading the field with its parentheses ([`field_labels`]).
    pub fields: BTreeMap<u64, String>,
    /// Entries of the functions carrying the code as a constant, the class's
    /// own methods left out, sorted.
    pub referrers: Vec<u64>,
    /// The global the class's id accessor returns the address of, when a
    /// virtual of the class is one.
    pub id_global: Option<u64>,
    /// Entries of the functions reading that global, the class's own methods
    /// and the accessor left out, sorted: what accepts or handles the message.
    pub handlers: Vec<u64>,
}

/// The global a function returns the address or the value of, when its body
/// is nothing but `lea rax, [g]; ret` or `mov eax, [g]; ret`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function's entry.
/// * `bitness` - Decoder bitness.
pub(crate) fn returned_global(program: &Program, entry: u64, bitness: u32) -> Option<u64> {
    /// Longest encoding of the two instructions.
    const MAX_BYTES: usize = 8;
    let bytes = program
        .read_va(entry, MAX_BYTES)
        .or_else(|| program.read_va(entry, 7))?;
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
    let rip_relative = first.op1_kind() == OpKind::Memory && first.memory_base() == Register::RIP;
    (to_rax && rip_relative && matches!(first.mnemonic(), Mnemonic::Lea | Mnemonic::Mov))
        .then(|| first.memory_displacement64())
}

/// Where a class keeps its id: the virtual handing it out, and the global
/// it hands out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IdHome {
    /// The id accessor's entry.
    accessor: u64,
    /// The global the accessor returns the address of.
    global: u64,
}

/// The global a class's id accessor returns, from the first of its virtuals
/// that returns a global the registration does not reference.
///
/// The type descriptor is also handed out by a virtual of that shape, and it
/// is what the registration passes along with the code, so a global any
/// carrier of the code references is the descriptor, not the id.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `class` - The qualified class name.
/// * `carriers` - Entries of the functions carrying the code as a constant.
///
/// # Returns
///
/// The accessor's entry and the global.
fn id_global(
    program: &Program,
    analysis: &Analysis,
    class: &str,
    carriers: &[u64],
) -> Option<IdHome> {
    let bitness = program.arch.bitness()?;
    let info = analysis.classes.by_name.get(class)?;
    info.slots
        .iter()
        .filter_map(|&accessor| {
            returned_global(program, accessor, bitness).map(|global| IdHome { accessor, global })
        })
        .find(|home| {
            !analysis
                .xrefs_to(home.global)
                .iter()
                .any(|site| site.from_entry.is_some_and(|e| carriers.contains(&e)))
        })
}

/// Entries of the functions referencing `global`, `accessor` and the
/// methods of `class` left out, sorted.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `global` - The id's home.
/// * `accessor` - The virtual that returns it.
/// * `class` - The message class.
fn readers_of(
    analysis: &Analysis,
    overlay: &Overlay,
    global: u64,
    accessor: u64,
    class: &str,
) -> Vec<u64> {
    let mut out: Vec<u64> = analysis
        .xrefs_to(global)
        .iter()
        .filter_map(|site| site.from_entry)
        .filter(|&e| e != accessor && class_of(&name_of(analysis, overlay, e)) != Some(class))
        .collect();
    dedup_sorted(&mut out);
    out
}

/// Every function carrying one of `codes` as a four-byte constant, by code.
///
/// One pass over the executable bytes at every alignment, so an immediate
/// in an instruction is found wherever it sits.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, for the function each hit lands in.
/// * `codes` - The codes to look for.
fn code_referrers(
    program: &Program,
    analysis: &Analysis,
    codes: &[u32],
) -> FxHashMap<u32, Vec<u64>> {
    let wanted: FxHashSet<u32> = codes.iter().copied().collect();
    let mut out: FxHashMap<u32, Vec<u64>> = FxHashMap::default();
    for section in program.sections.iter().filter(|s| s.executable) {
        let start = usize::try_from(section.file_off).unwrap_or(usize::MAX);
        let len = usize::try_from(section.file_size).unwrap_or(0);
        let Some(bytes) = program.bytes.get(start..start.saturating_add(len)) else {
            continue;
        };
        for (i, window) in bytes.windows(4).enumerate() {
            let Ok(word) = <[u8; 4]>::try_from(window) else {
                continue;
            };
            let code = u32::from_le_bytes(word);
            if !wanted.contains(&code) {
                continue;
            }
            let va = section.va.saturating_add(i as u64);
            if let Some(f) = analysis.function_at(va) {
                out.entry(code).or_default().push(f.entry);
            }
        }
    }
    for list in out.values_mut() {
        dedup_sorted(list);
    }
    out
}

/// The catalog: every registered class whose name contains `filter`, with
/// its fields and referrers, ordered by class name.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the registered codes.
/// * `overlay` - Names in force.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
#[must_use]
pub fn catalog(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    filter: &str,
) -> Vec<MessageEntry> {
    let q = filter.to_lowercase();
    let picked: Vec<(&String, &u32)> = analysis
        .classes
        .ids
        .iter()
        .filter(|(class, _)| q.is_empty() || class.to_lowercase().contains(&q))
        .collect();
    let codes: Vec<u32> = picked.iter().map(|(_, c)| **c).collect();
    let referrers = code_referrers(program, analysis, &codes);
    let referrers = &referrers;
    super::striped_with(
        &picked,
        PAR_MIN,
        || (),
        |(), &(class, &code)| {
            let carriers: &[u64] = referrers.get(&code).map_or(&[], Vec::as_slice);
            let home = id_global(program, analysis, class, carriers);
            MessageEntry {
                code,
                class: class.clone(),
                fields: field_labels(program, analysis, overlay, class)
                    .into_iter()
                    .map(|(off, label)| (off, label.to_string()))
                    .collect(),
                referrers: referrers
                    .get(&code)
                    .map(|entries| {
                        entries
                            .iter()
                            .copied()
                            .filter(|&e| {
                                class_of(&name_of(analysis, overlay, e)) != Some(class.as_str())
                            })
                            .collect()
                    })
                    .unwrap_or_default(),
                id_global: home.map(|h| h.global),
                handlers: home
                    .map(|h| readers_of(analysis, overlay, h.global, h.accessor, class))
                    .unwrap_or_default(),
            }
        },
    )
    .into_iter()
    .flatten()
    .collect()
}

/// Every registered class's id home, by class; a class that inherits its
/// parent's accessor shares its home.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the registered codes and classes.
fn id_accessors(program: &Program, analysis: &Analysis) -> Vec<(String, IdHome)> {
    let codes: Vec<u32> = analysis.classes.ids.values().copied().collect();
    let referrers = code_referrers(program, analysis, &codes);
    analysis
        .classes
        .ids
        .iter()
        .filter_map(|(class, code)| {
            let carriers: &[u64] = referrers.get(code).map_or(&[], Vec::as_slice);
            id_global(program, analysis, class, carriers).map(|home| (class.clone(), home))
        })
        .collect()
}

/// The class an id accessor belongs to among those that hold it: the one
/// whose parent does not hold it, so it introduced the accessor rather than
/// inheriting it; `None` when that is not exactly one.
///
/// # Arguments
///
/// * `classes` - The recovered classes.
/// * `holders` - The classes whose id accessor it is.
/// * `accessor` - The accessor's entry.
fn introducer<'a>(
    classes: &BTreeMap<String, super::vtables::ClassInfo>,
    holders: &[&'a str],
    accessor: u64,
) -> Option<&'a str> {
    single(holders.iter().copied().filter(|h| {
        classes
            .get(*h)
            .and_then(|c| c.parent.as_ref())
            .and_then(|p| classes.get(p))
            .is_none_or(|p| !p.slots.contains(&accessor))
    }))
}

/// The home of every registered class's id, the global its id accessor
/// hands out, mapped to the class, and the accessors by class.
///
/// A handler compares what it received against these globals
/// (`if (g32_1413744d4 == *(uint32_t*)msg->GetId())`), so naming each one
/// `Class::Id` says which message a branch is for. One pass over the
/// executable bytes finds the registrations, as for [`catalog`], and the
/// class's own virtuals the accessor. A home several registered classes
/// share belongs to the one that introduced its accessor.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the registered codes.
fn id_homes_and_accessors(
    program: &Program,
    analysis: &Analysis,
) -> (FxHashMap<u64, String>, BTreeMap<String, u64>) {
    let found = id_accessors(program, analysis);
    let mut by_home: BTreeMap<(u64, u64), Vec<&str>> = BTreeMap::new();
    for (class, home) in &found {
        by_home
            .entry((home.global, home.accessor))
            .or_default()
            .push(class);
    }
    let mut homes: FxHashMap<u64, String> = FxHashMap::default();
    let mut accessors: BTreeMap<String, u64> = BTreeMap::new();
    for ((global, acc), holders) in by_home {
        let owner = if let [one] = holders[..] {
            Some(one)
        } else {
            introducer(&analysis.classes.by_name, &holders, acc)
        };
        if let Some(owner) = owner {
            homes.insert(global, owner.to_owned());
            accessors.insert(owner.to_owned(), acc);
        }
    }
    (homes, accessors)
}

/// The home of every registered class's id: the global its id accessor
/// hands out, mapped to the class ([`id_homes_and_accessors`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the registered codes.
#[must_use]
pub fn id_homes(program: &Program, analysis: &Analysis) -> FxHashMap<u64, String> {
    id_homes_and_accessors(program, analysis).0
}

/// Names each registered class's id accessor `Class::GetId` where only its
/// vtable slot named it, and keeps the id homes for the text to name.
///
/// The accessor is a virtual whose whole body hands out the class's id
/// global, so a dispatch that asks a message for it (`rax->vfunc_3()`)
/// reads `rax->GetId()` and the branch after it compares against a named
/// `Class::Id`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with classes; accessors renamed in place.
pub(crate) fn name_id_accessors(program: &Program, analysis: &mut Analysis) {
    let (homes, accessors) = id_homes_and_accessors(program, analysis);
    let method = analysis.packs.name_for("class_id_accessor").to_owned();
    for (class, acc) in accessors {
        if let Some(f) = analysis.function_mut(acc)
            && (f.name.is_none() || f.name_source == super::NameSource::Slot)
        {
            f.name = Some(format!("{class}::{method}"));
            f.name_inferred = true;
            f.name_source = super::NameSource::Helper;
        }
    }
    analysis.derived.get_or_build("id_homes", (), || homes);
}

/// Renders the catalog as a `#`-headed table.
///
/// One row per class, tab-separated: the code as [`fourcc`] renders it
/// (its four characters quoted, or its value when a byte is unprintable),
/// the class, its named fields as `name@+offset`, the id global, the
/// handlers and the functions it is registered in, up to [`HANDLERS_MAX`]
/// names in a cell with `+N more` for the rest. A function named in two or
/// more cells of the page is numbered in a `# functions:` line and its
/// number stands in the cells ([`Legend`]). An answer lists [`PAGE`] rows
/// at most, whatever `limit` allows beyond, and the header says how many
/// classes matched, so a filter narrows a catalog the page does not fit.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `limit` - Rows shown at most, [`PAGE`] when it allows more.
#[must_use]
pub fn catalog_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    filter: &str,
    limit: usize,
) -> String {
    let all = analysis
        .derived
        .get_or_build_named("messages", overlay.fingerprint(), (), || {
            catalog(program, analysis, overlay, "")
        });
    let q = filter.to_lowercase();
    let entries: Vec<&MessageEntry> = all
        .iter()
        .filter(|e| q.is_empty() || e.class.to_lowercase().contains(&q))
        .collect();
    let total = entries.len();
    let shown = total.min(limit).min(PAGE);
    let named = |entries: &[u64]| -> Named {
        let names = entries
            .iter()
            .take(HANDLERS_MAX)
            .map(|&entry| name_of(analysis, overlay, entry))
            .collect();
        (names, entries.len().saturating_sub(HANDLERS_MAX))
    };
    let rows: Vec<(&MessageEntry, Named, Named)> = entries
        .iter()
        .take(shown)
        .map(|&e| (e, named(&e.handlers), named(&e.referrers)))
        .collect();
    let legend = Legend::of(
        rows.iter()
            .flat_map(|(_, handlers, referrers)| handlers.0.iter().chain(&referrers.0))
            .map(String::as_str),
    );
    let cell = |(names, more): &Named| -> String {
        let mut parts: Vec<String> = names.iter().map(|n| legend.cell(n)).collect();
        if *more > 0 {
            parts.push(format!("+{more} more"));
        }
        parts.join(" ")
    };
    let mut out = format!("# {total} classes registered a wire id");
    if !q.is_empty() {
        let _ = write!(out, " and match {}", crate::text::quoted(filter));
    }
    let _ = write!(out, ", showing {shown}");
    if shown < total {
        if shown == PAGE {
            let _ = write!(out, " ({PAGE} per answer)");
        }
        out.push_str("; borer://messages/<filter> narrows");
    }
    out.push('\n');
    out.push_str(&legend.line("functions"));
    out.push_str("code\tclass\tfields\tid\thandlers\tregistered_in\n");
    for (e, handlers, referrers) in &rows {
        let fields: Vec<String> = e
            .fields
            .iter()
            .map(|(off, name)| format!("{name}@+{off:#x}"))
            .collect();
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}\t{}\t{}",
            fourcc(e.code),
            e.class,
            fields.join(" "),
            e.id_global.map_or(String::new(), |g| format!("{g:#x}")),
            cell(handlers),
            cell(referrers)
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::vtables::ClassInfo;

    /// A shared id accessor belongs to the class that introduced it, not
    /// the one that inherits it; with no parent to tell them apart it
    /// belongs to neither.
    ///
    /// # Panics
    ///
    /// When the owner differs.
    #[test]
    fn a_shared_id_accessor_belongs_to_its_introducer() {
        let class = |name: &str, parent: Option<&str>, slots: &[u64]| {
            (
                name.to_owned(),
                ClassInfo {
                    name: name.to_owned(),
                    parent: parent.map(str::to_owned),
                    slots: slots.to_vec(),
                    ..ClassInfo::default()
                },
            )
        };
        let classes: BTreeMap<String, ClassInfo> = [
            class("Msg", None, &[0x10, 0x30]),
            class("Kill", Some("Msg"), &[0x10, 0x41]),
            class("KillAll", Some("Kill"), &[0x10, 0x41]),
            class("Loose", None, &[0x41]),
        ]
        .into();
        assert_eq!(
            introducer(&classes, &["Kill", "KillAll"], 0x41),
            Some("Kill")
        );
        assert_eq!(introducer(&classes, &["Kill", "Loose"], 0x41), None);
    }

    /// A code renders as its four characters quoted, or as its value when
    /// a byte is unprintable, since no text names that code exactly.
    ///
    /// # Panics
    ///
    /// When a rendering disagrees with its expectation.
    #[test]
    fn codes_render_as_four_characters_or_their_value() {
        assert_eq!(fourcc(0x4558_4954), "'EXIT'");
        assert_eq!(fourcc(0x4549_434f), "'EICO'");
        assert_eq!(fourcc(0x0158_4954), "0x01584954");
        assert_eq!(
            super::super::classes::code_or_hex(0x0158_4954),
            "0x01584954"
        );
        assert_eq!(super::super::classes::code_or_hex(0x4558_4954), "EXIT");
    }

    /// A name two cells share is numbered once in the legend and stands as
    /// its number in the cells; a name used once stays spelled out, and a
    /// page without a repeated name has no legend line.
    ///
    /// # Panics
    ///
    /// When the legend numbers the wrong names.
    #[test]
    fn a_legend_numbers_only_the_names_that_repeat() {
        let legend = Legend::of(["b", "a", "b", "c", "a"].into_iter());
        assert_eq!(legend.line("functions"), "# functions: 1=b 2=a\n");
        assert_eq!(legend.cell("b"), "1");
        assert_eq!(legend.cell("a"), "2");
        assert_eq!(legend.cell("c"), "c");
        assert_eq!(Legend::of(["x", "y"].into_iter()).line("functions"), "");
    }

    /// The one pass finds a code wherever it sits in executable bytes and
    /// names the function it lands in.
    ///
    /// # Panics
    ///
    /// When the scan disagrees with the hand-built image.
    #[test]
    fn referrers_are_found_at_any_alignment() {
        let p = Program::raw_x64(&[
            0x90, // ASM: nop
            0xb8, 0x54, 0x49, 0x58, 0x45, // ASM: mov eax, 0x45584954 ('EXIT')
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let hits = code_referrers(&p, &a, &[0x4558_4954, 0x1111_1111]);
        assert_eq!(hits.get(&0x4558_4954), Some(&vec![0x1000]));
        assert_eq!(hits.get(&0x1111_1111), None);
    }

    /// An accessor that is `lea rax, [g]; ret` names its global, one that
    /// loads the value does too, and anything longer does not.
    ///
    /// # Panics
    ///
    /// When a reading disagrees with the hand-assembled bytes.
    #[test]
    fn id_accessors_name_their_global() {
        let p = Program::raw_x64(&[
            0x48, 0x8d, 0x05, 0x09, 0x00, 0x00, 0x00, // ASM: lea rax, [rip+9]  -> 0x1010
            0xc3, // ASM: ret
            0x8b, 0x05, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, [rip+2] -> 0x1010
            0xc3, // ASM: ret
            0x90, 0x90, 0x90, 0x90, // ASM: nop x4 (the global at 0x1010)
            0x48, 0x8d, 0x05, 0x00, 0x00, 0x00, 0x00, // ASM: lea rax, [rip+0]
            0x90, // ASM: nop
            0xc3, // ASM: ret
        ]);
        assert_eq!(returned_global(&p, 0x1000, 64), Some(0x1010));
        assert_eq!(returned_global(&p, 0x1008, 64), Some(0x1010));
        assert_eq!(returned_global(&p, 0x1014, 64), None);
    }
}
