//! Run-time type information many classes share costs the analysis no
//! more heap than one class's: a base list it decodes again and again is
//! held once.

use borer_engine::analysis::Analysis;
use borer_engine::num::from_usize;
use borer_engine::program::{Arch, Program, Section};

use super::{LOAD_HEAP_PER_BYTE, kept, measured, put32, serial};

/// Classes with a locator of their own.
const RTTI_CLASSES: usize = 2000;
/// Bytes of each class's own records: its table, locator, type descriptor
/// and, under [`Spread::OwnHierarchies`], hierarchy.
const RTTI_CLASS_BYTES: usize = 0x50;
/// Where the base class descriptors of [`Spread::OwnHierarchies`] start,
/// past the shared records, one every 0x20 bytes.
const BASES_AT: usize = 0x400;
/// Where their type descriptors start, one every 0x20 bytes.
const BASE_NAMES_AT: usize = 0xc00;
/// Where the base array of [`Spread::Sliding`] starts, past the shared
/// records: [`RTTI_CLASSES`] plus 64 entries.
const SLIDING_AT: usize = 0x1400;
/// Where its base class descriptors start, one every 0x20 bytes.
const SLIDING_BASES_AT: usize = 0x3800;

/// How the classes of [`rtti_classes`] share their run-time type
/// information.
#[derive(Clone, Copy)]
enum Spread {
    /// Every class names one hierarchy, whose base array names one base
    /// with a long name `entries - 1` times.
    OneBase,
    /// Each class names a hierarchy of its own, and every hierarchy names
    /// one base array of `entries - 1` distinct bases.
    OwnHierarchies,
    /// Each class names a hierarchy of its own whose base array starts one
    /// entry further into one long array: descriptor `j` names base `Sj`
    /// at offset `j`, so no two classes list the same bases.
    Sliding,
}

/// Builds a 32-bit image of [`RTTI_CLASSES`] classes whose run-time type
/// information shares its bases as `spread` says.
///
/// One function stores every class's table at `[ecx]`, so each table is
/// referenced; each table's locator names the class's own type.
///
/// # Arguments
///
/// * `entries` - The hierarchy's entries, the class's own first: 2 to 64.
/// * `spread` - How the classes share their hierarchy and bases.
fn rtti_classes(entries: u32, spread: Spread) -> Program {
    let code_len = 6 * RTTI_CLASSES + 0x20;
    let rdata_va = 0x401000 + from_usize(code_len).next_multiple_of(0x1000);
    let at = |off: usize| u32::try_from(rdata_va + from_usize(off)).unwrap_or(0);
    let shared = RTTI_CLASS_BYTES * RTTI_CLASSES;
    let (hierarchy, array, base, long) = (shared, shared + 0x10, shared + 0x110, shared + 0x130);
    let mut code = Vec::with_capacity(code_len);
    for i in 0..RTTI_CLASSES {
        code.extend([0xc7, 0x01]); // ASM: mov dword [ecx], table
        code.extend(at(RTTI_CLASS_BYTES * i + 4).to_le_bytes());
    }
    let slot = 0x401000 + u32::try_from(code.len() + 1).unwrap_or(0);
    code.push(0xc3); // ASM: ret
    code.extend([0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret
    code.resize(code_len, 0xcc);
    let slid = match spread {
        Spread::OneBase | Spread::OwnHierarchies => 0,
        Spread::Sliding => RTTI_CLASSES + 64,
    };
    let names_at = SLIDING_BASES_AT + 0x20 * slid;
    let mut rdata = vec![0u8; shared + names_at + 0x20 * slid + BASE_NAMES_AT + 0x20 * 64];
    let mut words = |off: usize, words: &[u32]| {
        for (k, w) in words.iter().enumerate() {
            put32(&mut rdata, off + 4 * k, *w);
        }
    };
    for i in 0..RTTI_CLASSES {
        let c = RTTI_CLASS_BYTES * i;
        let (own, first) = match spread {
            Spread::OneBase => (hierarchy, array),
            Spread::OwnHierarchies => (c + 0x38, array),
            Spread::Sliding => (c + 0x38, shared + SLIDING_AT + 4 * i),
        };
        words(c, &[at(c + 0x10), slot, slot, 0]);
        words(c + 0x10, &[0, 0, 0, at(c + 0x24), at(own)]);
        words(own, &[0, 0, entries, at(first)]);
    }
    for j in 0..slid {
        let descriptor = shared + SLIDING_BASES_AT + 0x20 * j;
        let named = shared + names_at + 0x20 * j;
        let mdisp = u32::try_from(j).unwrap_or(0);
        words(shared + SLIDING_AT + 4 * j, &[at(descriptor)]);
        words(descriptor, &[at(named), 0, mdisp, u32::MAX, 0]);
    }
    for k in 0..64 {
        let (descriptor, named) = (
            shared + BASES_AT + 0x20 * k,
            shared + BASE_NAMES_AT + 0x20 * k,
        );
        let entry = match spread {
            Spread::OneBase => base,
            Spread::OwnHierarchies | Spread::Sliding => descriptor,
        };
        words(array + 4 * k, &[at(entry)]);
        words(descriptor, &[at(named), 0, 0, u32::MAX, 0]);
    }
    words(base, &[at(long), 0, 0, u32::MAX, 0]);
    let mut name = |off: usize, text: &str| {
        rdata[off + 8..off + 8 + text.len()].copy_from_slice(text.as_bytes());
    };
    name(long, &format!(".?AV{}@@", "L".repeat(500)));
    for k in 0..64 {
        name(shared + BASE_NAMES_AT + 0x20 * k, &format!(".?AVB{k:02}@@"));
    }
    for j in 0..slid {
        name(shared + names_at + 0x20 * j, &format!(".?AVS{j:04}@@"));
    }
    for i in 0..RTTI_CLASSES {
        name(RTTI_CLASS_BYTES * i + 0x24, &format!(".?AVC{i:04}@@"));
    }
    let rdata_off = u64::try_from(code.len()).unwrap_or(0);
    let rdata_len = u64::try_from(rdata.len()).unwrap_or(0);
    let sections = vec![
        Section::mapped(".text", 0x401000, 0, rdata_off, false, true),
        Section::mapped(".rdata", rdata_va, rdata_off, rdata_len, false, false),
    ];
    code.extend(rdata);
    Program::raw(code, Arch::X86, 0x400000, Some(0x401000), sections)
}

/// Checks that a class keeps where its run-time type information lists
/// its bases, not the list, and that the list reads back with `bases`
/// entries.
///
/// # Arguments
///
/// * `p` - An image of [`rtti_classes`].
/// * `a` - Its analysis.
/// * `bases` - How many direct bases each class has.
fn assert_read_back(p: &Program, a: &Analysis, bases: usize) {
    use borer_engine::analysis::vtables::Bases;
    let first = a.classes.by_name.get("C0007").expect("a class");
    assert!(
        matches!(first.bases, Bases::Rtti { .. }),
        "{:?}",
        first.bases
    );
    assert_eq!(
        first.direct_bases(p).len(),
        bases,
        "{:?}",
        first.parent_name()
    );
    assert!(a.classes.by_name.len() >= RTTI_CLASSES);
}

/// Thousands of classes sharing one hierarchy whose base array repeats one
/// long-named base cost the analysis no more heap than one naming it once.
///
/// Each class keeps where its hierarchy sits and its parent, whose name
/// every class shares.
#[test]
fn classes_sharing_a_hierarchy_share_its_bases() {
    let _serial = serial();
    let analyzed = |entries: u32| {
        let p = rtti_classes(entries, Spread::OneBase);
        let (a, extra) = measured(|| Analysis::compute(&p));
        assert_read_back(&p, &a, 1);
        extra
    };
    let (once, repeated) = (analyzed(2), analyzed(64));
    assert!(
        repeated <= once + once / 10,
        "naming the base 63 times took {repeated} bytes of heap, once {once}"
    );
    println!("analysis heap: {once} bytes naming the base once, {repeated} naming it 63 times");
}

/// Thousands of classes each with a hierarchy of its own, all naming one
/// array of 63 distinct bases, cost the analysis no more heap than classes
/// sharing one hierarchy.
///
/// Held per class, the 63 links took 8.4 MB for this 177 KB file, 2.8
/// times what one shared hierarchy takes.
#[test]
fn classes_with_hierarchies_of_their_own_share_equal_bases() {
    let _serial = serial();
    let heap = |spread: Spread| {
        let p = rtti_classes(64, spread);
        let (a, extra) = measured(|| Analysis::compute(&p));
        (p, a, extra)
    };
    let (_, _, shared) = heap(Spread::OneBase);
    let (p, a, own) = heap(Spread::OwnHierarchies);
    println!("analysis heap: {shared} bytes under one hierarchy, {own} under one each");
    assert!(
        own <= shared + shared / 10,
        "hierarchies of their own took {own} bytes of heap, one shared {shared}"
    );
    assert_read_back(&p, &a, 63);
}

/// Thousands of classes whose hierarchies list sliding windows of one
/// long base array keep no more heap with 63 bases each than with one.
///
/// No two classes list the same bases, and the analysis keeps no list of
/// bases per class, only where the hierarchy sits and the parent. The
/// same image with one base each is the baseline: an image of shared
/// hierarchies holds other data, which the analysis indexes differently.
///
/// Holding each class's 63 links kept 7.6 MB against 2.6 MB with one base
/// each (2026-11-23).
#[test]
fn classes_with_sliding_base_arrays_keep_no_bases_each() {
    let _serial = serial();
    let held = |entries: u32| {
        let p = rtti_classes(entries, Spread::Sliding);
        let (a, held) = kept(|| Analysis::compute(&p));
        assert_read_back(&p, &a, usize::try_from(entries - 1).unwrap_or(0));
        held
    };
    let (one, all) = (held(2), held(64));
    println!("analysis kept: {one} bytes with one base each, {all} with 63");
    assert!(
        all <= one + one / 10,
        "63 sliding bases each kept {all} bytes of heap, one {one}"
    );
}

/// A graph about one class, every class's base array sliding, stays
/// within the load bar.
///
/// No two classes list the same bases; finding the class's children costs
/// four bytes a link, not a list of names per distinct list.
///
/// The names, one list per distinct list, took 3.5 MB for this 0.3 MB
/// file (2026-11-23).
#[test]
fn a_class_graph_over_sliding_base_arrays_stays_within_the_bar() {
    use borer_engine::analysis::render::{GRAPH_NODES_MAX, class_graph};
    let _serial = serial();
    let p = rtti_classes(64, Spread::Sliding);
    let a = Analysis::compute(&p);
    let (g, extra) = measured(|| class_graph(&p, &a, Some("C0007"), GRAPH_NODES_MAX));
    let g = g.expect("a graph");
    assert_eq!(g.nodes.len(), 64, "the class and its 63 parents");
    let size = p.bytes.len();
    println!("class graph: {extra} bytes of heap for a {size} byte file");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap"
    );
}

/// Most classes [`classes_sharing_their_bases`] builds.
const SHARING: usize = 16_384;
/// Heap a class graph may take per class it considers but does not draw.
///
/// That is its name in the lists of classes found and seen, and four
/// bytes for each of its at most 63 parent links, once as a parent and
/// once as a child. It measured 300 bytes about every class and 585 about
/// a base (2026-11-23).
const CLASS_GRAPH_BYTES: usize = 640;

/// Returns an analysis of `n` classes, each with the same 63 direct bases,
/// one shared list.
///
/// # Arguments
///
/// * `n` - How many classes.
fn classes_sharing_their_bases(n: usize) -> Analysis {
    use borer_engine::analysis::vtables::{Bases, ClassInfo, ParentEvidence, ParentLink};
    let bases: std::sync::Arc<[ParentLink]> = (0..63)
        .map(|k| ParentLink::at_start(format!("B{k:02}"), ParentEvidence::Rtti))
        .collect();
    let mut a = Analysis::default();
    for i in 0..n {
        let name = format!("C{i:05}");
        let info = ClassInfo {
            name: name.clone(),
            bases: Bases::Stated(std::sync::Arc::clone(&bases)),
            ..ClassInfo::default()
        };
        a.classes.by_name.insert(name, info);
    }
    a
}

/// A class graph of classes sharing 63 bases holds links only for the
/// nodes it draws and counts the rest.
///
/// About every class or about a base, past the 1024 nodes the cap draws,
/// each further class costs at most [`CLASS_GRAPH_BYTES`] of heap.
///
/// Built over every class first, the links of the graph of 16,384
/// classes took 113 MB, about 7 KB of heap per class.
#[test]
fn a_class_graph_of_classes_sharing_their_bases_holds_what_it_draws() {
    use borer_engine::analysis::render::{GRAPH_NODES_MAX, class_graph};
    let _serial = serial();
    let p = Program::raw(Vec::new(), Arch::X86, 0, None, Vec::new());
    for focus in [None, Some("B00")] {
        let heap = |n: usize| {
            let a = classes_sharing_their_bases(n);
            let (g, extra) = measured(|| class_graph(&p, &a, focus, GRAPH_NODES_MAX));
            let g = g.expect("a graph");
            let cut = g.cut.expect("the cap cuts");
            assert_eq!((g.nodes.len(), cut.edges_total), (GRAPH_NODES_MAX, 63 * n));
            extra
        };
        let (few, many) = (heap(SHARING / 4), heap(SHARING));
        println!(
            "class graph about {focus:?}: {few} bytes of heap, {many} for 4 times the classes"
        );
        let more = SHARING - SHARING / 4;
        assert!(
            many <= few + CLASS_GRAPH_BYTES * more,
            "{focus:?}: {many} bytes of heap for {SHARING} classes, {few} for a quarter"
        );
    }
}
