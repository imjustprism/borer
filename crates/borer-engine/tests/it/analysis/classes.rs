//! Classes: vtables, constructors, descriptors, singletons, fields and layouts.

use super::*;

/// A TLS singleton reads as its class on both sides of a branch.
///
/// A runtime caches every manager in a thread-local block and reaches one as
/// `block[slot]`. The lifter folds such a read into the singleton's name, but
/// only while the block's register still carries the value inline: after a
/// branch, where the register has been written out and the join merges the
/// environments, the same access fell back to `*(uint64_t*)(0x58 + rbx)`.
/// On one client that left every manager unreadable.
///
/// The fixture loads the block, reads slot 0x58 before a branch and again
/// after the join; both must name the class.
#[test]
fn a_tls_singleton_reads_as_its_class_after_a_join() {
    let code: [u8; 41] = [
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x1c, 0xc8, 0xbf, 0x58,
        0x00, 0x00, 0x00, 0x48, 0x8b, 0x14, 0x1f, 0x48, 0x85, 0xd2, 0x74, 0x05, 0xe8, 0x08, 0x00,
        0x00, 0x00, 0x48, 0x8b, 0x04, 0x1f, 0x48, 0x01, 0xd0, 0xc3, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x2000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    let mut a = Analysis::compute(&p);
    a.classes.tls_slots.insert(0x58, "App::World".to_owned());
    let o = Overlay::default();
    let text =
        borer_engine::analysis::decompile::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(
        text.contains("App::World"),
        "the slot did not read as its singleton:\n{text}"
    );
    assert!(
        !text.contains("+ rbx") && !text.contains("rbx +"),
        "the slot still reads as a raw offset from the block:\n{text}"
    );
}

/// A virtual method no signature string named takes its slot's name.
///
/// `Base`'s table holds `Q` at slot 1 and no assert names it, so it becomes
/// `Base::vfunc_1` and every call to it reads that way.
#[test]
fn unnamed_vtable_slots_take_their_class_and_index() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let f = a.function(0x11e0).expect("the slot function");
    assert_eq!(f.name.as_deref(), Some("Base::vfunc_1"), "{:?}", f.name);
    assert!(f.name_inferred);
    assert_eq!(f.name_source, NameSource::Slot);
}

/// An assert that names a method does not name the field it reads.
///
/// `LKC` asserts `this->IsSet()`, so the field at 8 is what `IsSet` reads,
/// not a member called `IsSet`; rendering it `this->IsSet()` would put a
/// call in the text where the code reads memory, so it stays an offset.
#[test]
fn a_method_named_in_an_assert_does_not_name_a_field() {
    use borer_engine::analysis::classes::field_names;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let names = field_names(&p, &a, &o, "Lk");
    assert!(names.is_empty(), "a method is not a member: {names:?}");
}

/// A class's fields read the same in every answer that labels them.
///
/// `Lk::Chk`'s only assert reads the field at 8 through `this->IsSet()`, so
/// the layout and the field's typed uses both label it by that getter,
/// `IsSet()`, while the decompiler's member names leave it out (see the
/// test above). `Arr<char>`'s field at 8 is `size` by its template
/// sibling's assert, in its layout as in its member names.
#[test]
fn a_field_reads_the_same_label_in_every_answer() {
    use borer_engine::analysis::classes::{
        class_layout, field_names, render_layout, typed_field_uses,
    };
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let lk = render_layout(&class_layout(&p, &a, &o, "Lk").expect("Lk"), &a, &o);
    assert!(
        lk.lines()
            .any(|l| l.starts_with("+0x8 ") && l.contains(" IsSet() ")),
        "{lk}"
    );
    let uses = typed_field_uses(&p, &a, &o, "Lk", 8).expect("Lk is a class");
    assert_eq!(uses.name.as_deref(), Some("IsSet()"));
    let arr = render_layout(
        &class_layout(&p, &a, &o, "Arr<char>").expect("Arr<char>"),
        &a,
        &o,
    );
    assert!(
        arr.lines()
            .any(|l| l.starts_with("+0x8 ") && l.contains(" size ")),
        "{arr}"
    );
    assert_eq!(
        field_names(&p, &a, &o, "Arr<char>")
            .get(&8)
            .map(String::as_str),
        Some("size")
    );
}

/// A template's instantiations pool the names their asserts give.
///
/// `Arr<char>`'s one method asserts nothing, but `Arr<int>` proves the same
/// template puts `size` at 8, and every instantiation of a template that
/// holds its elements by pointer lays them out the same way.
#[test]
fn instantiations_share_the_field_names_of_their_template() {
    use borer_engine::analysis::classes::field_names;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        field_names(&p, &a, &o, "Arr<int>")
            .get(&8)
            .map(String::as_str),
        Some("size"),
        "the instantiation that asserts names its own field"
    );
    assert_eq!(
        field_names(&p, &a, &o, "Arr<char>")
            .get(&8)
            .map(String::as_str),
        Some("size"),
        "the one that does not takes the name from its sibling"
    );
}

/// A class's field labels follow the names in force: asked again after a
/// rename, the class answers what a fresh session asked once would.
///
/// `Arr<char>` takes `size` at 8 from its template sibling `Arr<int>::Add`.
/// Renamed out of the template, the sibling names nothing; with the rename
/// dropped it names `size` again, though `Arr<char>`'s own methods never
/// changed.
#[test]
fn field_labels_follow_the_names_in_force() {
    use borer_engine::analysis::classes::{FieldLabel, field_labels};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut renamed = Overlay::default();
    renamed.names.insert(0x4e50, "Other::Add".to_owned());
    let label = |o: &Overlay| field_labels(&p, &a, o, "Arr<char>").remove(&8);
    assert_eq!(label(&renamed), None, "no sibling names the field");
    let fresh = field_labels(&p, &Analysis::compute(&p), &Overlay::default(), "Arr<char>");
    assert_eq!(fresh.get(&8), Some(&FieldLabel::Member("size".to_owned())));
    assert_eq!(label(&Overlay::default()).as_ref(), fresh.get(&8));
}

/// One function's field accesses come back keyed by base and offset.
///
/// `CM` reads `[rcx+0x10]`, `[rcx+0x14]` and `[rcx+0x18]` as 32-bit fields off
/// its first argument, so `fields_tsv` reports three read rows at those offsets
/// with a 4-byte width. This is the per-function offset table an SDK checks its
/// `@derive` anchors against.
#[test]
fn field_accesses_of_a_function_list_offset_width_and_direction() {
    use borer_engine::analysis::classes::{field_accesses, fields_tsv};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let sites = field_accesses(&p, &a, &o, 0x5200).expect("CM decompiles");
    let base = sites
        .keys()
        .find(|(_, off)| *off == 0x10)
        .map(|(b, _)| b.clone())
        .expect("a field at 0x10");
    for off in [0x10u64, 0x14, 0x18] {
        let site = sites
            .get(&(base.clone(), off))
            .unwrap_or_else(|| panic!("no field {off:#x}: {sites:?}"));
        assert!(
            site.widths.contains(&32),
            "field {off:#x} not 32-bit: {site:?}"
        );
        assert!(
            site.reads > 0 && site.writes == 0,
            "field {off:#x} not a read: {site:?}"
        );
    }
    let tsv = fields_tsv(&p, &a, &o, 0x5200).expect("CM decompiles");
    assert!(
        tsv.contains(&format!("{base}\t0x10\t4\tr")),
        "tsv row missing:\n{tsv}"
    );
}

/// The recovered singletons list the class kept at each thread-local slot.
///
/// `Tls::Tls` registers its instance at a thread-local slot, so the singleton
/// registry names that class at a `tls` row. This is the program's global
/// object model — which one-of-a-kind objects it keeps and where.
#[test]
fn singletons_list_the_class_at_each_thread_local_slot() {
    use borer_engine::analysis::render::singletons_tsv;
    let p = fixture();
    let a = Analysis::compute(&p);
    let out = singletons_tsv(&a, &Overlay::default(), "");
    assert!(out.starts_with("# "), "no header:\n{out}");
    assert!(
        out.lines()
            .any(|l| l.starts_with("tls\t") && l.ends_with("Tls")),
        "the thread-local singleton was not recovered:\n{out}"
    );
    let filtered = singletons_tsv(&a, &Overlay::default(), "tls");
    assert!(
        filtered.contains("\tTls\n"),
        "filter dropped the match:\n{filtered}"
    );
}

/// A pointer to a function in data is a reference to it.
///
/// `Der`'s table at 0x22a0 holds `0x1870` in its first slot, and a virtual
/// method is reached that way and no other; without the tables, asking what
/// reaches it answers nothing.
#[test]
fn a_pointer_table_slot_references_the_function_it_holds() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let sites = a.xrefs_to(0x1870);
    let slot = sites
        .iter()
        .find(|s| s.kind == RefKind::Table)
        .expect("the table slot is a reference");
    assert_eq!(slot.va, 0x22a0);
    assert_eq!(slot.from_entry, None, "a table slot is data, not a caller");
}

/// A float field keeps its width when a wider store covers it.
///
/// `Fz::Set` zeroes eight bytes over the float at 0x10 and the one after
/// it, which is what a constructor does; taking the widest access would
/// call a four-byte float a double.
#[test]
fn a_float_field_is_not_widened_by_a_zeroing_store() {
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let fz = class_layout(&p, &a, &o, "Fz").expect("Fz layout");
    let text = render_layout(&fz, &a, &o);
    assert!(text.contains("+0x10   float"), "{text}");
}

/// The functions using a class's field are the ones holding a pointer typed
/// as the class, not every instruction at the offset.
///
/// `Der`'s field at 8 is read by `Der::Chk` through `this`, by `HT` through
/// the parameter its caller hinted `Der *`, by `Der2::Foo` through a derived
/// `this`, and copied by `Der::Cmp` from its `Der *` parameter into `this`.
/// `Cls::Set` writes and `Cls::Has` reads `[rcx+8]` too, of another class,
/// and stay out. Each row carries the instructions it was found at.
#[test]
fn a_class_field_lists_the_functions_using_it_through_a_typed_pointer() {
    use borer_engine::analysis::classes::{typed_field_uses, typed_field_uses_tsv};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let uses = typed_field_uses(&p, &a, &o, "Der", 8).expect("Der is a class");
    let rows: Vec<(u64, Vec<&str>, usize, usize)> = uses
        .uses
        .iter()
        .map(|u| {
            (
                u.entry,
                u.via.iter().map(String::as_str).collect(),
                u.field.reads,
                u.field.writes,
            )
        })
        .collect();
    assert_eq!(
        rows,
        vec![
            (0x1740, vec!["this"], 1, 0),
            (0x18d0, vec!["a1"], 1, 0),
            (0x19a0, vec!["this"], 1, 0),
            (0x19d0, vec!["a2", "this"], 1, 1),
        ],
        "{uses:?}"
    );
    assert_eq!(uses.derived, vec!["Der2".to_owned()]);
    assert_eq!(uses.name.as_deref(), Some("count"));
    let cmp = uses.uses.last().expect("Der::Cmp uses the field");
    assert_eq!(cmp.sites, vec![0x19d0, 0x19d3], "the load and the store");
    let tsv = typed_field_uses_tsv(&uses, &a, &o, 8, 0, 10, false);
    assert!(
        tsv.starts_with("# Der+0x8 count: 4 functions use it through a pointer typed as the class (a method's object, a typed parameter, a smart pointer's operator ->) or as a class derived from it (Der2): 1 stores, 4 loads, 0 address-takens, showing 4 from 0
"),
        "{tsv}"
    );
    assert!(tsv.contains("0x19d0	Der::Cmp	a2,this	rw	"), "{tsv}");
    assert!(!tsv.contains("Cls::"), "another class's field at 8: {tsv}");
}

/// A class registration records the code that identifies it on the wire.
///
/// `RG` hands a registrar `"Zz::Thing"` and `0x41424344`; without the code
/// a recovered message format has no name a reader could match a packet to.
#[test]
fn a_class_registration_records_its_wire_id() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(a.classes.ids.get("Zz::Thing").copied(), Some(0x4142_4344));
}

/// The registry lists every class that carries a wire code.
///
/// An agent asking what a four-character code in a packet belongs to, or
/// what code a class travels under, reads one table instead of decompiling
/// the registrar. `RG` registers `Zz::Thing` as `'ABCD'`.
#[test]
fn the_class_registry_lists_a_registered_class() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let all = borer_engine::analysis::render::class_ids_tsv(&a, "");
    assert!(all.contains("Zz::Thing"), "{all}");
    assert!(all.contains("'ABCD'"), "{all}");
    let row = all
        .lines()
        .find(|l| l.ends_with("Zz::Thing"))
        .expect("the registered class has a row");
    assert!(
        row.starts_with("'ABCD'\t") && row.split('\t').count() == 4,
        "a row is the code, the method count, the first method and the class, tab-separated: {row}"
    );
    assert!(all.contains("# code\tmethods\tfirst\tclass\n"), "{all}");
    let filtered = borer_engine::analysis::render::class_ids_tsv(&a, "abcd");
    assert!(filtered.contains("Zz::Thing"), "{filtered}");
    assert!(
        !borer_engine::analysis::render::class_ids_tsv(&a, "nothinghere").contains("Zz::Thing"),
        "the filter let everything through"
    );
}

/// The source tree groups the functions by the file that asserts.
///
/// A reader opening an unknown binary asks which subsystems it was built
/// from before asking about any function. The fixture cites
/// `C:\ws\code\foundation\util/fourcc.h` and `src/ah.cc`, and the build
/// root the first carries is dropped.
#[test]
fn the_source_tree_groups_functions_by_file() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let dirs = borer_engine::analysis::render::source_tree_tsv(&p, &a, "");
    assert!(dirs.contains("directory"), "{dirs}");
    assert!(dirs.contains("fourcc.h") || dirs.contains("util"), "{dirs}");
    assert!(
        dirs.contains("# base: C:/\n"),
        "the build root is written once: {dirs}"
    );
    let files = borer_engine::analysis::render::source_tree_tsv(&p, &a, "fourcc");
    assert!(files.contains("fourcc.h"), "{files}");
    assert!(
        files.contains("# base: C:/\n"),
        "the build root is written once: {files}"
    );
    assert!(
        files
            .lines()
            .any(|l| l.ends_with("\tws/code/foundation/util/fourcc.h")
                && l.starts_with(|c: char| c.is_ascii_digit())
                && l.split('\t').count() == 3),
        "a row is the functions, the first and the file, tab-separated: {files}"
    );
    assert!(
        !files
            .lines()
            .any(|l| !l.starts_with('#') && l.contains("C:/ws")),
        "the build root is still in a row: {files}"
    );
}

/// The assertion index says which classes name a field.
///
/// A reader who meets `state` in one class wants the others that call a
/// field by that name, which the assertions say and no symbol does. `AS`
/// asserts `this->head`, `GG` asserts `this->tail`.
#[test]
fn the_assertion_index_lists_a_named_field() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let all = borer_engine::analysis::render::asserted_fields_tsv(&p, &a, &o, "");
    assert!(all.contains("head") || all.contains("tail"), "{all}");
    let one = borer_engine::analysis::render::asserted_fields_tsv(&p, &a, &o, "tail");
    assert!(one.contains("tail"), "{one}");
    assert!(
        one.contains("this->tail"),
        "the filtered listing does not say what is asserted: {one}"
    );
    assert!(
        one.lines()
            .any(|l| l.starts_with(|c: char| c.is_ascii_digit())
                && l.contains("\ttail\t")
                && l.split('\t').count() == 3),
        "a row is the functions, the field and the classes, tab-separated: {one}"
    );
    assert!(
        one.lines()
            .any(|l| l.starts_with('\t') && l.contains("this->tail")),
        "a condition is one tab-indented line: {one}"
    );
    assert!(
        !one.contains(" head "),
        "the filter let everything through: {one}"
    );
}

/// A call or jump through an import slot is a call or a jump, not a data read.
///
/// `call qword [rel <IAT slot>]` is how a PE reaches an import without a
/// thunk. Recording the slot as a plain memory reference hides every such
/// call: the import's cross-references read `imm/mem`, and no caller lists
/// the import among its callees.
#[test]
fn calls_through_an_import_slot_keep_their_kind() {
    let a = Analysis::compute(&fixture());
    let sites = a
        .xrefs
        .get(&0x2050)
        .expect("ReportAssertFailure slot has refs");
    let kind_at = |va: u64| sites.iter().find(|s| s.va == va).map(|s| s.kind);
    assert_eq!(kind_at(0x1230), Some(RefKind::Call), "{sites:?}");
    assert_eq!(kind_at(0x1210), Some(RefKind::Jmp), "{sites:?}");
}

/// Asking for the function at an import's slot is answered with what the
/// slot is: the import's code lives in another module.
///
/// # Panics
///
/// When the slot reads as a function not found, or the function in the
/// image is not found.
#[test]
fn an_import_slot_is_no_function_and_says_so() {
    use borer_engine::analysis::function_entry;
    let mut bytes = vec![0u8; 0x2000];
    bytes[0] = 0xc3; // ASM: ret
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![
            Section::mapped(".text", 0x1_4000_1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x1_4000_2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.format = BinaryFormat::Pe;
    p.symbols.push(Symbol {
        name: "KERNEL32.dll!GetLastError".to_owned(),
        addr: 0x1_4000_2000,
        kind: SymbolKind::Import,
    });
    let a = Analysis::compute(&p);
    assert_eq!(function_entry(&p, &a, 0x1_4000_1000), Ok(0x1_4000_1000));
    let err = function_entry(&p, &a, 0x1_4000_2000).unwrap_err();
    assert!(
        err.contains("import slot of KERNEL32.dll!GetLastError"),
        "{err}"
    );
    let err = function_entry(&p, &a, 0x1_4000_2100).unwrap_err();
    assert!(err.contains("no discovered function contains"), "{err}");
    assert!(
        err.ends_with("; the nearest function before it is sub_140001000 at 0x140001000"),
        "{err}"
    );
    let err = function_entry(&p, &a, 0x1000).unwrap_err();
    assert_eq!(
        err,
        "no discovered function contains 0x1000: it is outside the image (0x140001000..0x140003000); as an RVA it is 0x140001000, which is mapped"
    );
    let err = function_entry(&p, &a, 0x9_0000_0000).unwrap_err();
    assert!(
        err.ends_with("outside the image (0x140001000..0x140003000)"),
        "{err}"
    );
}

/// Constructors give classes their vtables and parents.
///
/// `Der::Der` calls `Base::Base` with `this` and then stores `Der`'s vtable,
/// whose two slots are read up to the terminating zero word; the unnamed
/// function storing the same vtable becomes `Der::ctor_or_dtor`; the layout
/// shows parent, vtable and slots, and `Base` lists `Der` as derived.
#[test]
fn constructors_give_classes_vtables_and_parents() {
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let der = a.classes.by_name.get("Der").expect("Der");
    assert_eq!(der.vtable, Some(0x22a0));
    assert_eq!(der.slots, vec![0x1870, 0x1200]);
    assert_eq!(der.parent.as_deref(), Some("Base"));
    assert_eq!(der.ctors, vec![0x16f0, 0x1710, 0x1730]);
    let base = a.classes.by_name.get("Base").expect("Base");
    assert_eq!((base.vtable, base.parent.as_deref()), (Some(0x2280), None));
    assert_eq!(base.slots, vec![0x1200, 0x11e0]);
    assert_eq!(
        a.classes.vtables.get(&0x22a0).map(String::as_str),
        Some("Der")
    );
    let uc = a.function(0x1730).expect("UC");
    assert_eq!(uc.name.as_deref(), Some("Der::ctor_or_dtor"));
    assert!(uc.name_inferred);
    let o = Overlay::default();
    let layout = class_layout(&p, &a, &o, "Der").expect("layout");
    let text = render_layout(&layout, &a, &o);
    assert!(text.contains("parent:  Base\n"), "{text}");
    let slots = format!(
        "vftable: 0x22a0 (2 slots)\n  [0] {}\n  [1] {}\n",
        name_of(&a, &o, 0x1870),
        name_of(&a, &o, 0x1200)
    );
    assert!(text.contains(&slots), "{text}");
    assert!(text.contains("+0x0    vftable"), "{text}");
    let base_layout = class_layout(&p, &a, &o, "Base").expect("base layout");
    let base_text = render_layout(&base_layout, &a, &o);
    assert!(base_text.contains("derived: Der\n"), "{base_text}");
    assert!(text.contains("derived: Der2\n"), "{text}");
}

/// Virtual method names travel along the slot index.
///
/// `Der2::Foo` overrides slot 0 of `Der`'s table, so the unnamed function
/// there becomes `Der::Foo`; `Base`'s slot 0 is an export without a class
/// and keeps its name.
#[test]
fn virtual_method_names_follow_the_slot() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let dv = a.function(0x1870).expect("DV");
    assert_eq!(dv.name.as_deref(), Some("Der::Foo"));
    assert!(dv.name_inferred);
    let base_slot0 = a.function(0x1200).expect("P");
    assert!(base_slot0.name.as_deref().is_none_or(|n| !n.contains("::")));
}

/// A constructor storing `this` into the TLS block registers a singleton.
///
/// `Tls::Tls` stores at offset 0x10, so that slot is `Tls`, and the getter
/// `TG` returning that slot returns a `Tls *`; `Glob::Glob` stores `this`
/// in the global at 0x27c0, which holds a `Glob`; both layouts say where
/// their singleton lives.
#[test]
fn constructors_register_tls_singletons() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes.tls_slots.get(&0x10).map(String::as_str),
        Some("Tls")
    );
    let tg = a.function(0x1ab0).expect("TG");
    assert_eq!(tg.ret_hint.as_deref(), Some("Tls"));
    assert_eq!(
        a.classes.global_hints.get(&0x27c0).map(String::as_str),
        Some("Glob")
    );
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let o = Overlay::default();
    let tls = class_layout(&p, &a, &o, "Tls").expect("Tls layout");
    assert!(render_layout(&tls, &a, &o).contains("singleton: TLS slot 0x10\n"));
    let glob = class_layout(&p, &a, &o, "Glob").expect("Glob layout");
    assert!(render_layout(&glob, &a, &o).contains("singleton: global 0x27c0\n"));
}

/// The class layout lists a class's constructors and factories by name.
///
/// `Ns::Thing` has the constructor `DK`, named `Ns::Thing::ctor_or_dtor`;
/// `Ns::T3` has the factory `CI`, named `Ns::T3::create`.
#[test]
fn class_layout_lists_constructors_and_factories() {
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let thing = class_layout(&p, &a, &o, "Ns::Thing").expect("Ns::Thing layout");
    assert!(render_layout(&thing, &a, &o).contains(
        "constructors: Ns::Thing::ctor_or_dtor
"
    ));
    let t3 = class_layout(&p, &a, &o, "Ns::T3").expect("Ns::T3 layout");
    assert!(render_layout(&t3, &a, &o).contains(
        "factories: Ns::T3::create
"
    ));
}

/// A class layout is asked for by the name the classes listing prints,
/// bare or qualified, in any case.
///
/// `borer://classes` prints `Thing (Ns::Thing)` for a class registered by
/// its last segment, and an agent asks `class_layout` for `Thing`; the
/// answer was `no function belongs to class 'Thing'`. A bare name is the
/// class whose last segment it is, the first by name when several, and a
/// name is matched in any case, as `resolve` matches a function.
#[test]
fn class_layout_resolves_the_name_the_classes_listing_prints() {
    use borer_engine::analysis::classes::{class_layout, resolve_class};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        resolve_class(&a, &o, "Thing").as_deref(),
        Some("Ns::Thing"),
        "a bare name is the class whose last segment it is"
    );
    assert_eq!(
        resolve_class(&a, &o, "ns::thing").as_deref(),
        Some("Ns::Thing"),
        "a qualified name is matched in any case"
    );
    assert_eq!(resolve_class(&a, &o, "t3").as_deref(), Some("Ns::T3"));
    assert_eq!(resolve_class(&a, &o, "NoSuchClass"), None);
    assert_eq!(resolve_class(&a, &o, ""), None);
    let bare = class_layout(&p, &a, &o, "Thing").expect("Thing resolves to Ns::Thing");
    let full = class_layout(&p, &a, &o, "Ns::Thing").expect("Ns::Thing layout");
    assert_eq!(bare, full, "the bare name answers with the same layout");
    assert_eq!(
        bare.name, "Ns::Thing",
        "the layout is named as the methods qualify it"
    );
}

/// Functions of one instruction shape over different constants share a
/// shape class but not a clone class.
///
/// `SP1` and `SP2` differ only in their immediates.
#[test]
fn near_clones_share_a_shape_class() {
    let a = Analysis::compute(&fixture());
    let shapes = a.shapes_of(0x4990);
    assert!(
        shapes.contains(&0x4990) && shapes.contains(&0x49a0),
        "{shapes:?}"
    );
    assert!(a.clones_of(0x4990).is_empty());
    assert_ne!(
        a.function(0x4990).map(|f| f.body_hash),
        a.function(0x49a0).map(|f| f.body_hash)
    );
}

/// Overrides of one virtual method share its return verdict.
///
/// `CB` reads the result of `BF1`, so slot 1 of `class_2970` returns a
/// value; `DF1` overrides that slot in `class_2988`, whose parent is
/// `class_2970`, and has no caller, so it takes the verdict.
#[test]
fn slot_siblings_share_the_return_verdict() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let verdict = |e: u64| a.function(e).and_then(|f| f.returns_value);
    assert_eq!(verdict(0x1de0), Some(true));
    assert_eq!(verdict(0x1df0), Some(true));
    assert_eq!(
        a.classes
            .by_name
            .get("class_2988")
            .and_then(|c| c.parent.as_deref()),
        Some("class_2970")
    );
}

/// A field filled by a creator and the getter of that field carry the
/// class.
///
/// `DK3` stores `DC`'s result at `this + 8`, so `class_2910`'s field at 8
/// holds a `Ns::Thing`; `FG`, slot 2 of `class_2910`, returns that field,
/// so it returns a `Ns::Thing`.
#[test]
fn creator_filled_fields_and_their_getters_carry_the_class() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes
            .field_hints
            .get(&("class_2910".to_owned(), 8))
            .map(String::as_str),
        Some("Ns::Thing")
    );
    assert_eq!(
        a.function(0x1c50).and_then(|f| f.ret_hint.as_deref()),
        Some("Ns::Thing")
    );
}

/// A constructor this pass names still registers its singleton.
///
/// `DK3` stores the table at 0x2910, which nothing names, and stores `this`
/// at 0x3010; the class `class_2910` gets that global as its singleton.
#[test]
fn constructors_named_by_the_pass_register_singletons() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let c = a.classes.by_name.get("class_2910").expect("class_2910");
    assert_eq!(c.ctors, vec![0x1c30]);
    assert_eq!(
        a.classes.global_hints.get(&0x3010).map(String::as_str),
        Some("class_2910")
    );
}

/// Creators, the globals they fill and the getters of those globals carry
/// the class along.
///
/// `DC` returns the result of `DK`, a constructor of `Ns::Thing`, so it
/// returns a `Ns::Thing`; `GS` stores `DC`'s result at 0x3008, so the global
/// holds one; `GG` returns the global's word, so it returns one too.
#[test]
fn creators_globals_and_getters_carry_the_class() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let hint = |e: u64| a.function(e).and_then(|f| f.ret_hint.as_deref());
    assert_eq!(hint(0x1bc0), Some("Ns::Thing"));
    assert_eq!(
        a.classes.global_hints.get(&0x3008).map(String::as_str),
        Some("Ns::Thing")
    );
    assert_eq!(hint(0x1c10), Some("Ns::Thing"));
}

/// A constructor with its base's constructor inlined stores two tables: the
/// shorter is the base's, the longer its own.
///
/// `TT` stores the two-slot table at 0x2a00 and then the three-slot table at
/// 0x2a20 without calling anything, so it constructs the class of the
/// longer table, whose parent owns the shorter.
#[test]
fn inlined_base_constructors_store_two_tables() {
    let a = Analysis::compute(&fixture());
    let own = a
        .classes
        .vtables
        .get(&0x2a20)
        .expect("derived table")
        .clone();
    let base = a.classes.vtables.get(&0x2a00).expect("base table").clone();
    let c = a.classes.by_name.get(&own).expect("derived class");
    assert_eq!(c.parent.as_deref(), Some(base.as_str()));
    assert_eq!(c.ctors, vec![0x1e50]);
    assert_eq!(
        a.function(0x1e50).and_then(|f| f.name.clone()),
        Some(format!("{own}::ctor_or_dtor"))
    );
}

/// An initializer names the descriptor of a class no registration spells.
///
/// `DI3` spells `"Ns::T3"` beside the unnamed object at 0x3080 and the
/// named `Ns::Thing` descriptor, so the object is `Ns::T3`'s and its parent
/// is `Ns::Thing`.
#[test]
fn initializers_name_unregistered_descriptors() {
    let a = Analysis::compute(&fixture());
    let c = a.classes.by_name.get("Ns::T3").expect("Ns::T3");
    assert_eq!(c.parent.as_deref(), Some("Ns::Thing"));
}

/// A constructor storing three tables in order names the longest its own
/// and the next its parent's.
///
/// `TT3` stores the two-, three- and four-slot tables at 0x2a00, 0x2a20 and
/// 0x2ab0 in turn: it constructs the class of the four-slot table, whose
/// parent owns the three-slot one (`TT`'s class), the base of that base
/// having been inlined too.
#[test]
fn three_inlined_tables_name_the_nearest_base() {
    let a = Analysis::compute(&fixture());
    let own = a.classes.vtables.get(&0x2ab0).expect("own table").clone();
    let mid = a
        .classes
        .vtables
        .get(&0x2a20)
        .expect("middle table")
        .clone();
    let c = a.classes.by_name.get(&own).expect("class");
    assert_eq!(c.parent.as_deref(), Some(mid.as_str()));
    assert_eq!(c.ctors, vec![0x10e1]);
}

/// A creator constructing in place gives a descriptor-only class its
/// vtable.
///
/// `CI` stores the table at 0x2ad8 through the allocation a call returned
/// and references `Ns::T3`'s descriptor: `Ns::T3`, known until now only
/// from its descriptor, owns that table, keeps its descriptor parent, and
/// `CI` is its `create`.
#[test]
fn creators_constructing_in_place_give_classes_their_vtable() {
    let a = Analysis::compute(&fixture());
    let c = a.classes.by_name.get("Ns::T3").expect("Ns::T3");
    assert_eq!(c.vtable, Some(0x2ad8));
    assert_eq!(c.parent.as_deref(), Some("Ns::Thing"));
    assert_eq!(c.creators, vec![0x11e4]);
    assert_eq!(
        a.function(0x11e4).and_then(|f| f.name.as_deref()),
        Some("Ns::T3::create")
    );
}

/// The parent a class's descriptor names wins over the base table its
/// constructor stores first.
///
/// `TT2` stores the two-slot table at 0x2a00 before its own at 0x2a60, and
/// `CR` creates from the descriptor `DR4` registers as `Ns::T4`, whose
/// initializer `DI4` names `Ns::T2` as the parent: the class is `Ns::T4`
/// with parent `Ns::T2`, not the class of the inlined table, since a store
/// the compiler kept may be a grandparent's.
#[test]
fn descriptor_parents_win_over_inlined_tables() {
    let a = Analysis::compute(&fixture());
    let c = a.classes.by_name.get("Ns::T4").expect("Ns::T4");
    assert_eq!(c.vtable, Some(0x2a60));
    assert_eq!(c.parent.as_deref(), Some("Ns::T2"));
}

/// Slot sharing walks through ancestors without a table.
///
/// `Ns::T4` derives from `Ns::T2`, a class known only from its descriptor,
/// which derives from `Ns::Thing`: slot 1 of `Ns::T4`'s table (`BF1`, whose
/// result `CB` reads) and slot 1 of `Ns::Thing`'s (`S4`, which nothing
/// calls) override one method, so `S4` takes the verdict.
#[test]
fn slot_sharing_walks_through_classes_without_a_table() {
    let a = Analysis::compute(&fixture());
    assert_eq!(
        a.classes
            .by_name
            .get("Ns::T2")
            .and_then(|c| c.parent.as_deref()),
        Some("Ns::Thing")
    );
    assert_eq!(a.function(0x1bf0).and_then(|f| f.returns_value), Some(true));
}

/// A descriptor initializer links a class to its parent.
///
/// `DI` spells `"Ns::T2"` beside two described objects, the one `DR2`
/// registered under that name and `Ns::Thing`'s, so `Ns::T2` derives from
/// `Ns::Thing`; no constructor stores a table for it, so it is a class
/// without a vtable.
#[test]
fn descriptor_initializers_link_parents() {
    let a = Analysis::compute(&fixture());
    let c = a.classes.by_name.get("Ns::T2").expect("Ns::T2");
    assert_eq!(c.parent.as_deref(), Some("Ns::Thing"));
    assert_eq!(c.vtable, None);
    assert!(
        a.classes
            .by_name
            .get("Ns::Thing")
            .is_some_and(|t| t.parent.is_none())
    );
}

/// A table no signature names takes its class name from the descriptor its
/// creator allocates from.
///
/// `DR` spells `"Ns::Thing"` beside the object at 0x3000, `DC` references
/// that object and calls `DK`, which stores the table at 0x28c0, so the
/// table is `Ns::Thing`'s and `DK` its `ctor_or_dtor`.
#[test]
fn descriptors_name_constructed_tables() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes.vtables.get(&0x28c0).map(String::as_str),
        Some("Ns::Thing")
    );
    let c = a.classes.by_name.get("Ns::Thing").expect("Ns::Thing");
    assert_eq!(c.slots, vec![0x1be0, 0x1bf0]);
    assert_eq!(c.ctors, vec![0x1bb0]);
    assert_eq!(
        a.function(0x1bb0).and_then(|f| f.name.as_deref()),
        Some("Ns::Thing::ctor_or_dtor")
    );
    assert!(!a.classes.by_name.contains_key("class_28c0"));
}

/// A table nothing names but a function stores at `[this]` is a class of
/// its own.
///
/// `UT` stores the table at 0x2800, so `class_2800` exists with the table's
/// slots, `UT` is its `ctor_or_dtor` and its slot functions take it as
/// `this`.
#[test]
fn unnamed_tables_with_a_constructor_become_classes() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes.vtables.get(&0x2800).map(String::as_str),
        Some("class_2800")
    );
    let c = a.classes.by_name.get("class_2800").expect("class_2800");
    assert_eq!(c.slots, vec![0x1b20, 0x1b30]);
    assert_eq!(c.ctors, vec![0x1b10]);
    let ut = a.function(0x1b10).expect("UT");
    assert_eq!(ut.name.as_deref(), Some("class_2800::ctor_or_dtor"));
    let s1 = a.function(0x1b20).expect("S1");
    assert_eq!(
        s1.param_hints.get(&0).map(String::as_str),
        Some("class_2800")
    );
}

/// A table no named constructor stores is named by its slots.
///
/// 0x22c0 holds `Der2::Foo` (in no other table) and a shared slot, so it is
/// `Der2`'s vtable; the unnamed function storing it becomes
/// `Der2::ctor_or_dtor` and its base-constructor call makes `Der` the parent.
#[test]
fn tables_without_constructors_are_named_by_their_slots() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let der2 = a.classes.by_name.get("Der2").expect("Der2");
    assert_eq!(der2.vtable, Some(0x22c0));
    assert_eq!(der2.slots, vec![0x1740, 0x1200]);
    assert_eq!(der2.parent.as_deref(), Some("Der"));
    assert_eq!(der2.ctors, vec![0x1750]);
    assert_eq!(
        a.classes.vtables.get(&0x22c0).map(String::as_str),
        Some("Der2")
    );
    let uc2 = a.function(0x1750).expect("UC2");
    assert_eq!(uc2.name.as_deref(), Some("Der2::ctor_or_dtor"));
}

/// The layout of `Cls` lists its fields with widths, directions and types.
///
/// `Cls::Set` reads field 0, writes fields 8 (32-bit) and 0x10 (64-bit) and
/// passes `this + 0x20` to the `const` method `Other::Get`, so the embedded
/// `Other` at 0x20 is typed, and the rendering names the methods. `IG`
/// hands its first argument to `Cls::Has` as `this`, so it takes a `Cls` and
/// counts among the functions of the class.
#[test]
fn class_layout_collects_field_accesses_of_the_methods() {
    use borer_engine::analysis::classes::{class_layout, methods_of, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(methods_of(&a, &o, "Cls"), vec![0x1640, 0x1660, 0x40f4]);
    let layout = class_layout(&p, &a, &o, "Cls").expect("class found");
    let text = borer_engine::analysis::decompile::decompile(&p, &a, &o, 0x1640).expect("text");
    let f0 = layout.fields.get(&0).expect("field 0");
    assert!(f0.reads >= 1 && f0.writes == 0, "{text}");
    assert!(f0.widths.contains(&64));
    let f8 = layout.fields.get(&8).expect("field 8");
    assert_eq!((f8.reads, f8.writes), (1, 1));
    assert!(f8.widths.contains(&32));
    let f10 = layout.fields.get(&0x10).expect("field 0x10");
    assert_eq!((f10.reads, f10.writes), (0, 1));
    let text = render_layout(&layout, &a, &o);
    assert!(
        text.starts_with("class Cls: 3 methods, 4 fields, size >= 0x28"),
        "{text}"
    );
    assert!(text.contains("+0x8    u32        1/1   Set, Has"), "{text}");
    let f20 = layout.fields.get(&0x20).expect("field 0x20");
    assert!(f20.types.contains("Other"), "{text}");
    assert_eq!(f20.address_taken, 1);
    assert!(text.contains("+0x20   Other"), "{text}");
}

/// A call through an import slot names the import in the disassembly.
///
/// `call qword [rel <slot>]` reaches an import without a thunk, and the slot
/// address is the only thing that says which one. Left as a number, every
/// such call reads as a branch into data.
#[test]
fn disassembly_names_the_import_a_slot_call_reaches() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let out = borer_engine::analysis::render::disasm_function(
        &p,
        &a,
        &Overlay::default(),
        0x1810,
        64,
        false,
    )
    .expect("AS disassembles");
    assert!(out.contains("KERNEL32.dll!ReportAssertFailure"), "{out}");
}

/// A class layout, applied, defines its struct and types each method's
/// object with it, so the re-decompiled methods name the fields.
///
/// `Cls` reads a qword at 0, a dword at 8 and writes a qword at 0x10, and
/// hands the address of an embedded `Other` at 0x20 on: the struct takes
/// the three, notes the embedded one it cannot size, and every method's
/// first parameter becomes a `ClsS *`.
#[test]
fn an_applied_class_layout_types_each_methods_object() {
    use borer_engine::analysis::apply::from_class;
    use borer_engine::analysis::classes::class_layout;
    let p = fixture();
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let layout = class_layout(&p, &a, &plain, "Cls").expect("class found");
    let plan = from_class(&p, &a, &plain, &layout, "ClsS").expect("a plan");
    assert_eq!(
        plan.describe(&a, &plain),
        [
            "struct ClsS (0x18 bytes): 0x0 f_0 u64, 0x8 f_8 u32, 0x10 f_10 u64",
            "prototype Cls::Set (0x1640): void (ClsS *this, int)",
            "prototype Cls::Has (0x1660): bool (ClsS *this, int)",
            "prototype sub_40f4 (0x40f4): uint32_t (ClsS *)",
            "# 0x20 is only addressed (an embedded object), so it states no width; left out",
        ]
    );
    let before =
        borer_engine::analysis::decompile::decompile(&p, &a, &plain, 0x1640).expect("text");
    assert!(before.contains("this->field_0x8 = a2;"), "{before}");
    let mut o = plain;
    plan.apply(&mut o);
    let set = borer_engine::analysis::decompile::decompile(&p, &a, &o, 0x1640).expect("text");
    assert!(
        set.contains("// signature: void Cls::Set(ClsS *this, int a2)"),
        "{set}"
    );
    assert!(set.contains("this->f_8 = a2;"), "{set}");
    assert!(set.contains("this->f_10 = "), "{set}");
}
