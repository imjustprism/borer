//! The census of unresolved indirect calls and jumps: each site with its
//! form, why discovery left it unresolved and the candidates a rule
//! admits, which never become callers.

use std::num::NonZeroUsize;

use borer_engine::analysis::render::{
    Candidate, Form, Level, Rule, Site, Why, XrefView, call_children, census, xref_rows,
};
use borer_engine::analysis::{Analysis, Overlay, parse_addr};
use borer_engine::program::{Arch, Program, Section};
use borer_engine::progress::Workers;

/// Returns an x86-64 image with `code` at 0x1000 and a page of writable,
/// zeroed data at 0x2000.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, at most a page.
fn image(code: &[u8]) -> Program {
    let mut bytes = vec![0xcc; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    bytes.resize(0x2000, 0);
    let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
    let data = Section::mapped(".data", 0x2000, 0x1000, 0x1000, true, false);
    Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text, data])
}

/// Returns an image whose function at 0x1000 calls through `rax`, into
/// the trampoline at 0x1040, through the empty slot at 0x2000, and jumps
/// on into the trampoline at its tail.
fn unresolved() -> Program {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xff, 0xd0, // ASM: call rax
        0xe8, 0x35, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0xff, 0x15, 0xef, 0x0f, 0x00, 0x00, // ASM: call [rip+0xfef] (0x2000)
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x05, // ASM: je 0x101e
        0xe9, 0x22, 0x00, 0x00, 0x00, // ASM: jmp 0x1040
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0xff, 0xe0]); // ASM: jmp rax
    image(&code)
}

/// Returns an image whose function at 0x1000 stores `f` 0x1040 into the
/// slot at 0x2000 and `h` 0x1050 into the one at 0x2008, then calls
/// through 0x2000, which the file leaves zero.
fn stores() -> Program {
    let mut code = vec![
        0x48, 0x8d, 0x05, 0x39, 0x00, 0x00, 0x00, // ASM: lea rax,[rip+0x39] (0x1040)
        0x48, 0x89, 0x05, 0xf2, 0x0f, 0x00, 0x00, // ASM: mov [rip+0xff2],rax (0x2000)
        0x48, 0x8d, 0x05, 0x3b, 0x00, 0x00, 0x00, // ASM: lea rax,[rip+0x3b] (0x1050)
        0x48, 0x89, 0x05, 0xec, 0x0f, 0x00, 0x00, // ASM: mov [rip+0xfec],rax (0x2008)
        0xff, 0x15, 0xde, 0x0f, 0x00, 0x00, // ASM: call [rip+0xfde] (0x2000)
        0xe8, 0x19, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0xe8, 0x24, 0x00, 0x00, 0x00, // ASM: call 0x1050
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
    code.resize(0x50, 0xcc);
    code.extend([0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret
    image(&code)
}

/// Returns an image of little-endian instruction words at 0x1000.
///
/// # Arguments
///
/// * `arch` - The instruction set.
/// * `words` - The instructions.
fn words_image(arch: Arch, words: &[u32]) -> Program {
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).unwrap_or(0);
    let text = Section::mapped(".text", 0x1000, 0, len, false, true);
    Program::raw(code, arch, 0, Some(0x1000), vec![text])
}

/// Returns the site at an address of a census.
///
/// # Arguments
///
/// * `sites` - The census's sites.
/// * `at` - The call or jump.
fn at(sites: &[Site], at: u64) -> Option<(Form, Why)> {
    sites.iter().find(|s| s.at == at).map(|s| (s.form, s.why))
}

/// Each unresolved site is one row with how it forms its target and why.
///
/// A call through a register, a call and a tail jump into a trampoline,
/// and a call through an empty data slot are a row each; the trampoline's
/// own jump is none.
///
/// # Panics
///
/// When a site is missing, extra, or has the wrong form or why.
#[test]
fn each_unresolved_site_is_a_row_with_its_form_and_why() {
    let p = unresolved();
    let a = Analysis::compute(&p);
    let found = census(&p, &a);
    assert_eq!(found.sites.len(), 4, "{:?}", found.sites);
    assert_eq!(
        at(&found.sites, 0x1004),
        Some((Form::Register, Why::NoTarget))
    );
    let into = (
        Form::IntoTrampoline { entry: 0x1040 },
        Why::Trampoline { through: 0x1040 },
    );
    assert_eq!(at(&found.sites, 0x1006), Some(into));
    assert_eq!(at(&found.sites, 0x1019), Some(into));
    assert_eq!(
        at(&found.sites, 0x100b),
        Some((
            Form::Global { slot: 0x2000 },
            Why::SlotFilledAtRunTime { slot: 0x2000 }
        ))
    );
    assert!(found.through.contains(&0x1040));
    assert!(found.sites.iter().all(|s| s.function == 0x1000));
}

/// A store into exactly the called slot admits the function it writes.
///
/// The call through a slot the file leaves zero lists the function stored
/// there, tagged with the store, and not the one stored into the next
/// slot.
///
/// # Panics
///
/// When the candidates differ.
#[test]
fn a_store_into_the_called_slot_admits_its_function() {
    let p = stores();
    let a = Analysis::compute(&p);
    let found = census(&p, &a);
    let site = found.sites.iter().find(|s| s.at == 0x101c);
    let site = site.map(|s| (s.form, s.candidates.to_vec(), s.candidates_total));
    assert_eq!(
        site,
        Some((
            Form::Global { slot: 0x2000 },
            vec![Candidate {
                target: 0x1040,
                rule: Rule::StoredSlot { store: 0x1007 }
            }],
            1
        ))
    );
}

/// A candidate is no caller.
///
/// The cross-references of the stored function name its direct call and
/// not the call through the slot it is a candidate of, and they and its
/// callers are the same before and after the census is read.
///
/// # Panics
///
/// When reading the census changes either.
#[test]
fn candidates_never_become_callers() {
    let p = stores();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let view = XrefView::Page {
        offset: 0,
        limit: 60,
    };
    let rows = xref_rows(&p, &a, &o, 0x1040, view);
    let callers = call_children(&p, &a, &o, 0x1040, Level::Callers);
    let sites: Vec<u64> = rows
        .rows
        .iter()
        .flat_map(|r| r.sites.iter().map(|&(va, _)| va))
        .collect();
    assert!(
        sites.contains(&0x1022) && !sites.contains(&0x101c),
        "{sites:x?}"
    );
    assert!(
        census(&p, &a)
            .sites
            .iter()
            .any(|s| !s.candidates.is_empty())
    );
    assert_eq!(xref_rows(&p, &a, &o, 0x1040, view), rows);
    assert_eq!(call_children(&p, &a, &o, 0x1040, Level::Callers), callers);
}

/// The census is the same over analyses computed at one worker and at
/// sixteen; the census itself is built on one thread.
///
/// # Panics
///
/// When the sites differ.
#[test]
fn the_census_is_the_same_at_any_thread_count() {
    let p = unresolved();
    let sites = |n: usize| {
        let workers = Workers(NonZeroUsize::new(n).unwrap_or(NonZeroUsize::MIN));
        workers.within(|| census(&p, &Analysis::compute(&p)).sites.clone())
    };
    assert_eq!(sites(1), sites(16));
}

/// `borer://indirect` pages rows whose site cells are mapped addresses.
///
/// Its first line counts the rows, its last names the next page, and a
/// form it does not know is refused with the forms it takes.
///
/// # Panics
///
/// When a line, a cell or the refusal differs.
#[test]
fn the_census_answer_pages_rows_whose_sites_are_mapped() {
    let p = unresolved();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let ask = |uri: &str| borer_engine::answer::ask(&p, &a, &o, uri);
    let page = ask("borer://indirect!limit=1").and_then(Result::ok);
    let page = page.unwrap_or_default();
    assert!(
        page.starts_with(
            "# 4 unresolved indirect calls and jumps in 1 function, showing 1 of 4 from 0\n"
        ),
        "{page}"
    );
    assert!(
        page.contains("\n0x1004\tsub_1000\tregister\tno target in the file\t-\n"),
        "{page}"
    );
    assert!(
        page.ends_with("# 3 more; borer://indirect!limit=1!offset=1 for the next page\n"),
        "{page}"
    );
    let global = ask("borer://indirect/0x1000,form=global").and_then(Result::ok);
    let global = global.unwrap_or_default();
    assert!(global.contains("showing 1 of 1 from 0"), "{global}");
    let refused = ask("borer://indirect/form=wide").and_then(Result::err);
    assert!(
        refused.is_some_and(|r| r.contains("register, vtable, field, global, trampoline, jump")),
    );
    let listed = borer_engine::answer::listing(&p, Some(&a), &o, "borer://indirect");
    let listed = listed.unwrap_or_else(|e| panic!("{e}"));
    let column = listed
        .columns()
        .and_then(|c| c.iter().position(|n| n == "site"));
    assert_eq!(column, Some(0));
    assert_eq!(listed.len(), 4);
    for r in 0..listed.len() {
        let cell = listed.fields(r).and_then(|f| f.first().copied());
        let va = cell.and_then(parse_addr);
        assert!(va.is_some_and(|va| p.section_at(va).is_some()), "{cell:?}");
    }
}

/// Each form and reason reads as a cell for an agent and a sentence.
///
/// # Panics
///
/// When a spelling differs.
#[test]
fn forms_and_reasons_read_as_sentences() {
    let slot = Form::VtableSlot { slot: 3 };
    assert_eq!(slot.spell(), "vtable slot 3");
    assert_eq!(
        slot.person(),
        "Calls slot 3 of the table an object's first word points at."
    );
    let filled = Why::SlotFilledAtRunTime { slot: 0x2000 };
    assert_eq!(filled.spell(), "0x2000 is filled at run time");
    assert!(
        filled
            .person()
            .starts_with("The slot at 0x2000 holds no function")
    );
    assert_eq!(Form::Field { offset: -8 }.spell(), "field -0x8");
}

/// A vtable slot admits only what a class holds there that is a function.
///
/// Of three classes, one holds a function in slot 1, one a zero word and
/// one a data address: the call through slot 1 lists the function alone.
///
/// # Panics
///
/// When the candidates differ.
#[test]
fn a_slot_word_that_is_no_function_is_no_candidate() {
    use borer_engine::analysis::vtables::ClassInfo;
    let mut code = vec![
        0x48, 0x8b, 0x01, // ASM: mov rax,[rcx]
        0xff, 0x50, 0x08, // ASM: call [rax+8]
        0xe8, 0x35, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
    let p = image(&code);
    let mut a = Analysis::compute(&p);
    for (name, word) in [("A", 0x1040), ("B", 0), ("C", 0x2000)] {
        let info = ClassInfo {
            name: name.to_owned(),
            slots: vec![0, word],
            ..ClassInfo::default()
        };
        a.classes.by_name.insert(name.to_owned(), info);
    }
    let found = census(&p, &a);
    let site = found.sites.iter().find(|s| s.at == 0x1003);
    let site = site.map(|s| (s.form, s.candidates.to_vec(), s.candidates_total));
    let only = Candidate {
        target: 0x1040,
        rule: Rule::VtableSlot { class: "A".into() },
    };
    assert_eq!(site, Some((Form::VtableSlot { slot: 1 }, vec![only], 1)));
}

/// A table read from no object's first word is no vtable: a call through
/// a word of a pointer loaded from `[rcx+0x10]` or from a global is a
/// field, and no class's slot becomes its candidate.
///
/// # Panics
///
/// When either call is called a vtable slot or given a candidate.
#[test]
fn a_table_not_read_from_an_object_s_first_word_is_a_field() {
    use borer_engine::analysis::vtables::ClassInfo;
    let mut code = vec![
        0x48, 0x8b, 0x41, 0x10, // ASM: mov rax,[rcx+0x10]
        0xff, 0x50, 0x08, // ASM: call [rax+8]
        0x48, 0x8b, 0x05, 0xf2, 0x0f, 0x00, 0x00, // ASM: mov rax,[rip+0xff2] (0x2000)
        0xff, 0x50, 0x08, // ASM: call [rax+8]
        0xe8, 0x2a, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
    let p = image(&code);
    let mut a = Analysis::compute(&p);
    let info = ClassInfo {
        name: "A".to_owned(),
        slots: vec![0, 0x1040],
        ..ClassInfo::default()
    };
    a.classes.by_name.insert("A".to_owned(), info);
    let found = census(&p, &a);
    let row = |va| {
        found
            .sites
            .iter()
            .find(|s| s.at == va)
            .map(|s| (s.form, s.candidates_total))
    };
    assert_eq!(row(0x1004), Some((Form::Field { offset: 8 }, 0)));
    assert_eq!(row(0x100e), Some((Form::Field { offset: 8 }, 0)));
}

/// On arm64 a table read from an object's first word is a vtable slot,
/// one read from `[x0, #16]` a field.
///
/// # Panics
///
/// When either call has the other's form.
#[test]
fn an_arm64_table_is_a_slot_only_from_an_object_s_first_word() {
    let words: [u32; 7] = [
        0xf940_0808, // ASM: ldr x8,[x0,#16]
        0xf940_0508, // ASM: ldr x8,[x8,#8]
        0xd63f_0100, // ASM: blr x8
        0xf940_0008, // ASM: ldr x8,[x0]
        0xf940_0508, // ASM: ldr x8,[x8,#8]
        0xd63f_0100, // ASM: blr x8
        0xd65f_03c0, // ASM: ret
    ];
    let p = words_image(Arch::Arm64, &words);
    let a = Analysis::compute(&p);
    let found = census(&p, &a);
    assert_eq!(
        at(&found.sites, 0x1008),
        Some((Form::Field { offset: 8 }, Why::NoTarget))
    );
    assert_eq!(
        at(&found.sites, 0x1014),
        Some((Form::VtableSlot { slot: 1 }, Why::NoTarget))
    );
}

/// A direct call names its target, so it is no row even when the target
/// is no code.
///
/// On x86-64 the call goes into data, on ARM32 a `bl` to an address no
/// section maps.
///
/// # Panics
///
/// When either census lists a site.
#[test]
fn a_direct_call_to_no_code_is_no_row() {
    let code = [
        0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x2000
        0xc3, // ASM: ret
    ];
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert_eq!(census(&p, &a).sites, Vec::new());
    let words: [u32; 2] = [
        0xeb00_1ffe, // ASM: bl 0x9000
        0xe12f_ff1e, // ASM: bx lr
    ];
    let p = words_image(Arch::Arm, &words);
    let a = Analysis::compute(&p);
    assert_eq!(census(&p, &a).sites, Vec::new());
}

/// A call through a stack slot, an indexed table or a register loaded
/// from the stack is memory.
///
/// None is a register the block does not load, and a table read through
/// a register set to a fixed address is a field.
///
/// # Panics
///
/// When a site has another form.
#[test]
fn memory_and_fixed_tables_have_their_own_forms() {
    let code = [
        0xff, 0x54, 0x24, 0x28, // ASM: call [rsp+0x28]
        0xff, 0x14, 0xc8, // ASM: call [rax+rcx*8]
        0x48, 0x8b, 0x44, 0x24, 0x20, // ASM: mov rax,[rsp+0x20]
        0xff, 0xd0, // ASM: call rax
        0x48, 0x8d, 0x0d, 0xeb, 0x0f, 0x00, 0x00, // ASM: lea rcx,[rip+0xfeb] (0x2000)
        0x48, 0x8b, 0x01, // ASM: mov rax,[rcx]
        0xff, 0x50, 0x08, // ASM: call [rax+8]
        0xc3, // ASM: ret
    ];
    let p = image(&code);
    let a = Analysis::compute(&p);
    let found = census(&p, &a);
    let form = |va| at(&found.sites, va).map(|(f, _)| f);
    assert_eq!(form(0x1000), Some(Form::Memory));
    assert_eq!(form(0x1004), Some(Form::Memory));
    assert_eq!(form(0x100c), Some(Form::Memory));
    assert_eq!(form(0x1018), Some(Form::Field { offset: 8 }));
    assert_eq!(
        Form::Memory.person(),
        "Goes through a word in memory: a stack slot, an indexed table, or a register loaded from one."
    );
}

/// On arm64 a table read through a register `adrp` and `add` set is a
/// field, not a vtable slot.
///
/// # Panics
///
/// When the call has another form.
#[test]
fn an_arm64_table_at_a_fixed_address_is_a_field() {
    let words: [u32; 6] = [
        0xb000_0000, // ASM: adrp x0,0x2000
        0x9100_4000, // ASM: add x0,x0,#0x10
        0xf940_0008, // ASM: ldr x8,[x0]
        0xf940_0508, // ASM: ldr x8,[x8,#8]
        0xd63f_0100, // ASM: blr x8
        0xd65f_03c0, // ASM: ret
    ];
    let p = words_image(Arch::Arm64, &words);
    let a = Analysis::compute(&p);
    let found = census(&p, &a);
    assert_eq!(
        at(&found.sites, 0x1010),
        Some((Form::Field { offset: 8 }, Why::NoTarget))
    );
}

/// A call into a trampoline that jumps through a fixed slot is a call
/// through that slot, and a store into the slot admits its function.
///
/// The row names the slot and never says the stub jumps through a
/// register.
///
/// # Panics
///
/// When the row's form, why, candidates or text differ.
#[test]
fn a_trampoline_through_a_slot_names_the_slot() {
    let mut code = vec![
        0x48, 0x8d, 0x05, 0x49, 0x00, 0x00, 0x00, // ASM: lea rax,[rip+0x49] (0x1050)
        0x48, 0x89, 0x05, 0xf2, 0x0f, 0x00, 0x00, // ASM: mov [rip+0xff2],rax (0x2000)
        0xe8, 0x2d, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0xe8, 0x33, 0x00, 0x00, 0x00, // ASM: call 0x1050
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0xff, 0x25, 0xba, 0x0f, 0x00, 0x00]); // ASM: jmp [rip+0xfba] (0x2000)
    code.resize(0x50, 0xcc);
    code.extend([0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
    let p = image(&code);
    let a = Analysis::compute(&p);
    let found = census(&p, &a);
    let site = found.sites.iter().find(|s| s.at == 0x100e);
    let site = site.map(|s| (s.form, s.why, s.candidates.to_vec()));
    let stored = Candidate {
        target: 0x1050,
        rule: Rule::StoredSlot { store: 0x1007 },
    };
    assert_eq!(
        site,
        Some((
            Form::Global { slot: 0x2000 },
            Why::Trampoline { through: 0x1040 },
            vec![stored]
        ))
    );
    let o = Overlay::default();
    let text = borer_engine::answer::ask(&p, &a, &o, "borer://indirect").and_then(Result::ok);
    let text = text.unwrap_or_default();
    let row = text
        .lines()
        .find(|l| l.starts_with("0x100e"))
        .unwrap_or_default();
    assert!(
        row.contains("0x2000") && !row.contains("register"),
        "{text}"
    );
}

/// A direct call into data that holds a trampoline's address runs the
/// data's bytes, not the trampoline: it is no row.
///
/// # Panics
///
/// When the call is listed.
#[test]
fn a_direct_call_into_a_slot_holding_a_trampoline_is_no_row() {
    let mut bytes = vec![0xcc; 0x1000];
    bytes[..6].copy_from_slice(&[
        0xe8, 0xfb, 0x0f, 0x00, 0x00, // ASM: call 0x2000
        0xc3, // ASM: ret
    ]);
    bytes[0x40..0x42].copy_from_slice(&[0xff, 0xe0]); // ASM: jmp rax
    bytes.extend(0x1040u64.to_le_bytes());
    bytes.resize(0x2000, 0);
    let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
    let data = Section::mapped(".data", 0x2000, 0x1000, 0x1000, true, false);
    let p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text, data]);
    let a = Analysis::compute(&p);
    let found = census(&p, &a);
    assert_eq!(at(&found.sites, 0x1000), None, "{:?}", found.sites);
}
