//! Classes, virtual calls, fields, layouts, enums and asserts in the text.

use super::*;

/// A class's field names are read from its methods once: the second
/// call answers from the memo on the analysis, with the same names.
#[test]
fn field_names_are_read_once_per_class() {
    use borer_engine::analysis::classes::field_names;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let first = field_names(&p, &a, &o, "Nothing::Here");
    let second = field_names(&p, &a, &o, "Nothing::Here");
    assert_eq!(first, second);
    assert_eq!(a.derived.held("field_names"), 1, "{:?}", a.derived);
}

/// A 64-bit product of two sign-extended 32-bit loads casts an operand.
///
/// `movsxd` both, then `imul rax,rdx`, multiplies at 64 bits. Written as
/// `*(int32_t*)a1 * *(int32_t*)(a1 + 4)`, C would multiply two `int`s and
/// overflow at 32 bits, so the text widens the operands first.
#[test]
fn a_wide_product_of_narrow_loads_widens_first() {
    let code = [
        0x48, 0x63, 0x01, // ASM: movsxd rax,dword [rcx]
        0x48, 0x63, 0x51, 0x04, // ASM: movsxd rdx,dword [rcx+4]
        0x48, 0x0f, 0xaf, 0xc2, // ASM: imul rax,rdx
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("(int64_t)*(int32_t*)"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A method returning by hidden pointer with three declared parameters
/// needs five positions, one on the stack, so it has `this` though only
/// four registers are read.
///
/// `mov rax,[rcx]; mov [rdx],eax; mov eax,[rsp+0x28]; add eax,r9d; add
/// eax,r8d; mov [rdx+4],eax; lea r10,[rip+sig]; mov rax,rdx; ret` under
/// `class Util::String __cdecl Cls::Name(int,int,int)`.
#[test]
fn a_method_whose_positions_overflow_the_registers_has_this() {
    let code = [
        0x48, 0x8b, 0x01, 0x89, 0x02, 0x8b, 0x44, 0x24, 0x28, 0x41, 0x03, 0xc1, 0x41, 0x03, 0xc0,
        0x89, 0x42, 0x04, 0x4c, 0x8d, 0x15, 0xe7, 0x0f, 0x00, 0x00, 0x48, 0x8b, 0xc2, 0xc3,
    ];
    let p = program64_with_data(
        &code,
        b"class Util::String __cdecl Cls::Name(int,int,int)\0",
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("Cls::Name(Cls *this, Util::String *result, int a3, int a4, int a5)"),
        "{text}"
    );
}

/// A home slot the function uses as a local is `home_N`, not `arg_N`: a
/// write there changes no argument.
///
/// `sub rsp,0x28; mov dword [rsp+0x30],0x41554556; lea rcx,[rsp+0x30];
/// call 0x140001040; add rsp,0x28; ret`, the callee `mov eax,[rcx]; ret`.
#[test]
fn a_home_slot_used_as_a_local_is_named_home() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0xc7, 0x44, 0x24, 0x30, 0x56, 0x45, 0x55, 0x41, 0x48, 0x8d, 0x4c,
        0x24, 0x30, 0xe8, 0x2a, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x01, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("home_0 = 'AUEV';"), "{text}");
    assert!(text.contains("sub_140001040(&home_0)"), "{text}");
    assert!(!text.contains("arg_0"), "{text}");
}

/// `F` becomes a `for` loop.
///
/// `cmp ecx,5; jge` is a signed 32-bit compare and
/// both the counter and the sum are 32-bit writes, so the counter is an
/// `int32_t` and the compare needs no cast. The counter lives only in the
/// loop, so it is `i`. No temporaries and no back-edge goto survive.
#[test]
fn while_loop_structured() {
    let out = dc(0x1100);
    assert!(
        out.contains("for (i = 0; i < 5; i += 1)"),
        "no for sugar:\n{out}"
    );
    assert!(
        out.contains("int32_t i;"),
        "counter not signed 32-bit:\n{out}"
    );
    assert!(out.contains("var1 += i;"), "loop body missing:\n{out}");
    assert!(!out.contains("tmp_"), "spurious temporaries:\n{out}");
    assert!(
        !out.contains("goto L_1107;"),
        "back-edge goto survived structuring:\n{out}"
    );
    assert!(out.contains("return var1;"), "return missing:\n{out}");
}

/// `LD`: a ladder split in two by an ordered compare, both halves sharing
/// the default arm, is one `switch` whose default is that arm, written
/// once, and every arm reaches the one tail with no goto.
///
/// The `rdx` each arm sets is a value the tail's call does not take, so no
/// arm keeps it.
#[test]
fn shared_default_arm_is_copied_so_the_ladder_structures() {
    let out = dc(0x1550);
    assert!(!out.contains("goto"), "{out}");
    assert_eq!(out.matches("default: {").count(), 1, "{out}");
    assert!(
        out.contains("case 1: {") && out.contains("case 2: {"),
        "{out}"
    );
    assert!(out.contains("Base::vfunc_1("), "{out}");
    assert!(out.contains("switch (a1) {"), "{out}");
    assert!(out.contains("case 6: {"), "{out}");
    assert!(out.contains("default: {"), "{out}");
}

/// `NM2`: the inferred names show in the header and at the call site.
#[test]
fn inferred_names_render_in_headers_and_calls() {
    let out = dc(0x15e0);
    assert!(out.starts_with("// Foo::Baz @ 0x15e0"), "{out}");
    assert!(out.contains("Foo::Bar("), "{out}");
}

/// The skeleton of `sub_4930`'s guarded stores keeps its tests and the
/// calls in them and elides the stores.
#[test]
fn skeleton_keeps_flow_and_calls_only() {
    let out = dc(0x4930);
    let sk = skeleton(&out);
    assert!(sk.contains("if (a1 != 0) {"), "{sk}");
    assert!(sk.contains("Base::vfunc_1("), "{sk}");
    assert!(sk.contains("return 13;"), "{sk}");
    assert!(!sk.contains("*(uint32_t*)a2 = a1;"), "{sk}");
    assert!(sk.contains("..."), "{sk}");
    assert!(sk.len() < out.len(), "{sk}");
}

/// Declared signatures type the header and name the object `this`.
///
/// `CL1` carries `void __cdecl Cls::Set(int)` and reads two registers, so it
/// is a member function: the header shows the declared types with `this`,
/// the body reads `this`, and the `void` return holds; `NM`
/// (`int Foo::Bar(void)`, no register read) is a plain function with the
/// declared return type.
#[test]
fn signatures_from_asserts_type_the_header_and_name_this() {
    let out = dc(0x1640);
    assert!(
        out.contains("// signature: void Cls::Set(Cls *this, int a2)"),
        "{out}"
    );
    assert!(out.contains("this->field_0x8 = a2;"), "{out}");
    assert!(!out.contains("return rax"), "{out}");
    let bar = dc(0x15d0);
    assert!(bar.contains("// signature: int Foo::Bar()"), "{bar}");
    let has = dc(0x1660);
    assert!(
        has.contains("// signature: bool Cls::Has(Cls *this, int a2) const"),
        "{has}"
    );
    assert!(has.contains("*(uint32_t*)((uintptr_t)this + 8)"), "{has}");
    let of = dc(0x1680);
    assert!(
        of.contains("// signature: Util::String Name::Of(Util::String *result, int a2)"),
        "{of}"
    );
    assert!(of.contains("*(uint32_t*)result = a2;"), "{of}");
    assert!(of.contains("return result;"), "{of}");
}

/// A constructor's vtable store names the table: `Der::Der` renders
/// `Base::Base(this);` then `*(uint64_t*)this = &Der::vftable;`.
#[test]
fn constructors_store_named_vtables() {
    let cc = dc(0x16f0);
    assert!(cc.contains("Base::Base(this);"), "{cc}");
    assert!(cc.contains("*(uint64_t*)this = &Der::vftable;"), "{cc}");
}

/// A call through slot 1 of a receiver's vtable resolves to the slot's
/// function and renders in source form.
///
/// In `Der::Run` the receiver is `this`; in `VR2` it is the result of
/// `Fac::Get`, declared to return `Der *`; in `PU` it is the word a
/// `const Core::Ptr<Der> &` parameter holds, copied into `rax`.
#[test]
fn virtual_calls_resolve_through_the_receiver_class() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, 0x1770).unwrap_or_default();
    assert!(
        text.contains("// signature: void Der::Run(Der *this)"),
        "{text}"
    );
    let callee = borer_engine::analysis::name_of(&a, &o, 0x1200);
    assert!(text.contains(&format!("this->{callee}(")), "{text}");
    let vr2 = decompile(&p, &a, &o, 0x1780).unwrap_or_default();
    assert!(vr2.contains("var1 = Fac::Get();"), "{vr2}");
    assert!(vr2.contains(&format!("var1->{callee}(")), "{vr2}");
    let pu = decompile(&p, &a, &o, 0x17b0).unwrap_or_default();
    assert!(pu.contains("var1 = *(uint64_t*)a2;"), "{pu}");
    assert!(pu.contains(&format!("var1->{callee}(")), "{pu}");
}

/// A word of data between a vtable's methods does not end the table: the
/// methods after it stay at the indexes their byte offsets give, and a
/// virtual call through them still resolves.
///
/// `F1` sits at slot 2 of the table `RM` stores, past the datum `0x9999`
/// at slot 1, and its call through slot 0 of its own table reaches `F0`.
#[test]
fn a_data_slot_inside_a_vtable_keeps_the_methods_after_it() {
    let text = dc(0x5660);
    assert!(
        text.contains("// signature: uint64_t class_3730::vfunc_2(class_3730 *this)"),
        "{text}"
    );
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let slots = a.classes.by_name.get("class_3730").map(|c| c.slots.clone());
    assert_eq!(slots, Some(vec![0x5650, 0, 0x5660]));
    let callee = borer_engine::analysis::name_of(&a, &o, 0x5650);
    assert_eq!(callee, "class_3730::vfunc_0");
    assert!(text.contains("this->vfunc_0("), "{text}");
}

/// A vtable a constructor stores is named by its locator, and the class
/// that names it reaches the methods' own calls.
///
/// `Ns::Solo`'s table holds one slot, which a constructor must store
/// before it counts as a table at all, and `X`, the helper its
/// constructor hands `this` to after the store, resolves its call through
/// the class rather than an address-built name; `Ns::Rtti`'s two-slot
/// table gives `M1` the same resolution in its own body.
#[test]
fn a_locator_named_class_reaches_the_methods_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes.vtables.get(&0x3678).map(String::as_str),
        Some("Ns::Rtti")
    );
    assert_eq!(
        a.classes.vtables.get(&0x3718).map(String::as_str),
        Some("Ns::Solo")
    );
    assert_eq!(
        borer_engine::analysis::name_of(&a, &o, 0x56a0),
        "Ns::Solo::vfunc_0"
    );
    assert_eq!(
        borer_engine::analysis::name_of(&a, &o, 0x5680),
        "Ns::Solo::ctor_or_dtor"
    );
    let x = decompile(&p, &a, &o, 0x56b0).unwrap_or_default();
    assert!(
        x.contains("// signature: uint64_t sub_56b0(Ns::Solo *a1)"),
        "{x}"
    );
    assert!(x.contains("a1->vfunc_0("), "{x}");
    let m1 = decompile(&p, &a, &o, 0x5630).unwrap_or_default();
    assert!(
        m1.contains("// signature: uint64_t Ns::Rtti::vfunc_1(Ns::Rtti *this)"),
        "{m1}"
    );
    assert!(m1.contains("this->vfunc_0("), "{m1}");
}

/// A further base's table under multiple inheritance is named after its
/// base, and the base's methods it holds carry the base's class.
///
/// `Ns::Wide` stores `Ns::Tail`'s table at `[this+0x10]`; the table is
/// named `Ns::Wide::vftable_Ns::Tail`, its slots name `Ns::Tail`'s
/// methods and give the class its layout, although `Ns::Tail` has no
/// table of its own in the image.
#[test]
fn a_further_bases_vtable_is_named_after_its_base() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes.secondary_vtables.get(&0x32f0).map(String::as_str),
        Some("Ns::Wide::vftable_Ns::Tail")
    );
    assert_eq!(
        borer_engine::analysis::name_of(&a, &o, 0x5740),
        "Ns::Tail::vfunc_0"
    );
    assert_eq!(
        borer_engine::analysis::name_of(&a, &o, 0x5750),
        "Ns::Tail::vfunc_1"
    );
    let layout = borer_engine::analysis::classes::class_layout(&p, &a, &o, "Ns::Tail");
    let fields = layout.map(|l| l.fields.keys().copied().collect::<Vec<u64>>());
    assert_eq!(fields, Some(vec![4, 8]));
}

/// A method that never reads `this` is still a member when a parameter
/// arrives past the first argument register.
///
/// `Pk::Pick` declares one `int` and reads only `edx`, so `this` fills the
/// first slot and the body's `a2` matches the header.
#[test]
fn unused_this_still_counts_as_a_parameter() {
    let text = dc(0x17f0);
    assert!(
        text.contains("// signature: int Pk::Pick(Pk *this, int a2)"),
        "{text}"
    );
    assert!(text.contains("return a2;"), "{text}");
}

/// Assert literals render compactly: the function's own signature string
/// is `__FUNCSIG__`, the source path keeps its last two components, and
/// the asserted expression and line stay as they are.
#[test]
fn assert_literals_render_compactly() {
    let text = dc(0x1810);
    assert!(text.contains("// signature: void As::Chk()"), "{text}");
    assert!(
        text.contains("ReportAssertFailure(\"f.IsValid()\", \"util/fourcc.h\", 191, __FUNCSIG__);"),
        "{text}"
    );
}

/// A shared return block is as small as its `return`, whatever its epilogue.
///
/// `TE` is `LP3` with eight callee-saved registers to restore: the return
/// block holds ten instructions but renders as one statement, so the
/// chains into it are still copied, the returning exit is still written
/// inline and no `goto` remains.
#[test]
fn epilogue_instructions_do_not_count_against_copies() {
    let out = dc(0x1d30);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("while (1) {"), "{out}");
    assert!(out.contains("return a1;"), "{out}");
}

/// A loop whose condition sits after its body structures from its header.
///
/// `RL` enters its loop by a jump to the condition at the bottom, so the
/// body precedes the header in address order; the emitter reaches the body
/// first, finds the loop it belongs to and writes it from the header as a
/// `while`.
#[test]
fn rotated_loops_structure_from_their_header() {
    let out = dc(0x1ee0);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("while ("), "{out}");
    assert!(out.contains("Base::vfunc_1("), "{out}");
}

/// A parameter typed as a smart pointer by its callers resolves the
/// virtual call through it.
///
/// `UP`'s first parameter points at the `Core::Ptr<Der>` field `Der::Pass`
/// passes, so its header reads `Core::Ptr<Der> *a1` and the call through
/// the object the pointer holds resolves to slot 1 of `Der`'s table.
#[test]
fn smart_pointer_parameters_resolve_virtual_calls() {
    let out = dc(0x12f0);
    assert!(out.contains("Core::Ptr<Der> *a1"), "{out}");
    assert!(!out.contains("->vtable["), "{out}");
}

/// A function whose code another copies says so in its header, and one
/// that stands alone says nothing.
///
/// `CL_A` and `CL_B` are clones, so both name the class and its first
/// member; `CL_C` differs by an instruction and carries no such line.
#[test]
fn cloned_functions_name_their_class_in_the_header() {
    let a = dc(0x4220);
    assert!(
        a.contains("// clones: 2 functions run this code, the first at 0x4220"),
        "{a}"
    );
    let b = dc(0x4240);
    assert!(
        b.contains("// clones: 2 functions run this code, the first at 0x4220"),
        "{b}"
    );
    assert!(!dc(0x4260).contains("// clones:"), "{}", dc(0x4260));
}

/// A ladder nesting past sixty-four levels still structures without gotos.
///
/// `DEEP` nests seventy-two compare levels whose arms all jump to one
/// shared `ret`; every arm copies the tail as `return k;` and none falls
/// back to a jump.
#[test]
fn ladders_deeper_than_sixty_four_levels_structure() {
    let out = dc(0x4300);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("return 70;"), "{out}");
    assert!(out.contains("return 255;"), "{out}");
}

/// A string-compare ladder and a constant-to-string table both yield an
/// enum in the header.
///
/// `EN` compares its argument against four literals through `Q` and
/// returns a constant for each; `EN2` returns a literal for each of four
/// constants.
#[test]
fn name_tables_recover_as_enums() {
    let to_string = dc(0x4830);
    assert!(
        to_string.contains(
            "// enum values of a1: 4 values, Normal = 0, Pressed = 1, Over = 2, Down = 3"
        ),
        "{to_string}"
    );
    let parser = dc(0x47b0);
    assert!(
        parser.contains(
            "// enum by Base::vfunc_1 compare: 4 values, Back = 1, Tab = 2, Clear = 3, Return = 4"
        ),
        "{parser}"
    );
}

/// The header names what a body writes, reads and stores through.
///
/// `LK` drops a count through an atomic on `a1 + 8`; `CL_A` only reads a
/// global; `GC` stores nine words through `rdx`, which still holds `a2`
/// after a call to a bare `ret`, so the header names the first eight and
/// counts the rest.
#[test]
fn headers_summarize_effects() {
    let lk = dc(0x4790);
    assert!(lk.contains("// effects: writes a1+8"), "{lk}");
    let cl = dc(0x4220);
    assert!(cl.contains("// effects: reads g64_3090"), "{cl}");
    let gc = dc(0x4180);
    assert!(
        gc.contains("// effects: writes a2, a2+4, a2+8, a2+0xc") && gc.contains("(+1 more)"),
        "{gc}"
    );
}

/// A function whose instruction shape others share names one of them.
///
/// `SP1` and `SP2` differ only in constants; each header points at the
/// other.
#[test]
fn near_clones_name_their_shape_class_in_the_header() {
    let out = dc(0x4990);
    assert!(
        out.contains("// shape: ") && out.contains("e.g. 0x49a0"),
        "{out}"
    );
    assert!(!out.contains("// clones:"), "{out}");
}

/// The binary-wide table listing finds every function that encodes a name
/// table, and nothing else.
///
/// `EN` (a parser), `EN2` and `EN3` (constant-to-string tables) are the
/// fixture's three tables.
#[test]
fn enum_tables_list_every_name_table_once() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let tables = enum_tables(&p, &a, &Overlay::default());
    let entries: Vec<u64> = tables.iter().map(|(e, _)| *e).collect();
    assert_eq!(entries, vec![0x47b0, 0x4830, 0x4a50], "{tables:?}");
    assert!(
        tables.iter().all(|(_, t)| t.members.len() == 4),
        "{tables:?}"
    );
    assert_eq!(tables[0].1.name, "by Base::vfunc_1 compare");
}

/// With the binary's tables in the overlay, callers render constants by
/// their member names.
///
/// `CE1` compares `EN`'s result with 3, which `EN` maps from `"Clear"`;
/// `CE2` passes 2 to `EN2`, which names it `"Over"`.
#[test]
fn callers_render_constants_by_their_enum_names() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.enums = enums_by_name(&a, &o, &enum_tables(&p, &a, &o)).into();
    let compare = decompile(&p, &a, &o, 0x4a20).expect("decompile");
    assert!(compare.contains("Clear"), "{compare}");
    assert!(
        !compare.contains("== 3") && !compare.contains("!= 3"),
        "{compare}"
    );
    let pass = decompile(&p, &a, &o, 0x4a40).expect("decompile");
    assert!(pass.contains("sub_4830(Over)"), "{pass}");
    let plain = decompile(&p, &a, &Overlay::default(), 0x4a20).expect("decompile");
    assert!(plain.contains("sub_47b0(a1) != 3)"), "{plain}");
}

/// The binary's own tables, each read when a body names its function,
/// render every function as the whole binary's tables do.
///
/// Besides the fixture's own names, one overlay names `EN2` and `EN3`
/// alike (the later function's table wins the name) and one names `EN`
/// `TryGet` and `EN3` `Get`, so `CE1`'s call is found by a name's tail as
/// well: the tie and the tail are both looked up as the whole tables would.
#[test]
fn tables_read_on_demand_render_as_the_whole_binarys() {
    use borer_engine::analysis::decompile::decompile_named;
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut tie = Overlay::default();
    tie.names.insert(0x4830, "Pick".to_owned());
    tie.names.insert(0x4a50, "Pick".to_owned());
    let mut tail = Overlay::default();
    tail.names.insert(0x47b0, "TryGet".to_owned());
    tail.names.insert(0x4a50, "Get".to_owned());
    for o in [Overlay::default(), tie, tail] {
        let mut given = o.clone();
        given.enums = enums_by_name(&a, &o, &enum_tables(&p, &a, &o)).into();
        let binary = Overlay {
            enum_source: EnumSource::Binary,
            ..o.clone()
        };
        for f in &a.functions {
            assert_eq!(
                decompile(&p, &a, &binary, f.entry),
                decompile(&p, &a, &given, f.entry),
                "{:#x} under {:?}",
                f.entry,
                o.names
            );
            assert_eq!(
                decompile_named(&p, &a, &binary, f.entry),
                decompile_named(&p, &a, &given, f.entry),
                "{:#x} under {:?}",
                f.entry,
                o.names
            );
        }
    }
    let binary = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    let compare = decompile(&p, &a, &binary, 0x4a20).expect("decompile");
    assert!(compare.contains("Clear"), "{compare}");
    let plain = decompile(&p, &a, &Overlay::default(), 0x4a20).expect("decompile");
    assert!(plain.contains("sub_47b0(a1) != 3)"), "{plain}");
}

/// A recovered table's members name the cases that test them.
///
/// `EN2` switches on `a1`. The arms print `case Normal:` through
/// `case Down:`. The default returns a null pointer, `return 0`, which is
/// not one of those cases, so it stays a number. The header keeps the
/// numbers the table was read from.
#[test]
fn a_recovered_enum_names_its_cases() {
    let out = dc(0x4830);
    assert!(
        out.contains("// enum values of a1: 4 values, Normal = 0, Pressed = 1, Over = 2, Down = 3"),
        "{out}"
    );
    assert!(out.contains("case Normal:"), "{out}");
    assert!(out.contains("case Pressed:"), "{out}");
    assert!(out.contains("case Over:"), "{out}");
    assert!(out.contains("case Down:"), "{out}");
    assert!(out.contains("return \"Normal\";"), "{out}");
    assert!(out.contains("default: {\n  return 0;\n}"), "{out}");
    assert!(!out.contains("case 0:"), "{out}");
    assert!(!out.contains("case 1:"), "{out}");
    assert!(!out.contains("case 2:"), "{out}");
    assert!(!out.contains("case 3:"), "{out}");
}

/// A pointer read through often enough gets a layout and named fields.
///
/// `LY` touches three dword fields of `a1`: the header lists them with
/// their widths and each access reads as `a1->field_0x18`; the sum is
/// stored and returned, so it is computed once.
#[test]
fn pointers_read_often_get_a_layout() {
    let out = dc(0x4c10);
    assert!(
        out.contains("// layout a1: 0x18 u32, 0x1c u32, 0x20 u32"),
        "{out}"
    );
    assert!(
        out.contains("var1 = a1->field_0x18 + a1->field_0x1c;"),
        "{out}"
    );
    assert!(out.contains("a1->field_0x20 = var1;"), "{out}");
    assert!(!out.contains("*(uint32_t*)"), "{out}");
}

/// A struct the user applied to a global's pointer names the fields read
/// through it, at the width each field states.
///
/// `UT` reads the object the global at 0x3400 points at: with `Player`
/// applied there as a `Player *`, each dword load at a stated `u32` field
/// renders by that field's name, and a field stated wider than the read
/// (`gold` an `i64` over a dword load) stays an offset access the layout
/// pass names, since reading it as the field would state a width the type
/// does not.
#[test]
fn an_applied_struct_names_the_fields_it_reads() {
    use borer_engine::analysis::utypes::{build_struct, parse_type};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let fields = vec![
        (0x18, "hp".to_owned(), parse_type("u32").unwrap()),
        (0x1c, "mp".to_owned(), parse_type("u32").unwrap()),
        (0x20, "gold".to_owned(), parse_type("i64").unwrap()),
    ];
    let player = build_struct("Player", None, &fields, &o.types, 8).unwrap();
    o.types.insert("Player".to_owned(), player);
    o.applied.insert(0x3400, parse_type("Player *").unwrap());
    let text = decompile(&p, &a, &o, 0x55c0).unwrap_or_default();
    assert!(text.contains("g64_3400->hp"), "{text}");
    assert!(text.contains("g64_3400->mp"), "{text}");
    assert!(
        !text.contains("->gold"),
        "a dword read named as an i64 field:\n{text}"
    );
    assert!(text.contains("->field_0x20"), "{text}");
}

/// An enum the user applied to a global names the constants a function
/// compares it with.
///
/// `EN` compares the dword global at 0x3420 with 1 and 2: with `State`
/// applied there, each compare renders by its member name, a value the enum
/// does not state stays a number, and without the application the constants
/// stay numbers too.
#[test]
fn an_applied_enum_names_compared_constants() {
    use borer_engine::analysis::utypes::{build_enum, parse_type};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let stated = [
        (2u64, "Done".to_owned()),
        (0u64, "Idle".to_owned()),
        (1u64, "Run".to_owned()),
    ];
    o.types
        .insert("State".to_owned(), build_enum("State", 4, &stated).unwrap());
    o.applied.insert(0x3420, parse_type("State").unwrap());
    let text = decompile(&p, &a, &o, 0x55e0).unwrap_or_default();
    assert!(text.contains("Run"), "{text}");
    assert!(text.contains("Done"), "{text}");
    assert!(!text.contains("== 1") && !text.contains("== 2"), "{text}");
    let plain = decompile(&p, &a, &Overlay::default(), 0x55e0).unwrap_or_default();
    assert!(plain.contains("== 1") && plain.contains("== 2"), "{plain}");
}

/// An enum-typed field of a user-applied struct names the constants its
/// accesses are compared with.
///
/// `EF` reads the dword at offset 8 of the object the global at 0x3430
/// points at and compares it with 1 and 2: with `Item` applied there
/// carrying an `ItemState` field at 8, the access renders `->state` and
/// each compare names its member; without the application the field is a
/// raw dereference and the constants stay numbers.
#[test]
fn an_applied_enum_field_names_its_accesses() {
    use borer_engine::analysis::utypes::{build_enum, build_struct, parse_type};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let stated = [
        (2u64, "Broken".to_owned()),
        (0u64, "Off".to_owned()),
        (1u64, "On".to_owned()),
    ];
    o.types.insert(
        "ItemState".to_owned(),
        build_enum("ItemState", 4, &stated).unwrap(),
    );
    let fields = vec![(8u64, "state".to_owned(), parse_type("ItemState").unwrap())];
    let item = build_struct("Item", None, &fields, &o.types, 8).unwrap();
    o.types.insert("Item".to_owned(), item);
    o.applied.insert(0x3490, parse_type("Item *").unwrap());
    let text = decompile(&p, &a, &o, 0x56c0).unwrap_or_default();
    assert!(text.contains("->state == On"), "{text}");
    assert!(text.contains("->state == Broken"), "{text}");
    let plain = decompile(&p, &a, &Overlay::default(), 0x56c0).unwrap_or_default();
    assert!(plain.contains("== 1") && plain.contains("== 2"), "{plain}");
    assert!(!plain.contains("->state"), "{plain}");
}

/// The conditions a function asserts head its body as its contract.
///
/// `As::Chk` calls an assert macro whose first argument is the text of the
/// condition, so the header lists it without the reader opening the body.
/// A condition naming a string literal carries single quotes, one carrying
/// a brace is left out, and a call whose second argument is not a source
/// path is not an assert.
#[test]
fn asserted_conditions_head_the_body() {
    let out = dc(0x1810);
    assert!(out.contains("// asserts: f.IsValid()"), "{out}");
    let none = dc(0x11c0);
    assert!(!none.contains("// asserts:"), "{none}");
    let text = concat!(
        "sub_1000(\"StringAtom(\\\"empty\\\") != this->name\", \"util/a.h\", 12);\n",
        "sub_1000(\"lambda { x }\", \"util/a.h\", 13);\n",
        "sub_1000(\"plain\", \"not a path\", 14);\n",
        "sub_1000(\"res\", \"util/a.h\", 15);\n",
    );
    let line = asserts_of(text).unwrap_or_default();
    assert_eq!(line, "StringAtom('empty') != this->name, res", "{line}");
    let quoted = dc(0x4d20);
    assert!(
        quoted.contains("// asserts: StringAtom('x') != f"),
        "{quoted}"
    );
    assert!(
        !quoted
            .lines()
            .any(|l| l.starts_with("//") && l.contains('"'))
    );
}

/// A class flows from a typed parameter into the callee it is passed to.
///
/// `PF`'s signature string types its second parameter `Ns::Thing *`, and it
/// passes that parameter straight to `PG`, which no string names: `PG`'s own
/// parameter is that class.
#[test]
fn a_typed_parameter_carries_its_class_into_the_callee() {
    let out = dc(0x4d70);
    assert!(
        out.contains("// signature: uint64_t sub_4d70(Ns::Thing *a1)"),
        "{out}"
    );
}

/// A function names its own fields from its own assertions.
///
/// `Der::Chk` guards on the field at 8 and asserts `this->count` about it,
/// which is both halves of the name inside one function; knowing the class
/// is what the named decompile needs, and most functions have no name to
/// take a class from, so the plain decompile names it too.
#[test]
fn a_function_names_the_fields_its_own_asserts_name() {
    let out = dc(0x19a0);
    assert!(out.contains("if (this->count == 0) {"), "{out}");
    assert!(!out.contains("field_0x8"), "{out}");
}

/// A function's header says what its callers pass it.
///
/// `PT` reads one argument and its two callers set it to 7 and to 9, so the
/// values a parameter is called with are in the header rather than in every
/// call site a reader would otherwise have to visit.
#[test]
fn the_header_says_what_callers_pass() {
    let out = dc(0x4fd0);
    assert!(out.contains("// callers pass: a1 = 7, 9"), "{out}");
}

/// A field at offset zero takes its name from an assertion too.
///
/// `GZ` guards on `*(uint32_t*)this` and asserts `this->head` about it; the
/// offset-zero spelling has no `+ 0` for the renamer to find, so it needs
/// the form of its own that the layout pass already uses.
#[test]
fn an_assert_names_the_field_at_offset_zero() {
    let out = dc(0x5000);
    assert!(out.contains("if (this->head == 0) {"), "{out}");
}

/// The assertion need not be the line after its guard.
///
/// `GG` calls `ReportAssertFailure` between the two, which is what a caller that
/// spells its own signature out first looks like; the guard is still the
/// nearest line above that opens a block.
#[test]
fn an_assert_a_line_below_its_guard_still_names_the_field() {
    let out = dc(0x5040);
    assert!(out.contains("if (this->tail == 0) {"), "{out}");
}

/// A serializer's header states the message's wire format.
///
/// `EC` hands its stream a 32-bit field and then a 1-bit one; recovering
/// that from an encoder is the work an analyst does by hand for every
/// message in a protocol, and the encoder already states it. Its stream
/// class `Network::Bs` carries no stream word, so the line needs the test
/// pack's `stream Network::`.
#[test]
fn a_serializer_header_states_the_wire_format() {
    assert!(!dc(0x50c0).contains("// wire:"));
    let out = dc_pack(0x50c0);
    assert!(
        out.contains("// wire: 32 bits a1+0x20, 1 bit a1+0x24"),
        "{out}"
    );
}

/// A function's header names the source file it came from.
///
/// `Der::Chk` asserts, and an assertion cites the file it was written in,
/// so the function says which subsystem it belongs to; answering that
/// otherwise means reading its callers.
#[test]
fn a_function_header_names_its_source_file() {
    let out = dc(0x19a0);
    assert!(out.contains("// source: util/fourcc.h"), "{out}");
}

/// An indexed read keeps its expression when its base has a layout.
///
/// `CM` reads three plain fields, which earns its object a layout, and then
/// indexes an array beginning at the first of them; taking the offset from
/// the front of that operand rewrote half the expression away and left text
/// that does not parse.
#[test]
fn an_indexed_read_is_not_rewritten_as_a_field() {
    let out = dc(0x5200);
    for line in out.lines() {
        assert_eq!(
            line.matches('(').count(),
            line.matches(')').count(),
            "unbalanced: {out}"
        );
    }
    assert!(out.contains("a2 * 8"), "{out}");
}

/// A singleton getter's result resolves the virtual call on it.
///
/// `GV` calls slot 1 through the result of `GG`, which returns the global
/// that holds a `Ns::Thing`, so the call resolves to the table's slot 1
/// (`S4`) instead of `->vtable[1]`.
#[test]
fn getter_results_resolve_virtual_calls() {
    let out = dc(0x1c20);
    assert!(out.contains("->sub_1bf0("), "{out}");
    assert!(!out.contains("->vtable["), "{out}");
}

/// A smart pointer's arrow operator types the call it feeds.
///
/// `PA` is declared `class Der *__cdecl Core::Ptr<class Der>::operator
/// ->(void) const`, a signature whose `->` once broke the parse, so it is
/// named and returns `Der *`; `PB` calls slot 1 through its result, which
/// resolves to `Der`'s method.
#[test]
fn arrow_operator_signatures_type_their_results() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let pa = a.function(0x1b90).expect("PA");
    assert_eq!(pa.name.as_deref(), Some("Core::Ptr<Der>::operator ->"));
    let pb = decompile(&p, &a, &o, 0x1ba0).unwrap_or_default();
    let der_slot1 = borer_engine::analysis::name_of(&a, &o, 0x1200);
    assert!(pb.contains(&format!("->{der_slot1}(")), "{pb}");
    assert!(!pb.contains("->vtable["), "{pb}");
}

/// A virtual call nothing resolves names its slot.
///
/// `VU` calls slot 2 of `a1`'s vtable and no declaration types `a1`, so
/// the call reads `a1->vtable[2]()` with the receiver dropped from the
/// arguments instead of the double dereference.
#[test]
fn unresolved_virtual_calls_name_their_slot() {
    let out = dc(0x1b80);
    assert!(out.contains("a1->vtable[2]()"), "{out}");
    assert!(!out.contains("(*(uint64_t*)(*(uint64_t*)"), "{out}");
}

/// The skeleton's header is one line.
///
/// `ES`'s full text opens with the `// exported_es @ ...` line, the
/// `// signature:` line and an escape note; its skeleton folds the
/// signature into the header and drops the note.
#[test]
fn skeleton_header_is_one_line_without_notes() {
    let full = dc(0x1410);
    assert!(full.contains("// signature: "), "{full}");
    assert!(full.contains("// note: "), "{full}");
    let sk = skeleton(&full);
    let head = sk.lines().next().unwrap_or_default();
    assert!(
        head.starts_with("// uint64_t exported_es(") && head.contains(") @ 0x1410: "),
        "{sk}"
    );
    assert!(!sk.contains("// signature: "), "{sk}");
    assert!(!sk.contains("// note: "), "{sk}");
}

/// Template arguments shrink to `<..>` in the skeleton.
///
/// `Der::Use` is declared `void Der::Use(const class Core::Ptr<class Der>
/// &)`, so its full text names the parameter `Core::Ptr<Der>` and its
/// skeleton `Core::Ptr<..>`.
#[test]
fn skeleton_elides_template_arguments() {
    let full = dc(0x17b0);
    assert!(full.contains("Core::Ptr<Der>"), "{full}");
    let sk = skeleton(&full);
    assert!(sk.contains("Core::Ptr<..>"), "{sk}");
    assert!(!sk.contains("Core::Ptr<Der>"), "{sk}");
}

/// The skeleton folds an assert helper called outright.
///
/// `AH` calls `AK("n == 1", "n must be one", "src/ah.cc", 0x1c2)`, which
/// the full text shows as the call and the skeleton as `assert(n == 1);`.
#[test]
fn skeleton_folds_assert_helper_calls() {
    let full = dc(0x1b50);
    assert!(
        full.contains("sub_1b40(\"n == 1\", \"n must be one\", \"src/ah.cc\", 0x1c2);"),
        "{full}"
    );
    let sk = skeleton(&full);
    assert!(sk.contains("assert(n == 1);"), "{sk}");
    assert!(!sk.contains("sub_1b40"), "{sk}");
}

/// The skeleton folds a guarded assert into one line.
///
/// `AG`'s `if (this == nullptr) { ReportAssertFailure("f.IsValid()", ...); }`
/// becomes `assert(f.IsValid());` while the full text keeps the guard. `this` is a
/// pointer, so the zero test is `nullptr`, not `0`.
#[test]
fn skeleton_folds_guarded_asserts() {
    let full = dc(0x1840);
    assert!(full.contains("if (this == nullptr) {"), "{full}");
    let skel = skeleton(&full);
    assert!(skel.contains("assert(f.IsValid());"), "{skel}");
    assert!(!skel.contains("ReportAssertFailure"), "{skel}");
}

/// A parameter class hinted by callers shows in the header: `HT`, called
/// by `Der::Tick` with its `this`, renders `uint32_t sub_18d0(Der *a1)`.
#[test]
fn hinted_parameter_classes_render_in_the_header() {
    let text = dc(0x18d0);
    assert!(
        text.contains("// signature: uint32_t sub_18d0(Der *a1)"),
        "{text}"
    );
}

/// Hinted result and field classes drive headers and virtual calls.
///
/// `GT` heads `Base *sub_18e0(Der *a1)`, and `Der::Poll`'s call through the
/// vtable of its field at 0x10 resolves to `Base`'s slot 1.
#[test]
fn hinted_results_and_fields_resolve_virtual_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let gt = decompile(&p, &a, &o, 0x18e0).unwrap_or_default();
    assert!(gt.contains("// signature: Base *sub_18e0(Der *a1)"), "{gt}");
    let poll = decompile(&p, &a, &o, 0x18f0).unwrap_or_default();
    let method = |va: u64| {
        let full = borer_engine::analysis::name_of(&a, &o, va);
        full.rsplit("::").next().unwrap_or(&full).to_owned()
    };
    let slot = method(0x11e0);
    assert!(poll.contains(&format!("->{slot}(")), "{poll}");
    let wait = decompile(&p, &a, &o, 0x1920).unwrap_or_default();
    let der_slot1 = method(0x1200);
    assert!(wait.contains(&format!("->{der_slot1}(")), "{wait}");
    let peek = decompile(&p, &a, &o, 0x1960).unwrap_or_default();
    assert!(peek.contains(&format!("var1->{der_slot1}(")), "{peek}");
    let local = decompile(&p, &a, &o, 0x1a00).unwrap_or_default();
    assert!(local.contains("Fac::Make(&local_"), "{local}");
    assert!(local.contains(&format!("->{der_slot1}(")), "{local}");
}

/// A function named after a class through its vtable slot, with that class
/// hinted for its first parameter, is a method: `Der::Foo` heads
/// `uint32_t Der::Foo(Der *this)`.
#[test]
fn slot_named_methods_get_this() {
    let text = dc(0x1870);
    assert!(
        text.contains("// signature: uint32_t Der::Foo(Der *this)"),
        "{text}"
    );
}

/// The named variant renders fields by their assert-derived names.
///
/// `Der::Chk`'s guard reads `this->count`, and `Der::Cmp` copies
/// `a2->count` from its `Der *` parameter. `Der::Cmp` asserts nothing
/// itself, so only the class knows what its field is called and the plain
/// decompile leaves it an offset.
#[test]
fn named_decompile_renders_fields_by_name() {
    use borer_engine::analysis::decompile::decompile_named;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile_named(&p, &a, &o, 0x19a0).unwrap_or_default();
    assert!(text.contains("if (this->count == 0) {"), "{text}");
    let plain = decompile(&p, &a, &o, 0x19d0).unwrap_or_default();
    assert!(!plain.contains("->count"), "{plain}");
    let cmp = decompile_named(&p, &a, &o, 0x19d0).unwrap_or_default();
    assert!(cmp.contains("this->count = a2->count;"), "{cmp}");
}

/// A member field a constructor types resolves the calls made through it.
///
/// `Wrap::Wrap` inlines the base's initializing store, writing `WBase`'s
/// vtable at `[this+8]`, so the embedded subobject at 8 is a `WBase`:
/// `Wrap::Call`'s call through that field's vtable resolves to `WBase`'s
/// slot 1. `Wrap::Miss` calls through the field at 0x10, which nothing
/// types, and its call still names the slot.
#[test]
fn embedded_field_receivers_resolve_their_virtual_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let ctor = decompile(&p, &a, &o, 0x5800).unwrap_or_default();
    assert!(ctor.contains("&WBase::vftable;"), "{ctor}");
    let call = decompile(&p, &a, &o, 0x5830).unwrap_or_default();
    let slot1 = borer_engine::analysis::name_of(&a, &o, 0x5876);
    assert!(call.contains(&format!("{slot1}(this);")), "{call}");
    assert!(!call.contains("->vtable["), "{call}");
    assert_eq!(
        borer_engine::analysis::decompile::virtual_callees(&p, &a, &o, 0x5830),
        vec![0x5876]
    );
    let miss = decompile(&p, &a, &o, 0x5850).unwrap_or_default();
    assert!(miss.contains("->vtable[1]()"), "{miss}");
}

/// A home slot whose address escaped is written out before the call that
/// reads it renders.
///
/// `mov [rsp+8],rbx; push rdi; sub rsp,0x20; mov rdi,rcx; mov ebx,edx; lea
/// rdx,[rsp+0x38]; call f; mov edx,[rsp+0x38]; mov rcx,rdi; add edx,ebx;
/// mov [rsp+0x38],edx; call g; ...` with `f` storing through `rdx`: the
/// second call passes the slot's new value, where it once passed `home_8 +
/// a2` after `home_8 += a2;` and so added `a2` twice.
#[test]
fn an_escaped_home_slot_is_written_out_before_the_call_reads_it() {
    let mut code = vec![
        0x48, 0x89, 0x5c, 0x24, 0x08, 0x57, 0x48, 0x83, 0xec, 0x20, 0x48, 0x8b, 0xf9, 0x8b, 0xda,
        0x48, 0x8d, 0x54, 0x24, 0x38, 0xe8, 0x27, 0x00, 0x00, 0x00, 0x8b, 0x54, 0x24, 0x38, 0x48,
        0x8b, 0xcf, 0x03, 0xd3, 0x89, 0x54, 0x24, 0x38, 0xe8, 0x35, 0x00, 0x00, 0x00, 0x48, 0x8b,
        0x5c, 0x24, 0x30, 0x48, 0x83, 0xc4, 0x20, 0x5f, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xc7, 0x02, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x89, 0xd0, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("home_8 += a2;"), "{text}");
    assert!(text.contains("sub_140001060(a1, home_8);"), "{text}");
}

/// A call passes every argument up to the last the callee reads.
///
/// `sub rsp,0x28; lea rdx,[rsp+0x20]; call f; mov eax,[rsp+0x20]; add
/// rsp,0x28; ret`, with `f` writing through `rdx` alone: the callee's
/// first slot is one it never reads, and the register the caller left in
/// it is what the call passes there, so the list goes on to the address
/// the callee writes through, where it once stopped at the empty slot and
/// left the local unset. A tail jump hands on the caller's own parameters
/// in the registers it never wrote: `mov rcx,[rcx]; jmp g` at 0x1020,
/// with `g` reading `r9` past a call and a stack argument, passes all
/// five.
#[test]
fn a_call_passes_its_arguments_past_a_slot_the_callee_skips() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x20, 0xe8, 0x32, 0x00, 0x00, 0x00, 0x8b,
        0x44, 0x24, 0x20, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xc7, 0x02, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(
        text.lines()
            .any(|l| l.contains("sub_140001040(rcx, &local_")),
        "{text}"
    );
    assert!(
        text.lines()
            .any(|l| l.starts_with("uint64_t ") && l.contains("rcx")),
        "{text}"
    );
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x48, 0x8b, 0x09, 0xe9, 0x18, 0x00, 0x00, 0x00]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x85, 0xc9, 0x74, 0x06, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xc3, 0x4c, 0x89, 0xc8, 0x48, 0x03,
        0x44, 0x24, 0x28, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.push(0xc3);
    let text = decompiled(&program64(&code), 0x1_4000_1020);
    assert!(
        text.contains("sub_140001040(*(uint64_t*)a1, a2, a3, a4, a5);"),
        "{text}"
    );
}

/// A callee whose result is only the low byte of `rax` merges into what
/// the caller had there, and a caller that returns it returns the merge.
///
/// `mov rax,rcx; mov dl,[rcx]; and dl,1; call BYTESET; ret`, where
/// `BYTESET` is `mov al,dl; mov [rcx],dl; ret`, leaves the machine's `rax`
/// as the caller's pointer with the callee's byte in its low lane; the
/// text once claimed the byte alone, and a run answered without the
/// pointer's bits.
#[test]
fn a_narrow_callee_result_merges_into_the_callers_rax() {
    let mut code = vec![
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0x8a, 0x11, // ASM: mov dl,[rcx]
        0x80, 0xe2, 0x01, // ASM: and dl,1
        0xe8, 0x13, 0x00, 0x00, 0x00, // ASM: call 0x140001020
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x88, 0xd0, // ASM: mov al,dl
        0x88, 0x11, // ASM: mov [rcx],dl
        0xc3, // ASM: ret
    ]);
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(a1 & ~0xff) | ("), "the merge: {text}");
}

/// A word shifted into the high half of a 64-bit result keeps its bits.
///
/// `mov eax,[rcx]; movzx edx,word [rcx+4]; shl rdx,0x20; or rax,rdx; ret`
/// shifts in 64 bits, where the text's `*(uint16_t*)(a1 + 4) << 0x20`
/// shifted an `int` by 32 and lost the word: the shift is cast to
/// `uint64_t` first.
#[test]
fn a_narrow_load_shifted_into_the_high_half_keeps_its_bits() {
    let code = [
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0x0f, 0xb7, 0x51, 0x04, // ASM: movzx edx, word [rcx+4]
        0x48, 0xc1, 0xe2, 0x20, // ASM: shl rdx, 0x20
        0x48, 0x09, 0xd0, // ASM: or rax, rdx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(
        text.contains("(uint64_t)*(uint16_t*)(a1 + 4) << 0x20"),
        "{text}"
    );
}

/// A store narrower than a word keeps the value's low bits without a mask.
///
/// The byte `lea eax, [rcx+rdx]; mov [r8], al` stores and the swapped word
/// `bswap ecx; mov [r8+4], ecx` stores truncate as C's assignment does,
/// so neither shows the `& 0xff` or `& 0xffffffff` the register reads
/// carried.
#[test]
fn a_narrow_store_shows_no_mask_of_what_it_drops() {
    let code = [
        0x8d, 0x04, 0x11, // ASM: lea eax, [rcx + rdx]
        0x41, 0x88, 0x00, // ASM: mov byte ptr [r8], al
        0x0f, 0xc9, // ASM: bswap ecx
        0x41, 0x89, 0x48, 0x04, // ASM: mov dword ptr [r8 + 0x4], ecx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(!text.contains("& 0xff"), "{text}");
}

/// A load wider than the slot it starts at reads the slots above it too.
///
/// `mov byte [rsp+4],1; mov [rsp+5],r9b; mov [rsp+6],r8w; mov edx,[rsp+4];
/// mov [rcx+8],edx` packs three slots into one dword, as a Rust enum's
/// constructor does: the text's `local_c`, a `uint8_t`, read one byte of
/// the four, and the three above it were lost. The word the two byte
/// stores at `[rsp+8]` fill reads as the value they compose.
#[test]
fn a_load_wider_than_its_slot_reads_the_slots_above() {
    let code = [
        0x48, 0x83, 0xec, 0x10, // ASM: sub rsp, 0x10
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx
        0x88, 0x54, 0x24, 0x0b, // ASM: mov [rsp+0xb], dl
        0x66, 0x44, 0x89, 0x44, 0x24, 0x0c, // ASM: mov [rsp+0xc], r8w
        0x44, 0x88, 0x4c, 0x24, 0x0f, // ASM: mov [rsp+0xf], r9b
        0xc6, 0x44, 0x24, 0x04, 0x01, // ASM: mov byte [rsp+4], 1
        0x44, 0x88, 0x4c, 0x24, 0x05, // ASM: mov [rsp+5], r9b
        0x66, 0x44, 0x89, 0x44, 0x24, 0x06, // ASM: mov [rsp+6], r8w
        0x88, 0x54, 0x24, 0x08, // ASM: mov [rsp+8], dl
        0x88, 0x54, 0x24, 0x09, // ASM: mov [rsp+9], dl
        0x48, 0x8d, 0x15, 0x1b, 0x00, 0x00, 0x00, // ASM: lea rdx, [rel 0x140001040]
        0x48, 0x89, 0x11, // ASM: mov [rcx], rdx
        0x8b, 0x54, 0x24, 0x04, // ASM: mov edx, [rsp+4]
        0x89, 0x51, 0x08, // ASM: mov [rcx+8], edx
        0x66, 0x8b, 0x54, 0x24, 0x08, // ASM: mov dx, [rsp+8]
        0x66, 0x89, 0x51, 0x0c, // ASM: mov [rcx+0xc], dx
        0x48, 0x83, 0xc4, 0x10, // ASM: add rsp, 0x10
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("*(uint32_t*)&local_4"), "{text}");
    assert!(text.contains("(a2 << 8) | a2"), "{text}");
}

/// A parameter typed narrow from its masks keeps the bits a shift moves
/// past them.
///
/// `mov eax,edx; shl rax,0xa; and ecx,0x3ff; or rax,rcx; ret` packs `a2`
/// above ten bits of `a1` in 64 bits. Every use of `a2` was masked to 32
/// bits, so the header declares it `uint32_t` and the masks go; the shift
/// then ran in `unsigned int` and lost the bits past 32: it is cast to
/// `uint64_t` in their place.
#[test]
fn a_parameter_typed_narrow_keeps_what_a_shift_moves_past_it() {
    let code = [
        0x89, 0xd0, // ASM: mov eax, edx
        0x48, 0xc1, 0xe0, 0x0a, // ASM: shl rax, 0xa
        0x81, 0xe1, 0xff, 0x03, 0x00, 0x00, // ASM: and ecx, 0x3ff
        0x48, 0x09, 0xc8, // ASM: or rax, rcx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(uint64_t)a2 << 0xa"), "{text}");
}

/// A parameter typed narrow from its masks compares a difference of it as
/// the machine does, unsigned.
///
/// `movzx eax,cl; sub rax,7; cmp rax,3; jb L; xor eax,eax; ret; L: mov
/// eax,1; ret` tests `a1` in 7..10 with one unsigned compare. Typed
/// `uint8_t`, `a1 - 7` was an `int`, negative below 7, and the compare
/// held for every such `a1`.
#[test]
fn a_parameter_typed_narrow_compares_its_difference_unsigned() {
    let code = [
        0x0f, 0xb6, 0xc1, // ASM: movzx eax, cl
        0x48, 0x83, 0xe8, 0x07, // ASM: sub rax, 7
        0x48, 0x83, 0xf8, 0x03, // ASM: cmp rax, 3
        0x72, 0x03, // ASM: jb 0x140001010
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(uint64_t)a1 - 7 < 3"), "{text}");
}

/// Two structures of two `int`s passed by value at `-O0`, each spilled
/// whole from its register and read back a field at a time, and one
/// built a field at a time and read back whole as the result.
///
/// `cross(P p, P q)` is `p.x * q.y - p.y * q.x` and `mk(a, b)` returns
/// `{a + b, a - b}` in `rax`, as clang `-O0` for System V x86-64 builds
/// them. The fields' slots lie inside the whole one's, and each slot's text
/// variable held only its own store: `p.y` read a variable nothing
/// assigned, and the result read two variables as one.
#[test]
fn a_structure_spilled_whole_reads_back_by_field() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let code = [
        0x55, // ASM: push rbp (cross)
        0x48, 0x89, 0xe5, // ASM: mov rbp,rsp
        0x48, 0x89, 0x7d, 0xf8, // ASM: mov [rbp-0x8],rdi
        0x48, 0x89, 0x75, 0xf0, // ASM: mov [rbp-0x10],rsi
        0x8b, 0x45, 0xf8, // ASM: mov eax,[rbp-0x8]
        0x0f, 0xaf, 0x45, 0xf4, // ASM: imul eax,[rbp-0xc]
        0x8b, 0x4d, 0xfc, // ASM: mov ecx,[rbp-0x4]
        0x0f, 0xaf, 0x4d, 0xf0, // ASM: imul ecx,[rbp-0x10]
        0x29, 0xc8, // ASM: sub eax,ecx
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
        0x66, 0x90, // ASM: nop
        0x55, // ASM: push rbp (mk)
        0x48, 0x89, 0xe5, // ASM: mov rbp,rsp
        0x89, 0x7d, 0xf4, // ASM: mov [rbp-0xc],edi
        0x89, 0x75, 0xf0, // ASM: mov [rbp-0x10],esi
        0x8b, 0x45, 0xf4, // ASM: mov eax,[rbp-0xc]
        0x03, 0x45, 0xf0, // ASM: add eax,[rbp-0x10]
        0x89, 0x45, 0xf8, // ASM: mov [rbp-0x8],eax
        0x8b, 0x45, 0xf4, // ASM: mov eax,[rbp-0xc]
        0x2b, 0x45, 0xf0, // ASM: sub eax,[rbp-0x10]
        0x89, 0x45, 0xfc, // ASM: mov [rbp-0x4],eax
        0x48, 0x8b, 0x45, 0xf8, // ASM: mov rax,[rbp-0x8]
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Elf;
    let cross = runs_agree(&p, 0x401_000);
    assert!(cross.contains(">> 32)"), "the high field: {cross}");
    let mk = runs_agree(&p, 0x401_020);
    assert!(mk.contains("<< 0x20"), "the result's high field: {mk}");
}

/// The structure check reads a call to a dotted clone under the name the
/// text spells it with: `.weak.__divti3.default` is called as
/// `_weak___divti3_default(...)`, and the call is the binary's.
#[test]
fn the_structure_check_reads_a_dotted_clone_s_call_as_the_text_spells_it() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![
        0x48, 0x83, 0xec, 0x08, // ASM: sub rsp, 8
        0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x1_4000_1020
        0x48, 0x83, 0xc4, 0x08, // ASM: add rsp, 8
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([0x8d, 0x41, 0x01, 0xc3]); // ASM: lea eax, [rcx + 1]; ret
    let mut p = program64(&code);
    p.symbols.push(Symbol {
        name: ".weak.__divti3.default".to_owned(),
        addr: 0x1_4000_1020,
        kind: SymbolKind::Local,
    });
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("_weak___divti3_default("), "{text}");
    let a = Analysis::compute(&p);
    assert_eq!(
        check_structure(&p, &a, &Overlay::default(), 0x1_4000_1000, &text),
        Structure::Agrees,
        "{text}"
    );
}

/// A read through a scaled index into an array global the debug
/// information types is that element's field.
///
/// `movsxd rax,edi; shl rax,4; lea rdx,[rip+table+8]; mov rax,[rax+rdx];
/// ret` reads the pointer at offset 8 of the 16-byte element `a1` of
/// `struct pair table[4]`: the text returns `table[a1].name`.
#[test]
fn an_indexed_read_of_a_stated_table_names_the_field() {
    use borer_engine::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
    use borer_engine::dwarf::Global;
    let code = [
        0x48, 0x63, 0xc7, // ASM: movsxd rax,edi
        0x48, 0xc1, 0xe0, 0x04, // ASM: shl rax,4
        0x48, 0x8d, 0x15, 0xfa, 0x1f, 0x00, 0x00, // ASM: lea rdx,[rip+0x1ffa]
        0x48, 0x8b, 0x04, 0x10, // ASM: mov rax,[rax+rdx]
        0xc3, // ASM: ret
    ];
    let mut p = program64_with_globals(&code, false, &[("table", 0x1_4000_3000)]);
    p.debug_types.insert(
        "pair".to_owned(),
        UserType::Struct(UserStruct {
            size: 16,
            fields: [
                (
                    0,
                    UserField {
                        name: "key".to_owned(),
                        ty: TypeExpr::I16,
                    },
                ),
                (
                    8,
                    UserField {
                        name: "name".to_owned(),
                        ty: TypeExpr::Ptr(Box::new(TypeExpr::Char)),
                    },
                ),
            ]
            .into(),
        }),
    );
    p.debug_globals = vec![Global {
        name: "table".to_owned(),
        addr: Some(0x1_4000_3000),
        type_name: Some("struct pair[]".to_owned()),
        ty: Some(TypeExpr::Array(
            Box::new(TypeExpr::Named("pair".to_owned())),
            4,
        )),
    }];
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("return table[a1].name;"), "{text}");
}
