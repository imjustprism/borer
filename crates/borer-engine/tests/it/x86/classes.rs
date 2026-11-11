//! Classes on 32-bit images: vtables, RTTI, Qt meta-objects and receivers.

use super::*;

/// A class with MSVC run-time type information is named from it, its
/// virtual methods after it, and its parent from the hierarchy descriptor.
///
/// The constructor at 0x401000 stores the vtable at 0x402018, whose
/// locator one word before it (the twenty-byte record at 0x402000) leads
/// to `.?AVFoo@@` and to a base array naming `.?AVBase@@` second; the two
/// slots are `mov eax,1; ret` and `mov eax,2; ret`.
#[test]
fn a_vtable_with_rtti_names_its_class_and_parent() {
    let mut code = vec![0xc7, 0x01, 0x18, 0x20, 0x40, 0x00, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0u32, 0, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x14, &le(0x402000));
    put(&mut data, 0x18, &le(0x401020));
    put(&mut data, 0x1c, &le(0x401030));
    put(&mut data, 0x48, b".?AVFoo@@\0");
    for (k, v) in [0u32, 0, 2, 0x402080].into_iter().enumerate() {
        put(&mut data, 0x70 + k * 4, &le(v));
    }
    put(&mut data, 0x80, &le(0x402090));
    put(&mut data, 0x84, &le(0x4020b0));
    put(&mut data, 0x90, &le(0x402040));
    put(&mut data, 0xb0, &le(0x4020d0));
    put(&mut data, 0xd8, b".?AVBase@@\0");
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401020).as_deref(), Some("Foo::vfunc_0"));
    assert_eq!(name(0x401030).as_deref(), Some("Foo::vfunc_1"));
    let foo = a.classes.by_name.get("Foo").expect("Foo is a class");
    assert_eq!(foo.vtable, Some(0x402018));
    assert_eq!(foo.parent.as_deref(), Some("Base"));
}

/// A global singleton's loaded pointer resolves the virtual call made
/// through it, and a global nothing registered does not.
///
/// The constructor at 0x401000 stores the RTTI-named table of `G2` at
/// `[ecx]` and registers `this` in the global at 0x4020e0, the only
/// global-addressing form 32-bit code has; `GU2` 0x401030 loads that
/// global's word and calls slot 1, which resolves to `G2::vfunc_1`.
/// `GU3` 0x401040 does the same through 0x4020e4, which no constructor
/// registered, so its call names the slot only.
/// A further base's table, stored at `[this+8]` by an inlined base
/// constructor, types the embedded subobject there, and a call through
/// that field resolves to the base's method.
///
/// The constructor at 0x401000 stores `Foo`'s table at `[ecx]` and the
/// further base's table 0x402108 at `[ecx+8]`; `Bar`'s own constructor at
/// 0x401070 stores its table 0x402158, so the embedded subobject at 8 is
/// a `Bar`. `Foo::vfunc_2` 0x401050 calls slot 1 of the vtable at
/// `[ecx+8]`, which resolves to `Bar::vfunc_1`; `Foo::vfunc_3` 0x401060
/// does the same through the field at 0xc, which nothing types, and its
/// call names the slot only.
#[test]
fn embedded_base_fields_resolve_their_calls() {
    let mut code = vec![
        0xc7, 0x01, 0x18, 0x20, 0x40, 0x00, // ASM: mov dword [ecx],0x402018
        0xc7, 0x41, 0x08, 0x08, 0x21, 0x40, 0x00, // ASM: mov dword [ecx+8],0x402108
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x03, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x04, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x8b, 0x41, 0x08, 0xff, 0x50, 0x04, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8b, 0x41, 0x0c, 0xff, 0x50, 0x04, 0xc3]);
    code.resize(0x70, 0xcc);
    code.extend_from_slice(&[0xc7, 0x01, 0x58, 0x21, 0x40, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x170];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0u32, 0, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x14, &le(0x402000));
    put(&mut data, 0x18, &le(0x401030));
    put(&mut data, 0x1c, &le(0x401040));
    put(&mut data, 0x20, &le(0x401050));
    put(&mut data, 0x24, &le(0x401060));
    put(&mut data, 0x48, b".?AVFoo@@\0");
    for (k, v) in [0u32, 0, 2, 0x402080].into_iter().enumerate() {
        put(&mut data, 0x70 + k * 4, &le(v));
    }
    put(&mut data, 0x80, &le(0x402090));
    put(&mut data, 0x84, &le(0x4020a0));
    put(&mut data, 0x90, &le(0x402040));
    for (k, v) in [0x4020c0u32, 0, 8, u32::MAX, 0].into_iter().enumerate() {
        put(&mut data, 0xa0 + k * 4, &le(v));
    }
    put(&mut data, 0xc8, b".?AVBar@@\0");
    for (k, v) in [0u32, 8, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, 0xf0 + k * 4, &le(v));
    }
    put(&mut data, 0x104, &le(0x4020f0));
    put(&mut data, 0x108, &le(0x401010));
    put(&mut data, 0x10c, &le(0x401020));
    for (k, v) in [0u32, 0, 0, 0x4020c0, 0x402070].into_iter().enumerate() {
        put(&mut data, 0x140 + k * 4, &le(v));
    }
    put(&mut data, 0x154, &le(0x402140));
    put(&mut data, 0x158, &le(0x401010));
    put(&mut data, 0x15c, &le(0x401020));
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes
            .secondary_vtables
            .get(&0x402108)
            .map(String::as_str),
        Some("Foo::vftable_Bar")
    );
    let call = decompile(&p, &a, &o, 0x401050).unwrap_or_default();
    assert!(call.contains("Bar::vfunc_1(this);"), "{call}");
    assert!(!call.contains("->vtable["), "{call}");
    assert_eq!(
        borer_engine::analysis::decompile::virtual_callees(&p, &a, &o, 0x401050),
        vec![0x401020]
    );
    let miss = decompile(&p, &a, &o, 0x401060).unwrap_or_default();
    assert!(miss.contains("->vtable[1]()"), "{miss}");
}

/// A slot holding an import thunk does not name the class after the
/// import's class: the table is this image's, the class the thunk names
/// lives in the DLL.
///
/// The constructor at 0x401000 stores the table at 0x402010, whose first
/// slot is the thunk `jmp [0x402100]` at 0x401010 through the import
/// `QNetworkCookieJar::insertCookie` and whose second is `mov eax,1; ret`
/// at 0x401020. Without run-time type information the class is
/// `class_402010`, not `Qt5Network.dll!QNetworkCookieJar`.
#[test]
fn an_import_thunk_in_a_slot_does_not_name_the_class_after_the_import() {
    let mut code = vec![0xc7, 0x01, 0x10, 0x20, 0x40, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xff, 0x25, 0x00, 0x21, 0x40, 0x00]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut data = vec![0u8; 0x110];
    data[0x10..0x14].copy_from_slice(&0x401010u32.to_le_bytes());
    data[0x14..0x18].copy_from_slice(&0x401020u32.to_le_bytes());
    let mut p = image_with_data(&code, &data);
    p.symbols = vec![Symbol {
        name: "Qt5Network.dll!?insertCookie@QNetworkCookieJar@@UAE_NABVQNetworkCookie@@@Z"
            .to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let names: Vec<&String> = a.classes.by_name.keys().collect();
    assert!(a.classes.by_name.contains_key("class_402010"), "{names:?}");
    assert!(names.iter().all(|n| !n.contains('!')), "{names:?}");
}

/// A further base's vtable, stored at `[this+8]` and named by a locator
/// with subobject offset 8, renders as the class's table for the base the
/// hierarchy places at that offset.
///
/// The constructor at 0x401000 stores 0x402018 at `[ecx]` and 0x402108 at
/// `[ecx+8]`; the second table's locator at 0x4020f0 names `Foo` at
/// offset 8, and `Foo`'s base array lists `Bar` with displacement 8.
#[test]
fn a_further_bases_vtable_is_named_after_its_base() {
    let mut code = vec![
        0xc7, 0x01, 0x18, 0x20, 0x40, 0x00, 0xc7, 0x41, 0x08, 0x08, 0x21, 0x40, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x120];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0u32, 0, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x14, &le(0x402000));
    put(&mut data, 0x18, &le(0x401020));
    put(&mut data, 0x1c, &le(0x401030));
    put(&mut data, 0x48, b".?AVFoo@@\0");
    for (k, v) in [0u32, 0, 2, 0x402080].into_iter().enumerate() {
        put(&mut data, 0x70 + k * 4, &le(v));
    }
    put(&mut data, 0x80, &le(0x402090));
    put(&mut data, 0x84, &le(0x4020a0));
    put(&mut data, 0x90, &le(0x402040));
    for (k, v) in [0x4020c0u32, 0, 8, u32::MAX, 0].into_iter().enumerate() {
        put(&mut data, 0xa0 + k * 4, &le(v));
    }
    put(&mut data, 0xc8, b".?AVBar@@\0");
    for (k, v) in [0u32, 8, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, 0xf0 + k * 4, &le(v));
    }
    put(&mut data, 0x104, &le(0x4020f0));
    put(&mut data, 0x108, &le(0x401020));
    put(&mut data, 0x10c, &le(0x401030));
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes
            .secondary_vtables
            .get(&0x402108)
            .map(String::as_str),
        Some("Foo::vftable_Bar")
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("&Foo::vftable_Bar"), "{text}");
    assert!(
        text.contains("&Foo::vftable;") || text.contains("&Foo::vftable,"),
        "{text}"
    );
}

/// The static data a `QStringLiteral` or `QByteArrayLiteral` expands to,
/// a `QArrayData` header before the text, renders as the literal, and the
/// lambda storing it is named after the macro and the text.
///
/// Two lambdas of the kind the macros produce: `mov dword [ecx], 0x402000;
/// mov eax, ecx; ret` at 0x401000 with `{-1, 5, 0, 16}` and `u"Hello"`
/// at 0x402000, and the same at 0x401010 storing 0x402030, where
/// `{-1, 3, 0, 16}` and `"abc"` lie.
#[test]
fn a_qt_literals_static_data_renders_as_the_literal() {
    let mut code = vec![0xc7, 0x01, 0x00, 0x20, 0x40, 0x00, 0x8b, 0xc1, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xc7, 0x01, 0x30, 0x20, 0x40, 0x00, 0x8b, 0xc1, 0xc3]);
    let mut data = vec![0u8; 0x40];
    let header = |len: u32| {
        let mut h = Vec::new();
        for v in [u32::MAX, len, 0, 16] {
            h.extend_from_slice(&v.to_le_bytes());
        }
        h
    };
    data[..16].copy_from_slice(&header(5));
    for (k, c) in "Hello".encode_utf16().enumerate() {
        data[16 + k * 2..18 + k * 2].copy_from_slice(&c.to_le_bytes());
    }
    data[0x30..0x40].copy_from_slice(&header(3));
    data.extend_from_slice(b"abc\0");
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("= QStringLiteral(\"Hello\");"), "{text}");
    let text = decompile(&p, &a, &Overlay::default(), 0x401010).unwrap_or_default();
    assert!(text.contains("= QByteArrayLiteral(\"abc\");"), "{text}");
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401000).as_deref(), Some("QStringLiteral_Hello"));
    assert_eq!(name(0x401010).as_deref(), Some("QByteArrayLiteral_abc"));
}

/// A one-slot table a constructor stores at `[this]` is the class's
/// vtable: `mov dword [ecx],0x402000; ret` over a table whose one slot is
/// `mov eax,1; ret` at 0x401010.
#[test]
fn a_one_slot_table_a_constructor_stores_is_a_vtable() {
    let mut code = vec![0xc7, 0x01, 0x00, 0x20, 0x40, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut data = vec![0x10, 0x10, 0x40, 0x00];
    data.resize(16, 0);
    let text = dc_data(&code, &data, &[]);
    assert!(text.contains("&class_402000::vftable"), "{text}");
}

/// A table an object on the stack points at is a class's vtable: `sub
/// esp,8; mov dword [esp],0x402000; mov eax,[esp]; add esp,8; ret` over a
/// two-slot table, `mov eax,1; ret` at 0x401020 twice.
#[test]
fn a_table_a_stack_object_points_at_is_a_vtable() {
    let mut code = vec![
        0x83, 0xec, 0x08, 0xc7, 0x04, 0x24, 0x00, 0x20, 0x40, 0x00, 0x8b, 0x04, 0x24, 0x83, 0xc4,
        0x08, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut data = vec![0x20, 0x10, 0x40, 0x00, 0x20, 0x10, 0x40, 0x00];
    data.resize(16, 0);
    let text = dc_data(&code, &data, &[]);
    assert!(text.contains("&class_402000::vftable"), "{text}");
}

/// A class `moc` described is read from its string table, meta-data and
/// meta-object, its dispatcher names the slot's function, and the
/// meta-object's address renders as the class's `staticMetaObject`.
///
/// The string table at 0x402000 holds `Foo` and `doIt`; the meta-data at
/// 0x402030 declares one public slot; the meta-object at 0x402080 points
/// at both and at the dispatcher at 0x401020, `if (_c == 0 && _id == 0)
/// _t->doIt()`, which calls the function at 0x401000. The function at
/// 0x401040 is `mov eax, 0x402080; ret`.
#[test]
fn a_moc_described_class_names_its_slot() {
    use borer_engine::analysis::render::qt_tsv;
    let mut code = vec![0x8b, 0x41, 0x04, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x44, 0x24, 0x08, 0x0b, 0x44, 0x24, 0x0c, 0x75, 0x0a, 0x8b, 0x4c, 0x24, 0x04, 0xe8,
        0xcd, 0xff, 0xff, 0xff, 0xc3, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x80, 0x20, 0x40, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0xffff_ffffu32, 3, 0, 0x20, 0xffff_ffff, 4, 0, 0x14]
        .into_iter()
        .enumerate()
    {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x20, b"Foo\0doIt\0");
    let meta = [
        7u32, 0, 0, 0, 1, 14, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 19, 2, 0x0a,
    ];
    for (k, v) in meta.into_iter().enumerate() {
        put(&mut data, 0x30 + k * 4, &le(v));
    }
    for (k, v) in [0u32, 0x402000, 0x402030, 0x401020, 0, 0]
        .into_iter()
        .enumerate()
    {
        put(&mut data, 0x80 + k * 4, &le(v));
    }
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401000).as_deref(), Some("Foo::doIt"));
    let text = qt_tsv(&a);
    assert!(
        text.contains("class Foo  (staticMetaObject 0x402080, qt_static_metacall 0x401020)"),
        "{text}"
    );
    assert!(text.contains("slots: doIt@0x401000"), "{text}");
    let text = decompile(&p, &a, &Overlay::default(), 0x401040).unwrap_or_default();
    assert!(text.contains("return &Foo::staticMetaObject;"), "{text}");
}

/// A class `moc` described with no signals, slots or properties, whose
/// string table is its name alone and whose method offset is zero, is
/// listed, so its meta-object is named where it is returned.
///
/// The string table at 0x402000 holds only `Foo`; the meta-data at
/// 0x402030 declares nothing; the meta-object at 0x402080 points at both
/// and has no dispatcher. The function at 0x401000 is `mov eax,
/// 0x402080; ret`.
#[test]
fn a_moc_class_with_nothing_declared_is_listed() {
    use borer_engine::analysis::render::qt_tsv;
    let code = [0xb8, 0x80, 0x20, 0x40, 0x00, 0xc3];
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0xffff_ffffu32, 3, 0, 0x10].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x10, b"Foo\0");
    for (k, v) in [7u32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        .into_iter()
        .enumerate()
    {
        put(&mut data, 0x30 + k * 4, &le(v));
    }
    for (k, v) in [0u32, 0x402000, 0x402030, 0, 0, 0].into_iter().enumerate() {
        put(&mut data, 0x80 + k * 4, &le(v));
    }
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let text = qt_tsv(&a);
    assert!(
        text.contains("class Foo  (staticMetaObject 0x402080)"),
        "{text}"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("return &Foo::staticMetaObject;"), "{text}");
}

/// The first three slots of a `Q_OBJECT` class's vtable are named.
///
/// They are `metaObject`, `qt_metacast` and `qt_metacall` once the first
/// is seen to return the class's meta-object; the slot after them keeps
/// its numbered name.
///
/// `Foo`'s string table is at 0x402000 and its meta-object at 0x402080;
/// the locator at 0x4020a0 names `Foo` for the table at 0x402118, whose
/// slots are 0x401000 (`mov eax, 0x402080; ret`), 0x401010, 0x401020 and
/// 0x401030; the constructor at 0x401040 stores the table.
#[test]
fn a_qobjects_first_three_virtuals_are_named() {
    let mut code = vec![0xb8, 0x80, 0x20, 0x40, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0x33, 0xc0, 0xc3]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xc7, 0x01, 0x18, 0x21, 0x40, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x140];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    let words = |data: &mut Vec<u8>, at: usize, values: &[u32]| {
        for (k, v) in values.iter().enumerate() {
            data[at + k * 4..at + k * 4 + 4].copy_from_slice(&le(*v));
        }
    };
    words(&mut data, 0, &[0xffff_ffff, 3, 0, 0x10]);
    put(&mut data, 0x10, b"Foo\0");
    words(&mut data, 0x30, &[7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    words(&mut data, 0x80, &[0, 0x402000, 0x402030, 0, 0, 0]);
    words(&mut data, 0xa0, &[0, 0, 0, 0x4020c0, 0x4020e0]);
    put(&mut data, 0xc8, b".?AVFoo@@\0");
    words(&mut data, 0xe0, &[0, 0, 1, 0x4020f0]);
    words(&mut data, 0xf0, &[0x4020f8]);
    words(&mut data, 0xf8, &[0x4020c0, 0, 0, 0xffff_ffff, 0, 0]);
    words(
        &mut data,
        0x114,
        &[0x4020a0, 0x401000, 0x401010, 0x401020, 0x401030],
    );
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401000).as_deref(), Some("Foo::metaObject"));
    assert_eq!(name(0x401010).as_deref(), Some("Foo::qt_metacast"));
    assert_eq!(name(0x401020).as_deref(), Some("Foo::qt_metacall"));
    assert_eq!(name(0x401030).as_deref(), Some("Foo::vfunc_3"));
}

/// A dispatcher compiled to a compare ladder maps each case by the count
/// it reaches, whatever order the compiler laid the case blocks out in.
///
/// `Bar` declares slots `a`, `b`, `c`; the dispatcher at 0x401030 tests
/// `_c`, loads `_id`, then `sub eax,0; je c0; dec eax; je c1; dec eax;
/// jne exit` with `c2` falling through first and `c0`, `c1` after it.
#[test]
fn a_ladder_dispatcher_maps_its_cases_by_count() {
    let mut code = vec![0x8b, 0x41, 0x04, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0x8b, 0x41, 0x08, 0xc3]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x8b, 0x41, 0x0c, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x44, 0x24, 0x08, 0x85, 0xc0, 0x75, 0x2d, 0x8b, 0x44, 0x24, 0x0c, 0x83, 0xe8, 0x00,
        0x74, 0x10, 0x48, 0x74, 0x17, 0x48, 0x75, 0x1e, 0x8b, 0x4c, 0x24, 0x04, 0xe8, 0xd0, 0xff,
        0xff, 0xff, 0xc3, 0x8b, 0x4c, 0x24, 0x04, 0xe8, 0xa6, 0xff, 0xff, 0xff, 0xc3, 0x8b, 0x4c,
        0x24, 0x04, 0xe8, 0xac, 0xff, 0xff, 0xff, 0xc3, 0xc3,
    ]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    let headers = [
        0xffff_ffffu32,
        3,
        0,
        0x40,
        0xffff_ffff,
        1,
        0,
        0x34,
        0xffff_ffff,
        1,
        0,
        0x26,
        0xffff_ffff,
        1,
        0,
        0x18,
    ];
    for (k, v) in headers.into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x40, b"Bar\0a\0b\0c\0");
    let mut meta = vec![7u32, 0, 0, 0, 3, 14, 0, 0, 0, 0, 0, 0, 0, 0];
    for name in 1..=3u32 {
        meta.extend_from_slice(&[name, 0, 29, 2, 0x0a]);
    }
    for (k, v) in meta.into_iter().enumerate() {
        put(&mut data, 0x50 + k * 4, &le(v));
    }
    for (k, v) in [0u32, 0x402000, 0x402050, 0x401030, 0, 0]
        .into_iter()
        .enumerate()
    {
        put(&mut data, 0xd0 + k * 4, &le(v));
    }
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401000).as_deref(), Some("Bar::a"));
    assert_eq!(name(0x401010).as_deref(), Some("Bar::b"));
    assert_eq!(name(0x401020).as_deref(), Some("Bar::c"));
}

/// A one-slot vtable a constructor stores is named by its complete object
/// locator on a 32-bit image as on a 64-bit one.
///
/// The locator's links are absolute and its signature zero; the class it
/// names (`One`) reaches the table, its constructor and its one virtual
/// method, although nothing but the constructor vouches for the table.
#[test]
fn a_locators_class_names_a_one_slot_table_on_a_32_bit_image() {
    let code = [
        0xb8, 0x58, 0x20, 0x40, 0x00, // ASM: mov eax,0x402058
        0x89, 0x01, // ASM: mov [ecx],eax
        0xc3, // ASM: ret
        0x8b, 0x41, 0x08, // ASM: mov eax,[ecx+8] (S0 at 0x401008)
        0xc3, // ASM: ret
    ];
    let mut data = vec![0u8; 0x60];
    let put = |d: &mut Vec<u8>, at: usize, b: &[u8]| d[at..at + b.len()].copy_from_slice(b);
    put(&mut data, 0x08, b".?AVOne@@\0");
    put(&mut data, 0x20, &1u32.to_le_bytes());
    put(&mut data, 0x24, &0x402028u32.to_le_bytes());
    put(&mut data, 0x28, &0x402030u32.to_le_bytes());
    put(&mut data, 0x30, &0x402000u32.to_le_bytes());
    put(&mut data, 0x3c, &u32::MAX.to_le_bytes());
    put(&mut data, 0x4c, &0x402000u32.to_le_bytes());
    put(&mut data, 0x50, &0x402018u32.to_le_bytes());
    put(&mut data, 0x54, &0x402040u32.to_le_bytes());
    put(&mut data, 0x58, &0x401008u32.to_le_bytes());
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes.vtables.get(&0x402058).map(String::as_str),
        Some("One")
    );
    assert_eq!(name_of(&a, &o, 0x401008), "One::vfunc_0");
    assert_eq!(name_of(&a, &o, 0x401000), "One::ctor_or_dtor");
}
