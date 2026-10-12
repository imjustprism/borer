//! Objective-C metadata on hand-built Mach-O images.
//!
//! One class `Foo : NSObject` with an instance method in a relative
//! method list and a class method in a list of pointers, a category
//! `NSString(Shout)`, selector and class references and the chained
//! fixups that make them pointers. The methods take their runtime names,
//! the sends to `objc_msgSend` (through its stub, its slot or an
//! `__objc_stubs` entry) read as `[recv sel]`, and corrupt metadata is
//! refused without a panic.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use crate::machogen::{self, ARM64, CODE, Fix, PIE, R, RW, RX, Sect, Seg, Starts, X86_64};
use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::objc::objc_tsv;
use borer_engine::analysis::render::{disasm_function, function_summary};
use borer_engine::analysis::{Analysis, NameSource, Overlay, name_of};
use borer_engine::program::Program;
use borer_engine::table::Window;

/// Where `__TEXT` is mapped: the image base.
const TEXT: u64 = 0x1_0000_0000;
/// The `__DATA_CONST` segment: the slots, the lists and the read-only
/// class data.
const CONST: u64 = TEXT + 0x1000;
/// The `__DATA` segment: the class and its metaclass.
const DATA: u64 = TEXT + 0x2000;
/// The entry, which sends the messages, past the load commands.
const MAIN: u64 = TEXT + 0x800;
/// The arm64 stub after `objc_msgSend`'s slot.
const STUB: u64 = TEXT + 0x880;
/// `-[Foo bar]`.
const BAR: u64 = TEXT + 0x900;
/// `+[Foo shared]`.
const SHARED: u64 = TEXT + 0x910;
/// `-[NSString(Shout) shout]`, which sends `bar` to `self`.
const SHOUT: u64 = TEXT + 0x920;
/// The arm64 `__objc_stubs` entry sending `shout`.
const OBJC_STUB: u64 = TEXT + 0x940;
/// The selector names: `bar`, `shared` at `+4`, `shout` at `+0xb`.
const METHNAME: u64 = TEXT + 0xc00;
/// The methods' type string.
const TYPES: u64 = TEXT + 0xc20;
/// The class and category names: `Foo`, `Shout` at `+4`.
const CLASSNAME: u64 = TEXT + 0xc40;
/// `objc_msgSend`'s slot.
const GOT: u64 = CONST;
/// The selector references: `bar`, `shared`, `shout`.
const SELREF_BAR: u64 = CONST + 0x20;
/// The selector reference to `shared`.
const SELREF_SHARED: u64 = CONST + 0x28;
/// The selector reference to `shout`.
const SELREF_SHOUT: u64 = CONST + 0x30;
/// The class reference to `Foo`.
const CLASSREF: u64 = CONST + 0x38;
/// `LC_DYLD_CHAINED_FIXUPS`.
const LC_DYLD_CHAINED_FIXUPS: u32 = 0x8000_0034;
/// `LC_FUNCTION_STARTS`.
const LC_FUNCTION_STARTS: u32 = 0x26;
/// `DYLD_CHAINED_PTR_64_OFFSET`.
const PTR_64_OFFSET: u16 = 6;

/// Little-endian bytes of arm64 instruction words.
///
/// # Arguments
///
/// * `words` - The words.
fn words(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// The arm64 code, `(address, bytes)`.
///
/// `main` sends `shared` to `Foo` through the stub, `bar` to the result,
/// and `shout` to that result through the `__objc_stubs` entry; then come
/// the stub, the three methods and the `__objc_stubs` entry.
fn arm64_code() -> Vec<(u64, Vec<u8>)> {
    vec![
        (
            MAIN,
            words(&[
                0xb000_0000, // ASM: adrp x0, CONST
                0xf940_1c00, // ASM: ldr x0, [x0, #0x38]
                0xb000_0001, // ASM: adrp x1, CONST
                0xf940_1421, // ASM: ldr x1, [x1, #0x28]
                0x9400_001c, // ASM: bl STUB
                0xb000_0001, // ASM: adrp x1, CONST
                0xf940_1021, // ASM: ldr x1, [x1, #0x20]
                0x9400_0019, // ASM: bl STUB
                0x9400_0048, // ASM: bl OBJC_STUB
                0xd65f_03c0, // ASM: ret
            ]),
        ),
        (
            STUB,
            words(&[
                0xb000_0010, // ASM: adrp x16, CONST
                0xf940_0210, // ASM: ldr x16, [x16]
                0xd61f_0200, // ASM: br x16
            ]),
        ),
        (BAR, words(&[0xd65f_03c0])),    // ASM: ret
        (SHARED, words(&[0xd65f_03c0])), // ASM: ret
        (
            SHOUT,
            words(&[
                0xb000_0001, // ASM: adrp x1, CONST
                0xf940_1021, // ASM: ldr x1, [x1, #0x20]
                0x97ff_ffd6, // ASM: bl STUB
                0xd65f_03c0, // ASM: ret
            ]),
        ),
        (
            OBJC_STUB,
            words(&[
                0xb000_0001, // ASM: adrp x1, CONST
                0xf940_1821, // ASM: ldr x1, [x1, #0x30]
                0xb000_0010, // ASM: adrp x16, CONST
                0xf940_0210, // ASM: ldr x16, [x16]
                0xd61f_0200, // ASM: br x16
                0xd420_0020, // ASM: brk #1
                0xd420_0020, // ASM: brk #1
                0xd420_0020, // ASM: brk #1
            ]),
        ),
    ]
}

/// A RIP-relative operand's displacement.
///
/// # Arguments
///
/// * `next` - The address of the instruction after the operand's.
/// * `target` - The address it names.
fn rip(next: u64, target: u64) -> [u8; 4] {
    i32::try_from(i64::try_from(target).expect("fits") - i64::try_from(next).expect("fits"))
        .expect("near")
        .to_le_bytes()
}

/// The x86-64 code: `main` sends `shared` to `Foo` and `bar` to the
/// result through `objc_msgSend`'s slot; the methods.
fn x86_code() -> Vec<(u64, Vec<u8>)> {
    let mut main = vec![0x48, 0x8b, 0x3d]; // ASM: mov rdi, [rip+CLASSREF]
    main.extend(rip(MAIN + 7, CLASSREF));
    main.extend([0x48, 0x8b, 0x35]); // ASM: mov rsi, [rip+SELREF_SHARED]
    main.extend(rip(MAIN + 14, SELREF_SHARED));
    main.extend([0xff, 0x15]); // ASM: call [rip+GOT]
    main.extend(rip(MAIN + 20, GOT));
    main.extend([0x48, 0x89, 0xc7]); // ASM: mov rdi, rax
    main.extend([0x48, 0x8b, 0x35]); // ASM: mov rsi, [rip+SELREF_BAR]
    main.extend(rip(MAIN + 30, SELREF_BAR));
    main.extend([0xff, 0x15]); // ASM: call [rip+GOT]
    main.extend(rip(MAIN + 36, GOT));
    main.push(0xc3); // ASM: ret
    let mut shout = vec![0x48, 0x8b, 0x35]; // ASM: mov rsi, [rip+SELREF_BAR]
    shout.extend(rip(SHOUT + 7, SELREF_BAR));
    shout.extend([0xff, 0x15]); // ASM: call [rip+GOT]
    shout.extend(rip(SHOUT + 13, GOT));
    shout.push(0xc3); // ASM: ret
    vec![
        (MAIN, main),
        (BAR, vec![0xc3]),    // ASM: ret
        (SHARED, vec![0xc3]), // ASM: ret
        (SHOUT, shout),
    ]
}

/// Writes `value` as a little-endian `u32` at `at`.
///
/// # Arguments
///
/// * `b` - The bytes.
/// * `at` - The offset.
/// * `value` - The value.
fn put32(b: &mut [u8], at: usize, value: u32) {
    b[at..at + 4].copy_from_slice(&value.to_le_bytes());
}

/// Writes a relative method list of one method at `at` in `b`, which is
/// mapped at `base`.
///
/// # Arguments
///
/// * `b` - The segment's bytes.
/// * `base` - The segment's address.
/// * `at` - The list's offset in the segment.
/// * `selref` - The method's selector reference.
/// * `imp` - Its implementation.
fn small_list(b: &mut [u8], base: u64, at: usize, selref: u64, imp: u64) {
    put32(b, at, 0x8000_000c);
    put32(b, at + 4, 1);
    for (k, target) in [selref, TYPES, imp].into_iter().enumerate() {
        let field = base + u64::try_from(at + 8 + 4 * k).expect("fits");
        let off = i64::try_from(target).expect("fits") - i64::try_from(field).expect("fits");
        b[at + 8 + 4 * k..at + 12 + 4 * k]
            .copy_from_slice(&i32::try_from(off).expect("near").to_le_bytes());
    }
}

/// Builds the image for one CPU.
///
/// # Arguments
///
/// * `cpu` - The CPU type.
/// * `code` - The code, `(address, bytes)` in `__TEXT`.
/// * `starts` - The functions' offsets from [`TEXT`], ascending.
/// * `corrupt` - Plants corrupt metadata beside the sound, in sections of
///   the same names past it: a class list entry pointing nowhere, a
///   category whose name points nowhere, and one whose method list counts
///   four billion methods.
fn image(cpu: u32, code: &[(u64, Vec<u8>)], starts: &[u64], corrupt: bool) -> Program {
    let mut text = vec![0u8; 0x1000];
    for (va, bytes) in code {
        let at = usize::try_from(va - TEXT).expect("fits");
        text[at..at + bytes.len()].copy_from_slice(bytes);
    }
    let off = |va: u64| usize::try_from(va - TEXT).expect("fits");
    let rebase = |va: u64| Fix::Rebase(va - TEXT);
    text[off(METHNAME)..off(METHNAME) + 17].copy_from_slice(b"bar\0shared\0shout\0");
    text[off(TYPES)..off(TYPES) + 8].copy_from_slice(b"v16@0:8\0");
    text[off(CLASSNAME)..off(CLASSNAME) + 10].copy_from_slice(b"Foo\0Shout\0");
    let mut konst = vec![0u8; 0x200];
    let mut fixups = vec![
        (0x00, Fix::Bind(0)),
        (0x10, rebase(DATA)),
        (0x18, rebase(CONST + 0x108)),
        (0x20, rebase(METHNAME)),
        (0x28, rebase(METHNAME + 4)),
        (0x30, rebase(METHNAME + 0xb)),
        (0x38, rebase(DATA)),
        (0x58, rebase(CLASSNAME)),
        (0x60, rebase(CONST + 0xd0)),
        (0xa0, rebase(CLASSNAME)),
        (0xa8, rebase(CONST + 0xe8)),
        (0xf0, rebase(METHNAME + 4)),
        (0xf8, rebase(TYPES)),
        (0x100, rebase(SHARED)),
        (0x108, rebase(CLASSNAME + 4)),
        (0x110, Fix::Bind(1)),
        (0x118, rebase(CONST + 0x138)),
    ];
    if corrupt {
        fixups.extend([
            (0x150, Fix::Rebase(0x9_0000)),
            (0x158, rebase(CONST + 0x170)),
            (0x160, rebase(CONST + 0x190)),
            (0x170, Fix::Rebase(0x9_0000)),
            (0x178, Fix::Bind(1)),
            (0x190, rebase(CLASSNAME + 4)),
            (0x198, Fix::Bind(1)),
            (0x1a0, rebase(CONST + 0x1c0)),
        ]);
    }
    machogen::chain(&mut konst, &fixups);
    put32(&mut konst, 0x44, 8);
    put32(&mut konst, 0x48, 8);
    put32(&mut konst, 0x88, 1);
    put32(&mut konst, 0x8c, 0x28);
    put32(&mut konst, 0x90, 0x28);
    small_list(&mut konst, CONST, 0xd0, SELREF_BAR, BAR);
    put32(&mut konst, 0xe8, 24);
    put32(&mut konst, 0xec, 1);
    small_list(&mut konst, CONST, 0x138, SELREF_SHOUT, SHOUT);
    if corrupt {
        put32(&mut konst, 0x1c0, 0x8000_000c);
        put32(&mut konst, 0x1c4, u32::MAX);
    }
    let mut data = vec![0u8; 0x100];
    machogen::chain(
        &mut data,
        &[
            (0x00, rebase(DATA + 0x28)),
            (0x08, Fix::Bind(2)),
            (0x20, rebase(CONST + 0x40)),
            (0x28, Fix::Bind(3)),
            (0x30, Fix::Bind(3)),
            (0x48, rebase(CONST + 0x88)),
        ],
    );
    let payload = machogen::chained(
        4,
        &[1, 2].map(|segment| Starts {
            segment,
            format: PTR_64_OFFSET,
            offset: if segment == 1 { 0x1000 } else { 0x2000 },
            page_size: 0x1000,
            pages: vec![0],
        }),
        &[
            (1, false, "_objc_msgSend"),
            (1, false, "_OBJC_CLASS_$_NSString"),
            (1, false, "_OBJC_CLASS_$_NSObject"),
            (1, false, "_OBJC_METACLASS_$_NSObject"),
        ],
    );
    let mut function_starts = Vec::new();
    let mut last = 0u64;
    for &s in starts {
        let mut delta = s - last;
        last = s;
        loop {
            let low = u8::try_from(delta & 0x7f).expect("seven bits");
            delta >>= 7;
            function_starts.push(if delta == 0 { low } else { low | 0x80 });
            if delta == 0 {
                break;
            }
        }
    }
    function_starts.push(0);
    let starts_at = 0x3000 + payload.len().next_multiple_of(8);
    let mut linkedit = payload.clone();
    linkedit.resize(starts_at - 0x3000, 0);
    linkedit.extend_from_slice(&function_starts);
    let sect = |name, addr, size, flags| Sect {
        name,
        addr,
        size,
        flags,
    };
    let mut lists = vec![
        sect("__got", GOT, 8, 6),
        sect("__objc_classlist", CONST + 0x10, 8, 0),
        sect("__objc_catlist", CONST + 0x18, 8, 0),
        sect("__objc_selrefs", SELREF_BAR, 0x18, 5),
        sect("__objc_classrefs", CLASSREF, 8, 0),
        sect("__objc_const", CONST + 0x40, 0x110, 0),
    ];
    if corrupt {
        lists.extend([
            sect("__objc_classlist", CONST + 0x150, 8, 0),
            sect("__objc_catlist", CONST + 0x158, 0x10, 0),
            sect("__objc_const", CONST + 0x168, 0x98, 0),
        ]);
    }
    let segs = [
        Seg {
            name: "__TEXT",
            vmaddr: TEXT,
            fileoff: 0,
            bytes: text,
            prot: RX,
            sections: vec![
                sect("__text", MAIN, OBJC_STUB - MAIN, CODE),
                sect("__objc_stubs", OBJC_STUB, 0x20, CODE),
                sect("__objc_methname", METHNAME, 0x20, 2),
                sect("__objc_methtype", TYPES, 0x10, 2),
                sect("__objc_classname", CLASSNAME, 0x10, 2),
            ],
        },
        Seg {
            name: "__DATA_CONST",
            vmaddr: CONST,
            fileoff: 0x1000,
            bytes: konst,
            prot: RW,
            sections: lists,
        },
        Seg {
            name: "__DATA",
            vmaddr: DATA,
            fileoff: 0x2000,
            bytes: data,
            prot: RW,
            sections: vec![sect("__objc_data", DATA, 0x50, 0)],
        },
        Seg {
            name: "__LINKEDIT",
            vmaddr: TEXT + 0x10_0000,
            fileoff: 0x3000,
            bytes: linkedit,
            prot: R,
            sections: Vec::new(),
        },
    ];
    let bytes = machogen::build(
        cpu,
        PIE,
        &segs,
        &[
            machogen::main(MAIN - TEXT),
            machogen::dylib("/usr/lib/libobjc.A.dylib"),
            machogen::linkedit(LC_DYLD_CHAINED_FIXUPS, 0x3000, payload.len()),
            machogen::linkedit(
                LC_FUNCTION_STARTS,
                u64::try_from(starts_at).expect("fits"),
                function_starts.len(),
            ),
        ],
    );
    Program::from_bytes(PathBuf::from("objc.macho"), bytes).expect("the image loads")
}

/// The name a function goes by, and where it came from.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `entry` - The function's entry.
fn named(a: &Analysis, entry: u64) -> (String, NameSource) {
    let f = a.function(entry).expect("a function starts there");
    (name_of(a, &Overlay::default(), entry), f.name_source)
}

/// The arm64 functions' offsets from [`TEXT`], for `LC_FUNCTION_STARTS`.
const A64_STARTS: [u64; 6] = [
    MAIN - TEXT,
    STUB - TEXT,
    BAR - TEXT,
    SHARED - TEXT,
    SHOUT - TEXT,
    OBJC_STUB - TEXT,
];

/// The arm64 image names every method from the runtime metadata, and
/// every send reads as `[recv sel]`.
///
/// An instance method from a relative list, a class method from a list of
/// pointers, a category's method and the `__objc_stubs` entry after its
/// selector are named; stripped, the methods were `sub_` functions and
/// every call read as `objc_msgSend`.
#[test]
fn arm64_methods_are_named_and_sends_read_as_messages() {
    let p = image(ARM64, &arm64_code(), &A64_STARTS, false);
    let a = Analysis::compute(&p);
    assert_eq!(named(&a, BAR), ("-[Foo bar]".to_owned(), NameSource::ObjC));
    assert_eq!(
        named(&a, SHARED),
        ("+[Foo shared]".to_owned(), NameSource::ObjC)
    );
    assert_eq!(
        named(&a, SHOUT),
        ("-[NSString(Shout) shout]".to_owned(), NameSource::ObjC)
    );
    assert_eq!(
        named(&a, OBJC_STUB),
        ("objc_msgSend$shout".to_owned(), NameSource::ObjC)
    );
    assert_eq!(named(&a, STUB).0, "objc_msgSend");
    let sent: Vec<(u64, String)> = a
        .objc
        .messages
        .iter()
        .map(|(site, m)| (*site, m.text()))
        .collect();
    assert_eq!(
        sent,
        [
            (MAIN + 0x10, "[Foo shared]".to_owned()),
            (MAIN + 0x1c, "[[Foo shared] bar]".to_owned()),
            (MAIN + 0x20, "[[[Foo shared] bar] shout]".to_owned()),
            (SHOUT + 8, "[self bar]".to_owned()),
        ]
    );
    let o = Overlay::default();
    let summary = function_summary(&p, &a, &o, MAIN).expect("main summarizes");
    assert!(
        summary.contains(
            "messages: 3 [[Foo shared], [[Foo shared] bar], [[[Foo shared] bar] shout]]\n"
        ),
        "{summary}"
    );
    let listing = disasm_function(&p, &a, &o, SHOUT, 50, false).expect("shout lists");
    assert!(listing.contains("  ; [self bar]\n"), "{listing}");
    let text = decompile(&p, &a, &o, MAIN).expect("main decompiles");
    assert!(
        text.contains(
            "\n// messages: [Foo shared], [[Foo shared] bar], [[[Foo shared] bar] shout]\n"
        ),
        "{text}"
    );
    assert!(
        text.contains("x0 = objc_msgSend(Foo, @selector(shared));\n"),
        "the class and selector references read by name: {text}"
    );
    let objc = objc_tsv(&a, "", Window::first(50));
    assert!(
        objc.starts_with(
            "# 3 Objective-C methods in 1 classes and 1 categories, 0 protocols, 3 selector references, 4 messages recovered\n"
        ),
        "{objc}"
    );
    for row in [
        format!("Foo\tNSObject\t-\tbar\t{BAR:#x}\n"),
        format!("Foo\tNSObject\t+\tshared\t{SHARED:#x}\n"),
        format!("NSString(Shout)\t\t-\tshout\t{SHOUT:#x}\n"),
    ] {
        assert!(objc.contains(&row), "{row} in {objc}");
    }
}

/// On x86-64 the selector rides in `rsi`, loaded from its reference, and
/// a receiver moved from `rax` is the message whose result it is.
#[test]
fn x86_64_sends_read_their_selector_from_rsi() {
    let starts = [MAIN - TEXT, BAR - TEXT, SHARED - TEXT, SHOUT - TEXT];
    let p = image(X86_64, &x86_code(), &starts, false);
    let a = Analysis::compute(&p);
    assert_eq!(named(&a, SHARED).0, "+[Foo shared]");
    assert_eq!(named(&a, SHOUT).0, "-[NSString(Shout) shout]");
    let sent: Vec<String> = a.objc.messages.values().map(|m| m.text()).collect();
    assert_eq!(
        sent,
        ["[Foo shared]", "[[Foo shared] bar]", "[self bar]"],
        "{:#x?}",
        a.objc.messages
    );
    let o = Overlay::default();
    let listing = disasm_function(&p, &a, &o, MAIN, 50, false).expect("main lists");
    assert!(listing.contains("  ; [[Foo shared] bar]\n"), "{listing}");
    let text = decompile(&p, &a, &o, MAIN).expect("main decompiles");
    assert!(
        text.contains("\n// messages: [Foo shared], [[Foo shared] bar]\n"),
        "{text}"
    );
    assert!(
        text.contains("rax = objc_msgSend(Foo, @selector(shared));\n"),
        "the class and selector references read by name: {text}"
    );
}

/// Corrupt metadata is refused and counted, and what reads still names
/// its methods.
///
/// A class list entry pointing past every section, a category whose name
/// points nowhere and a method list stating four billion methods each
/// count as refused; the sound class and category still name theirs.
#[test]
fn corrupt_metadata_is_refused_cleanly() {
    let p = image(ARM64, &arm64_code(), &A64_STARTS, true);
    let a = Analysis::compute(&p);
    assert_eq!(named(&a, BAR).0, "-[Foo bar]");
    assert_eq!(named(&a, SHOUT).0, "-[NSString(Shout) shout]");
    assert!(a.objc.refused >= 3, "{:?}", a.objc);
    let objc = objc_tsv(&a, "", Window::first(50));
    assert!(objc.contains(" entries refused ("), "{objc}");
}
