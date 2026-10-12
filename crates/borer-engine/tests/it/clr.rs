//! .NET metadata triage from a hand-built managed PE.
//!
//! A PE whose CLR runtime header points at ECMA-335 metadata lists its
//! types, its methods with their bodies' addresses, its P/Invokes, the
//! members and assemblies it references and its user strings; the method
//! names become symbols `why` explains, an IL body a data symbol and a
//! native body a function. Metadata that does not hold is refused with
//! its reason, and no byte of it set to anything makes the load panic.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use crate::protection::{IMAGE_BASE, PE_AT, pe, sec};
use borer_engine::analysis::render::{iocs_tsv, why_tsv};
use borer_engine::analysis::{Analysis, Overlay, function_entry};
use borer_engine::clr::{Body, clr_tsv, with_user_strings};
use borer_engine::program::{Program, SymbolKind};
use borer_engine::strings::{Encoding, find_wide_strings};

/// Where the CLR header sits.
const COR20_RVA: u32 = 0x1000;
/// `Ns.Program::Main`'s IL body.
const MAIN_RVA: u32 = 0x1050;
/// `Ns.Program::Helper`'s native body: `mov eax, 7; ret`.
const HELPER_RVA: u32 = 0x1060;
/// Where the metadata root sits.
const META_RVA: u32 = 0x1080;
/// The user string carrying an indicator.
const URL: &str = "http://evil.test/payload";
/// A user string with characters the ASCII-only walk splits at.
const WIDE: &str = "h\u{e9}llo w\u{f6}rld, gr\u{fc}\u{df}e";

/// Table numbers the fixture fills.
const MODULE: u32 = 0x00;
/// `TypeRef`.
const TYPE_REF: u32 = 0x01;
/// `TypeDef`.
const TYPE_DEF: u32 = 0x02;
/// `MethodDef`.
const METHOD_DEF: u32 = 0x06;
/// `MemberRef`.
const MEMBER_REF: u32 = 0x0a;
/// `ModuleRef`.
const MODULE_REF: u32 = 0x1a;
/// `ImplMap`.
const IMPL_MAP: u32 = 0x1c;
/// `Assembly`.
const ASSEMBLY: u32 = 0x20;
/// `AssemblyRef`.
const ASSEMBLY_REF: u32 = 0x23;

/// A `#Strings` heap under construction: each name's index by name.
#[derive(Default)]
struct Strings {
    /// The heap's bytes, the empty string first.
    bytes: Vec<u8>,
}

impl Strings {
    /// Adds a name and returns its index as a two-byte cell.
    fn add(&mut self, name: &str) -> [u8; 2] {
        if self.bytes.is_empty() {
            self.bytes.push(0);
        }
        let at = u16::try_from(self.bytes.len()).expect("a small heap");
        self.bytes.extend_from_slice(name.as_bytes());
        self.bytes.push(0);
        at.to_le_bytes()
    }
}

/// A two-byte cell.
fn c2(v: u16) -> [u8; 2] {
    v.to_le_bytes()
}

/// A `#US` heap holding `texts`, each its compressed length, its UTF-16LE
/// characters and the trailing flag byte.
fn user_heap(texts: &[&str]) -> Vec<u8> {
    let mut heap = vec![0u8];
    for text in texts {
        let units: Vec<u16> = text.encode_utf16().collect();
        let len = units.len() * 2 + 1;
        assert!(len < 0x80, "one-byte lengths in the fixture");
        heap.push(u8::try_from(len).expect("fits"));
        for u in units {
            heap.extend_from_slice(&u.to_le_bytes());
        }
        heap.push(0);
    }
    while heap.len() % 4 != 0 {
        heap.push(0);
    }
    heap
}

/// The metadata's parts, which a test may change before they are joined.
struct Meta {
    /// Rows per table, by table number.
    rows: Vec<(u32, u32)>,
    /// Each table's rows, in table order, as the table stream holds them.
    tables: Vec<u8>,
    /// `#Strings`.
    strings: Vec<u8>,
    /// `#US`.
    us: Vec<u8>,
    /// Offset of the `MemberRef` row's parent cell in [`Meta::tables`].
    member_parent: usize,
    /// Offset of the `TypeDef` row 2 name cell in [`Meta::tables`].
    program_name: usize,
}

/// The fixture's metadata parts, an assembly `Hello`.
///
/// It has a `<Module>` type and `Ns.Program`, whose methods are `Main`
/// (IL), `Helper` (native) and `MessageBox` (a P/Invoke of
/// `user32.dll!MessageBoxW`); one reference to `System.Object::.ctor` in
/// `mscorlib` 4.0.0.0; two user strings.
fn meta() -> Meta {
    let mut s = Strings::default();
    let mut t: Vec<u8> = Vec::new();
    let mut rows = Vec::new();
    let push = |t: &mut Vec<u8>, cells: &[&[u8]]| {
        for c in cells {
            t.extend_from_slice(c);
        }
    };
    rows.push((MODULE, 1));
    let module = s.add("Hello.exe");
    push(&mut t, &[&c2(0), &module, &c2(1), &c2(0), &c2(0)]);
    rows.push((TYPE_REF, 1));
    let (object, system) = (s.add("Object"), s.add("System"));
    push(&mut t, &[&c2((1 << 2) | 2), &object, &system]);
    rows.push((TYPE_DEF, 2));
    let lone = s.add("<Module>");
    push(
        &mut t,
        &[&0u32.to_le_bytes(), &lone, &c2(0), &c2(0), &c2(1), &c2(1)],
    );
    let program_name = t.len() + 4;
    let (program, ns) = (s.add("Program"), s.add("Ns"));
    push(
        &mut t,
        &[
            &0x0010_0001u32.to_le_bytes(),
            &program,
            &ns,
            &c2((1 << 2) | 1),
            &c2(1),
            &c2(1),
        ],
    );
    rows.push((METHOD_DEF, 3));
    for (rva, impl_flags, flags, name) in [
        (MAIN_RVA, 0u16, 0x0096u16, "Main"),
        (HELPER_RVA, 1, 0x0096, "Helper"),
        (0, 0x0080, 0x2096, "MessageBox"),
    ] {
        let name = s.add(name);
        push(
            &mut t,
            &[
                &rva.to_le_bytes(),
                &c2(impl_flags),
                &c2(flags),
                &name,
                &c2(1),
                &c2(1),
            ],
        );
    }
    rows.push((MEMBER_REF, 1));
    let member_parent = t.len();
    let ctor = s.add(".ctor");
    push(&mut t, &[&c2((1 << 3) | 1), &ctor, &c2(1)]);
    rows.push((MODULE_REF, 1));
    let user32 = s.add("user32.dll");
    push(&mut t, &[&user32]);
    rows.push((IMPL_MAP, 1));
    let entry = s.add("MessageBoxW");
    push(&mut t, &[&c2(0x0104), &c2((3 << 1) | 1), &entry, &c2(1)]);
    rows.push((ASSEMBLY, 1));
    let hello = s.add("Hello");
    push(
        &mut t,
        &[
            &0x8004u32.to_le_bytes(),
            &c2(1),
            &c2(0),
            &c2(0),
            &c2(0),
            &0u32.to_le_bytes(),
            &c2(0),
            &hello,
            &c2(0),
        ],
    );
    rows.push((ASSEMBLY_REF, 1));
    let mscorlib = s.add("mscorlib");
    push(
        &mut t,
        &[
            &c2(4),
            &c2(0),
            &c2(0),
            &c2(0),
            &0u32.to_le_bytes(),
            &c2(0),
            &mscorlib,
            &c2(0),
            &c2(0),
        ],
    );
    while s.bytes.len() % 4 != 0 {
        s.bytes.push(0);
    }
    Meta {
        rows,
        tables: t,
        strings: s.bytes,
        us: user_heap(&[URL, WIDE]),
        member_parent,
        program_name,
    }
}

/// Joins the parts into a metadata root with its five streams.
fn root(m: &Meta) -> Vec<u8> {
    let mut stream = vec![0, 0, 0, 0, 2, 0, 0, 1];
    let valid = m.rows.iter().fold(0u64, |v, (t, _)| v | (1 << t));
    stream.extend_from_slice(&valid.to_le_bytes());
    stream.extend_from_slice(&0u64.to_le_bytes());
    for (_, n) in &m.rows {
        stream.extend_from_slice(&n.to_le_bytes());
    }
    stream.extend_from_slice(&m.tables);
    while stream.len() % 4 != 0 {
        stream.push(0);
    }
    let guid = vec![0x11u8; 16];
    let blob = vec![0u8, 3, 0x20, 0, 1, 0, 0, 0];
    let streams: [(&str, &[u8]); 5] = [
        ("#~", &stream),
        ("#Strings", &m.strings),
        ("#US", &m.us),
        ("#GUID", &guid),
        ("#Blob", &blob),
    ];
    let version = b"v4.0.30319\0\0";
    let mut head = Vec::new();
    head.extend_from_slice(b"BSJB");
    head.extend_from_slice(&c2(1));
    head.extend_from_slice(&c2(1));
    head.extend_from_slice(&0u32.to_le_bytes());
    head.extend_from_slice(&u32::try_from(version.len()).expect("fits").to_le_bytes());
    head.extend_from_slice(version);
    head.extend_from_slice(&c2(0));
    head.extend_from_slice(&c2(5));
    let names_len: usize = streams.iter().map(|(n, _)| (n.len() + 4) / 4 * 4 + 8).sum();
    let mut off = head.len() + names_len;
    let mut body = Vec::new();
    for (name, bytes) in streams {
        head.extend_from_slice(&u32::try_from(off).expect("fits").to_le_bytes());
        head.extend_from_slice(&u32::try_from(bytes.len()).expect("fits").to_le_bytes());
        let mut padded = name.as_bytes().to_vec();
        padded.push(0);
        while padded.len() % 4 != 0 {
            padded.push(0);
        }
        head.extend_from_slice(&padded);
        body.extend_from_slice(bytes);
        off += bytes.len();
    }
    head.extend_from_slice(&body);
    head
}

/// A PE32+ image whose `.text` holds the CLR header, `Main`'s IL body,
/// `Helper`'s native body and the metadata, with data directory 14 naming
/// the header.
///
/// # Arguments
///
/// * `metadata` - The metadata root and its streams.
fn image(metadata: &[u8]) -> Vec<u8> {
    let mut text = vec![0u8; usize::try_from(META_RVA - COR20_RVA).expect("fits")];
    text.extend_from_slice(metadata);
    let mut cor20 = Vec::new();
    cor20.extend_from_slice(&72u32.to_le_bytes());
    cor20.extend_from_slice(&c2(2));
    cor20.extend_from_slice(&c2(5));
    cor20.extend_from_slice(&META_RVA.to_le_bytes());
    cor20.extend_from_slice(&u32::try_from(metadata.len()).expect("fits").to_le_bytes());
    cor20.extend_from_slice(&0x0002_0003u32.to_le_bytes());
    cor20.extend_from_slice(&0x0600_0001u32.to_le_bytes());
    cor20.resize(72, 0);
    text[..72].copy_from_slice(&cor20);
    let main = usize::try_from(MAIN_RVA - COR20_RVA).expect("fits");
    // ASM: tiny IL header (2 bytes of code), nop, ret.
    text[main..main + 3].copy_from_slice(&[0x0a, 0x00, 0x2a]);
    let helper = usize::try_from(HELPER_RVA - COR20_RVA).expect("fits");
    // ASM: mov eax, 7; ret
    text[helper..helper + 6].copy_from_slice(&[0xb8, 7, 0, 0, 0, 0xc3]);
    let mut b = pe(&[sec(".text", COR20_RVA, text)], 0);
    let dir = PE_AT + 24 + 112 + 14 * 8;
    b[dir..dir + 4].copy_from_slice(&COR20_RVA.to_le_bytes());
    b[dir + 4..dir + 8].copy_from_slice(&72u32.to_le_bytes());
    b
}

/// Loads an image built from the metadata.
fn load(metadata: &[u8]) -> Program {
    Program::from_bytes(PathBuf::from("hello.exe"), image(metadata)).expect("the PE loads")
}

/// The VA of an RVA in the fixture.
fn va(rva: u32) -> u64 {
    IMAGE_BASE + u64::from(rva)
}

/// The metadata lists the types, methods, P/Invoke, references and strings.
///
/// The three methods come with their bodies' addresses (IL, native,
/// none), the P/Invoke as `dll!export`, the referenced member and
/// assembly, and both user strings whole; the summary's `.net:` line names
/// the assembly, the flags and the entry.
#[test]
fn a_managed_pe_lists_its_types_methods_pinvoke_and_strings() {
    let p = load(&root(&meta()));
    let clr = p.clr().expect("the metadata reads");
    assert_eq!(clr.runtime, (2, 5));
    assert_eq!(clr.version, "v4.0.30319");
    assert_eq!(
        clr.assembly,
        Some(("Hello".to_owned(), "1.0.0.0".to_owned()))
    );
    let types: Vec<&str> = clr.types.iter().map(|t| t.name.as_str()).collect();
    assert_eq!(types, ["<Module>", "Ns.Program"]);
    let methods: Vec<(&str, u32, Body)> = clr
        .methods
        .iter()
        .map(|m| (m.name.as_str(), m.rva, m.body))
        .collect();
    assert_eq!(
        methods,
        [
            ("Ns.Program::Main", MAIN_RVA, Body::Il),
            ("Ns.Program::Helper", HELPER_RVA, Body::Native),
            ("Ns.Program::MessageBox", 0, Body::None),
        ]
    );
    let texts: Vec<&str> = clr.user_strings.iter().map(|s| s.text.as_str()).collect();
    assert_eq!(texts, [URL, WIDE]);

    let listing = clr_tsv(&p, "").expect("it lists");
    for row in [
        format!(
            "method\t0x06000001\t{:#x}\tNs.Program::Main\til",
            va(MAIN_RVA)
        ),
        format!(
            "method\t0x06000002\t{:#x}\tNs.Program::Helper\tnative",
            va(HELPER_RVA)
        ),
        "pinvoke\t0x06000003\t-\tNs.Program::MessageBox\tuser32.dll!MessageBoxW".to_owned(),
        "type\t0x02000002\t-\tNs.Program\t3 methods".to_owned(),
        "memberref\t0x0a000001\t-\tSystem.Object::.ctor\tmscorlib".to_owned(),
        "asmref\t0x23000001\t-\tmscorlib\t4.0.0.0".to_owned(),
        "string\t0x70000001\t".to_owned(),
    ] {
        assert!(listing.contains(&row), "{row}\n{listing}");
    }
    assert!(
        listing.contains(&format!("\"{URL}\"\t24 chars")),
        "{listing}"
    );
    assert!(listing.contains("IL is not decompiled"), "{listing}");
    assert!(
        listing.contains("entry 0x06000001 Ns.Program::Main"),
        "{listing}"
    );
    let pinvokes = clr_tsv(&p, "pinvoke").expect("it narrows");
    assert!(pinvokes.contains("# showing 1 of 1 from 0"), "{pinvokes}");

    let info = p.summary();
    assert!(
        info.contains(".net:    assembly Hello 1.0.0.0, runtime 2.5, metadata v4.0.30319, ilonly 32bitreq 32bitpref; entry 0x06000001 Ns.Program::Main; types 2, methods 3 (native 1), pinvokes 1, assembly refs 1, user strings 2"),
        "{info}"
    );
}

/// Method names are symbols, and `why` says the .NET metadata named them.
///
/// An IL body is named by a data symbol and a native body by a function
/// the analysis discovers; `why` says which one borer does not decompile,
/// and a tool asking for the function at an IL body is refused.
#[test]
fn method_names_are_symbols_why_explains() {
    let p = load(&root(&meta()));
    let named = |addr: u64| {
        p.symbols
            .iter()
            .find(|s| s.addr == addr)
            .map(|s| (s.name.as_str(), s.kind))
    };
    assert_eq!(
        named(va(MAIN_RVA)),
        Some(("Ns.Program::Main", SymbolKind::Data))
    );
    assert_eq!(
        named(va(HELPER_RVA)),
        Some(("Ns.Program::Helper", SymbolKind::Local))
    );
    let a = Analysis::compute(&p);
    assert!(
        a.function(va(HELPER_RVA)).is_some(),
        "the native method is analyzed as code"
    );
    let o = Overlay::default();
    let il = why_tsv(&p, &a, &o, &format!("{:#x}", va(MAIN_RVA))).expect("why answers");
    assert!(
        il.contains("# name: the .NET metadata records it as method 0x06000001 Ns.Program::Main, an IL body, which borer does not decompile"),
        "{il}"
    );
    let refused = function_entry(&p, &a, va(MAIN_RVA)).expect_err("an IL body is no function");
    assert!(
        refused.contains(
            "is the IL body of .NET method 0x06000001 Ns.Program::Main: borer does not decompile"
        ),
        "{refused}"
    );
    assert_eq!(function_entry(&p, &a, va(HELPER_RVA)), Ok(va(HELPER_RVA)));
    let native = why_tsv(&p, &a, &o, "Ns.Program::Helper").expect("why answers");
    assert!(
        native.contains("method 0x06000002 Ns.Program::Helper, a native method"),
        "{native}"
    );
    assert!(native.contains("the .NET metadata"), "{native}");
}

/// The user strings join the strings listing whole and tagged, in place of
/// the ASCII-only runs the walk found in `#US`, and feed the indicators.
#[test]
fn user_strings_feed_strings_and_indicators() {
    let p = load(&root(&meta()));
    let walked = find_wide_strings(&p.bytes, 5);
    let merged = with_user_strings(&p, walked, 5);
    let ours: Vec<(&str, Encoding)> = merged
        .iter()
        .filter(|h| h.encoding == Encoding::DotnetUs)
        .map(|h| (h.text.as_str(), h.encoding))
        .collect();
    assert_eq!(
        ours,
        [(URL, Encoding::DotnetUs), (WIDE, Encoding::DotnetUs)]
    );
    assert!(
        merged
            .iter()
            .all(|h| h.encoding == Encoding::DotnetUs || !h.text.contains("llo w")),
        "the walk's split pieces of the wide string are gone"
    );
    let a = Analysis::compute(&p);
    let iocs = iocs_tsv(&p, &a, &Overlay::default(), "url").expect("iocs answer");
    assert!(
        iocs.lines()
            .any(|l| l.contains(URL) && l.contains("dotnet-us")),
        "the URL is an indicator from a user string: {iocs}"
    );
}

/// Two loads of the same bytes list the same metadata and summary, byte
/// for byte.
#[test]
fn the_listing_is_deterministic() {
    let bytes = root(&meta());
    let (one, two) = (load(&bytes), load(&bytes));
    assert_eq!(clr_tsv(&one, ""), clr_tsv(&two, ""));
    assert_eq!(one.summary(), two.summary());
}

/// Metadata that does not hold is refused with the reason, and loads.
///
/// A table stream whose row counts run past it, a name past `#Strings`, a
/// coded index naming no table, and a stream past the metadata are each
/// refused, in the listing and the summary; the program still loads.
#[test]
fn corrupt_metadata_is_refused_cleanly() {
    let mut absurd = meta();
    for (t, n) in &mut absurd.rows {
        if *t == METHOD_DEF {
            *n = 0x00ff_ffff;
        }
    }
    let mut far_name = meta();
    let at = far_name.program_name;
    far_name.tables[at..at + 2].copy_from_slice(&c2(0x7fff));
    let mut no_table = meta();
    let at = no_table.member_parent;
    no_table.tables[at..at + 2].copy_from_slice(&c2((1 << 3) | 7));
    let mut past = root(&meta());
    let first_offset = 20 + 12;
    past[first_offset..first_offset + 4].copy_from_slice(&0x00ff_0000u32.to_le_bytes());
    for (bytes, why) in [
        (
            root(&absurd),
            "the MethodDef table's 16777215 rows of 14 bytes run past the table stream's",
        ),
        (
            root(&far_name),
            "TypeDef row 2's name is at #Strings offset 0x7fff, past the heap's",
        ),
        (
            root(&no_table),
            "MemberRef row 1's parent 0xf names no table",
        ),
        (past, "stream #~ at metadata offset 0xff0000"),
    ] {
        let p = load(&bytes);
        let refused = clr_tsv(&p, "").expect_err("the metadata is refused");
        assert!(refused.contains(why), "{why}\n{refused}");
        assert!(
            p.summary()
                .contains(".net:    a CLR runtime header, its metadata refused: "),
            "{}",
            p.summary()
        );
        assert!(p.clr().is_none());
    }
}

/// No byte of the metadata, set to `0xff` or `0x00`, makes the load or
/// the listing panic.
#[test]
fn no_byte_of_the_metadata_makes_the_load_panic() {
    let good = root(&meta());
    for at in 0..good.len() {
        for v in [0x00, 0xff] {
            let mut bad = good.clone();
            bad[at] = v;
            let p = load(&bad);
            let _ = clr_tsv(&p, "string,offset=1");
            let _ = p.summary();
        }
    }
}

/// A program with no CLR header says so in one line.
#[test]
fn a_native_pe_is_not_a_net_assembly() {
    let p = Program::from_bytes(
        PathBuf::from("native.exe"),
        pe(&[sec(".text", 0x1000, vec![0xc3; 16])], 0x1000),
    )
    .expect("the PE loads");
    assert!(p.clr.is_none());
    assert_eq!(
        clr_tsv(&p, "").expect("it answers"),
        "# not a .NET assembly: the image has no CLR runtime header (data directory 14)\n"
    );
    assert!(!p.summary().contains(".net:"));
}
