//! What built a file and what wraps it.
//!
//! The compiler and its version, the runtime or installer around the
//! program, and the packer over it, each with the evidence it was read from
//! and how sure that reading is.
//!
//! Structure decides first: the MSVC Rich header, Go's pclntab, the CLR
//! header, a `PyInstaller` cookie, an installer's own table. Marks a
//! runtime leaves in its strings come next, and say less. A file nothing
//! names is said to be unknown.
//!
//! Every mark is stored back to front ([`reversed`]) so borer's own binary,
//! or a tool built with it, does not find every toolchain in its own
//! tables; one pass over at most [`SCAN_MAX`] bytes finds them all.

use crate::bundle::{self, Bundle};
use crate::fileinfo::{forward, reversed};
use crate::program::{BinaryFormat, Program};

/// Bytes of the file the mark scan reads.
pub const SCAN_MAX: usize = 256 << 20;
/// Longest compiler identification text quoted.
const IDENT_MAX: usize = 96;
/// Most places a mark is looked for before it counts as absent, when the
/// first place it occurs is not the shape wanted.
const TRIES_MAX: usize = 16;

/// What a finding says about the file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Role {
    /// The compiler, language or runtime the code was built with.
    Compiler,
    /// An interpreter, bundler or installer the program ships inside.
    Wrapper,
    /// A packer or protector over the image.
    Packer,
}

/// How sure a finding is, most sure first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Confidence {
    /// Read from a structure only that toolchain writes.
    High,
    /// Read from marks the toolchain leaves, which another could copy.
    Medium,
    /// A hint: one weak mark.
    Low,
}

impl Confidence {
    /// The word a line shows.
    #[must_use]
    pub const fn word(self) -> &'static str {
        match self {
            Self::High => "high",
            Self::Medium => "medium",
            Self::Low => "low",
        }
    }
}

/// One toolchain, wrapper or packer found, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Finding {
    /// What it says about the file.
    pub role: Role,
    /// Its name.
    pub name: &'static str,
    /// Its version or flavor, when the evidence states one.
    pub version: Option<String>,
    /// How sure the finding is: the surest of its evidence.
    pub confidence: Confidence,
    /// Where it was read: offsets, sections, imports, resources.
    pub evidence: Vec<String>,
    /// What an analyst does next; empty for nothing to add.
    pub hint: &'static str,
}

/// A toolchain told by marks in its bytes.
struct Marked {
    /// What it says about the file.
    role: Role,
    /// Its name.
    name: &'static str,
    /// Marks, each back to front ([`reversed`]).
    marks: &'static [&'static [u8]],
    /// How many of the marks a file must carry.
    need: usize,
    /// How sure the marks make it.
    confidence: Confidence,
    /// What an analyst does next.
    hint: &'static str,
}

/// The toolchains read by their marks.
const MARKED: [Marked; 12] = [
    Marked {
        role: Role::Wrapper,
        name: "Nuitka",
        marks: &[
            &reversed(b"__nuitka_version__"),
            &reversed(b"nuitka-onefile"),
        ],
        need: 1,
        confidence: Confidence::Medium,
        hint: "Python compiled to C: the module code is native, the constants are in the data",
    },
    Marked {
        role: Role::Wrapper,
        name: "AutoIt",
        marks: &[&reversed(b"AU3!EA06"), &reversed(b">>>AUTOIT SCRIPT<<<")],
        need: 1,
        confidence: Confidence::Medium,
        hint: "the script is an encrypted resource: extract it with an AutoIt decompiler rather than reading the interpreter",
    },
    Marked {
        role: Role::Wrapper,
        name: "Electron",
        marks: &[
            &reversed(b"ELECTRON_RUN_AS_NODE"),
            &reversed(b"electron.asar"),
        ],
        need: 2,
        confidence: Confidence::Medium,
        hint: "the logic is JavaScript in resources/app.asar beside the executable, not in this binary",
    },
    Marked {
        role: Role::Wrapper,
        name: "PyInstaller",
        marks: &[&reversed(b"_MEIPASS"), &reversed(b"pyi-runtime-tmpdir")],
        need: 1,
        confidence: Confidence::Medium,
        hint: "the Python code is in the appended archive: extract it with pyinstxtractor, then decompile the .pyc",
    },
    Marked {
        role: Role::Wrapper,
        name: "NSIS",
        marks: &[
            &reversed(b"Nullsoft.NSIS.exehead"),
            &reversed(b"Nullsoft Install System"),
        ],
        need: 1,
        confidence: Confidence::Medium,
        hint: "the installer script and files are in the appended data: 7-Zip lists and extracts them",
    },
    Marked {
        role: Role::Wrapper,
        name: "Inno Setup",
        marks: &[
            &reversed(b"JR.Inno.Setup"),
            &reversed(b"Inno Setup Setup Data ("),
        ],
        need: 1,
        confidence: Confidence::Medium,
        hint: "the setup script and files are compressed in the setup data: innoextract reads them",
    },
    Marked {
        role: Role::Compiler,
        name: "Nim",
        marks: &[&reversed(b"@NimMain"), &reversed(b"fatal.nim")],
        need: 1,
        confidence: Confidence::Medium,
        hint: "Nim compiles through C: NimMain is the program's real entry",
    },
    Marked {
        role: Role::Compiler,
        name: "C++Builder",
        marks: &[&reversed(b"__CPPdebugHook"), &reversed(b"Borland C++")],
        need: 1,
        confidence: Confidence::Medium,
        hint: "a VCL program: forms are RCDATA resources and the RTTI names the classes",
    },
    Marked {
        role: Role::Compiler,
        name: "Delphi or C++Builder",
        marks: &[
            &reversed(b"Embarcadero"),
            &reversed(b"Borland"),
            &reversed(b"TObject"),
        ],
        need: 2,
        confidence: Confidence::Medium,
        hint: "a VCL program: forms are RCDATA resources and the RTTI names the classes",
    },
    Marked {
        role: Role::Compiler,
        name: "MinGW-w64",
        marks: &[
            &reversed(b"Mingw-w64 runtime failure"),
            &reversed(b"libgcc_s_"),
        ],
        need: 1,
        confidence: Confidence::Medium,
        hint: "GCC-built: the CRT is MinGW's, not MSVC's",
    },
    Marked {
        role: Role::Compiler,
        name: "Zig",
        marks: &[
            &reversed(b"reached unreachable code"),
            &reversed(b"attempt to use null value"),
            &reversed(b"integer cast truncated bits"),
        ],
        need: 2,
        confidence: Confidence::Medium,
        hint: "Zig's safety checks panic with these texts: their callers are the checked operations",
    },
    Marked {
        role: Role::Compiler,
        name: "D",
        marks: &[
            &reversed(b"_Dmain"),
            &reversed(b"core.exception"),
            &reversed(b"object.Throwable"),
        ],
        need: 2,
        confidence: Confidence::Medium,
        hint: "D's runtime starts the program: _Dmain is the user's main",
    },
];

/// Marks read for their text rather than counted: `GCC: (`, `clang version `,
/// rustc's commit path, Go's build information header, VB's header magic.
const GCC: [u8; 6] = reversed(b"GCC: (");
/// The text clang identifies itself with, back to front.
const CLANG: [u8; 14] = reversed(b"clang version ");
/// The path rustc embeds before its commit hash, back to front.
const RUSTC_PATH: [u8; 7] = reversed(b"/rustc/");
/// The Go build information header, back to front.
const GO_BUILDINFO: [u8; 14] = reversed(b"\xff Go buildinf:");

/// Where each needle first occurs in `hay`, in one pass.
///
/// # Arguments
///
/// * `hay` - The bytes searched; only the first [`SCAN_MAX`] are read.
/// * `needles` - The texts looked for, forward.
///
/// # Returns
///
/// One offset per needle, `None` for one absent or empty.
fn first_offsets(hay: &[u8], needles: &[Vec<u8>]) -> Vec<Option<usize>> {
    let hay = hay.get(..hay.len().min(SCAN_MAX)).unwrap_or(hay);
    let mut by_first: Vec<Vec<usize>> = vec![Vec::new(); 256];
    for (i, n) in needles.iter().enumerate() {
        if let Some(slot) = n.first().and_then(|&b| by_first.get_mut(usize::from(b))) {
            slot.push(i);
        }
    }
    let mut found = vec![None; needles.len()];
    let mut left = needles.iter().filter(|n| !n.is_empty()).count();
    for (at, &b) in hay.iter().enumerate() {
        if left == 0 {
            break;
        }
        for &i in by_first.get(usize::from(b)).map_or(&[][..], Vec::as_slice) {
            if found[i].is_none() && hay.get(at..).is_some_and(|h| h.starts_with(&needles[i])) {
                found[i] = Some(at);
                left -= 1;
            }
        }
    }
    found
}

/// The printable text at `at`, up to a NUL or [`IDENT_MAX`] bytes.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `at` - Where the text starts.
fn ident(bytes: &[u8], at: usize) -> String {
    bytes
        .get(at..)
        .unwrap_or_default()
        .iter()
        .take(IDENT_MAX)
        .take_while(|b| b.is_ascii_graphic() || **b == b' ')
        .map(|&b| char::from(b))
        .collect()
}

/// The rustc commit a Rust build's panic paths name, from the first
/// `/rustc/<40 hex digits>/` in the file, starting the search at `from`.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `from` - Where `/rustc/` first occurs.
fn rust_commit(bytes: &[u8], from: usize) -> Option<(usize, String)> {
    let prefix = forward(&RUSTC_PATH);
    let mut at = from;
    for _ in 0..TRIES_MAX {
        let hash = bytes.get(at + prefix.len()..at + prefix.len() + 41)?;
        if hash[..40].iter().all(u8::is_ascii_hexdigit) && hash[40] == b'/' {
            return Some((at, String::from_utf8_lossy(&hash[..12]).into_owned()));
        }
        at += 1 + crate::fileinfo::find(bytes.get(at + 1..)?, &prefix)?;
    }
    None
}

/// The Go release named after the build information header at `at`, `go1.22.3`.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `at` - Where the header starts.
fn go_version(bytes: &[u8], at: usize) -> Option<String> {
    let window = bytes.get(at..bytes.len().min(at + 0x200))?;
    let start = crate::fileinfo::find(window, b"go1.")?;
    let text: String = window
        .get(start..)?
        .iter()
        .take_while(|b| b.is_ascii_alphanumeric() || **b == b'.')
        .map(|&b| char::from(b))
        .collect();
    (text.len() > 4).then_some(text)
}

/// Adds a finding, or merges its evidence into one of the same name.
///
/// # Arguments
///
/// * `out` - The findings so far.
/// * `f` - The finding.
fn add(out: &mut Vec<Finding>, f: Finding) {
    if let Some(old) = out.iter_mut().find(|o| o.name == f.name) {
        old.confidence = old.confidence.min(f.confidence);
        if old.version.is_none() {
            old.version = f.version;
        }
        old.evidence.extend(f.evidence);
        if old.hint.is_empty() {
            old.hint = f.hint;
        }
    } else {
        out.push(f);
    }
}

/// A finding with no version.
///
/// # Arguments
///
/// * `role` - What it says about the file.
/// * `name` - Its name.
/// * `confidence` - How sure it is.
/// * `evidence` - Where it was read.
/// * `hint` - What to do next.
fn plain(
    role: Role,
    name: &'static str,
    confidence: Confidence,
    evidence: String,
    hint: &'static str,
) -> Finding {
    Finding {
        role,
        name,
        version: None,
        confidence,
        evidence: vec![evidence],
        hint,
    }
}

/// The findings the marks and the compiler texts give.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `out` - The findings so far.
fn by_marks(bytes: &[u8], out: &mut Vec<Finding>) {
    let texts: [&[u8]; 4] = [&GCC, &CLANG, &RUSTC_PATH, &GO_BUILDINFO];
    let needles: Vec<Vec<u8>> = MARKED
        .iter()
        .flat_map(|m| m.marks.iter())
        .chain(texts.iter())
        .map(|m| forward(m))
        .collect();
    let found = first_offsets(bytes, &needles);
    let mut at = found.iter().copied();
    for m in &MARKED {
        let hits: Vec<String> = m
            .marks
            .iter()
            .zip(at.by_ref())
            .filter_map(|(mark, off)| {
                off.map(|o| format!("'{}' at {o:#x}", String::from_utf8_lossy(&forward(mark))))
            })
            .collect();
        if hits.len() >= m.need {
            add(
                out,
                Finding {
                    role: m.role,
                    name: m.name,
                    version: None,
                    confidence: m.confidence,
                    evidence: hits,
                    hint: m.hint,
                },
            );
        }
    }
    let [gcc, clang, rustc, go] = [at.next(), at.next(), at.next(), at.next()].map(Option::flatten);
    if let Some(o) = gcc {
        let text = ident(bytes, o);
        add(
            out,
            Finding {
                role: Role::Compiler,
                name: "GCC",
                version: text.strip_prefix("GCC: ").map(str::to_owned),
                confidence: Confidence::High,
                evidence: vec![format!("compiler identification at {o:#x}")],
                hint: "GCC-built: the CRT is MinGW's or glibc's, not MSVC's",
            },
        );
    }
    if let Some(o) = clang {
        let text = ident(bytes, o + CLANG.len());
        add(
            out,
            Finding {
                role: Role::Compiler,
                name: "Clang",
                version: text
                    .split(' ')
                    .next()
                    .filter(|v| !v.is_empty())
                    .map(str::to_owned),
                confidence: Confidence::High,
                evidence: vec![format!("compiler identification at {o:#x}")],
                hint: "",
            },
        );
    }
    if let Some((o, commit)) = rustc.and_then(|o| rust_commit(bytes, o)) {
        add(
            out,
            Finding {
                role: Role::Compiler,
                name: "Rust",
                version: Some(format!("rustc commit {commit}")),
                confidence: Confidence::High,
                evidence: vec![format!("rustc source path at {o:#x}")],
                hint: "monomorphized generics and inlined iterators: read the panic locations' file paths for the crate layout",
            },
        );
    }
    if let Some(o) = go {
        add(
            out,
            Finding {
                role: Role::Compiler,
                name: "Go",
                version: go_version(bytes, o),
                confidence: Confidence::High,
                evidence: vec![format!("build information at {o:#x}")],
                hint: "names and types come from the pclntab and type links; expect a large runtime around little user code",
            },
        );
    }
}

/// The tools of the Visual Studio 2015 and later toolsets, by their Rich
/// header product id: what each counted object was made by.
const RICH_TOOLS: [(u16, &str); 18] = [
    (0xfd, "aliasobj"),
    (0xfe, "cvtpgd"),
    (0xff, "cvtres"),
    (0x100, "export"),
    (0x101, "implib"),
    (0x102, "linker"),
    (0x103, "MASM"),
    (0x104, "C"),
    (0x105, "C++"),
    (0x106, "C/CIL"),
    (0x107, "C++/CIL"),
    (0x108, "C LTCG"),
    (0x109, "C++ LTCG"),
    (0x10a, "MSIL LTCG"),
    (0x10b, "C PGI"),
    (0x10c, "C++ PGI"),
    (0x10d, "C PGO"),
    (0x10e, "C++ PGO"),
];

/// The linker version lld-link writes by default.
const LLD_LINKER: &str = "14.0";
/// The first Rich product id of the Visual Studio 2015 and later toolsets.
const RICH_VS2015: u16 = 0xfd;
/// The Rich product id of the linker of those toolsets.
const RICH_LINKER: u16 = 0x102;
/// The Rich product ids at or above which an older toolset's build 50727
/// is Visual Studio 2012's rather than 2005's.
const RICH_VS2012: u16 = 0xc7;

/// Visual Studio 2015 and later releases by the builds their compiler and
/// linker carry: `(first build, last build, cl version, release)`, in
/// build order.
const MSVC_BUILDS: [(u16, u16, &str, &str); 38] = [
    (23026, 23026, "19.00", "Visual Studio 2015"),
    (23506, 23506, "19.00", "Visual Studio 2015 Update 1"),
    (23918, 23918, "19.00", "Visual Studio 2015 Update 2"),
    (24123, 24215, "19.00", "Visual Studio 2015 Update 3"),
    (25017, 25019, "19.10", "Visual Studio 2017 15.0-15.2"),
    (25506, 25508, "19.11", "Visual Studio 2017 15.3-15.4"),
    (25830, 25835, "19.12", "Visual Studio 2017 15.5"),
    (26128, 26132, "19.13", "Visual Studio 2017 15.6"),
    (26428, 26433, "19.14", "Visual Studio 2017 15.7"),
    (26726, 26732, "19.15", "Visual Studio 2017 15.8"),
    (27023, 27054, "19.16", "Visual Studio 2017 15.9"),
    (27508, 27508, "19.20", "Visual Studio 2019 16.0"),
    (27702, 27702, "19.21", "Visual Studio 2019 16.1"),
    (27905, 27905, "19.22", "Visual Studio 2019 16.2"),
    (28105, 28107, "19.23", "Visual Studio 2019 16.3"),
    (28314, 28319, "19.24", "Visual Studio 2019 16.4"),
    (28610, 28614, "19.25", "Visual Studio 2019 16.5"),
    (28805, 28806, "19.26", "Visual Studio 2019 16.6"),
    (29110, 29112, "19.27", "Visual Studio 2019 16.7"),
    (29333, 29337, "19.28", "Visual Studio 2019 16.8"),
    (29910, 29915, "19.28", "Visual Studio 2019 16.9"),
    (30037, 30040, "19.29", "Visual Studio 2019 16.10"),
    (30133, 30159, "19.29", "Visual Studio 2019 16.11"),
    (30705, 30709, "19.30", "Visual Studio 2022 17.0"),
    (31104, 31114, "19.31", "Visual Studio 2022 17.1"),
    (31326, 31332, "19.32", "Visual Studio 2022 17.2"),
    (31517, 31631, "19.33", "Visual Studio 2022 17.3"),
    (31933, 31948, "19.34", "Visual Studio 2022 17.4"),
    (32215, 32217, "19.35", "Visual Studio 2022 17.5"),
    (32532, 32546, "19.36", "Visual Studio 2022 17.6"),
    (32822, 32826, "19.37", "Visual Studio 2022 17.7"),
    (33130, 33145, "19.38", "Visual Studio 2022 17.8"),
    (33519, 33523, "19.39", "Visual Studio 2022 17.9"),
    (33808, 33816, "19.40", "Visual Studio 2022 17.10"),
    (34120, 34123, "19.41", "Visual Studio 2022 17.11"),
    (34433, 34441, "19.42", "Visual Studio 2022 17.12"),
    (34808, 34810, "19.43", "Visual Studio 2022 17.13"),
    (35207, 35225, "19.44", "Visual Studio 2022 17.14"),
];

/// Releases before Visual Studio 2015 by the one build each shipped:
/// `(build, cl version, release)`. Build 50727 is two releases; the
/// product id tells them apart ([`RICH_VS2012`]).
const MSVC_OLD_BUILDS: [(u16, &str, &str); 17] = [
    (8168, "12.00", "Visual Studio 6"),
    (9466, "13.00", "Visual Studio .NET 2002"),
    (3077, "13.10", "Visual Studio .NET 2003"),
    (6030, "13.10", "Visual Studio .NET 2003 SP1"),
    (21022, "15.00", "Visual Studio 2008"),
    (30729, "15.00", "Visual Studio 2008 SP1"),
    (30319, "16.00", "Visual Studio 2010"),
    (40219, "16.00", "Visual Studio 2010 SP1"),
    (51106, "17.00", "Visual Studio 2012 Update 1"),
    (60315, "17.00", "Visual Studio 2012 Update 2"),
    (60610, "17.00", "Visual Studio 2012 Update 3"),
    (61030, "17.00", "Visual Studio 2012 Update 4"),
    (21005, "18.00", "Visual Studio 2013"),
    (30501, "18.00", "Visual Studio 2013 Update 2"),
    (30723, "18.00", "Visual Studio 2013 Update 3"),
    (31101, "18.00", "Visual Studio 2013 Update 4"),
    (40629, "18.00", "Visual Studio 2013 Update 5"),
];

/// The release a Rich entry's toolset build names, and how sure that is.
///
/// # Arguments
///
/// * `id` - The entry's product id.
/// * `build` - Its build.
fn msvc_release(id: u16, build: u16) -> (String, Confidence) {
    if id < RICH_VS2015 {
        if build == 50727 {
            return if id >= RICH_VS2012 {
                ("cl 17.00, Visual Studio 2012".to_owned(), Confidence::High)
            } else {
                ("cl 14.00, Visual Studio 2005".to_owned(), Confidence::High)
            };
        }
        return MSVC_OLD_BUILDS.iter().find(|b| b.0 == build).map_or_else(
            || {
                (
                    format!(
                        "a toolset before Visual Studio 2015, build {build} not in borer's table"
                    ),
                    Confidence::Medium,
                )
            },
            |(_, cl, release)| (format!("cl {cl}, {release}"), Confidence::High),
        );
    }
    if let Some((_, _, cl, release)) = MSVC_BUILDS.iter().find(|b| (b.0..=b.1).contains(&build)) {
        return (
            format!("cl {cl} build {build}, {release}"),
            Confidence::High,
        );
    }
    let before = MSVC_BUILDS.iter().rev().find(|b| b.1 < build);
    let after = MSVC_BUILDS.iter().find(|b| b.0 > build);
    let text = match (before, after) {
        (Some(b), Some(a)) => format!("build {build}, between {} and {}", b.3, a.3),
        (Some(b), None) => format!(
            "build {build}, newer than {}, where borer's table ends",
            b.3
        ),
        _ => format!("build {build}, not in borer's table"),
    };
    (text, Confidence::Medium)
}

/// The MSVC toolset the Rich header names: the linker's build, or the
/// newest tool's when the linker is not listed, and the objects each
/// language contributed.
///
/// # Arguments
///
/// * `rich` - The Rich header entries ([`crate::headers::Headers::rich`]).
fn msvc(rich: &[(u16, u16, u32)]) -> Option<Finding> {
    let tools: Vec<&(u16, u16, u32)> = rich.iter().filter(|e| e.0 > 1).collect();
    let pick = tools
        .iter()
        .find(|e| e.0 == RICH_LINKER)
        .or_else(|| tools.iter().max_by_key(|e| (e.0, e.1)))?;
    let (release, confidence) = msvc_release(pick.0, pick.1);
    let langs: Vec<String> = RICH_TOOLS
        .iter()
        .filter(|(id, _)| *id >= 0x103)
        .filter_map(|&(id, name)| {
            let n: u64 = rich
                .iter()
                .filter(|e| e.0 == id)
                .map(|e| u64::from(e.2))
                .sum();
            (n > 0).then(|| format!("{name} {n}"))
        })
        .collect();
    let tool = RICH_TOOLS
        .iter()
        .find(|t| t.0 == pick.0)
        .map_or("tool", |t| t.1);
    let mut evidence = vec![format!("Rich header {tool} entry {:#x}.{}", pick.0, pick.1)];
    if !langs.is_empty() {
        evidence.push(format!("objects by language: {}", langs.join(", ")));
    }
    Some(Finding {
        role: Role::Compiler,
        name: "MSVC",
        version: Some(release),
        confidence,
        evidence,
        hint: "",
    })
}

/// The .NET runtime a CLR header names: the framework its references
/// point at, and whether native code sits beside the IL.
///
/// # Arguments
///
/// * `p` - The loaded file.
/// * `out` - The findings so far.
fn dotnet(p: &Program, out: &mut Vec<Finding>) {
    match &p.clr {
        Some(Ok(clr)) => {
            let framework = clr
                .assembly_refs
                .iter()
                .find_map(|r| match r.name.as_str() {
                    "mscorlib" => Some(format!(".NET Framework (mscorlib {})", r.version)),
                    "System.Runtime" => Some(format!(
                        ".NET Core or .NET 5+ (System.Runtime {})",
                        r.version
                    )),
                    "netstandard" => Some(format!(".NET Standard (netstandard {})", r.version)),
                    _ => None,
                });
            let mixed = clr.flags & 1 == 0;
            add(
                out,
                Finding {
                    role: Role::Compiler,
                    name: ".NET",
                    version: framework.or_else(|| Some(format!("metadata {}", clr.version))),
                    confidence: Confidence::High,
                    evidence: vec![format!(
                        "CLR header at {:#x}, {}",
                        clr.at,
                        if mixed {
                            "native code beside the IL (C++/CLI or ReadyToRun)"
                        } else {
                            "IL only"
                        }
                    )],
                    hint: "the code is IL: read it with borer://clr, not the x86 disassembly",
                },
            );
        }
        Some(Err(_)) => add(
            out,
            plain(
                Role::Compiler,
                ".NET",
                Confidence::Medium,
                "a CLR header whose metadata was refused".to_owned(),
                "",
            ),
        ),
        None => {}
    }
}

/// The findings the file's structure gives: the Rich header, the pclntab,
/// the CLR header, the Visual Basic runtime import, the NW.js loader
/// import, the VCL's resources, a .NET apphost.
///
/// # Arguments
///
/// * `p` - The loaded file.
/// * `res` - Its resources ([`crate::rsrc::resources`]).
/// * `out` - The findings so far.
fn by_structure(p: &Program, res: &[crate::rsrc::Resource], out: &mut Vec<Finding>) {
    if let Some(f) = msvc(&p.headers.rich) {
        add(out, f);
    }
    if p.format == BinaryFormat::Pe
        && p.headers.rich.is_empty()
        && p.headers.linker.as_deref() == Some(LLD_LINKER)
    {
        add(
            out,
            plain(
                Role::Compiler,
                "LLVM lld-link",
                Confidence::Low,
                format!(
                    "no Rich header and linker version {LLD_LINKER}, lld-link's default; MSVC's link.exe writes a Rich header unless it is stripped"
                ),
                "",
            ),
        );
    }
    if let Some(go) = &p.go {
        add(
            out,
            plain(
                Role::Compiler,
                "Go",
                Confidence::High,
                format!("pclntab at {:#x}", go.at),
                "",
            ),
        );
    }
    dotnet(p, out);
    for lib in &p.headers.libraries {
        let found = match lib.to_ascii_lowercase().as_str() {
            "msvbvm60.dll" => Some((Role::Compiler, "Visual Basic 6")),
            "msvbvm50.dll" => Some((Role::Compiler, "Visual Basic 5")),
            "nw_elf.dll" | "nw.dll" => Some((Role::Wrapper, "NW.js")),
            _ => None,
        };
        if let Some((role, name)) = found {
            let hint = if role == Role::Wrapper {
                "the logic is JavaScript in package.nw or beside the executable, not in this binary"
            } else {
                "the VB runtime runs the program: the project header the entry point pushes lists its forms and modules"
            };
            add(
                out,
                plain(role, name, Confidence::High, format!("imports {lib}"), hint),
            );
        }
    }
    let vcl: Vec<String> = res
        .iter()
        .filter(|r| {
            r.kind == crate::rsrc::RCDATA && matches!(r.name.as_str(), "DVCLAL" | "PACKAGEINFO")
        })
        .map(|r| format!("RCDATA {} at {:#x}", r.name, r.off))
        .collect();
    if !vcl.is_empty() {
        add(
            out,
            Finding {
                role: Role::Compiler,
                name: "Delphi or C++Builder",
                version: None,
                confidence: Confidence::High,
                evidence: vcl,
                hint: "a VCL program: forms are RCDATA resources and the RTTI names the classes",
            },
        );
    }
    if let Some((at, 0)) = bundle::dotnet_marker(&p.bytes) {
        add(
            out,
            plain(
                Role::Wrapper,
                ".NET apphost",
                Confidence::High,
                format!("bundle marker at {at:#x} with no bundle behind it"),
                "a launcher: the program is the .dll of the same name beside it",
            ),
        );
    }
}

/// The wrapper each payload names ([`bundle::bundles`]).
///
/// # Arguments
///
/// * `bundles` - The payloads.
/// * `out` - The findings so far.
fn by_bundles(bundles: &[Bundle], out: &mut Vec<Finding>) {
    for b in bundles {
        add(
            out,
            Finding {
                role: Role::Wrapper,
                name: b.wrapper,
                version: b.about.clone(),
                confidence: Confidence::High,
                evidence: vec![format!("payload table at {:#x}", b.off)],
                hint: "",
            },
        );
    }
}

/// The packers [`crate::analysis::render::packer_marks`] names: sure when
/// an entry stub or a header mark says so, less when only a section name
/// does, which anyone can write.
///
/// # Arguments
///
/// * `p` - The loaded file.
/// * `out` - The findings so far.
fn by_packer_marks(p: &Program, out: &mut Vec<Finding>) {
    for (name, marks) in crate::analysis::render::packer_marks(p) {
        let by_section = marks.iter().filter(|m| m.ends_with(" section")).count();
        let renamed = name == "UPX" && by_section == 0;
        add(
            out,
            Finding {
                role: Role::Packer,
                name,
                version: renamed
                    .then(|| "sections renamed: a modified or hand-edited UPX".to_owned()),
                confidence: if by_section < marks.len() {
                    Confidence::High
                } else {
                    Confidence::Medium
                },
                evidence: marks,
                hint: "the code here is the unpacker: borer://unpack/<entry> runs it to the original entry point",
            },
        );
    }
}

/// Everything the file says about what built and wraps it, compilers
/// first, then wrappers, then packers, each in the order found.
///
/// # Arguments
///
/// * `p` - The loaded file.
/// * `bundles` - Its payloads ([`bundle::bundles`]).
#[must_use]
pub fn identify(p: &Program, bundles: &[Bundle]) -> Vec<Finding> {
    let res = crate::rsrc::resources(p);
    let mut out = Vec::new();
    by_structure(p, &res, &mut out);
    by_bundles(bundles, &mut out);
    by_marks(&p.bytes, &mut out);
    by_packer_marks(p, &mut out);
    out.sort_by_key(|f| f.role);
    out
}

/// The lines a file summary or a triage shows about what built the file.
///
/// One per finding (the role, the name and version, the confidence and the
/// evidence) and one per payload; a file with headers whose compiler nothing
/// names says it is unknown, while a raw file, with none to read, says nothing.
///
/// # Arguments
///
/// * `p` - The loaded file.
/// * `triage` - Lines for a triage: labels unpadded and each finding's
///   hint after it.
#[must_use]
pub fn lines(p: &Program, triage: bool) -> Vec<String> {
    let label = |role: Role| match (role, triage) {
        (Role::Compiler, false) => "built:   ",
        (Role::Packer, false) => "packer:  ",
        (Role::Compiler, true) => "built: ",
        (Role::Packer, true) => "packer: ",
        (Role::Wrapper, _) => "wrapper: ",
    };
    let bundles = bundle::bundles(p);
    let found = identify(p, &bundles);
    let mut out: Vec<String> = Vec::new();
    if p.format != BinaryFormat::Raw && !found.iter().any(|f| f.role == Role::Compiler) {
        out.push(format!(
            "{}unknown: no Rich header, compiler text or runtime mark{}",
            label(Role::Compiler),
            p.headers
                .linker
                .as_ref()
                .map_or_else(String::new, |l| format!("; linker version {l}"))
        ));
    }
    for f in &found {
        let mut line = format!(
            "{}{}{} ({}: {})",
            label(f.role),
            f.name,
            f.version
                .as_ref()
                .map_or_else(String::new, |v| format!(", {}", crate::text::one_line(v))),
            f.confidence.word(),
            f.evidence.join("; ")
        );
        if triage && !f.hint.is_empty() {
            line.push_str(" - ");
            line.push_str(f.hint);
        }
        out.push(line);
    }
    for b in &bundles {
        out.push(format!(
            "payload: {} at {:#x}, {}; borer://children lists each with its offset and size",
            b.wrapper,
            b.off,
            bundle::entry_count(b)
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{Confidence, first_offsets, msvc, msvc_release};

    /// The linker's build names the release, and the objects are counted by
    /// language.
    ///
    /// # Panics
    ///
    /// When the release or the counts read otherwise.
    #[test]
    fn the_rich_linker_entry_names_the_release() {
        let f = msvc(&[
            (0x105, 33135, 200),
            (0x104, 33135, 30),
            (0x102, 33135, 1),
            (1, 0, 300),
        ])
        .expect("an MSVC finding");
        assert_eq!(
            f.version.as_deref(),
            Some("cl 19.38 build 33135, Visual Studio 2022 17.8")
        );
        assert_eq!(f.confidence, Confidence::High);
        assert_eq!(f.evidence[1], "objects by language: C 30, C++ 200");
        assert!(msvc(&[(1, 0, 10)]).is_none());
        let big = msvc(&[(0x105, 1, u32::MAX), (0x105, 2, 1)]).expect("an MSVC finding");
        assert_eq!(big.evidence[1], "objects by language: C++ 4294967296");
    }

    /// Older toolsets are named by their one build, 50727 by its product
    /// id, and a build outside the table says where it falls.
    ///
    /// # Panics
    ///
    /// When a release reads otherwise.
    #[test]
    fn builds_outside_the_newest_toolsets_say_what_they_can() {
        assert_eq!(
            msvc_release(0x9d, 40219).0,
            "cl 16.00, Visual Studio 2010 SP1"
        );
        assert_eq!(msvc_release(0xcc, 50727).0, "cl 17.00, Visual Studio 2012");
        assert_eq!(msvc_release(0x78, 50727).0, "cl 14.00, Visual Studio 2005");
        let (gap, sure) = msvc_release(0x102, 30000);
        assert_eq!(
            gap,
            "build 30000, between Visual Studio 2019 16.9 and Visual Studio 2019 16.10"
        );
        assert_eq!(sure, Confidence::Medium);
        assert!(
            msvc_release(0x102, 40000)
                .0
                .contains("newer than Visual Studio 2022 17.14")
        );
    }

    /// One pass finds each needle's first offset, an empty one never.
    ///
    /// # Panics
    ///
    /// When an offset reads otherwise.
    #[test]
    fn the_mark_scan_finds_first_offsets() {
        let found = first_offsets(
            b"xxabcabz",
            &[b"ab".to_vec(), b"abz".to_vec(), Vec::new(), b"q".to_vec()],
        );
        assert_eq!(found, [Some(2), Some(5), None, None]);
    }
}
