//! Whose template signatures a function references, from the strings GCC
//! and Clang write.
//!
//! Each image is hand-built: a `main` calling each function, the
//! functions, and the signature strings in read-only data. Each function
//! is one of the shapes the C-208 replan found passing every byte-level
//! test of "this string is the function's own" while the template was
//! inlined into it (Revision 2, counterexamples 1-10), reduced to its
//! entry and its references. None takes a name from a template
//! signature; each gains one `// references the signature of:` line per
//! template it references, which is true of the template's own body, of
//! an inliner, and of a callee handed the string alike.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::answer_header;
use borer_engine::analysis::render::function_summary;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::{from_usize, lo32, saturating_usize};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};
use borer_engine::progress::Workers;

/// One function of an image.
struct Fun {
    /// Its entry.
    entry: u64,
    /// The bytes before its references.
    pre: Vec<u8>,
    /// The strings it references, in order, by address.
    refs: Vec<u64>,
    /// The bytes after its references.
    post: Vec<u8>,
}

/// `push rbp; mov rbp, rsp; sub rsp, 0x20`.
const FRAME: [u8; 8] = [0x55, 0x48, 0x89, 0xe5, 0x48, 0x83, 0xec, 0x20];

/// `leave; ret`.
const LEAVE: [u8; 2] = [0xc9, 0xc3];

/// `mov [rbp-4], edi`.
const SPILL_EDI: [u8; 3] = [0x89, 0x7d, 0xfc];

/// `cmp dword [rbp-4], 0`.
const RELOAD: [u8; 4] = [0x83, 0x7d, 0xfc, 0x00];

/// Clang's `static T &Singleton<Foo>::get()`.
const GET: &str = "static T &Singleton<Foo>::get() [T = Foo]";

/// Clang's `T &registry()`.
const REGISTRY: &str = "T &registry() [T = Foo]";

/// Clang's `static void Box<int>::Make(T)`.
const MAKE: &str = "static void Box<int>::Make(T) [T = int]";

/// Clang's `static void Box<int>::Check(T)`.
const CHECK: &str = "static void Box<int>::Check(T) [T = int]";

/// Clang's `T &Vec<int>::back()`.
const BACK: &str = "T &Vec<int>::back() [T = int]";

/// Clang's `T &Vec<int>::front()`.
const FRONT: &str = "T &Vec<int>::front() [T = int]";

/// GCC's `T& Vec<T>::back()`.
const GCC_BACK: &str = "T& Vec<T>::back() [with T = int]";

/// Returns a function of `pre`, its references and `post`.
///
/// # Arguments
///
/// * `entry` - Its entry.
/// * `pre` - The bytes before its references.
/// * `refs` - The strings it references.
/// * `post` - The bytes after them.
fn fun(entry: u64, pre: &[&[u8]], refs: &[u64], post: &[u8]) -> Fun {
    Fun {
        entry,
        pre: pre.concat(),
        refs: refs.to_vec(),
        post: post.to_vec(),
    }
}

/// Builds an image of `funs` and the strings `sigs`.
///
/// `.text` is at 0x1000, entered at a `main` that calls each function, and
/// a read-only `.rodata` at 0x2000 holds the strings, each referenced by a
/// `lea rax, [rip+string]`.
///
/// # Arguments
///
/// * `elf` - An ELF image (System V) or a raw one (Microsoft x64).
/// * `funs` - The functions, in address order past `main`.
/// * `sigs` - Each string's address and text.
fn image(elf: bool, funs: &[Fun], sigs: &[(u64, &str)]) -> Program {
    let rel = |end: u64, to: u64| lo32(to.wrapping_sub(end)).to_le_bytes();
    let mut text = Vec::with_capacity(0x2000);
    for f in funs {
        let end = 0x1000 + from_usize(text.len()) + 5;
        text.push(0xe8); // ASM: call f
        text.extend(rel(end, f.entry));
    }
    text.push(0xc3); // ASM: ret
    for f in funs {
        text.resize(saturating_usize(f.entry - 0x1000), 0xcc);
        text.extend_from_slice(&f.pre);
        for &to in &f.refs {
            let end = 0x1000 + from_usize(text.len()) + 7;
            text.extend([0x48, 0x8d, 0x05]); // ASM: lea rax,[rip+string]
            text.extend(rel(end, to));
        }
        text.extend_from_slice(&f.post);
    }
    text.resize(0x2000, 0);
    for &(at, sig) in sigs {
        let off = saturating_usize(at - 0x1000);
        text[off..off + sig.len()].copy_from_slice(sig.as_bytes());
    }
    let mut p = Program::raw(
        text,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rodata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    if elf {
        p.format = BinaryFormat::Elf;
    }
    p
}

/// Returns a function's name and the signature lines of its header.
///
/// Each `// references the signature of:` line comes with its prefix cut,
/// then the `signatures referenced:` count line when there is one.
///
/// # Arguments
///
/// * `p` - The image.
/// * `a` - Its analysis.
/// * `entry` - The function's entry.
fn read(p: &Program, a: &Analysis, entry: u64) -> (Option<String>, Vec<String>) {
    let name = a.function(entry).and_then(|f| f.name.clone());
    let header = answer_header(p, a, &Overlay::default(), entry, None).unwrap_or_default();
    let refs = header
        .lines()
        .filter_map(|l| {
            l.strip_prefix("// references the signature of: ")
                .or_else(|| {
                    l.strip_prefix("// ")
                        .filter(|r| r.starts_with("signatures referenced: "))
                })
        })
        .map(str::to_owned)
        .collect();
    (name, refs)
}

/// Returns the line a name's string at an address gives.
///
/// # Arguments
///
/// * `name` - The name.
/// * `at` - The string's address.
fn line(name: &str, at: u64) -> String {
    format!(
        "{name} (string at {at:#x}; its own body, code inlined from it, or code handed the string)"
    )
}

/// One counterexample: its image, then each function with the name it
/// keeps and the lines it gains.
type Shape = (Program, Vec<(u64, Option<&'static str>, Vec<String>)>);

/// Returns counterexamples 1 to 10, each reduced to its entry and its
/// references.
fn shapes() -> Vec<Shape> {
    let mut all = first_shapes();
    all.extend(later_shapes());
    all
}

/// Returns counterexamples 1 to 5, each reduced to its entry and its
/// references.
fn first_shapes() -> Vec<Shape> {
    let sysv = |funs: &[Fun], sigs: &[(u64, &str)]| image(true, funs, sigs);
    vec![
        (
            sysv(
                &[fun(0x1100, &[], &[0x2000, 0x2100], &[0xc3])],
                &[(0x2000, GET), (0x2100, REGISTRY)],
            ),
            vec![(
                0x1100,
                None,
                vec![
                    line("Singleton<Foo>::get", 0x2000),
                    line("registry", 0x2100),
                ],
            )],
        ),
        (
            sysv(
                &[
                    fun(0x1100, &[], &[0x2000, 0x2100], &[0xc3]),
                    fun(0x1140, &[], &[0x2100], &[0xc3]),
                ],
                &[(0x2000, "void shutdown_all()"), (0x2100, GET)],
            ),
            vec![
                (
                    0x1100,
                    Some("shutdown_all"),
                    vec![line("Singleton<Foo>::get", 0x2100)],
                ),
                (0x1140, None, vec![line("Singleton<Foo>::get", 0x2100)]),
            ],
        ),
        (
            sysv(
                &[fun(
                    0x1100,
                    &[&[0x48, 0x89, 0x3c, 0x24], &[0x48, 0x89, 0xe7]], // ASM: mov [rsp],rdi; mov rdi,rsp
                    &[0x2000],
                    &[0xc3],
                )],
                &[(0x2000, MAKE)],
            ),
            vec![(0x1100, None, vec![line("Box<int>::Make", 0x2000)])],
        ),
        (
            sysv(
                &[fun(
                    0x1100,
                    &[&FRAME, &SPILL_EDI, &[0x48, 0x8d, 0x7d, 0xfc], &RELOAD], // ASM: lea rdi,[rbp-4]
                    &[0x2000],
                    &LEAVE,
                )],
                &[(0x2000, CHECK)],
            ),
            vec![(0x1100, None, vec![line("Box<int>::Check", 0x2000)])],
        ),
        (
            sysv(
                &[fun(
                    0x1100,
                    &[&FRAME, &SPILL_EDI, &RELOAD],
                    &[0x2000],
                    &LEAVE,
                )],
                &[(0x2000, CHECK)],
            ),
            vec![(0x1100, None, vec![line("Box<int>::Check", 0x2000)])],
        ),
    ]
}

/// Returns counterexamples 6 to 10, each reduced to its entry and its
/// references.
fn later_shapes() -> Vec<Shape> {
    let sysv = |funs: &[Fun], sigs: &[(u64, &str)]| image(true, funs, sigs);
    vec![
        (
            sysv(
                &[fun(
                    0x1100,
                    &[&FRAME, &SPILL_EDI, &[0x48, 0x8d, 0x45, 0xfc], &RELOAD], // ASM: lea rax,[rbp-4]
                    &[0x2000],
                    &LEAVE,
                )],
                &[(0x2000, CHECK)],
            ),
            vec![(0x1100, None, vec![line("Box<int>::Check", 0x2000)])],
        ),
        (
            image(
                false,
                &[fun(
                    0x1100,
                    &[
                        &[0x55],                                           // ASM: push rbp
                        &[0x48, 0x83, 0xec, 0x30],                         // ASM: sub rsp,0x30
                        &[0x48, 0x8d, 0x6c, 0x24, 0x30], // ASM: lea rbp,[rsp+0x30]
                        &[0x48, 0xc7, 0x45, 0xf8, 0xfe, 0xff, 0xff, 0xff], // ASM: mov qword [rbp-8],-2
                        &[0x89, 0x4d, 0xf4],                               // ASM: mov [rbp-0xc],ecx
                    ],
                    &[0x2000],
                    &[0x48, 0x83, 0xc4, 0x30, 0x5d, 0xc3], // ASM: add rsp,0x30; pop rbp; ret
                )],
                &[(0x2000, CHECK)],
            ),
            vec![(0x1100, None, vec![line("Box<int>::Check", 0x2000)])],
        ),
        (
            sysv(
                &[fun(
                    0x1100,
                    &[&FRAME, &[0x48, 0x89, 0x7d, 0xf0]], // ASM: mov [rbp-0x10],rdi
                    &[0x2000],
                    &LEAVE,
                )],
                &[(0x2000, BACK)],
            ),
            vec![(0x1100, None, vec![line("Vec<int>::back", 0x2000)])],
        ),
        (
            sysv(
                &[fun(
                    0x1100,
                    &[&FRAME, &[0x48, 0x89, 0x7d, 0xf0]], // ASM: mov [rbp-0x10],rdi
                    &[0x2000],
                    &LEAVE,
                )],
                &[(0x2000, FRONT)],
            ),
            vec![(0x1100, None, vec![line("Vec<int>::front", 0x2000)])],
        ),
        (
            sysv(
                &[fun(0x1100, &[], &[0x2000], &[0xc3])],
                &[(0x2000, GCC_BACK)],
            ),
            vec![(0x1100, None, vec![line("Vec<int>::back", 0x2000)])],
        ),
    ]
}

/// Each counterexample keeps its name and says whose signature it reads.
///
/// It gains one line per template signature it references, in the
/// decompile header and in its summary.
///
/// `shutdown_all` keeps the name its own plain signature gives, and both
/// referrers of the shared `get` string say they reference its signature.
#[test]
fn each_counterexample_keeps_its_name_and_says_whose_signature_it_reads() {
    for (k, (p, want)) in shapes().into_iter().enumerate() {
        let a = Analysis::compute(&p);
        for (entry, name, refs) in want {
            let got = read(&p, &a, entry);
            assert_eq!(got.0.as_deref(), name, "shape {}: {entry:#x}", k + 1);
            assert_eq!(got.1, refs, "shape {}: {entry:#x}", k + 1);
            let summary = function_summary(&p, &a, &Overlay::default(), entry).unwrap_or_default();
            for l in &refs {
                let row = format!("references the signature of: {l}\n");
                assert!(summary.contains(&row), "shape {}: {summary}", k + 1);
            }
        }
    }
}

/// Past eight names a function lists the first eight, in string address
/// order, and says how many there are.
#[test]
fn past_eight_names_the_lines_say_how_many() {
    let sigs: Vec<(u64, String)> = (0..10u64)
        .map(|k| {
            (
                0x2000 + 0x80 * k,
                format!("void Box<int>::M{k}() [T = int]"),
            )
        })
        .collect();
    let refs: Vec<u64> = sigs.iter().rev().map(|s| s.0).collect();
    let texts: Vec<(u64, &str)> = sigs.iter().map(|(at, s)| (*at, s.as_str())).collect();
    let p = image(true, &[fun(0x1100, &[], &refs, &[0xc3])], &texts);
    let a = Analysis::compute(&p);
    let (_, refs) = read(&p, &a, 0x1100);
    let mut want: Vec<String> = (0..8u64)
        .map(|k| line(&format!("Box<int>::M{k}"), 0x2000 + 0x80 * k))
        .collect();
    want.push("signatures referenced: showing 8 of 10".to_owned());
    assert_eq!(refs, want);
    let summary = function_summary(&p, &a, &Overlay::default(), 0x1100).unwrap_or_default();
    let rows = summary.matches("\nreferences the signature of: ").count();
    assert_eq!(rows, 8, "{summary}");
    assert!(
        summary.contains("\nsignatures referenced: showing 8 of 10\n"),
        "{summary}"
    );
}

/// A log format that ends in a bracketed `[name = value]` gives no line:
/// its head declares no function, as the plain signature guard reads it.
#[test]
fn a_log_format_gives_no_line() {
    let p = image(
        true,
        &[fun(
            0x1100,
            &[],
            &[0x2000, 0x2100, 0x2200, 0x2300, 0x2400],
            &[0xc3],
        )],
        &[
            (0x2000, "send (%zu bytes) [fd = %d]"),
            (0x2100, "recv() [rc = %d]"),
            (0x2200, "Retrying: open (%s) [errno = %d]"),
            (0x2300, "Retrying: Net::open(%s) [errno = %d]"),
            (0x2400, "Calling Net::Connect() [fd = %d]"),
        ],
    );
    let a = Analysis::compute(&p);
    assert_eq!(read(&p, &a, 0x1100), (None, Vec::new()));
}

/// A string read from inside, or one not ending in its bindings, holds
/// nothing: only a string referenced at its first byte counts.
#[test]
fn only_a_string_referenced_at_its_start_counts() {
    let p = image(
        true,
        &[fun(0x1100, &[], &[0x2001, 0x2100], &[0xc3])],
        &[
            (0x2000, BACK),
            (0x2100, "void Box<int>::Grow() [T = int] trailing"),
        ],
    );
    let a = Analysis::compute(&p);
    assert_eq!(read(&p, &a, 0x1100), (None, Vec::new()));
}

/// Data addresses the wide image's function references besides its two
/// template signatures: past the 256 items under which the program's
/// strings are read on one thread.
const WIDE: u64 = 298;

/// Returns an image whose one function references its two template
/// signatures and [`WIDE`] other data addresses, so the program's strings
/// are read across the workers.
fn wide() -> Shape {
    let refs: Vec<u64> = [0x2000, 0x2100]
        .into_iter()
        .chain((0..WIDE).map(|k| 0x2200 + 8 * k))
        .collect();
    let p = image(
        true,
        &[fun(0x1100, &[], &refs, &[0xc3])],
        &[(0x2000, BACK), (0x2100, GCC_BACK)],
    );
    let lines = vec![line("Vec<int>::back", 0x2000)];
    (p, vec![(0x1100, None, lines)])
}

/// Names and lines are the same for two analyses and for one worker as
/// for many, the strings read on several threads included.
#[test]
fn signature_lines_are_deterministic() {
    let answer = || {
        shapes()
            .into_iter()
            .chain([wide()])
            .map(|(p, want)| {
                let a = Analysis::compute(&p);
                want.iter()
                    .map(|(entry, _, lines)| {
                        let got = read(&p, &a, *entry);
                        assert_eq!(&got.1, lines, "{entry:#x}");
                        got
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    };
    let first = answer();
    assert_eq!(first, answer());
    let one = Workers(std::num::NonZeroUsize::MIN).within(answer);
    assert_eq!(first, one);
}
