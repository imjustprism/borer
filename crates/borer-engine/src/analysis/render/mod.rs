//! Agent-facing renderings of analysis results (plain-text tables,
//! mermaid graphs, hard caps, showing-N-of-M headers).
//!
//! The helpers here are the conventions every renderer shares: a count's
//! plural, the `(+N more)` and `# N more ...` tails of a cut list, the
//! `borer://.../<filter>` hint, and the way a spec's address token is read.

mod catalog;
mod dataflow;
mod diff;
mod graph;
mod listing;
mod literals;
mod obfuscation;
mod oracle;
mod protection;
mod runs;
mod summary;
mod triage;
mod unpack;

pub use catalog::*;
pub use dataflow::*;
pub use diff::*;
pub use graph::*;
pub use listing::*;
pub use literals::*;
pub use obfuscation::*;
pub use oracle::*;
pub use protection::*;
pub use runs::*;
pub use summary::*;
pub use triage::*;
pub use unpack::*;

use super::{
    Analysis, BasicBlock, BlockTerm, Function, Overlay, RefKind, RefSite, bare_name, name_of,
    parse_addr,
};
use crate::disasm;
use crate::emulate::{Emulator, Stop, Written};
use crate::isa::x86::{
    Decoder, DecoderOptions, FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess,
    OpKind, Register,
};
use crate::num::from_usize;
use crate::program::{BinaryFormat, Feature, Program, Section, Symbol, SymbolKind};
use crate::strings::{cstr_at, literal_byte, wstr_at};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::Arc;

/// `s` when `n` is not one, so a count reads `1 string` and `2 strings`.
///
/// # Arguments
///
/// * `n` - The count.
pub(super) fn plural(n: usize) -> &'static str {
    if n == 1 { "" } else { "s" }
}

/// The ` (+N more)` tail of a list cut at `cap`.
///
/// # Arguments
///
/// * `total` - How many there were.
/// * `cap` - How many were shown at most.
///
/// # Returns
///
/// The tail, or an empty string when nothing was cut.
pub(super) fn plus_more(total: usize, cap: usize) -> String {
    let more = total.saturating_sub(cap);
    if more > 0 {
        format!(" (+{more} more)")
    } else {
        String::new()
    }
}

/// Writes `# N more <what>` under a list cut at `cap`.
///
/// # Arguments
///
/// * `out` - The report.
/// * `total` - How many there were.
/// * `cap` - How many were listed at most.
/// * `what` - The rest of the line: `not listed`, `fields not listed`.
pub(super) fn more_line(out: &mut String, total: usize, cap: usize, what: &str) {
    if total > cap {
        let _ = writeln!(out, "# {} more {what}", total - cap);
    }
}

/// Writes `  ... +N more<what>` under an indented list cut at `cap`.
///
/// # Arguments
///
/// * `out` - The report.
/// * `total` - How many there were.
/// * `cap` - How many were listed at most.
/// * `what` - A noun with its leading space, or nothing.
pub(super) fn elided_line(out: &mut String, total: usize, cap: usize, what: &str) {
    if total > cap {
        let _ = writeln!(out, "  ... +{} more{what}", total - cap);
    }
}

/// The `; borer://<resource>/<filter> narrows the list` tail of a header
/// whose list was cut at `cap`.
///
/// # Arguments
///
/// * `total` - How many there were.
/// * `cap` - How many were listed at most.
/// * `resource` - The resource that takes a filter.
///
/// # Returns
///
/// The tail, or an empty string when nothing was cut.
pub(super) fn narrows(total: usize, cap: usize, resource: &str) -> String {
    if total > cap {
        format!("; borer://{resource}/<filter> narrows the list")
    } else {
        String::new()
    }
}

/// An address as `0x..`, or `-` for none.
///
/// # Arguments
///
/// * `va` - The address, when there is one.
pub(super) fn hex_or_dash(va: Option<u64>) -> String {
    va.map_or_else(|| String::from("-"), |va| format!("{va:#x}"))
}

/// A function's name without its module prefix, for a line that names it.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names.
/// * `va` - The function's entry.
pub(super) fn short_name(a: &Analysis, o: &Overlay, va: u64) -> String {
    bare_name(&name_of(a, o, va)).to_owned()
}

/// Every string the program's generators build, recovered once per analysis.
///
/// [`generated_strings`] runs each generator in the emulator, the costliest
/// read any report makes; `why` wants it for every address it is asked
/// about and `triage` for the whole program. The answer depends on the image
/// and its analysis alone, names play no part, so it is built once through
/// [`Analysis::derived`] and every later report reads the same recovery.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
///
/// # Returns
///
/// The unfiltered recovery, shared.
pub(super) fn recovered_strings(p: &Program, a: &Analysis) -> Arc<Recovery> {
    a.derived
        .get_or_build("generated_strings", (), || generated_strings(p, a, ""))
}

/// Resolves a spec's address token: `0x`-hex, decimal, or a function name.
///
/// A name wins over bare text that also reads as a number, as in
/// [`crate::analysis::resolve`]; `0x`-hex is always the address.
///
/// # Arguments
///
/// * `a` - The analysis, for its functions.
/// * `o` - User names.
/// * `text` - The token.
///
/// # Returns
///
/// The address, or `None` when the token is neither a number nor a name.
pub(super) fn locate(a: &Analysis, o: &Overlay, text: &str) -> Option<u64> {
    if crate::analysis::hex_prefixed(text) {
        return parse_addr(text);
    }
    resolve(a, o, text).or_else(|| parse_addr(text))
}

/// Splits a comma-separated spec into its address token and the directives
/// after it.
///
/// # Arguments
///
/// * `spec` - The spec.
///
/// # Returns
///
/// The first token, trimmed, and the rest untrimmed.
pub(super) fn spec_head(spec: &str) -> (&str, std::str::Split<'_, char>) {
    let mut parts = spec.split(',');
    (parts.next().unwrap_or(spec).trim(), parts)
}

/// Writes `bytes` into the machine from `at` on.
///
/// # Arguments
///
/// * `emu` - The machine.
/// * `at` - Where the first byte goes.
/// * `bytes` - The bytes.
pub(super) fn poke_all(emu: &mut Emulator<'_>, at: u64, bytes: &[u8]) {
    for (k, b) in bytes.iter().enumerate() {
        emu.poke(at.wrapping_add(from_usize(k)), *b);
    }
}

/// Visits every instruction of a function, block by block, as the bytes
/// decode.
///
/// A block whose bytes cannot be read is skipped; nothing is sorted or
/// dropped. [`function_instructions`] is the address-ordered, deduplicated
/// form for a pass that needs one.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The function.
/// * `bitness` - Decoder bitness of the program.
/// * `visit` - Called once per instruction.
pub(super) fn each_instruction(
    p: &Program,
    f: &Function,
    bitness: u32,
    mut visit: impl FnMut(&Instruction),
) {
    let mut i = Instruction::default();
    for b in &f.blocks {
        let len = usize::try_from(b.end - b.start).unwrap_or(0);
        let Some(code) = p.read_va(b.start, len) else {
            continue;
        };
        let mut d = Decoder::with_ip(bitness, code, b.start, DecoderOptions::NONE);
        while d.can_decode() {
            d.decode_out(&mut i);
            visit(&i);
        }
    }
}

/// The tail of a fragment answer's header line when it shows the scope
/// headers ([`scope_headers`]) of its lines, numbered `^N`.
pub const SCOPE_NOTE: &str = "; ^N marks context: the signature and the if/else/loop/switch/case headers enclosing the lines shown";

/// The header lines of the pseudo-C scopes enclosing each picked line:
/// the breadcrumbs a fragment of a function needs to be read as true.
///
/// A line of nested pseudo-C states its effect only inside its scopes, and
/// most lines are nested: 64 to 85 percent of the statement lines of a
/// whole-binary decompile run under a condition the line does not carry. A
/// filtered, paged or grepped answer without its headers states each such
/// line as unconditional; readers handed the bare lines answered 2 of 6
/// condition questions right, and 6 of 6 with the enclosing headers beside
/// them, at 1.6 times the tokens. An `else` header comes with the `if` and
/// every `else if` before it, and a `case` or `default` with its `switch`,
/// since `} else {` or `case 3: {` alone names no condition. The function's
/// signature encloses every other line of its text and comes beside them
/// when a line shown reads one of its parameters: it says what `a1` is, which
/// `a1->field_0x24 = 9;` does not, and a fragment that reads no parameter
/// is spared it (half the functions of a program-wide grep).
///
/// The scopes are read from the text as the decompiler writes it: a header
/// ends in `{` and what it encloses is indented deeper, a `}` closes the
/// innermost open header at its own depth, an `else` stands at its `if`'s
/// depth and a `case` at its `switch`'s. The signature is the
/// `// signature:` line, or the first line when the skeleton folds it in
/// there (`// void f(int a1) @ 0x1000: ...`). One pass over the lines, so a
/// filter over a function of thousands of lines stays linear.
///
/// # Arguments
///
/// * `lines` - The function's pseudo-C, one entry per line.
/// * `picked` - Indices into `lines` of the lines an answer shows; an
///   index past the end is ignored.
///
/// # Returns
///
/// The indices of every header enclosing a picked line, in line order, the
/// picked lines themselves left out.
#[must_use]
pub fn scope_headers(lines: &[&str], picked: &[usize]) -> BTreeSet<usize> {
    let depth: Vec<usize> = lines
        .iter()
        .map(|l| l.len() - l.trim_start_matches(' ').len())
        .collect();
    let is_case = |t: &str| t.starts_with("case ") || t.starts_with("default:");
    let enclosing = |open: &[usize], d: usize| open.iter().rev().copied().find(|&h| depth[h] < d);
    let mut parent: Vec<Option<usize>> = vec![None; lines.len()];
    let mut chain: Vec<Option<usize>> = vec![None; lines.len()];
    let mut open: Vec<usize> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        let d = depth[i];
        while open.last().is_some_and(|&h| depth[h] > d) {
            open.pop();
        }
        let level = open.last().copied().filter(|&h| depth[h] == d);
        if t.starts_with('}') {
            if level.is_some() {
                open.pop();
            }
            if t.starts_with("} else") {
                chain[i] = level;
            }
            parent[i] = enclosing(&open, d);
        } else if is_case(t) {
            let switch = match level {
                Some(h) if is_case(lines[h].trim_start()) => {
                    open.pop();
                    open.last().copied().filter(|&s| depth[s] == d)
                }
                other => other,
            };
            chain[i] = switch;
            parent[i] = switch.map_or_else(|| enclosing(&open, d), |s| parent[s]);
        } else {
            parent[i] = enclosing(&open, d);
        }
        if t.ends_with('{') && !t.starts_with("//") {
            open.push(i);
        }
    }
    let mut headers = BTreeSet::new();
    let mut walk: Vec<usize> = picked
        .iter()
        .copied()
        .filter(|&i| i < lines.len())
        .collect();
    while let Some(x) = walk.pop() {
        for h in [chain[x], parent[x]].into_iter().flatten() {
            if headers.insert(h) {
                walk.push(h);
            }
        }
    }
    for p in picked {
        headers.remove(p);
    }
    let signature = lines
        .iter()
        .enumerate()
        .find_map(|(i, l)| Some((i, l.strip_prefix("// signature: ")?)))
        .or_else(|| {
            let (head, _) = lines.first()?.strip_prefix("// ")?.split_once(" @ 0x")?;
            head.contains('(').then_some((0, head))
        });
    if let Some((at, sig)) = signature
        && !picked.contains(&at)
    {
        let names = super::schema::declared_names(sig);
        let reads_one = |i: &usize| {
            lines
                .get(*i)
                .is_some_and(|l| names.iter().any(|n| super::schema::has_word(l, n)))
        };
        if picked.iter().chain(&headers).any(reads_one) {
            headers.insert(at);
        }
    }
    headers
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::string_literal;
    use crate::num::from_usize;
    use crate::program::{Arch, BinaryFormat, Program, Section};

    /// Builds a one-section read-only program holding `data` at 0x2000.
    ///
    /// # Arguments
    ///
    /// * `data` - The section's file bytes.
    fn rodata(data: &[u8]) -> Program {
        let rdata = Section::mapped(".rdata", 0x2000, 0, from_usize(data.len()), false, false);
        Program::raw(data.to_vec(), Arch::X86_64, 0, None, vec![rdata])
    }

    /// A zeroed image of `size` bytes with each `(offset, bytes)` run written in.
    ///
    /// # Arguments
    ///
    /// * `size` - The image's length.
    /// * `runs` - Where each run of bytes goes.
    fn image(size: usize, runs: &[(usize, &[u8])]) -> Vec<u8> {
        let mut bytes = vec![0u8; size];
        for (at, run) in runs {
            bytes[*at..*at + run.len()].copy_from_slice(run);
        }
        bytes
    }

    /// Builds a program whose `.text` is the page at 0x1000 of `bytes`.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The whole image.
    /// * `entry` - The entry point.
    /// * `writable` - Whether the code page is writable, as a decryptor needs.
    fn text(bytes: Vec<u8>, entry: u64, writable: bool) -> Program {
        let text = Section::mapped(".text", 0x1000, 0x1000, 0x1000, writable, true);
        Program::raw(bytes, Arch::X86_64, 0, Some(entry), vec![text])
    }

    /// Hex byte runs parse with or without spaces; odd or empty fail.
    #[test]
    fn hex_bytes_parse() {
        assert_eq!(super::parse_hex_bytes("9090"), Some(vec![0x90, 0x90]));
        assert_eq!(
            super::parse_hex_bytes("90 90 c3"),
            Some(vec![0x90, 0x90, 0xc3])
        );
        assert_eq!(super::parse_hex_bytes(""), None);
        assert_eq!(super::parse_hex_bytes("909"), None);
        assert_eq!(super::parse_hex_bytes("zz"), None);
    }

    /// The experiment spec reads every directive the harness acts on.
    #[test]
    fn experiment_spec_parses_every_directive() {
        let p = rodata(&[]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let spec = super::ExperimentSpec::parse(
            &a,
            &o,
            "0x1000,rcx=0x10,a1=0x2000,a3=7,w0x3000=deadbeef,stop=0x1020,steps=5000,dump=0x3000:8",
        )
        .expect("spec parses");
        assert_eq!(spec.entry, 0x1000);
        assert_eq!(spec.regs, vec![("rcx".to_owned(), 0x10)]);
        assert_eq!(spec.args, vec![(0, 0x2000), (2, 7)], "a1 is position 0");
        assert_eq!(spec.writes, vec![(0x3000, vec![0xde, 0xad, 0xbe, 0xef])]);
        assert_eq!(spec.stop, Some(0x1020));
        assert_eq!(spec.budget, 5000);
        assert_eq!(spec.dumps, vec![(0x3000, 8, 8)]);
    }

    /// A malformed directive names itself in the error.
    #[test]
    fn experiment_spec_reports_a_bad_directive() {
        let p = rodata(&[]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let err = super::ExperimentSpec::parse(&a, &o, "0x1000,dump=0x3000").unwrap_err();
        assert!(err.contains("addr:len"), "{err}");
    }

    /// Writes to one buffer over and over read back as separate strings.
    ///
    /// A decoder fills the same bytes once per string, so the final memory
    /// state keeps only the last of them. Scanning the writes in the order
    /// they happened is what separates them: the address going backwards
    /// ends a run.
    #[test]
    fn overlapping_writes_are_separate_strings() {
        use crate::emulate::Written;
        let mut hist = Vec::new();
        for (base, text) in [(0x100u64, "mortisengine.com"), (0x100, "/api/auth/login")] {
            for (i, b) in text.bytes().enumerate() {
                hist.push(Written {
                    addr: base + from_usize(i),
                    value: b,
                });
            }
        }
        let runs = super::written_text(&hist, 6);
        assert_eq!(
            runs.iter().map(|(_, t)| t.as_str()).collect::<Vec<_>>(),
            vec!["mortisengine.com", "/api/auth/login"]
        );
    }

    /// A run shorter than the minimum is not reported.
    #[test]
    fn short_written_runs_are_dropped() {
        use crate::emulate::Written;
        let hist: Vec<Written> = "abc"
            .bytes()
            .enumerate()
            .map(|(i, b)| Written {
                addr: 0x200 + from_usize(i),
                value: b,
            })
            .collect();
        assert!(super::written_text(&hist, 6).is_empty());
    }

    /// A dump at the top of memory is clamped, not wrapped to zero.
    ///
    /// Reading past the end of the address space would report bytes from the
    /// bottom of it, and the header's end address would overflow.
    #[test]
    fn a_dump_stops_at_the_end_of_memory() {
        let p = rodata(&[]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let spec = super::ExperimentSpec::parse(&a, &o, "0x1000,dump=0xffffffffffffffff:64")
            .expect("spec parses");
        assert_eq!(spec.dumps, vec![(u64::MAX, 1, 64)]);
    }

    /// A dump length takes hex or decimal, like every other value in a spec.
    ///
    /// `dump=0x3000:0x80` reads 128 bytes; before, only `:128` was accepted
    /// and a hex length was rejected as malformed.
    #[test]
    fn a_dump_length_takes_hex_or_decimal() {
        let p = rodata(&[]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let hex = super::ExperimentSpec::parse(&a, &o, "0x1000,dump=0x3000:0x80")
            .expect("hex length parses");
        let dec = super::ExperimentSpec::parse(&a, &o, "0x1000,dump=0x3000:128")
            .expect("decimal length parses");
        assert_eq!(hex.dumps, vec![(0x3000, 128, 128)]);
        assert_eq!(dec.dumps, hex.dumps);
    }

    /// A dump reads memory as a load reads it.
    ///
    /// The image's bytes where the run wrote none, `??` where nothing is
    /// mapped, and a length past the cap is cut and said to be; it read every
    /// byte the run did not write as `00`, mapped or not, and cut silently.
    #[test]
    fn a_dump_reads_the_image_and_marks_what_is_unmapped() {
        let p = Program::raw_x64(&[0xc3, 0x41, 0x42]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::emulate_tsv(
            &p,
            &a,
            &o,
            "0x1000,dump=0x1000:3,dump=0x50000000:2,dump=0x1000:5000",
        )
        .expect("the run answers");
        assert!(
            out.contains("# dump 0x1000..0x1003\n0x0000001000  c3 41 42 "),
            "{out}"
        );
        assert!(
            out.contains(
                "# dump 0x50000000..0x50000002, ?? where nothing is mapped\n0x0050000000  ?? ?? "
            ),
            "{out}"
        );
        assert!(
            out.contains("# dump 0x1000..0x2000, 4096 of the 5000 bytes asked"),
            "{out}"
        );
    }

    /// Scattered code over enough blocks reads as control-flow obfuscation.
    ///
    /// A function whose span dwarfs its code across several blocks is a VM or a
    /// flattened dispatcher; a contiguous function, or a small scattered stub,
    /// is not flagged. The cases, in order: 425 bytes across 3.8 MB in 16
    /// blocks (the unpacked Themida VM entry); ordinary contiguous code, whose
    /// span is its code; a two-block stub with a far jump, too few blocks to
    /// be sure; and a tight span over many blocks, which is not scattered.
    #[test]
    fn dispersed_control_flow_is_recognized() {
        assert!(super::control_flow_dispersed(425, 0x3a_0f0d, 16));
        assert!(!super::control_flow_dispersed(0x99, 0x99, 15));
        assert!(!super::control_flow_dispersed(0x20, 0x8000, 2));
        assert!(!super::control_flow_dispersed(0x400, 0x800, 20));
    }

    /// A listing in packed code says the bytes are not the real program yet.
    ///
    /// An executable section whose bytes are high-entropy (encrypted on disk)
    /// and one the file backs with no bytes at all (a protector's virtual-only
    /// section) both disassemble to confident garbage; the caveat says so and
    /// points at unpacking, instead of letting the decode stand as code. The
    /// packed section holds all 256 byte values once: entropy 8.0, the shape
    /// of encrypted content.
    #[test]
    fn a_listing_in_packed_code_carries_a_caveat() {
        let bytes: Vec<u8> = (0u8..=255).collect();
        let packed = Section {
            vsize: 0x1000,
            ..Section::mapped(".packed", 0x2000, 0, 256, false, true)
        };
        let themida = Section {
            file_size: 0,
            ..Section::mapped(".themida", 0x3000, 256, 0x1000, false, true)
        };
        let p = Program {
            format: BinaryFormat::Pe,
            ..Program::raw(bytes, Arch::X86_64, 0, None, vec![packed, themida])
        };
        let a = crate::analysis::Analysis::compute(&p);
        let packed = super::listing_caveat(&p, &a, 0x2000);
        assert!(packed.contains("are packed (entropy"), "{packed}");
        assert!(packed.contains("unpack"), "{packed}");
        let virtual_only = super::listing_caveat(&p, &a, 0x3000);
        assert!(
            virtual_only.contains("backs with no bytes"),
            "{virtual_only}"
        );
    }

    /// A register the emulator cannot set stops the run instead of being echoed.
    ///
    /// Reporting `eax=0x5` for a setting that was never applied would answer
    /// a different question than the one asked.
    #[test]
    fn a_misspelled_register_is_refused() {
        let p = rodata(&[]);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::emulate_tsv(&p, &a, &o, "0x2000,eaxx=5").unwrap_err();
        assert!(out.contains("eaxx is not a register"), "{out}");
        assert!(!out.contains("ran "), "the run went ahead anyway: {out}");
    }

    /// A pseudo-C function with every kind of scope the decompiler writes:
    /// a preamble, `if` / `else if` / `else`, `while`, `switch` with a
    /// braced case, a one-line case and a `default` holding a `do` loop.
    const SCOPED: &str = "// f @ 0x1000: 9 instructions, 3 blocks
uint64_t rax;

rax = 0;
if (a1 != 0) {
  rax = 1;
  while (rax < 9) {
    rax += 2;
  }
} else if (a2 == 3) {
  switch (a3) {
  case 1: {
    rax = Foo(a1);
    break;
  }
  case 2: break;
  default: {
    do {
      rax = Bar(rax);
    } while (rax != 0);
    break;
  }
  }
} else {
  rax = Baz();
}
return rax;
";

    /// Every picked line comes with the headers of the scopes enclosing it.
    ///
    /// An `else` comes with the `if` and `else if` before it, a `case` or
    /// `default` with its `switch`, a loop body with its loop. A top-level
    /// line has none, a picked header is not repeated as its own context,
    /// and an index past the end is ignored.
    ///
    /// # Panics
    ///
    /// When a header is missing, a bystander is taken for one, or a picked
    /// line is listed as context.
    #[test]
    fn a_fragment_comes_with_the_headers_enclosing_it() {
        let lines: Vec<&str> = SCOPED.lines().collect();
        let headers = |picked: &[usize]| -> Vec<usize> {
            super::scope_headers(&lines, picked).into_iter().collect()
        };
        assert_eq!(lines[12].trim(), "rax = Foo(a1);");
        assert_eq!(headers(&[12]), vec![4, 9, 10, 11], "case 1 in its switch");
        assert_eq!(
            headers(&[18]),
            vec![4, 9, 10, 16, 17],
            "a do loop in the default"
        );
        assert_eq!(headers(&[15]), vec![4, 9, 10], "a one-line case");
        assert_eq!(headers(&[24]), vec![4, 9, 23], "the last else");
        assert_eq!(headers(&[23]), vec![4, 9], "a picked else brings its if");
        assert_eq!(headers(&[7]), vec![4, 6], "a while body");
        assert!(headers(&[3, 26, 1]).is_empty(), "top level and preamble");
        assert_eq!(headers(&[11, 12]), vec![4, 9, 10], "a picked header");
        assert!(headers(&[99]).is_empty(), "past the end");
    }

    /// A picked line that reads a parameter, or sits under a header that
    /// does, comes with the function's signature, which says what the
    /// parameter is; in the skeleton the signature is the first line.
    ///
    /// A line reading no parameter gets none, a preamble line naming one
    /// gets the signature alone, a picked signature is not its own context,
    /// and nothing picked gets nothing.
    ///
    /// # Panics
    ///
    /// When the signature is missing beside a line, or listed beside none.
    #[test]
    fn a_fragment_comes_with_the_signature_enclosing_it() {
        let full = "// f @ 0x1000: 9 instructions, 3 blocks\n// signature: void f(RakNet::RakNetClient *a1)\n// effects: writes a1+0x24\nuint64_t rax;\n\nif (a1 != 0) {\n  a1->field_0x24 = 9;\n  rax = 1;\n}\nreturn;\n";
        let lines: Vec<&str> = full.lines().collect();
        let headers = |lines: &[&str], picked: &[usize]| -> Vec<usize> {
            super::scope_headers(lines, picked).into_iter().collect()
        };
        assert_eq!(headers(&lines, &[6]), vec![1, 5], "a nested store");
        assert_eq!(
            headers(&lines, &[7]),
            vec![1, 5],
            "under a header reading a1"
        );
        assert!(headers(&lines, &[9]).is_empty(), "a return reading nothing");
        assert_eq!(headers(&lines, &[2]), vec![1], "a preamble line");
        assert!(headers(&lines, &[1]).is_empty(), "the signature picked");
        assert!(headers(&lines, &[]).is_empty(), "nothing picked");
        let skeleton = "// void f(RakNet::RakNetClient *a1) @ 0x1000: 9 instructions, 3 blocks
...
if (a1 != 0) {
  a1->field_0x24 = 9;
}
";
        let lines: Vec<&str> = skeleton.lines().collect();
        assert_eq!(
            headers(&lines, &[3]),
            vec![0, 2],
            "the skeleton's first line"
        );
    }

    /// A string search that misses the table falls back to the generators.
    ///
    /// A protected binary does not store the strings that matter, so a search
    /// that finds nothing in the table has not answered the question yet.
    /// With no generator to run, the fallback changes nothing and the miss is
    /// still a miss.
    #[test]
    fn a_missed_search_reports_no_pairs() {
        let p = rodata(b"stored text here\0");
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::functions_by_string_tsv(&p, &a, &o, "absent", 0, 10);
        assert!(out.contains("0 function/string pairs"), "{out}");
    }

    /// Recovery returns data, and the report is a rendering of it.
    ///
    /// Nothing to recover here, so both halves agree on nothing: what is
    /// asserted is that the data half answers at all, which is what a string
    /// search needs from it.
    #[test]
    fn recovery_answers_with_data() {
        let p = rodata(b"\0");
        let a = crate::analysis::Analysis::compute(&p);
        let recovered = super::generated_strings(&p, &a, "");
        assert!(recovered.found.is_empty());
        assert_eq!((recovered.runs, recovered.generators), (0, 0));
    }

    /// Triage answers on a program with nothing in it, and says so.
    ///
    /// The report is the first call an agent makes, so it has to produce a
    /// usable answer for any input rather than depending on a rich binary.
    #[test]
    fn triage_answers_for_an_empty_program() {
        let p = rodata(b"nothing here\0");
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::triage_tsv(&p, &a, &o);
        assert!(out.starts_with("# triage:"), "{out}");
        assert!(out.contains("# protection:"), "{out}");
        assert!(out.contains("# capabilities:"), "{out}");
        assert!(out.contains("nothing stood out"), "{out}");
        assert!(out.ends_with("runs one\n"), "{out}");
    }

    /// A value passed to a call is reported, and the convention ends it.
    ///
    /// A `call` does not read its arguments as operands, so nothing about the
    /// instruction says a value is being passed; the convention does. And the
    /// same convention lets the callee destroy those registers, so the value
    /// does not survive the call. The bytes at 0x2000 are data in this
    /// fixture, so the pass is exercised through its parser and its refusals,
    /// which is what a caller hits.
    #[test]
    fn taint_follows_a_value_into_a_call() {
        let p = rodata(b"not code\0");
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::taint_tsv(&p, &a, &o, "0x2000,eaxx").unwrap_err();
        assert!(out.contains("not a general register"), "{out}");
        let out = super::taint_tsv(&p, &a, &o, "nowhere").unwrap_err();
        assert!(out.contains("cannot resolve"), "{out}");
        let out = super::taint_tsv(&p, &a, &o, "0x9999").unwrap_err();
        assert!(out.contains("no function contains"), "{out}");
    }

    /// The layout pass refuses what it cannot answer, and answers nothing
    /// for a program with no code.
    #[test]
    fn layout_refuses_what_it_cannot_answer() {
        let p = rodata(b"not code\0");
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        assert!(
            super::layout_tsv(&p, &a, &o, "0x2000,eaxx")
                .unwrap_err()
                .contains("not a general register")
        );
        assert!(
            super::layout_tsv(&p, &a, &o, "nowhere")
                .unwrap_err()
                .contains("cannot resolve")
        );
        assert!(
            super::layout_tsv(&p, &a, &o, "0x9999")
                .unwrap_err()
                .contains("no function contains")
        );
    }

    /// An unnamed address says so, rather than implying a name it has not got.
    ///
    /// The point of the report is the difference between a name the compiler
    /// wrote down and `sub_` plus an address, so the second case has to say
    /// which it is.
    #[test]
    fn why_says_when_nothing_names_an_address() {
        let p = rodata(b"some text here\0");
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::why_tsv(&p, &a, &o, "0x2000").unwrap();
        assert!(out.contains("# name: nothing names it"), "{out}");
        assert!(out.contains("read as a string"), "{out}");
        assert!(
            super::why_tsv(&p, &a, &o, "nowhere")
                .unwrap_err()
                .contains("cannot resolve")
        );
    }

    /// A name the user set is reported as theirs, not as a discovery.
    #[test]
    fn why_credits_a_name_the_user_set() {
        let p = rodata(b"\0");
        let a = crate::analysis::Analysis::compute(&p);
        let mut o = crate::analysis::Overlay::default();
        o.names.insert(0x2000, String::from("session_key"));
        let out = super::why_tsv(&p, &a, &o, "0x2000").unwrap();
        assert!(out.contains("you set it: session_key"), "{out}");
    }

    /// A hand-written `strlen` is identified by what it computes.
    ///
    /// Nothing about these bytes resembles any library build. Running the
    /// function is what names it, which is the point: a signature database
    /// recognizes the builds it was made from, and this recognizes the
    /// behaviour.
    #[test]
    fn a_library_function_is_named_by_running_it() {
        // ASM: xor eax,eax; loop: cmp byte [rcx+rax],0; je done; inc rax;
        // ASM: jmp loop; done: ret
        let code: &[u8] = &[
            0x31, 0xc0, // ASM: xor eax,eax
            0x80, 0x3c, 0x01, 0x00, // ASM: cmp byte [rcx+rax],0
            0x74, 0x05, // ASM: je done (0x100d)
            0x48, 0xff, 0xc0, // ASM: inc rax
            0xeb, 0xf5, // ASM: jmp loop (0x1002)
            0xc3, // ASM: ret
        ];
        let p = text(image(0x2000, &[(0x1000, code)]), 0x1000, false);
        let (what, evidence) = super::identify_behaviour(&p, 0x1000).expect("identified");
        assert_eq!(what, "strlen", "{evidence}");
        assert!(evidence.contains("9, 3 and 0"), "{evidence}");
    }

    /// The value a check wants is found among the constants it compares to.
    ///
    /// The search is over the function's own constants rather than over
    /// every 64-bit number, which is what makes it finish, and the runs are
    /// what prove which constant works. The accepting value stands alone, and
    /// it is reported first because a check accepts few inputs and rejects
    /// the rest.
    #[test]
    fn the_value_a_check_wants_is_found() {
        // ASM: xor eax,eax; cmp ecx,0x1337; jne done; mov eax,1; done: ret
        let code: &[u8] = &[
            0x31, 0xc0, // ASM: xor eax,eax
            0x81, 0xf9, 0x37, 0x13, 0x00, 0x00, // ASM: cmp ecx,0x1337
            0x75, 0x05, // ASM: jne done
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
            0xc3, // ASM: ret
        ];
        let p = text(image(0x2000, &[(0x1000, code)]), 0x1000, false);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::solve_tsv(&p, &a, &o, "0x1000").unwrap();
        let lines: Vec<&str> = out.lines().collect();
        assert!(lines.len() >= 3, "{out}");
        assert!(lines[1].contains("returns 0x1"), "{out}");
        assert!(lines[1].contains("0x1337"), "{out}");
        assert!(lines[2].contains("returns 0x0"), "{out}");
    }

    /// A program with no dispatcher says so rather than guessing at one.
    ///
    /// The test that separates a flattening dispatcher from an ordinary
    /// switch is that most of its cases come back to it, and a binary with
    /// neither has to report neither.
    #[test]
    fn nothing_is_flattened_without_a_returning_switch() {
        let p = rodata(b"no code here\0");
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::flattening_tsv(&p, &a, &o, "").unwrap();
        assert!(out.contains("no flattened control flow"), "{out}");
        let one = super::flattening_tsv(&p, &a, &o, "0x2000").unwrap_err();
        assert!(one.contains("no flattening dispatch"), "{one}");
    }

    /// Unpacking finds a function that only exists after the run.
    ///
    /// The decryptor and the encrypted payload are both in the file, so
    /// discovery over the file sees the decryptor and garbage. Running it and
    /// analyzing what it wrote is what finds the payload, which is the whole
    /// claim of the unpacking path. The payload is `mov eax,7; ret` with each
    /// byte exclusive-ored with the key.
    #[test]
    fn unpacking_finds_the_payload() {
        // ASM: at 0x1000, mov rcx,0x1800; mov rdx,6; loop: xor byte [rcx],0x5a;
        // ASM: inc rcx; dec rdx; jnz loop; jmp 0x1800
        let boot: &[u8] = &[
            0x48, 0xc7, 0xc1, 0x00, 0x18, 0x00, 0x00, // ASM: mov rcx,0x1800
            0x48, 0xc7, 0xc2, 0x06, 0x00, 0x00, 0x00, // ASM: mov rdx,6
            0x80, 0x31, 0x5a, // ASM: xor byte [rcx],0x5a
            0x48, 0xff, 0xc1, // ASM: inc rcx
            0x48, 0xff, 0xca, // ASM: dec rdx
            0x75, 0xf5, // ASM: jnz loop
            0xe9, 0xe2, 0x07, 0x00, 0x00, // ASM: jmp 0x1800
        ];
        let payload: Vec<u8> = [0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3]
            .iter()
            .map(|b| b ^ 0x5a)
            .collect();
        let bytes = image(0x2000, &[(0x1000, boot), (0x1800, &payload)]);
        let p = text(bytes, 0x1000, true);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::unpack_tsv(&p, &a, &o, "0x1000").unwrap();
        assert!(
            out.contains("original entry point"),
            "the decrypted code was never executed:\n{out}"
        );
        assert!(out.contains("0x1800"), "{out}");
        assert!(
            out.contains("re-analyzed the materialized image"),
            "the image was not rebuilt:\n{out}"
        );
        assert!(
            out.contains("only the materialized image has"),
            "the payload was not found:\n{out}"
        );
    }

    /// A name follows its function when an update moves it.
    ///
    /// This is the whole claim of carrying names: the addresses change and
    /// the fingerprints do not, so the pairing the diff uses to find real
    /// changes is what carries a name across a build.
    #[test]
    fn a_name_follows_its_function_to_a_new_address() {
        // ASM: mov eax,7; ret -- the same function, at two addresses.
        let body: &[u8] = &[0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3];
        let build = |at: usize| text(image(0x2000, &[(at, body)]), from_usize(at), false);
        let old = build(0x1000);
        let new = build(0x1400);
        let old_a = crate::analysis::Analysis::compute(&old);
        let new_a = crate::analysis::Analysis::compute(&new);
        let mut old_o = crate::analysis::Overlay::default();
        old_o.names.insert(0x1000, String::from("answer"));
        let out =
            super::carry_names_tsv(&old_a, &old_o, &new_a, &crate::analysis::Overlay::default());
        assert!(out.contains("1 of 1 name(s) carry"), "{out}");
        assert!(out.contains("0x1400"), "the new address is wrong:\n{out}");
        assert!(out.contains("answer"), "{out}");
        assert!(out.contains("the same body"), "{out}");
    }

    /// A handler's work names the virtual operation it implements.
    ///
    /// A trace of handler addresses says three handlers ran; a trace of
    /// operations says what the original program did, which is the point of
    /// devirtualizing at all. A compare outranks arithmetic, because a
    /// handler that compares and adds is deciding a branch, not computing a
    /// value.
    #[test]
    fn a_handler_is_named_by_what_it_does() {
        for (ops, memory, want) in [
            (vec!["add"], false, "virtual arithmetic"),
            (vec!["sub", "adc"], true, "virtual arithmetic"),
            (vec!["xor"], false, "virtual logic"),
            (vec!["shl"], false, "a virtual shift or rotate"),
            (vec!["cmp"], false, "a virtual compare or branch"),
            (vec!["call"], true, "calls out of the machine"),
            (vec![], true, "a virtual load or store"),
            (vec![], false, "a virtual register move"),
            (vec!["cpuid"], false, "an operation this does not classify"),
        ] {
            assert_eq!(super::virtual_op(&ops, memory), want, "{ops:?}");
        }
        assert_eq!(
            super::virtual_op(&["add", "cmp"], false),
            "a virtual compare or branch"
        );
    }

    /// Running a flattened function recovers the order its blocks run in.
    ///
    /// Flattening keeps the program counter in a variable, so the order
    /// cannot be read off the code. Watching the dispatch is what recovers
    /// it: every trip through is one original block. The fixture is a
    /// dispatcher over a four-entry table at 0x2000 (case 0 unused, then the
    /// three case blocks); the state starts at 2, and each case sets the next
    /// state and jumps back, so the order is 2, 1, 3 and then the exit.
    #[test]
    fn running_a_flattened_function_recovers_its_order() {
        // ASM: at 0x1000, mov eax,2
        // ASM: loop (0x1005): cmp eax,4; jae out; jmp [0x2000+rax*8]
        // ASM: case1 (0x1016): mov eax,3; jmp loop
        // ASM: case2 (0x101d): mov eax,1; jmp loop
        // ASM: case3 (0x1024): mov eax,4; jmp loop
        // ASM: out   (0x102b): ret
        let table: Vec<u8> = [0x102bu64, 0x1016, 0x101d, 0x1024]
            .iter()
            .flat_map(|t| t.to_le_bytes())
            .collect();
        let runs: &[(usize, &[u8])] = &[
            (0x1000, &[0xb8, 0x02, 0x00, 0x00, 0x00]), // ASM: mov eax,2
            (0x1005, &[0x83, 0xf8, 0x04]),             // ASM: cmp eax,4
            (0x1008, &[0x73, 0x21]),                   // ASM: jae 0x102b
            (0x100a, &[0xff, 0x24, 0xc5, 0x00, 0x20, 0x00, 0x00]), // ASM: jmp [0x2000+rax*8]
            (0x1016, &[0xb8, 0x03, 0x00, 0x00, 0x00, 0xeb, 0xe8]), // ASM: mov eax,3; jmp 0x1005
            (0x101d, &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xeb, 0xe1]), // ASM: mov eax,1; jmp 0x1005
            (0x1024, &[0xb8, 0x04, 0x00, 0x00, 0x00, 0xeb, 0xda]), // ASM: mov eax,4; jmp 0x1005
            (0x102b, &[0xc3]),                         // ASM: ret
            (0x2000, &table),
        ];
        let sections = vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ];
        let p = Program::raw(image(0x3000, runs), Arch::X86_64, 0, Some(0x1000), sections);
        let order = super::dispatch_order(&p, 0x1000, 0x100a).expect("emulated");
        assert_eq!(
            order.0,
            vec![0x101d, 0x1016, 0x1024],
            "the recovered order is wrong ({}), ",
            order.1
        );
    }

    /// A reference into the middle of a literal resolves to the literal.
    ///
    /// Chunked comparisons reference a long string at `+0x10` and `+0x20`.
    /// Reading forward from there reports a string cut mid-word that is not
    /// in the binary as a string of its own.
    #[test]
    fn an_interior_reference_resolves_to_its_string() {
        let p = rodata(b"Invalid server response\0");
        assert_eq!(
            string_literal(&p, 0x2000, 120),
            Some((0x2000, String::from("\"Invalid server response\"")))
        );
        assert_eq!(
            string_literal(&p, 0x2010, 120),
            Some((0x2000, String::from("\"Invalid server response\"")))
        );
    }

    /// Binary data ending in printable bytes does not become a literal.
    ///
    /// The walk back to a string's first byte must not run from bytes that
    /// were never a string, or an SSE constant whose tail reads as text is
    /// reported as one.
    #[test]
    fn binary_data_does_not_become_a_literal() {
        let mut data = vec![0u8; 16];
        data.extend_from_slice(b"abc");
        data.extend_from_slice(&[0xff, 0x00]);
        let p = rodata(&data);
        assert_eq!(string_literal(&p, 0x2013, 120), None);
    }

    /// The generators run once per analysis, however many reports ask.
    ///
    /// `why` reads the recovery for every address it explains and `triage`
    /// for the whole program; running every generator in the emulator per
    /// question made each of them pay the costliest read in the engine
    /// again. The second `why` answers the same as the first, and all three
    /// reports share one recovery.
    #[test]
    fn generators_run_once_per_analysis() {
        let p = rodata(b"some text here\0");
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let first = super::why_tsv(&p, &a, &o, "0x2000").unwrap();
        let again = super::why_tsv(&p, &a, &o, "0x2000").unwrap();
        let _ = super::triage_tsv(&p, &a, &o);
        assert_eq!(first, again);
        assert_eq!(a.derived.held("generated_strings"), 1);
    }

    /// The hidden-strings report and the string search read the stored
    /// recovery whatever their filter, and answer as a run for that filter.
    #[test]
    fn hidden_strings_share_the_stored_recovery() {
        let p = rodata(b"some text here\0");
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let all = super::hidden_strings_tsv(&p, &a, &o, "");
        let some = super::hidden_strings_tsv(&p, &a, &o, "text");
        let _ = super::functions_by_string_tsv(&p, &a, &o, "absent", 0, 10);
        assert_eq!(a.derived.held("generated_strings"), 1);
        let direct = super::generated_strings(&p, &a, "text");
        let (found, _, runs, generators) = super::hidden_strings(&p, &a, "text");
        assert_eq!(
            (found.len(), runs, generators),
            (direct.found.len(), direct.runs, direct.generators)
        );
        assert!(all.starts_with('#') && some.starts_with('#'), "{all}{some}");
    }

    /// A store the second pass sees again is reported once.
    ///
    /// The taint pass walks the function twice so a loop's back edge is
    /// followed; the store at 0x1001 is met on both passes and is one place
    /// the value went, not two.
    #[test]
    fn taint_reports_a_store_once_across_passes() {
        let code: &[u8] = &[
            0x90, // ASM: nop
            0x48, 0x89, 0x01, // ASM: mov [rcx],rax
            0xc3, // ASM: ret
        ];
        let p = text(image(0x2000, &[(0x1000, code)]), 0x1000, false);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        let out = super::taint_tsv(&p, &a, &o, "0x1000,rax").unwrap();
        assert_eq!(out.matches("stored by").count(), 1, "{out}");
        assert!(out.contains("0x1001"), "{out}");
    }

    /// A check's constants are listed once each, in the order first tested.
    ///
    /// The count orders the license-check table, so a constant compared
    /// twice must count once, and the first comparison fixes its place.
    #[test]
    fn check_constants_are_distinct_in_first_seen_order() {
        let code: &[u8] = &[
            0x3d, 0x2b, 0x4a, 0x00, 0x00, // ASM: cmp eax,0x4a2b
            0x3d, 0x37, 0x13, 0x00, 0x00, // ASM: cmp eax,0x1337
            0x3d, 0x2b, 0x4a, 0x00, 0x00, // ASM: cmp eax,0x4a2b
            0xc3, // ASM: ret
        ];
        let p = text(image(0x2000, &[(0x1000, code)]), 0x1000, false);
        let a = crate::analysis::Analysis::compute(&p);
        assert_eq!(
            super::check_constants(&p, &a, 0x1000, 64),
            vec![0x4a2b, 0x1337]
        );
    }
}
