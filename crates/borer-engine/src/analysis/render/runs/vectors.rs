//! Generated test vectors: inputs drawn for a function, each run in the
//! emulator and checked against its text, and the C harness that replays
//! them.

use super::{
    Arg, BUDGET, BUDGET_MAX, INPUTS_MAX, Outcome, Shared, Verdict, args_shown, run_one, small_hex,
    writes_shown,
};
use crate::analysis::decompile::interp::{Mode, Script};
use crate::analysis::decompile::signature::{Kind, Passing, Signature, passing, printed};
use crate::analysis::decompile::{Pass, Passes, decompile_named};
use crate::analysis::render::oracle::compared_constants;
use crate::analysis::render::*;
use crate::text::one_line;

/// The seed the lifter's check runs from when a run differs, fixed so the
/// report is the same every time.
pub(super) const VERIFY_SEED: u64 = 1;

/// The values a generated integer argument is drawn from besides random
/// ones: the edges a check compares against.
const EDGES: [u64; 12] = [
    0,
    1,
    2,
    7,
    0x10,
    0x7f,
    0x80,
    0xff,
    0x7fff_ffff,
    0x8000_0000,
    0xffff_ffff,
    u64::MAX,
];

/// Bytes a generated buffer argument holds.
const GENERATED_BUFFER: usize = 64;

/// Longest text a generated buffer argument holds before its zeros.
const GENERATED_TEXT: u64 = 40;

/// The characters a generated text is spelled with.
const GENERATED_CHARS: &[u8] = b"abcdefghijklmnopqrstuvwxyz0123456789 ,.-_/";

/// A value cut to a parameter's width and extended as its sign says.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The parameter's width, 1 to 64.
/// * `signed` - Whether the parameter is signed.
pub(super) fn cut(v: u64, bits: u8, signed: bool) -> u64 {
    let shift = 64 - u32::from(bits.clamp(1, 64));
    if signed {
        ((v << shift).cast_signed() >> shift).cast_unsigned()
    } else {
        (v << shift) >> shift
    }
}

/// Inputs generated for a function from the kinds of its parameters.
///
/// Each input is a pure function of the seed, the function's entry and the
/// input's position: an integer is an edge value, a small number, a small
/// negative one or a random word, cut to the parameter's width and extended
/// as its sign says; a pointer is a buffer of [`GENERATED_BUFFER`] bytes
/// holding a short text, random bytes, or zeros.
///
/// # Arguments
///
/// * `kinds` - The parameters' kinds, in order.
/// * `count` - How many inputs.
/// * `seed` - The seed.
/// * `entry` - The function's entry, stirred into the seed.
///
/// # Errors
///
/// When a parameter is floating, or of a type a run does not pass.
pub(super) fn generated(
    kinds: &[Kind],
    count: usize,
    seed: u64,
    entry: u64,
) -> Result<Vec<Vec<Arg>>, String> {
    /// Stirs the seed, as `splitmix64` does.
    const GOLDEN: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut out = Vec::with_capacity(count);
    for j in 0..count {
        let mut state = seed ^ entry.wrapping_mul(GOLDEN) ^ from_usize(j).wrapping_mul(GOLDEN << 1);
        let mut next = move || {
            state = state.wrapping_add(GOLDEN);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        let mut input = Vec::with_capacity(kinds.len());
        for (k, kind) in kinds.iter().enumerate() {
            input.push(match *kind {
                Kind::Int(bits, signed) => {
                    let v = match next() % 4 {
                        0 => EDGES
                            .get(usize::try_from(next() % from_usize(EDGES.len())).unwrap_or(0))
                            .copied()
                            .unwrap_or(0),
                        1 => next() % 16,
                        2 => (next() % 16).wrapping_neg(),
                        _ => next(),
                    };
                    Arg::Int(cut(v, bits, signed))
                }
                Kind::Pointer => match next() % 3 {
                    0 => {
                        let mut b = vec![0u8; GENERATED_BUFFER];
                        for slot in b
                            .iter_mut()
                            .take(usize::try_from(next() % GENERATED_TEXT).unwrap_or(0))
                        {
                            let c = usize::try_from(next() % from_usize(GENERATED_CHARS.len()))
                                .unwrap_or(0);
                            *slot = GENERATED_CHARS.get(c).copied().unwrap_or(b'a');
                        }
                        Arg::Bytes(b)
                    }
                    1 => Arg::Bytes(
                        (0..GENERATED_BUFFER)
                            .map(|_| crate::num::lo8(next()))
                            .collect(),
                    ),
                    _ => Arg::Out(GENERATED_BUFFER),
                },
                Kind::Float => {
                    return Err(format!("a{} is floating, which a run does not pass", k + 1));
                }
                Kind::Other => {
                    return Err(format!("a{} is of a type a run does not pass", k + 1));
                }
            });
        }
        out.push(input);
    }
    Ok(out)
}

/// Checks a function's printed text against the binary on inputs generated
/// from its signature.
///
/// The text the tools print ([`decompile_named`]) runs as C on each input
/// beside the binary in the emulator, as [`run_tsv`] runs them, from inputs
/// that are a pure function of `seed` and the function ([`generated`]):
/// the same call answers the same.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `entry` - The function's entry.
/// * `count` - How many inputs.
/// * `seed` - The inputs' seed.
/// * `budget` - Steps each run is given, on either side.
///
/// # Returns
///
/// Each input's arguments as a report row spells them, with the text's
/// verdict on it.
///
/// # Errors
///
/// When the function does not decompile, its signature does not read, or a
/// parameter is of a type a run does not pass.
pub fn check_generated(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    count: usize,
    seed: u64,
    budget: usize,
) -> Result<Vec<(String, Verdict)>, String> {
    generated_in(p, a, o, entry, (count, seed, budget), Mode::Machine)
}

/// Checks a function's printed text, read as ISO C, against the binary on
/// inputs generated from its signature.
///
/// As [`check_generated`], with the text run in ISO mode ([`Mode::Iso`]):
/// each local is an object of its own, and a read of a variable or a
/// local's byte no line set, or of a name the text never declares, is a
/// difference at that line. Nothing gates on it yet; it measures how often
/// the text is the C it claims to be.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `entry` - The function's entry.
/// * `count` - How many inputs.
/// * `seed` - The inputs' seed.
/// * `budget` - Steps each run is given, on either side.
///
/// # Returns
///
/// Each input's arguments as a report row spells them, with the verdict of
/// the ISO run on it.
///
/// # Errors
///
/// As [`check_generated`].
pub fn check_generated_iso(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    count: usize,
    seed: u64,
    budget: usize,
) -> Result<Vec<(String, Verdict)>, String> {
    generated_in(p, a, o, entry, (count, seed, budget), Mode::Iso)
}

/// [`check_generated`] with the text read in one [`Mode`].
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `entry` - The function's entry.
/// * `(count, seed, budget)` - How many inputs, their seed, and the steps
///   each run is given.
/// * `mode` - How the text is read.
///
/// # Errors
///
/// As [`check_generated`].
fn generated_in(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    (count, seed, budget): (usize, u64, usize),
    mode: Mode,
) -> Result<Vec<(String, Verdict)>, String> {
    let text = decompile_named(p, a, o, entry).ok_or("the function does not decompile")?;
    let word = u8::try_from(p.arch.bitness().unwrap_or(64)).unwrap_or(64);
    let sig = printed(&text, word)?;
    let inputs = generated(&sig.parameter_kinds(), count, seed, entry)?;
    let script = match mode {
        Mode::Machine => Script::read(p, a, o, entry, &text),
        Mode::Iso => Script::read_iso(p, a, o, entry, &text),
    };
    let shared = Shared {
        script,
        sig: Ok(sig),
        pass: Some(passing(p, a, o, entry)),
    };
    Ok(inputs
        .iter()
        .map(|input| {
            let shown: Vec<String> = input.iter().map(Arg::shown).collect();
            let outcome = run_one(p, a, &shared, entry, input, budget);
            (shown.join(" "), outcome.verdict)
        })
        .collect())
}

/// Where a bisection of a function's text passes under the ISO check
/// ([`bisect_iso`]) found the text to break.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bisected {
    /// No input differs on the full text: nothing to bisect.
    Agrees,
    /// The text with every pass left out differs already: what the passes
    /// were handed was wrong, so no pass broke it.
    Unbisected(Counterexample),
    /// The text with the passes before `pass` agrees and the text with
    /// `pass` too differs.
    Broke {
        /// The first pass whose text differs.
        pass: Pass,
        /// The input it differs on, and where.
        at: Counterexample,
        /// Whether the full pipeline with only this pass left out agrees,
        /// so leaving it out alone repairs the function.
        alone: bool,
        /// The text with the passes before `pass`, and with `pass` too.
        texts: (String, String),
    },
}

/// One input a text differs on, and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Counterexample {
    /// The input's arguments, as a report row spells them.
    pub input: String,
    /// The line of the text that differs, trimmed; empty when not known.
    pub line: String,
    /// What differs there.
    pub why: String,
}

/// Finds the first text pass that breaks a function under the ISO check.
///
/// The inputs are drawn once, from the signature the full text prints, as
/// [`check_generated_iso`] draws them, and every text below is run on the
/// same ones beside the binary. When the full text differs on one, the
/// passes of [`Pass::ALL`] are bisected: the text built with only the
/// first `k` of them ([`Passes::after`]) is checked for each `k` a binary
/// search asks for, from none (which must agree, or no pass is to blame)
/// to all. A text that does not read, or an input it leaves unchecked,
/// counts as agreeing: the bisection looks for a difference, not for a
/// claim.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names; its own [`Overlay::passes`] are replaced.
/// * `entry` - The function's entry.
/// * `count` - How many inputs.
/// * `seed` - The inputs' seed.
/// * `budget` - Steps each run is given, on either side.
///
/// # Returns
///
/// Where the text broke ([`Bisected`]).
///
/// # Errors
///
/// As [`check_generated`].
pub fn bisect_iso(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    count: usize,
    seed: u64,
    budget: usize,
) -> Result<Bisected, String> {
    let full = Overlay {
        passes: Passes::NONE,
        ..o.clone()
    };
    let drawn = draw(p, a, &full, entry, count, seed)?;
    let differs = |skip: Passes| -> Option<Counterexample> {
        let under = Overlay {
            passes: skip,
            ..full.clone()
        };
        first_difference(p, a, &under, entry, &drawn, budget).differs
    };
    let Some(mut at) = differs(Passes::NONE) else {
        return Ok(Bisected::Agrees);
    };
    if let Some(before) = differs(Passes::after(0)) {
        return Ok(Bisected::Unbisected(before));
    }
    let (good, bad, c) = first_breaking(&differs);
    if let Some(c) = c {
        at = c;
    }
    let Some(&pass) = Pass::ALL.get(good) else {
        return Ok(Bisected::Unbisected(at));
    };
    let alone = differs(Passes::NONE.without(pass)).is_none();
    let text_of = |k: usize| {
        let under = Overlay {
            passes: Passes::after(k),
            ..full.clone()
        };
        decompile_named(p, a, &under, entry).unwrap_or_default()
    };
    Ok(Bisected::Broke {
        pass,
        at,
        alone,
        texts: (text_of(good), text_of(bad)),
    })
}

/// Bisects [`Pass::ALL`] for the first pass whose text differs, given that
/// the text with none of them agrees and the text with all of them does
/// not.
///
/// # Arguments
///
/// * `differs` - Checks the text built without a set of passes: the input
///   it differs on, or `None` when it agrees.
///
/// # Returns
///
/// How many passes run in the last text that agreed and in the first that
/// differed, and the counterexample of the narrowest text that differed,
/// `None` when the bisection probed none.
pub(super) fn first_breaking(
    differs: &impl Fn(Passes) -> Option<Counterexample>,
) -> (usize, usize, Option<Counterexample>) {
    let (mut good, mut bad, mut at) = (0, Pass::ALL.len(), None);
    while bad - good > 1 {
        let mid = good + (bad - good) / 2;
        match differs(Passes::after(mid)) {
            Some(c) => {
                bad = mid;
                at = Some(c);
            }
            None => good = mid,
        }
    }
    (good, bad, at)
}

/// The inputs a function's texts are checked on, drawn once from the
/// signature one of them prints, with the convention the binary is called
/// by.
#[derive(Debug, Clone)]
pub(super) struct Drawn {
    /// The signature the inputs were drawn from.
    sig: Signature,
    /// The inputs.
    inputs: Vec<Vec<Arg>>,
    /// How the binary takes its arguments.
    pass: Passing,
}

/// Draws the inputs a function's texts are checked on, as
/// [`check_generated_iso`] draws them.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - The overlay whose text's signature types the inputs.
/// * `entry` - The function's entry.
/// * `count` - How many inputs.
/// * `seed` - The inputs' seed.
///
/// # Returns
///
/// The inputs, the signature and the convention.
///
/// # Errors
///
/// As [`check_generated`].
pub(super) fn draw(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    count: usize,
    seed: u64,
) -> Result<Drawn, String> {
    let text = decompile_named(p, a, o, entry).ok_or("the function does not decompile")?;
    let word = u8::try_from(p.arch.bitness().unwrap_or(64)).unwrap_or(64);
    let sig = printed(&text, word)?;
    let inputs = generated(&sig.parameter_kinds(), count, seed, entry)?;
    Ok(Drawn {
        sig,
        inputs,
        pass: passing(p, a, o, entry),
    })
}

/// What one text did on drawn inputs under the ISO check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Checked {
    /// The first input the text differs on, and where; `None` when none.
    pub(super) differs: Option<Counterexample>,
    /// Inputs the text agreed on before it differed, or in all.
    pub(super) agreed: usize,
}

/// Runs a function's text, read as ISO C, beside the binary on drawn
/// inputs, until the first input it differs on.
///
/// A text that does not decompile or read, or an input it leaves
/// unchecked, differs on nothing: the check looks for a difference, not
/// for a claim.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `u` - The overlay the text is built under.
/// * `entry` - The function's entry.
/// * `drawn` - The inputs.
/// * `budget` - Steps each run is given, on either side.
///
/// # Returns
///
/// The first difference and how many inputs agreed.
pub(super) fn first_difference(
    p: &Program,
    a: &Analysis,
    u: &Overlay,
    entry: u64,
    drawn: &Drawn,
    budget: usize,
) -> Checked {
    let mut out = Checked {
        differs: None,
        agreed: 0,
    };
    let Some(text) = decompile_named(p, a, u, entry) else {
        return out;
    };
    let shared = Shared {
        script: Script::read_iso(p, a, u, entry, &text),
        sig: Ok(drawn.sig.clone()),
        pass: Some(drawn.pass.clone()),
    };
    for input in &drawn.inputs {
        match run_one(p, a, &shared, entry, input, budget).verdict {
            Verdict::Differs(line, why) => {
                out.differs = Some(Counterexample {
                    input: input.iter().map(Arg::shown).collect::<Vec<_>>().join(" "),
                    line: line
                        .checked_sub(1)
                        .and_then(|k| text.lines().nth(k))
                        .map_or_else(String::new, |l| l.trim().to_owned()),
                    why,
                });
                return out;
            }
            Verdict::Agrees => out.agreed += 1,
            Verdict::Unchecked(..) => {}
        }
    }
    out
}

/// Inputs a vector request runs unless its spec says how many.
pub(super) const VECTORS: usize = 16;

/// The seed a vector request's generated inputs are drawn from, fixed so
/// the same request answers the same.
const VECTORS_SEED: u64 = 0x7e57_7ec7;

/// Vectors the harness asserts before the rest are left to the table.
const HARNESS_MAX: usize = 16;

/// The inputs of a vector request, each input once.
///
/// One per constant the function compares against, then inputs generated
/// from its signature ([`generated`]); twice as many are generated as are
/// needed, so a repeat dropped does not cut the count. A constant fills every integer parameter, cut to its width, and every
/// pointer parameter as a [`GENERATED_BUFFER`]-byte buffer opening with the
/// constant's little-endian bytes, so a check of a buffer's first word sees
/// the value it compares with. The constants take at most half the inputs.
///
/// # Arguments
///
/// * `kinds` - The parameters' kinds, in order.
/// * `constants` - The values the function compares against, in order.
/// * `count` - How many inputs.
/// * `entry` - The function's entry, which stirs the generated inputs.
///
/// # Errors
///
/// When a parameter is floating, or of a type a run does not pass.
pub(super) fn vector_inputs(
    kinds: &[Kind],
    constants: &[u64],
    count: usize,
    entry: u64,
) -> Result<Vec<Vec<Arg>>, String> {
    let mut out: Vec<Vec<Arg>> = Vec::with_capacity(count);
    for &c in constants.iter().take(count.div_ceil(2)) {
        let mut input = Vec::with_capacity(kinds.len());
        for (k, kind) in kinds.iter().enumerate() {
            input.push(match *kind {
                Kind::Int(bits, signed) => Arg::Int(cut(c, bits, signed)),
                Kind::Pointer => {
                    let mut b = c.to_le_bytes().to_vec();
                    b.resize(GENERATED_BUFFER, 0);
                    Arg::Bytes(b)
                }
                Kind::Float => {
                    return Err(format!("a{} is floating, which a run does not pass", k + 1));
                }
                Kind::Other => {
                    return Err(format!("a{} is of a type a run does not pass", k + 1));
                }
            });
        }
        if !out.contains(&input) {
            out.push(input);
        }
    }
    for input in generated(kinds, count.saturating_mul(2), VECTORS_SEED, entry)? {
        if out.len() >= count {
            break;
        }
        if !out.contains(&input) {
            out.push(input);
        }
    }
    Ok(out)
}

/// The C type a harness declares a parameter or result of a kind as.
///
/// # Arguments
///
/// * `kind` - The kind.
fn c_type(kind: Kind) -> String {
    match kind {
        Kind::Int(bits, signed) => format!(
            "{}int{}_t",
            if signed { "" } else { "u" },
            bits.clamp(8, 64).next_power_of_two()
        ),
        Kind::Pointer => "uint8_t *".to_owned(),
        Kind::Float => "double".to_owned(),
        Kind::Other => "uint64_t".to_owned(),
    }
}

/// A function's name as a C identifier: its last `::` segment, every
/// character that cannot be in one made `_`.
///
/// # Arguments
///
/// * `name` - The name.
pub(super) fn c_name(name: &str) -> String {
    let mut out: String = name
        .rsplit("::")
        .next()
        .unwrap_or(name)
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    if out.is_empty() || out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

/// Bytes as a C array initializer, its trailing zeros left to the array's
/// size.
///
/// # Arguments
///
/// * `b` - The bytes.
fn c_bytes(b: &[u8]) -> String {
    let end = b.iter().rposition(|c| *c != 0).map_or(0, |i| i + 1);
    let body: Vec<String> = b
        .get(..end)
        .unwrap_or(b)
        .iter()
        .map(|c| format!("{c:#04x}"))
        .collect();
    if body.is_empty() {
        "{0}".to_owned()
    } else {
        format!("{{{}}}", body.join(", "))
    }
}

/// The C a harness opens with after its header comment: the includes, the
/// failure count and the two helpers each vector's line reports through.
const HARNESS_HEAD: &str = "#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int failed;

/* Reports a vector whose result differs. */
static void differs(int vector, unsigned long long got, unsigned long long want) {
    printf(\"vector %d: returned %#llx, want %#llx\\n\", vector, got, want);
    failed++;
}

/* Reports a vector that left other bytes in a buffer. */
static void changed(int vector, int arg) {
    printf(\"vector %d: a%d holds other bytes\\n\", vector, arg);
    failed++;
}
";

/// Writes a C program asserting the vectors that returned, a line each:
/// the call's result at its declared width and the bytes it left in each
/// buffer it changed.
///
/// # Arguments
///
/// * `name` - The function's name, as a C identifier.
/// * `sig` - Its signature.
/// * `inputs` - Every input, in table order.
/// * `outcomes` - Each input's run.
pub(super) fn harness(
    name: &str,
    sig: &Signature,
    inputs: &[Vec<Arg>],
    outcomes: &[Arc<Outcome>],
) -> String {
    let kinds = sig.parameter_kinds();
    let ret = sig.return_kind();
    let params: Vec<String> = kinds
        .iter()
        .enumerate()
        .map(|(k, kind)| match kind {
            Kind::Pointer => format!("uint8_t *a{}", k + 1),
            Kind::Int(..) | Kind::Float | Kind::Other => format!("{} a{}", c_type(*kind), k + 1),
        })
        .collect();
    let params = if params.is_empty() {
        "void".to_owned()
    } else {
        params.join(", ")
    };
    let (ret_type, got) = match ret {
        None => ("void".to_owned(), None),
        Some((Kind::Int(bits, signed), _)) => (
            c_type(Kind::Int(bits, signed)),
            Some(if signed {
                format!("({})got", c_type(Kind::Int(bits, false)))
            } else {
                "got".to_owned()
            }),
        ),
        Some((kind @ (Kind::Pointer | Kind::Float | Kind::Other), _)) => (c_type(kind), None),
    };
    let returned: Vec<usize> = (0..outcomes.len())
        .filter(|&n| outcomes.get(n).is_some_and(|x| x.value.is_some()))
        .collect();
    let mut out = format!(
        "/* {} of the {} vectors that returned, for {}, as borer's emulator ran the binary.\n   Link with a reimplementation of {name}: the run prints each vector that differs and exits 1 if any did. */\n{HARNESS_HEAD}\n{ret_type} {name}({params});\n\nint main(void) {{\n",
        returned.len().min(HARNESS_MAX),
        returned.len(),
        sig.text
    );
    if got.is_none() && ret.is_some() {
        out.push_str("    /* the result is not an integer, so only the buffers are compared */\n");
    }
    for &n in returned.iter().take(HARNESS_MAX) {
        let (Some(input), Some(x)) = (inputs.get(n), outcomes.get(n)) else {
            continue;
        };
        let vector = n + 1;
        let mut line = String::from("    {");
        let mut args = Vec::with_capacity(input.len());
        for (k, arg) in input.iter().enumerate() {
            match arg {
                Arg::Int(v) => args.push(format!("{v:#x}")),
                Arg::Bytes(_) | Arg::Out(_) => {
                    let initial = arg.initial();
                    let _ = write!(
                        line,
                        " uint8_t b{}[{}] = {};",
                        k + 1,
                        initial.len().max(1),
                        c_bytes(&initial)
                    );
                    args.push(format!("b{}", k + 1));
                }
            }
        }
        let call = format!("{name}({})", args.join(", "));
        match (&got, x.value) {
            (Some(got), Some(v)) => {
                let _ = write!(
                    line,
                    " {ret_type} got = {call}; if ({got} != {v:#x}) differs({vector}, {got}, {v:#x});"
                );
            }
            (Some(_) | None, _) => {
                let _ = write!(line, " {call};");
            }
        }
        for (k, after, _) in &x.writes {
            let _ = write!(
                line,
                " static const uint8_t w{0}[{1}] = {2}; if (memcmp(b{0}, w{0}, sizeof w{0})) changed({vector}, {0});",
                k + 1,
                after.len().max(1),
                c_bytes(after)
            );
        }
        line.push_str(" }\n");
        out.push_str(&line);
    }
    out.push_str("    printf(\"%d vectors differ\\n\", failed);\n    return failed != 0;\n}\n");
    out
}

/// Records test vectors for reimplementing a function: inputs typed by
/// its recovered signature, each run in the emulator, and a C harness that
/// asserts what the binary answered.
///
/// The inputs open with the constants the function compares against (the
/// values `solve` tries, [`compared_constants`]), then ones generated from
/// the signature ([`generated`]), each a pure function of the function and
/// a fixed seed, so the same request answers the same, byte for byte. Each
/// runs as [`run_tsv`] runs it, through the same memo. The table gives a
/// row per input; the harness asserts the first [`HARNESS_MAX`] that
/// returned: the result at its declared width, and the bytes each changed
/// buffer holds after.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - `<function>[,count=N][,steps=N]`: at most [`INPUTS_MAX`]
///   inputs, [`VECTORS`] by default.
///
/// # Returns
///
/// A header with the signature and the counts, the table, then the
/// harness under a `# harness` line.
///
/// # Errors
///
/// When the spec does not read, the function does not decompile or has no
/// signature, a parameter is of a type a run does not pass, or the code is
/// arm64.
pub fn vectors_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    x86_only(p, "vectors")?;
    let (target, rest) = spec_head(spec);
    let start = locate(a, o, target).ok_or_else(|| unresolved(target))?;
    let entry = a
        .function_at(start)
        .ok_or_else(|| format!("no function contains {start:#x}"))?
        .entry;
    let (mut count, mut budget) = (VECTORS, BUDGET);
    for option in rest.map(str::trim) {
        match option.split_once('=') {
            Some(("count", n)) => {
                count = parse_count(n)
                    .filter(|n| (1..=INPUTS_MAX).contains(n))
                    .ok_or_else(|| format!("count is 1 to {INPUTS_MAX}"))?;
            }
            Some(("steps", n)) => {
                budget = parse_count(n)
                    .filter(|n| (1..=BUDGET_MAX).contains(n))
                    .ok_or_else(|| format!("steps is 1 to {BUDGET_MAX}"))?;
            }
            _ => {
                return Err(format!(
                    "vectors takes <function>[,count=N][,steps=N]; cannot read {}",
                    one_line(option)
                ));
            }
        }
    }
    within_total(count, budget)?;
    let text = decompile_named(p, a, o, entry).ok_or("the function does not decompile")?;
    let word = u8::try_from(p.arch.bitness().unwrap_or(64)).unwrap_or(64);
    let sig = printed(&text, word)?;
    let constants: Vec<u64> =
        compared_constants(&function_instructions(p, a, entry), Vec::new(), INPUTS_MAX)
            .iter()
            .map(|c| c.value)
            .collect();
    let inputs = vector_inputs(&sig.parameter_kinds(), &constants, count, entry)?;
    let seeded = constants.len().min(count.div_ceil(2));
    let shared = Shared {
        script: Script::read(p, a, o, entry, &text),
        pass: Some(passing(p, a, o, entry)),
        sig: Ok(sig.clone()),
    };
    let names = o.fingerprint();
    let outcomes: Vec<Arc<Outcome>> = inputs
        .iter()
        .map(|input| {
            a.derived.get_or_build_item(
                "fn_run",
                names,
                (entry, budget, input.clone()),
                || run_one(p, a, &shared, entry, input, budget),
                Outcome::bytes,
            )
        })
        .collect();
    let returned = outcomes.iter().filter(|x| x.value.is_some()).count();
    let mut out = format!(
        "# vectors for {}: {} input{} ({seeded} from the constants it compares, the rest generated from its signature), at most {budget} steps each; {returned} returned\n",
        sig.text,
        inputs.len(),
        plural(inputs.len())
    );
    out.push_str("# args\treturns\tstop\twrites\n");
    for (input, x) in inputs.iter().zip(&outcomes) {
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}",
            args_shown(input),
            x.value.map_or_else(|| "-".to_owned(), small_hex),
            x.stop,
            writes_shown(x)
        );
    }
    if returned == 0 {
        out.push_str("# harness: none, since no vector returned\n");
        return Ok(out);
    }
    out.push_str("# harness: C, asserting the vectors that returned\n");
    out.push_str(&harness(
        &c_name(&short_name(a, o, entry)),
        &sig,
        &inputs,
        &outcomes,
    ));
    Ok(out)
}
