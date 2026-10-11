//! Scripts: a user's own rules over what borer recovered, in a sandbox.
//!
//! borer's analyses are general. What a user knows about one program (that
//! every function passing a string to one logger is named by that string,
//! that a table at one address lists handlers) is a few lines of script. A
//! script is Rhai, a small language embedded in pure Rust: it reads the
//! program through the functions below and proposes names and comments,
//! which a front end prints, saves as a project or applies. It cannot touch
//! a file, the network, a process or the clock (`import` and `eval` are
//! gone and there is no such function to call), and it runs under an
//! operation budget, so a pack's script from anyone is safe to run.
//!
//! What a script sees:
//!
//! * `program()`: `path`, `format`, `arch`, `bits`, `base`, `entry`.
//! * `functions()`, `functions(filter)`: every function as a map (`entry`,
//!   `name`, `size`, `instrs`, `blocks`, `source`), the filter a
//!   case-insensitive part of the name; `function(entry or name)` adds
//!   `callers` and `callees`, and is `()` for no function.
//! * `callers(entry)`, `callees(entry)`, `name(entry)`,
//!   `strings(entry)` (`at`, `text` for each string it references),
//!   `xrefs(addr)` (`from`, `kind`, `function`).
//! * `read_u8`/`read_u16`/`read_u32`/`read_u64(addr)`, `bytes(addr, n)`,
//!   `cstr(addr)`, each `()` where nothing is mapped.
//! * `find_bytes("48 8b ?? ff")`, `find_text(text)`: addresses.
//! * `decompile(entry or name)`, `disasm(addr, count)` (`at`, `bytes`,
//!   `text`), `scenario(entry or name, "a2=5")` (the function decompiled
//!   with those parameters fixed).
//! * `imports()`, `exports()` (`name`, `at`), `sections()` (`name`, `at`,
//!   `size`, `r`, `w`, `x`).
//! * `hex(n)`, `args()` (the words after the script on the command line).
//! * `rename(entry, name)`, `comment(addr, text)`: proposals.
//!
//! A pack's `[scripts] run <file>` lines run at the end of every analysis
//! the pack takes part in ([`run_pack_scripts`]): the names a script
//! proposes go on functions borer left unnamed or named by vtable slot,
//! the same rule a pack's `[names]` lines follow, so a pack can carry a
//! program's rules as well as its data.

use std::cell::{Cell, RefCell};
use std::fmt::Write as _;
use std::rc::Rc;
use std::sync::Arc;

use rhai::{Array, Blob, Dynamic, Engine, INT, Map, Scope};

use crate::analysis::{Analysis, Function, NameSource, Overlay, decompile, name_of, resolve};
use crate::program::{Program, SymbolKind};

/// Operations a script may run before it is stopped.
pub const OPS_MAX: u64 = 200_000_000;
/// Deepest call nesting a script may reach.
const CALLS_MAX: usize = 64;
/// Longest string a script may build.
const STRING_MAX: usize = 1 << 22;
/// Most elements in one array or blob a script may build.
const ARRAY_MAX: usize = 1 << 21;
/// Most bytes one `bytes` call reads.
const BYTES_MAX: usize = 1 << 20;
/// Most instructions one `disasm` call decodes.
const DISASM_MAX: usize = 4096;
/// Shortest text read as a string a function references.
const STRING_MIN: usize = 4;
/// Longest text read as a string a function references.
const STRING_CAP: usize = 512;

/// What a script printed and proposed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ScriptRun {
    /// What it printed, a line per `print`.
    pub output: Vec<String>,
    /// The names it proposed, in the order it proposed them.
    pub names: Vec<(u64, String)>,
    /// The comments it proposed.
    pub comments: Vec<(u64, String)>,
    /// Operations it ran.
    pub operations: u64,
}

/// What one pack script did at the end of an analysis.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PackScript {
    /// The pack that runs it.
    pub pack: String,
    /// The script's file, as the pack's reader showed it.
    pub file: String,
    /// Functions it named.
    pub named: usize,
    /// Names it proposed for functions the program or an earlier rule
    /// already names, which stay.
    pub kept: usize,
    /// Comments it proposed, which an analysis does not hold.
    pub comments: usize,
    /// What it printed.
    pub output: Vec<String>,
    /// Operations it ran.
    pub operations: u64,
    /// Its error, when it failed; names it proposed before failing stay
    /// unapplied.
    pub error: Option<String>,
}

/// What a script's functions read, shared by every registered function.
struct Host {
    /// The loaded image.
    program: Arc<Program>,
    /// What borer recovered.
    analysis: Arc<Analysis>,
    /// The names in force.
    overlay: Arc<Overlay>,
    /// What the script printed and proposed so far.
    run: RefCell<ScriptRun>,
    /// The words after the script on the command line.
    args: Vec<String>,
}

/// An address as a script's integer; one above `i64::MAX` wraps, and
/// [`addr`] undoes it.
///
/// # Arguments
///
/// * `v` - The address.
fn int(v: u64) -> INT {
    INT::from_ne_bytes(v.to_ne_bytes())
}

/// A script's integer as an address.
///
/// # Arguments
///
/// * `v` - The integer.
fn addr(v: INT) -> u64 {
    u64::from_ne_bytes(v.to_ne_bytes())
}

/// A count as a script's integer.
///
/// # Arguments
///
/// * `n` - The count.
fn count(n: usize) -> INT {
    INT::try_from(n).unwrap_or(INT::MAX)
}

/// A map from keys and values.
///
/// # Arguments
///
/// * `pairs` - The keys and values.
fn map(pairs: Vec<(&str, Dynamic)>) -> Dynamic {
    let m: Map = pairs.into_iter().map(|(k, v)| (k.into(), v)).collect();
    Dynamic::from_map(m)
}

/// A list of addresses as a script's array.
///
/// # Arguments
///
/// * `list` - The addresses.
fn addrs(list: impl IntoIterator<Item = u64>) -> Array {
    list.into_iter()
        .map(|v| Dynamic::from_int(int(v)))
        .collect()
}

/// Whether a function's map carries its call edges.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Edges {
    /// Only the function's own facts, for a list.
    Omitted,
    /// `callers` and `callees` too, for one function.
    Included,
}

impl Host {
    /// A function as a script's map, with its callers and callees when
    /// asked.
    ///
    /// # Arguments
    ///
    /// * `f` - The function.
    /// * `edges` - Whether `callers` and `callees` are in the map.
    fn function_map(&self, f: &Function, edges: Edges) -> Dynamic {
        let mut pairs = vec![
            ("entry", Dynamic::from_int(int(f.entry))),
            (
                "name",
                name_of(&self.analysis, &self.overlay, f.entry).into(),
            ),
            (
                "size",
                Dynamic::from_int(int(f.end.saturating_sub(f.start))),
            ),
            ("instrs", Dynamic::from_int(count(f.instr_count))),
            ("blocks", Dynamic::from_int(count(f.blocks.len()))),
            ("source", f.name_source.code().into()),
        ];
        if edges == Edges::Included {
            pairs.push(("callers", Dynamic::from_array(addrs(f.callers.clone()))));
            pairs.push(("callees", Dynamic::from_array(addrs(f.callees.clone()))));
        }
        map(pairs)
    }

    /// The entry a script's argument names: an integer is an address, text
    /// is an address, `sub_` name or function name.
    ///
    /// # Arguments
    ///
    /// * `target` - The argument.
    fn entry_of(&self, target: &Dynamic) -> Option<u64> {
        if let Ok(v) = target.as_int() {
            return Some(addr(v));
        }
        let text = target.clone().into_immutable_string().ok()?;
        resolve(&self.program, &self.analysis, &self.overlay, &text).ok()
    }

    /// Reads `N` bytes at an address as a little-endian integer.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn read<const N: usize>(&self, at: INT) -> Dynamic {
        let Some(raw) = self.program.read_va(addr(at), N) else {
            return Dynamic::UNIT;
        };
        let mut buf = [0u8; 8];
        for (d, s) in buf.iter_mut().zip(raw) {
            *d = *s;
        }
        Dynamic::from_int(int(u64::from_le_bytes(buf)))
    }
}

/// Runs a script over a program.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - What borer recovered.
/// * `overlay` - The names in force.
/// * `code` - The script.
/// * `args` - The words after the script on the command line.
///
/// # Returns
///
/// What the script printed and proposed.
///
/// # Errors
///
/// The script's own error, with its line, when it does not parse, calls
/// what does not exist, fails, or runs past its operation budget.
pub fn run(
    program: Arc<Program>,
    analysis: Arc<Analysis>,
    overlay: Arc<Overlay>,
    code: &str,
    args: &[String],
) -> Result<ScriptRun, String> {
    let host = Rc::new(Host {
        program,
        analysis,
        overlay,
        run: RefCell::new(ScriptRun::default()),
        args: args.to_vec(),
    });
    let ops = Rc::new(Cell::new(0u64));
    let mut engine = Engine::new();
    engine
        .set_max_operations(OPS_MAX)
        .set_max_call_levels(CALLS_MAX)
        .set_max_string_size(STRING_MAX)
        .set_max_array_size(ARRAY_MAX)
        .set_max_map_size(ARRAY_MAX);
    engine.disable_symbol("eval");
    let h = Rc::clone(&host);
    engine.on_print(move |s| h.run.borrow_mut().output.push(s.to_owned()));
    let h = Rc::clone(&host);
    engine.on_debug(move |s, _, _| h.run.borrow_mut().output.push(s.to_owned()));
    let seen = Rc::clone(&ops);
    engine.on_progress(move |n| {
        seen.set(n);
        None
    });
    register(&mut engine, &host);
    let result = engine
        .run_with_scope(&mut Scope::new(), code)
        .map_err(|e| e.to_string());
    drop(engine);
    let mut out = host.run.borrow().clone();
    out.operations = ops.get();
    result.map(|()| out)
}

/// Registers every function a script can call.
///
/// # Arguments
///
/// * `engine` - The engine.
/// * `host` - What the functions read and where proposals go.
fn register(engine: &mut Engine, host: &Rc<Host>) {
    let h = Rc::clone(host);
    engine.register_fn("program", move || {
        let p = &h.program;
        map(vec![
            ("path", p.path.display().to_string().into()),
            ("format", format!("{:?}", p.format).into()),
            ("arch", p.arch.name().into()),
            (
                "bits",
                Dynamic::from_int(INT::from(p.arch.bitness().unwrap_or(0))),
            ),
            ("base", Dynamic::from_int(int(p.image_base))),
            (
                "entry",
                p.entry.map_or(Dynamic::UNIT, |e| Dynamic::from_int(int(e))),
            ),
        ])
    });
    let h = Rc::clone(host);
    engine.register_fn("functions", move || -> Array {
        h.analysis
            .functions
            .iter()
            .map(|f| h.function_map(f, Edges::Omitted))
            .collect()
    });
    let h = Rc::clone(host);
    engine.register_fn("functions", move |filter: &str| -> Array {
        let q = filter.to_lowercase();
        h.analysis
            .functions
            .iter()
            .filter(|f| {
                name_of(&h.analysis, &h.overlay, f.entry)
                    .to_lowercase()
                    .contains(&q)
            })
            .map(|f| h.function_map(f, Edges::Omitted))
            .collect()
    });
    let h = Rc::clone(host);
    engine.register_fn("function", move |target: Dynamic| {
        h.entry_of(&target)
            .and_then(|e| h.analysis.function(e))
            .map_or(Dynamic::UNIT, |f| h.function_map(f, Edges::Included))
    });
    let h = Rc::clone(host);
    engine.register_fn("callers", move |entry: INT| -> Array {
        h.analysis
            .function(addr(entry))
            .map_or_else(Array::new, |f| addrs(f.callers.clone()))
    });
    let h = Rc::clone(host);
    engine.register_fn("callees", move |entry: INT| -> Array {
        h.analysis
            .function(addr(entry))
            .map_or_else(Array::new, |f| addrs(f.callees.clone()))
    });
    let h = Rc::clone(host);
    engine.register_fn("name", move |entry: INT| {
        name_of(&h.analysis, &h.overlay, addr(entry))
    });
    let h = Rc::clone(host);
    engine.register_fn("strings", move |entry: INT| -> Array {
        let Some(refs) = h.analysis.refs_by_function.get(&addr(entry)) else {
            return Array::new();
        };
        refs.iter()
            .filter_map(|&(target, _)| {
                let (_, text) =
                    crate::strings::cstr_at(&h.program, target, STRING_MIN, STRING_CAP)?;
                Some(map(vec![
                    ("at", Dynamic::from_int(int(target))),
                    ("text", text.into()),
                ]))
            })
            .collect()
    });
    let h = Rc::clone(host);
    engine.register_fn("xrefs", move |at: INT| -> Array {
        h.analysis
            .xrefs
            .get(&addr(at))
            .map_or_else(Array::new, |sites| {
                sites
                    .iter()
                    .map(|s| {
                        map(vec![
                            ("from", Dynamic::from_int(int(s.va))),
                            ("kind", s.kind.word().into()),
                            (
                                "function",
                                s.from_entry
                                    .map_or(Dynamic::UNIT, |e| Dynamic::from_int(int(e))),
                            ),
                        ])
                    })
                    .collect()
            })
    });
    let h = Rc::clone(host);
    engine.register_fn("read_u8", move |at: INT| h.read::<1>(at));
    let h = Rc::clone(host);
    engine.register_fn("read_u16", move |at: INT| h.read::<2>(at));
    let h = Rc::clone(host);
    engine.register_fn("read_u32", move |at: INT| h.read::<4>(at));
    let h = Rc::clone(host);
    engine.register_fn("read_u64", move |at: INT| h.read::<8>(at));
    let h = Rc::clone(host);
    engine.register_fn("bytes", move |at: INT, n: INT| -> Blob {
        let n = usize::try_from(n).unwrap_or(0).min(BYTES_MAX);
        h.program
            .read_va_upto(addr(at), n)
            .map_or_else(Blob::new, <[u8]>::to_vec)
    });
    let h = Rc::clone(host);
    engine.register_fn("cstr", move |at: INT| {
        crate::strings::cstr_at(&h.program, addr(at), 1, STRING_CAP)
            .map_or(Dynamic::UNIT, |(_, text)| text.into())
    });
    let h = Rc::clone(host);
    engine.register_fn("find_bytes", move |pattern: &str| -> Array {
        crate::search::parse_pattern(pattern).map_or_else(Array::new, |p| {
            addrs(
                crate::search::find_bytes(&h.program, &p, 0)
                    .hits
                    .iter()
                    .filter_map(|hit| hit.va),
            )
        })
    });
    let h = Rc::clone(host);
    engine.register_fn("find_text", move |text: &str| -> Array {
        addrs(
            crate::search::find_text(&h.program, text.as_bytes(), 0)
                .hits
                .iter()
                .filter_map(|hit| hit.va),
        )
    });
    let h = Rc::clone(host);
    engine.register_fn("decompile", move |target: Dynamic| {
        h.entry_of(&target)
            .and_then(|e| decompile::decompile(&h.program, &h.analysis, &h.overlay, e))
            .map_or(Dynamic::UNIT, Dynamic::from)
    });
    let h = Rc::clone(host);
    engine.register_fn("scenario", move |target: Dynamic, spec: &str| {
        let Ok(assume) = decompile::parse_scenario(spec) else {
            return Dynamic::UNIT;
        };
        h.entry_of(&target)
            .and_then(|e| {
                decompile::decompile_scenario(&h.program, &h.analysis, &h.overlay, e, &assume)
            })
            .map_or(Dynamic::UNIT, Dynamic::from)
    });
    let h = Rc::clone(host);
    engine.register_fn("disasm", move |at: INT, n: INT| -> Array {
        let Some(bits) = h.program.arch.bitness() else {
            return Array::new();
        };
        let n = usize::try_from(n).unwrap_or(0).min(DISASM_MAX);
        let Some(code) = h.program.read_va_upto(addr(at), n.saturating_mul(15)) else {
            return Array::new();
        };
        crate::disasm::disassemble(code, addr(at), bits, n)
            .into_iter()
            .map(|l| {
                let hex: String = l.bytes.iter().map(|b| format!("{b:02x}")).collect();
                map(vec![
                    ("at", Dynamic::from_int(int(l.va))),
                    ("bytes", hex.into()),
                    ("text", l.text.into()),
                ])
            })
            .collect()
    });
    let symbols = |kind: SymbolKind| {
        let h = Rc::clone(host);
        move || -> Array {
            h.program
                .symbols
                .iter()
                .filter(|s| s.kind == kind)
                .map(|s| {
                    map(vec![
                        ("name", s.name.clone().into()),
                        ("at", Dynamic::from_int(int(s.addr))),
                    ])
                })
                .collect()
        }
    };
    engine.register_fn("imports", symbols(SymbolKind::Import));
    engine.register_fn("exports", symbols(SymbolKind::Export));
    let h = Rc::clone(host);
    engine.register_fn("sections", move || -> Array {
        h.program
            .sections
            .iter()
            .map(|s| {
                map(vec![
                    ("name", s.name.clone().into()),
                    ("at", Dynamic::from_int(int(s.va))),
                    ("size", Dynamic::from_int(int(s.vsize))),
                    ("r", s.readable.into()),
                    ("w", s.writable.into()),
                    ("x", s.executable.into()),
                ])
            })
            .collect()
    });
    engine.register_fn("hex", |v: INT| format!("{:#x}", addr(v)));
    let h = Rc::clone(host);
    engine.register_fn("args", move || -> Array {
        h.args.iter().map(|a| a.clone().into()).collect()
    });
    let h = Rc::clone(host);
    engine.register_fn("rename", move |entry: INT, name: &str| {
        let name = name.trim();
        if !name.is_empty() && !name.contains(['\t', '\n', '\r']) {
            h.run
                .borrow_mut()
                .names
                .push((addr(entry), name.to_owned()));
        }
    });
    let h = Rc::clone(host);
    engine.register_fn("comment", move |at: INT, text: &str| {
        let text = text.replace(['\t', '\n', '\r'], " ");
        if !text.trim().is_empty() {
            h.run.borrow_mut().comments.push((addr(at), text));
        }
    });
}

/// Runs every pack script over an analysis and names what they propose.
///
/// Each script sees the analysis as it stands, pack names included, and
/// the ones before it have not yet named anything, so their order does not
/// change what any of them sees. A name goes on a function borer left
/// unnamed or named by vtable slot, the first script's first; a failing
/// script names nothing and its error is kept.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The analysis, with its packs.
///
/// # Returns
///
/// The analysis, named, with a [`PackScript`] per script.
#[must_use]
pub fn run_pack_scripts(program: &Program, analysis: Analysis) -> Analysis {
    let scripts: Vec<(String, String, String)> = analysis
        .packs
        .packs
        .iter()
        .flat_map(|p| {
            p.scripts
                .iter()
                .map(|(file, code)| (p.name.clone(), file.clone(), code.clone()))
        })
        .collect();
    if scripts.is_empty() {
        return analysis;
    }
    let program = Arc::new(program.clone());
    let shared = Arc::new(analysis);
    let runs: Vec<(PackScript, Vec<(u64, String)>)> = scripts
        .into_iter()
        .map(|(pack, file, code)| {
            let result = run(
                Arc::clone(&program),
                Arc::clone(&shared),
                Arc::default(),
                &code,
                &[],
            );
            let mut report = PackScript {
                pack,
                file,
                ..PackScript::default()
            };
            match result {
                Ok(done) => {
                    report.comments = done.comments.len();
                    report.output = done.output;
                    report.operations = done.operations;
                    (report, done.names)
                }
                Err(e) => {
                    report.error = Some(e);
                    (report, Vec::new())
                }
            }
        })
        .collect();
    // INVARIANT: every other handle on `shared` lived in a script engine,
    // and `run` drops its engine before it returns, so this is the last.
    let Some(mut analysis) = Arc::into_inner(shared) else {
        return Analysis::default();
    };
    for (mut report, names) in runs {
        for (entry, name) in names {
            let Some(f) = analysis.function_mut(entry) else {
                continue;
            };
            if matches!(f.name_source, NameSource::None | NameSource::Slot) {
                f.name = Some(name);
                f.name_inferred = false;
                f.name_source = NameSource::Pack;
                report.named += 1;
            } else {
                report.kept += 1;
            }
        }
        analysis.pack_scripts.push(report);
    }
    analysis
}

/// What the pack scripts did, as a `#` summary and a row per script;
/// empty when no pack runs one.
///
/// # Arguments
///
/// * `scripts` - What [`run_pack_scripts`] recorded.
#[must_use]
pub fn pack_scripts_tsv(scripts: &[PackScript]) -> String {
    if scripts.is_empty() {
        return String::new();
    }
    let named: usize = scripts.iter().map(|s| s.named).sum();
    let failed = scripts.iter().filter(|s| s.error.is_some()).count();
    let mut out = format!(
        "# pack scripts: {} ran, {failed} failed, {named} functions named\n",
        scripts.len()
    );
    out.push_str("pack\tscript\tnamed\tkept\tcomments\toperations\tresult\n");
    for s in scripts {
        let result = s.error.as_deref().map_or_else(
            || s.output.last().cloned().unwrap_or_else(|| "ok".to_owned()),
            |e| format!("failed: {}", e.replace(['\t', '\n'], " ")),
        );
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}\t{}\t{}\t{result}",
            s.pack, s.file, s.named, s.kept, s.comments, s.operations
        );
    }
    out
}

/// What a script printed, then its proposals as a table: a `#` summary
/// and a row per name or comment.
///
/// # Arguments
///
/// * `run` - The run.
#[must_use]
pub fn run_tsv(run: &ScriptRun) -> String {
    let mut out = String::new();
    for line in &run.output {
        let _ = writeln!(out, "{line}");
    }
    let _ = writeln!(
        out,
        "# script: {} names and {} comments proposed, {} operations",
        run.names.len(),
        run.comments.len(),
        run.operations
    );
    if !run.names.is_empty() || !run.comments.is_empty() {
        out.push_str("what\tat\ttext\n");
        for (at, name) in &run.names {
            let _ = writeln!(out, "name\t{at:#x}\t{name}");
        }
        for (at, text) in &run.comments {
            let _ = writeln!(out, "comment\t{at:#x}\t{text}");
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A caller at `0x1000` and the function it calls at `0x1010`, which
    /// loads the string `"Mine::Thing"` at `0x1040`.
    fn fixture() -> (Arc<Program>, Arc<Analysis>) {
        let mut code = vec![0x48, 0x83, 0xec, 0x28]; // ASM: sub rsp, 0x28
        code.extend([0xe8, 0x07, 0x00, 0x00, 0x00]); // ASM: call 0x1010
        code.extend([0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 0x28; ret
        code.resize(0x10, 0xcc);
        code.extend([0x48, 0x8d, 0x05, 0x29, 0x00, 0x00, 0x00]); // ASM: lea rax, [rip+0x29] (0x1040)
        code.push(0xc3); // ASM: ret
        code.resize(0x40, 0xcc);
        code.extend(b"Mine::Thing\0");
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        (Arc::new(p), Arc::new(a))
    }

    /// Runs a script over the fixture.
    ///
    /// # Arguments
    ///
    /// * `code` - The script.
    ///
    /// # Errors
    ///
    /// The script's error.
    fn go(code: &str) -> Result<ScriptRun, String> {
        let (p, a) = fixture();
        run(p, a, Arc::default(), code, &["x".to_owned()])
    }

    /// A script walks the functions, reads what one references and
    /// proposes a name from it.
    ///
    /// # Panics
    ///
    /// When the script's output or proposals differ.
    #[test]
    fn a_script_names_a_function_by_its_string() {
        let run = go(r#"
            for f in functions() {
                for s in strings(f.entry) {
                    if s.text.contains("::") && f.name.starts_with("sub_") {
                        rename(f.entry, s.text);
                        print(`${hex(f.entry)} ${s.text}`);
                    }
                }
            }
            let f = function("sub_1000");
            print(`callees ${f.callees.len} first ${hex(f.callees[0])}`);
            print(`arg ${args()[0]} byte ${hex(read_u8(0x1010))} text ${cstr(0x1040)}`);
            print(`${disasm(0x1010, 1)[0].text}`);
        "#)
        .expect("the script runs");
        assert_eq!(
            run.output,
            vec![
                "0x1010 Mine::Thing",
                "callees 1 first 0x1010",
                "arg x byte 0x48 text Mine::Thing",
                "lea rax,[rel 1040h]",
            ]
        );
        assert_eq!(run.names, vec![(0x1010, "Mine::Thing".to_owned())]);
        assert!(run.operations > 0);
        let text = run_tsv(&run);
        assert!(
            text.contains("# script: 1 names and 0 comments proposed"),
            "{text}"
        );
        assert!(text.contains("\nname\t0x1010\tMine::Thing\n"), "{text}");
    }

    /// A pack's script names an unnamed function at the end of the
    /// analysis, a failing one names nothing, and both are reported.
    ///
    /// # Panics
    ///
    /// When the name or the report differs.
    #[test]
    fn a_pack_script_names_at_the_end_of_the_analysis() {
        let (p, _) = fixture();
        let (mut pack, _) = crate::pack::Pack::parse(
            "pack mine 1\n[scripts]\nrun a.rhai\nrun b.rhai\n",
            "mine.borer",
        )
        .expect("reads");
        assert_eq!(pack.script_files(), vec!["a.rhai", "b.rhai"]);
        pack.scripts = vec![
            (
                "a.rhai".to_owned(),
                "rename(0x1010, \"Mine::Thing\"); rename(0x1010, \"Other\"); print(\"done\");"
                    .to_owned(),
            ),
            (
                "b.rhai".to_owned(),
                "rename(0x1000, \"x\"); oops();".to_owned(),
            ),
        ];
        let packs = Arc::new(crate::pack::Packs { packs: vec![pack] });
        let a = Analysis::compute_with(&p, packs);
        let f = a.function(0x1010).expect("the callee");
        assert_eq!(f.name.as_deref(), Some("Mine::Thing"));
        assert_eq!(f.name_source, NameSource::Pack);
        assert!(
            a.function(0x1000)
                .is_some_and(|f| f.name_source != NameSource::Pack)
        );
        assert_eq!(a.pack_scripts.len(), 2);
        assert_eq!((a.pack_scripts[0].named, a.pack_scripts[0].kept), (1, 1));
        assert!(a.pack_scripts[1].error.is_some());
        let text = pack_scripts_tsv(&a.pack_scripts);
        assert!(
            text.starts_with("# pack scripts: 2 ran, 1 failed, 1 functions named"),
            "{text}"
        );
        assert!(text.contains("\nmine\ta.rhai\t1\t1\t0\t"), "{text}");
        assert!(text.contains("\tdone\n"), "{text}");
    }

    /// A script cannot import, evaluate text or run forever, and an error
    /// names its line.
    ///
    /// # Panics
    ///
    /// When a sandboxed script runs.
    #[test]
    fn a_script_stays_in_its_sandbox() {
        assert!(go(r#"import "x" as y;"#).is_err());
        assert!(go(r#"eval("1 + 1");"#).is_err());
        let err = go("loop {}").expect_err("the budget stops it");
        assert!(err.contains("operations"), "{err}");
        let err = go("\n\nno_such_function();").expect_err("an unknown call fails");
        assert!(err.contains("line 3"), "{err}");
    }
}
