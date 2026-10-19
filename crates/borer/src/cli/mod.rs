//! The one-shot command line: `borer <command> <binary> [args...]` runs one
//! query against the same engine the MCP server uses and prints a
//! context-window-sized answer.

use std::fmt::Write as _;
use std::sync::Arc;

use anyhow::{Context as _, anyhow, bail};
use borer_engine::analysis::{
    Overlay, about, anchors, attributes, classes, decompile, encode, fieldrefs, map, messages,
    name_of, parse_addr, parse_off, ports, protocol, render, schema, senders, sigs, snapshot,
    utypes, vtables,
};
use borer_engine::isa::Isa;
use borer_engine::pack::Pack;
use borer_engine::program::{Feature, Program};
use borer_engine::table::Window;
use borer_engine::text::{one_line, quoted, short_path};
use borer_engine::{disasm, entropy, hexdump as hexfmt, memory, num, script, search};

use crate::params::parse_field_offset;
use crate::params::{Filter, SearchKind, StringEncoding};
use crate::resources::ABOUT_NEEDS_A_NAME;
use crate::strwalk::{strings_page, walk_rows};
use crate::tools::bytes::entropy_threshold;
use crate::tools::search::render_hits;

/// `print!` into the answer, which `crate::term` writes to stdout once,
/// after the loading line is cleared: the same bytes as printing them here.
macro_rules! print {
    ($($arg:tt)*) => {
        crate::term::out(format_args!($($arg)*))
    };
}
/// `println!` into the answer, as [`print!`] does.
macro_rules! println {
    () => {
        crate::term::out(format_args!("
"))
    };
    ($($arg:tt)*) => {{
        crate::term::out(format_args!($($arg)*));
        crate::term::out(format_args!("
"));
    }};
}
/// `eprintln!` through `crate::term::note`, which clears the loading line first.
macro_rules! eprintln {
    ($($arg:tt)*) => {
        crate::term::note(&format!($($arg)*))
    };
}

mod args;
mod packs;
mod session;

use args::{
    COMMAND_FLAGS, Command, Direction, Query, RawFlags, SlotQuery, arg, cli_limit, cli_page,
    command_usage, entry_at, export_args, filter_limit, num_arg, path_arg, search_args,
    split_pack_args, unknown_word,
};
use packs::{pack_report, packs_report, sigmake, writable, write_file};
use session::{Session, decompiled, needs_a_binary, open};

/// Usage text printed by `help` and on argument errors.
const USAGE: &str = "usage: borer <command> <binary> [args...]
commands:
  info <binary>                            summary: format, arch, sections, symbols
  functions <binary> [filter] [offset] [limit]  discovered functions (100 a page, max 300; \"\" for no filter)
  function <binary> <address|name>         one function's ranges, blocks and edges
  summary <binary> <address|name>          one-call function triage
  symbols <binary> [filter] [offset] [limit]  imports, exports and locals (50 a page, max 1000)
  hexdump <binary> <address|name> [length]  bytes at a virtual address or name, or at off:<n> in the file (default 64, max 4096)
  entropy <binary> [threshold]             high-entropy regions (default 7.2)
  search <binary> <pattern> [text] [offset]  AOB hex with ?? wildcards, or a substring; 500 a page
  fstrings <binary> <address|name>         string literals one function references
  findstr <binary> <filter>                functions referencing a matching string
  disasm <binary> <address|name> [count]   disassemble at a virtual address or name (default 32, max 256)
  disasmfn <binary> <address|name>         a whole function, block by block
  decompile <binary> <address|name> [skeleton|full] [offset] [limit]  structured pseudo-C (skeleton: flow and calls only); 300 lines a page, limit 0 for all
  class <binary> <class|method address>    class layout from its methods' field accesses
  fieldrefs <binary> <offset> [filter] [skip] [limit]  every instruction touching [reg+offset]; filter names the function (100 a page, max 500)
  vslot <binary> <slot> [filter] [limit]   classes whose virtual at a slot returns a constant (a wire id, a type tag); filter names the class (max 2000)
  index <binary>                           decompile every function once into the cache that grep reads
  grep <binary> <text> [filter] [offset] [limit]  pseudo-C lines containing the text program-wide, or matching it when written re:<expression> ((?i) inside ignores case); filter names the function (100 a page, max 500)
  schema <binary> <function|class>         the record a deserializer reads off its stream: fields, widths, nesting, repeats
  schemas <binary> <slot> [filter] [limit]  every class with a constant at a slot and the record it decodes: a protocol as one table (max 2000)
  encode <binary> <function|class>         what a serializer writes onto its stream: fields in wire order, widths, the object field each came from
  encodes <binary> <slot> [filter] [limit]  every class with a constant at a slot and what it encodes: the outbound protocol as one table (max 2000)
  senders <binary> <slot> [filter] [limit]  every class with a constant at a slot and the functions constructing it: who sends each command (max 2000)
  protocol <binary> <slot> [filter] [limit]  every class with a constant at a slot with its senders, its handler, what it encodes and what it decodes on one row (max 2000)
  hooks <binary> <slot> [filter] [limit]   every class with a constant at a slot with the addresses a binding hooks: encoder, decoder, handler, send call sites (max 2000)
  shape <binary> <function> [limit]        every function running the same code over other operands, with the strings and data that differ (max 2000)
  messages <binary> [filter] [limit]       every class that registered a wire id, with its named fields and the functions testing for the id (max 200)
  about <binary> <name>                    everything known about one name from every table: attribute, class, message routes, wire, function
  snapshot <binary> <out>                  write the program's commands, packet layouts, attributes, message routes and ids by stable name to a file
  changes <binary> <snapshot>              what changed since a snapshot: commands, layouts, attributes, routes and ids added, removed or changed
  map <binary> [namespace] [limit]         the program's namespaces with their classes by role (pack [roles] lines, else role words in class names); a namespace lists its classes (max 5000)
  attrs <binary> [filter] [limit]          every typed attribute the program registers (a pack names the registrar): code, name, type, access, default, users; one exact match lists every user with the definition global (max 200)
  ports <binary> [filter] [limit]          every message every port accepts and the function it is dispatched to (a pack names the accept helpers); filter names the component or the message (max 5000)
  anchors <binary> <manifest>              re-derive every pinned fact in a manifest (field, vconst, function, encode, decode lines) and report held, moved, changed or gone; fails unless all held
  xrefs <binary> <address|name>            cross-references to an address
  cfg <binary> <address|name>              function control-flow graph (mermaid)
  callgraph <binary> <address|name> [callers|callees]  callgraph (mermaid, max 30); callers walks what reaches it
  strings <binary> [filter] [offset] [limit]    printable strings (100 a page, max 500; \"\" for no filter)
  crypto <binary>                          known crypto/hash constants
  qt <binary>                              Qt classes from moc metadata: signals, slots, properties
  triage <binary>                          one call: what it is, what it hides, where to read
  taint <binary> <addr>[,reg]              follow a value forward: what carries it, what it reaches
  layout <binary> <addr>[,reg]             propose a struct from what a function does through a pointer
  why <binary> <address|name>              what is at an address, and where each fact came from
  solve <binary> <addr>[,aN]               find an argument value that changes the answer
  partial <binary> <address>               a counted loop comparing a few bits of a product: lattice, not more samples
  flat <binary> [address]                  functions whose control flow was flattened into a switch
  vm <binary> [address]                    find the VM dispatch loops, or describe one's handlers
  devirt <binary> <address>[,budget=N,...]  run a virtualized function and recover its virtual program; budget=N pushes past a long bootstrap
  unpack <binary> <address>[,budget=N] [out]  run the unpacker; with out, write the materialized image
  oracle <binary> <address|name>           run a checksum on the standard probe and name it
  emulate <binary> <spec>                  run code and read it back; spec: addr[,reg=v,aN=v,w<addr>=<hex>,stop=<addr>,steps=<n>,trace=<n>,origin=<v>,dump=<addr>:<len>]; aN is the decompiler's aN, a1 the first
  run <binary> <function>[,steps=N]/<input>[;<input>...]  call a function on typed inputs (each: comma-separated 5, -1, \"text\", hex:0102, out:16) and check its decompiled text gives the same
  hidden <binary> [filter]                 strings the program generates instead of storing
  read <binary> <address|name> [kind] [count]  typed values (u8..u64, f32, f64, ptr, cstr, wstr; default 1, max 256); off:<n> reads by file offset
  fingerprint <binary> [out]               function fingerprints; with out, write the sidecar borer://diff reads
  doctor [offline]                         the local setup, one line each: version and commit, toolchain, symbol cache and server (offline skips the server), index cache, .mcp.json
  setup [--apply]                          register this binary as the MCP server borer with every agent client installed (Claude Code, Claude Desktop, Cursor, Windsurf, VS Code, Gemini CLI, Codex CLI, Zed); a dry run that shows each file and entry unless --apply, which keeps a .bak of each file it changes
  update [--check]                         install the latest release over this binary, checked against its SHA256SUMS; --check only says whether one is out (a command line run also checks once a day and says so on stderr; BORER_NO_UPDATE_CHECK=1 turns that off)
  version                                  print the version (also --version, -V)
  fetch-pdb <binary> [server]              fetch the companion PDB the debug record names from a symbol server (default msdl) into the local cache, kept only if its guid+age match; reload to apply
  pack <file>                              read a pack and report its name, its keys by section and what borer does not read
  pack-keys                                every key a pack can set, with its default and meaning
  packs <binary>                           the packs borer knows and whether each loads for the binary: the named ones, and every pack-directory pack whose [match] lines all hold
  export <binary> --c <out.c> [--library]   every function as one C file: the includes, each type, prototype, table and global once at the top, then every body leaves first; library functions (a signature named them) are left out unless --library
  export-pack <binary> <name> [project] [all]the names a project file gave (and with all, the names borer recovered) as a pack that finds the same functions in another build by their first bytes
  sigmake <out> <name> <library>...         the functions of static libraries or objects (.lib, .obj, .a, .o, Rust .rlib) as a pack of signatures, the relocated bytes masked, that names them in any program linked with them; an <out> ending in .bsig is a compact set like the ones borer ships
  script <binary> <file> [args...]           run a Rhai script in a sandbox: it reads functions, strings, bytes and xrefs, prints, and proposes names and comments; --save <project> writes them for export-pack
  scenario <binary> <function> <a2=5,...>    decompile under assumptions: branches and switches on the fixed parameters fold and only the code that can run is written
  scenarios <binary> <function> <a2=0..32>   a scenario per value of one parameter (a range, or values joined by |), the ones that behave alike grouped with their calls and returns
  types <binary> [project] [filter] [offset] [limit]  user-defined types a project states and where each is applied (50 a page, max 500; \"\" for no filter)
  set-type <binary> <project> struct <name> [size] <off:name:type>...  define a struct in the project; or set-type <binary> <project> enum <name> [size] <name:value>...; or set-type <binary> <project> typedef <name> <type>; or set-type <binary> <project> apply <address|name> <type>, so decompile names that global's fields or constants
  verify <binary> [function|all] [limit] [seed]check the lifter against the emulator (arm64 code against the arm64 machine) block by block from seeded states; lists every register, stack slot, store and branch they disagree on and fails if any (default all, 2000 functions)
  verify <binary> <function|all> <limit> <seed> text  check the text's statements instead (x86 and x64 only): each block's, replayed under the lifter's witness, against the emulator from three seeded states; lists every claim the machine does not bear out and fails on any but lane roughness
  verify <binary> <function|all> <limit> <seed> mir  the same check as the first form, every lifted value read through MIR: lowered to width-explicit ops and run by the MIR evaluator
options:
  --pack <file>                            run the analysis with a pack (repeatable; BORER_PACKS lists more, for the MCP server too)
  --no-auto-packs                          load only the packs --pack and BORER_PACKS name, not the pack directories' (BORER_AUTO_PACKS=0 does the same)
  --no-pdb                                 do not apply the companion PDB the debug record names, where one is on disk
  --arch <x86|x64|arm64>                   read the binary as raw code or a memory dump of that architecture, its headers unread
  --base <address>                         with --arch: where the file's first byte maps (default 0)
  --entry <address>                        with --arch: the entry (default the first executable byte)
  --regions <va@off:len[:rwx],...>         with --arch, instead of --base: map these parts of the file at these addresses (max 256)
no arguments starts the MCP stdio server";

/// The cap on rows that list classes: every class a program has fits.
const CLASS_ROWS: usize = 2000;

/// The cap on rows of the port and namespace catalogs.
const CATALOG_ROWS: usize = 5000;

/// The cap on rows of the message and attribute catalogs, where their
/// renderers page.
const PAGE_ROWS: usize = 200;

/// Bytes per window the entropy scan measures.
const ENTROPY_WINDOW: usize = 1024;

/// Runs one CLI command against a binary, sharing the engine with the server.
///
/// The command word is read first, so a word that is no command, an
/// option borer does not know or an argument too many is refused before
/// any binary is loaded; then the pack tools run on pack files alone, and
/// every other command opens the binary.
///
/// # Arguments
///
/// * `args` - Command, binary path, and command arguments (see the usage text).
///
/// # Errors
///
/// For an unknown command, option or help topic, an argument too many, a
/// missing or unloadable binary, a bad address, or an engine failure; the
/// message carries the command's usage lines where it helps.
pub(crate) fn cli(args: &[String]) -> anyhow::Result<()> {
    if let [word] = args
        && matches!(word.as_str(), "--version" | "-V" | "version")
    {
        println!("borer {}", env!("CARGO_PKG_VERSION"));
        return Ok(());
    }
    let (args, raw) = RawFlags::split(args)?;
    let (owned, pack_files, auto, pdb) = split_pack_args(&args)?;
    let args = owned.as_slice();
    let Some(word) = args.first() else {
        bail!("an option was given but no command; `borer help` lists the commands");
    };
    if matches!(word.as_str(), "help" | "--help" | "-h") {
        if let Some(extra) = args.get(2) {
            bail!("help takes one command, not also {}", quoted(extra));
        }
        match args.get(1) {
            Some(topic) => {
                println!(
                    "{}",
                    command_usage(USAGE, topic).with_context(|| unknown_word(topic))?
                );
            }
            None if crate::term::styled_out() => print!("{}", crate::term::paint_usage(USAGE)),
            None => println!("{USAGE}"),
        }
        return Ok(());
    }
    let command = Command::parse(word).with_context(|| unknown_word(word))?;
    if args.iter().skip(1).any(|a| a == "--help" || a == "-h") {
        println!(
            "{}",
            command_usage(USAGE, word).unwrap_or_else(|| USAGE.to_owned())
        );
        return Ok(());
    }
    if let Command::Query(q) = command
        && let Some(flag) = args.iter().enumerate().skip(1).find_map(|(i, a)| {
            let handed_on = q == Query::Script && i > 2;
            (a.starts_with("--") && !COMMAND_FLAGS.contains(&a.as_str()) && !handed_on).then_some(a)
        })
    {
        bail!("{}", unknown_word(flag));
    }
    let (first, after) = match command {
        Command::Query(_) => (2, " after the binary"),
        Command::PackKeys
        | Command::Pack
        | Command::Sigmake
        | Command::Packs
        | Command::Doctor
        | Command::Setup
        | Command::Update
        | Command::FetchPdb => (1, ""),
    };
    let layout = raw.layout()?;
    let maps_a_binary = match command {
        Command::Query(_) | Command::Packs => true,
        Command::PackKeys
        | Command::Pack
        | Command::Sigmake
        | Command::Doctor
        | Command::Setup
        | Command::Update
        | Command::FetchPdb => false,
    };
    if layout.is_some() && !maps_a_binary {
        bail!(
            "--arch, --base, --entry and --regions say how a query reads its binary; {word} maps none"
        );
    }
    if let Some(most) = command.most_args()
        && let Some(extra) = args.get(first + most)
    {
        let takes = match most {
            0 => format!("nothing{after}, not"),
            1 => format!("one argument{after}, not also"),
            n => format!("at most {n} arguments{after}, not also"),
        };
        bail!(
            "{word} takes {takes} {}\n{}",
            quoted(extra),
            command_usage(USAGE, word).unwrap_or_default()
        );
    }
    match command {
        Command::PackKeys => print!("{}", borer_engine::pack::keys_tsv()),
        Command::Pack => {
            let file = arg(args, 1, "pack needs a file")?;
            let text = std::fs::read_to_string(file)
                .with_context(|| format!("reading {}", short_path(file)))?;
            let (pack, warnings) =
                Pack::parse(&text, &short_path(file)).map_err(anyhow::Error::msg)?;
            print!("{}", pack_report(&pack, &warnings));
        }
        Command::Sigmake => sigmake(args)?,
        Command::Packs => {
            let (named, program) = open(args, &pack_files, pdb, layout.as_ref())?;
            print!("{}", packs_report(&program, &named, auto));
        }
        Command::Doctor => {
            let offline = match args.get(1).map(String::as_str) {
                None => false,
                Some("offline") => true,
                Some(other) => bail!("doctor takes `offline` or nothing, not {}", quoted(other)),
            };
            print!("{}", crate::doctor::doctor(offline)?);
        }
        Command::Setup => {
            let apply = match args.get(1).map(String::as_str) {
                None => false,
                Some("--apply") => true,
                Some(other) => bail!("setup takes `--apply` or nothing, not {}", quoted(other)),
            };
            let (report, failed) = crate::setup::setup(apply)?;
            print!("{report}");
            if failed > 0 {
                bail!("{failed} client(s) could not be set up; their lines say why");
            }
        }
        Command::Update => {
            let check_only = match args.get(1).map(String::as_str) {
                None => false,
                Some("--check") => true,
                Some(other) => bail!("update takes `--check` or nothing, not {}", quoted(other)),
            };
            print!(
                "{}{}",
                crate::term::mark(true),
                crate::update::update(check_only)?
            );
        }
        Command::FetchPdb => {
            let path = args.get(1).with_context(|| needs_a_binary(word))?;
            let program = Program::load_with(std::path::Path::new(path), false)
                .with_context(|| format!("loading {}", short_path(path)))?;
            let record = program.pdb_record.as_ref().with_context(|| {
                format!(
                    "{} names no companion pdb (no codeview record)",
                    short_path(path)
                )
            })?;
            let root = crate::symsrv::cache_dir().with_context(|| {
                format!(
                    "no cache directory: set {}, LOCALAPPDATA, XDG_CACHE_HOME or HOME",
                    crate::symsrv::CACHE_ENV
                )
            })?;
            let server = args
                .get(2)
                .map_or(crate::symsrv::DEFAULT_SERVER, String::as_str);
            let said = crate::symsrv::obtain(record, &root, server, false, crate::symsrv::curl)
                .map_err(|e| anyhow!("{e}"))?;
            println!("{said}");
        }
        Command::Query(q) => {
            let (named, program) = open(args, &pack_files, pdb, layout.as_ref())?;
            query(q, args, &Session::fit(program, &named, auto))?;
        }
    }
    Ok(())
}

/// Runs one query against an open binary.
///
/// Every query reads its arguments in the order the usage text lists them
/// and reports the first that is missing or wrong; `callgraph` alone reads
/// its direction before it looks the function up, since a `callers` walk may
/// start from an import or a data symbol, and reports a bad direction after
/// a bad address.
///
/// # Arguments
///
/// * `cmd` - The query.
/// * `args` - The command line, the command first and the binary second.
/// * `s` - The binary with its packs.
///
/// # Errors
///
/// For a missing or bad argument, an architecture borer cannot disassemble,
/// a file that cannot be read or written, or an engine failure.
fn query(cmd: Query, args: &[String], s: &Session) -> anyhow::Result<()> {
    match cmd {
        Query::Info => print!("{}", s.program.summary()),
        Query::Functions => {
            let a = s.analysis(Feature::Discover)?;
            let (offset, limit) = cli_page(args, 3, 100, 300)?;
            let (_, _, text) = render::functions_tsv(
                &a,
                &s.overlay,
                args.get(2).map(String::as_str).filter(|f| !f.is_empty()),
                render::FunctionOrder::Address,
                offset,
                limit,
            );
            print!("{text}");
        }
        Query::Function => {
            let (a, entry) = s.function_arg(
                args,
                2,
                "function needs an address or name",
                Feature::Discover,
            )?;
            print!(
                "{}",
                render::function_detail(&a, &s.overlay, entry, 0)
                    .context("no function at address")?
            );
        }
        Query::Summary => {
            let (a, entry) = s.function_arg(
                args,
                2,
                "summary needs an address or name",
                Feature::Discover,
            )?;
            print!(
                "{}",
                render::function_summary(&s.program, &a, &s.overlay, entry)
                    .context("no function at address")?
            );
        }
        Query::Symbols => {
            let a = s.analysis_or_empty();
            let (offset, limit) = cli_page(args, 3, 50, 1000)?;
            let (_, _, text) = render::symbols_tsv(
                &s.program,
                &a,
                None,
                args.get(2).map(String::as_str).filter(|f| !f.is_empty()),
                offset,
                limit,
            );
            print!("{text}");
        }
        Query::Hexdump => {
            let n: usize = num_arg(args, 3, 64, "hexdump length")?.min(4096);
            if n == 0 {
                bail!("hexdump length must be at least 1");
            }
            if let Some(off) = args.get(2).and_then(|t| parse_off(t)) {
                let dump = hexfmt::file_hexdump(&s.program, off, n).map_err(anyhow::Error::msg)?;
                print!("{dump}");
                return Ok(());
            }
            let va = s.address(arg(args, 2, "hexdump needs an address")?)?;
            let code = s.program.read_va_upto(va, n).with_context(|| {
                format!(
                    "address {va:#x} not mapped{}",
                    memory::by_offset_hint(&s.program)
                )
            })?;
            let sec = s
                .program
                .section_at(va)
                .map_or_else(String::new, |sec| format!(" {}", sec.name));
            println!("# {va:#x}..{:#x}{sec}", va + num::from_usize(code.len()));
            print!("{}", hexfmt::hexdump(code, va));
        }
        Query::Entropy => {
            let threshold = entropy_threshold(num_arg(args, 2, 7.2, "entropy threshold")?)
                .map_err(anyhow::Error::msg)?;
            print!(
                "{}",
                entropy::report(
                    &s.program,
                    ENTROPY_WINDOW,
                    threshold,
                    0,
                    entropy::REGIONS_MAX
                )
            );
        }
        Query::Search => {
            let pattern = arg(args, 2, "search needs a pattern")?;
            if pattern.is_empty() {
                bail!("search needs a non-empty pattern; an empty one would match nothing");
            }
            let (kind, offset) = search_args(args.get(3..).unwrap_or_default())?;
            let hits = match kind {
                SearchKind::Text => search::find_text(&s.program, pattern, offset),
                SearchKind::Bytes => {
                    let pat = search::parse_pattern(pattern)
                        .context("bad AOB pattern; use hex bytes with ?? wildcards")?;
                    search::find_bytes(&s.program, &pat, offset)
                }
            };
            let a = s.analysis_or_empty();
            print!("{}", render_hits(&hits, offset, false, (&a, &s.overlay)));
        }
        Query::Fstrings => {
            let (a, entry) = s.function_arg(
                args,
                2,
                "fstrings needs an address or name",
                Feature::Discover,
            )?;
            print!(
                "{}",
                render::function_strings_tsv(&s.program, &a, &s.overlay, entry)
                    .context("no function at address")?
            );
        }
        Query::Findstr => {
            let a = s.analysis(Feature::Discover)?;
            let filter = arg(args, 2, "findstr needs a filter")?;
            print!(
                "{}",
                render::functions_by_string_tsv(&s.program, &a, &s.overlay, filter, 0, 50)
            );
        }
        Query::Disasm => {
            let va = s.address(arg(args, 2, "disasm needs an address")?)?;
            let count: usize = num_arg(args, 3, 32, "disasm count")?;
            if count == 0 {
                bail!("disasm count must be at least 1");
            }
            let count = count.min(256);
            let isa = s
                .program
                .isa_for(Feature::Disasm)
                .map_err(anyhow::Error::msg)?;
            let code = s
                .program
                .read_va_upto(va, 16 * 1024)
                .with_context(|| format!("address {va:#x} not mapped"))?;
            let a = s.analysis_or_empty();
            let window = render::sweep_limit(&s.program, &a, va)
                .and_then(|end| usize::try_from(end - va).ok())
                .and_then(|n| code.get(..n.min(code.len())))
                .unwrap_or(code);
            let lines = disasm::disassemble_isa(window, va, isa, count);
            let caveat = render::listing_caveat(&s.program, &a, va);
            if !caveat.is_empty() {
                println!("# {caveat}");
            }
            print!("{}", disasm::render(&lines, true));
        }
        Query::Disasmfn => {
            let (a, entry) = s.function_arg(
                args,
                2,
                "disasmfn needs an address or name",
                Feature::Discover,
            )?;
            print!(
                "{}",
                render::disasm_function(&s.program, &a, &s.overlay, entry, 400, false)
                    .context("no function at address")?
            );
        }
        Query::Decompile => {
            print!("{}", decompiled(args, s)?);
            if let Some(steps) = decompile::step_times() {
                eprint!("{steps}");
            }
        }
        Query::Class => {
            let a = s.analysis(Feature::Decompile)?;
            let what = arg(args, 2, "class needs a class name or a method address")?;
            let class = match s.resolve(&a, what) {
                Ok(va) => {
                    let name = name_of(&a, &s.overlay, entry_at(&s.program, &a, va)?);
                    classes::class_of(&name)
                        .with_context(|| format!("{} is not a class method", quoted(&name)))?
                        .to_owned()
                }
                Err(_) => what.to_owned(),
            };
            let layout = classes::class_layout(&s.program, &a, &s.overlay, &class)
                .with_context(|| format!("no function belongs to class {}", quoted(&class)))?;
            print!("{}", classes::render_layout(&layout, &a, &s.overlay));
        }
        Query::Fieldrefs => {
            let a = s.analysis(Feature::Decompile)?;
            let offset = parse_field_offset(arg(args, 2, "fieldrefs needs a field offset")?)?;
            let filter = args.get(3).map_or("", String::as_str);
            let (skip, limit) = cli_page(args, 4, 100, 500)?;
            print!(
                "{}",
                fieldrefs::field_refs_tsv(
                    &s.program,
                    &a,
                    &s.overlay,
                    offset,
                    filter,
                    Window {
                        skip,
                        limit,
                        again: None
                    }
                )
            );
        }
        Query::Vslot => {
            let a = s.analysis(Feature::Decompile)?;
            let q = SlotQuery::parse(args, "vslot needs a vtable slot index")?;
            print!(
                "{}",
                vtables::slot_constants_tsv(&s.program, &a, q.slot, q.filter, q.limit)
            );
        }
        Query::Index => {
            let a = s.analysis(Feature::Decompile)?;
            #[expect(
                clippy::disallowed_methods,
                reason = "the CLI tells the user how long indexing took"
            )]
            let t0 = std::time::Instant::now();
            let (index, path, built) =
                borer::index::load_or_build(&s.program, &a).map_err(anyhow::Error::msg)?;
            if built {
                eprintln!("indexed in {:.3} s", t0.elapsed().as_secs_f64());
            }
            if let Some(steps) = decompile::step_times() {
                eprint!("{steps}");
            }
            println!(
                "# {} {} functions, {} bytes of pseudo-C -> {}",
                if built { "indexed" } else { "already indexed" },
                index.functions.len(),
                index.text_bytes(),
                path.display()
            );
        }
        Query::Grep => {
            let pattern = arg(args, 2, "grep needs the text to find")?;
            if pattern.is_empty() {
                bail!("grep needs a non-empty text; an empty one would match nothing");
            }
            borer::index::Matcher::parse(pattern).map_err(anyhow::Error::msg)?;
            let filter = args.get(3).map_or("", String::as_str);
            let (skip, limit) = cli_page(args, 4, 100, 500)?;
            let a = s.analysis(Feature::Decompile)?;
            let (index, _, built) =
                borer::index::load_or_build(&s.program, &a).map_err(anyhow::Error::msg)?;
            if built {
                eprintln!(
                    "there was no index for this program; every function was decompiled once"
                );
            }
            print!(
                "{}",
                borer::index::grep_tsv(
                    &index,
                    &a,
                    &s.overlay,
                    pattern,
                    filter,
                    Window {
                        skip,
                        limit,
                        again: None
                    }
                )
                .map_err(anyhow::Error::msg)?
            );
        }
        Query::Schema => {
            let a = s.analysis(Feature::Decompile)?;
            let what = arg(
                args,
                2,
                "schema needs a function (address or name) or a class name",
            )?;
            let text = match s.resolve(&a, what) {
                Ok(va) => {
                    schema::schema_tsv(&s.program, &a, &s.overlay, entry_at(&s.program, &a, va)?)
                        .with_context(|| {
                            format!("{} hands no stream to its calls", one_line(what))
                        })?
                }
                Err(_) => schema::class_schema_tsv(&s.program, &a, &s.overlay, what).with_context(
                    || {
                        format!(
                            "{} is neither a function nor a class whose virtuals read a stream",
                            quoted(what)
                        )
                    },
                )?,
            };
            print!("{text}");
        }
        Query::Schemas => {
            let a = s.analysis(Feature::Decompile)?;
            let q = SlotQuery::parse(args, "schemas needs the vtable slot the id sits in")?;
            print!(
                "{}",
                schema::schemas_tsv(&s.program, &a, &s.overlay, q.slot, q.filter, q.limit)
            );
        }
        Query::Encode => {
            let a = s.analysis(Feature::Decompile)?;
            let what = arg(
                args,
                2,
                "encode needs a function (address or name) or a class name",
            )?;
            let text = match s.resolve(&a, what) {
                Ok(va) => {
                    encode::encoding_tsv(&s.program, &a, &s.overlay, entry_at(&s.program, &a, va)?)
                        .with_context(|| format!("{} hands its stream nothing", one_line(what)))?
                }
                Err(_) => encode::class_encoding_tsv(&s.program, &a, &s.overlay, what)
                    .with_context(|| {
                        format!(
                            "{} is neither a function nor a class whose virtuals write a stream",
                            quoted(what)
                        )
                    })?,
            };
            print!("{text}");
        }
        Query::Encodes => {
            let a = s.analysis(Feature::Decompile)?;
            let q = SlotQuery::parse(args, "encodes needs the vtable slot the id sits in")?;
            print!(
                "{}",
                encode::encodings_tsv(&s.program, &a, &s.overlay, q.slot, q.filter, q.limit)
            );
        }
        Query::Senders => {
            let a = s.analysis(Feature::Decompile)?;
            let q = SlotQuery::parse(args, "senders needs the vtable slot the id sits in")?;
            print!(
                "{}",
                senders::senders_tsv(&s.program, &a, &s.overlay, q.slot, q.filter, q.limit)
            );
        }
        Query::Protocol => {
            let a = s.analysis(Feature::Decompile)?;
            let q = SlotQuery::parse(args, "protocol needs the vtable slot the id sits in")?;
            print!(
                "{}",
                protocol::protocol_tsv(&s.program, &a, &s.overlay, q.slot, q.filter, q.limit)
            );
        }
        Query::Hooks => {
            let a = s.analysis(Feature::Decompile)?;
            let q = SlotQuery::parse(args, "hooks needs the vtable slot the id sits in")?;
            print!(
                "{}",
                protocol::hooks_tsv(&s.program, &a, &s.overlay, q.slot, q.filter, q.limit)
            );
        }
        Query::Shape => {
            let (a, entry) =
                s.function_arg(args, 2, "shape needs a function", Feature::Discover)?;
            let limit = cli_limit(args, 3, CLASS_ROWS, CLASS_ROWS)?;
            print!(
                "{}",
                render::shape_siblings_tsv(&s.program, &a, &s.overlay, entry, limit)
                    .context("no function at address")?
            );
        }
        Query::Messages => {
            let a = s.analysis(Feature::Decompile)?;
            let (filter, limit) = filter_limit(args, PAGE_ROWS)?;
            print!(
                "{}",
                messages::catalog_tsv(&s.program, &a, &s.overlay, filter, Window::first(limit))
            );
        }
        Query::About => {
            let a = s.analysis(Feature::Decompile)?;
            let name = arg(args, 2, ABOUT_NEEDS_A_NAME)?;
            if name.trim().is_empty() {
                bail!(ABOUT_NEEDS_A_NAME);
            }
            print!("{}", about::about_tsv(&s.program, &a, &s.overlay, name));
        }
        Query::Snapshot => {
            let out = path_arg(args, 2, "snapshot needs a file to write")?;
            writable(out)?;
            let a = s.analysis(Feature::Decompile)?;
            let facts = snapshot::facts(&s.program, &a, &s.overlay);
            write_file(out, snapshot::write(&facts).as_bytes())?;
            println!(
                "wrote {} facts to {}; `borer changes <binary> {}` after the next update lists what changed",
                facts.len(),
                short_path(out),
                short_path(out)
            );
        }
        Query::Changes => {
            let a = s.analysis(Feature::Decompile)?;
            let path = path_arg(args, 2, "changes needs a snapshot file")?;
            let text = std::fs::read_to_string(path)
                .with_context(|| format!("reading {}", short_path(path)))?;
            let before = snapshot::read(&text).map_err(anyhow::Error::msg)?;
            let after = snapshot::facts(&s.program, &a, &s.overlay);
            print!("{}", snapshot::changes_tsv(&before, &after));
        }
        Query::Map => {
            let a = s.analysis(Feature::Decompile)?;
            let (namespace, limit) = filter_limit(args, CATALOG_ROWS)?;
            print!("{}", map::map_tsv(&a, &s.overlay, namespace, limit));
        }
        Query::Attrs => {
            let a = s.analysis(Feature::Decompile)?;
            let (filter, limit) = filter_limit(args, PAGE_ROWS)?;
            print!(
                "{}",
                attributes::catalog_tsv(&s.program, &a, &s.overlay, filter, Window::first(limit))
            );
        }
        Query::Ports => {
            let a = s.analysis(Feature::Decompile)?;
            let (filter, limit) = filter_limit(args, CATALOG_ROWS)?;
            print!(
                "{}",
                ports::routes_tsv(&s.program, &a, &s.overlay, filter, limit)
            );
        }
        Query::Anchors => {
            let a = s.analysis(Feature::Decompile)?;
            let manifest = path_arg(args, 2, "anchors needs a manifest file")?;
            let text = std::fs::read_to_string(manifest)
                .with_context(|| format!("reading {}", short_path(manifest)))?;
            let pinned = anchors::parse_manifest(&text).map_err(anyhow::Error::msg)?;
            let (table, all_held) =
                anchors::verify_tsv(&s.program, &a, &s.overlay, &pinned, pinned.len());
            print!("{table}");
            if !all_held {
                bail!("anchors moved, changed or gone; see the table above");
            }
        }
        Query::Xrefs => {
            let a = s.analysis(Feature::Discover)?;
            let va = s.resolve(&a, arg(args, 2, "xrefs needs an address")?)?;
            print!(
                "{}",
                render::xrefs_tsv(&a, &s.overlay, va, 0, render::XREF_ROWS_DEFAULT, false)
            );
        }
        Query::Cfg => {
            let (a, entry) =
                s.function_arg(args, 2, "cfg/callgraph needs an address", Feature::Discover)?;
            print!(
                "{}",
                render::cfg_mermaid(&a, &s.overlay, entry, 0).context("no function at address")?
            );
        }
        Query::Callgraph => {
            let a = s.analysis(Feature::Discover)?;
            let va = s.resolve(&a, arg(args, 2, "cfg/callgraph needs an address")?)?;
            let direction = Direction::parse(args.get(3).map(String::as_str));
            let referenced = matches!(direction, Ok(Direction::Callers))
                && (a.symbol_at(&s.program, va).is_some() || a.xrefs.contains_key(&va));
            let entry = if referenced {
                a.function_at(va).map_or(va, |f| f.entry)
            } else {
                entry_at(&s.program, &a, va)?
            };
            let callers = direction? == Direction::Callers;
            print!(
                "{}",
                render::callgraph_mermaid(&s.program, &a, &s.overlay, entry, 30, callers)
            );
        }
        Query::Strings => {
            let filter = Filter::new(args.get(2).map(String::as_str).filter(|f| !f.is_empty()));
            let window = cli_page(args, 3, 100, 500)?;
            let walk = (crate::strwalk::WALK_MIN, StringEncoding::Both);
            let rows = walk_rows(&s.program, &s.analysis_or_empty(), walk.1, walk.0);
            print!(
                "{}",
                strings_page(&s.program, rows, &filter, walk, window, false)
            );
        }
        Query::Crypto => {
            let a = s.analysis_or_empty();
            print!("{}", render::crypto_tsv(&s.program, &a, &s.overlay, 0, 200));
        }
        Query::Qt => {
            let a = s.analysis(Feature::Decompile)?;
            print!("{}", render::qt_tsv(&a));
        }
        Query::Triage => {
            if s.program.refuses(Feature::Decompile).is_some() {
                print!("{}", render::file_triage_tsv(&s.program));
            } else {
                let a = s.analysis(Feature::Decompile)?;
                print!("{}", render::triage_tsv(&s.program, &a, &s.overlay));
            }
        }
        Query::Taint => {
            let a = s.analysis(Feature::Decompile)?;
            let spec = arg(args, 2, "taint needs <address>[,<register>]")?;
            print!(
                "{}",
                render::taint_tsv(&s.program, &a, &s.overlay, spec).map_err(anyhow::Error::msg)?
            );
        }
        Query::Layout => {
            let a = s.analysis(Feature::Decompile)?;
            let spec = arg(args, 2, "layout needs <address>[,<register>]")?;
            print!(
                "{}",
                render::layout_tsv(&s.program, &a, &s.overlay, spec).map_err(anyhow::Error::msg)?
            );
        }
        Query::Why => {
            let a = s.analysis(Feature::Decompile)?;
            let target = arg(args, 2, "why needs an address or name")?;
            print!(
                "{}",
                render::why_tsv(&s.program, &a, &s.overlay, target).map_err(anyhow::Error::msg)?
            );
        }
        Query::Solve => {
            let a = s.analysis(Feature::Emulate)?;
            let spec = arg(args, 2, "solve needs <address>[,<argument>]")?;
            print!(
                "{}",
                render::solve_tsv(&s.program, &a, &s.overlay, spec).map_err(anyhow::Error::msg)?
            );
        }
        Query::Partial => {
            let a = s.analysis(Feature::Decompile)?;
            let target = arg(args, 2, "partial needs an address")?;
            print!(
                "{}",
                render::partial_tsv(&s.program, &a, &s.overlay, target)
                    .map_err(anyhow::Error::msg)?
            );
        }
        Query::Flat => {
            let a = s.analysis(Feature::Decompile)?;
            let filter = args.get(2).map_or("", String::as_str);
            print!(
                "{}",
                render::flattening_tsv(&s.program, &a, &s.overlay, filter)
                    .map_err(anyhow::Error::msg)?
            );
        }
        Query::Vm => {
            let a = s.analysis(Feature::Decompile)?;
            let filter = args.get(2).map_or("", String::as_str);
            print!(
                "{}",
                render::vm_dispatch_tsv(&s.program, &a, &s.overlay, filter)
                    .map_err(anyhow::Error::msg)?
            );
        }
        Query::Devirt => {
            let a = s.analysis(Feature::Emulate)?;
            let target = arg(args, 2, "devirt needs <address>[,reg=value...]")?;
            print!(
                "{}",
                render::devirtualize_tsv(&s.program, &a, &s.overlay, target)
                    .map_err(anyhow::Error::msg)?
            );
        }
        Query::Unpack => {
            let a = s.analysis(Feature::Emulate)?;
            let spec = arg(args, 2, "unpack needs an address")?;
            match args.get(3) {
                Some(out) => {
                    let (at, budget) = render::unpack_start(&s.program, &a, &s.overlay, spec)
                        .map_err(anyhow::Error::msg)?;
                    let (bytes, oep, truncated) = render::unpacked_image(&s.program, at, budget)
                        .context("nothing was materialized inside the file")?;
                    write_file(out, &bytes)?;
                    let entry_note = oep.map_or_else(String::new, |e| {
                        format!("; the run reached its original entry at {e:#x}")
                    });
                    let partial_note = if truncated {
                        "; the step budget ran out, so the image may be partial \u{2014} pass a larger budget= (e.g. 0x...,budget=200000000) for a fuller dump"
                    } else {
                        ""
                    };
                    println!(
                        "wrote {} bytes to {}{entry_note}{partial_note}",
                        bytes.len(),
                        short_path(out)
                    );
                }
                None => print!(
                    "{}",
                    render::unpack_tsv(&s.program, &a, &s.overlay, spec)
                        .map_err(anyhow::Error::msg)?
                ),
            }
        }
        Query::Oracle => {
            let a = s.analysis(Feature::Emulate)?;
            let what = arg(args, 2, "oracle needs an address or name")?;
            print!(
                "{}",
                render::oracle_tsv(&s.program, &a, &s.overlay, what).map_err(anyhow::Error::msg)?
            );
        }
        Query::Emulate => {
            let a = s.analysis(Feature::Emulate)?;
            let what = arg(args, 2, "emulate needs an address or name")?;
            print!(
                "{}",
                render::emulate_tsv(&s.program, &a, &s.overlay, what)
                    .map_err(anyhow::Error::msg)?
            );
        }
        Query::Run => {
            let a = s.analysis(Feature::Emulate)?;
            let what = arg(args, 2, "run needs <function>/<input>[;<input>...]")?;
            print!(
                "{}",
                render::run_tsv(&s.program, &a, &s.overlay, what).map_err(anyhow::Error::msg)?
            );
        }
        Query::Hidden => {
            let a = s.analysis(Feature::Emulate)?;
            let filter = args.get(2).map_or("", String::as_str);
            print!(
                "{}",
                render::hidden_strings_tsv(&s.program, &a, &s.overlay, filter)
            );
        }
        Query::Read => {
            let off = args.get(2).and_then(|t| parse_off(t));
            let start = match off {
                Some(off) => off,
                None => s.address(arg(args, 2, "read needs an address")?)?,
            };
            let kind_text = args.get(3).map_or("u64", String::as_str);
            let kind = memory::Kind::parse(kind_text).with_context(|| {
                format!(
                    "unknown kind {}; use one of: {}",
                    quoted(kind_text),
                    memory::Kind::NAMES
                )
            })?;
            let count: usize = num_arg(args, 4, 1, "read count")?;
            if count == 0 {
                bail!("read count must be at least 1");
            }
            let count = count.min(256);
            let (values, place) = match off {
                Some(off) => (
                    memory::read_values_at_offset(&s.program, off, kind, count),
                    "off:",
                ),
                None => (memory::read_values(&s.program, start, kind, count), ""),
            };
            let values = values.map_err(anyhow::Error::msg)?;
            if values.len() < count {
                let next = values
                    .last()
                    .map_or(start, |v| v.at.wrapping_add(num::from_usize(v.size)));
                println!(
                    "# {} of {count} {kind_text}: nothing readable at {place}{next:#x}",
                    values.len()
                );
            }
            for v in &values {
                println!("{:<12} {}", format!("{:#x}", v.at), v.text);
            }
        }
        Query::Fingerprint => {
            let a = s.analysis(Feature::Discover)?;
            let text = render::fingerprint_tsv(&a);
            match args.get(2) {
                Some(out) => {
                    write_file(out, text.as_bytes())?;
                    println!(
                        "wrote {} fingerprints to {} ({} bytes); borer://diff/{} reads it",
                        a.functions.len(),
                        short_path(out),
                        text.len(),
                        short_path(out)
                    );
                }
                None => print!("{text}"),
            }
        }
        Query::Export => {
            let (out, library) = export_args(args)?;
            writable(out)?;
            let a = s.analysis(Feature::Decompile)?;
            crate::term::busy(
                &format!(
                    "decompiling {} functions into {}",
                    a.functions.len(),
                    short_path(out)
                ),
                &[],
            );
            let written = borer::export::write_c(&s.program, &a, &s.overlay, library, out)?;
            println!("{}", written.line(out));
        }
        Query::ExportPack => {
            let name = args
                .get(2)
                .filter(|n| !n.is_empty() && !n.contains(char::is_whitespace))
                .context("export-pack needs a pack name, one word")?;
            let mut overlay = Overlay::default();
            let mut all = false;
            for extra in args.iter().skip(3) {
                if extra == "all" {
                    all = true;
                } else {
                    overlay = borer::project::ProjectFile::load(extra)
                        .and_then(|pf| pf.to_overlay())
                        .map_err(anyhow::Error::msg)?;
                }
            }
            let a = s.analysis(Feature::Decompile)?;
            print!("{}", sigs::export_pack(&s.program, &a, &overlay, name, all));
        }
        Query::Script => {
            let file = path_arg(args, 2, "script needs a script file")?;
            let code = std::fs::read_to_string(file)
                .with_context(|| format!("reading {}", short_path(file)))?;
            let mut words = Vec::new();
            let mut save = None;
            let mut rest = args.iter().skip(3);
            while let Some(w) = rest.next() {
                if w == "--save" {
                    save = Some(rest.next().context("--save needs a project file")?.clone());
                } else {
                    words.push(w.clone());
                }
            }
            if let Some(why) = s.program.refuses(Feature::Disasm) {
                bail!("{why}");
            }
            let a = s.analysis_or_empty();
            let run = script::run(
                Arc::clone(&s.program),
                Arc::new(a),
                Arc::default(),
                &code,
                &words,
            )
            .map_err(|e| anyhow::anyhow!("{}: {e}", short_path(file)))?;
            print!("{}", script::run_tsv(&run));
            if let Some(path) = save {
                let mut overlay = Overlay::default();
                overlay.names.extend(run.names.iter().cloned());
                overlay.comments.extend(run.comments.iter().cloned());
                borer::project::ProjectFile::from_overlay(
                    &s.program.path.display().to_string(),
                    Some(borer::project::identity(&s.program.bytes)),
                    &overlay,
                )
                .save(&path)
                .map_err(anyhow::Error::msg)?;
                eprintln!(
                    "borer: saved {} names and {} comments to {}",
                    overlay.names.len(),
                    overlay.comments.len(),
                    short_path(&path)
                );
            }
        }
        Query::Scenario => {
            let a = s.analysis(Feature::Decompile)?;
            let va = s.resolve(&a, arg(args, 2, "scenario needs a function")?)?;
            let assume = decompile::parse_scenario(arg(
                args,
                3,
                "scenario needs assumptions, such as a2=5",
            )?)
            .map_err(anyhow::Error::msg)?;
            let entry = entry_at(&s.program, &a, va)?;
            let text = decompile::decompile_scenario(&s.program, &a, &s.overlay, entry, &assume)
                .context("the function does not decompile")?;
            print!("{text}");
        }
        Query::Scenarios => {
            let a = s.analysis(Feature::Decompile)?;
            let va = s.resolve(&a, arg(args, 2, "scenarios needs a function")?)?;
            let (slot, values) = decompile::parse_explosion(arg(
                args,
                3,
                "scenarios needs a parameter and values, such as a2=0..32",
            )?)
            .map_err(anyhow::Error::msg)?;
            let entry = entry_at(&s.program, &a, va)?;
            let cases = decompile::explode(&s.program, &a, &s.overlay, entry, slot, &values);
            print!("{}", decompile::explode_tsv(&cases, slot, values.len()));
        }
        Query::Types => {
            let mut overlay = Overlay::default();
            if let Some(project) = args.get(2).filter(|p| !p.is_empty()) {
                overlay = borer::project::ProjectFile::load(project)
                    .and_then(|pf| pf.to_overlay())
                    .map_err(anyhow::Error::msg)?;
            }
            let filter = args
                .get(3)
                .map(|f| f.to_lowercase())
                .filter(|f| !f.is_empty());
            let (offset, limit) = cli_page(args, 4, 50, utypes::TYPES_ROWS_MAX)?;
            let stated = borer_engine::analysis::protos::rows(&overlay.prototypes, &overlay.vars);
            let (_, _, table) = utypes::list_tsv(
                &overlay.types,
                &overlay.applied,
                &stated,
                filter.as_deref(),
                offset,
                limit,
            );
            print!("{table}");
        }
        Query::SetType => {
            let project = path_arg(args, 2, "set-type needs a project file")?;
            let word: u64 = if s.program.is_64 { 8 } else { 4 };
            let (program, sha256, mut overlay) = if std::path::Path::new(project).exists() {
                let pf = borer::project::ProjectFile::load(project).map_err(anyhow::Error::msg)?;
                let overlay = pf.to_overlay().map_err(anyhow::Error::msg)?;
                (pf.program, pf.sha256, overlay)
            } else {
                (
                    s.program.path.display().to_string(),
                    Some(borer::project::identity(&s.program.bytes)),
                    Overlay::default(),
                )
            };
            let mut say = String::new();
            match arg(args, 3, "set-type needs struct, enum, typedef or apply")? {
                "struct" => {
                    let name = arg(args, 4, "set-type struct needs a name")?;
                    let mut at = 5;
                    let size = args
                        .get(at)
                        .filter(|a| !a.contains(':'))
                        .and_then(|a| parse_addr(a));
                    if size.is_some() {
                        at += 1;
                    }
                    let mut stated: Vec<(u64, String, utypes::TypeExpr)> = Vec::new();
                    for spec in args.iter().skip(at) {
                        let mut parts = spec.splitn(3, ':');
                        let (Some(off), Some(field), Some(ty)) =
                            (parts.next(), parts.next(), parts.next())
                        else {
                            bail!("field {} is not off:name:type", one_line(spec));
                        };
                        let off = parse_addr(off).with_context(|| {
                            format!(
                                "field {}'s offset {} is not a number",
                                one_line(field),
                                one_line(off)
                            )
                        })?;
                        let ty = utypes::parse_type(ty)
                            .with_context(|| format!("field {}'s type", one_line(field)))?;
                        stated.push((off, field.to_owned(), ty));
                    }
                    if stated.is_empty() {
                        bail!(
                            "struct {} states no fields; give them as off:name:type",
                            one_line(name)
                        );
                    }
                    let built = utypes::build_struct(name, size, &stated, &overlay.types, word)
                        .map_err(anyhow::Error::msg)?;
                    if let utypes::UserType::Struct(s) = &built {
                        let _ = write!(
                            say,
                            "defined struct {name}: {} field(s), {:#x} byte(s)",
                            s.fields.len(),
                            s.size
                        );
                    }
                    overlay.types.insert(name.to_owned(), built);
                }
                "enum" => {
                    let name = arg(args, 4, "set-type enum needs a name")?;
                    let mut at = 5;
                    let size = args
                        .get(at)
                        .filter(|a| !a.contains(':'))
                        .and_then(|a| parse_addr(a));
                    if size.is_some() {
                        at += 1;
                    }
                    let mut stated: Vec<(u64, String)> = Vec::new();
                    for spec in args.iter().skip(at) {
                        let Some((value_name, value)) = spec.split_once(':') else {
                            bail!("value {} is not name:value", one_line(spec));
                        };
                        let value = parse_addr(value).with_context(|| {
                            format!(
                                "value {}: {} is not a number",
                                one_line(value_name),
                                one_line(value)
                            )
                        })?;
                        stated.push((value, value_name.to_owned()));
                    }
                    if stated.is_empty() {
                        bail!(
                            "enum {} states no values; give them as name:value",
                            one_line(name)
                        );
                    }
                    let built = utypes::build_enum(name, size.unwrap_or(4), &stated)
                        .map_err(anyhow::Error::msg)?;
                    if let utypes::UserType::Enum(e) = &built {
                        let _ = write!(
                            say,
                            "defined enum {name}: {} value(s), {:#x} byte(s)",
                            e.values.len(),
                            e.size
                        );
                    }
                    overlay.types.insert(name.to_owned(), built);
                }
                "typedef" => {
                    let name = arg(args, 4, "set-type typedef needs a name")?;
                    let spelled = arg(args, 5, "set-type typedef needs the type it stands for")?;
                    let ty = utypes::parse_type(spelled).map_err(anyhow::Error::msg)?;
                    let built = utypes::build_alias(name, &ty, &overlay.types, word)
                        .map_err(anyhow::Error::msg)?;
                    let _ = write!(say, "defined typedef {name}: {}", ty.spell());
                    overlay.types.insert(name.to_owned(), built);
                }
                "apply" => {
                    let text = arg(args, 4, "set-type apply needs an address or name")?;
                    let spelled = arg(args, 5, "set-type apply needs the type to apply")?;
                    let ty = utypes::parse_type(spelled).map_err(anyhow::Error::msg)?;
                    let a = s.analysis(Feature::Discover)?;
                    let va = s.resolve(&a, text)?;
                    crate::params::must_be_in_a_section(
                        &s.program,
                        va,
                        crate::params::Annotation::Type,
                    )
                    .map_err(anyhow::Error::msg)?;
                    if let Some(f) = a.function_at(va) {
                        bail!(
                            "{va:#x} is inside {}; types apply to data globals",
                            name_of(&a, &s.overlay, f.entry)
                        );
                    }
                    let width = utypes::width_of(&overlay.types, &ty, word).ok_or_else(|| {
                        anyhow!(
                            "the type {} names nothing defined; set-type struct or enum first",
                            ty.spell()
                        )
                    })?;
                    let renders = if utypes::named_enum(&overlay.types, &ty).is_some() {
                        "names its values"
                    } else {
                        "names its fields"
                    };
                    let _ = write!(
                        say,
                        "applied {} at {va:#x} ({width} byte(s)); decompile {renders}",
                        ty.spell()
                    );
                    overlay.applied.insert(va, ty);
                }
                other => bail!(
                    "set-type takes struct, enum, typedef or apply, not {}",
                    one_line(other)
                ),
            }
            borer::project::ProjectFile::from_overlay(&program, sha256, &overlay)
                .save(project)
                .map_err(anyhow::Error::msg)?;
            println!("{say}; written to {}", short_path(project));
        }
        Query::Verify => {
            let text = args.get(5).is_some_and(|m| m == "text");
            let mir = args.get(5).is_some_and(|m| m == "mir");
            let a64 = !text && s.program.arch.isa() == Some(Isa::A64);
            let a = s.analysis(if a64 {
                Feature::Discover
            } else {
                Feature::Decompile
            })?;
            let which = args
                .get(2)
                .map(String::as_str)
                .filter(|w| !w.is_empty() && *w != "all");
            let limit: usize = match args.get(3).filter(|l| !l.is_empty()) {
                Some(l) => l.parse().context("the limit is a number")?,
                None => 2000,
            };
            let seed: u64 = match args.get(4).filter(|l| !l.is_empty()) {
                Some(l) => l.parse().context("the seed is a number")?,
                None => 1,
            };
            let entries: Vec<u64> = match which {
                None => a
                    .functions
                    .iter()
                    .filter(|f| f.thunk.is_none() && f.funclet.is_none())
                    .map(|f| f.entry)
                    .take(limit)
                    .collect(),
                Some(which) => vec![entry_at(&s.program, &a, s.resolve(&a, which)?)?],
            };
            if text {
                let r = decompile::replay::replay(&s.program, &a, &entries, seed);
                print!("{}", decompile::replay::replay_tsv(&r));
                if !r.wrong().is_empty() {
                    bail!("the text and the emulator disagree; see the table above");
                }
                return Ok(());
            }
            if a64 {
                let v = if mir {
                    decompile::verify_a64::verify_mir(&s.program, &a, &entries, seed)
                } else {
                    decompile::verify_a64::verify(&s.program, &a, &entries, seed)
                };
                print!("{}", decompile::verify_a64::verify_tsv(&v));
                if !v.mismatches.is_empty() {
                    bail!("the lifter and the emulator disagree; see the table above");
                }
                return Ok(());
            }
            let v = if mir {
                decompile::verify::verify_mir(&s.program, &a, &entries, seed)
            } else {
                decompile::verify::verify(&s.program, &a, &entries, seed)
            };
            print!("{}", decompile::verify::verify_tsv(&v));
            if !v.mismatches.is_empty() {
                bail!("the lifter and the emulator disagree; see the table above");
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::Overlay;
    use borer_engine::program::{Arch, Program, Section};

    use super::{Query, Session, USAGE, command_usage, decompiled};

    /// A command line: the command, a binary, then `rest`.
    ///
    /// # Arguments
    ///
    /// * `command` - The command word.
    /// * `rest` - The arguments after the binary.
    fn line(command: &str, rest: &[&str]) -> Vec<String> {
        [command, "x"]
            .iter()
            .chain(rest)
            .map(|w| (*w).to_owned())
            .collect()
    }

    /// A session over one function at 0x1000 of `stores` stores through
    /// its first argument, one pseudo-C line each.
    ///
    /// # Arguments
    ///
    /// * `stores` - The stores the function makes before it returns.
    ///
    /// # Panics
    ///
    /// When the code does not fit a `u64` size.
    fn session(stores: u32) -> Session {
        let mut code = Vec::new();
        for n in 0..stores {
            code.extend_from_slice(&[0xc7, 0x81]); // ASM: mov dword [rcx+disp32],imm32
            code.extend_from_slice(&(n * 4).to_le_bytes());
            code.extend_from_slice(&n.to_le_bytes());
        }
        code.push(0xc3); // ASM: ret
        let size = u64::try_from(code.len()).expect("fits");
        let text = Section::mapped(".text", 0x1000, 0, size, false, true);
        Session {
            program: Arc::new(Program::raw(
                code,
                Arch::X86_64,
                0,
                Some(0x1000),
                vec![text],
            )),
            packs: Arc::default(),
            overlay: Overlay::default(),
        }
    }

    /// `decompile` pages a long function as the `decompile` tool does: 300
    /// lines under a `// showing` line, an offset and a limit after the
    /// function (zero for every line), and a short one untouched.
    ///
    /// # Panics
    ///
    /// When a page differs from the tool's.
    #[test]
    fn decompile_pages_a_long_function_as_the_tool_does() {
        let s = session(400);
        let page = decompiled(&line("decompile", &["0x1000"]), &s).expect("decompiles");
        let head = page.lines().next().unwrap_or_default();
        assert!(head.starts_with("// showing 300 of "), "{head}");
        assert_eq!(page.lines().count(), 301, "{head}");
        let next = decompiled(&line("decompile", &["0x1000", "300", "5"]), &s).expect("pages");
        let head = next.lines().next().unwrap_or_default();
        assert!(
            head.starts_with("// showing 5 of ") && head.contains(" lines from 300"),
            "{head}"
        );
        let all = decompiled(&line("decompile", &["0x1000", "full", "", "0"]), &s).expect("all");
        let total: usize = head
            .strip_prefix("// showing 5 of ")
            .and_then(|r| r.split(' ').next())
            .and_then(|n| n.parse().ok())
            .expect("a total");
        assert_eq!(all.lines().count(), total, "every line, untouched");
        let short = session(3);
        let whole = decompiled(&line("decompile", &["0x1000"]), &short).expect("decompiles");
        assert!(!whole.contains("// showing"), "{whole}");
        let bad =
            decompiled(&line("decompile", &["0x1000", "outline"]), &s).expect_err("not a detail");
        assert!(bad.to_string().starts_with("unknown detail"), "{bad}");
        let bad =
            decompiled(&line("decompile", &["0x1000", "full", "x"]), &s).expect_err("not a number");
        assert_eq!(bad.to_string(), "decompile offset 'x' is not a number");
    }

    /// The vm and devirt words parse, and each carries its own usage lines.
    ///
    /// `borer help <word>` prints the one command's usage, and a word with
    /// no line there falls back to the whole text, which reads as a refusal
    /// of a command that exists.
    ///
    /// # Panics
    ///
    /// When a word does not parse or names no line of the usage text.
    #[test]
    fn vm_and_devirt_parse_and_have_usage_lines() {
        assert_eq!(Query::parse("vm"), Some(Query::Vm));
        assert_eq!(Query::parse("devirt"), Some(Query::Devirt));
        for word in ["vm", "devirt"] {
            let usage = command_usage(USAGE, word)
                .unwrap_or_else(|| panic!("{word} has no line in the usage text"));
            assert!(usage.contains(word), "{word}: {usage}");
        }
    }

    /// `export` reads `--c <out.c>` and `--library`, and refuses a line
    /// without the file or with another word.
    ///
    /// # Panics
    ///
    /// When a line reads otherwise.
    #[test]
    fn export_reads_its_file_and_library_flag() {
        use super::export_args;
        use borer_engine::analysis::decompile::export::Library;
        assert_eq!(Query::parse("export"), Some(Query::Export));
        assert!(command_usage(USAGE, "export").is_some());
        let both = line("export", &["--c", "a.c", "--library"]);
        let (out, library) = export_args(&both).expect("reads");
        assert_eq!((out, library), ("a.c", Library::Include));
        let plain = line("export", &["--c", "a.c"]);
        let (_, library) = export_args(&plain).expect("reads");
        assert_eq!(library, Library::Skip);
        let missing = export_args(&line("export", &["--library"])).expect_err("no file");
        assert!(missing.to_string().contains("--c <out.c>"), "{missing}");
        let other = export_args(&line("export", &["--c", "a.c", "b"])).expect_err("a stray word");
        assert!(other.to_string().contains("'b'"), "{other}");
    }
}
