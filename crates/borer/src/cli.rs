//! The one-shot command line: `borer <command> <binary> [args...]` runs one
//! query against the same engine the MCP server uses and prints a
//! context-window-sized answer.

use std::fmt::Write as _;
use std::sync::Arc;

use anyhow::{Context as _, anyhow, bail};
use borer_engine::analysis::{
    Analysis, Overlay, about, anchors, attributes, classes, decompile, encode, fieldrefs, libnames,
    map, messages, name_of, parse_addr, parse_off, ports, protocol, render, resolve_suggesting,
    schema, senders, sigs, snapshot, utypes, vtables,
};
use borer_engine::isa::Isa;
use borer_engine::layout::{self, Layout};
use borer_engine::pack::{Pack, Packs};
use borer_engine::program::{Feature, Program};
use borer_engine::table::Window;
use borer_engine::text::{one_line, quoted, short_path};
use borer_engine::{disasm, entropy, hexdump as hexfmt, libsig, memory, script, search};

use super::{
    entropy_threshold, env_pack_files, marked, parse_field_offset, read_packs, render_hits,
    strings_page, walk_rows, window,
};
use crate::params::{Detail, Filter, SearchKind, StringEncoding};
use crate::resources::ABOUT_NEEDS_A_NAME;

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
  export-pack <binary> <name> [project] [all]the names a project file gave (and with all, the names borer recovered) as a pack that finds the same functions in another build by their first bytes
  sigmake <out> <name> <library>...         the functions of static libraries or objects (.lib, .obj, .a, .o, Rust .rlib) as a pack of signatures, the relocated bytes masked, that names them in any program linked with them
  script <binary> <file> [args...]           run a Rhai script in a sandbox: it reads functions, strings, bytes and xrefs, prints, and proposes names and comments; --save <project> writes them for export-pack
  scenario <binary> <function> <a2=5,...>    decompile under assumptions: branches and switches on the fixed parameters fold and only the code that can run is written
  scenarios <binary> <function> <a2=0..32>   a scenario per value of one parameter (a range, or values joined by |), the ones that behave alike grouped with their calls and returns
  types <binary> [project] [filter] [offset] [limit]  user-defined types a project states and where each is applied (50 a page, max 500; \"\" for no filter)
  set-type <binary> <project> struct <name> [size] <off:name:type>...  define a struct in the project; or set-type <binary> <project> enum <name> [size] <name:value>...; or set-type <binary> <project> typedef <name> <type>; or set-type <binary> <project> apply <address|name> <type>, so decompile names that global's fields or constants
  verify <binary> [function|all] [limit] [seed]check the lifter against the emulator (arm64 code against the arm64 machine) block by block from seeded states; lists every register, stack slot, store and branch they disagree on and fails if any (default all, 2000 functions)
  verify <binary> <function|all> <limit> <seed> text  check the text's statements instead (x86 and x64 only): each block's, replayed under the lifter's witness, against the emulator from three seeded states; lists every claim the machine does not bear out and fails on any but lane roughness
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

/// A command word, by what it needs before it runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Command {
    /// `pack-keys`: every key a pack can set; no binary.
    PackKeys,
    /// `pack <file>`: a pack's report for its author; no binary.
    Pack,
    /// `sigmake <out> <name> <library>...`: a signature pack from libraries; no binary.
    Sigmake,
    /// `packs <binary>`: which packs fit, before any is loaded.
    Packs,
    /// `doctor [offline]`: the local setup, one line per item; no binary.
    Doctor,
    /// `setup [--apply]`: register this binary with the installed agent
    /// clients; no binary.
    Setup,
    /// `update [--check]`: install the latest release over this binary; no binary.
    Update,
    /// `fetch-pdb <binary> [server]`: fetch the companion PDB the debug
    /// record names; no query.
    FetchPdb,
    /// Everything else: a query against the binary with the packs that fit it.
    Query(Query),
}

impl Command {
    /// Parses a command word.
    ///
    /// # Arguments
    ///
    /// * `word` - The first argument after the options.
    ///
    /// # Returns
    ///
    /// The command, or `None` when no command has that word.
    fn parse(word: &str) -> Option<Self> {
        Some(match word {
            "pack-keys" => Self::PackKeys,
            "pack" => Self::Pack,
            "sigmake" => Self::Sigmake,
            "packs" => Self::Packs,
            "doctor" => Self::Doctor,
            "setup" => Self::Setup,
            "update" => Self::Update,
            "fetch-pdb" => Self::FetchPdb,
            query => Self::Query(Query::parse(query)?),
        })
    }

    /// The most arguments the command reads after its word, or after the
    /// binary for a query, as the usage text lists them.
    ///
    /// Some commands ignored what came after the arguments they read and
    /// others refused it, so `info x junk` answered as if `junk` were not
    /// there while `index x junk` was an error.
    ///
    /// # Returns
    ///
    /// The count, or `None` for a command that reads any number
    /// (`sigmake`, `script`, `set-type`).
    fn most_args(self) -> Option<usize> {
        match self {
            Self::PackKeys => Some(0),
            Self::Pack | Self::Packs | Self::Doctor | Self::Setup | Self::Update => Some(1),
            Self::FetchPdb => Some(2),
            Self::Sigmake => None,
            Self::Query(q) => q.most_args(),
        }
    }
}

/// A query against one binary, by its command word; the order is the usage text's.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Query {
    /// `info`: format, arch, sections, symbols.
    Info,
    /// `functions [filter] [offset] [limit]`: the discovered functions, a page at a time.
    Functions,
    /// `function <address|name>`: one function's ranges, blocks and edges.
    Function,
    /// `summary <address|name>`: one-call function triage.
    Summary,
    /// `symbols [filter] [offset] [limit]`: imports, exports and locals, a page at a time.
    Symbols,
    /// `hexdump <address|name> [length]`: bytes at a virtual address or name.
    Hexdump,
    /// `entropy [threshold]`: high-entropy regions.
    Entropy,
    /// `search <pattern> [text|bytes] [offset]`: AOB hex with `??` wildcards, or a substring.
    Search,
    /// `fstrings <address|name>`: the string literals one function references.
    Fstrings,
    /// `findstr <filter>`: the functions referencing a matching string.
    Findstr,
    /// `disasm <address|name> [count]`: instructions at a virtual address or name.
    Disasm,
    /// `disasmfn <address|name>`: a whole function, block by block.
    Disasmfn,
    /// `decompile <address|name> [skeleton|full] [offset] [limit]`: structured
    /// pseudo-C, paged by line as the `decompile` tool pages it.
    Decompile,
    /// `class <class|method address>`: a class layout from its methods' field accesses.
    Class,
    /// `fieldrefs <offset> [filter] [skip] [limit]`: every instruction touching `[reg+offset]`.
    Fieldrefs,
    /// `vslot <slot> [filter] [limit]`: the classes whose virtual at a slot returns a constant.
    Vslot,
    /// `index`: decompile every function once into the cache `grep` reads.
    Index,
    /// `grep <text> [filter] [offset] [limit]`: pseudo-C lines containing the text program-wide.
    Grep,
    /// `schema <function|class>`: the record a deserializer reads off its stream.
    Schema,
    /// `schemas <slot> [filter] [limit]`: every class with a constant at a slot and the record it decodes.
    Schemas,
    /// `encode <function|class>`: what a serializer writes onto its stream.
    Encode,
    /// `encodes <slot> [filter] [limit]`: every class with a constant at a slot and what it encodes.
    Encodes,
    /// `senders <slot> [filter] [limit]`: every class with a constant at a slot and the functions constructing it.
    Senders,
    /// `protocol <slot> [filter] [limit]`: every class with a constant at a slot with its senders, handler, encoding and decoding.
    Protocol,
    /// `hooks <slot> [filter] [limit]`: every class with a constant at a slot with the addresses a binding hooks.
    Hooks,
    /// `shape <function> [limit]`: every function running the same code over other operands.
    Shape,
    /// `messages [filter] [limit]`: every class that registered a wire id.
    Messages,
    /// `about <name>`: everything known about one name from every table.
    About,
    /// `snapshot <out>`: the program's commands, layouts, attributes, routes and ids by stable name, to a file.
    Snapshot,
    /// `changes <snapshot>`: what changed since a snapshot.
    Changes,
    /// `map [namespace] [limit]`: the program's namespaces with their classes by role.
    Map,
    /// `attrs [filter] [limit]`: every typed attribute the program registers.
    Attrs,
    /// `ports [filter] [limit]`: every message every port accepts and its handler.
    Ports,
    /// `anchors <manifest>`: re-derive every pinned fact in a manifest; fails unless all held.
    Anchors,
    /// `xrefs <address|name>`: cross-references to an address.
    Xrefs,
    /// `cfg <address|name>`: a function's control-flow graph as mermaid.
    Cfg,
    /// `callgraph <address|name> [callers|callees]`: a callgraph as mermaid; a `callers` walk may start from an import or a data symbol, by what references it.
    Callgraph,
    /// `strings [filter] [offset] [limit]`: printable strings in both encodings, since an ASCII-only sweep misses every wide literal.
    Strings,
    /// `crypto`: known crypto and hash constants.
    Crypto,
    /// `qt`: Qt classes from moc metadata.
    Qt,
    /// `triage`: what it is, what it hides, where to read.
    Triage,
    /// `taint <addr>[,reg]`: follow a value forward.
    Taint,
    /// `layout <addr>[,reg]`: propose a struct from what a function does through a pointer.
    Layout,
    /// `why <address|name>`: what is at an address, and where each fact came from.
    Why,
    /// `solve <addr>[,aN]`: find an argument value that changes the answer.
    Solve,
    /// `partial <address>`: a counted loop comparing a few bits of a product.
    Partial,
    /// `flat [address]`: functions whose control flow was flattened into a switch.
    Flat,
    /// `vm [address]`: the VM dispatch loops found, or one loop's handlers.
    Vm,
    /// `devirt <address>[,budget=N,...]`: the virtual program a virtualized function runs.
    Devirt,
    /// `unpack <address>[,budget=N] [out]`: the unpacker's report, or with `out` the image it materialized written to a file, since a tool reads a file and an image inside one emulator run is only a report.
    Unpack,
    /// `oracle <address|name>`: run a checksum on the standard probe and name it.
    Oracle,
    /// `emulate <spec>`: run code and read it back.
    Emulate,
    /// `run <function>/<inputs>`: call a function on typed inputs and check its text on them.
    Run,
    /// `hidden [filter]`: strings the program generates instead of storing.
    Hidden,
    /// `read <address|name> [kind] [count]`: typed values.
    Read,
    /// `fingerprint [out]`: one line per function, megabytes on a real client, so `out` writes the file beside a build that `borer://diff` reads.
    Fingerprint,
    /// `export-pack <name> [project] [all]`: the names a project file gave as a pack that finds the same functions in another build.
    ExportPack,
    /// `script <file> [args...]`: run a Rhai script in a sandbox; `--save <project>` writes its names and comments.
    Script,
    /// `scenario <function> <a2=5,...>`: decompile under assumptions.
    Scenario,
    /// `scenarios <function> <a2=0..32>`: a scenario per value of one parameter.
    Scenarios,
    /// `types [project] [filter] [offset] [limit]`: the user types a project states, and where each is applied.
    Types,
    /// `set-type <project> struct <name> [size] <off:name:type>... | enum <name> [size] <name:value>... | typedef <name> <type> | apply <address|name> <type>`: define or apply a user type, written to the project.
    SetType,
    /// `verify [function|all] [limit] [seed] [text]`: check the lifter, or with `text` the text's statements, against the emulator; fails on any disagreement.
    Verify,
}

impl Query {
    /// Parses a query's command word.
    ///
    /// # Arguments
    ///
    /// * `word` - The command word.
    ///
    /// # Returns
    ///
    /// The query, or `None` when no query has that word.
    fn parse(word: &str) -> Option<Self> {
        Some(match word {
            "info" => Self::Info,
            "functions" => Self::Functions,
            "function" => Self::Function,
            "summary" => Self::Summary,
            "symbols" => Self::Symbols,
            "hexdump" => Self::Hexdump,
            "entropy" => Self::Entropy,
            "search" => Self::Search,
            "fstrings" => Self::Fstrings,
            "findstr" => Self::Findstr,
            "disasm" => Self::Disasm,
            "disasmfn" => Self::Disasmfn,
            "decompile" => Self::Decompile,
            "class" => Self::Class,
            "fieldrefs" => Self::Fieldrefs,
            "vslot" => Self::Vslot,
            "index" => Self::Index,
            "grep" => Self::Grep,
            "schema" => Self::Schema,
            "schemas" => Self::Schemas,
            "encode" => Self::Encode,
            "encodes" => Self::Encodes,
            "senders" => Self::Senders,
            "protocol" => Self::Protocol,
            "hooks" => Self::Hooks,
            "shape" => Self::Shape,
            "messages" => Self::Messages,
            "about" => Self::About,
            "snapshot" => Self::Snapshot,
            "changes" => Self::Changes,
            "map" => Self::Map,
            "attrs" => Self::Attrs,
            "ports" => Self::Ports,
            "anchors" => Self::Anchors,
            "xrefs" => Self::Xrefs,
            "cfg" => Self::Cfg,
            "callgraph" => Self::Callgraph,
            "strings" => Self::Strings,
            "crypto" => Self::Crypto,
            "qt" => Self::Qt,
            "triage" => Self::Triage,
            "taint" => Self::Taint,
            "layout" => Self::Layout,
            "why" => Self::Why,
            "solve" => Self::Solve,
            "partial" => Self::Partial,
            "flat" => Self::Flat,
            "vm" => Self::Vm,
            "devirt" => Self::Devirt,
            "unpack" => Self::Unpack,
            "oracle" => Self::Oracle,
            "emulate" => Self::Emulate,
            "run" => Self::Run,
            "hidden" => Self::Hidden,
            "read" => Self::Read,
            "fingerprint" => Self::Fingerprint,
            "export-pack" => Self::ExportPack,
            "script" => Self::Script,
            "scenario" => Self::Scenario,
            "scenarios" => Self::Scenarios,
            "types" => Self::Types,
            "set-type" => Self::SetType,
            "verify" => Self::Verify,
            _ => return None,
        })
    }

    /// The most arguments the query reads after the binary, as the usage
    /// text lists them ([`Command::most_args`]).
    ///
    /// # Returns
    ///
    /// The count, or `None` for a query that reads any number.
    fn most_args(self) -> Option<usize> {
        Some(match self {
            Self::Info | Self::Index | Self::Crypto | Self::Qt | Self::Triage => 0,
            Self::Function
            | Self::Summary
            | Self::Entropy
            | Self::Fstrings
            | Self::Findstr
            | Self::Disasmfn
            | Self::Class
            | Self::Schema
            | Self::Encode
            | Self::About
            | Self::Snapshot
            | Self::Changes
            | Self::Anchors
            | Self::Xrefs
            | Self::Cfg
            | Self::Taint
            | Self::Layout
            | Self::Why
            | Self::Solve
            | Self::Partial
            | Self::Flat
            | Self::Vm
            | Self::Devirt
            | Self::Oracle
            | Self::Emulate
            | Self::Run
            | Self::Hidden
            | Self::Fingerprint => 1,
            Self::Hexdump
            | Self::Disasm
            | Self::Shape
            | Self::Messages
            | Self::Map
            | Self::Attrs
            | Self::Ports
            | Self::Callgraph
            | Self::Unpack
            | Self::Scenario
            | Self::Scenarios => 2,
            Self::Functions
            | Self::Search
            | Self::Vslot
            | Self::Schemas
            | Self::Encodes
            | Self::Senders
            | Self::Protocol
            | Self::Hooks
            | Self::Strings
            | Self::Symbols
            | Self::Read
            | Self::ExportPack => 3,
            Self::Decompile | Self::Fieldrefs | Self::Grep | Self::Types | Self::Verify => 4,
            Self::Script | Self::SetType => return None,
        })
    }
}

/// Which way `callgraph` walks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
enum Direction {
    /// What the function calls.
    #[default]
    Callees,
    /// What reaches the function.
    Callers,
}

impl Direction {
    /// Parses `callgraph`'s direction word.
    ///
    /// # Arguments
    ///
    /// * `word` - `callers`, `callees` or nothing.
    ///
    /// # Errors
    ///
    /// For any other word.
    fn parse(word: Option<&str>) -> anyhow::Result<Self> {
        match word {
            None | Some("callees") => Ok(Self::Callees),
            Some("callers") => Ok(Self::Callers),
            Some(other) => bail!(
                "unknown direction {}: use callers, callees, or nothing",
                quoted(other)
            ),
        }
    }
}

/// Parses `decompile`'s detail word into the server's [`Detail`].
///
/// # Arguments
///
/// * `word` - `skeleton`, `full` or nothing.
///
/// # Errors
///
/// For any other word.
fn detail(word: Option<&str>) -> anyhow::Result<Detail> {
    match word {
        None | Some("full") => Ok(Detail::Full),
        Some("skeleton") => Ok(Detail::Skeleton),
        Some(other) => bail!(
            "unknown detail {}: use skeleton, full, or nothing",
            quoted(other)
        ),
    }
}

/// Reads `decompile`'s words after the function: an optional detail word,
/// then the line to start from and the lines to show, as the `decompile`
/// tool's `offset` and `limit` page.
///
/// A word that is a number opens the page, so `decompile <binary> f 300`
/// reads the second page; an empty word is the default.
///
/// # Arguments
///
/// * `words` - The arguments after the function.
///
/// # Returns
///
/// The detail, the offset and the limit; zero for the limit is every line.
///
/// # Errors
///
/// For a first word that is neither a detail word nor a number, or an
/// offset or limit that is not a number.
fn decompile_args(words: &[String]) -> anyhow::Result<(Detail, Option<u32>, Option<u32>)> {
    let paging = |w: &String| w.is_empty() || w.parse::<u32>().is_ok();
    let (detail, page) = match words.split_first() {
        Some((first, rest)) if !paging(first) => (detail(Some(first))?, rest),
        Some(_) | None => (Detail::Full, words),
    };
    let number = |i: usize, what: &str| -> anyhow::Result<Option<u32>> {
        page.get(i)
            .filter(|w| !w.is_empty())
            .map(|w| {
                w.parse::<u32>()
                    .map_err(|_| anyhow!("decompile {what} {} is not a number", quoted(w)))
            })
            .transpose()
    };
    Ok((detail, number(0, "offset")?, number(1, "limit")?))
}

/// Reads `search`'s words after the pattern: `text`, `bytes` or a page
/// offset, in any order.
///
/// `bytes` names the default and does not undo a `text` beside it; the
/// first number is the offset.
///
/// # Arguments
///
/// * `words` - The arguments after the pattern.
///
/// # Returns
///
/// What to search for, and where the page starts.
///
/// # Errors
///
/// For a word that is none of the three.
fn search_args(words: &[String]) -> anyhow::Result<(SearchKind, usize)> {
    let mut kind = SearchKind::Bytes;
    let mut offset = None;
    for word in words {
        match word.as_str() {
            "text" => kind = SearchKind::Text,
            "bytes" => {}
            other => match other.parse::<usize>() {
                Ok(n) => {
                    offset.get_or_insert(n);
                }
                Err(_) => bail!(
                    "search takes `text`, `bytes` or a page offset after the pattern, not {}",
                    quoted(other)
                ),
            },
        }
    }
    Ok((kind, offset.unwrap_or(0)))
}

/// Returns a positional argument.
///
/// # Arguments
///
/// * `args` - The command line, the command first and the binary second.
/// * `i` - The argument's index; a command's first argument is 2.
/// * `missing` - The error when the line is shorter, `<command> needs <what>`.
///
/// # Errors
///
/// With `missing`, when the line has no argument `i`.
fn arg<'a>(args: &'a [String], i: usize, missing: &'static str) -> anyhow::Result<&'a str> {
    args.get(i).map(String::as_str).context(missing)
}

/// Reads an optional numeric argument.
///
/// # Arguments
///
/// * `args` - The command line.
/// * `i` - The argument's index.
/// * `default` - The value when the line is shorter.
/// * `what` - The argument as the message names it, `<command> <argument>`.
///
/// # Errors
///
/// When the argument is not a number, naming it: the parser's own
/// `invalid digit found in string` did not say which argument it meant.
fn num_arg<T: std::str::FromStr>(
    args: &[String],
    i: usize,
    default: T,
    what: &str,
) -> anyhow::Result<T> {
    args.get(i).map_or(Ok(default), |s| {
        s.parse()
            .map_err(|_| anyhow::anyhow!("{what} {} is not a number", quoted(s)))
    })
}

/// Returns a positional argument that names a file, refusing an empty one.
///
/// An empty path reached the file system, whose message did not say the
/// path was empty.
///
/// # Arguments
///
/// * `args` - The command line.
/// * `i` - The argument's index.
/// * `missing` - The error when the line is shorter, `<command> needs <what>`.
///
/// # Errors
///
/// With `missing`, when the line has no argument `i` or it is empty.
fn path_arg<'a>(args: &'a [String], i: usize, missing: &'static str) -> anyhow::Result<&'a str> {
    let path = arg(args, i, missing)?;
    if path.is_empty() {
        bail!("{missing}; the path is empty");
    }
    Ok(path)
}

/// Reads a CLI listing's `[limit]` argument.
///
/// # Arguments
///
/// * `args` - The command line.
/// * `at` - Index of the limit argument.
/// * `default` - Rows when no limit is given.
/// * `max` - The cap on the limit.
///
/// # Errors
///
/// When the argument is not a number, or zero.
fn cli_limit(args: &[String], at: usize, default: usize, max: usize) -> anyhow::Result<usize> {
    let limit = match args.get(at).filter(|l| !l.is_empty()) {
        Some(l) => l
            .parse::<usize>()
            .with_context(|| format!("limit {} is not a number", quoted(l)))?,
        None => default,
    };
    if limit == 0 {
        bail!("limit must be at least 1");
    }
    Ok(limit.min(max))
}

/// Reads a CLI listing's `[offset] [limit]` arguments.
///
/// The MCP tools page; the CLI printed the first hundred and stopped, so
/// a filter with more matches could not be read to the end from a shell.
///
/// # Arguments
///
/// * `args` - The command line.
/// * `at` - Index of the offset argument; the limit follows it.
/// * `default` - Rows when no limit is given.
/// * `max` - The cap on the limit.
///
/// # Errors
///
/// When either argument is not a number, or the limit is zero.
fn cli_page(
    args: &[String],
    at: usize,
    default: usize,
    max: usize,
) -> anyhow::Result<(usize, usize)> {
    let offset = match args.get(at).filter(|o| !o.is_empty()) {
        Some(o) => o
            .parse::<usize>()
            .with_context(|| format!("offset {} is not a number", quoted(o)))?,
        None => 0,
    };
    Ok((offset, cli_limit(args, at + 1, default, max)?))
}

/// Reads a catalog's `[filter] [limit]` arguments, the two after the binary.
///
/// # Arguments
///
/// * `args` - The command line.
/// * `max` - The cap on the limit, and the limit when none is given.
///
/// # Errors
///
/// When the limit is not a number, or zero.
fn filter_limit(args: &[String], max: usize) -> anyhow::Result<(&str, usize)> {
    Ok((
        args.get(2).map_or("", String::as_str),
        cli_limit(args, 3, max, max)?,
    ))
}

/// The arguments of the commands that read a constant off a vtable slot:
/// `<slot> [filter] [limit]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SlotQuery<'a> {
    /// The zero-based vtable slot.
    slot: usize,
    /// A substring of the class name; empty keeps every class.
    filter: &'a str,
    /// Rows at most, 1 to [`CLASS_ROWS`].
    limit: usize,
}

impl<'a> SlotQuery<'a> {
    /// Reads the arguments after the binary.
    ///
    /// # Arguments
    ///
    /// * `args` - The command line.
    /// * `missing` - The error when no slot is given.
    ///
    /// # Errors
    ///
    /// When the slot is missing or not a number, or the limit is not a
    /// number or zero.
    fn parse(args: &'a [String], missing: &'static str) -> anyhow::Result<Self> {
        let slot = arg(args, 2, missing)?
            .parse()
            .context("the slot is a zero-based index")?;
        Ok(Self {
            slot,
            filter: args.get(3).map_or("", String::as_str),
            limit: cli_limit(args, 4, CLASS_ROWS, CLASS_ROWS)?,
        })
    }
}

/// Returns the entry of the discovered function containing an address.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - The analysis.
/// * `va` - The address.
///
/// # Errors
///
/// When no discovered function contains `va`, saying so of an import's
/// slot ([`borer_engine::analysis::function_entry`]).
fn entry_at(p: &Program, a: &Analysis, va: u64) -> anyhow::Result<u64> {
    borer_engine::analysis::function_entry(p, a, va).map_err(anyhow::Error::msg)
}

/// Writes a file for a command that was asked to produce one.
///
/// # Arguments
///
/// * `path` - Where to write, as the caller gave it.
/// * `bytes` - What to write.
///
/// # Errors
///
/// When the path names a device rather than a file, or the write fails.
fn write_file(path: &str, bytes: &[u8]) -> anyhow::Result<()> {
    writable(path)?;
    std::fs::write(path, bytes).with_context(|| format!("writing {}", short_path(path)))
}

/// Refuses a path that names a device rather than a file, before a
/// command spends an analysis on what it would write there.
///
/// # Arguments
///
/// * `path` - Where the command will write, as the caller gave it.
///
/// # Errors
///
/// When the path is empty or names a device (`NUL`, `CON`, `COM1`).
fn writable(path: &str) -> anyhow::Result<()> {
    if let Some(why) = borer_engine::program::unusable_path(std::path::Path::new(path)) {
        bail!("{why}; nothing was written");
    }
    Ok(())
}

/// Writes the functions of static libraries, objects or IDA `.pat` signature
/// files as a pack of library signatures: `sigmake <out> <name> <library>...`.
///
/// # Arguments
///
/// * `args` - The command line, the command first.
///
/// # Errors
///
/// When an argument is missing, a library cannot be read, is neither an
/// archive, an object nor an IDA `.pat` file, or gives no function while
/// members of it are damaged (each is named on stderr), or the pack cannot
/// be written.
fn sigmake(args: &[String]) -> anyhow::Result<()> {
    let out = arg(args, 1, "sigmake needs an output file")?;
    let name = args
        .get(2)
        .filter(|n| !n.is_empty() && !n.contains(char::is_whitespace))
        .context("sigmake needs a pack name, one word")?;
    let libraries = args
        .get(3..)
        .filter(|l| !l.is_empty())
        .context("sigmake needs at least one library or object")?;
    let mut functions = Vec::new();
    let mut files = Vec::new();
    for library in libraries {
        let bytes =
            std::fs::read(library).with_context(|| format!("reading {}", short_path(library)))?;
        let (found, damaged) = libsig::read(&bytes).with_context(|| short_path(library))?;
        for why in &damaged {
            eprintln!("borer: {}: {why}", short_path(library));
        }
        if found.is_empty() && !damaged.is_empty() {
            bail!(
                "{}: no function was read and {} member(s) are damaged (see above); nothing was written",
                short_path(library),
                damaged.len()
            );
        }
        println!("# {}: {} functions", short_path(library), found.len());
        functions.extend(found);
        files.push(
            std::path::Path::new(library)
                .file_name()
                .map_or_else(|| library.clone(), |f| f.to_string_lossy().into_owned()),
        );
    }
    let description = format!("the functions of {}", files.join(", "));
    let text = libsig::pack_text(name, &description, &functions);
    write_file(out, text.as_bytes())?;
    println!(
        "# wrote {}: {} signatures",
        short_path(out),
        text.lines().filter(|l| l.starts_with("lib ")).count()
    );
    Ok(())
}

/// Returns the usage lines of one command: every line that opens with its
/// name, as `help <cmd>` and `<cmd> --help` print it.
///
/// # Arguments
///
/// * `usage` - The whole usage text.
/// * `cmd` - The command's name.
///
/// # Returns
///
/// The lines under a `usage:` header, or `None` when no line names the command.
fn command_usage(usage: &str, cmd: &str) -> Option<String> {
    let lines: Vec<&str> = usage
        .lines()
        .filter(|l| {
            l.strip_prefix("  ")
                .is_some_and(|rest| rest.split_whitespace().next() == Some(cmd))
        })
        .collect();
    (!lines.is_empty()).then(|| format!("usage:\n{}", lines.join("\n")))
}

/// Splits `--pack <file>`, `--pack=<file>`, `--no-auto-packs` and
/// `--no-pdb` out of a command line.
///
/// # Arguments
///
/// * `args` - The command line after the program name.
///
/// # Returns
///
/// The other arguments in order, the pack files (`BORER_PACKS`'s first,
/// then the command line's), whether the pack directories' packs may load
/// by themselves, and whether a companion PDB may apply.
///
/// # Errors
///
/// When `--pack` ends the line with no file after it.
fn split_pack_args(args: &[String]) -> anyhow::Result<(Vec<String>, Vec<String>, bool, bool)> {
    let mut rest = Vec::with_capacity(args.len());
    let mut files = env_pack_files();
    let mut auto = borer::packs::auto_enabled();
    let mut pdb = true;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--no-pdb" {
            pdb = false;
        } else if a == "--no-auto-packs" {
            auto = false;
        } else if a == "--pack" {
            let file = it
                .next()
                .ok_or_else(|| anyhow::anyhow!("--pack needs a file"))?;
            files.push(file.clone());
        } else if let Some(file) = a.strip_prefix("--pack=") {
            files.push(file.to_owned());
        } else {
            rest.push(a.clone());
        }
    }
    Ok((rest, files, auto, pdb))
}

/// The raw layout flags of a command line, as given.
#[derive(Debug, Default)]
struct RawFlags {
    /// `--arch`: the architecture the bytes map as.
    arch: Option<String>,
    /// `--base`: where the whole file maps.
    base: Option<String>,
    /// `--entry`: the entry address.
    entry: Option<String>,
    /// `--regions`: the parts of the file mapped instead of the whole.
    regions: Option<String>,
}

impl RawFlags {
    /// Takes the layout flags (`--arch`, `--base`, `--entry`,
    /// `--regions`, each `--flag value` or `--flag=value`) out of a command
    /// line.
    ///
    /// # Arguments
    ///
    /// * `args` - The command line after the program name.
    ///
    /// # Returns
    ///
    /// The other arguments in order, and the flags.
    ///
    /// # Errors
    ///
    /// When a flag ends the line with no value after it, or is given twice.
    fn split(args: &[String]) -> anyhow::Result<(Vec<String>, RawFlags)> {
        let mut rest = Vec::with_capacity(args.len());
        let mut raw = RawFlags::default();
        let mut it = args.iter();
        while let Some(a) = it.next() {
            let (flag, inline) = a
                .split_once('=')
                .map_or((a.as_str(), None), |(f, v)| (f, Some(v)));
            let Some(slot) = raw.slot(flag) else {
                rest.push(a.clone());
                continue;
            };
            let value = match inline {
                Some(v) => v.to_owned(),
                None => it
                    .next()
                    .with_context(|| format!("{flag} needs a value"))?
                    .clone(),
            };
            if slot.replace(value).is_some() {
                bail!("{flag} is given twice");
            }
        }
        Ok((rest, raw))
    }

    /// Returns where a layout flag's value goes.
    ///
    /// # Arguments
    ///
    /// * `flag` - The flag as typed, before any `=`.
    ///
    /// # Returns
    ///
    /// The flag's slot, or `None` when the word is no layout flag.
    fn slot(&mut self, flag: &str) -> Option<&mut Option<String>> {
        match flag {
            "--arch" => Some(&mut self.arch),
            "--base" => Some(&mut self.base),
            "--entry" => Some(&mut self.entry),
            "--regions" => Some(&mut self.regions),
            _ => None,
        }
    }

    /// Reads the layout the flags state.
    ///
    /// # Returns
    ///
    /// `None` when no layout flag was given.
    ///
    /// # Errors
    ///
    /// As [`layout::parse_arch`] and [`Layout::parse`].
    fn layout(&self) -> anyhow::Result<Option<Layout>> {
        let arch = self.arch.as_deref().map(layout::parse_arch).transpose()?;
        Layout::parse(
            arch,
            self.base.as_deref(),
            self.entry.as_deref(),
            self.regions.as_deref(),
        )
    }
}

/// Describes a pack for its author: name, version, what it is about, its
/// lines counted by section and key, and the warnings about keys borer does
/// not read.
///
/// # Arguments
///
/// * `pack` - The pack.
/// * `warnings` - What reading it reported.
fn pack_report(pack: &Pack, warnings: &[String]) -> String {
    let mut counts: std::collections::BTreeMap<(&str, &str), usize> =
        std::collections::BTreeMap::new();
    for e in &pack.entries {
        *counts
            .entry((e.section.as_str(), e.key.as_str()))
            .or_default() += 1;
    }
    let mut out = format!(
        "# pack {} {}: {} lines in {} keys, {} warnings\n",
        pack.name,
        pack.version,
        pack.entries.len(),
        counts.len(),
        warnings.len()
    );
    if !pack.about.is_empty() {
        let _ = writeln!(out, "# {}", pack.about);
    }
    out.push_str("section\tkey\tlines\n");
    for ((section, key), n) in counts {
        let _ = writeln!(out, "{section}	{key}	{n}");
    }
    for w in warnings {
        let _ = writeln!(out, "# warning: {w}");
    }
    out
}

/// Lists the packs borer knows and whether each loads for a program, then
/// the names and scripts the loading ones give it.
///
/// # Arguments
///
/// * `program` - The program.
/// * `named` - The packs the command line and `BORER_PACKS` name.
/// * `auto` - Whether the pack directories' packs may load by themselves.
fn packs_report(program: &Program, named: &Packs, auto: bool) -> String {
    let mut out = borer::packs::listing(program, named, auto);
    let (loaded, _) = borer::packs::for_program(program, named, auto);
    let scripts = loaded.packs.iter().any(|p| !p.scripts.is_empty());
    let names = !loaded.list("names", "fn").is_empty() || !loaded.list("names", "lib").is_empty();
    if (scripts || names) && program.arch.supports(Feature::Discover) {
        let a = Analysis::compute_with(program, loaded);
        out.push_str(&sigs::pack_names_tsv(&a.pack_names));
        out.push_str(&libnames::library_names_tsv(&a.library_names));
        out.push_str(&script::pack_scripts_tsv(&a.pack_scripts));
    }
    out
}

/// The refusal of a command given no binary: what it needs, then its own
/// usage lines rather than every command's.
///
/// # Arguments
///
/// * `word` - The command word.
fn needs_a_binary(word: &str) -> String {
    format!(
        "{word} needs a binary path\n{}",
        command_usage(USAGE, word).unwrap_or_default()
    )
}

/// Reads the named packs and loads the binary the command line names.
///
/// # Arguments
///
/// * `args` - The command line, the command first and the binary second.
/// * `pack_files` - The pack files to read.
/// * `apply_pdb` - Whether a companion PDB's symbols may apply.
/// * `layout` - Where a raw file's bytes map; `None` reads its headers.
///
/// # Returns
///
/// The named packs and the loaded program.
///
/// # Errors
///
/// When a pack cannot be read, no binary is named, or it does not load.
fn open(
    args: &[String],
    pack_files: &[String],
    apply_pdb: bool,
    layout: Option<&Layout>,
) -> anyhow::Result<(Arc<Packs>, Program)> {
    let named = read_packs(pack_files)?;
    let path = args
        .get(1)
        .with_context(|| needs_a_binary(args.first().map_or("", String::as_str)))?;
    let file = std::path::Path::new(path);
    crate::term::busy(&format!("loading {}", file_name(file)), &head_bytes(file));
    let program = match layout {
        Some(layout) => Program::load_layout(file, layout),
        None => {
            let symsrv = crate::symsrv::cache_dir().filter(|_| apply_pdb);
            Program::load_with_symsrv(file, apply_pdb, symsrv.as_deref())
        }
    }
    .with_context(|| format!("loading {}", short_path(path)))?;
    Ok((named, program))
}

/// A file's name without its folder, for the loading line.
///
/// # Arguments
///
/// * `file` - The path.
fn file_name(file: &std::path::Path) -> String {
    file.file_name()
        .map_or_else(|| file.to_string_lossy(), |n| n.to_string_lossy())
        .into_owned()
}

/// The first bytes of a file, for the loading line to stream; none when it
/// cannot be read.
///
/// # Arguments
///
/// * `file` - The binary.
fn head_bytes(file: &std::path::Path) -> Vec<u8> {
    use std::io::Read as _;
    let mut head = Vec::with_capacity(256);
    if let Ok(f) = std::fs::File::open(file) {
        let _ = f.take(256).read_to_end(&mut head);
    }
    head
}

/// A binary with the packs that fit it, as every query reads it.
#[derive(Debug)]
struct Session {
    /// The loaded file.
    program: Arc<Program>,
    /// The packs the analysis runs with: the named ones, and the pack
    /// directories' that fit the program.
    packs: Arc<Packs>,
    /// The names and comments: none, the CLI reads no project file.
    overlay: Overlay,
}

impl Session {
    /// Fits the pack directories' packs to a program, saying on stderr
    /// which loaded.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded file.
    /// * `named` - The packs the command line and `BORER_PACKS` name.
    /// * `auto` - Whether the pack directories' packs may load by themselves.
    fn fit(program: Program, named: &Packs, auto: bool) -> Self {
        let (packs, notes) = borer::packs::for_program(&program, named, auto);
        for note in notes {
            eprintln!("borer: {note}");
        }
        Self {
            program: Arc::new(program),
            packs,
            overlay: Overlay::default(),
        }
    }

    /// Computes the analysis for a command that reads `feature` of the
    /// program's code.
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the command reads: [`Feature::Discover`] for
    ///   functions, blocks, references and calls, [`Feature::Decompile`]
    ///   for anything read from lifted code, [`Feature::Emulate`] for
    ///   anything that runs it.
    ///
    /// # Errors
    ///
    /// When the engine does not do `feature` with the architecture
    /// ([`Program::refuses`]).
    fn analysis(&self, feature: Feature) -> anyhow::Result<Analysis> {
        if let Some(why) = self.program.refuses(feature) {
            bail!("{why}");
        }
        crate::term::busy(&format!("analyzing {}", file_name(&self.program.path)), &[]);
        Ok(Analysis::compute_with(
            &self.program,
            Arc::clone(&self.packs),
        ))
    }

    /// Computes the analysis, or returns an empty one when borer cannot
    /// discover the architecture's functions.
    ///
    /// For facts of the file rather than of its code: the symbol table and
    /// a crypto constant are parsed or scanned without disassembling
    /// anything, and read the analysis only to say which function they
    /// belong to. Refusing them on an architecture borer cannot disassemble
    /// threw away what it had already read out of the headers.
    fn analysis_or_empty(&self) -> Analysis {
        self.analysis(Feature::Discover).unwrap_or_default()
    }

    /// Resolves an address or a name.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis.
    /// * `text` - `0x`-hex, decimal, or a function or symbol name.
    ///
    /// # Errors
    ///
    /// When the text is neither, naming the nearest names.
    fn resolve(&self, a: &Analysis, text: &str) -> anyhow::Result<u64> {
        resolve_suggesting(&self.program, a, &self.overlay, text).map_err(anyhow::Error::msg)
    }

    /// Resolves an address argument as the MCP tools do: `0x`-hex text
    /// at once, anything else as a name first (through the analysis when
    /// the architecture has one, else the symbols), then as a number.
    ///
    /// `disasm`, `hexdump` and `read` took numbers alone, where the tools
    /// of the same names take a function, an import or an export by name.
    ///
    /// # Arguments
    ///
    /// * `text` - The argument.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name.
    fn address(&self, text: &str) -> anyhow::Result<u64> {
        if borer_engine::analysis::hex_prefixed(text)
            && let Some(va) = parse_addr(text)
        {
            return Ok(va);
        }
        self.resolve(&self.analysis_or_empty(), text)
    }

    /// Computes the analysis and finds the function a positional argument
    /// names.
    ///
    /// # Arguments
    ///
    /// * `args` - The command line.
    /// * `i` - The argument's index.
    /// * `missing` - The error when the line is shorter.
    /// * `feature` - The stage the command reads ([`Session::analysis`]).
    ///
    /// # Returns
    ///
    /// The analysis and the function's entry.
    ///
    /// # Errors
    ///
    /// When the analysis cannot run, the argument is missing or does not
    /// resolve, or no discovered function contains it.
    fn function_arg(
        &self,
        args: &[String],
        i: usize,
        missing: &'static str,
        feature: Feature,
    ) -> anyhow::Result<(Analysis, u64)> {
        let a = self.analysis(feature)?;
        let va = self.resolve(&a, arg(args, i, missing)?)?;
        let entry = entry_at(&self.program, &a, va)?;
        Ok((a, entry))
    }
}

/// Answers `decompile <binary> <address|name> [skeleton|full] [offset]
/// [limit]`: the function's pseudo-C, paged by line as the `decompile`
/// tool pages it ([`window`]).
///
/// The CLI printed every line, 6,610 of them for one function of a
/// system program, where the tool shows 300 under a `// showing N of M`
/// line saying how to read the rest.
///
/// # Arguments
///
/// * `args` - The command line, the command first and the binary second.
/// * `s` - The binary with its packs.
///
/// # Returns
///
/// The page of pseudo-C to print.
///
/// # Errors
///
/// For a bad detail, offset or limit, a function argument that is missing
/// or names no function, or a function that does not decompile.
fn decompiled(args: &[String], s: &Session) -> anyhow::Result<String> {
    let (detail, offset, limit) = decompile_args(args.get(3..).unwrap_or_default())?;
    let (a, entry) = s.function_arg(
        args,
        2,
        "decompile needs an address or name",
        Feature::Decompile,
    )?;
    let raw = std::env::var_os("BORER_RAW").is_some();
    let header = (!raw)
        .then(|| decompile::checked_header(&s.program, &a, &s.overlay, entry))
        .flatten();
    let text = if raw {
        decompile::decompile_raw(&s.program, &a, &s.overlay, entry)
    } else {
        decompile::decompile_named(&s.program, &a, &s.overlay, entry)
    }
    .with_context(|| format!("decompilation failed at {entry:#x}"))?;
    let text = match detail {
        Detail::Skeleton => decompile::skeleton(&text),
        Detail::Full if raw => text,
        Detail::Full => marked(&s.program, &a, &s.overlay, entry, &text),
    };
    let text = decompile::with_header(&text, header.as_deref());
    Ok(window(&text, None, offset, limit))
}

/// The refusal of a word that names no command: an option borer does not
/// know when it opens with a dash, else a command.
///
/// The whole usage text came with it, 4 KB of it, and a word in the
/// command's place was first loaded as the binary, so `--bogus info x`
/// said the file `info` was not there.
///
/// # Arguments
///
/// * `word` - The word.
fn unknown_word(word: &str) -> String {
    if word.starts_with('-') {
        format!(
            "unknown option {}; the options are --pack <file>, --no-auto-packs and --no-pdb",
            quoted(word)
        )
    } else {
        format!(
            "unknown command {}; `borer help` lists the commands",
            quoted(word)
        )
    }
}

/// The words beginning `--` that queries read themselves, beside the
/// options [`split_pack_args`] takes off the line; `setup` and `doctor`
/// refuse any other word with their own message.
const COMMAND_FLAGS: &[&str] = &["--help", "--save"];

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
            println!("# {va:#x}..{:#x}{sec}", va + code.len() as u64);
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
        Query::Decompile => print!("{}", decompiled(args, s)?),
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
                eprintln!("indexed in {:.1} s", t0.elapsed().as_secs_f64());
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
                    .map_or(start, |v| v.at.wrapping_add(v.size as u64));
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
                let v = decompile::verify_a64::verify(&s.program, &a, &entries, seed);
                print!("{}", decompile::verify_a64::verify_tsv(&v));
                if !v.mismatches.is_empty() {
                    bail!("the lifter and the emulator disagree; see the table above");
                }
                return Ok(());
            }
            let v = decompile::verify::verify(&s.program, &a, &entries, seed);
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
}
