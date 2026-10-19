//! Parsing a command line into a [`Query`]: the commands, their flags and
//! arguments, and the usage each prints when a word is wrong.

use anyhow::{Context as _, anyhow, bail};
use borer_engine::analysis::Analysis;
use borer_engine::layout::{self, Layout};
use borer_engine::program::Program;
use borer_engine::text::quoted;

use super::CLASS_ROWS;
use crate::params::{Detail, SearchKind};
use crate::state::env_pack_files;

/// A command word, by what it needs before it runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Command {
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
    pub(super) fn parse(word: &str) -> Option<Self> {
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
    pub(super) fn most_args(self) -> Option<usize> {
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
pub(super) enum Query {
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
    /// `export --c <out.c> [--library]`: every function as one C file, leaves first.
    Export,
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
    /// `verify [function|all] [limit] [seed] [text|mir]`: check the lifter, or with `text` the text's statements, against the emulator, with `mir` reading the lifted values through MIR; fails on any disagreement.
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
    pub(super) fn parse(word: &str) -> Option<Self> {
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
            "export" => Self::Export,
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
    pub(super) fn most_args(self) -> Option<usize> {
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
            | Self::Export
            | Self::ExportPack => 3,
            Self::Decompile | Self::Fieldrefs | Self::Grep | Self::Types | Self::Verify => 4,
            Self::Script | Self::SetType => return None,
        })
    }
}

/// Which way `callgraph` walks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub(super) enum Direction {
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
    pub(super) fn parse(word: Option<&str>) -> anyhow::Result<Self> {
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
pub(super) fn detail(word: Option<&str>) -> anyhow::Result<Detail> {
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
pub(super) fn decompile_args(
    words: &[String],
) -> anyhow::Result<(Detail, Option<u32>, Option<u32>)> {
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
pub(super) fn search_args(words: &[String]) -> anyhow::Result<(SearchKind, usize)> {
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
pub(super) fn arg<'a>(
    args: &'a [String],
    i: usize,
    missing: &'static str,
) -> anyhow::Result<&'a str> {
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
pub(super) fn num_arg<T: std::str::FromStr>(
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
pub(super) fn path_arg<'a>(
    args: &'a [String],
    i: usize,
    missing: &'static str,
) -> anyhow::Result<&'a str> {
    let path = arg(args, i, missing)?;
    if path.is_empty() {
        bail!("{missing}; the path is empty");
    }
    Ok(path)
}

/// Reads `export`'s arguments after the binary: `--c <out.c>`, and
/// `--library` to write library code too.
///
/// # Arguments
///
/// * `args` - The command line, the command first and the binary second.
///
/// # Returns
///
/// The C file to write, and whether library code goes into it.
///
/// # Errors
///
/// When `--c` is missing or has no path after it, or a word is neither.
pub(super) fn export_args(
    args: &[String],
) -> anyhow::Result<(&str, borer_engine::analysis::decompile::export::Library)> {
    use borer_engine::analysis::decompile::export::Library;
    let mut out = None;
    let mut library = Library::Skip;
    let mut rest = args.iter().skip(2);
    while let Some(word) = rest.next() {
        match word.as_str() {
            "--c" => {
                out = Some(
                    rest.next()
                        .filter(|p| !p.is_empty())
                        .context("--c needs the C file to write")?
                        .as_str(),
                );
            }
            "--library" => library = Library::Include,
            other => bail!(
                "export takes --c <out.c> and --library, not {}",
                quoted(other)
            ),
        }
    }
    Ok((out.context("export needs --c <out.c>")?, library))
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
pub(super) fn cli_limit(
    args: &[String],
    at: usize,
    default: usize,
    max: usize,
) -> anyhow::Result<usize> {
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
pub(super) fn cli_page(
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
pub(super) fn filter_limit(args: &[String], max: usize) -> anyhow::Result<(&str, usize)> {
    Ok((
        args.get(2).map_or("", String::as_str),
        cli_limit(args, 3, max, max)?,
    ))
}

/// The arguments of the commands that read a constant off a vtable slot:
/// `<slot> [filter] [limit]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct SlotQuery<'a> {
    /// The zero-based vtable slot.
    pub(super) slot: usize,
    /// A substring of the class name; empty keeps every class.
    pub(super) filter: &'a str,
    /// Rows at most, 1 to [`CLASS_ROWS`].
    pub(super) limit: usize,
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
    pub(super) fn parse(args: &'a [String], missing: &'static str) -> anyhow::Result<Self> {
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
pub(super) fn entry_at(p: &Program, a: &Analysis, va: u64) -> anyhow::Result<u64> {
    borer_engine::analysis::function_entry(p, a, va).map_err(anyhow::Error::msg)
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
pub(super) fn command_usage(usage: &str, cmd: &str) -> Option<String> {
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
pub(super) fn split_pack_args(
    args: &[String],
) -> anyhow::Result<(Vec<String>, Vec<String>, bool, bool)> {
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
pub(super) struct RawFlags {
    /// `--arch`: the architecture the bytes map as.
    pub(super) arch: Option<String>,
    /// `--base`: where the whole file maps.
    pub(super) base: Option<String>,
    /// `--entry`: the entry address.
    pub(super) entry: Option<String>,
    /// `--regions`: the parts of the file mapped instead of the whole.
    pub(super) regions: Option<String>,
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
    pub(super) fn split(args: &[String]) -> anyhow::Result<(Vec<String>, RawFlags)> {
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
    pub(super) fn slot(&mut self, flag: &str) -> Option<&mut Option<String>> {
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
    pub(super) fn layout(&self) -> anyhow::Result<Option<Layout>> {
        let arch = self.arch.as_deref().map(layout::parse_arch).transpose()?;
        Layout::parse(
            arch,
            self.base.as_deref(),
            self.entry.as_deref(),
            self.regions.as_deref(),
        )
    }
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
pub(super) fn unknown_word(word: &str) -> String {
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
pub(super) const COMMAND_FLAGS: &[&str] = &["--help", "--save", "--c", "--library"];
