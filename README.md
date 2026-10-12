# borer

borer is a reverse-engineering engine in Rust that an AI agent drives over
MCP. It loads PE, ELF and Mach-O files, finds functions, disassembles and
decompiles x86/x86-64, and answers in short plain-text tables instead of
the full listings a GUI tool would show.

No Ghidra, IDA or Binary Ninja runs behind it. The loader, function
discovery, lifter, emulator and decompiler all live in this repo; instruction
decoding comes from [iced-x86](https://github.com/icedland/iced) for x86 and
[yaxpeax-arm](https://crates.io/crates/yaxpeax-arm) for arm64.

## Why another one

Most RE tools assume a person at a big screen. Put an MCP wrapper around
them and the agent still gets screen-shaped answers: 4,000-line listings,
JSON dumps, a whole function when it needed three lines of it. borer starts
from the agent's side:

- Lists are paged and filterable, and every one starts with a
  `# showing N of M` line, so the agent knows what it didn't get.
- Defaults are small: 50 functions a page, 300 lines of decompile.
- Answers over 512 bytes end with a `# since=<tag>` line. Send the same
  request with that tag and you get a one-line "unchanged" note, or only
  the lines that changed.
- Same binary, same question, same bytes back. Nothing in the engine reads
  the clock or a random seed.
- Malformed and hostile files are expected. Reads are bounds-checked, scans
  are capped, walks run on a step budget. Bad input gets an error, not a
  crash.

## What it looks like

Real output, run against `whoami.exe` from a stock Windows 11 install
(build 26200). No symbols, so functions get `sub_` names.

```text
$ borer triage C:/Windows/System32/whoami.exe
# triage: whoami.exe
# PE x86-64, 98304 bytes, entry 0x140001cb0, 7 sections, 127 imports, 0 exports, 245 functions
# protection: plain: no packer marks
# anti-analysis: a program that resists being watched
# crypto: 0 crypto/hash constant hits
# dynamic imports: 0 functions resolved at runtime, 0 libraries loaded, from 0 call site groups
# checks: 0 functions judge a key, serial or license
# generated strings: 0 recovered from 0 generator(s)
# capabilities: 5 of 16 capabilities present across 127 imports
#   privilege escalation      AdjustTokenPrivileges, LookupPrivilegeDisplayNameW, LookupPrivilegeNameW, LookupPrivilegeValueW
#   process control           OpenProcessToken, TerminateProcess
#   anti-analysis             QueryPerformanceCounter
#   host reconnaissance       GetUserNameExW
#   process injection         OpenProcessToken
# read first: no protection signal fired, so the ranking is by the strings and imports each function references
0x14000b5e0  sub_14000b5e0                references 4 strings and 8 imports
0x140009d88  sub_140009d88                references 0 strings and 11 imports
0x140002528  sub_140002528                references 9 strings and 0 imports
...
# next: function_summary(addr), then decompile(addr); emulate/<addr> runs one
```

The capability groups are a first guess from imports, not a verdict:
`whoami` asks for token privileges because listing them is its job.

```text
$ borer decompile C:/Windows/System32/whoami.exe 0x140002528
// sub_140002528 @ 0x140002528: 317 instructions, 20 blocks
// checked vs binary: statements as emitted, 20/20 blocks x3 states; unchecked: C spelling, later text passes
...
```

That second line is the part worth knowing about. borer runs each block of
the function in its own emulator from three seeded states and compares the
machine state with what the pseudo-C says happened. Here all 20 blocks
agreed. It checks what each statement computes, not how its C is spelled
or what the later text passes rewrote, and the header says so. When some
blocks don't agree, or can't be checked, the header says which and
why. The body itself is rough: on optimized code like this you get a long
list of stack locals and globals before the first real statement.

Speed, on borer's own release binary (17 MB x64 PE) on an 8-core desktop,
each a fresh process:

| command | result | time |
| --- | --- | --- |
| `borer functions` | 11,499 functions | 1.3 s |
| `borer triage` | full triage report | 3.4 s |

## Install

Download the archive for your machine from the
[latest release](https://github.com/imjustprism/borer/releases/latest):
Windows x64 (`.zip`), Linux x64 (glibc 2.35 or newer), macOS on Apple
silicon or Intel (`.tar.gz`). `SHA256SUMS` lists their checksums. Unpack
it where the binary can stay, then let it register itself with your agent
clients:

```bash
tar -xzf borer-v0.1.0-x86_64-unknown-linux-gnu.tar.gz
cd borer-v0.1.0-x86_64-unknown-linux-gnu
./borer setup           # what it would change, client by client
./borer setup --apply   # change it
```

On Windows, unzip the archive and run `borer.exe setup` the same way.
`setup` looks for Claude Code, Claude Desktop, Cursor, Windsurf, VS Code,
Gemini CLI, Codex CLI and Zed by their configuration directories and adds
a server named `borer` that runs the binary you started. Claude Code is
registered with `claude mcp add --scope user` when `claude` is on `PATH`.
Every file it changes is first copied to `<file>.bak`, the entry is
inserted without touching the rest of the file, and a client that already
has a `borer` server is left alone. Restart a client to pick it up.

The macOS binaries are not notarized; if Gatekeeper stops one, run
`xattr -d com.apple.quarantine borer` once.

### From source

```bash
git clone https://github.com/imjustprism/borer
cd borer
cargo build --release
target/release/borer setup --apply
```

`rust-toolchain.toml` pins Rust 1.96.1 and rustup picks it up on its own.
`cargo build --profile dist` makes the stripped, `panic=abort` build the
releases ship.

CI runs the full gate on Windows, and clippy and the tests on Linux and
macOS. The tests that analyze borer's own build run on Windows only, and
live process access is Windows only.

## Using it from an agent

With no arguments, `borer` speaks MCP over stdio. `borer setup` registers
it with the clients it knows; by hand, in Claude Code:

```bash
claude mcp add --scope user borer -- /path/to/borer
```

For other clients, the usual config block:

```json
{
  "mcpServers": {
    "borer": { "command": "/path/to/borer" }
  }
}
```

A normal session goes `load_binary`, then the `borer://triage` resource
(what the file is, how it is protected, what it can do and where to read
first), then `find_function_by_string`, `strings` or `symbols` to find
something worth reading, `function_summary` to size it up, `decompile` to read it, and
`xrefs`, `cfg` or `callgraph` to see how it connects. Any `address`
argument takes hex, decimal or a name.

There are 41 tools:

| area | tools |
| --- | --- |
| loading | `load_binary`, `binary_info`, `fetch_pdb`, `reload` |
| finding things | `functions`, `function`, `symbols`, `strings`, `search`, `find_function_by_string`, `find_crypto_constants`, `entropy` |
| reading code | `function_summary`, `function_strings`, `decompile`, `decompile_batch`, `disassemble`, `disassemble_function`, `cfg`, `callgraph`, `reaches`, `xrefs`, `class_layout` |
| reading data | `read`, `hexdump` |
| annotating | `set_name`, `set_comment`, `set_type`, `types`, `annotations`, `save_project`, `load_project` |
| live process | `live_attach`, `live_detach`, `live_modules`, `live_read`, `live_object`, `live_instances`, `live_watch` |
| everything else | `query`, `script` |

Annotation tools are dry-run unless told otherwise. `save_project` writes
names, comments and types to a separate project file; the binary itself is
never touched.

Heavier analyses are MCP resources under `borer://`, over seventy of them:
taint tracking, struct layout from pointer use, emulation, input solving,
unpacking, control-flow-flattening and VM detection, devirtualization,
binary diffing and carrying names over to a new build, wire protocol
recovery, and more. Clients that can't read resources can pass the same URI
to the `query` tool. A template read without its argument (`borer://emulate`)
returns its grammar and an example, an unknown URI the nearest names, and
`borer://help` the full list. The prompts are resources too,
`borer://playbook/<name>`, for agents whose client offers prompts only to
the user.

`reload` restarts the server on a freshly built binary without the client
noticing. The process the client launched is a small relay that keeps
running, so the loaded file, names and comments survive the restart.

## Using it from the command line

With arguments, the same binary runs one query and exits:

```bash
borer info      sample.exe
borer functions sample.exe
borer decompile sample.exe <address|name>
borer xrefs     sample.exe <address|name>
borer strings   sample.exe
```

`borer help` lists all of them (there are about 70).

## Live processes

On Windows, `live_attach` opens a running process with `PROCESS_VM_READ`
and nothing else: no writes, no breakpoints, no injected code. It maps the
loaded binary onto the live module whose headers match the file (a module
that only shares the file's name is refused, with what differs), so the
live tools take the same addresses and names as the static ones; a later
`load_binary` maps the new binary, and `reload` detaches. `live_object` reads an object using
the field layout borer recovered for its class, `live_instances` finds a
class's objects by vtable, and `live_watch` shows which fields changed
between two reads.

Some anti-cheat and anti-tamper software flags any foreign handle to its
process, read-only or not. Try it on something you don't mind losing first.

## Packs

Knowledge about a specific engine or library goes in a pack file, never in
engine code. `packs/nebula.borer` is an example for the Nebula Device 3
engine: its RTTI layout, message ids, singletons and attribute registry.
Packs in a pack directory load on their own for binaries they match.
`borer pack-keys` lists every key a pack can set.

`sigmake` turns static libraries into a signature pack, with relocated
bytes masked, so functions linked from those libraries get their names
back:

```bash
borer sigmake msvc-x64.borer msvc-x64 libcmt.lib libvcruntime.lib libucrt.lib
borer functions sample.exe --pack msvc-x64.borer
```

## Scripting

[Rhai](https://rhai.rs/) scripts run in a sandbox: no files, no network,
no clock, and an operation budget. They can read functions, strings, bytes
and xrefs, decompile, and propose names and comments.

An agent sends one through the `script` tool when no single tool answers
its question; `print(help())` lists everything a script can call. Inside a
script, `query(uri)` returns the text of any `borer://` resource, so a few
lines can combine taint, layout, grep and the rest:

```rhai
for f in functions("crypt") {
    if callers(f.entry).len > 3 {
        print(`${hex(f.entry)} ${f.name}`);
    }
}
```

A run may make 2,000 `decompile` calls and 200 `query` calls. A failed
script still returns what it printed before the error, with the line that
failed. Proposed names and comments stay a preview until `dry_run=false`.

From the command line, scripts are files. A few examples are in
[`packs/scripts`](packs/scripts):

```bash
borer script sample.exe packs/scripts/suspicious_apis.rhai
```

## Limits

- Only x86 and x86-64 are decompiled. An arm64 Mach-O, ELF or PE loads
  its sections and symbols, disassembles, and has its functions, blocks
  and calls discovered (`functions`, `function`, `disassemble_function`,
  `cfg`, `callgraph`, `xrefs` on calls), but jump tables, data references
  and import stubs are not resolved yet. Its code runs under
  `borer://emulate` and `borer://run` in an arm64 machine that models the
  integer, memory and branch instructions and stops on anything else (no
  floating-point arithmetic, no vector lanes, no system calls but exit);
  the tools that decompile it, and those built on the x86 machine
  (`oracle`, `solve`, `unpack`, `devirt`, `hidden`), refuse it. Other
  machines are not decoded.
- Decompiler output is structured but rough, as the example above shows.
  Shapes it can't prove come out as labels and gotos rather than a guess.
- Relocations are read for analysis, not applied. Mach-O chained fixups
  aren't read at all.
- DWARF support covers function names, parameters, frame locals and types,
  not line tables or inlined frames.
- Live process access is Windows only.

## Workspace

| crate | what it is |
| --- | --- |
| [`borer-engine`](crates/borer-engine) | The analysis core: loading, disassembly, lifting, emulation, decompilation, queries. Synchronous, no I/O, no async, no MCP types. |
| [`borer`](crates/borer) | The MCP server and the CLI on top of the engine. |
| [`borer-live`](crates/borer-live) | Read-only access to a running process. The only crate that talks to the OS process API. |
| [`borer-fixtures`](crates/borer-fixtures) | Small binaries the tests decompile and check against their source. |

About 160k lines of Rust and 1,200 tests.

## Contributing

`python scripts/gate.py` runs what CI runs: `cargo fmt`, clippy with
`-D warnings`, the tests, rustdoc with warnings as errors, `cargo deny`,
`typos`, `ruff`, and a smoke test that drives the real server over
JSON-RPC. `--fast` skips the slow part at the end.

The full rules live in [`borer.rules`](borer.rules), for people and coding
agents alike. Every file name a coding agent looks for (`AGENTS.md`,
`CLAUDE.md`, `GEMINI.md`, `.cursorrules`, `.github/copilot-instructions.md`
and the rest) is a symlink to it, so whatever agent you use picks up the
same rules without being told. The short version:

- `borer-engine` stays pure: no async, no filesystem writes, no MCP types.
- No `unwrap`, `expect` or `panic!` in engine or server code. Tests may.
- No unbounded output. Every list has a cap and says when it hit it.
- No `as` between integer widths; use the helpers in `crate::num`.
- Every item has a doc comment. Lints enforce it.
- Commit titles are one line, `type: summary`, where type is one of `add`,
  `fix`, `improve`, `refactor`, `perf`, `docs`, `test`, `chore` or
  `revert`. `scripts/commits.py` checks them.

On Windows, git checks symlinks out as plain text files unless Developer
Mode is on and `core.symlinks` is `true`. A flat link holds just the path
`borer.rules`, which most agents follow anyway.

## License

[MIT](LICENSE)

The imphash's ordinal name tables come from
[pefile](https://github.com/erocarrera/pefile) (MIT, Copyright (c) 2004-2024
Ero Carrera); its notice is at the top of
[`ordinals.tsv`](crates/borer-engine/src/ordinals.tsv).
