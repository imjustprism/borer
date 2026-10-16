# borer

Reverse-engineering engine for an AI agent. Rust core, MCP server, command-line
front end. No GUI, and no Ghidra, IDA, or Binary Ninja behind it.

The loader, function discovery, lifter, emulator, and decompiler live in this
repository. Instruction decoding comes from
[iced-x86](https://github.com/icedland/iced) for x86 and x86-64, and from
[yaxpeax-arm](https://crates.io/crates/yaxpeax-arm) for arm64.

> [!WARNING]
> **Version 0.1.0, beta.** A lot of what a finished disassembler does is not
> implemented. Output spelling, tool names, and resource URIs can still change.
> The decompiler is structured and checked, and it is still rough. Read
> [What this beta does not do](#what-this-beta-does-not-do) before you plan a
> workflow around it.

> [!NOTE]
> Answers are plain-text tables sized for a context window, not a screen.
> Lists are paged (`# showing N of M`). Defaults stay small: 50 functions a
> page, 300 lines of decompile. An answer over 512 bytes ends with
> `# since=<tag>`. Send the same request with that tag and you get a one-line
> unchanged note, or only the lines that changed.

## Contents

- [What this beta does not do](#what-this-beta-does-not-do)
- [What it does](#what-it-does)
- [Why another one](#why-another-one)
- [What the output looks like](#what-the-output-looks-like)
- [Install](#install)
- [From an agent](#from-an-agent)
- [From the command line](#from-the-command-line)
- [Live processes](#live-processes)
- [Packs and signatures](#packs-and-signatures)
- [Scripting](#scripting)
- [Workspace](#workspace)
- [Contributing](#contributing)
- [License](#license)

## What this beta does not do

These are refusals and gaps, not a backlog promise.

| Area | State in 0.1.0 |
| --- | --- |
| Instruction sets other than x86, x86-64, and arm64 | Not decoded. |
| arm64 beyond decompile, disassembly, and a partial emulator | `taint`, `layout`, `stackstrings`, `oracle`, `solve`, `unpack`, `devirt`, and `hidden` refuse it. The arm64 machine models integer, memory, and branch instructions and stops on anything else: no floating-point arithmetic, no vector lanes, no system calls except exit. A `run` text column on arm64 stays unchecked. |
| Decompiler polish | Shapes it cannot prove stay labels and gotos. On optimized code the body often opens with a long list of stack locals and globals. C spelling and later text passes are not what the block check covers. |
| Interactive UI | None. No graph window, no hex editor, no TUI. |
| Debugger | None. Windows live attach is read-only memory. No breakpoints, no writes, no injected code. Live access does not exist on Linux or macOS. |
| .NET IL | Metadata is read. IL is not decompiled. Mixed-mode native methods are analyzed as native code. |
| Swift | Metadata is not read. |
| Objective-C calls in pseudo-C | Methods are named `-[Class sel]` / `+[Class sel]`. A resolved `objc_msgSend` shows up in summaries, listings, and a decompile `// messages:` line. The decompiled call itself stays a call. |
| DWARF | Function names, parameters, frame locals, and types. Not line tables. Not inlined frames. |
| Go | `pclntab` names (Go 1.2 on, found by magic when stripped). On x86-64, Go 1.18+ register ABI and the stack-growth check fold. Source lines are not recovered. ABI0 assembly functions are not told apart from the rest. |
| ELF packed Android relocations | `APS2` tables are not read. Dynamic relocations that are read: `.rela.dyn`, `.rel.dyn`, `DT_RELR`, GOT binds, for x86, x86-64, and arm64. |
| Mach-O pointer formats | 64-bit chained fixups, arm64e (authentication stripped), kernel cache, and dyld info opcodes are applied. 32-bit chains and the shared cache chain format are refused. |
| PE base relocations | Read for analysis. |
| Containers inside a file | `borer://children` lists PE, ELF, Mach-O, zip, gzip, xz, 7z, cab, squashfs, cpio, uImage, cramfs, and Android boot images when the headers validate. Containers are not extracted. A program row opens with `load_binary path=<file>@<off>`. |
| Stable plugin API, signature corpus, or processor modules | Not in this beta. Target knowledge is a pack file. Library names come from `sigmake` on libraries you already have. |

> [!IMPORTANT]
> Capability groups in triage are a first guess from imports, not a verdict.
> A program that lists privileges imports the privilege APIs because that is
> its job.

## What it does

Loads PE, ELF, and Mach-O. Finds functions. Disassembles and decompiles x86,
x86-64, and arm64. On arm64 the decompiler uses the arm64 procedure call
standard: arguments in `x0` to `x7` and `v0` to `v7`, a result in `x0`,
`x0:x1`, or `v0`, a large result through `x8`.

Each decompiled block can be run in the emulator from three seeded states and
compared with what the pseudo-C statements claim. The header says how many
blocks agreed, and which were not checked. Unmodelled opcodes stay as
`/* asm: ... */` instead of a guessed statement.

The same binary and the same question return the same bytes. Nothing in the
engine reads the clock or a random seed. Malformed and hostile files are
expected: reads are bounds-checked, scans are capped, walks run on a step
budget. Bad input is an error, not a crash.

Heavier questions are `borer://` resources (over seventy): taint inside one
function, struct layout from pointer use, emulation, input solving, unpacking,
control-flow flattening, VM dispatch, devirtualization, binary diff and name
carry, wire-protocol recovery, stack strings, runtime-decoded strings, IOC
extraction, and more. `borer://help` lists them. A template read with no
argument (`borer://emulate`) returns its grammar and an example.

On a static Linux binary, capabilities come from syscall sites (`syscall`,
`int 0x80`, arm64 `svc #0`), named only where the number is set in the same
block as the call. A number set elsewhere counts as unresolved.

Speed, on borer's own release binary (17 MB x64 PE) on an 8-core desktop,
each a fresh process:

| Command | Result | Time |
| --- | --- | --- |
| `borer functions` | 11,499 functions | 1.3 s |
| `borer triage` | full triage report | 3.4 s |

## Why another one

Most reverse-engineering tools assume a person at a big screen. An MCP wrapper
around one of them still returns screen-shaped answers: a 4,000-line listing,
a JSON dump, a whole function when three lines were enough.

borer starts from the agent's side.

- Every list says what was held back.
- Filters and pages are server-side.
- Annotation tools are dry-run unless told otherwise. `save_project` writes
  names, comments, and types to a separate project file. The binary is never
  modified.
- Knowledge about one engine or library is a pack file you keep locally,
  not a hard-coded name in the engine. This repository does not ship packs.

## What the output looks like

`borer triage <file>` is one report: format, protection, anti-analysis,
crypto constants, imports resolved at runtime, license-style checks,
generated strings, a capability guess, then the functions to read first.
With no symbols, functions are named `sub_<address>`.

`borer decompile <file> <address>` starts with two comments. The second one
is the part worth knowing:

```text
// sub_<entry> @ 0x<address>: N instructions, N blocks
// checked vs binary: statements as emitted, 20/20 blocks x3 states; unchecked: C spelling, later text passes
```

Each block was run in the emulator from three seeded states and compared
with what the statements claim. The check is what each statement computes,
not how its C is spelled. When some blocks do not agree, or cannot be
checked, the header says which and why. The body on optimized code is still
rough: a long list of stack locals and globals before the first real
statement.

## Install

Prebuilt archives are on the
[latest release](https://github.com/imjustprism/borer/releases/latest):
Windows x64 (`.zip`), Linux x64 (glibc 2.35 or newer), macOS on Apple silicon
or Intel (`.tar.gz`). `SHA256SUMS` lists the checksums.

```bash
tar -xzf borer-v0.1.0-x86_64-unknown-linux-gnu.tar.gz
cd borer-v0.1.0-x86_64-unknown-linux-gnu
./borer setup           # what it would change, client by client
./borer setup --apply   # change it
```

On Windows, unzip and run `borer.exe setup` the same way.

`setup` looks for Claude Code, Claude Desktop, Cursor, Windsurf, VS Code,
Gemini CLI, Codex CLI, and Zed by their configuration directories and adds a
server named `borer` that runs the binary you started. Claude Code is
registered with `claude mcp add --scope user` when `claude` is on `PATH`.
Every file it changes is copied to `<file>.bak` first. The entry is inserted
without touching the rest of the file. A client that already has a `borer`
server is left alone. Restart the client to pick it up.

> [!NOTE]
> The macOS binaries are not notarized. If Gatekeeper stops one, run
> `xattr -d com.apple.quarantine borer` once.

### From source

```bash
git clone https://github.com/imjustprism/borer
cd borer
cargo build --release
target/release/borer setup --apply
```

`rust-toolchain.toml` pins Rust 1.96.1. rustup picks it up on its own.
`cargo build --profile dist` makes the stripped, `panic=abort` build the
releases ship.

CI runs the full gate on Windows, and clippy and the tests on Linux and
macOS. Tests that analyze borer's own build run on Windows only. Live process
access is Windows only.

## From an agent

With no arguments, `borer` speaks MCP over stdio.

```bash
claude mcp add --scope user borer -- /path/to/borer
```

For other clients:

```json
{
  "mcpServers": {
    "borer": { "command": "/path/to/borer" }
  }
}
```

A normal session is `load_binary`, then `borer://triage` (what the file is,
how it is protected, what it can do, where to read first), then
`find_function_by_string`, `strings`, or `symbols`, then `function_summary`,
then `decompile`, then `xrefs`, `cfg`, or `callgraph`. Any `address` argument
takes `0x` hex, decimal, or a name (function, import, overlay name).

There are 41 tools.

| Area | Tools |
| --- | --- |
| Loading | `load_binary`, `binary_info`, `fetch_pdb`, `reload` |
| Finding things | `functions`, `function`, `symbols`, `strings`, `search`, `find_function_by_string`, `find_crypto_constants`, `entropy` |
| Reading code | `function_summary`, `function_strings`, `decompile`, `decompile_batch`, `disassemble`, `disassemble_function`, `cfg`, `callgraph`, `reaches`, `xrefs`, `class_layout` |
| Reading data | `read`, `hexdump` |
| Annotating | `set_name`, `set_comment`, `set_type`, `types`, `annotations`, `save_project`, `load_project` |
| Live process | `live_attach`, `live_detach`, `live_modules`, `live_read`, `live_object`, `live_instances`, `live_watch` |
| Everything else | `query`, `script` |

Clients that cannot read resources pass the same URI to `query`. An unknown
URI returns the nearest names. `borer://help` is the full list.
`borer://help/<name>` is one resource's grammar. A listing pages with
`!offset=<n>` and `!limit=<n>` on its URI. `borer://session` says what the
session loaded, named, commented, and typed, and which answers it holds, cut,
or paged.

Prompts are resources too, `borer://playbook/<name>` (`triage`, `protocol`,
`find_check`, `explain_function`), for agents whose client offers prompts
only to the user.

`reload` restarts the server on a freshly built binary without the client
noticing. The process the client launched is a small relay that keeps
running, so the loaded file, names, and comments survive the restart.

Resources worth knowing by name:

| Question | URI |
| --- | --- |
| Where to start | `borer://triage`, `borer://why/{address}`, `borer://about/{name}` |
| Does the pseudo-C match a run | `borer://run/{function}/{input}`, `borer://emulate/{address}` |
| Follow a value or a pointer | `borer://taint/{spec}`, `borer://layout/{spec}`, `borer://fields/{address}` |
| Packed, flattened, or virtualized | `borer://protection`, `borer://unpack/{address}`, `borer://flat`, `borer://vm`, `borer://devirt/{address}` |
| Strings that are not stored in plaintext | `borer://stackstrings`, `borer://hidden`, `borer://decoded` |
| A check, a key, a license | `borer://checks`, `borer://solve/{spec}`, `borer://partial/{address}` |
| Another build of the same program | `borer://diff/{path}`, `borer://difffn/{function}/{path}`, `borer://carry/{path}`, `borer://migrate/{function}/{path}` |
| Search every decompilation | `borer://grep/{text}` (builds `borer://index` on first use) |

The rest (protocol tables, Qt, Objective-C, CLR metadata, IOC rows, packs,
snapshots) are on `borer://help`.

## From the command line

With arguments, the same binary runs one query and exits.

```bash
borer info      sample.exe
borer functions sample.exe
borer decompile sample.exe <address|name>
borer xrefs     sample.exe <address|name>
borer strings   sample.exe
borer help
```

`borer help` lists every command. There are about 70. They call the same
engine as the MCP tools. Useful ones that are easy to miss:

```bash
borer triage sample.exe
borer summary sample.exe <address|name>
borer verify sample.exe          # lifter against the emulator; fails on a disagreement
borer doctor                     # local setup: version, symbol cache, server
borer fetch-pdb sample.exe       # PDB named by the debug record, guid+age checked
```

Global options (see `borer help` for the full grammar):

| Option | Effect |
| --- | --- |
| `--pack <file>` | Analyze with a pack. Repeatable. `BORER_PACKS` lists more, including for the MCP server. |
| `--no-auto-packs` | Only packs named by `--pack` and `BORER_PACKS`. `BORER_AUTO_PACKS=0` does the same. |
| `--no-pdb` | Do not apply a companion PDB that is already on disk. |
| `--arch <x86\|x64\|arm64>` | Read the file as raw code or a memory dump. Headers are not parsed. |
| `--base`, `--entry`, `--regions` | Where that raw image maps, and which slices. At most 256 regions. |

## Live processes

On Windows, `live_attach` opens a running process with `PROCESS_VM_READ` and
nothing else. It maps the loaded binary onto the live module whose headers
match the file. A module that only shares the file's name is refused, and the
refusal says what differs. Live tools then take the same addresses and names
as the static ones. A later `load_binary` maps the new binary. `reload`
detaches.

`live_object` reads an object using the field layout recovered for its class.
`live_instances` finds a class's objects by vtable. `live_watch` shows which
fields changed between two reads. Every live address may be a static address
or a name.

> [!CAUTION]
> Some anti-cheat and anti-tamper software flags any foreign handle to its
> process, read-only or not. Try it on something you do not mind losing first.

## Packs and signatures

> [!NOTE]
> No pack ships with borer. A pack is target knowledge (one engine's class
> names, registrars, message ports), and it stays on your machine.

A pack file loads with `--pack`, with `BORER_PACKS`, or by itself from a
pack directory when every `[match]` line holds. Directories, in order: the
paths in `BORER_PACK_DIRS` if that is set, otherwise the user config
directory (`%APPDATA%\borer\packs`, `$XDG_CONFIG_HOME/borer/packs`, or
`~/.config/borer/packs`), then `packs` beside the executable and beside the
repository. `borer pack-keys` lists every key a pack can set. `borer pack
<file>` reports which keys borer does not read.

`sigmake` turns static libraries into a signature pack, with relocated bytes
masked, so functions linked from those libraries get their names back. It
reads COFF `.lib` / `.obj`, ELF `.a` / `.o`, and Rust `.rlib`:

```bash
borer sigmake msvc-x64.borer msvc-x64 libcmt.lib libvcruntime.lib libucrt.lib
borer sigmake musl.borer musl libc.a
borer functions sample.exe --pack msvc-x64.borer
```

There is no shipped signature corpus in this beta. You build the pack from
libraries you have.

## Scripting

[Rhai](https://rhai.rs/) scripts run in a sandbox: no files, no network, no
clock, and an operation budget. They can read functions, strings, bytes, and
xrefs, decompile, and propose names and comments.

An agent sends one through the `script` tool when no single tool answers the
question. `print(help())` lists what a script can call. `query(uri)` returns
the text of any `borer://` resource. `rows(uri)` returns the same as a list of
maps keyed by columns. `layout(e)` is the fields a function reads through a
pointer.

```rhai
for f in functions("crypt") {
    if callers(f.entry).len > 3 {
        print(`${hex(f.entry)} ${f.name}`);
    }
}
```

A run may make 2,000 `decompile` calls and 200 `query` calls. A failed script
still returns what it printed before the error, with the line that failed.
Proposed names and comments stay a preview until `dry_run=false`.

From the command line, a script is a file you pass:

```bash
borer script sample.exe scan.rhai
```

## Workspace

| Crate | What it is |
| --- | --- |
| [`borer-engine`](crates/borer-engine) | Analysis core: loading, disassembly, lifting, emulation, decompilation, queries. Synchronous. No I/O, no async, no MCP types. That is what keeps it testable and wasm-buildable. The shipped product is the CLI and the MCP server, not a wasm build. |
| [`borer`](crates/borer) | MCP server and CLI, thin adapters over the engine. |
| [`borer-live`](crates/borer-live) | Read-only access to a running process. The only crate that talks to the OS process API. |
| [`borer-fixtures`](crates/borer-fixtures) | Small binaries the tests decompile and check against their source. |

About 160,000 lines of Rust and 1,200 tests.

## Contributing

`python scripts/gate.py` runs what CI runs: `cargo fmt`, clippy with
`-D warnings`, the tests, rustdoc with warnings as errors, `cargo deny`,
`typos`, `ruff`, and a smoke test that drives the real server over JSON-RPC.
`--fast` skips the slow part at the end. Say "gate not run" when it was not.

The full rules are in [`borer.rules`](borer.rules). Every file name a coding
agent looks for (`AGENTS.md`, `CLAUDE.md`, `GEMINI.md`, `.cursorrules`,
`.github/copilot-instructions.md`, and the rest) points at that file. Short
version:

- `borer-engine` stays pure: no async, no filesystem writes, no MCP types.
- No `unwrap`, `expect`, or `panic!` in engine or server code. Tests may.
- No unbounded output. Every list has a cap and says when it hit it.
- No `as` between integer widths. Use the helpers in `crate::num`.
- Every item has a doc comment. Lints enforce it.
- Commit titles are one line, `type: summary`, where type is one of `add`,
  `fix`, `improve`, `refactor`, `perf`, `docs`, `test`, `chore`, or
  `revert`. `scripts/check/commits.py` checks them.

On Windows, git checks symlinks out as plain text files unless Developer Mode
is on and `core.symlinks` is `true`. A flat link holds just the path
`borer.rules`, which most agents follow anyway.

## License

[MIT](LICENSE). Copyright (c) 2026 imjustprism.

The imphash ordinal name tables come from
[pefile](https://github.com/erocarrera/pefile) (MIT, Copyright (c) 2004-2024
Ero Carrera). The TLSH digest follows Trend Micro's
[reference implementation](https://github.com/trendmicro/tlsh) (BSD,
Copyright (c) 2013 Trend Micro Incorporated). Notices are in
[NOTICE](NOTICE), which ships with every release archive.
