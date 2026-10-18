<picture>
  <source media="(prefers-color-scheme: dark)" srcset="assets/banner/banner-dark.png">
  <img alt="borer" src="assets/banner/banner-light.png" width="100%">
</picture>

# borer

A reverse-engineering engine built for AI agents. One Rust binary: an MCP
server when run with no arguments, a command-line tool with them. No GUI, and
no Ghidra, IDA or Binary Ninja underneath.

- **Formats:** PE, ELF, Mach-O, raw code and memory dumps.
- **Architectures:** x86, x86-64 and arm64: disassembly, decompilation and emulation.
- **Output:** plain-text tables sized for a context window, paged and capped,
  identical bytes for the same question every time.

> [!WARNING]
> Version 0.1.0, beta. Tool names, output spelling and resource URIs can still
> change. See [Limits](#limits).

## Why borer

| | borer | Ghidra 12.1.4 (headless MCP) |
| --- | --- | --- |
| Ready to answer, sqlite3 DLL (1,900 functions) | 0.1 s | 115 s cold, 5 s warm |
| One decompile, median | 2-7 ms | 220-260 ms |
| Recompiled output gives the source's answer | 359 / 420 | 308 / 420 |
| Recompiled output compiles but gives a wrong answer | 4 | 50 |

Measured on 60 known C functions built seven ways (x64 ELF and PE at
O0/Od/O2/Os, arm64 at O0/O2), plus findstr, notepad, msvcrt and sqlite. Each
decompiled function was compiled again and run against its source. Ghidra
still prints fewer gotos and fewer width casts on large optimized functions.

What makes it different:

- **Checked decompilation.** Every block of pseudo-C is run in an emulator
  from three seeded states and compared with the machine. The header says how
  many blocks agreed. Instructions it cannot model stay as `/* asm: ... */`
  instead of a guess.
- **Built for a context window.** Every list is filtered and paged on the
  server and says `# showing N of M`. A repeated request with `since=<tag>`
  returns only what changed.
- **Deterministic and hostile-input safe.** No clock, no random seed. Reads
  are bounds-checked, scans capped, walks fuel-limited: a malformed file gets
  an error, never a crash.
- **Safe annotation.** Renames and comments are dry-run by default and go to a
  separate project file. The binary is never modified.

## Install

Download an archive from the
[latest release](https://github.com/imjustprism/borer/releases/latest)
(Windows x64, Linux x64, macOS), then register it with your MCP clients:

```bash
./borer setup           # show what would change
./borer setup --apply   # register borer with every client found
```

`setup` finds Claude Code, Claude Desktop, Cursor, Windsurf, VS Code, Gemini
CLI, Codex CLI and Zed. It backs up each file it edits to `<file>.bak`.

From source, with the toolchain that `rust-toolchain.toml` pins:

```bash
git clone https://github.com/imjustprism/borer
cd borer
cargo build --release
target/release/borer setup --apply
```

To register it by hand:

```json
{ "mcpServers": { "borer": { "command": "/path/to/borer" } } }
```

## Use it from an agent

A typical session:

1. `load_binary`
2. `borer://triage` (what the file is, how it is protected, where to start)
3. `find_function_by_string`, `strings` or `symbols`
4. `function_summary`, then `decompile`
5. `xrefs`, `cfg` or `callgraph` to go wider

Any address argument takes `0x` hex, decimal, or a name.

| Area | Tools |
| --- | --- |
| Load | `load_binary`, `binary_info`, `fetch_pdb`, `reload` |
| Find | `functions`, `function`, `symbols`, `strings`, `search`, `find_function_by_string`, `find_crypto_constants`, `entropy` |
| Read code | `function_summary`, `function_strings`, `decompile`, `decompile_batch`, `disassemble`, `disassemble_function`, `cfg`, `callgraph`, `reaches`, `xrefs`, `class_layout` |
| Read data | `read`, `hexdump` |
| Annotate | `set_name`, `set_comment`, `set_type`, `types`, `annotations`, `save_project`, `load_project` |
| Live process | `live_attach`, `live_detach`, `live_modules`, `live_read`, `live_object`, `live_instances`, `live_watch` |
| Anything else | `query`, `script` |

Deeper analyses are `borer://` resources: taint, struct layout, emulation,
input solving, unpacking, flattening, VM dispatch, devirtualization, binary
diff, stack strings, decoded strings and IOCs. `borer://help` lists all of
them. A client without resource support passes the same URI to `query`.

## Use it from the command line

```bash
borer triage    sample.exe
borer functions sample.exe
borer decompile sample.exe <address|name>
borer xrefs     sample.exe <address|name>
borer verify    sample.exe    # lifter vs emulator; fails on any disagreement
borer help                    # every command
```

Useful flags: `--pack <file>` loads target knowledge, `--no-pdb` skips the
companion PDB, and `--arch x86|x64|arm64` (with `--base`, `--entry` and
`--regions`) maps raw code or a dump.

## More

- **Live processes (Windows only):** `live_attach` opens a running process
  read-only (`PROCESS_VM_READ`) and maps the loaded binary onto it. The live
  tools then read objects by their recovered class layout and watch fields
  change. Some anti-cheat software flags any foreign handle, read-only or not.
- **Packs:** target knowledge (one engine's class names, message ports) lives
  in local `.borer` files, never in engine code. None ship with borer.
  `borer sigmake` builds a signature pack from static libraries you already
  have (COFF `.lib`, ELF `.a`, Rust `.rlib`).
- **Scripting:** sandboxed [Rhai](https://rhai.rs/) scripts (no files, no
  network, an operation budget) through the `script` tool or `borer script`.

## Limits

- No instruction sets beyond x86, x86-64 and arm64.
- On arm64, `taint`, `layout`, `solve`, `unpack` and `devirt` refuse to run.
- Shapes the structurer cannot prove stay as labels and gotos. SIMD code
  prints as intrinsics (`paddd`, `__add_4s`), not as C.
- No debugger: no breakpoints and no writes. Live access is Windows only.
- .NET IL and Swift are not decompiled (.NET metadata is read).
- DWARF supplies names and types, not line tables.
- Embedded containers are listed (`borer://children`), not extracted.
- No bundled signature corpus.

## Workspace

| Crate | Role |
| --- | --- |
| [`borer-engine`](crates/borer-engine) | The analysis core: loading, lifting, emulation, decompilation. Pure and synchronous: no I/O, no async. |
| [`borer`](crates/borer) | The MCP server and CLI, thin adapters over the engine. |
| [`borer-live`](crates/borer-live) | Read-only access to a running process. |
| [`borer-fixtures`](crates/borer-fixtures) | Programs the tests decompile and check against their source. |

## Contributing

`python scripts/gate.py` runs what CI runs: fmt, clippy with `-D warnings`,
tests, rustdoc, `cargo deny`, typos, ruff and a smoke test of the real server.
The rules for people and coding agents alike are in
[`borer.rules`](borer.rules). Commit titles look like `type: summary`.

## License

[MIT](LICENSE). Third-party notices (pefile ordinal tables, the TLSH reference
implementation) are in [NOTICE](NOTICE).
