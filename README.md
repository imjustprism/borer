<p align="center">
  <a href="https://borer.lol">
    <picture>
      <source media="(prefers-color-scheme: dark)" srcset="brand/banner-dark.png">
      <img alt="borer: reverse engineering, rebuilt for AI agents" src="brand/banner-light.png" width="100%">
    </picture>
  </a>
</p>

<p align="center">
  <a href="https://github.com/imjustprism/borer/releases/latest"><img alt="Release" src="https://img.shields.io/github/v/release/imjustprism/borer?style=flat-square&labelColor=0b0c0e&color=26272b&label=release"></a>
  <a href="https://github.com/imjustprism/borer/actions/workflows/ci.yml"><img alt="CI" src="https://img.shields.io/github/actions/workflow/status/imjustprism/borer/ci.yml?branch=main&style=flat-square&labelColor=0b0c0e&color=26272b&label=ci"></a>
  <a href="LICENSE"><img alt="AGPL-3.0 license" src="https://img.shields.io/badge/license-AGPL--3.0-26272b?style=flat-square&labelColor=0b0c0e&color=26272b"></a>
  <img alt="Rust 2024" src="https://img.shields.io/badge/rust-2024-26272b?style=flat-square&labelColor=0b0c0e&color=26272b&logo=rust&logoColor=d4d4d8">
  <img alt="MCP server" src="https://img.shields.io/badge/MCP-server-26272b?style=flat-square&labelColor=0b0c0e&color=26272b">
  <img alt="PE, ELF, Mach-O" src="https://img.shields.io/badge/PE%20%C2%B7%20ELF%20%C2%B7%20Mach--O-x86%20%C2%B7%20x64%20%C2%B7%20arm64-26272b?style=flat-square&labelColor=0b0c0e&color=26272b">
</p>

<p align="center">
  <a href="https://borer.lol"><b>borer.lol</b></a> &nbsp;·&nbsp;
  <a href="https://borer.lol/docs">Docs</a> &nbsp;·&nbsp;
  <a href="#install">Install</a> &nbsp;·&nbsp;
  <a href="https://borer.lol/docs/tools">Tools</a> &nbsp;·&nbsp;
  <a href="https://borer.lol/llms.txt">llms.txt</a>
</p>

A reverse-engineering engine built for AI agents. One Rust binary: an MCP
server when run with no arguments, a command-line tool with them. No GUI, and
no Ghidra, IDA or Binary Ninja underneath.

- **Formats:** PE, ELF, Mach-O, raw code and memory dumps.
- **Architectures:** x86, x86-64 and arm64: disassembly, decompilation and
  emulation. 32-bit ARM (A32 and Thumb-2): disassembly and decompilation.
- **Output:** plain-text tables sized for a context window, paged and capped,
  identical bytes for the same question every time.

> [!WARNING]
> Version 0.1.1, beta. Tool names, output spelling and resource URIs can still
> change. See [Limits](#limits).

## Why borer

| | borer | Ghidra 12.1.3 (headless) |
| --- | --- | --- |
| Load sqlite3.dll and list its functions, cold (Ghidra: import and auto-analysis) | 0.15 s | 138 s |
| The same, analysis kept from an earlier run | 0.13 s | 3.1 s |
| Decompile every function of sqlite3.dll (borer on every core, Ghidra one function at a time) | 2.7 s | 48 s |
| Peak memory, sqlite3.dll | 73 MB | 1.5 GB |
| Install | one file | 1.2 GB with its JDK |

Speed is measured on notepad, msvcrt, sqlite3, ntdll and kernelbase, each
tool as it ships, one after the other
([numbers](scripts/run/vs_ghidra.json), [harness](scripts/run/vs_ghidra.py)).
The rows above are borer 0.1.0's run of that harness; a rerun on the current
build will replace them. Listing functions is not decompiling them: borer
analyzes on the first call that needs it, so its first decompile of a large
binary pays for that analysis, while Ghidra's has paid already. One function
at a time the two decompilers take about as long, a few milliseconds each;
borer's time includes checking every block. Ghidra still prints fewer gotos
and fewer width casts on large optimized functions.

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

One command downloads the latest release for your machine, checks it against
the release's SHA256SUMS, and registers borer with every MCP client it finds.

macOS and Linux:

```bash
curl -fsSL https://borer.lol/install | sh
```

Windows (PowerShell):

```powershell
irm https://borer.lol/install.ps1 | iex
```

`setup` finds Claude Code, Claude Desktop, Cursor, Windsurf, Devin Desktop, VS Code, VS Code Insiders, Gemini CLI, Codex CLI and Zed.
It backs up each file it edits to `<file>.bak`, replaces an entry whose
program no longer exists (`--replace` replaces any other), and ends by naming
the clients to restart: none reads its configuration again while it runs
(quit Claude Desktop from the tray; in Cursor, turn borer on under Settings >
MCP). For Codex it also sets `tool_timeout_sec = 600`, since the first
analysis of a large binary can take longer than Codex's default minute.

As a Claude Code plugin, which fetches the binary of the plugin's version
when a session starts and replaces it when the plugin updates:

```text
/plugin marketplace add imjustprism/borer
/plugin install borer@borer
```

Or by hand: download an archive from the
[latest release](https://github.com/imjustprism/borer/releases/latest)
(Windows x64, Linux x64, macOS), move `borer` where it will stay (`setup`
registers the path it runs from), then:

```bash
./borer setup           # show what would change
./borer setup --apply   # register borer with every client found
```

From source, with the toolchain that `rust-toolchain.toml` pins:

```bash
git clone https://github.com/imjustprism/borer
cd borer
cargo build --release
target/release/borer setup --apply
```

To register it by hand, use an absolute path. Claude Desktop, Cursor,
Windsurf and Gemini CLI read `mcpServers`:

```json
{ "mcpServers": { "borer": { "command": "/path/to/borer", "args": [] } } }
```

VS Code (`mcp.json` in the user folder) reads `servers`:

```json
{ "servers": { "borer": { "type": "stdio", "command": "/path/to/borer", "args": [] } } }
```

Zed (`settings.json`) reads `context_servers`:

```json
{ "context_servers": { "borer": { "command": "/path/to/borer", "args": [] } } }
```

Codex CLI (`~/.codex/config.toml`):

```toml
[mcp_servers.borer]
command = "/path/to/borer"
args = []
startup_timeout_sec = 30
tool_timeout_sec = 600
```

To uninstall, `borer setup --apply --remove` takes borer out of every client
(`borer setup --remove` shows what it would change); then delete the binary
and its cache (`%LOCALAPPDATA%\borer`, or `~/.cache/borer`). The installers
do all three:

```bash
curl -fsSL https://borer.lol/install | sh -s -- --uninstall
```

```powershell
& ([scriptblock]::Create((irm https://borer.lol/install.ps1))) -Uninstall
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
| Live process (Windows only) | `live_attach`, `live_detach`, `live_modules`, `live_read`, `live_object`, `live_instances`, `live_watch` |
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
- **Sizes:** every answer is capped at 72,000 bytes, cut at a line with a note
  on how to page the rest (`BORER_BUDGET` sets the cap in bytes, `0` lifts
  it). A file is read into memory whole, so one past 1 GiB is refused with a
  message (`BORER_MAX_FILE`, in bytes or with `K`, `M` or `G`; `0` lifts it).
  A client that sends a progress token gets a progress notification every few
  seconds while a first analysis runs.

## Network access

borer sends nothing about what you analyze, and has no telemetry or crash
reporting. Three things reach the network:

- **The update check.** A command line run at a terminal checks once a day
  whether a newer release is out: a request to
  `https://github.com/imjustprism/borer/releases/latest` with the user agent
  `borer/<version>`, so GitHub sees your IP address, the version and the
  time. It never runs for the MCP server, under `CI`, or with stderr
  redirected; `BORER_NO_UPDATE_CHECK=1` turns it off.
- **`fetch_pdb`**, only when asked and dry-run by default, sends the PDB's
  name, GUID and age to the symbol server (Microsoft's unless configured).
  `borer doctor` checks that server is reachable unless run as
  `borer doctor offline`.
- **`borer update`** and the installers download the release from GitHub.

## Limits

- No instruction sets beyond x86, x86-64, arm64 and 32-bit ARM.
- 32-bit ARM code is not emulated, so the emulator-backed analyses refuse it.
- On arm64, `taint`, `layout`, `solve`, `unpack` and `devirt` refuse to run.
- Shapes the structurer cannot prove stay as labels and gotos. SIMD code
  prints as intrinsics (`paddd`, `__add_4s`), not as C.
- No debugger: no breakpoints and no writes. Live access is Windows only.
- .NET IL and Swift are not decompiled (.NET metadata is read).
- DWARF supplies names and types, not line tables.
- Embedded containers are listed (`borer://children`), not extracted.
- Library signatures ship for three runtimes only (LLVM compiler-rt, the
  Microsoft C++ standard library, the Rust standard library); any other
  library needs a pack built with `borer sigmake`.

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

By opening a pull request you agree that your contribution is licensed under
the project's license and that the maintainer may relicense it, including under
commercial terms. The details are in [CONTRIBUTING.md](CONTRIBUTING.md).

## License

borer is free software under the [GNU Affero General Public License
v3.0](LICENSE) (AGPL-3.0-only). Use it for anything, change it and share it;
if you distribute borer or a modified version, or run one as a network
service, you must publish its complete source under the same license.
Versions 0.1.0 and 0.1.1 were released under MIT. A commercial license, for
uses the AGPL does not fit, is available: open an issue or reach out on
GitHub.

Third-party notices (pefile ordinal tables, the TLSH reference
implementation, the library signature sets and the SDK type data, with their
provenance) are in [NOTICE](NOTICE). Each release archive also carries
THIRD-PARTY-LICENSES, the licenses of every crate and runtime the binary links.

Ghidra is a project of the NSA; IDA and Hex-Rays are trademarks of Hex-Rays
SA; Binary Ninja is a trademark of Vector 35; Claude is a trademark of
Anthropic; other names are their owners' trademarks. borer is not affiliated
with or endorsed by any of them.
