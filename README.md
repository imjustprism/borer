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
  <img alt="MCP server" src="https://img.shields.io/badge/MCP-server-26272b?style=flat-square&labelColor=0b0c0e&color=26272b">
</p>

<p align="center">
  <a href="https://borer.lol"><b>borer.lol</b></a> &nbsp;·&nbsp;
  <a href="https://borer.lol/docs">Docs</a> &nbsp;·&nbsp;
  <a href="#what-it-does">Cases</a> &nbsp;·&nbsp;
  <a href="#install">Install</a> &nbsp;·&nbsp;
  <a href="https://borer.lol/docs/tools">Tools</a> &nbsp;·&nbsp;
  <a href="https://borer.lol/llms.txt">llms.txt</a>
</p>

borer is a reverse-engineering engine whose user is an AI agent. One Rust
binary: an MCP server when run with no arguments, a command-line tool with
them. It owns its loader, lifters, emulator and decompiler, and it has no GUI.

Everything below is real output of borer 0.2.12 (release build, commit
`7d9bb42c`) on two files of Windows 11: `notepad.exe` 10.0.26100.8457 (sha256
`2d0b3948...2efb158f`) and `ntdll.dll` 10.0.26100.9549 (sha256
`b072efae...ce5aed21`). Lines cut for length are marked `...`. Addresses
differ on another build: `borer symbols ntdll.dll RtlComputeCrc32` finds the
export, and its decompile names the two functions it forwards to.

> [!WARNING]
> borer is early-stage. Tool names, output and resource URIs still change
> between releases. Please report anything that looks wrong.

## What it does

### One call says what a file is and where to read

```console
$ borer triage notepad.exe
# PE x86-64, 360448 bytes, entry 0x1400019c0, 8 sections, 340 imports, 0 exports, 523 functions
# built: MSVC, cl 19.38 build 33145, Visual Studio 2022 17.8 (high: Rich header linker entry 0x102.33145; ...)
# protection: plain: no packer marks
# dynamic imports: 13 functions resolved at runtime, 1 library loaded, from 16 call site groups
# capabilities: 6 of 16 capabilities present across 340 imports
#   filesystem                CreateFileW, DeleteFileW, FindFirstFileW, ReadFile, WriteFile
#   persistence               RegCreateKeyExW, RegCreateKeyW, RegSetKeyValueW, RegSetValueExW
...
# blind spot: 4 of 18 GetProcAddress calls pass a name the decompiler cannot read (computed, hashed or decrypted): the imports resolved there stay unseen
# read first: no protection signal fired, so the ranking is by the strings and imports each function references
0x140013150  sub_140013150                references 13 strings and 47 imports
0x140012a28  sub_140012a28                references 38 strings and 3 imports
...
# next: function_summary(addr), then decompile(addr); emulate/<addr> runs one
```

The whole answer is 2,408 bytes. It ends with what to call next, and it names
its own blind spot instead of hiding it.

### The decompiler checks its own work

Every function's header says how much of the text was checked against the
machine code it came from:

```console
$ borer decompile ntdll.dll 0x180102184
// sub_180102184 @ 0x180102184: 6 instructions, 3 blocks
// checked vs binary: statements as emitted, 3/3 blocks: 3 proved; unchecked: C spelling, later text passes
// signature: uint64_t sub_180102184(uint64_t a1, uint8_t *a2, uint32_t a3)
...
if (a2 == nullptr) {
  return 0;
}
return sub_1800ed890(a1, a2, a3);
```

`certify` goes one step further: it runs the final text as C beside the
binary on the same inputs and grades the result.

```console
$ borer certify ntdll.dll 0x180102184
# certify for sub_180102184 (0x180102184): what of its decompilation was checked against the binary; agreement is evidence, not proof
lift	statements as emitted, 3/3 blocks: 3 proved; unchecked: C spelling, later text passes
text	20 of 64 inputs agree as ISO C, 44 unchecked, 0 differ (seed 1, 20000 steps each)
unchecked	44	the binary did not return: fault at 0x500000010050
reached	2 of 3 blocks; never reached: 0x180102191
grade	agrees	every input checked agrees (they reached 2 of 3 blocks) and no lifted block is contradicted
```

The block check covers x86, x86-64, arm64 and 32-bit ARM; RISC-V output has
no check header yet. `certify` runs on x86 and x86-64. The header always says
what was not checked (here the C spelling and the later text passes). An
instruction borer cannot model stays in the text as `/* asm: ... */`. It is
never replaced by a guess.

### It runs code without running the file

borer has its own emulator, so an agent can call a function on typed inputs
and read the result. Here the function `RtlComputeCrc32` forwards to gets the
standard CRC-32 test string, and answers the published check value
`0xcbf43926`. The last column says the decompiled text, run on the same
inputs, gave the same results:

```console
$ borer run ntdll.dll '0x1800ed890/0,"123456789",9;0,"",0;0,"a",1'
# run uint32_t sub_1800ed890(uint32_t a1, uint8_t *a2, uint64_t a3): 3 inputs, at most 1000000 steps each; the text agrees on 3, differs on 0, unchecked on 0
# args	returns	stop	steps	writes	text
0 "123456789" 9	0xcbf43926	returned	126	-	agrees
0 "" 0	0	returned	38	-	agrees
0 "a" 1	0xe8b7be43	returned	47	-	agrees
```

The same emulator drives input solving (`solve`), unpacking (`unpack`),
devirtualization (`devirt`), taint (`taint`) and struct recovery (`layout`).
The file itself is never executed and never modified.

### It says what it does not know

Ask the exported wrapper the same question and borer does not round its
answer up:

```console
$ borer run ntdll.dll 'RtlComputeCrc32/0,"123456789",9'
# run uint64_t RtlComputeCrc32(uint64_t a1, uint64_t a2, uint64_t a3): 1 input, at most 1000000 steps each; the text agrees on 0, differs on 0, unchecked on 1
...
0 "123456789" 9	0xcbf43926	returned	131	-	unchecked
# input 1 unchecked at line 6 `return sub_180102184(a1, a2, a3);`: the text states only the low 8 bits of the result; the bits above are the machine's own
```

A heuristic answer names its evidence. `borer why <address>` lists where
each fact about an address came from:

```console
$ borer why ntdll.dll 0x1800ed890
# 0x1800ed890 is the entry of sub_1800ed890: 864 bytes, 36 blocks, 215 instructions
# section .text at 0x180001000, r-x and code
# name: nothing names it, so the name is the address
# discovered by: an entry in the exception or symbol table, then 1 call site(s)
# referenced from 1 site(s): 0x18010218c in sub_180102184
```

### It finds code by what it is

```console
$ borer crypto ntdll.dll
# 17 crypto/hash constant hits: 6 algorithm(s) across 16 function(s)
# algorithm        sites  functions  where
CRC-32            8      3          data in .rdata, read by sub_18015431c, sub_180154538, crc32_fn
MD5               3      9          data in .rdata, read by sha1_or_ripemd160_fn, MD5Init, MD5Final, ...
SHA-256           2      2          data in .rdata, read by sha256_fn, sha256_or_blake2s_fn
...
```

```console
$ borer sig ntdll.dll 0x180102184
# signature of sub_180102184 at 0x180102184: 8 bytes, 1 wildcarded, unique in the image
pattern  48 85 D2 74 ?? 45 8B C0
...
```

Classes, vtables, message formats, opcode dispatchers, decoded and generated
strings, IOCs and YARA rules come from the same engine: `borer help` lists
every command, and `borer://help` every resource.

### Answers sized for a context window

Every list is filtered and paged on the server, and says how much it left
out:

```console
$ borer functions notepad.exe "" 0 3
# showing 3 of 481 functions; 39 import thunks left out, filter=thunk lists them; 3 exception funclets left out, filter=funclet lists them
# entry size blocks instrs callers callees src name
0x140001008 133 3 26 5 2 - sub_140001008
0x140001094 288 12 67 2 2 - sub_140001094
0x1400011bc 149 3 27 5 2 - sub_1400011bc
```

Over MCP, an answer of 512 bytes or more carries a `since` tag. Send the same
request with that tag after renaming a function or setting a type, and borer
answers with only the lines that changed, or one line saying nothing did.
Every answer ends with an evidence id; the session keeps the text behind the
last 256 ids, so a recent answer can be fetched again exactly.

### Same question, same bytes

The same binary and the same query give the same bytes, on one core or all of
them, in any order. That is a tested contract, not a habit: the gate decompiles
a corpus twice and in parallel and compares.

```console
$ borer decompile notepad.exe 0x140013150 full 0 100000 | sha256sum
b45d12089ef2280f...
$ borer decompile notepad.exe 0x140013150 full 0 100000 | sha256sum
b45d12089ef2280f...
```

### A hostile file gets an error, not a crash

Reads are bounds-checked, scans capped and walks fuel-limited, and the
loaders are fuzzed in CI. The first 300 bytes of notepad.exe:

```console
$ borer triage cut.exe
Error: loading cut.exe

Caused by:
    the file starts like a PE but its headers do not parse, even leniently: it is truncated or damaged (300 bytes; ...)
```

### Fast enough to read everything

On notepad.exe (523 functions), `borer triage` loads, discovers and ranks the
whole file in about 2.3 seconds (release build `7d9bb42c`, three runs: 2.24,
2.41, 2.29 s). A cold decompile takes under 7 ms per function at the 95th
percentile (`tests/bench.rs`, release build `70b5db2c`, three runs: 6.64,
6.48, 6.49 ms). Both on one desktop machine. The time bars, 25 ms at p95 and
5 s at worst per function, are part of the gate. An agent can read every
function instead of guessing where to look.

## Platforms

| Architecture | Disassemble | Decompile | Emulation tools |
| --- | --- | --- | --- |
| x86, x86-64 | yes | yes | yes |
| arm64 | yes | yes | yes |
| 32-bit ARM (A32, Thumb-2) | yes | yes | no |
| RISC-V (RV32, RV64 GC) | yes | yes | no |

Formats: PE, ELF, Mach-O, raw code and memory dumps.

## Install

macOS and Linux:

```bash
curl -fsSL https://borer.lol/install | sh
```

Windows (PowerShell):

```powershell
irm https://borer.lol/install.ps1 | iex
```

The installer downloads the latest release, checks it against the release's
SHA256SUMS and registers borer with every MCP client it finds: Claude Code,
Claude Desktop, Cursor, VS Code, Windsurf, Zed, Codex CLI, Gemini CLI and 20
more. Restart the clients it names afterwards.

Package managers install the same release binary:

```bash
cargo binstall borer                  # or cargo install borer
brew install imjustprism/tap/borer    # macOS, Linux x64
npm install -g @imjustprism/borer     # or npx -y @imjustprism/borer
pipx install borer                    # or uvx borer
```

On Windows with Scoop: `scoop bucket add imjustprism
https://github.com/imjustprism/scoop-bucket`, then `scoop install
imjustprism/borer`. In Claude Code: `/plugin marketplace add imjustprism/borer`,
then `/plugin install borer@borer`. From source, with the toolchain
`rust-toolchain.toml` pins: `cargo build --release`.

Register an installed binary with `borer setup --apply` (`borer setup` alone
shows each file and entry it would write, in each client's own format). Most
clients (Claude Desktop, Cursor, Windsurf, Gemini CLI and others) read
`mcpServers`, with the binary's absolute path:

```json
{ "mcpServers": { "borer": { "command": "/path/to/borer", "args": [] } } }
```

VS Code reads `servers` (with `"type": "stdio"`), Zed `context_servers`, and
Codex CLI `[mcp_servers.borer]` in its TOML; `borer setup` writes each in its
own format.

To uninstall, run `borer setup --apply --remove`, then delete the binary and
its cache (`%LOCALAPPDATA%\borer` or `~/.cache/borer`). The installers do all
three with `--uninstall` (`-Uninstall` in PowerShell).

## Quick start

From an agent:

1. `load_binary`
2. read `borer://triage`: what the file is, how it is protected, where to start
3. `find_function_by_string`, `strings` or `symbols`
4. `function_summary`, then `decompile`
5. `xrefs`, `cfg` or `callgraph` to go wider

Any address argument takes `0x` hex, decimal or a name.

| Area | Tools |
| --- | --- |
| Load | `load_binary`, `binary_info`, `fetch_pdb`, `reload` |
| Find | `functions`, `function`, `symbols`, `strings`, `search`, `find_function_by_string`, `find_crypto_constants`, `entropy` |
| Read code | `function_summary`, `function_strings`, `decompile`, `decompile_batch`, `disassemble`, `disassemble_function`, `cfg`, `callgraph`, `reaches`, `xrefs`, `class_layout` |
| Read data | `read`, `hexdump` |
| Annotate | `set_name`, `set_comment`, `set_type`, `types`, `annotations`, `save_project`, `load_project` |
| Live process (Windows) | `live_attach`, `live_detach`, `live_modules`, `live_read`, `live_object`, `live_instances`, `live_watch`, `live_scan` |
| Anything else | `query`, `script` |

Deeper analyses are `borer://` resources: taint, struct layout, emulation,
input solving, unpacking, deobfuscation, binary diff, decoded strings, IOCs,
signatures and YARA rules. `borer://help` lists them all, and a client without
resource support passes the same URI to `query`.

From the command line:

```bash
borer triage    sample.exe
borer decompile sample.exe <address|name>
borer xrefs     sample.exe <address|name>
borer certify   sample.exe <address|name>   # how far the decompiled text was checked
borer help                                  # every command
```

`--pack <file>` loads target knowledge, `--no-pdb` skips the companion PDB, and
`--arch x86|x64|arm64` with `--base` and `--entry` maps raw code or a dump.

## More

What borer does not do yet is in [docs/limits.md](docs/limits.md). It has no
telemetry; the few things that reach the network are listed in
[docs/network.md](docs/network.md).

## Contributing

`python scripts/gate.py` runs what CI runs. The rules for people and coding
agents are in [`borer.rules`](borer.rules), and the terms for contributions in
[CONTRIBUTING.md](CONTRIBUTING.md).

| Crate | Role |
| --- | --- |
| [`borer-engine`](crates/borer-engine) | The analysis core: loading, lifting, emulation, decompilation. Pure and synchronous. |
| [`borer`](crates/borer) | The MCP server and CLI over the engine. |
| [`borer-live`](crates/borer-live) | Read-only access to a running process. |
| [`borer-fixtures`](crates/borer-fixtures) | Programs the tests decompile and check against their source. |

## License

borer is free software under the [GNU Affero General Public License
v3.0](LICENSE) (AGPL-3.0-only). If you distribute borer or a modified version,
or let users interact with a modified version over a network, you must offer
its complete source under the same license. Versions 0.1.0 and 0.1.1 were
released under MIT. A
commercial license is available for uses the AGPL does not fit: open an issue
or reach out on GitHub.

Third-party notices are in [NOTICE](NOTICE), and each release archive carries
the licenses of everything the binary links. Ghidra is a project of the NSA.
IDA and Hex-Rays are trademarks of Hex-Rays SA, Binary Ninja is a trademark of
Vector 35, and Claude is a trademark of Anthropic. borer is not affiliated with
or endorsed by any of them.
