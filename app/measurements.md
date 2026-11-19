# borer-app spike: measured go/no-go

Verdict: **go**. The Zed variant meets every UI bar on this machine.

## Setup

- Build: `cargo build --release` of the `add/app-spike` branch at 985dd217 (this
  report is the commit after it), Zed `v1.28.1`
  (`e8bc16acee5ae1937600d571d441c4b5d7b0d288`), Rust 1.98.1.
- Machine: AMD Ryzen 7 9800X3D, AMD Radeon RX 9070 XT (240 Hz display) beside
  the CPU's Radeon graphics. gpui reported a 2 ms refresh interval for the
  window, so the frame numbers below hold at 500 Hz pacing.
- Script: `python scripts/run/app_measure.py --exe <release borer-app.exe>`,
  one full run; startup and open are 10 runs each.
- The measurement modes run through a `Harness` entity that wraps the app view.
  A plain `borer-app [binary]` window has none of it.

## Bars

| Measure | Result | Bar | Pass |
| --- | --- | --- | --- |
| 100,000-row list scroll, frame draw p99 | 2.98 ms (max 4.10) | 8.3 ms | yes |
| 1,000,000-line code scroll, frame draw p99 | 5.44 ms (max 41.6) | 8.3 ms | yes |
| Input to paint p99, 200 keys and 100 clicks via `SendInput` | 5.46 ms (p50 2.65, max 7.28) | 16 ms | yes |
| First frame, median of 10 | 141.7 ms (max 154.2) | 300 ms | yes |
| notepad.exe open to its function list, median of 10 | 182.3 ms (max 186.1) | 1 s | yes |
| Memory beyond the engine (`--measure-memory` minus `--headless`) | 78.0 MB (101 MB minus 23 MB) | 150 MB | yes |

Details:

- **List scroll.** The rows of `edgehtml.dll`, which analyzed in 2.3 s, are
  98,962 rows repeated by index to 100,000. Present interval p99 is 3.63 ms.
- **Code scroll.** The lines of every decompile view of notepad.exe are 24,427
  lines repeated by index to 1,000,000. Present interval p99 is 5.82 ms. The one
  41.6 ms frame is the slowest of 4,046.
- **Input.**
  - End to end, from `SendInput` to the present of the frame that shows the
    result, the background filter or decompile included.
  - The background work behind an input took 1.97 ms at p99. gpui's own
    input-to-frame histogram reads 4.58 ms at p99.
- **UI-thread engine calls: 0 in every phase.** The count covers engine calls
  routed through `run_engine`. The worker test
  `only_the_worker_names_engine_compute_calls` keeps every other module from
  calling the engine directly.

## Cost

| Item | Value |
| --- | --- |
| Clean `cargo build --release` (empty target directory) | 440 s |
| Incremental release build after touching one app file | 160 s |
| `borer-app.exe` | 36.2 MB |
| `borer_app.pdb` | 99.5 MB |
| Zed in cargo's git cache (checkout plus database) | 503 MB plus 408 MB |
| Unique crates, Windows graph (`cargo tree -e normal,build`) | 326 |
| `cargo deny check bans licenses sources` | bans ok, licenses ok, sources ok |
| Network connections opened during every measured run | none (154 polls) |

Zed crates in the graph:
- GPL-3.0-or-later: `ui`, `ui_macros`, `theme`, `syntax_theme`, `component`,
  `icons`, `menu`.
- Apache-2.0: `gpui`, `gpui_macros`, `gpui_platform`, `gpui_windows`,
  `gpui_shared_string`, `gpui_util`, `collections`, `refineable`,
  `derive_refineable`, `sum_tree`, `scheduler`, `http_client`, `ztracing`,
  `ztracing_macro`.

## What the spike leaves out

- **Command palette.** The spike has no palette. Zed's `command_palette`
  toggles from a `Workspace`, and a `Workspace` needs a `Project` and an
  `AppState` (client, user store, languages, fs, node runtime). Hosting the
  views in Zed's workspace is the next step, U1. Shortcuts already come from
  gpui's keymap per action, which is the list that palette reads.
- **Open path.** The app loads binaries directly and leaves packs out. The
  status line says so.
- **gpui profiler.** gpui's `profiler` feature stays on in the shipped build.
  The harness reads its histograms.

## U1-1: the app in Zed's workspace (2026-11-16)

Release build of `c3f3742f` (add/app-workspace), same machine and script as above
(`python scripts/run/app_measure.py --exe <exe>`). The window is now Zed's `Workspace`:
the functions panel in the left dock, decompile tabs in the center pane, Zed's
command palette, nav history and dock persistence. Every measured run gets a fresh
data directory of its own.

| Measure | Result | Bar | Pass |
| --- | --- | --- | --- |
| 100,000-row list scroll, frame draw p99 | 2.97 ms (max 4.99) | 8.3 ms | yes |
| 1,000,000-line code scroll, frame draw p99 | 2.62 ms (max 25.8) | 8.3 ms | yes |
| Input to paint p99, 200 keys and 100 clicks via `SendInput` | 6.83 ms (p50 3.24, max 8.29) | 16 ms | yes |
| First frame, median of 10 | 190.6 ms (max 237.6) | 300 ms | yes |
| notepad.exe open to its function list, median of 10 | 247.0 ms (max 272.1) | 1 s | yes |
| Memory beyond the engine | 87.1 MB (108.7 MB minus 21.7 MB) | 150 MB | yes |

- List scroll: `edgehtml.dll` (2.66 s to analyze), 98,962 rows repeated to 100,000;
  present p99 3.88 ms. Code scroll: notepad's 24,427 lines repeated to 1,000,000;
  present p99 3.79 ms. Both report the scrolled view painted.
- Input: background work behind an input 1.88 ms at p99; gpui's own input-to-frame
  histogram 5.76 ms at p99. Keys are counted where gpui intercepts them, before a
  binding or the filter editor takes them.
- Folder drop: a folder whose `.zed/settings.json` names a context server, dropped
  on the Start tab and on a decompile tab, reaches the tab's handler both times;
  the project keeps 0 folders.
- UI-thread engine calls: 0 in every phase. Sockets: none (180 polls). Child
  processes: 0 in every run, counted by a job object each run joins before it runs.
- Compared with the spike, first frame is 49 ms slower (Zed's database, settings,
  keymap and workspace), open to list 65 ms slower, memory 9 MB more.

| Cost | Value |
| --- | --- |
| Clean `cargo build --release` (empty release directory, dependencies already fetched) | 644 s |
| Incremental release build after touching one app file | 258 s |
| `borer-app.exe` | 137.5 MB |
| Unique crates, Windows graph (`cargo tree -p borer-app -e normal,build --target x86_64-pc-windows-msvc --prefix none \| sort -u`) | 736 (103 from Zed) |
| `cargo deny check bans licenses sources` | ok (licenses added for Zed's graph, each named in deny.toml) |

- The exe grew from 36 MB: Zed's workspace pulls `language`, which turns on
  tree-sitter's `wasm` feature (wasmtime and cranelift) unconditionally, plus
  `project`, `client` and their TLS stack; none of that runs, but it links.

## Action bars

`python scripts/run/app_measure.py` runs `--measure --phase actions`: on notepad.exe, then
on the large DLL the list scroll loads, each action 50 times on the first functions by
address that call another (the first call token of each for xrefs), dispatched through
the path its key takes. Ack is dispatch to the first presented frame whose stamp (active
tab and its revision, its top line, the functions panel's row and filter, the go-to
picker, the xrefs panel's referent and rows, status line) differs, a count of running
requests left out as nothing on screen shows it; settle is dispatch to the presented frame
after which no job runs, every open view shows the binary's state and the stamp holds
one more frame. Pan and zoom sweep 2 s each on notepad's 20 largest graphs and the large
DLL's largest, timed by frame draw. A large DLL that is missing or too slow to analyze
is printed as skipped. The bars are `BARS` in `borer-app/src/measure/actions.rs`:

| Action | Ack p99 | Settle p95, notepad | Settle p95, large DLL |
| --- | --- | --- | --- |
| go to a name (confirm) | 16 ms | 50 ms | 100 ms |
| Find Everywhere keystroke | 16 ms | 16 ms | 50 ms |
| xrefs on a call token | 16 ms | 16 ms | 33 ms |
| toggle listing (warm) | 16 ms | 16 ms | 16 ms |
| open graph (warm) | 16 ms | 50 ms | 100 ms |
| functions filter keystroke | 16 ms | 16 ms | 50 ms |
| open overview | 16 ms | 500 ms | reported |
| back | 16 ms | reported | reported |
| graph pan, zoom: frame draw p99 | 8.3 ms | | |

First run, 2026-11-18, release build of add/app-check-gutter (the tip that adds this
line), Ryzen 7 9800X3D, another agent's cargo build running on the machine throughout, so
the times are upper bounds. Ack and settle p95/p99 in ms:

| Bench | Action | Ack p95/p99 | Settle p95/p99 |
| --- | --- | --- | --- |
| notepad | goto | 13.3/15.4 | 13.3/15.4 |
| notepad | find | 5.4/7.1 | 5.4/7.1 |
| notepad | xrefs | none seen (36 still, 14 skipped) | 2.2/2.2 |
| notepad | listing | 13.3/14.0 | 13.3/14.0 |
| notepad | graph | 7.7/8.2 | 7.7/8.2 |
| notepad | filter | 8.6/10.3 | 8.6/10.3 |
| notepad | overview | 8.9/9.9 | 9.0/2466 |
| notepad | back | 10.5/11.8 | 10.5/11.8 |
| large | goto | 10.3/11.0 | 10.8/10002 (1 late) |
| large | find | 4.5/9.7 | 11.0/11.5 |
| large | xrefs | none seen (50 still) | 2.0/2.1 |
| large | listing | 10.4/11.3 | 10.4/11.3 |
| large | graph | 8.9/11.2 | 8.9/11.2 |
| large | filter | 6.6/7.8 | 10.8/12.2 |
| large | overview | 7.0/7.6 | 7.3/8805 |
| large | back | 8.6/9.8 | 8.6/9.8 |

Graph frame draw p99: pan 2.2 ms (notepad) and 2.0 ms (large), zoom 7.8 and 5.6 ms. UI
thread engine calls: 0.

The xrefs ack was never seen because the harness docked only the functions panel before
its load, so the app's own docking returned early and the xrefs panel never existed:
xrefs opened nothing. With every panel docked as a load docks them, a rerun on the same
machine (still busy) gave: notepad xrefs ack p95/p99 6.3/6.4 ms (36 runs, 14 skipped:
targets with no call token), large xrefs ack 6.7/78.9 ms (one outlier, a miss), notepad
overview ack p99 18.0 ms (a miss); every other action as above or faster.

The full script on that build: first frame median 192 ms, notepad open median 234 ms,
memory delta 146.0 MB, list scroll draw p99 3.2 ms, code scroll draw p99 3.6 ms.

Input phase: the clicks reach the window (9 presses and 9 releases in the stalled run)
but none opened a function, so input-to-paint is reported as not measured, with that
reason, and the script fails; why a click on the announced call token opens nothing is
not found yet.
