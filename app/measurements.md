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
