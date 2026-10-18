#!/usr/bin/env python3
"""borer against Ghidra headless, on the same binaries, in the scenarios an agent meets.

Usage: python scripts/run/vs_ghidra.py --ghidra <install dir> [--borer PATH]
       [--sample N] [--all-under MB] <binary>...

Per binary and per tool it measures:

- ready_cold_s: from starting the tool to being able to answer about the
  binary's code. borer: a fresh MCP server, load_binary and a functions
  call. Ghidra: analyzeHeadless importing the file and running its
  auto-analysis, up to when a post-script starts.
- ready_warm_s: the same once the work is kept. borer: a fresh server again
  (its analysis is not kept, so this is a second cold start). Ghidra: reopening
  the analyzed project with -noanalysis.
- decompile_ms p50/p95: one function at a time over an even sample of each
  tool's own functions, the whole function (borer limit 0).
- all_fps: every function decompiled, in functions per second, for binaries
  under --all-under MB. borer: `borer index` (parallel, as it ships). Ghidra:
  one decompiler process over every function, as a script does it.
- peak_mb: the largest resident memory of the tool's process tree.

Both tools run one after the other, never at once. Writes a TSV to stdout.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

import psutil

HERE = Path(__file__).resolve().parent
_ID = 0


class Peak:
    """Polls a process tree's resident memory and keeps the largest total."""

    def __init__(self, pid: int) -> None:
        self.pid = pid
        self.peak = 0
        self._stop = threading.Event()
        self._t = threading.Thread(target=self._run, daemon=True)
        self._t.start()

    def _run(self) -> None:
        while not self._stop.is_set():
            try:
                root = psutil.Process(self.pid)
                tree = [root, *root.children(recursive=True)]
                rss = sum(p.memory_info().rss for p in tree if p.is_running())
                self.peak = max(self.peak, rss)
            except psutil.Error:
                pass
            time.sleep(0.05)

    def stop(self) -> int:
        """Stops polling; returns the peak in MB."""
        self._stop.set()
        self._t.join()
        return round(self.peak / 2**20)


def _send(proc: subprocess.Popen, method: str, params: dict | None = None) -> int:
    """Sends a JSON-RPC request, returning its id."""
    global _ID
    _ID += 1
    msg: dict = {"jsonrpc": "2.0", "id": _ID, "method": method}
    if params is not None:
        msg["params"] = params
    assert proc.stdin is not None
    proc.stdin.write(json.dumps(msg).encode() + b"\n")
    proc.stdin.flush()
    return _ID


def _reply(proc: subprocess.Popen, rid: int) -> dict:
    """Reads messages until the reply to `rid`."""
    assert proc.stdout is not None
    while True:
        line = proc.stdout.readline()
        if not line:
            raise EOFError("server closed its stdout")
        msg = json.loads(line)
        if msg.get("id") == rid:
            if "error" in msg:
                raise RuntimeError(str(msg["error"]))
            return msg["result"]


def _tool(proc: subprocess.Popen, name: str, args: dict) -> str:
    """Calls a tool and returns its text."""
    result = _reply(proc, _send(proc, "tools/call", {"name": name, "arguments": args}))
    return "".join(p.get("text", "") for p in result.get("content", []) if p.get("type") == "text")


def _server(borer: str) -> subprocess.Popen:
    """Starts a borer MCP server and performs the handshake."""
    proc = subprocess.Popen(
        [borer], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL
    )
    _reply(
        proc,
        _send(
            proc,
            "initialize",
            {
                "protocolVersion": "2025-06-18",
                "capabilities": {},
                "clientInfo": {"name": "vs-ghidra", "version": "0"},
            },
        ),
    )
    assert proc.stdin is not None
    proc.stdin.write(b'{"jsonrpc":"2.0","method":"notifications/initialized"}\n')
    proc.stdin.flush()
    return proc


def _ready(borer: str, binary: str) -> tuple[subprocess.Popen, float]:
    """Starts borer and loads and analyzes `binary`; returns the server and seconds."""
    t0 = time.perf_counter()
    proc = _server(borer)
    _tool(proc, "load_binary", {"path": binary})
    _tool(proc, "functions", {"limit": 1})
    return proc, time.perf_counter() - t0


def _entries(proc: subprocess.Popen) -> list[str]:
    """Every function entry borer lists, page by page."""
    out: list[str] = []
    offset = 0
    while True:
        text = _tool(proc, "functions", {"offset": offset, "limit": 300})
        rows = [line.split()[0] for line in text.splitlines() if line.startswith("0x")]
        out += rows
        if len(rows) < 300:
            return out
        offset += 300


def _pct(values: list[float], q: float) -> float:
    """The q-th quantile of values (0..1)."""
    s = sorted(values)
    return s[min(len(s) - 1, int(q * len(s)))]


def borer_row(borer: str, binary: str, sample: int, do_all: bool) -> dict:
    """Measures borer on one binary."""
    row: dict = {}
    # One untimed start first: a new executable's first run pays the
    # antivirus scan, which is not borer's time.
    warm_up, _ = _ready(borer, binary)
    warm_up.kill()
    proc, cold = _ready(borer, binary)
    peak = Peak(proc.pid)
    row["ready_cold_s"] = round(cold, 2)
    entries = _entries(proc)
    row["functions"] = len(entries)
    step = max(1, len(entries) / sample)
    picked = [entries[int(i * step)] for i in range(min(sample, len(entries)))]
    times = []
    for e in picked:
        t = time.perf_counter()
        _tool(proc, "decompile", {"address": e, "limit": 0})
        times.append((time.perf_counter() - t) * 1000)
    # The first decompile also lifts the binary, as Ghidra's opens its decompiler.
    row["first_decompile_ms"] = round(times[0], 1)
    rest = times[1:] or times
    row["decompile_p50_ms"] = round(statistics.median(rest), 1)
    row["decompile_p95_ms"] = round(_pct(rest, 0.95), 1)
    row["decompile_mean_ms"] = round(statistics.mean(rest), 1)
    row["peak_mb"] = peak.stop()
    proc.kill()
    proc2, warm = _ready(borer, binary)
    proc2.kill()
    row["ready_warm_s"] = round(warm, 2)
    if do_all:
        cache = tempfile.mkdtemp(prefix="borer-idx-")
        env = {**os.environ, "BORER_INDEX_CACHE": cache, "LOCALAPPDATA": cache}
        t = time.perf_counter()
        done = subprocess.run(
            [borer, "index", binary], env=env, capture_output=True, text=True, check=False
        )
        # `index` says how long the decompiling took, without the load.
        said = re.search(r"indexed in ([\d.]+) s", done.stderr)
        secs = float(said.group(1)) if said else time.perf_counter() - t
        row["all_fps"] = round(len(entries) / max(secs, 1e-3))
        shutil.rmtree(cache, ignore_errors=True)
    return row


def _headless(ghidra: Path, args: list[str]) -> tuple[float, int, float]:
    """Runs analyzeHeadless; returns (start epoch s, peak MB, wall s)."""
    exe = ghidra / "support" / ("analyzeHeadless.bat" if os.name == "nt" else "analyzeHeadless")
    start = time.time()
    proc = subprocess.Popen([str(exe), *args], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    peak = Peak(proc.pid)
    proc.wait()
    return start, peak.stop(), time.time() - start


def _read(out: Path) -> tuple[float, int, list[float]]:
    """Reads BenchDecompile's file: (started epoch s, functions, ms per decompile)."""
    started, total, times = 0.0, 0, []
    for line in out.read_text().splitlines():
        parts = line.split("\t")
        if parts[0] == "started":
            started = int(parts[1]) / 1000
        elif parts[0] == "functions":
            total = int(parts[1])
        elif len(parts) == 3:
            times.append(float(parts[1]))
    return started, total, times


def ghidra_row(ghidra: Path, binary: str, sample: int, do_all: bool) -> dict:
    """Measures Ghidra headless on one binary."""
    row: dict = {}
    work = Path(tempfile.mkdtemp(prefix="vsg-"))
    script = ["-scriptPath", str(HERE / "ghidra"), "-postScript", "BenchDecompile.java"]
    out = work / "cold.tsv"
    start, peak, _ = _headless(
        ghidra, [str(work), "p", "-import", binary, *script, str(out), str(sample)]
    )
    began, total, times = _read(out)
    row["ready_cold_s"] = round(began - start, 2)
    row["functions"] = total
    row["decompile_p50_ms"] = round(statistics.median(times[1:] or times), 1)
    row["decompile_p95_ms"] = round(_pct(times[1:] or times, 0.95), 1)
    row["decompile_mean_ms"] = round(statistics.mean(times[1:] or times), 1)
    row["first_decompile_ms"] = round(times[0], 1) if times else ""
    row["peak_mb"] = peak
    out2 = work / "warm.tsv"
    start, _, _ = _headless(
        ghidra, [str(work), "p", "-process", "-noanalysis", *script, str(out2), "1"]
    )
    row["ready_warm_s"] = round(_read(out2)[0] - start, 2)
    if do_all:
        out3 = work / "all.tsv"
        _, _, _ = _headless(
            ghidra, [str(work), "p", "-process", "-noanalysis", *script, str(out3), "0"]
        )
        _, total, all_times = _read(out3)
        row["all_fps"] = round(total / (sum(all_times) / 1000)) if all_times else ""
    shutil.rmtree(work, ignore_errors=True)
    return row


def main() -> int:
    """Runs both tools over every binary and prints a TSV."""
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ghidra", required=True, type=Path, help="Ghidra install directory")
    ap.add_argument("--borer", default="target/release/borer.exe", help="borer binary")
    ap.add_argument("--sample", type=int, default=100, help="functions to decompile each")
    ap.add_argument("--all-under", type=float, default=1.6, help="MB; decompile all below it")
    ap.add_argument("binaries", nargs="+")
    a = ap.parse_args()
    cols = [
        "binary",
        "mb",
        "tool",
        "functions",
        "ready_cold_s",
        "ready_warm_s",
        "decompile_p50_ms",
        "decompile_p95_ms",
        "decompile_mean_ms",
        "first_decompile_ms",
        "all_fps",
        "peak_mb",
    ]
    print("\t".join(cols), flush=True)
    for b in a.binaries:
        mb = round(os.path.getsize(b) / 2**20, 2)
        do_all = mb <= a.all_under
        for tool in ("borer", "ghidra"):
            try:
                measured = (
                    borer_row(a.borer, b, a.sample, do_all)
                    if tool == "borer"
                    else ghidra_row(a.ghidra, b, a.sample, do_all)
                )
                row = {"binary": Path(b).name, "mb": mb, "tool": tool, **measured}
            except (RuntimeError, EOFError, OSError, ValueError) as e:
                print(f"FAIL {tool} {b}: {e}", file=sys.stderr, flush=True)
                continue
            print("\t".join(str(row.get(c, "")) for c in cols), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
