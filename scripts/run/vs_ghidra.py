#!/usr/bin/env python3
"""borer against Ghidra headless, on the same binaries, in the scenarios an agent meets.

Usage: python scripts/run/vs_ghidra.py --ghidra <install dir> [--ghidra-zip ZIP]
       [--borer PATH] [--runs N] [--sample N] [--tools borer,ghidra] [--add]
       <binary>...

Every metric is measured --runs times (default 5), the runs of all binaries
and both tools interleaved, and a row keeps every run and its median, min,
max and spread. Before each run the script waits for a quiet machine (no
compiler process, CPU under --idle-pct), records the load it saw, and redoes
a run a compiler started during. Per binary and per tool:

- ready_cold_s: from starting the tool to its first answer about the
  binary's code, with nothing of this binary kept by the tool. borer: a
  fresh MCP server with empty caches (index, symbols, packs off), load_binary
  and functions. Ghidra: analyzeHeadless into a new project, importing the
  file and running its default auto-analysis, up to when a post-script
  starts. The Windows file cache cannot be emptied without admin, so for
  both the tool's own files and the binary are in it: one untimed start of
  each tool on another binary comes first, and the binary is read before
  every run.
- first_decompile_s: the same start up to the first function's (lowest
  address) whole decompile, including starting the decompiler.
- ready_warm_s: the same once the work is kept. borer keeps no analysis, so
  this is a fresh server again; Ghidra reopens the analyzed project with
  -noanalysis.
- decompile_ms p50/p95/mean: one function at a time over an even sample of
  each tool's own functions, the first one left out, the whole function.
- all_fps: every function decompiled, in functions per second, analysis
  excluded. borer: `index` on every core. Ghidra: the faster of its
  ParallelDecompiler on every core (what its C exporter uses,
  all_parallel_fps) and one decompiler driven one function at a time, which
  wins on small binaries. On one core (all_1core_fps): borer `index` pinned
  to one CPU against Ghidra's one decompiler.
- peak_mb: the largest resident memory of the tool's process tree over the
  cold run (analysis and the decompile sample); all_peak_mb over the every
  core sweep. The tree is polled every 20 ms, and the largest single
  process's own peak working set is a floor, so neither is overstated.

Each tool's functions are its own: Ghidra's without thunks and externals,
borer's as `functions` lists them and `index` decompiles them; rates are per
function, and both counts are kept. A run that fails is recorded with its
error, never dropped. Results go to vs_ghidra.json: a rerun replaces the
rows it measures and keeps the others; with --add it adds its runs to the
rows' runs, so two occasions can be pooled and compared (`pass`).
"""

from __future__ import annotations

import argparse
import contextlib
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import threading
import time
import zipfile
from pathlib import Path

import psutil

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
_ID = 0
# Processes that mean another build is running on the machine.
COMPILERS = {
    "cargo.exe",
    "rustc.exe",
    "clippy-driver.exe",
    "link.exe",
    "lld-link.exe",
    "rust-lld.exe",
    "cl.exe",
    "cargo",
    "rustc",
    "clippy-driver",
}
# How often a run is redone when a compiler started during it.
RETRIES = 3
# Whether this is a trial of the script: no waiting, nothing redone, runs marked.
TRIAL = False


def _compilers() -> list[str]:
    """The compiler processes running now."""
    names = set()
    for p in psutil.process_iter(["name"]):
        name = (p.info["name"] or "").lower()
        if name in COMPILERS:
            names.add(name)
    return sorted(names)


def quiet(idle_pct: float) -> float:
    """Waits until no compiler runs and CPU is under idle_pct; returns that CPU %."""
    waited = 0
    while True:
        busy = _compilers()
        cpu = psutil.cpu_percent(interval=3)
        if TRIAL or (not busy and cpu < idle_pct):
            return cpu
        if waited % 300 == 0:
            print(f"  waiting for a quiet machine: cpu {cpu}% {busy}", file=sys.stderr, flush=True)
        time.sleep(30)
        waited += 30


class Watch:
    """Polls a process tree: peak resident memory, decompiler processes, compilers seen."""

    def __init__(self, pid: int) -> None:
        self.pid = pid
        self.peak = 0
        self.own_peak = 0
        self.decompilers = 0
        self.disturbed: set[str] = set()
        self._stop = threading.Event()
        self._t = threading.Thread(target=self._run, daemon=True)
        self._t.start()

    def _run(self) -> None:
        last_scan = 0.0
        while not self._stop.is_set():
            try:
                root = psutil.Process(self.pid)
                tree = [root, *root.children(recursive=True)]
                total = 0
                kids = 0
                for p in tree:
                    try:
                        mem = p.memory_info()
                        total += mem.rss
                        self.own_peak = max(self.own_peak, getattr(mem, "peak_wset", mem.rss))
                        kids += p.name().lower().startswith("decompile")
                    except psutil.Error:
                        pass
                self.peak = max(self.peak, total)
                self.decompilers = max(self.decompilers, kids)
            except psutil.Error:
                pass
            now = time.monotonic()
            if now - last_scan > 1:
                self.disturbed.update(_compilers())
                last_scan = now
            time.sleep(0.02)

    def stop(self) -> int:
        """Stops polling; returns the peak in MB."""
        self._stop.set()
        self._t.join()
        return round(max(self.peak, self.own_peak) / 2**20)


class Disturbed(Exception):
    """A compiler ran during a measurement, so it is redone."""


def _kill(proc: subprocess.Popen) -> None:
    """Ends a process and every process under it."""
    try:
        kids = psutil.Process(proc.pid).children(recursive=True)
    except psutil.Error:
        kids = []
    for p in [proc, *kids]:
        with contextlib.suppress(psutil.Error, OSError):
            p.kill()
    proc.wait()
    psutil.wait_procs(kids, timeout=10)


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
    """Calls a tool and returns its text; a tool error raises."""
    result = _reply(proc, _send(proc, "tools/call", {"name": name, "arguments": args}))
    text = "".join(p.get("text", "") for p in result.get("content", []) if p.get("type") == "text")
    if result.get("isError"):
        raise RuntimeError(f"{name} {args}: {text[:200]}")
    return text


def _env(cache: Path) -> dict:
    """borer's environment with every cache in `cache`, packs and the update check off."""
    env = {
        k: v for k, v in os.environ.items() if k not in {"BORER_PACKS", "BORER_BUDGET", "BORER_RAW"}
    }
    return env | {
        "BORER_CACHE_DIR": str(cache / "index"),
        "BORER_SYMCACHE": str(cache / "symsrv"),
        "LOCALAPPDATA": str(cache),
        "XDG_CACHE_HOME": str(cache),
        "BORER_AUTO_PACKS": "0",
        "BORER_NO_UPDATE_CHECK": "1",
    }


def _server(borer: str, env: dict) -> subprocess.Popen:
    """Starts a borer MCP server and performs the handshake."""
    proc = subprocess.Popen(
        [borer], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env
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


def _first_entry(text: str) -> str:
    """The first function entry in a `functions` answer."""
    for line in text.splitlines():
        if line.startswith("0x"):
            return line.split()[0]
    raise RuntimeError(f"functions listed none: {text[:200]}")


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


def _spread(times: list[float]) -> dict:
    """p50, p95 and mean of per-function milliseconds."""
    return {
        "decompile_p50_ms": round(statistics.median(times), 2),
        "decompile_p95_ms": round(_pct(times, 0.95), 2),
        "decompile_mean_ms": round(statistics.mean(times), 2),
    }


def _ready(borer: str, binary: str, env: dict) -> tuple[subprocess.Popen, Watch, float, str]:
    """Starts borer, loads `binary` and lists one function: (server, watch, seconds, entry)."""
    t0 = time.perf_counter()
    proc = _server(borer, env)
    watch = Watch(proc.pid)
    _tool(proc, "load_binary", {"path": binary})
    first = _first_entry(_tool(proc, "functions", {"limit": 1}))
    return proc, watch, time.perf_counter() - t0, first


def borer_run(borer: str, binary: str, sample: int) -> dict:
    """Measures borer once on one binary, every cache empty at the start."""
    row: dict = {}
    cache = Path(tempfile.mkdtemp(prefix="vsg-borer-"))
    env = _env(cache)
    try:
        Path(binary).read_bytes()
        t0 = time.perf_counter()
        proc, watch, cold, first = _ready(borer, binary, env)
        try:
            row["ready_cold_s"] = round(cold, 3)
            _tool(proc, "decompile", {"address": first, "limit": 0})
            row["first_decompile_s"] = round(time.perf_counter() - t0, 3)
            entries = _entries(proc)
            row["functions"] = len(entries)
            want = min(sample, len(entries) - 1)
            step = (len(entries) - 1) / max(want, 1)
            times = []
            for i in range(want):
                t = time.perf_counter()
                _tool(proc, "decompile", {"address": entries[1 + int(i * step)], "limit": 0})
                times.append((time.perf_counter() - t) * 1000)
            row |= _spread(times)
        finally:
            row["peak_mb"] = watch.stop()
            _kill(proc)
        if watch.disturbed and not TRIAL:
            raise Disturbed(watch.disturbed)
        proc, watch, warm, _ = _ready(borer, binary, env)
        watch.stop()
        _kill(proc)
        row["ready_warm_s"] = round(warm, 3)
        for key, one_core in (("all", False), ("all_1core", True)):
            shutil.rmtree(cache / "index", ignore_errors=True)
            fps, n, peak = _index(borer, binary, env, one_core)
            row[f"{key}_fps"] = fps
            row["index_functions"] = n
            if not one_core:
                row["all_peak_mb"] = peak
    finally:
        shutil.rmtree(cache, ignore_errors=True)
    return row


def _index(borer: str, binary: str, env: dict, one_core: bool) -> tuple[float, int, int]:
    """Runs `borer index`: (functions per second, functions, peak MB)."""
    proc = subprocess.Popen(
        [borer, "index", binary],
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if one_core:
        psutil.Process(proc.pid).cpu_affinity([2])
    watch = Watch(proc.pid)
    out, err = proc.communicate()
    peak = watch.stop()
    if watch.disturbed and not TRIAL:
        raise Disturbed(watch.disturbed)
    if proc.returncode != 0:
        raise RuntimeError(f"index exited {proc.returncode}: {err.strip()[-300:]}")
    # `index` says how long the decompiling took, without the load and analysis.
    said = re.search(r"indexed in ([\d.]+) s", err)
    count = re.search(r"# indexed (\d+) functions", out)
    if said is None or count is None:
        raise RuntimeError(f"index did not build: {out.strip()} {err.strip()[-300:]}")
    n = int(count.group(1))
    return round(n / max(float(said.group(1)), 1e-3), 1), n, peak


def _headless(ghidra: Path, args: list[str], log: Path) -> tuple[float, Watch]:
    """Runs analyzeHeadless; returns (start epoch s, stopped watch)."""
    exe = ghidra / "support" / ("analyzeHeadless.bat" if os.name == "nt" else "analyzeHeadless")
    with log.open("w", encoding="utf-8", errors="replace") as sink:
        start = time.time()
        proc = subprocess.Popen([str(exe), *args], stdout=sink, stderr=subprocess.STDOUT)
        watch = Watch(proc.pid)
        proc.wait()
    watch.stop()
    if watch.disturbed and not TRIAL:
        raise Disturbed(watch.disturbed)
    if proc.returncode != 0:
        raise RuntimeError(f"analyzeHeadless exited {proc.returncode}, see {log}")
    return start, watch


def _read(out: Path, log: Path) -> dict:
    """Reads BenchDecompile's file: started, functions, first, all_ms, failed, times."""
    if not out.exists():
        tail = log.read_text(encoding="utf-8", errors="replace")[-600:]
        raise RuntimeError(f"BenchDecompile wrote nothing: {tail}")
    got: dict = {"times": []}
    for line in out.read_text().splitlines():
        parts = line.split("\t")
        if parts[0] in {"started", "functions", "cores", "failed"}:
            got[parts[0]] = int(parts[1])
        elif parts[0] in {"first", "all_ms"}:
            got[parts[0]] = float(parts[1])
        elif len(parts) == 3:
            got["times"].append(float(parts[1]))
    return got


def ghidra_run(ghidra: Path, binary: str, sample: int) -> dict:
    """Measures Ghidra headless once on one binary, in a new project."""
    row: dict = {}
    work = Path(tempfile.mkdtemp(prefix="vsg-ghidra-"))
    script = ["-scriptPath", str(HERE / "ghidra"), "-postScript", "BenchDecompile.java"]
    try:
        Path(binary).read_bytes()
        out, log = work / "cold.tsv", work / "cold.log"
        start, watch = _headless(
            ghidra, [str(work), "p", "-import", binary, *script, str(out), str(sample)], log
        )
        got = _read(out, log)
        row["ready_cold_s"] = round(got["started"] / 1000 - start, 3)
        row["first_decompile_s"] = round(got["started"] / 1000 + got["first"] / 1000 - start, 3)
        row["functions"] = got["functions"]
        row |= _spread(got["times"])
        row["sample_failed"] = got["failed"]
        row["peak_mb"] = watch.stop()
        out, log = work / "warm.tsv", work / "warm.log"
        start, _ = _headless(
            ghidra, [str(work), "p", "-process", "-noanalysis", *script, str(out), "1"], log
        )
        row["ready_warm_s"] = round(_read(out, log)["started"] / 1000 - start, 3)
        for key, mode in (("all_parallel", ["parallel"]), ("all_1core", [])):
            out, log = work / f"{key}.tsv", work / f"{key}.log"
            _, watch = _headless(
                ghidra,
                [str(work), "p", "-process", "-noanalysis", *script, str(out), "0", *mode],
                log,
            )
            got = _read(out, log)
            row[f"{key}_fps"] = round(got["functions"] / (got["all_ms"] / 1000), 1)
            row[f"{key}_failed"] = got["failed"]
            if mode:
                row["all_peak_mb"] = watch.stop()
                row["all_decompilers"] = watch.decompilers
        # On a small binary one decompiler beats starting one per core: Ghidra's best counts.
        row["all_fps"] = max(row["all_parallel_fps"], row["all_1core_fps"])
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return row


COLUMNS = {
    "functions": "functions",
    "index_functions": "indexFunctions",
    "ready_cold_s": "readyColdS",
    "first_decompile_s": "firstDecompileS",
    "ready_warm_s": "readyWarmS",
    "decompile_p50_ms": "decompileP50Ms",
    "decompile_p95_ms": "decompileP95Ms",
    "decompile_mean_ms": "decompileMeanMs",
    "sample_failed": "sampleFailed",
    "all_fps": "allFps",
    "all_parallel_fps": "allFpsParallel",
    "all_parallel_failed": "allFailed",
    "all_1core_fps": "allFps1Core",
    "all_1core_failed": "allFailed1Core",
    "peak_mb": "peakMb",
    "all_peak_mb": "allPeakMb",
    "all_decompilers": "allDecompilers",
}

# Whether a larger value is better, for the comparison with the last run.
HIGHER = {"functions", "allFps", "allFpsParallel", "allFps1Core"}


def _machine() -> str:
    """The CPU, core counts, memory and OS, as one line."""
    cpu = platform.processor()
    if os.name == "nt":
        import winreg

        with winreg.OpenKey(
            winreg.HKEY_LOCAL_MACHINE, r"HARDWARE\DESCRIPTION\System\CentralProcessor\0"
        ) as key:
            cpu = str(winreg.QueryValueEx(key, "ProcessorNameString")[0]).strip()
    cores = psutil.cpu_count(logical=False)
    threads = psutil.cpu_count()
    ram = round(psutil.virtual_memory().total / 2**30)
    return f"{cpu}, {cores} cores / {threads} threads, {ram} GB, {platform.system()} {platform.release()}"


def _java(ghidra: Path) -> tuple[str, Path | None]:
    """The version and home of the JDK analyzeHeadless runs: java_home.save, else PATH."""
    version = (ghidra / "Ghidra" / "application.properties").read_text(encoding="utf-8")
    found = re.search(r"application\.version=(\S+)", version)
    saved = Path(os.environ.get("APPDATA", "")) / "ghidra"
    java = "java"
    if found:
        home = saved / f"ghidra_{found.group(1)}_PUBLIC" / "java_home.save"
        if home.exists():
            java = str(Path(home.read_text(encoding="utf-8").strip()) / "bin" / "java")
    done = subprocess.run(
        [java, "-XshowSettings:properties", "-version"], capture_output=True, text=True, check=False
    )
    props = {
        k.strip(): v.strip()
        for k, _, v in (line.partition(" = ") for line in done.stderr.splitlines())
        if v
    }
    home = props.get("java.home")
    return props.get("java.version", "?"), Path(home) if home else None


def _tree_mb(root: Path) -> float:
    """The size of every file under root, in MB."""
    total = sum(f.stat().st_size for f in root.rglob("*") if f.is_file())
    return round(total / 2**20, 1)


def _commit() -> str:
    """The borer commit the run measures, with a mark when the tree is dirty."""
    head = subprocess.run(
        ["git", "-C", str(REPO), "rev-parse", "--short", "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    ).stdout.strip()
    dirty = subprocess.run(
        ["git", "-C", str(REPO), "status", "--porcelain", "--", "crates"],
        capture_output=True,
        text=True,
        check=False,
    ).stdout.strip()
    return head + ("-dirty" if dirty else "")


def _meta(borer: str, ghidra: Path, ghidra_zip: Path | None) -> dict:
    """What a reader needs to judge the numbers: machine, versions, install sizes."""
    said = subprocess.run([borer, "--version"], capture_output=True, text=True, check=False)
    borer_version = said.stdout.split()[-1] if said.stdout.strip() else "?"
    props = (ghidra / "Ghidra" / "application.properties").read_text(encoding="utf-8")
    found = re.search(r"application\.version=(\S+)", props)
    ghidra_version = found.group(1) if found else "?"
    java_version, java_home = _java(ghidra)
    # What a user installs: the release zip's files, not a tree extensions were added to.
    ghidra_files = (
        round(sum(i.file_size for i in zipfile.ZipFile(ghidra_zip).infolist()) / 2**20, 1)
        if ghidra_zip
        else _tree_mb(ghidra)
    )
    jdk = _tree_mb(java_home) if java_home else 0
    return {
        "machine": _machine(),
        "versions": f"borer {borer_version}, Ghidra {ghidra_version} headless, Java {java_version}",
        "borerCommit": _commit(),
        "date": time.strftime("%Y-%m-%d"),
        "installMb": {
            "borer": round(os.path.getsize(borer) / 2**20, 1),
            "ghidra": round(ghidra_files + jdk),
        },
        "installParts": {"ghidraFiles": ghidra_files, "jdk": jdk},
    }


def _stats(values: list[float]) -> dict:
    """Median, min, max and spread ((max - min) / median, %) of one metric's runs."""
    med = statistics.median(values)
    return {
        "median": round(med, 3),
        "min": round(min(values), 3),
        "max": round(max(values), 3),
        "spreadPct": round((max(values) - min(values)) / med * 100, 1) if med else 0.0,
        "n": len(values),
    }


def _summarize(row: dict) -> None:
    """Sets a row's flat values (medians, which the site reads) and stats from its runs."""
    good = [r for r in row["runs"] if "error" not in r]
    row["stats"] = {}
    for key in COLUMNS.values():
        values = [r[key] for r in good if isinstance(r.get(key), (int, float))]
        if values:
            row["stats"][key] = _stats(values)
            row[key] = row["stats"][key]["median"]
            if key in {"functions", "indexFunctions", "peakMb", "allPeakMb", "allDecompilers"}:
                row[key] = round(row[key])
        else:
            row.pop(key, None)
    passes = sorted({r["pass"] for r in good})
    row["passes"] = {
        p: {
            key: round(statistics.median(v), 3)
            for key in COLUMNS.values()
            if (
                v := [
                    r[key] for r in good if r["pass"] == p and isinstance(r.get(key), (int, float))
                ]
            )
        }
        for p in passes
    }
    row["failures"] = [r for r in row["runs"] if "error" in r]


def _ratios(rows: list[dict]) -> dict:
    """The headline ratios: per binary borer against Ghidra on medians, then the median."""
    out: dict = {}
    for key in (
        "readyColdS",
        "firstDecompileS",
        "readyWarmS",
        "decompileP50Ms",
        "allFps",
        "allFps1Core",
        "peakMb",
        "allPeakMb",
    ):
        rs = []
        for b in sorted({r["binary"] for r in rows}):
            pair = {r["tool"]: r.get(key) for r in rows if r["binary"] == b}
            a, g = pair.get("borer"), pair.get("ghidra")
            if isinstance(a, (int, float)) and isinstance(g, (int, float)) and a > 0 and g > 0:
                rs.append(round(a / g if key in HIGHER else g / a, 2))
        if rs:
            out[key] = {"median": round(statistics.median(rs), 2), "perBinary": rs}
    return out


def _compare(old: dict | None, new: dict) -> str:
    """One line per metric whose median moved more than 5% since the last results."""
    if old is None:
        return "  new"
    out = []
    for key in COLUMNS.values():
        a, b = old.get(key), new.get(key)
        if not isinstance(a, (int, float)) or not isinstance(b, (int, float)) or a == 0:
            continue
        change = (b - a) / a
        if abs(change) < 0.05:
            continue
        better = (change > 0) == (key in HIGHER)
        out.append(f"  {key}: {a} -> {b} ({change:+.0%}, {'better' if better else 'worse'})")
    return "\n".join(out) or "  unchanged within 5%"


def _warm_up(a: argparse.Namespace, tools: list[str]) -> None:
    """One untimed start of each tool, so the first measured run pays no first-launch cost."""
    target = a.warm_up
    for tool in tools:
        try:
            if tool == "borer":
                env = _env(Path(tempfile.mkdtemp(prefix="vsg-warm-")))
                proc, watch, _, _ = _ready(a.borer, target, env)
                watch.stop()
                _kill(proc)
            else:
                work = Path(tempfile.mkdtemp(prefix="vsg-warm-"))
                script = ["-scriptPath", str(HERE / "ghidra"), "-postScript", "BenchDecompile.java"]
                _headless(
                    a.ghidra,
                    [str(work), "p", "-import", target, *script, str(work / "w.tsv"), "1"],
                    work / "w.log",
                )
                shutil.rmtree(work, ignore_errors=True)
        except (RuntimeError, EOFError, OSError, Disturbed) as e:
            print(f"warm-up {tool} failed: {e}", file=sys.stderr, flush=True)


def main() -> int:
    """Runs both tools over every binary, --runs times, and updates the results file."""
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ghidra", required=True, type=Path, help="Ghidra install directory")
    ap.add_argument("--ghidra-zip", type=Path, help="the release zip it came from, for its size")
    ap.add_argument("--borer", default="target/release/borer.exe", help="borer binary")
    ap.add_argument("--runs", type=int, default=5, help="runs of every measurement")
    ap.add_argument("--sample", type=int, default=100, help="functions to decompile one by one")
    ap.add_argument("--idle-pct", type=float, default=10, help="CPU %% a quiet machine is under")
    ap.add_argument(
        "--warm-up", default=r"C:\Windows\System32\whoami.exe", help="untimed first binary"
    )
    ap.add_argument("--out", type=Path, default=HERE / "vs_ghidra.json", help="results file")
    ap.add_argument("--tools", default="borer,ghidra", help="which tools to run")
    ap.add_argument("--add", action="store_true", help="add runs to the rows instead of replacing")
    ap.add_argument("--trial", action="store_true", help="try the script on a busy machine")
    ap.add_argument("binaries", nargs="+")
    a = ap.parse_args()
    global TRIAL
    TRIAL = a.trial
    a.borer = str(Path(a.borer).resolve())
    tools = a.tools.split(",")
    results = json.loads(a.out.read_text(encoding="utf-8")) if a.out.exists() else {"rows": []}
    meta = _meta(a.borer, a.ghidra, a.ghidra_zip)
    stamp = time.strftime("%Y-%m-%dT%H:%M")
    rows: list[dict] = results["rows"]
    old = {(r["binary"], r["tool"]): dict(r) for r in rows}
    fresh: dict[tuple[str, str], dict] = {}
    for b in a.binaries:
        for tool in tools:
            key = (Path(b).name, tool)
            kept = old.get(key, {}).get("runs", []) if a.add else []
            fresh[key] = {
                "binary": key[0],
                "mb": round(os.path.getsize(b) / 2**20, 2),
                "tool": tool,
            }
            fresh[key]["runs"] = list(kept)
    print(f"borer {meta['borerCommit']}, {meta['versions']}", file=sys.stderr, flush=True)
    quiet(a.idle_pct)
    _warm_up(a, tools)
    for i in range(a.runs):
        for b in a.binaries:
            for tool in tools:
                row = fresh[(Path(b).name, tool)]
                run: dict = {"pass": stamp, "run": i + 1} | ({"trial": True} if TRIAL else {})
                for attempt in range(RETRIES + 1):
                    run["loadPct"] = quiet(a.idle_pct)
                    run["at"] = time.strftime("%H:%M:%S")
                    try:
                        measured = (
                            borer_run(a.borer, b, a.sample)
                            if tool == "borer"
                            else ghidra_run(a.ghidra, b, a.sample)
                        )
                        run |= {COLUMNS[k]: v for k, v in measured.items() if k in COLUMNS}
                        break
                    except Disturbed as e:
                        print(f"  {tool} {b}: compilers ran ({e}), redoing", file=sys.stderr)
                        run["redone"] = attempt + 1
                    except (RuntimeError, EOFError, OSError, ValueError, KeyError) as e:
                        run["error"] = str(e)[:500]
                        print(f"FAIL {tool} {b}: {e}", file=sys.stderr, flush=True)
                        break
                else:
                    run["error"] = "a compiler ran during every attempt"
                row["runs"].append(run)
                _summarize(row)
                print(
                    f"run {i + 1}/{a.runs} {row['binary']} {tool}: "
                    + ", ".join(f"{k}={v}" for k, v in run.items() if k not in {"pass", "run"}),
                    file=sys.stderr,
                    flush=True,
                )
                # Written after every run, so an interrupted pass keeps what it measured.
                merged = [r for k, r in old.items() if k not in fresh] + list(fresh.values())
                merged.sort(key=lambda r: (r["mb"], r["binary"], r["tool"]))
                results |= meta
                results["method"] = __doc__.split("\n\n", 2)[2].strip()
                results["rows"] = merged
                results["ratios"] = _ratios(merged)
                a.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    for key, row in fresh.items():
        print(f"{key[0]} {key[1]}\n{_compare(old.get(key), row)}", file=sys.stderr, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
