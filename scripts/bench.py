#!/usr/bin/env python3
"""Benchmark borer against a corpus of binaries: speed, answer cost, coverage.

Usage: python scripts/bench.py [--borer PATH] <binary>...
Emits one TSV row per binary and a totals line. Every number comes from a
real MCP session over stdio: wall time per tool call, bytes per answer (the
token cost an agent pays), and the decompiler's own checked-blocks ratio
parsed from its answers. Compare runs by keeping the TSV; regressions in a
row are the signal.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time

_ID = 0


def _timed(proc: subprocess.Popen, name: str, args: dict) -> float:
    """Calls a tool and returns its wall time in seconds, answer dropped."""
    t = time.perf_counter()
    _call(proc, name, args)
    return time.perf_counter() - t


def _recv(proc: subprocess.Popen) -> dict:
    """Reads one line-delimited JSON-RPC message."""
    line = proc.stdout.readline()
    if not line:
        raise EOFError("server closed its stdout")
    return json.loads(line)


def _send(
    proc: subprocess.Popen, method: str, params: dict | None = None, notify: bool = False
) -> int:
    """Sends a request (or a notification), returning its id (0 for one)."""
    global _ID
    msg: dict = {"jsonrpc": "2.0", "method": method}
    if not notify:
        _ID += 1
        msg["id"] = _ID
    if params is not None:
        msg["params"] = params
    proc.stdin.write(json.dumps(msg).encode() + b"\n")
    proc.stdin.flush()
    return int(msg.get("id", 0))


def _call(proc: subprocess.Popen, name: str, args: dict) -> tuple[str, float]:
    """Calls a tool, returning (answer-text, wall-seconds)."""
    rid = _send(proc, "tools/call", {"name": name, "arguments": args})
    while True:
        msg = _recv(proc)
        if msg.get("id") != rid:
            continue
        if "error" in msg:
            raise RuntimeError(f"{name}: {msg['error']}")
        parts = msg["result"].get("content", [])
        text = "".join(p.get("text", "") for p in parts if p.get("type") == "text")
        return text, 0.0  # wall measured by the caller


def _init(proc: subprocess.Popen) -> None:
    """Performs the MCP handshake and the notifications/initialized signal."""
    rid = _send(
        proc,
        "initialize",
        {
            "protocolVersion": "2025-06-18",
            "capabilities": {},
            "clientInfo": {"name": "borer-bench", "version": "0.0.0"},
        },
    )
    while True:
        msg = _recv(proc)
        if msg.get("id") == rid and "result" in msg:
            break
    _send(proc, "notifications/initialized", notify=True)


def bench(borer: str, binary: str) -> dict:
    """Runs the standard workflow against one binary, measuring as it goes.

    The workflow is what an agent's first pass looks like: load, triage the
    image, list the biggest functions, summarize and decompile a few of
    them, then one strings and one search query.
    """
    proc = subprocess.Popen(
        [borer], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL
    )
    assert proc.stdin and proc.stdout
    stats: dict = {"binary": binary.split("\\")[-1].split("/")[-1]}
    try:
        t0 = time.perf_counter()
        _init(proc)
        rid = _send(proc, "tools/call", {"name": "load_binary", "arguments": {"path": binary}})
        while True:
            msg = _recv(proc)
            if msg.get("id") == rid:
                if "error" in msg:
                    raise RuntimeError(f"load: {msg['error']}")
                break
        stats["load_s"] = round(time.perf_counter() - t0, 2)

        calls: list[tuple[str, float, int]] = []

        def timed(name: str, args: dict) -> str:
            t = time.perf_counter()
            text = _call(proc, name, args)[0]
            calls.append((name, time.perf_counter() - t, len(text.encode())))
            return text

        info = timed("binary_info", {})
        timed("function_summary", {}) if False else None
        fns = timed("functions", {"sort": "size", "limit": 5})
        entries = [line.split() for line in fns.splitlines() if line[:2] == "0x"]
        checked_ratio = []
        for row in entries[:3]:
            entry = row[0]
            timed("function_summary", {"address": entry})
            text = timed("decompile", {"address": entry})
            for line in text.splitlines():
                if "checked vs binary" in line:
                    try:
                        got = line.split("statements as emitted, ")[1].split(" blocks")[0]
                        done, total = got.split("/")
                        if int(total) > 0:
                            checked_ratio.append(int(done) / int(total))
                    except (IndexError, ValueError):
                        pass
                if line.startswith("// signature:") and len(line) > 120:
                    stats.setdefault("long_sigs", 0)
                    stats["long_sigs"] += 1
        timed("strings", {"limit": 20})
        # The speed ops the showcase tracks: each repeated, the fastest run
        # kept, because a first call pays the walk and a filter's page its
        # rendering. Throughput comes from the binary's size on disk.
        size = os.path.getsize(binary)
        aob = min(
            _timed(proc, "search", {"query": "65 6c ?? ??", "kind": "bytes", "limit": 20})
            for _ in range(3)
        )
        stats["aob_ms"] = round(aob * 1000, 2)
        stats["aob_gbps"] = round(size / aob / 1e9, 1)
        filtered = min(_timed(proc, "strings", {"filter": "er", "limit": 20}) for _ in range(3))
        stats["str_ms"] = round(filtered * 1000, 2)
        timed("search", {"query": "65 6c", "kind": "bytes", "limit": 20})
        assert info

        stats["calls"] = len(calls)
        stats["bytes"] = sum(b for _, _, b in calls)
        stats["wall_s"] = round(sum(t for _, t, _ in calls), 2)
        stats["per_call_ms"] = round(1000 * stats["wall_s"] / max(1, len(calls)), 1)
        if checked_ratio:
            stats["checked"] = f"{sum(checked_ratio) / len(checked_ratio):.0%}"
        slow = sorted(calls, key=lambda c: -c[1])[:1]
        if slow:
            stats["slowest"] = f"{slow[0][0]}:{slow[0][1]:.2f}s"
    finally:
        proc.kill()
    return stats


def main() -> int:
    """Runs the benchmark over every argument, emitting one TSV row each."""
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--borer", default="target/release/borer.exe", help="server to drive")
    ap.add_argument("binaries", nargs="+", help="binaries to benchmark")
    args = ap.parse_args()
    rows = []
    for b in args.binaries:
        try:
            rows.append(bench(args.borer, b))
        except (RuntimeError, EOFError) as e:
            print(f"FAIL {b}: {e}", file=sys.stderr)
    cols = ["binary", "load_s", "calls", "wall_s", "per_call_ms", "bytes", "checked", "slowest"]
    keys = sorted(
        {k for r in rows for k in r} - {"binary"}, key=lambda k: cols.index(k) if k in cols else 99
    )
    print("\t".join(["binary"] + keys))
    for r in rows:
        print("\t".join(str(r.get(k, "")) for k in ["binary"] + keys))
    return 1 if len(rows) != len(args.binaries) else 0


if __name__ == "__main__":
    raise SystemExit(main())
