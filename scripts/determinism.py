#!/usr/bin/env python3
"""Check the determinism contract: same binary, same query, same bytes.

    python scripts/determinism.py [borer.exe] [target]

The contract every other guarantee rests on is that an answer does not
change between runs. Nothing in the engine is allowed to depend on a clock,
a random seed, an address the loader chose, or the iteration order of a hash
map, and each of those has a way of arriving quietly: a `HashMap` swapped in
for a `BTreeMap` in a hot path, a timestamp added to a report header.

So every command is run twice and the bytes compared. A difference is
printed with the first line that differs, because the line usually names the
cause.

The target defaults to the borer binary itself, which is the same
self-analysis the dogfood sweep uses: a real image with 88,000 functions,
where a map's ordering has room to show.

This is the cross-process form of the check, so it also catches an answer
that depends on where the loader put something. It is not in the gate
because every query pays for its own analysis pass, which is six minutes for
this list; the gate checks the same contract in two seconds by analyzing one
binary twice inside a single process (the `dogfood` suite). Run this one
when a cross-process difference is worth ruling out.
"""

from __future__ import annotations

import hashlib
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# One entry per command shape worth checking, with arguments that reach
# something on any binary. The emulator-driven ones matter most: they run
# code, and a machine that answered differently twice would be the worst
# kind of defect to ship.
QUERIES: list[list[str]] = [
    ["info"],
    ["functions"],
    ["symbols"],
    ["strings"],
    ["crypto"],
    ["entropy"],
    ["triage"],
    ["hidden"],
    ["summary", "entry"],
    ["function", "entry"],
    ["decompile", "entry"],
    ["decompile", "entry", "skeleton"],
    ["disasmfn", "entry"],
    ["cfg", "entry"],
    ["callgraph", "entry"],
    ["class", "entry"],
    ["xrefs", "entry"],
    ["fstrings", "entry"],
    ["why", "entry"],
    ["layout", "entry"],
    ["taint", "entry"],
    ["solve", "entry"],
    ["oracle", "entry"],
    ["emulate", "entry,steps=20000"],
]


def entry_of(exe: str, target: str) -> str | None:
    """Reads the target's entry point, the one address every binary has.

    Args:
        exe: The borer binary.
        target: The binary to analyze.

    Returns:
        The entry address as hex text, or None when there is none.
    """
    out = subprocess.run([exe, "info", target], capture_output=True, text=True, check=False).stdout
    for line in out.splitlines():
        if "entry:" in line:
            tail = line.split("entry:", 1)[1].strip().split()[0]
            return tail if tail.startswith("0x") else None
    return None


def run(exe: str, args: list[str]) -> tuple[bytes, bytes]:
    """Runs one query and returns its output and error streams."""
    done = subprocess.run([exe, *args], capture_output=True, check=False)
    return done.stdout, done.stderr


def main(argv: list[str]) -> int:
    """Runs every query twice and reports any difference."""
    # Absolute, because Windows will not launch a relative path that is not
    # on PATH, so an explicit argument failed where the default worked.
    exe = os.path.abspath(argv[0]) if argv else os.path.join(ROOT, "target", "debug", "borer.exe")
    if not os.path.exists(exe):
        exe = os.path.join(ROOT, "target", "debug", "borer")
    target = os.path.abspath(argv[1]) if len(argv) > 1 else exe
    if not os.path.exists(exe):
        print(f"[FAIL] {exe} is not built")
        return 1
    entry = entry_of(exe, target)
    if entry is None:
        print(f"[FAIL] {target} has no entry point to query")
        return 1
    unstable = 0
    seen: list[bytes] = []
    for query in QUERIES:
        args = [query[0], target] + [a.replace("entry", entry) for a in query[1:]]
        first, err = run(exe, args)
        second, _ = run(exe, args)
        seen.append(first)
        if first == second:
            continue
        unstable += 1
        name = " ".join(query)
        print(f"[FAIL] {name} differs between runs")
        one = first.decode("utf-8", "replace").splitlines()
        two = second.decode("utf-8", "replace").splitlines()
        for k, (a, b) in enumerate(zip(one, two, strict=False)):
            if a != b:
                print(f"  line {k + 1} first : {a[:160]}")
                print(f"  line {k + 1} second: {b[:160]}")
                break
        else:
            print(f"  lengths {len(one)} and {len(two)}")
        if err:
            print(f"  stderr: {err.decode('utf-8', 'replace')[:200]}")
    if unstable:
        print(f"\n[FAIL] {unstable} of {len(QUERIES)} queries are not deterministic")
        return 1
    # The digest is of what was already run, not a third pass: it is there so
    # a change in any answer is visible at a glance across commits.
    digest = hashlib.sha256(b"".join(seen)).hexdigest()
    print(f"DETERMINISM OK ({len(QUERIES)} queries, {digest[:12]})")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
