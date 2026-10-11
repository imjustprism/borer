#!/usr/bin/env python3
"""Measure how well borer decompiles a binary, over the functions that are hard.

Usage: python scripts/quality.py [path-to-borer.exe] [path-to-binary] [how-many]

Defaults to borer.exe against itself, over its 200 largest functions. Prints the
three things that make decompiled text worse than its source, each as the share
of functions carrying it and the number of sites:

  unmodelled instruction   the lifter met an opcode it has no semantics for, and
                           said so with `/* asm: ... */` rather than guessing
  FLAGS_UNKNOWN            a condition was read from flags nothing set
  goto                     control flow the structurer could not put back into
                           `if`/`else`/`while`/`for`/`switch`

Small functions are almost all thunks and leaf accessors and say nothing about
quality, so the sweep takes the largest by instruction count: the shapes that
defeat a decompiler only appear once a function is big enough to have them.

A goto is also classified, because the classes want different fixes. A backward
edge is a loop the structurer missed. A forward edge whose label sits outside
the jump's own block left a scope, which no local rewrite can undo and which
only region analysis fixes. A forward edge inside one block is a plain `if`/
`else` join.

Exits non-zero only on a protocol or tool error; the numbers are a report, not a
threshold, because what counts as good depends on the binary.
"""

from __future__ import annotations

import collections
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

from mcp import Client  # noqa: E402

ASM = re.compile(r"/\* asm: ([a-z0-9]+)")
GOTO = re.compile(r"goto (L_[0-9a-f]+);")
LABEL = re.compile(r"L_[0-9a-f]+:")


def indent_of(line: str) -> int:
    return len(line) - len(line.lstrip())


def largest(client: Client, want: int) -> list[tuple[int, str]]:
    """Every function, biggest first, as (instructions, entry)."""
    rows: list[tuple[int, str]] = []
    offset = 0
    while True:
        _, text = client.tool("functions", {"offset": offset, "limit": 300})
        page = [line.split() for line in text.splitlines() if line.startswith("0x")]
        if not page:
            break
        rows += [(int(c[3]), c[0]) for c in page]
        offset += 300
    rows.sort(reverse=True)
    return rows[:want]


def classify_gotos(lines: list[str]) -> collections.Counter:
    """Which kind each goto is, by where its label sits relative to the jump."""
    out: collections.Counter = collections.Counter()
    label_at = {
        m.group(0)[:-1]: i for i, text in enumerate(lines) if (m := LABEL.fullmatch(text.strip()))
    }
    for i, line in enumerate(lines):
        for m in GOTO.finditer(line):
            at = label_at.get(m.group(1))
            if at is None:
                out["dangling"] += 1
            elif at < i:
                out["backward, a loop edge"] += 1
            elif indent_of(lines[at]) < indent_of(line):
                out["forward, out of the enclosing block"] += 1
            else:
                out["forward, inside one block"] += 1
    return out


def main(argv: list[str]) -> int:
    exe = (
        os.path.abspath(argv[1])
        if len(argv) > 1
        else os.path.join(ROOT, "target", "release", "borer.exe")
    )
    target = os.path.abspath(argv[2]) if len(argv) > 2 else exe
    want = int(argv[3]) if len(argv) > 3 else 200

    client = Client(exe)
    client.tool("load_binary", {"path": target})
    rows = largest(client, want)
    if not rows:
        print("no functions to sweep")
        return 1
    print(
        f"{os.path.basename(target)}: the {len(rows)} largest functions, "
        f"{rows[0][0]} down to {rows[-1][0]} instructions"
    )

    asm: collections.Counter = collections.Counter()
    gotos: collections.Counter = collections.Counter()
    carrying = collections.Counter()
    seen = lines = 0
    for _, entry in rows:
        _, text = client.tool("decompile", {"address": entry})
        seen += 1
        body = text.splitlines()
        lines += len(body)
        hits = ASM.findall(text)
        asm.update(hits)
        if hits:
            carrying["unmodelled instruction"] += 1
        if "FLAGS_UNKNOWN" in text:
            carrying["FLAGS_UNKNOWN"] += 1
        kinds = classify_gotos(body)
        if kinds:
            carrying["goto"] += 1
        gotos.update(kinds)

    print(f"{seen} functions, {lines} lines of pseudo-C\n")
    for what, sites in (
        ("unmodelled instruction", sum(asm.values())),
        ("FLAGS_UNKNOWN", None),
        ("goto", sum(gotos.values())),
    ):
        n = carrying[what]
        tail = f"{sites} sites" if sites is not None else ""
        print(f"  {what:<24} {n:>4} of {seen} functions ({100 * n // seen}%)  {tail}")

    if gotos:
        print("\ngoto by kind:")
        total = sum(gotos.values())
        for kind, n in gotos.most_common():
            print(f"  {100 * n // total:>3}%  {n:>5}  {kind}")
    if asm:
        print("\nunmodelled instructions, most frequent first:")
        for mnemonic, n in asm.most_common(20):
            print(f"  {n:>5}  {mnemonic}")

    client.proc.stdin.close()
    client.proc.wait(timeout=30)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
