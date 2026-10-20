#!/usr/bin/env python3
"""Hold every Rust function and file to a size budget, with a ratchet.

    python scripts/check/sizes.py           fail when a function or file grew past its budget
    python scripts/check/sizes.py --record  rewrite the baseline to today's sizes

A size is code lines: lines with something other than whitespace, comments
and rustdoc. A function may have `FN_MAX` and a file `FILE_MAX`. The
functions and files already over budget are listed in `sizes.tsv` with
their size that day; each may shrink, never grow, and anything new must fit
the budget. A split or shrink can be recorded with `--record`, which only
ever lowers the list.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check.strip_comments import _block_end, _char_end, _string_end  # noqa: E402
from harness.root import ROOT  # noqa: E402

FN_MAX = 100
"""Code lines a function may have (clippy's `too_many_lines` default)."""

FILE_MAX = 1500
"""Code lines a file may have."""

BASELINE = Path(__file__).with_name("sizes.tsv")
"""The functions and files over budget, with the size each may not exceed."""

FN = re.compile(r"\bfn\s+([A-Za-z_]\w*)")


def blank(src: str) -> str:
    """Returns `src` with comments as spaces and literals as `x`, newlines kept."""
    out: list[str] = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        end = i
        if src.startswith("//", i):
            end = src.find("\n", i)
            end = n if end < 0 else end
            out.append(" " * (end - i))
        elif src.startswith("/*", i):
            end = _block_end(src, i)
            out.append(re.sub(r"[^\n]", " ", src[i:end]))
        elif c == '"' or (c == "'" and _char_end(src, i) > i):
            end = _string_end(src, i) if c == '"' else _char_end(src, i)
            out.append(re.sub(r"[^\n]", "x", src[i:end]))
        else:
            out.append(c)
            end = i + 1
        i = end
    return "".join(out)


def code_lines(text: str) -> int:
    """Counts the lines of blanked text that hold code."""
    return sum(1 for line in text.splitlines() if line.strip())


def functions(text: str) -> list[tuple[str, int]]:
    """Lists each function with a body as (name, code lines), in source order."""
    found: list[tuple[str, int]] = []
    for m in FN.finditer(text):
        i, depth = m.end(), 0
        while i < len(text) and not (depth == 0 and text[i] in "{;"):
            depth += (text[i] in "([") - (text[i] in ")]")
            i += 1
        if i >= len(text) or text[i] == ";":
            continue
        start, depth = i, 0
        while i < len(text):
            depth += (text[i] == "{") - (text[i] == "}")
            i += 1
            if depth == 0:
                break
        found.append((m.group(1), code_lines(text[start:i])))
    return found


def measure() -> dict[str, int]:
    """Every function and file over budget today, keyed `path` or `path::name#k`."""
    over: dict[str, int] = {}
    for path in sorted((ROOT / "crates").rglob("*.rs")):
        rel = path.relative_to(ROOT).as_posix()
        text = blank(path.read_text(encoding="utf-8"))
        if (n := code_lines(text)) > FILE_MAX:
            over[rel] = n
        seen: dict[str, int] = {}
        for name, n in functions(text):
            seen[name] = seen.get(name, 0) + 1
            if n > FN_MAX:
                over[f"{rel}::{name}#{seen[name]}"] = n
    return over


def main(argv: list[str]) -> int:
    over = measure()
    base: dict[str, int] = {}
    if BASELINE.exists():
        for line in BASELINE.read_text(encoding="utf-8").splitlines():
            if line and not line.startswith("#"):
                key, n = line.split("\t")
                base[key] = int(n)
    if "--record" in argv:
        kept = {k: n if k not in base else min(n, base[k]) for k, n in over.items()}
        rows = [f"{k}\t{n}" for k, n in sorted(kept.items())]
        head = f"# over budget (fn {FN_MAX}, file {FILE_MAX} code lines): may shrink, never grow"
        BASELINE.write_text("\n".join([head, *rows]) + "\n", encoding="utf-8", newline="\n")
        print(f"recorded {len(rows)} items over budget")
        return 0
    bad = [
        f"{k}: {n} code lines, budget {base.get(k, FILE_MAX if '::' not in k else FN_MAX)}"
        for k, n in sorted(over.items())
        if n > base.get(k, 0)
    ]
    for line in bad:
        print(line)
    if bad:
        print("split the function or file; `--record` only when one was renamed or split")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
