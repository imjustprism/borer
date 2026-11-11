#!/usr/bin/env python3
"""Hold the engine to the modules that may name a decoder crate or a seeded hash map.

    python scripts/check/paths.py           fail on a use outside the module that owns it
    python scripts/check/paths.py --record  lower the allowed uses to today's

Each rule in `RULES` is a pattern and the one path under the engine's source
that may match it: the decoder crates stay behind `isa`, and the standard
hash map and set, whose default hasher is seeded per process, stay in
`fxmap.rs`, which gives them a fixed one. A map or set counts where it is
named through `collections` or its `hash_map` and `hash_set`, and so do a
glob import and an alias of `collections`, which would bring one in
unnamed: a scan of the text, not the compiler's view. Comments and literals
do not count. The uses that break a rule today are listed in `paths.tsv`, by rule
and file with their count; each may shrink, never grow (ratchet.py).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check import ratchet  # noqa: E402
from check.sizes import blank  # noqa: E402
from harness.root import ROOT  # noqa: E402

ENGINE = "crates/borer-engine/src/"
"""The source the rules hold, from the repo root."""

RULES = (
    ("iced_x86 outside isa", re.compile(r"\biced_x86\b"), "isa/"),
    ("yaxpeax outside isa/a64/decode.rs", re.compile(r"\byaxpeax_\w+"), "isa/a64/decode.rs"),
    (
        "std hash map outside fxmap.rs",
        re.compile(
            r"\bcollections(::(hash_(map|set)::)?(\{[^}]*\b)?Hash(Map|Set)\b|::\*|\s+as\b)"
            r"|\bRandomState\b"
        ),
        "fxmap.rs",
    ),
)
"""Each rule: its name, what a use looks like, and the path under `ENGINE` that may hold one."""

BASELINE = Path(__file__).with_name("paths.tsv")
"""The uses outside their module today, with the count each may not exceed."""

HEAD = "# uses outside the module that owns them (rule: file): may shrink, never grow"
"""The baseline's first line."""


def uses() -> dict[str, int]:
    """Every file's uses outside the rule's module, keyed `rule: path`."""
    found: dict[str, int] = {}
    for path in sorted((ROOT / ENGINE).rglob("*.rs")):
        rel = path.relative_to(ROOT).as_posix()
        text = blank(path.read_text(encoding="utf-8"))
        for rule, pattern, home in RULES:
            if not rel.startswith(ENGINE + home) and (n := len(pattern.findall(text))):
                found[f"{rule}: {rel}"] = n
    return found


if __name__ == "__main__":
    sys.exit(ratchet.run(BASELINE, HEAD, uses(), sys.argv[1:], "uses"))
