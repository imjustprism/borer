#!/usr/bin/env python3
"""Write a guard's or registry's entry for borer from borer's own tool facts.

    python scripts/dev/tool_safety.py <target> [out] [--exe PATH]

`borer tools` prints every MCP tool with its four annotation hints and its
effects (what it touches: files, the network, another process, the
session), read from the tool definitions themselves, so an entry made from
it cannot drift from the tools. Each target is one module in
`scripts/dev/emitters/` with an `emit(manifest) -> dict` function and a
`FILE` name; supporting another guard or registry is adding one such file.
The entry is written to `out` (default: the target's `FILE` in the current
directory) as two-space JSON.

Targets: the module names in scripts/dev/emitters/ (hol_guard).
--exe defaults to the release build's borer (borer.exe on Windows), else the debug build's.
"""

from __future__ import annotations

import importlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))

from harness.client import pick_exe  # noqa: E402


def main(argv: list[str]) -> int:
    """Runs `borer tools`, hands its manifest to the target's emitter and
    writes what it returns."""
    args = list(argv)
    exe = pick_exe(args)
    if not args or len(args) > 2:
        raise SystemExit(__doc__)
    emitter = importlib.import_module(f"emitters.{args[0]}")
    run = subprocess.run([exe, "tools"], capture_output=True, text=True, encoding="utf-8")
    if run.returncode != 0:
        raise SystemExit(f"borer tools failed: {run.stderr.strip()}")
    entry = emitter.emit(json.loads(run.stdout))
    out = Path(args[1] if len(args) > 1 else emitter.FILE)
    out.write_text(json.dumps(entry, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
