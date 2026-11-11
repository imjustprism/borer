#!/usr/bin/env python3
"""Hold the duplicated Rust lines to a recorded count, with a ratchet.

    python scripts/check/dupes.py           fail when the count is not the recorded one
    python scripts/check/dupes.py --record  lower the recorded count to today's

The count is what jscpd reports as duplicated lines over every tracked file
that `.jscpd.json`'s `pattern` names, with that file's token and line floors.
`dupes.tsv` holds it: more duplicated lines fail, and so do fewer until
`--record` lowers the number, so it is always today's and can only shrink
(ratchet.py).

jscpd counts a clone against the files it read earlier, so the count depends
on the order it reads them in, and its own walk follows the file system's
(6455 to 6474 lines over the same tree). It is therefore handed the tracked
files sorted by path, through its API: its command line is too short for
them on Windows, and a `path` list in its config file finds nothing there.
A file jscpd leaves out (`maxLines`, `maxSize`) fails the check.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check import ratchet  # noqa: E402
from harness.root import ROOT  # noqa: E402

JSCPD = "jscpd@4.0.5"
"""The pinned scanner npx fetches."""

BASELINE = Path(__file__).with_name("dupes.tsv")
"""The duplicated lines recorded, which the count may not exceed."""

HEAD = "# duplicated lines jscpd finds in the tracked Rust: may shrink, never grow"
"""The baseline's first line."""

DETECT = """
const fs = require("fs"), path = require("path");
const bin = process.env.PATH.split(path.delimiter).find((d) => fs.existsSync(path.join(d, "jscpd")));
require(path.join(bin, "..", "jscpd")).detectClones(JSON.parse(fs.readFileSync(process.argv[2], "utf8")));
"""
"""Runs jscpd's detection with the options in the JSON file it is given;
npx puts the package's `.bin` directory, beside the package, on `PATH`."""


def scan() -> dict[str, int]:
    """Returns jscpd's totals over the tracked files, read in path order."""
    config = json.loads((ROOT / ".jscpd.json").read_text(encoding="utf-8"))
    listing = subprocess.run(
        ["git", "ls-files", "-z", "--", f":(glob){config['pattern']}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout.decode("utf-8")
    files = sorted(p for p in listing.split("\0") if p)
    read = sum(
        1
        for p in files
        if len((ROOT / p).read_text(encoding="utf-8").split("\n")) >= config["minLines"]
    )
    with tempfile.TemporaryDirectory() as tmp:
        options = config | {"path": files, "reporters": ["json"], "output": tmp, "silent": True}
        (Path(tmp) / "options.json").write_text(json.dumps(options), encoding="utf-8")
        (Path(tmp) / "detect.js").write_text(DETECT, encoding="utf-8")
        subprocess.run(
            [shutil.which("npx") or "npx", "--yes", "-p", JSCPD, "node"]
            + [str(Path(tmp) / "detect.js"), str(Path(tmp) / "options.json")],
            cwd=ROOT,
            check=True,
        )
        report = json.loads((Path(tmp) / "jscpd-report.json").read_text(encoding="utf-8"))
    total = report["statistics"]["total"]
    if total["sources"] != read:
        sys.exit(f"jscpd read {total['sources']} of {read} files: lift the caps in .jscpd.json")
    return total


def main(argv: list[str]) -> int:
    total = scan()
    print(f"{total['sources']} files, {total['clones']} clones")
    return ratchet.run(BASELINE, HEAD, {"duplicated": total["duplicatedLines"]}, argv, "lines")


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
