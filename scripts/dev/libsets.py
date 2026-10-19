#!/usr/bin/env python3
"""Write the library signature sets borer ships, and their manifest.

    python scripts/dev/libsets.py [borer.exe]

Each set is `borer sigmake <set>.bsig <name> <library>...` over runtime
libraries installed on a build machine, written to
crates/borer-engine/src/libsets/, and `manifest.tsv` beside them records,
per set, its function count, its size, the license of the code it was read
from, the toolchain version, the library files and the SHA-256 of each.

Only libraries whose license allows shipping what is derived from them are
listed here (`SETS`). The ones left out, and why, are in `REFUSED`, written
to the manifest as comment lines so the reason travels with the data:

* LLVM compiler-rt builtins: Apache-2.0 WITH LLVM-exception.
* The Microsoft C++ standard library (libcpmt.lib, built from
  github.com/microsoft/STL): Apache-2.0 WITH LLVM-exception.
* The Rust standard library (std, core, alloc, compiler_builtins):
  MIT OR Apache-2.0.
* The MSVC C runtime and vcruntime (libcmt.lib, libvcruntime.lib) and the
  Universal CRT (libucrt.lib) are under the Visual Studio and Windows SDK
  license terms, which do not allow redistributing them or what is derived
  from them; a user builds a local pack from them with `borer sigmake`.

A set is rewritten only when a library it names is found; one whose
libraries are missing keeps its file and row, so the script runs on any
machine that has some of them.
"""

from __future__ import annotations

import glob
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.root import ROOT  # noqa: E402

OUT = ROOT / "crates" / "borer-engine" / "src" / "libsets"

HOME = Path.home()
RUST = (
    HOME / ".rustup/toolchains/1.96.1-x86_64-pc-windows-msvc/lib/rustlib/x86_64-pc-windows-msvc/lib"
)
MSVC = Path(
    "C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/lib/x64"
)
LLVM = Path("C:/Program Files/LLVM/lib/clang/22/lib/windows")

# (set name, license, version, library globs)
SETS = [
    (
        "compiler-rt-22-x64-coff",
        "Apache-2.0 WITH LLVM-exception",
        "LLVM 22.1.8",
        [str(LLVM / "clang_rt.builtins-x86_64.lib")],
    ),
    (
        "msvc-stl-14.44-x64",
        "Apache-2.0 WITH LLVM-exception",
        "MSVC 14.44.35207",
        [str(MSVC / "libcpmt.lib")],
    ),
    (
        "rust-1.96-x64-msvc",
        "MIT OR Apache-2.0",
        "rustc 1.96.1",
        [
            str(RUST / "libstd-*.rlib"),
            str(RUST / "libcore-*.rlib"),
            str(RUST / "liballoc-*.rlib"),
            str(RUST / "libcompiler_builtins-*.rlib"),
        ],
    ),
]

REFUSED = [
    ("libcmt.lib, libvcruntime.lib", "Visual Studio license terms: not redistributable"),
    ("libucrt.lib", "Windows SDK license terms: not redistributable"),
]

HEADER = "set\tfunctions\tbytes\tlicense\tversion\tlibraries (sha256)\n"


def borer_exe() -> str:
    """Returns the borer binary to run: the argument, else the newest build."""
    if len(sys.argv) > 1:
        return sys.argv[1]
    target = os.environ.get("CARGO_TARGET_DIR") or str(ROOT / "target")
    for profile in ("release", "debug"):
        exe = Path(target) / profile / "borer.exe"
        if exe.is_file():
            return str(exe)
    raise SystemExit("no borer build found; pass the borer binary")


def sha256(path: str) -> str:
    """Returns a file's SHA-256 as hex."""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def old_rows() -> dict[str, str]:
    """Returns the manifest's current rows by set name."""
    path = OUT / "manifest.tsv"
    if not path.is_file():
        return {}
    rows = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if line and not line.startswith("#") and not line.startswith("set\t"):
            rows[line.split("\t", 1)[0]] = line
    return rows


def main() -> int:
    """Writes every set whose libraries are found, then the manifest."""
    exe = borer_exe()
    OUT.mkdir(parents=True, exist_ok=True)
    rows = old_rows()
    for name, license_, version, patterns in SETS:
        libraries = sorted(p for pattern in patterns for p in glob.glob(pattern))
        if not libraries:
            print(f"# {name}: no library found, kept as it is", file=sys.stderr)
            continue
        out = OUT / f"{name}.bsig"
        run = subprocess.run(
            [exe, "sigmake", str(out), name, *libraries],
            capture_output=True,
            text=True,
            check=False,
        )
        if run.returncode != 0:
            print(run.stdout + run.stderr, file=sys.stderr)
            return run.returncode
        found = re.search(r"wrote .*: (\d+) signatures in (\d+) bytes", run.stdout)
        if not found:
            print(run.stdout, file=sys.stderr)
            return 1
        sources = ", ".join(f"{Path(p).name} ({sha256(p)})" for p in libraries)
        rows[name] = "\t".join([name, found[1], found[2], license_, version, sources])
        print(f"# {name}: {found[1]} functions, {found[2]} bytes")
    lines = ["# library signature sets borer ships; scripts/dev/libsets.py writes this\n"]
    lines += [f"# not shipped: {what}: {why}\n" for what, why in REFUSED]
    lines.append(HEADER)
    lines += [rows[name] + "\n" for name, *_ in SETS if name in rows]
    (OUT / "manifest.tsv").write_text("".join(lines), encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
