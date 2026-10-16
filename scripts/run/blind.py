#!/usr/bin/env python3
"""Measure blind function discovery against what the compiler declared.

Usage: python scripts/run/blind.py [path-to-borer.exe] FILE.dll|exe ...

Every x64 PE carries the compiler's own list of function starts in its
exception directory (`.pdata`), one `RUNTIME_FUNCTION` per function. That is
the ground truth. The test copies each file with its export, exception and
debug directories zeroed, so borer must find every function from the code
alone, the way it must on a 32-bit image, a dump, or a stripped ELF.

Truth leaves out what a blind pass cannot be asked for: chained entries (the
second half of a split function) and funclets (a catch or cleanup block has
its own entry but is a piece of its parent, reached only through the
exception tables; on x64 it opens by homing its establisher frame,
`mov [rsp+10h], rdx`, and nothing calls or jumps to it).

Reported per file:

  recall      truth starts borer found as function entries
  interior    truth starts borer put inside another function (a boundary
              error: a missed tail call or a missed noreturn)
  missed      truth starts nothing covers at all
  referenced  extra entries something calls, a data pointer names, or the
              original exports - a leaf without an unwind entry, a vtable
              slot, a stub: almost surely real
  orphan      extra entries only a guess reached: the precision loss

Exits non-zero only on a protocol or tool error; the numbers are a report.
"""

from __future__ import annotations

import os
import struct
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.client import Client  # noqa: E402
from harness.root import ROOT  # noqa: E402

FUNCLET_OPENER = b"\x48\x89\x54\x24\x10"


def layout(b: bytes) -> tuple[int, int, list[tuple[int, int, int, int]]]:
    """Image base, data-directory offset, and (va, vsize, raw, rawsize) per section."""
    lfanew = struct.unpack_from("<I", b, 0x3C)[0]
    coff = lfanew + 4
    nsec = struct.unpack_from("<H", b, coff + 2)[0]
    optsz = struct.unpack_from("<H", b, coff + 16)[0]
    opt = coff + 20
    magic = struct.unpack_from("<H", b, opt)[0]
    plus = magic == 0x20B
    base = struct.unpack_from("<Q" if plus else "<I", b, opt + (24 if plus else 28))[0]
    ddir = opt + (112 if plus else 96)
    tbl = opt + optsz
    secs = []
    for i in range(nsec):
        vsz, va, rawsz, raw = struct.unpack_from("<IIII", b, tbl + 40 * i + 8)
        secs.append((va, vsz, raw, rawsz))
    return base, ddir, secs


def rva_to_off(secs: list[tuple[int, int, int, int]], rva: int) -> int | None:
    for va, vsz, raw, rawsz in secs:
        if va <= rva < va + max(vsz, rawsz):
            return raw + (rva - va)
    return None


def truth(b: bytes) -> tuple[int, set[int], int, int]:
    """Image base, declared starts less funclets, chained count, funclet count."""
    base, ddir, secs = layout(b)
    rva, size = struct.unpack_from("<II", b, ddir + 8 * 3)
    off = rva_to_off(secs, rva)
    starts: set[int] = set()
    chained = funclets = 0
    if off is None:
        return base, starts, 0, 0
    for i in range(size // 12):
        beg, _end, unw = struct.unpack_from("<III", b, off + 12 * i)
        if beg == 0:
            continue
        uoff = rva_to_off(secs, unw)
        if uoff is not None and uoff < len(b) and (b[uoff] >> 3) & 4:
            chained += 1
            continue
        boff = rva_to_off(secs, beg)
        if boff is not None and b[boff : boff + 5] == FUNCLET_OPENER:
            funclets += 1
            continue
        starts.add(base + beg)
    return base, starts, chained, funclets


def exported(b: bytes) -> set[int]:
    """The addresses the export directory names."""
    base, ddir, secs = layout(b)
    rva, size = struct.unpack_from("<II", b, ddir)
    off = rva_to_off(secs, rva)
    if off is None or size < 40:
        return set()
    count, table = struct.unpack_from("<II", b, off + 20), struct.unpack_from("<I", b, off + 28)[0]
    toff = rva_to_off(secs, table)
    if toff is None:
        return set()
    out = set()
    for i in range(min(count[0], 65536)):
        at = toff + 4 * i
        if at + 4 > len(b):
            break
        target = struct.unpack_from("<I", b, at)[0]
        if target and rva_to_off(secs, target) is not None:
            out.add(base + target)
    return out


def stripped(b: bytes) -> bytes:
    """The file with its export, exception and debug directories zeroed."""
    out = bytearray(b)
    _, ddir, _ = layout(b)
    for idx in (0, 3, 6):
        struct.pack_into("<II", out, ddir + 8 * idx, 0, 0)
    return bytes(out)


def measure(exe: str, src: str) -> None:
    with open(src, "rb") as f:
        b = f.read()
    base, declared, chained, funclets = truth(b)
    blind = src + ".blind"
    with open(blind, "wb") as f:
        f.write(stripped(b))
    client = Client(exe)
    t0 = time.time()
    client.tool("load_binary", {"path": blind})
    client.tool("functions", {"limit": 1})
    seconds = time.time() - t0
    fns: dict[int, tuple[int, int]] = {}
    offset = 0
    while True:
        _, page = client.tool("functions", {"offset": offset, "limit": 300})
        rows = [line.split() for line in page.splitlines() if line.startswith("0x")]
        if not rows:
            break
        for r in rows:
            fns[int(r[0], 16)] = (int(r[1]), int(r[4]))
        offset += 300
    found = set(fns)
    extra = found - declared
    # The original's exports are functions the file itself vouches for; a
    # leaf stub nothing inside calls is still real when it is exported.
    exports = exported(b)
    referenced = set()
    for e in extra:
        if fns[e][1] > 0 or e in exports:
            referenced.add(e)
            continue
        _, x = client.tool("xrefs", {"address": hex(e), "count_only": True})
        if not x.startswith("# 0 "):
            referenced.add(e)
    hit = declared & found
    missed = declared - found
    # A function's blocks need not be contiguous - a stub that tail-jumps
    # into a shared body owns both - so whether a miss lies inside another
    # function is borer's to say, not a span's.
    interior = set()
    for m in missed:
        try:
            client.tool("function", {"address": hex(m)})
            interior.add(m)
        except SystemExit:
            pass
    client.close()
    os.remove(blind)
    recall = len(hit) / max(1, len(declared))
    print(
        f"{os.path.basename(src):<18} truth={len(declared):>6} "
        f"(chained {chained}, funclets {funclets} left out)  found={len(found):>6}  "
        f"recall={100 * recall:6.2f}%  interior={len(interior):>3}  "
        f"missed={len(missed - interior):>5}  referenced={len(referenced):>5}  "
        f"orphan={len(extra - referenced):>5}  {seconds:.1f}s"
    )


def main(argv: list[str]) -> int:
    args = argv[1:]
    exe = os.path.join(ROOT, "target", "release", "borer.exe")
    if args and args[0].lower().endswith("borer.exe"):
        exe = os.path.abspath(args.pop(0))
    if not args:
        print(__doc__)
        return 1
    for src in args:
        measure(exe, os.path.abspath(src))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
