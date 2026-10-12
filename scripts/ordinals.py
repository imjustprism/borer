#!/usr/bin/env python3
"""Generate the table borer names imports by ordinal with.

    python scripts/ordinals.py [--check]

A program that imports a function by its ordinal alone names nothing in its
import table, so the decompiler printed `ORDINAL 359(...)`. The names are in
the export table of the DLL that provides the function, and the ordinals of
the system DLLs programs import that way are stable across Windows releases
(each comes from the SDK's import library). This script reads the export
tables of those DLLs from the machine it runs on and writes
crates/borer-engine/src/import_ordinals.tsv, one `dll<TAB>ordinal<TAB>name`
line per named export, sorted. With --check it exits 1 when the table differs
from what it would write; a machine without the DLLs (not Windows) skips.

pefile's own ordinal table (oleaut32, ws2_32, wsock32), which borer's imphash
reads, lives in ordinals.tsv and is not repeated here. The DLL list below is
the system DLLs certutil imports by ordinal, whose ordinals their .def files fix;
an ordinal of any other DLL, or one its export table does not name, prints as
`<dll>_ord<n>`.
"""

from __future__ import annotations

import os
import sys

DLLS = ["cabinet.dll", "certcli.dll", "wldap32.dll"]
"""The DLLs whose named exports the table lists."""

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "crates", "borer-engine", "src", "import_ordinals.tsv")


def rows() -> list[str] | None:
    """The table's lines, or None when the DLLs or pefile are missing."""
    try:
        import pefile
    except ImportError:
        return None
    system = os.path.join(os.environ.get("SYSTEMROOT", r"C:\Windows"), "System32")
    out = []
    for dll in DLLS:
        path = os.path.join(system, dll)
        if not os.path.isfile(path):
            return None
        pe = pefile.PE(path, fast_load=True)
        pe.parse_data_directories(
            directories=[pefile.DIRECTORY_ENTRY["IMAGE_DIRECTORY_ENTRY_EXPORT"]]
        )
        for sym in getattr(pe, "DIRECTORY_ENTRY_EXPORT", None).symbols:
            if sym.name:
                out.append(f"{dll}\t{sym.ordinal}\t{sym.name.decode('ascii', 'replace')}")
    return sorted(set(out), key=lambda r: (r.split("\t")[0], int(r.split("\t")[1]), r))


def main(argv: list[str]) -> int:
    lines = rows()
    if lines is None:
        print("[skip] ordinals: no pefile or no System32 DLLs here")
        return 0
    text = "".join(f"{ln}\n" for ln in lines)
    if "--check" in argv:
        with open(OUT, encoding="utf-8") as f:
            if f.read() != text:
                print(f"{OUT} differs from what scripts/ordinals.py writes")
                return 1
        return 0
    with open(OUT, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    print(f"wrote {len(lines)} rows to {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
