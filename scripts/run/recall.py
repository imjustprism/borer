#!/usr/bin/env python3
"""What borer finds against ground truth it did not compute, per binary and category.

Usage: python scripts/run/recall.py --bench DIR [--borer EXE] [--work DIR]
       [--only TAG,...] [--label NAME] [--sample N] [--compare A,B]

The bench directory holds `corpus/` (the hard_* and suite_* ELF builds with
their symbol tables, notepad.exe), `src/` (hard.c and suite.c) and
`dl/sqlite/*/sqlite3.c`. The work directory (default `<bench>/out/recall`)
receives what the ground truth needs: stripped copies of the ELF builds,
sqlite3 built by clang-cl with a full PDB, and kernelbase.dll. The LLVM
tools (llvm-nm, llvm-objdump, llvm-objcopy, llvm-pdbutil, llvm-readobj,
clang-cl) must be on PATH or in `C:\\Program Files\\LLVM\\bin`, and the
public PDBs of notepad and kernelbase in borer's symbol cache (`borer
fetch-pdb <binary>`).

borer always reads a binary without its symbols: an ELF stripped of
`.symtab`, a PE loaded with `pdb=false`. What it is measured against:

- functions: every function symbol (`llvm-nm -S`, PDB procedures and
  thunks, PDB public functions, `.pdata` entries that are not chained),
  split by how the function is reached: exported, called directly, only
  jumped to from another function (a tail call), or neither (reached only
  through a pointer). `extent` is the share of matched functions whose
  size or range is the symbol's size, with or without the `int3` traps
  that end it.
- calls: every direct call site llvm-objdump decodes inside a known
  function, looked up through `xrefs` on its target; a site in a function
  a row names as running the same code counts, and `+folds` also counts
  the sites of the functions past the names a row shows.
- data: every rip-relative operand into a non-code section (imports apart),
  looked up through `xrefs` on its target; `imports` the same for calls and
  jumps through an import slot.
- switch: every case target a PDB `S_ARMSWITCHTABLE` record gives, against
  the successors of the indirect jump in `function`.
- strings: every string literal of the source that the file holds
  NUL-terminated, and every `??_C@` literal a PDB names, against the rows
  of `strings` (each run of four or more printable characters must lie in
  a row, since a row ends at a newline); `xstring` the literals code
  references, through `find_function_by_string`.
- symbols: imports (delay-load included), exports and forwarders by name
  against llvm-readobj and the dynamic symbol table.
- crypto: the algorithms whose constants the source spells, against
  `find_crypto_constants`.
- search: byte windows of code with wildcards, and literals as text.

Precision is what borer lists that the ground truth does not hold, where
the ground truth is complete enough to say so (functions of a stripped ELF
or a full PDB, strings of a source build, call sites); the results keep a
sample of every category's misses and extras to inspect. Results go to
`<work>/recall_<label>.json`;
`--compare before,after` prints the table of two runs.
"""

from __future__ import annotations

import argparse
import ast
import bisect
import json
import os
import re
import shutil
import struct
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from harness.client import Client  # noqa: E402
from harness.root import ROOT  # noqa: E402

LLVM = Path(r"C:\Program Files\LLVM\bin")
SYMCACHE = Path(
    os.environ.get("BORER_SYMCACHE")
    or Path(os.environ.get("LOCALAPPDATA", "")) / "borer" / "symsrv"
)

NAME_SECTIONS = (
    ".dynstr",
    ".comment",
    ".strtab",
    ".shstrtab",
    ".interp",
    ".gnu.version_d",
    ".gnu.version_r",
)

CRYPTO = {
    0xEDB88320: "CRC-32",
    0x04C11DB7: "CRC-32",
    0x82F63B78: "CRC-32C",
    0xCBF29CE484222325: "FNV-1",
    0x100000001B3: "FNV-1",
    0x811C9DC5: "FNV-1",
    0x01000193: "FNV-1",
    0xFF51AFD7ED558CCD: "Murmur",
    0xC4CEB9FE1A85EC53: "Murmur",
    0xCC9E2D51: "Murmur",
    0x1B873593: "Murmur",
    0x67452301: "MD5",
    0x6A09E667: "SHA-256",
    0x428A2F98: "SHA-256",
    0x5A827999: "SHA-1",
    0x61707865: "ChaCha",
}


def tool(name: str) -> str:
    """Returns the path of an LLVM tool."""
    found = shutil.which(name)
    if found:
        return found
    exe = LLVM / f"{name}.exe"
    if exe.is_file():
        return str(exe)
    raise SystemExit(f"{name} not found on PATH or in {LLVM}")


def run(*args: str, cwd: Path | None = None) -> str:
    """Runs a command (in `cwd` when given) and returns its stdout, failing loudly."""
    p = subprocess.run(
        args, capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=cwd
    )
    if p.returncode != 0:
        raise SystemExit(f"{args[0]} failed ({p.returncode}): {p.stderr[-800:]}")
    return p.stdout


class Image:
    """The sections of a PE or ELF file, enough to map addresses to bytes."""

    def __init__(self, path: Path) -> None:
        self.data = path.read_bytes()
        self.sections: list[tuple[str, int, int, int, int, bool]] = []
        if self.data[:2] == b"MZ":
            self._pe()
        else:
            self._elf()

    def _pe(self) -> None:
        d = self.data
        pe = struct.unpack_from("<I", d, 0x3C)[0]
        nsec, opt_size = (
            struct.unpack_from("<H", d, pe + 6)[0],
            struct.unpack_from("<H", d, pe + 20)[0],
        )
        opt = pe + 24
        magic = struct.unpack_from("<H", d, opt)[0]
        self.pe64 = magic == 0x20B
        self.base = (
            struct.unpack_from("<Q", d, opt + 24)[0]
            if self.pe64
            else struct.unpack_from("<I", d, opt + 28)[0]
        )
        dirs = opt + (112 if self.pe64 else 96)
        self.dirs = [struct.unpack_from("<II", d, dirs + 8 * i) for i in range(16)]
        sec = opt + opt_size
        for i in range(nsec):
            name = d[sec + 40 * i : sec + 40 * i + 8].rstrip(b"\0").decode("latin-1")
            vsize, rva, rsize, roff = struct.unpack_from("<IIII", d, sec + 40 * i + 8)
            chars = struct.unpack_from("<I", d, sec + 40 * i + 36)[0]
            self.sections.append(
                (name, self.base + rva, max(vsize, rsize), roff, rsize, bool(chars & 0x20000000))
            )
        self.elf = False

    def _elf(self) -> None:
        d = self.data
        is64 = d[4] == 2
        self.base = 0
        self.elf = True
        self.pe64 = False
        if is64:
            shoff, shentsize, shnum, shstrndx = (
                struct.unpack_from("<Q", d, 0x28)[0],
                *struct.unpack_from("<HHH", d, 0x3A),
            )
        else:
            shoff, shentsize, shnum, shstrndx = (
                struct.unpack_from("<I", d, 0x20)[0],
                *struct.unpack_from("<HHH", d, 0x2E),
            )
        hdrs = []
        for i in range(shnum):
            o = shoff + i * shentsize
            if is64:
                name, typ, flags, addr, off, size = struct.unpack_from("<IIQQQQ", d, o)
            else:
                name, typ, flags, addr, off, size = struct.unpack_from("<IIIIII", d, o)
            hdrs.append((name, typ, flags, addr, off, size))
        strtab = hdrs[shstrndx][4]
        for name, typ, flags, addr, off, size in hdrs:
            if not flags & 2:
                continue
            nm = d[strtab + name : d.index(b"\0", strtab + name)].decode("latin-1")
            self.sections.append((nm, addr, size, off, 0 if typ == 8 else size, bool(flags & 4)))

    def section(self, va: int) -> tuple[str, int, int, int, int, bool] | None:
        """Returns the section holding a virtual address."""
        for s in self.sections:
            if s[1] <= va < s[1] + s[2]:
                return s
        return None

    def is_code(self, va: int) -> bool:
        """Returns whether a virtual address lies in an executable section."""
        s = self.section(va)
        return bool(s and s[5])

    def read(self, va: int, n: int) -> bytes:
        """Returns up to n file bytes at a virtual address."""
        s = self.section(va)
        if not s or va - s[1] >= s[4]:
            return b""
        o = s[3] + va - s[1]
        return self.data[o : o + min(n, s[4] - (va - s[1]))]

    def offset_va(self, off: int) -> int | None:
        """Returns the virtual address of a file offset."""
        for s in self.sections:
            if s[3] <= off < s[3] + s[4]:
                return s[1] + off - s[3]
        return None

    def data_sections(self):
        """Yields (va, bytes) of every file-backed section that is not code."""
        for s in self.sections:
            if not s[5] and s[4]:
                yield s[1], self.data[s[3] : s[3] + s[4]]


class Truth:
    """What a binary holds, from sources other than borer."""

    def __init__(self) -> None:
        self.funcs: dict[int, dict] = {}
        self.calls: dict[int, set[int]] = defaultdict(set)
        self.tails: dict[int, set[int]] = defaultdict(set)
        self.data: dict[int, set[int]] = defaultdict(set)
        self.iat: dict[int, set[int]] = defaultdict(set)
        self.switches: list[tuple[int, set[int]]] = []
        self.literals: list[tuple[str, bytes, list[int]]] = []
        self.imports: set[str] = set()
        self.exports: set[str] = set()
        self.forwards: set[str] = set()
        self.crypto: set[str] = set()
        self.chunks: list[tuple[int, int]] = []
        self.parents: dict[int, int] = {}
        self.complete_funcs = False
        self.complete_strings = False

    def add_func(self, va: int, name: str, size: int | None, kind: str) -> None:
        """Records a function, keeping the first name and a symbol's size over a table's."""
        f = self.funcs.setdefault(
            va, {"name": name, "size": size, "kind": kind, "symbol_size": False}
        )
        if f["size"] is None and size:
            f["size"] = size
        if size and kind != "pdata":
            f["size"], f["symbol_size"] = size, True

    def containing(self) -> list[tuple[int, int]]:
        """Returns (start, end) of every function with a size and every chunk, sorted."""
        return sorted(
            [(va, va + f["size"]) for va, f in self.funcs.items() if f["size"]] + self.chunks
        )


def nm_functions(t: Truth, path: Path) -> None:
    """Reads function symbols with sizes from an ELF symbol table."""
    for line in run(tool("llvm-nm"), "-S", "--defined-only", str(path)).splitlines():
        parts = line.split()
        if len(parts) == 4 and parts[2] in "tTwW":
            t.add_func(
                int(parts[0], 16),
                parts[3],
                int(parts[1], 16) or None,
                "local" if parts[2] == "t" else "global",
            )
    for line in run(tool("llvm-nm"), "-D", "--defined-only", str(path)).splitlines():
        parts = line.split()
        if len(parts) >= 3 and parts[-2] in "TW" or len(parts) >= 3 and parts[-2] in "DBRV":
            t.exports.add(parts[-1].split("@")[0])
    for line in run(tool("llvm-nm"), "-D", "--undefined-only", str(path)).splitlines():
        parts = line.split()
        if (
            parts
            and parts[0] in "Uw"
            and not parts[-1].startswith("_ITM")
            and parts[-1] != "__gmon_start__"
        ):
            t.imports.add(parts[-1].split("@")[0])
    t.complete_funcs = True


def pdb_sections(pdb: Path) -> list[int]:
    """Returns the RVA of every section a PDB records, by 1-based index."""
    rvas = [0]
    for m in re.finditer(
        r"SECTION HEADER #\d+\n.*?\n\s*[0-9A-F]+ virtual size\n\s*([0-9A-F]+) virtual address",
        run(tool("llvm-pdbutil"), "dump", "--section-headers", str(pdb)),
    ):
        rvas.append(int(m.group(1), 16))
    return rvas


def pdb_full(t: Truth, pdb: Path, img: Image) -> None:
    """Reads procedures, thunks and switch tables from a full PDB."""
    rvas = pdb_sections(pdb)
    text = run(tool("llvm-pdbutil"), "dump", "--symbols", str(pdb))

    def va(sec: str, off: str) -> int:
        return img.base + rvas[int(sec)] + int(off)

    for m in re.finditer(
        r"S_(GPROC32|LPROC32|THUNK32) \[size = \d+\] `([^`]*)`\n.*?addr = (\d+):(\d+), (?:code size|length) = (\d+)",
        text,
    ):
        kind = {"GPROC32": "global", "LPROC32": "local", "THUNK32": "thunk"}[m.group(1)]
        t.add_func(va(m.group(3), m.group(4)), m.group(2), int(m.group(5)) or None, kind)
    for m in re.finditer(
        r"S_ARMSWITCHTABLE .*\n\s*base = (\d+):(\d+), switchtype = (\w+), branch = (\d+):(\d+), table = (\d+):(\d+), entriescount = (\d+)",
        text,
    ):
        base, table, n = va(m.group(1), m.group(2)), va(m.group(6), m.group(7)), int(m.group(8))
        fmt = {
            "int32": ("<i", 4),
            "uint32": ("<I", 4),
            "pointer": ("<Q", 8),
            "int16": ("<h", 2),
            "uint16": ("<H", 2),
            "int8": ("<b", 1),
            "uint8": ("<B", 1),
        }.get(m.group(3))
        if not fmt:
            continue
        raw = img.read(table, n * fmt[1])
        vals = [struct.unpack_from(fmt[0], raw, i * fmt[1])[0] for i in range(len(raw) // fmt[1])]
        targets = {v if m.group(3) == "pointer" else base + v for v in vals}
        t.switches.append((va(m.group(4), m.group(5)), targets))
    t.complete_funcs = True


def pdb_publics(t: Truth, pdb: Path, img: Image) -> None:
    """Reads public functions and `??_C@` string literals from a PDB."""
    rvas = pdb_sections(pdb)
    text = run(tool("llvm-pdbutil"), "dump", "--publics", str(pdb))
    for m in re.finditer(
        r"S_PUB32 \[size = \d+\] `([^`]*)`\n\s*flags = ([^,]*), addr = (\d+):(\d+)", text
    ):
        name, flags, sec, off = m.groups()
        if int(sec) >= len(rvas):
            continue
        a = img.base + rvas[int(sec)] + int(off)
        if "function" in flags:
            kind = (
                "funclet"
                if re.search(r"\$(catch|fin|dtor|filt)\$|^\?(catch|dtor|fin|filt)\$", name)
                else "global"
            )
            t.add_func(a, name, None, kind)
        elif name.startswith("??_C@_"):
            wide = name[6] == "1"
            raw = img.read(a, 4096)
            unit = 2 if wide else 1
            end = next(
                (
                    i
                    for i in range(0, len(raw) - unit + 1, unit)
                    if raw[i : i + unit] == b"\0" * unit
                ),
                None,
            )
            if end is None:
                continue
            body = raw[:end]
            try:
                s = body.decode("utf-16-le" if wide else "latin-1")
            except UnicodeDecodeError:
                continue
            if len(s) >= 5 and all(c.isprintable() or c in "\t\r\n" for c in s):
                t.literals.append((s, body, [a]))


def pdata(t: Truth, img: Image) -> None:
    """Adds every `.pdata` entry that is not chained to another as a function."""
    rva, size = img.dirs[3]
    raw = img.read(img.base + rva, size)
    for i in range(len(raw) // 12):
        begin, end, unwind = struct.unpack_from("<III", raw, i * 12)
        if not begin or unwind & 1:
            continue
        info = img.read(img.base + unwind, 1)
        if info and info[0] >> 3 & 4:
            t.chunks.append((img.base + begin, img.base + end))
            codes = img.read(img.base + unwind + 2, 1)
            at = img.base + unwind + 4 + 2 * ((codes[0] + 1) & ~1 if codes else 0)
            parent = img.read(at, 4)
            if len(parent) == 4:
                t.parents[img.base + begin] = img.base + struct.unpack("<I", parent)[0]
            continue
        t.add_func(img.base + begin, f"pdata_{begin:x}", end - begin, "pdata")


def coff_symbols(t: Truth, path: Path) -> None:
    """Reads imports, delay imports, exports and forwarders with llvm-readobj."""
    for m in re.finditer(
        r"Export \{\n\s*Ordinal: (\d+)\n\s*Name: ([^\n]*)\n\s*(RVA|ForwardedTo): ([^\n]*)",
        run(tool("llvm-readobj"), "--coff-exports", str(path)),
    ):
        name = m.group(2).strip() or f"#{m.group(1)}"
        (t.forwards if m.group(3) == "ForwardedTo" else t.exports).add(name)
    for m in re.finditer(
        r"Symbol: ([^\n]*?) \((\d+)\)", run(tool("llvm-readobj"), "--coff-imports", str(path))
    ):
        t.imports.add(m.group(1).strip() or f"#{m.group(2)}")


def disassembly(t: Truth, path: Path, img: Image) -> None:
    """Reads direct calls, cross-function jumps and rip-relative operands."""
    extents = t.containing()
    starts = [e[0] for e in extents]

    def owner(va: int) -> int | None:
        i = bisect.bisect_right(starts, va) - 1
        return extents[i][0] if i >= 0 and va < extents[i][1] else None

    syntax = [] if ".a64." in path.name else ["-M", "intel"]
    out = run(tool("llvm-objdump"), "-d", "--no-show-raw-insn", *syntax, str(path))
    line_re = re.compile(r"^\s*([0-9a-f]+):\s+(\S+)\s*([^\n]*)$")
    prefix = None
    for line in out.splitlines():
        m = line_re.match(line)
        if not m:
            continue
        site, mnem, ops = int(m.group(1), 16), m.group(2), m.group(3)
        if mnem in ("lock", "rep", "repe", "repne", "notrack", "data16") and not ops:
            prefix = site
            continue
        site, prefix = prefix if prefix is not None else site, None
        src = owner(site)
        if src is None:
            continue
        direct = re.match(r"(?:0x)?([0-9a-f]+)\s*(?:<|$)", ops)
        if mnem in ("call", "callq", "bl") and direct:
            target = int(direct.group(1), 16)
            if target in t.funcs:
                t.calls[target].add(site)
        elif mnem in ("jmp", "jmpq", "b") and direct:
            target = int(direct.group(1), 16)
            if target in t.funcs and target != src:
                t.tails[target].add(site)
        rip = re.search(r"#\s*0x([0-9a-f]+)", ops)
        if rip and "rip" in ops:
            target = int(rip.group(1), 16)
            if img.is_code(target) or img.section(target) is None:
                continue
            if mnem.startswith(("call", "jmp")):
                t.iat[target].add(site)
            elif target not in t.funcs:
                t.data[target].add(site)


C_STRING = re.compile(r'(?<![\w\'])(L?)"((?:[^"\\\n]|\\.)*)"')


def source_literals(t: Truth, sources: list[Path], img: Image) -> None:
    """Adds every string literal of the sources that the file holds NUL-terminated."""
    seen: set[bytes] = set()
    sections = list(img.data_sections())
    for src in sources:
        text = src.read_text(encoding="utf-8", errors="replace")
        text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
        for m in C_STRING.finditer(text):
            if m.group(1):
                continue
            try:
                s = ast.literal_eval('"' + m.group(2).replace("\\\n", "") + '"')
            except (ValueError, SyntaxError):
                continue
            body = s.encode("latin-1", errors="ignore")
            if (
                len(body) < 5
                or body in seen
                or not all(32 <= b < 127 or b in (9, 10, 13) for b in body)
            ):
                continue
            seen.add(body)
            hits = []
            for base, raw in sections:
                i = raw.find(body + b"\0")
                while i >= 0 and len(hits) < 4:
                    hits.append(base + i)
                    i = raw.find(body + b"\0", i + 1)
            if hits:
                t.literals.append((s, body, hits))
    t.complete_strings = True


def source_crypto(t: Truth, sources: list[Path]) -> None:
    """Adds the algorithms whose constants the sources spell in hex."""
    for src in sources:
        for m in re.finditer(
            r"0x([0-9a-fA-F]{6,16})", src.read_text(encoding="utf-8", errors="replace")
        ):
            if (alg := CRYPTO.get(int(m.group(1), 16))) is not None:
                t.crypto.add(alg)


class Borer:
    """One borer server with a binary loaded, read the way an agent reads it."""

    def __init__(self, exe: str, path: Path) -> None:
        self.c = Client(exe)
        self.c.tool("load_binary", {"path": str(path), "pdb": False})

    def pages(self, name: str, args: dict, limit: int) -> list[str]:
        """Returns the data rows of every page of a list tool."""
        rows, off = [], 0
        while True:
            _, text = self.c.tool(name, {**args, "offset": off, "limit": limit})
            page = [r for r in text.splitlines() if r and not r.startswith("#")]
            rows += page
            m = re.search(r"showing (\d+) of (\d+)", text)
            if not m or off + int(m.group(1)) >= int(m.group(2)) or not page:
                return rows
            off += int(m.group(1))

    def functions(self) -> dict[int, int]:
        """Returns entry to size for every function, thunks and funclets included."""
        out = {}
        self.by_name: dict[str, int] = {}
        for filt in (None, "thunk", "funclet"):
            args = {"filter": filt} if filt else {}
            for r in self.pages("functions", args, 300):
                p = r.split()
                if len(p) >= 2 and p[0].startswith("0x"):
                    out[int(p[0], 16)] = int(p[1])
                    self.by_name[p[-1]] = int(p[0], 16)
        return out

    def folded(self, row: str) -> set[int]:
        """Returns the entries a row names as running the same code."""
        m = re.search(r"running the same code\): (.*)$", row)
        names = m.group(1).split(", ") if m else []
        return {self.by_name[n] for n in names if n in self.by_name}

    def span(self, entry: int) -> int | None:
        """Returns the bytes from a function's entry to the end of its range."""
        _, text = self.c.tool("function", {"address": hex(entry)})
        m = re.search(r"range:\s+0x([0-9a-f]+)\.\.0x([0-9a-f]+)", text)
        return int(m.group(2), 16) - int(m.group(1), 16) if m else None

    def sites(self, target: int) -> tuple[dict[int, str], set[int], int]:
        """Returns every reference site to an address with its kind, the
        functions a row folds in and names, whose own sites go unlisted, and
        how many folded functions go unnamed past a row's cap."""
        out, folded, unnamed = {}, set(), 0
        for r in self.pages("xrefs", {"address": hex(target)}, 500):
            body = r.split(": ", 1)[-1].split(" (+")[0]
            for m in re.finditer(r"0x([0-9a-f]+) ([\w/]+)", body):
                out[int(m.group(1), 16)] = m.group(2)
            named = self.folded(r)
            folded |= named
            if m := re.search(r"\(\+(\d+) functions? running the same code\)", r):
                unnamed += int(m.group(1)) - len(named)
        return out, folded, unnamed

    def close(self) -> None:
        """Ends the server."""
        self.c.proc.stdin.close()
        self.c.proc.wait(60)


def spread(items: list, n: int) -> list:
    """Returns at most n items taken evenly from a sorted list."""
    if len(items) <= n:
        return items
    k = len(items) / n
    return [items[int(i * k)] for i in range(n)]


def ratio(hit: int, total: int) -> dict:
    """Returns a hit/total cell."""
    return {"hit": hit, "total": total}


def measure(t: Truth, img: Image, b: Borer, sample: int, extras: dict) -> dict:
    """Measures every category the ground truth covers."""
    res: dict[str, dict] = {}
    bf = b.functions()
    exported = {va for va, f in t.funcs.items() if f["name"] in t.exports}
    reach: dict[str, list[int]] = defaultdict(list)
    for va, f in t.funcs.items():
        if f["kind"] in ("thunk", "funclet", "pdata"):
            reach[f["kind"]].append(va)
        elif va in exported:
            reach["exported"].append(va)
        elif t.calls.get(va):
            reach["called"].append(va)
        elif t.tails.get(va):
            reach["tailcalled"].append(va)
        else:
            reach["indirect"].append(va)
    for kind, vas in sorted(reach.items()):
        res[f"fn:{kind}"] = ratio(sum(v in bf for v in vas), len(vas))
        extras[f"fn:{kind}:missed"] = [
            f"{v:#x} {t.funcs[v]['name']}" for v in sorted(vas) if v not in bf
        ][:40]
    res["functions"] = ratio(sum(v in bf for v in t.funcs), len(t.funcs))
    sized = [v for v in t.funcs if t.funcs[v]["symbol_size"] and v in bf]

    def trimmed(v: int) -> int:
        """Returns a symbol's size less the `int3` traps that end it."""
        n = t.funcs[v]["size"]
        while n > 1 and img.read(v + n - 1, 1) == bytes([0xCC]):
            n -= 1
        return n

    wrong = [
        v
        for v in sized
        if bf[v] not in (t.funcs[v]["size"], trimmed(v))
        and b.span(v) not in (t.funcs[v]["size"], trimmed(v))
    ]
    res["extent"] = ratio(len(sized) - len(wrong), len(sized))
    extras["extent:wrong"] = [
        f"{v:#x} {t.funcs[v]['name']} truth={t.funcs[v]['size']} borer={b.span(v)}"
        for v in sorted(wrong)
    ][:40]
    if t.complete_funcs:
        extra = sorted(
            v for v in set(bf) - set(t.funcs) if not (img.section(v) or ("",))[0].startswith(".plt")
        )
        res["fn:precision"] = ratio(len(bf) - len(extra), len(bf))
        extras["fn:extra"] = [hex(v) for v in extra][:60]

    for cat, table in (
        ("calls", t.calls),
        ("tails", t.tails),
        ("data", t.data),
        ("imports", t.iat),
    ):
        targets = spread(sorted(table), sample)
        hit = total = extra = listed = hidden = 0
        missed, unexpected = [], []
        for target in targets:
            got, folded, unnamed = b.sites(target)
            for site in sorted(table[target]):
                total += 1
                if site in got or owner_of(t, site) in folded:
                    hit += 1
                elif unnamed:
                    hidden += 1
                elif len(missed) < 40:
                    missed.append(f"{site:#x} -> {target:#x}")
            if cat == "calls":
                calls = {s for s, k in got.items() if k == "call"}
                listed += len(calls)
                for s in sorted(calls - table[target] - t.tails.get(target, set())):
                    extra += 1
                    if len(unexpected) < 40:
                        unexpected.append(f"{s:#x} -> {target:#x}")
        res[cat] = ratio(hit, total)
        res[f"{cat}+folds"] = ratio(hit + hidden, total)
        extras[f"{cat}:missed"] = missed
        if cat == "calls":
            res["calls:precision"] = ratio(listed - extra, listed)
            extras["calls:extra"] = unexpected

    if t.switches:
        hit = total = 0
        missed = []
        by_fn: dict[int, list[tuple[int, set[int]]]] = defaultdict(list)
        starts = sorted(bf)

        for branch, targets in t.switches:
            i = bisect.bisect_right(starts, branch) - 1
            by_fn[starts[i] if i >= 0 else branch].append((branch, targets))
        for entry, tables in by_fn.items():
            blocks = function_blocks(b, entry)
            for branch, targets in tables:
                succ: set[int] = set()
                for start, size, term, s in blocks:
                    if start <= branch < start + size and term == "indirect":
                        succ = s
                total += len(targets)
                hit += len(targets & succ)
                if targets - succ and len(missed) < 40:
                    missed.append(f"{branch:#x}: {len(targets - succ)} of {len(targets)} missing")
        res["switch"] = ratio(hit, total)
        extras["switch:missed"] = missed

    t.literals = [lit for lit in t.literals if runs(lit[1])]
    if t.literals:
        rows = []
        for r in b.pages("strings", {"min_length": 4}, 500):
            p = r.split(" ", 3)
            if len(p) == 4 and p[0].startswith("0x"):
                rows.append((int(p[0], 16), int(p[1]) * (2 if p[2] == "utf16" else 1), p[2], p[3]))
        rows.sort()
        starts = [r[0] for r in rows]

        def covered(a: int, n: int) -> bool:
            lo, hi = bisect.bisect_left(starts, a - 4096), bisect.bisect_right(starts, a)
            return any(rows[i][0] + rows[i][1] >= a + n for i in range(lo, hi))

        hit = 0
        missed = []
        spans: list[tuple[int, int]] = []
        for s, body, addrs in t.literals:
            spans += [(a, a + len(body)) for a in addrs]
            if any(all(covered(a + o, n) for o, n in runs(body)) for a in addrs):
                hit += 1
            elif len(missed) < 40:
                missed.append(f"{addrs[0]:#x} {s[:60]!r}")
        res["strings"] = ratio(hit, len(t.literals))
        extras["strings:missed"] = missed
        if t.complete_strings:
            spans.sort()
            sstarts = [s[0] for s in spans]
            extra = []
            for va, n, enc, text in rows:
                i = bisect.bisect_right(sstarts, va + n) - 1
                overlaps = any(spans[j][1] > va for j in range(max(0, i - 8), i + 1))
                if (
                    len(text) >= 7
                    and not overlaps
                    and (img.section(va) or ("?",))[0] not in NAME_SECTIONS
                ):
                    extra.append((va, enc, text))
            res["strings:precision"] = ratio(len(rows) - len(extra), len(rows))
            extras["strings:extra"] = [
                f"{va:#x} {(img.section(va) or ('?',))[0]} {enc} {text[:60]}"
                for va, enc, text in extra
            ][:60]

        referenced = [
            (s, addrs) for s, body, addrs in t.literals if any(t.data.get(a) for a in addrs)
        ]
        hit = 0
        missed = []
        for s, addrs in spread(referenced, sample // 4 or 1):
            q = max(re.split(r'[\\"\x00-\x1f]', s[:60]), key=len)
            if len(q) < 4:
                continue
            _, text = b.c.tool("find_function_by_string", {"filter": q, "limit": 300})
            want = {
                fn for a in addrs for site in t.data.get(a, ()) for fn in [owner_of(t, site)] if fn
            }
            got = {int(m.group(1), 16) for m in re.finditer(r"^0x([0-9a-f]+) ", text, re.M)}
            got |= {e for row in text.splitlines() for e in b.folded(row)}
            if want & got or (not want and got):
                hit += 1
            elif len(missed) < 40:
                missed.append(f"{s[:50]!r} want {sorted(hex(w) for w in want)}")
        res["xstring"] = ratio(hit, len(spread(referenced, sample // 4 or 1)))
        extras["xstring:missed"] = missed

        hit = total = 0
        missed = []
        for s, _body, addrs in spread(
            [lit for lit in t.literals if all(32 <= c < 127 for c in lit[1])], 40
        ):
            _, text = b.c.tool("search", {"query": s[:40], "kind": "text", "limit": 500})
            got = {
                int(m.group(1), 16) for m in re.finditer(r"0x([0-9a-f]+)", text.split("\n", 2)[-1])
            }
            total += 1
            if set(addrs) & got:
                hit += 1
            elif len(missed) < 20:
                missed.append(f"{addrs[0]:#x} {s[:40]!r}")
        res["search:text"] = ratio(hit, total)
        extras["search:text:missed"] = missed

    code = sorted(v for v, f in t.funcs.items() if f["size"] and f["size"] >= 16)
    hit = total = 0
    missed = []
    for va in spread(code, 40):
        raw = img.read(va, 12)
        if len(raw) < 12:
            continue
        q = " ".join(f"{x:02x}" if i not in (5, 6) else "??" for i, x in enumerate(raw))
        _, text = b.c.tool("search", {"query": q, "limit": 500})
        got = {int(m.group(1), 16) for m in re.finditer(r"0x([0-9a-f]+)", text.split("\n", 2)[-1])}
        total += 1
        if va in got:
            hit += 1
        elif len(missed) < 20:
            missed.append(f"{va:#x} {q}")
    res["search:bytes"] = ratio(hit, total)
    extras["search:bytes:missed"] = missed

    for kind, want in (("import", t.imports), ("export", t.exports), ("forward", t.forwards)):
        if not want:
            continue
        got = set()
        for r in b.pages("symbols", {"kind": kind}, 1000):
            p = r.split(None, 1)
            if len(p) == 2 and p[0].startswith("0x"):
                got.add(p[1].split(" -> ")[0].strip())
        got |= {"#" + m.group(1) for n in got if (m := re.search(r"_ord(\d+)$", n))}
        resolved = sorted(n for n in got - want if not re.search(r"_ord\d+$", n))
        for n in sorted(x for x in want - got if x.startswith("#"))[: len(resolved)]:
            got.add(n)
            got.discard(resolved.pop())
        got = {n for n in got if not re.search(r"_ord\d+$", n)}
        res[f"sym:{kind}"] = ratio(len(want & got), len(want))
        res[f"sym:{kind}:precision"] = ratio(len(got & want), len(got))
        extras[f"sym:{kind}:missed"] = sorted(want - got)[:40]
        extras[f"sym:{kind}:extra"] = sorted(got - want)[:40]

    if t.crypto:
        _, text = b.c.tool("find_crypto_constants", {"limit": 500})
        found = {alg for alg in t.crypto if alg.lower() in text.lower()}
        res["crypto"] = ratio(len(found), len(t.crypto))
        extras["crypto:missed"] = sorted(t.crypto - found)
    return res


def runs(body: bytes) -> list[tuple[int, int]]:
    """Returns (offset, bytes) of every run of four or more printable ASCII
    characters in a literal, in its own encoding: a listing ends a row at a
    newline, a tab or a character past ASCII."""
    unit = 2 if len(body) > 1 and body[1] == 0 else 1
    out, start = [], None
    for i in range(0, len(body) + unit, unit):
        ok = i < len(body) and 32 <= body[i] < 127 and (unit == 1 or body[i + 1 : i + 2] == b"\0")
        if ok and start is None:
            start = i
        elif not ok and start is not None:
            if (i - start) // unit >= 4:
                out.append((start, i - start))
            start = None
    return out


def owner_of(t: Truth, site: int) -> int | None:
    """Returns the ground-truth function holding an address."""
    for start, end in t.chunks:
        if start <= site < end and start in t.parents:
            return t.parents[start]
    best = None
    for va, f in t.funcs.items():
        if f["size"] and va <= site < va + f["size"] and (best is None or va > best):
            best = va
    return best


def function_blocks(b: Borer, entry: int) -> list[tuple[int, int, str, set[int]]]:
    """Returns (start, size, terminator, successors) of every block of a function."""
    out, off = [], 0
    while True:
        _, text = b.c.tool("function", {"address": hex(entry), "offset": off})
        page = 0
        for r in text.splitlines():
            p = r.split()
            if len(p) >= 3 and p[0].startswith("0x") and p[1].isdigit():
                out.append(
                    (
                        int(p[0], 16),
                        int(p[1]),
                        p[2],
                        {int(x, 16) for x in p[3:] if x.startswith("0x")},
                    )
                )
                page += 1
        m = re.search(r"showing (\d+) of (\d+) blocks", text)
        if not m or off + page >= int(m.group(2)) or not page:
            return out
        off += page


def targets(bench: Path, work: Path) -> list[tuple[str, Path, Path, callable]]:
    """Returns (tag, file borer reads, file the truth reads, truth builder) per binary."""
    corpus, src = bench / "corpus", bench / "src"
    out = []
    for so in sorted(corpus.glob("*.so")):
        stripped = work / (so.stem + ".stripped.so")
        if not stripped.is_file() or stripped.stat().st_mtime < so.stat().st_mtime:
            run(tool("llvm-objcopy"), "--strip-all", str(so), str(stripped))
        sources = [src / ("hard.c" if so.name.startswith("hard") else "suite.c")]

        def build(so=so, sources=sources) -> tuple[Truth, Image]:
            t, img = Truth(), Image(so)
            nm_functions(t, so)
            disassembly(t, so, img)
            source_literals(t, sources, img)
            source_crypto(t, sources)
            return t, img

        out.append((so.name.replace(".so", "_elf"), stripped, so, build))

    sqlite_src = next(bench.glob("dl/sqlite/*/sqlite3.c"), None)
    dll = work / "sqlite3_pdb.dll"
    if sqlite_src and not dll.is_file():
        run(
            tool("clang-cl"),
            "/nologo",
            "/O2",
            "/Zi",
            "/MD",
            "-DSQLITE_API=__declspec(dllexport)",
            "/LD",
            str(sqlite_src),
            f"/Fe{dll}",
            "/link",
            "/DEBUG:FULL",
            f"/PDB:{work / 'sqlite3_pdb.pdb'}",
            cwd=work,
        )
    if dll.is_file():

        def build_sqlite() -> tuple[Truth, Image]:
            t, img = Truth(), Image(dll)
            pdb_full(t, work / "sqlite3_pdb.pdb", img)
            pdb_publics(t, work / "sqlite3_pdb.pdb", img)
            pdata(t, img)
            coff_symbols(t, dll)
            disassembly(t, dll, img)
            source_literals(t, [sqlite_src], img)
            t.complete_strings = False
            source_crypto(t, [sqlite_src])
            return t, img

        out.append(("sqlite3_pdb", dll, dll, build_sqlite))

    kb = work / "kernelbase.dll"
    if not kb.is_file():
        shutil.copy(
            Path(os.environ.get("SYSTEMROOT", r"C:\Windows")) / "System32" / "kernelbase.dll", kb
        )
    for tag, path in (("notepad", corpus / "notepad.exe"), ("kernelbase", kb)):
        pdb = next(
            iter(
                sorted(
                    SYMCACHE.glob(f"{path.stem}.pdb/*/{path.stem}.pdb"),
                    key=lambda p: p.stat().st_mtime,
                )
            ),
            None,
        )

        def build_public(path=path, pdb=pdb) -> tuple[Truth, Image]:
            t, img = Truth(), Image(path)
            if pdb is not None and pdb_matches(pdb, img):
                pdb_publics(t, pdb, img)
            pdata(t, img)
            coff_symbols(t, path)
            disassembly(t, path, img)
            return t, img

        if path.is_file():
            out.append((tag, path, path, build_public))
    return out


def pdb_matches(pdb: Path, img: Image) -> bool:
    """Returns whether a PDB's guid and age are the ones a PE's debug record names."""
    rva, size = img.dirs[6]
    raw = img.read(img.base + rva, size)
    for i in range(len(raw) // 28):
        typ, sz, addr = (
            struct.unpack_from("<I", raw, i * 28 + 12)[0],
            *struct.unpack_from("<II", raw, i * 28 + 16),
        )
        rec = img.read(img.base + addr, sz)
        if typ == 2 and rec[:4] == b"RSDS":
            guid = rec[4:20]
            g = f"{struct.unpack_from('<I', guid)[0]:08X}{struct.unpack_from('<H', guid, 4)[0]:04X}{struct.unpack_from('<H', guid, 6)[0]:04X}{guid[8:].hex().upper()}{struct.unpack_from('<I', rec, 20)[0]:X}"
            return pdb.parent.name == g
    return False


def table(runs: list[dict]) -> str:
    """Renders one row per binary and category, a column per run."""
    labels = [r["label"] for r in runs]
    out = ["| binary | category | " + " | ".join(labels) + " |", "|---|---|" + "---|" * len(labels)]
    tags = list(dict.fromkeys(tag for r in runs for tag in r["binaries"]))
    for tag in tags:
        cats = list(dict.fromkeys(c for r in runs for c in r["binaries"].get(tag, {})))
        for cat in cats:
            cells = []
            for r in runs:
                v = r["binaries"].get(tag, {}).get(cat)
                cells.append(
                    "-"
                    if not v
                    else f"{100 * v['hit'] / v['total']:.1f}% ({v['hit']}/{v['total']})"
                    if v["total"]
                    else "n/a"
                )
            out.append(f"| {tag} | {cat} | " + " | ".join(cells) + " |")
    return "\n".join(out)


def main() -> None:
    """Measures recall and precision per binary and writes the run."""
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument(
        "--bench", type=Path, default=Path(os.environ.get("BORER_BENCH", r"D:\Projects\bench"))
    )
    ap.add_argument("--borer", default=None)
    ap.add_argument("--work", type=Path, default=None)
    ap.add_argument("--only", default="")
    ap.add_argument("--label", default="run")
    ap.add_argument("--sample", type=int, default=2000, help="targets looked up per xref category")
    ap.add_argument("--compare", default="")
    a = ap.parse_args()
    work = a.work or a.bench / "out" / "recall"
    work.mkdir(parents=True, exist_ok=True)
    if a.compare:
        print(
            table(
                [
                    json.loads((work / f"recall_{label}.json").read_text())
                    for label in a.compare.split(",")
                ]
            )
        )
        return
    exe = a.borer or str(
        Path(os.environ.get("CARGO_TARGET_DIR") or ROOT / "target") / "release" / "borer.exe"
    )
    only = set(filter(None, a.only.split(",")))
    result = {"label": a.label, "borer": exe, "binaries": {}, "extras": {}}
    for tag, path, _, build in targets(a.bench, work):
        if only and tag not in only:
            continue
        print(f"== {tag}", file=sys.stderr, flush=True)
        t, img = build()
        b = Borer(exe, path)
        extras: dict = {}
        try:
            result["binaries"][tag] = measure(t, img, b, a.sample, extras)
        finally:
            b.close()
        result["extras"][tag] = extras
        for cat, v in result["binaries"][tag].items():
            print(f"  {cat:24} {v['hit']}/{v['total']}", file=sys.stderr, flush=True)
    (work / f"recall_{a.label}.json").write_text(json.dumps(result, indent=1))
    print(table([result]))


if __name__ == "__main__":
    main()
