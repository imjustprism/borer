#!/usr/bin/env python3
"""Golden diff of borer's `index` output: which functions' text changed.

Usage:
  python scripts/run/golden.py record <borer.exe> [--baseline FILE] [--full DIR] [--only TAG,TAG]
  python scripts/run/golden.py check  <borer.exe> [--baseline FILE] [--full DIR] [--only TAG,TAG]
                                       [--allow FILE] [--quiet]
  python scripts/run/golden.py show   <borer.exe> <tag> <entry>

`record` runs `borer index` on each corpus binary (notepad, msvcrt32,
sqlite3) and writes the baseline (default scripts/run/golden.tsv): per
binary its sha256 and function count, then per function its entry and a
16-hex-digit hash of its text. With --full DIR it also writes every text to
DIR/<tag>/<entry>.c, the full text kept off the repository.

`check` indexes again and compares with the baseline. It prints, per binary,
`identical` or the functions that changed, appeared or went away, and exits
1 when any did. With --full DIR (a directory an earlier `record --full`
wrote) it also prints a unified diff of each changed function. With --allow
FILE (one `<tag> <entry>` per line, `#` comments) the listed functions may
change: a step that changes only the functions it means to stays green.
`show` prints one function's text as `index` writes it now.

The corpus is read from BORER_GOLDEN_CORPUS, else from `bench/corpus` beside
the main checkout. A binary that is missing, or whose bytes differ from the
ones the baseline recorded, is skipped with `[skip]`, never failed: the hash
of a text only means something for the bytes it was decompiled from. The
index runs with an empty cache directory and no packs, so a pack directory
on the machine cannot change the answer.
"""

from __future__ import annotations

import difflib
import hashlib
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.root import ROOT  # noqa: E402

CORPUS = [
    ("notepad", "notepad.exe"),
    ("msvcrt32", "msvcrt32.dll"),
    ("sqlite3", "sqlite3.x64.dll"),
]
"""The corpus: tag and file name in the corpus folder."""

BASELINE = ROOT / "scripts" / "run" / "golden.tsv"
"""Where the hashes live unless --baseline says otherwise."""

MAGIC = b"BORERIDX"
"""The first bytes of an index file (crates/borer/src/index.rs)."""

FORMAT = 4
"""The index file layout this reader knows."""


def corpus_dir() -> Path:
    """The folder the corpus binaries are read from."""
    named = os.environ.get("BORER_GOLDEN_CORPUS")
    if named:
        return Path(named)
    common = subprocess.run(
        ["git", "rev-parse", "--path-format=absolute", "--git-common-dir"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    ).stdout.strip()
    main = Path(common).parent if common else ROOT
    return main.parent / "bench" / "corpus"


def sha256(path: Path) -> str:
    """The hex sha256 of a file's bytes."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def text_hash(text: str) -> str:
    """The compact hash a function's text is stored by."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def read_index(path: Path) -> list[tuple[int, str, str]]:
    """The (entry, name, text) records of an index file, in file order."""
    data = path.read_bytes()
    if data[:8] != MAGIC:
        raise SystemExit(f"{path}: not an index file")
    (fmt,) = struct.unpack_from("<I", data, 8)
    if fmt != FORMAT:
        raise SystemExit(f"{path}: index format {fmt}, this script reads {FORMAT}")
    (count,) = struct.unpack_from("<I", data, 28)
    at = 40
    out = []
    for _ in range(count):
        (entry,) = struct.unpack_from("<Q", data, at)
        at += 8
        fields = []
        for _ in range(2):
            (n,) = struct.unpack_from("<I", data, at)
            at += 4
            fields.append(data[at : at + n].decode("utf-8", "replace"))
            at += n
        out.append((entry, fields[0], fields[1]))
    return out


def index(exe: str, binary: Path) -> list[tuple[int, str, str]]:
    """Runs `borer index` on a binary in a fresh cache and returns its records."""
    env = {k: v for k, v in os.environ.items() if k not in {"BORER_PACKS", "BORER_BUDGET"}}
    with tempfile.TemporaryDirectory(prefix="borer-golden-") as cache:
        env["BORER_CACHE_DIR"] = cache
        env["BORER_AUTO_PACKS"] = "0"
        proc = subprocess.run([exe, "index", str(binary)], env=env, capture_output=True, text=True)
        if proc.returncode != 0:
            raise SystemExit(f"index {binary} exited {proc.returncode}: {proc.stderr[-400:]}")
        files = list(Path(cache).rglob("*.pcidx"))
        if len(files) != 1:
            raise SystemExit(f"index {binary}: expected one index file, found {len(files)}")
        return read_index(files[0])


def read_baseline(path: Path) -> dict[str, tuple[str, dict[int, str]]]:
    """The baseline: per tag the binary's sha256 and each entry's text hash."""
    out: dict[str, tuple[str, dict[int, str]]] = {}
    if not path.is_file():
        return out
    tag = ""
    for line in path.read_text(encoding="utf-8").splitlines():
        parts = line.split("\t")
        if parts[0] == "binary":
            tag = parts[1]
            out[tag] = (parts[2], {})
        elif len(parts) == 2 and tag:
            out[tag][1][int(parts[0], 16)] = parts[1]
    return out


def write_baseline(path: Path, rows: dict[str, tuple[str, dict[int, str]]]) -> None:
    """Writes the baseline, binaries in corpus order and entries ascending."""
    lines = ["# golden.py: per binary its sha256 and count, then entry and text hash"]
    for tag, _ in CORPUS:
        if tag not in rows:
            continue
        digest, funcs = rows[tag]
        lines.append(f"binary\t{tag}\t{digest}\t{len(funcs)}")
        lines += [f"{e:x}\t{h}" for e, h in sorted(funcs.items())]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")


def read_allow(path: str | None) -> set[tuple[str, int]]:
    """The `<tag> <entry>` pairs a check lets change."""
    if not path:
        return set()
    out = set()
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        words = line.split("#", 1)[0].split()
        if len(words) == 2:
            out.add((words[0], int(words[1], 16)))
    return out


def option(args: list[str], name: str) -> str | None:
    """The value after `name` in the arguments, if any."""
    return args[args.index(name) + 1] if name in args and args.index(name) + 1 < len(args) else None


def selected(args: list[str]) -> list[tuple[str, Path]]:
    """The corpus binaries to run: (tag, path), filtered by --only."""
    only = option(args, "--only")
    keep = set(only.split(",")) if only else None
    folder = corpus_dir()
    return [(t, folder / f) for t, f in CORPUS if keep is None or t in keep]


def record(exe: str, args: list[str]) -> int:
    """Writes the baseline (and with --full the texts) from a fresh index."""
    path = Path(option(args, "--baseline") or BASELINE)
    full = option(args, "--full")
    rows = read_baseline(path)
    for tag, binary in selected(args):
        if not binary.is_file():
            print(f"[skip] {tag}: no {binary}")
            continue
        records = index(exe, binary)
        rows[tag] = (sha256(binary), {e: text_hash(t) for e, _, t in records})
        if full:
            out = Path(full) / tag
            out.mkdir(parents=True, exist_ok=True)
            for e, _, t in records:
                (out / f"{e:x}.c").write_text(t, encoding="utf-8", newline="\n")
        print(f"[ok  ] {tag}: {len(records)} functions", flush=True)
    write_baseline(path, rows)
    print(f"baseline written: {path}")
    return 0


def check(exe: str, args: list[str]) -> int:
    """Compares a fresh index with the baseline; 1 when a function changed."""
    base = read_baseline(Path(option(args, "--baseline") or BASELINE))
    full = option(args, "--full")
    allow = read_allow(option(args, "--allow"))
    quiet = "--quiet" in args
    failed = 0
    for tag, binary in selected(args):
        if not binary.is_file():
            print(f"[skip] {tag}: no {binary}")
            continue
        if tag not in base:
            print(f"[skip] {tag}: not in the baseline")
            continue
        digest, want = base[tag]
        if sha256(binary) != digest:
            print(f"[skip] {tag}: {binary} is not the binary the baseline recorded")
            continue
        records = index(exe, binary)
        got = {e: text_hash(t) for e, _, t in records}
        texts = {e: (n, t) for e, n, t in records}
        changed = sorted(e for e in got.keys() & want.keys() if got[e] != want[e])
        added = sorted(got.keys() - want.keys())
        gone = sorted(want.keys() - got.keys())
        moved = [e for e in changed + added + gone if (tag, e) not in allow]
        allowed = len(changed) + len(added) + len(gone) - len(moved)
        if not moved:
            note = f", {allowed} allowed change(s)" if allowed else ""
            print(f"[ok  ] {tag}: identical over {len(got)} functions{note}")
            continue
        failed += 1
        print(
            f"[FAIL] {tag}: {len(changed)} changed, {len(added)} new, {len(gone)} gone "
            f"of {len(want)}" + (f", {allowed} allowed" if allowed else "")
        )
        for e in moved:
            kind = "changed" if e in changed else "new" if e in added else "gone"
            name = texts.get(e, ("", ""))[0]
            print(f"  {kind}\t{tag}\t{e:x}\t{name}")
            old = Path(full) / tag / f"{e:x}.c" if full else None
            if quiet or kind != "changed" or old is None or not old.is_file():
                continue
            diff = difflib.unified_diff(
                old.read_text(encoding="utf-8").splitlines(),
                texts[e][1].splitlines(),
                f"baseline/{e:x}",
                f"now/{e:x}",
                lineterm="",
            )
            print("\n".join(f"    {d}" for d in diff))
    return 1 if failed else 0


def show(exe: str, args: list[str]) -> int:
    """Prints one function's current text."""
    tag, entry = args[0], int(args[1], 16)
    for t, binary in selected([]):
        if t == tag:
            for e, _, text in index(exe, binary):
                if e == entry:
                    print(text, end="")
                    return 0
            print(f"no function at {entry:#x} in {tag}")
            return 1
    print(f"no corpus binary {tag}")
    return 1


def main(argv: list[str]) -> int:
    args = argv[1:]
    if len(args) < 2 or args[0] not in {"record", "check", "show"}:
        print(__doc__)
        return 2
    command, exe, rest = args[0], os.path.abspath(args[1]), args[2:]
    return {"record": record, "check": check, "show": show}[command](exe, rest)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
