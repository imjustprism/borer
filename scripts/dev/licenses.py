#!/usr/bin/env python3
"""Write THIRD-PARTY-LICENSES: the license of everything the borer binary links.

    python scripts/dev/licenses.py --target x86_64-pc-windows-msvc --out THIRD-PARTY-LICENSES

The release workflow runs this for each target and packs the file beside
LICENSE and NOTICE, since most of these licenses require their copyright and
license text to travel with a binary.

What it lists. The crates the `borer` package depends on for that target,
normal dependencies only (build scripts and dev dependencies do not ship),
from `cargo metadata --filter-platform`; the Rust standard library, whose
license texts come from the toolchain's `rust-docs` component, with its full
notice copied beside the output as RUST-STD-COPYRIGHT.html; and the C
sources a crate compiles in, named in `scripts/dev/licenses.tmpl`'s
`[bundled]` lines (mimalloc's, inside `libmimalloc-sys`). Each crate gets its
name, version, SPDX license expression, where its source is published (which
MPL-2.0 asks a binary to say) and the text of every license, copying, notice
or copyright file at its root. A crate that ships none is listed with its
expression, its authors and the text of each license the expression names
(from `rust-docs`), and is named on stderr.

The layout is the checked-in template `scripts/dev/licenses.tmpl`: its text,
with `{{target}}`, `{{std}}` and `{{crates}}` replaced. The output is
deterministic (crates sorted by name and version), so two runs over one lock
file and one toolchain agree.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TEMPLATE = Path(__file__).with_name("licenses.tmpl")
LICENSE_PREFIXES = ("license", "licence", "copying", "notice", "copyright", "unlicense")
RULE = "-" * 78
STD_NOTICE = "RUST-STD-COPYRIGHT.html"
NL = "\n"


def run(*command: str) -> str:
    """A command's standard output, trimmed; a failure stops the script."""
    return subprocess.run(
        list(command), cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()


def docs() -> Path:
    """The toolchain's `rust-docs` directory, which holds the license texts."""
    path = Path(run("rustc", "--print", "sysroot")) / "share" / "doc" / "rust"
    if not (path / "licenses").is_dir():
        sys.exit(f"licenses: no {path / 'licenses'}; run `rustup component add rust-docs`")
    return path


def shipped(meta: dict) -> list[dict]:
    """The packages the `borer` binary links: its normal dependencies, transitively."""
    packages = {p["id"]: p for p in meta["packages"]}
    nodes = {n["id"]: n for n in meta["resolve"]["nodes"]}
    workspace = set(meta["workspace_members"])
    root = next(i for i in workspace if packages[i]["name"] == "borer")
    seen: set[str] = set()
    todo = [root]
    while todo:
        for dep in nodes[todo.pop()]["deps"]:
            normal = any(k["kind"] is None for k in dep["dep_kinds"])
            if normal and dep["pkg"] not in seen:
                seen.add(dep["pkg"])
                todo.append(dep["pkg"])
    return sorted(
        (packages[i] for i in seen if i not in workspace),
        key=lambda p: (p["name"], p["version"]),
    )


def license_files(directory: Path) -> list[Path]:
    """The license-like files at a directory's root, sorted by name."""
    if not directory.is_dir():
        return []
    return sorted(
        (
            f
            for f in directory.iterdir()
            if f.is_file() and f.name.lower().startswith(LICENSE_PREFIXES)
        ),
        key=lambda f: f.name.lower(),
    )


def texts(files: list[Path], base: Path) -> str:
    """Each file's text under a line naming it, relative to `base`."""
    parts = []
    for f in files:
        body = f.read_text(encoding="utf-8", errors="replace").strip()
        parts.append(f"== {f.relative_to(base).as_posix()} =={NL}{NL}{body}{NL}")
    return NL.join(parts)


def bundled_lines(template: str) -> dict[str, list[str]]:
    """The `[bundled] crate path` lines of the template, by crate."""
    found: dict[str, list[str]] = {}
    for line in template.splitlines():
        if line.startswith("[bundled] "):
            crate, path = line.removeprefix("[bundled] ").split(maxsplit=1)
            found.setdefault(crate, []).append(path.strip())
    return found


def crate_section(package: dict, bundled: list[str], missing: list[str], known: Path) -> str:
    """One crate's entry: what it is, where its source is, and its license texts."""
    name, version = package["name"], package["version"]
    directory = Path(package["manifest_path"]).parent
    expression = package.get("license") or package.get("license_file") or "not stated"
    head = [
        RULE,
        f"{name} {version}",
        f"license: {expression}",
        f"source: https://crates.io/crates/{name}/{version}",
    ]
    if package.get("repository"):
        head.append(f"repository: {package['repository']}")
    files = license_files(directory)
    for rel in bundled:
        path = directory / rel
        if not path.is_file():
            sys.exit(f"licenses: {name} {version} has no {rel}; fix the [bundled] line")
        files.append(path)
    if files:
        return NL.join(head) + NL + NL + texts(files, directory)
    missing.append(f"{name} {version}")
    head.append(f"authors: {', '.join(package.get('authors') or []) or 'not stated'}")
    head.append("The crate ships no license file; the texts of the licenses it states follow.")
    ids = sorted(set(re.findall(r"[A-Za-z0-9.+-]+", expression)) - {"OR", "AND", "WITH"})
    named = [known / f"{i.removesuffix('+')}.txt" for i in ids]
    return NL.join(head) + NL + NL + texts([f for f in named if f.is_file()], known)


def std_section(rust_docs: Path) -> str:
    """The Rust standard library's licenses, naming its full notice."""
    licenses = rust_docs / "licenses"
    head = [
        RULE,
        f"The Rust standard library ({run('rustc', '-V')})",
        "license: MIT OR Apache-2.0",
        "source: https://github.com/rust-lang/rust",
        f"notices of the library and the code it includes: {STD_NOTICE}, beside this file",
    ]
    return (
        NL.join(head)
        + NL
        + NL
        + texts([licenses / "MIT.txt", licenses / "Apache-2.0.txt"], licenses)
    )


def main() -> None:
    """Writes the file for the target the arguments name, and the std notice beside it."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--target", required=True, help="the target triple built")
    parser.add_argument("--out", required=True, type=Path, help="the file to write")
    args = parser.parse_args()
    rust_docs = docs()
    template = TEMPLATE.read_text(encoding="utf-8")
    bundled = bundled_lines(template)
    meta = json.loads(
        run(
            "cargo",
            "metadata",
            "--format-version",
            "1",
            "--locked",
            "--filter-platform",
            args.target,
        )
    )
    missing: list[str] = []
    crates = NL.join(
        crate_section(p, bundled.get(p["name"], []), missing, rust_docs / "licenses")
        for p in shipped(meta)
    )
    body = NL.join(line for line in template.splitlines() if not line.startswith("[bundled] "))
    out = body.replace("{{target}}", args.target)
    out = out.replace("{{std}}", std_section(rust_docs)).replace("{{crates}}", crates)
    args.out.write_text(out.rstrip() + NL, encoding="utf-8", newline=NL)
    shutil.copyfile(rust_docs / "COPYRIGHT-library.html", args.out.with_name(STD_NOTICE))
    if missing:
        print(f"licenses: no license file in {', '.join(missing)}", file=sys.stderr)


if __name__ == "__main__":
    main()
