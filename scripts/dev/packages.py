#!/usr/bin/env python3
"""Write borer's package-manager packages from a release's archives.

    gh release download v0.2.5 -R imjustprism/borer -D dist
    python scripts/dev/packages.py manifests dist [OUT]
    python scripts/dev/packages.py npm dist OUT

`manifests` writes the Homebrew formula and the Scoop manifest
(`OUT/homebrew/borer.rb`, `OUT/scoop/borer.json`, `OUT` being `packaging/`
by default) from the release's SHA256SUMS alone. `npm` writes one directory
per npm package under `OUT`: `borer-mcp`, whose `borer-mcp` and `borer`
commands run packaging/npm/borer-mcp.js, and `borer-mcp-<os>-<cpu>` per
target, holding only that target's binary, its licenses and a package.json
whose `os` and `cpu` let npm install it on that platform alone; `borer-mcp`
names them all as optionalDependencies (the esbuild pattern). Every archive
is checked against SHA256SUMS before it is read.

Nothing is published: the release workflow copies what this writes into the
tap and bucket and publishes the packages.
"""

from __future__ import annotations

import hashlib
import io
import json
import re
import sys
import tarfile
import zipfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.root import ROOT  # noqa: E402

REPO = "https://github.com/imjustprism/borer"
"""Where the releases are published."""

DESCRIPTION = "Reverse-engineering engine for AI agents: MCP server and CLI"
"""The one-line summary every package carries."""

LICENSE = "AGPL-3.0-only"
"""borer's SPDX license expression."""

TARGETS = {
    "x86_64-pc-windows-msvc": ("win32", "x64"),
    "x86_64-unknown-linux-gnu": ("linux", "x64"),
    "x86_64-apple-darwin": ("darwin", "x64"),
    "aarch64-apple-darwin": ("darwin", "arm64"),
}
"""The targets release.yml builds, each one archive, with Node's
`process.platform` and `process.arch` there."""

NOTICES = ("LICENSE", "NOTICE", "THIRD-PARTY-LICENSES", "RUST-STD-COPYRIGHT.html")
"""The license files each archive carries beside the binary, which travel with it."""

NPM = "borer-mcp"
"""The npm package (`borer` is taken on npm)."""

ABOUT = f"""# borer

{DESCRIPTION}. This package installs the prebuilt `borer` binary of the
matching GitHub release; see {REPO} for what it does and how to use it.
"""
"""The README of every published package."""


def release(assets: Path) -> tuple[str, dict[str, tuple[str, str]]]:
    """Returns a release's version and, per target, its archive name and SHA-256.

    Args:
        assets: The directory holding the release's SHA256SUMS (and archives).

    Returns:
        The version without its `v`, and a map from target to archive file
        name and lowercase hex digest. Exits when a target's archive is
        missing or two archives disagree on the version.
    """
    sums: dict[str, str] = {}
    for line in (assets / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        digest, name = line.split()
        sums[name.lstrip("*")] = digest.lower()
    versions: set[str] = set()
    found: dict[str, tuple[str, str]] = {}
    for target in TARGETS:
        pattern = re.compile(rf"borer-v(.+)-{target}\.(?:tar\.gz|zip)")
        hits = [(n, d, m.group(1)) for n, d in sums.items() if (m := pattern.fullmatch(n))]
        if len(hits) != 1:
            raise SystemExit(f"SHA256SUMS lists {len(hits)} archives for {target}, not one")
        name, digest, version = hits[0]
        versions.add(version)
        found[target] = (name, digest)
    if len(versions) != 1:
        raise SystemExit(f"the archives name more than one version: {sorted(versions)}")
    return versions.pop(), found


def url(version: str, name: str) -> str:
    """Returns the download URL of one release archive."""
    return f"{REPO}/releases/download/v{version}/{name}"


def unpack(assets: Path, name: str, digest: str) -> dict[str, bytes]:
    """Returns the files of one release archive, by base name.

    Args:
        assets: The directory holding the archive.
        name: The archive's file name.
        digest: Its SHA-256 from SHA256SUMS.

    Returns:
        Each regular file's base name and bytes. Exits when the archive's
        hash is not `digest`.
    """
    data = (assets / name).read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise SystemExit(f"{name}: its SHA-256 is not the one SHA256SUMS lists")
    if name.endswith(".zip"):
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            return {Path(i).name: z.read(i) for i in z.namelist() if not i.endswith("/")}
    files: dict[str, bytes] = {}
    with tarfile.open(fileobj=io.BytesIO(data)) as t:
        for member in t.getmembers():
            if member.isfile() and (f := t.extractfile(member)):
                files[Path(member.name).name] = f.read()
    return files


def binary(target: str) -> str:
    """Returns the binary's file name on `target`."""
    return "borer.exe" if "windows" in target else "borer"


def write(path: Path, data: bytes | str, mode: int = 0o644) -> None:
    """Writes one package file with `mode`, creating its directory; text as UTF-8."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data.encode("utf-8") if isinstance(data, str) else data)
    path.chmod(mode)


def formula(version: str, archives: dict[str, tuple[str, str]]) -> str:
    """Returns the Homebrew formula: macOS arm64 and x86_64, Linux x86_64.

    Homebrew unpacks into the archive's one top directory, so the binary
    is at the root of the stage.
    """

    def source(target: str) -> str:
        name, digest = archives[target]
        return f'      url "{url(version, name)}"\n      sha256 "{digest}"\n'

    return (
        "class Borer < Formula\n"
        f'  desc "{DESCRIPTION}"\n'
        f'  homepage "{REPO}"\n'
        f'  version "{version}"\n'
        f'  license "{LICENSE}"\n'
        "\n"
        "  on_macos do\n"
        "    on_arm do\n"
        f"{source('aarch64-apple-darwin')}"
        "    end\n"
        "    on_intel do\n"
        f"{source('x86_64-apple-darwin')}"
        "    end\n"
        "  end\n"
        "\n"
        "  on_linux do\n"
        "    on_intel do\n"
        f"{source('x86_64-unknown-linux-gnu')}"
        "    end\n"
        "  end\n"
        "\n"
        "  def install\n"
        '    bin.install "borer"\n'
        '    prefix.install "THIRD-PARTY-LICENSES", "RUST-STD-COPYRIGHT.html"\n'
        "  end\n"
        "\n"
        "  test do\n"
        '    assert_match "borer #{version}", shell_output("#{bin}/borer --version")\n'
        "  end\n"
        "end\n"
    )


def scoop(version: str, archives: dict[str, tuple[str, str]]) -> str:
    """Returns the Scoop manifest for Windows x64, which updates itself from
    GitHub releases (`checkver`, `autoupdate`) with the hash from SHA256SUMS."""
    target = "x86_64-pc-windows-msvc"
    name, digest = archives[target]
    later = f"borer-v$version-{target}"
    manifest = {
        "version": version,
        "description": DESCRIPTION,
        "homepage": REPO,
        "license": LICENSE,
        "architecture": {
            "64bit": {
                "url": url(version, name),
                "hash": digest,
                "extract_dir": name.removesuffix(".zip"),
            }
        },
        "bin": "borer.exe",
        "checkver": "github",
        "autoupdate": {
            "architecture": {
                "64bit": {
                    "url": f"{REPO}/releases/download/v$version/{later}.zip",
                    "hash": {"url": "$baseurl/SHA256SUMS"},
                    "extract_dir": later,
                }
            }
        },
    }
    return json.dumps(manifest, indent=2) + "\n"


def manifests(assets: Path, out: Path) -> None:
    """Writes `out/homebrew/borer.rb` and `out/scoop/borer.json` for a release."""
    version, archives = release(assets)
    for path, text in (
        (out / "homebrew" / "borer.rb", formula(version, archives)),
        (out / "scoop" / "borer.json", scoop(version, archives)),
    ):
        write(path, text)
        print(f"wrote {path}")


def npm(assets: Path, out: Path) -> None:
    """Writes the `borer-mcp` package and one platform package per target under `out`."""
    version, archives = release(assets)
    common = {
        "version": version,
        "license": LICENSE,
        "homepage": REPO,
        "repository": {"type": "git", "url": f"git+{REPO}.git"},
    }
    platforms: dict[str, str] = {}
    for target, (os_name, cpu) in TARGETS.items():
        name = f"{NPM}-{os_name}-{cpu}"
        files = unpack(assets, *archives[target])
        manifest = {
            "name": name,
            "description": f"The borer binary for {os_name}-{cpu}, which {NPM} runs.",
            **common,
            "os": [os_name],
            "cpu": [cpu],
            **({"libc": ["glibc"]} if os_name == "linux" else {}),
        }
        write(out / name / "package.json", json.dumps(manifest, indent=2) + "\n")
        write(out / name / "README.md", ABOUT)
        for notice in NOTICES:
            write(out / name / notice, files[notice])
        write(out / name / "bin" / binary(target), files[binary(target)], 0o755)
        platforms[name] = version
        print(f"wrote {out / name}")
    launcher = out / NPM
    manifest = {
        "name": NPM,
        "description": DESCRIPTION,
        **common,
        "keywords": ["mcp", "mcp-server", "reverse-engineering", "decompiler", "disassembler"],
        "bin": {NPM: "bin/borer-mcp.js", "borer": "bin/borer-mcp.js"},
        "engines": {"node": ">=18"},
        "optionalDependencies": platforms,
    }
    write(launcher / "package.json", json.dumps(manifest, indent=2) + "\n")
    write(launcher / "README.md", ABOUT)
    write(launcher / "LICENSE", (ROOT / "LICENSE").read_bytes())
    script = (ROOT / "packaging" / "npm" / "borer-mcp.js").read_bytes()
    write(launcher / "bin" / "borer-mcp.js", script, 0o755)
    print(f"wrote {launcher}")


def main() -> None:
    """Runs the command the arguments name."""
    args = sys.argv[1:]
    if len(args) in (2, 3) and args[0] == "manifests":
        manifests(Path(args[1]), Path(args[2]) if len(args) == 3 else ROOT / "packaging")
    elif len(args) == 3 and args[0] == "npm":
        npm(Path(args[1]), Path(args[2]))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
