#!/usr/bin/env python3
"""Write borer's package-manager packages from a release's archives.

    gh release download v0.2.5 -R imjustprism/borer -D dist
    python scripts/dev/packages.py manifests dist [OUT]
    python scripts/dev/packages.py npm dist OUT
    python scripts/dev/packages.py wheels dist OUT

`manifests` writes the Homebrew formula and the Scoop manifest
(`OUT/homebrew/borer.rb`, `OUT/scoop/borer.json`, `OUT` being `packaging/`
by default) from the release's SHA256SUMS alone. `npm` writes one directory
per npm package under `OUT`: `borer-re`, whose `borer-re` and `borer`
commands run packaging/npm/borer-re.js, and `borer-re-<os>-<cpu>` per
target, holding only that target's binary, its licenses and a package.json
whose `os` and `cpu` let npm install it on that platform alone; `borer-re`
names them all as optionalDependencies (the esbuild pattern). `wheels`
writes one PyPI wheel of `borer` per target into `OUT`, the binary as the
wheel's script so pip puts a `borer` command on PATH (the ruff and uv
pattern), tagged with the platform the binary itself requires. Every
archive is checked against SHA256SUMS before it is read.

Nothing is published: the release workflow copies what this writes into the
tap and bucket and publishes the packages.
"""

from __future__ import annotations

import base64
import hashlib
import io
import json
import re
import struct
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

NPM = "borer-re"
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
    """Writes the `borer-re` package and one platform package per target under `out`."""
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
        "bin": {NPM: "bin/borer-re.js", "borer": "bin/borer-re.js"},
        "engines": {"node": ">=18"},
        "optionalDependencies": platforms,
    }
    write(launcher / "package.json", json.dumps(manifest, indent=2) + "\n")
    write(launcher / "README.md", ABOUT)
    write(launcher / "LICENSE", (ROOT / "LICENSE").read_bytes())
    script = (ROOT / "packaging" / "npm" / "borer-re.js").read_bytes()
    write(launcher / "bin" / "borer-re.js", script, 0o755)
    print(f"wrote {launcher}")


def platform_tag(target: str, exe: bytes) -> str:
    """Returns the wheel platform tag `target`'s binary requires.

    On Linux that is the newest glibc symbol version the binary links
    (`manylinux_2_<n>_x86_64`), on macOS the minimum system version its
    `LC_BUILD_VERSION` or `LC_VERSION_MIN_MACOSX` load command names.

    Args:
        target: The Rust target the binary is built for.
        exe: The binary.

    Returns:
        The tag. Exits when the binary does not name what the tag needs.
    """
    if "windows" in target:
        return "win_amd64"
    if "linux" in target:
        minors = [int(m.group(1)) for m in re.finditer(rb"GLIBC_2\.(\d+)", exe)]
        if not minors:
            raise SystemExit(f"{target}: the binary names no glibc version")
        return f"manylinux_2_{max(minors)}_x86_64"
    arch = "arm64" if target.startswith("aarch64") else "x86_64"
    magic, ncmds = struct.unpack_from("<I12xI", exe)
    if magic != 0xFEEDFACF:
        raise SystemExit(f"{target}: the binary is not a 64-bit little-endian Mach-O")
    off = 32
    for _ in range(ncmds):
        cmd, size = struct.unpack_from("<II", exe, off)
        if cmd in (0x32, 0x24):
            minos = struct.unpack_from("<II", exe, off + 8)[cmd == 0x32]
            return f"macosx_{minos >> 16}_{(minos >> 8) & 0xFF}_{arch}"
        off += size
    raise SystemExit(f"{target}: the binary names no minimum macOS version")


def wheel(version: str, target: str, files: dict[str, bytes], out: Path) -> Path:
    """Writes the `borer` wheel for one target and returns its path.

    Args:
        version: The release version, a plain PEP 440 release (`0.2.5`).
        target: The Rust target.
        files: The target's archive, from [`unpack`].
        out: The directory to write the wheel into.
    """
    exe = files[binary(target)]
    dist = f"borer-{version}"
    info = f"{dist}.dist-info"
    metadata = (
        "Metadata-Version: 2.4\n"
        f"Name: borer\nVersion: {version}\nSummary: {DESCRIPTION}\n"
        f"License-Expression: {LICENSE}\n"
        + "".join(f"License-File: {n}\n" for n in NOTICES)
        + f"Project-URL: Source, {REPO}\n"
        "Description-Content-Type: text/markdown\n\n" + ABOUT
    )
    tag = f"py3-none-{platform_tag(target, exe)}"
    entries = [
        (f"{dist}.data/scripts/{binary(target)}", exe, 0o755),
        *((f"{info}/licenses/{n}", files[n], 0o644) for n in NOTICES),
        (f"{info}/METADATA", metadata.encode(), 0o644),
        (
            f"{info}/WHEEL",
            f"Wheel-Version: 1.0\nGenerator: borer packages.py\n"
            f"Root-Is-Purelib: false\nTag: {tag}\n".encode(),
            0o644,
        ),
    ]
    record = ""
    for name, data, _ in entries:
        digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
        record += f"{name},sha256={digest},{len(data)}\n"
    entries.append((f"{info}/RECORD", f"{record}{info}/RECORD,,\n".encode(), 0o644))
    path = out / f"{dist}-{tag}.whl"
    out.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
        for name, data, mode in entries:
            entry = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            entry.external_attr = (0o100000 | mode) << 16
            z.writestr(entry, data, zipfile.ZIP_DEFLATED)
    return path


def wheels(assets: Path, out: Path) -> None:
    """Writes the `borer` wheel of every target into `out`."""
    version, archives = release(assets)
    if not re.fullmatch(r"\d+(\.\d+)*", version):
        raise SystemExit(f"version {version} is not a plain PEP 440 release; spell it for PyPI")
    for target in TARGETS:
        print(f"wrote {wheel(version, target, unpack(assets, *archives[target]), out)}")


def main() -> None:
    """Runs the command the arguments name."""
    args = sys.argv[1:]
    if len(args) in (2, 3) and args[0] == "manifests":
        manifests(Path(args[1]), Path(args[2]) if len(args) == 3 else ROOT / "packaging")
    elif len(args) == 3 and args[0] == "npm":
        npm(Path(args[1]), Path(args[2]))
    elif len(args) == 3 and args[0] == "wheels":
        wheels(Path(args[1]), Path(args[2]))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
