#!/usr/bin/env python3
"""Write borer's package-manager packages from a release's archives.

    gh release download v0.2.5 -R imjustprism/borer -D dist
    python scripts/dev/packages.py manifests dist [OUT]

`manifests` writes the Homebrew formula and the Scoop manifest
(`OUT/homebrew/borer.rb`, `OUT/scoop/borer.json`, `OUT` being `packaging/`
by default) from the release's SHA256SUMS alone. Nothing is published: the
release workflow copies what this writes into the tap and bucket.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.root import ROOT  # noqa: E402

REPO = "https://github.com/imjustprism/borer"
"""Where the releases are published."""

DESCRIPTION = "Reverse-engineering engine for AI agents: MCP server and CLI"
"""The one-line summary every package carries."""

LICENSE = "AGPL-3.0-only"
"""borer's SPDX license expression."""

TARGETS = (
    "x86_64-pc-windows-msvc",
    "x86_64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "aarch64-apple-darwin",
)
"""The targets release.yml builds, each one archive."""


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
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"wrote {path}")


def main() -> None:
    """Runs the command the arguments name."""
    args = sys.argv[1:]
    if len(args) in (2, 3) and args[0] == "manifests":
        manifests(Path(args[1]), Path(args[2]) if len(args) == 3 else ROOT / "packaging")
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
