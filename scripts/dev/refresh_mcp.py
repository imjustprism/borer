#!/usr/bin/env python3
"""Rebuild the MCP server and install it at the path .mcp.json pins.

    python scripts/dev/refresh_mcp.py

The server a client launches is a file on disk, and a client holds it open
for as long as the session lives, so a build cannot overwrite it while
anything is connected. It can be moved aside, which this does, so a refresh
works without closing the client. The `dist` profile is the shipped one:
release plus no unwinding tables and no symbols. Building into a side target
directory and copying the result keeps one stable path in .mcp.json that
never has to change, and leaves the main target directory alone.

Restart the MCP client afterwards: a running session keeps the binary it
launched, whatever the file on disk now holds.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.root import ROOT  # noqa: E402

BUILD_DIR = os.path.join(ROOT, "target", "mcpbuild")
BUILT = os.path.join(BUILD_DIR, "dist", "borer.exe")
INSTALLED = os.path.join(ROOT, "target", "mcp", "borer.exe")


def displace(path: str) -> bool:
    """Moves a running server out of the way so a new one can take its path.

    Windows refuses to overwrite the image of a running process but allows
    renaming it: the open handles a connected client holds follow the file,
    and the next launch reads whatever now sits at the pinned path. Stale
    copies are cleaned up on the following run, once nothing holds them.

    Args:
        path: The pinned server path.

    Returns:
        Whether the path was freed.
    """
    for n in range(64):
        stale = f"{path}.old{n}"
        if os.path.exists(stale):
            try:
                os.remove(stale)
            except OSError:
                continue
        try:
            os.replace(path, stale)
        except OSError:
            continue
        return True
    return False


def main() -> int:
    """Build the release server and copy it to the pinned path."""
    cmd = ["cargo", "build", "--profile", "dist", "--target-dir", BUILD_DIR]
    print(f"[run ] {' '.join(cmd)}", flush=True)
    if subprocess.run(cmd, cwd=ROOT).returncode != 0:
        return 1
    if not os.path.exists(BUILT):
        print(f"[FAIL] {BUILT} was not produced")
        return 1
    os.makedirs(os.path.dirname(INSTALLED), exist_ok=True)
    try:
        shutil.copy2(BUILT, INSTALLED)
    except PermissionError:
        if not displace(INSTALLED):
            print(f"[FAIL] {INSTALLED} is in use and could not be moved aside")
            return 1
        shutil.copy2(BUILT, INSTALLED)
        print("[note] a connected client held the old server; it was moved aside")
    head = subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True
    )
    stamp = head.stdout.strip() or "unknown"
    print(f"[ok  ] installed {INSTALLED} at {stamp}")
    print("restart the MCP client to pick it up")
    return 0


if __name__ == "__main__":
    sys.exit(main())
