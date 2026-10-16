"""The checkout these helpers belong to.

A script may live in a subdirectory. The root is the directory that holds
both `Cargo.toml` and `crates`, not the script's parent.
"""

from __future__ import annotations

from pathlib import Path


def repo_root() -> Path:
    """Returns the borer checkout this file belongs to."""
    for parent in Path(__file__).resolve().parents:
        if (parent / "Cargo.toml").is_file() and (parent / "crates").is_dir():
            return parent
    raise SystemExit("borer repo root not found")


ROOT = repo_root()
