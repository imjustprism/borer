#!/usr/bin/env python3
"""Verify the GPUI desktop workspace in `app/` on Windows.

Runs `cargo deny`, `cargo fmt --check`, `cargo clippy --all-targets -- -D warnings`,
`cargo doc`, and `cargo test` inside `app/` using a dedicated `<target>/app` build
directory so its 1.98.1 artifacts never collide with the root workspace's 1.96.1 target.
On platforms other than Windows it prints a `[skip]` line and exits 0.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.root import ROOT  # noqa: E402


def main() -> int:
    check_strict = "--check" in sys.argv[1:]
    if sys.platform != "win32":
        print("[skip] app: Windows-only GPUI desktop workspace")
        return 0

    app_dir = ROOT / "app"
    if not (app_dir / "Cargo.toml").is_file():
        print(f"app workspace missing at {app_dir}", file=sys.stderr)
        return 1

    outer_target = os.environ.get("CARGO_TARGET_DIR") or str(ROOT / "target")
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = os.path.join(outer_target, "app")

    commands: list[tuple[list[str], dict[str, str]]] = []
    if shutil.which("cargo-deny") is not None or check_strict:
        commands.append((["cargo", "deny", "check", "bans", "licenses", "sources"], {}))
    else:
        print("[skip] app deny: cargo-deny not installed", flush=True)

    commands.extend(
        [
            (["cargo", "fmt", "--all", "--check"], {}),
            (["cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings"], {}),
            (
                ["cargo", "doc", "--workspace", "--no-deps", "--document-private-items"],
                {"RUSTDOCFLAGS": "-D warnings"},
            ),
            (["cargo", "test", "--workspace"], {}),
        ]
    )

    for cmd, extra_env in commands:
        print(f"+ (app) {' '.join(cmd)}", flush=True)
        res = subprocess.run(cmd, cwd=app_dir, env={**env, **extra_env})
        if res.returncode != 0:
            return res.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
