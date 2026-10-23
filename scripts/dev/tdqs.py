#!/usr/bin/env python3
"""Check borer's tool definitions against TDQS, the score Glama ranks MCP servers by.

    python scripts/dev/tdqs.py [--score] [borer.exe]

Runs `mcp-tdqs lint` (offline, no key) against the server's tools/list, and with
--score the full rubric on tdqs.dev in hosted mode, printing the report and its
URL. Each hosted score spends one of the account's daily calls. The key is
TDQS_API_KEY, read from the environment or from `.env.local` at the repository
root (KEY=VALUE lines, ignored by git). Not part of the gate: the score is a
model's judgment, so it varies run to run and needs the network.
"""

import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TDQS = "mcp-tdqs@0.2.0"
HOSTED = "https://tdqs.dev"


def local_env() -> dict[str, str]:
    """Return the environment with `.env.local` added, the process's own values winning."""
    env = dict(os.environ, BORER_NO_UPDATE_CHECK="1")
    path = ROOT / ".env.local"
    if path.is_file():
        for line in path.read_text(encoding="utf-8").splitlines():
            key, sep, value = line.partition("=")
            if sep and not key.lstrip().startswith("#") and value.strip():
                env.setdefault(key.strip(), value.strip())
    return env


def main() -> int:
    """Lint, and score when asked; return the first failing exit code."""
    args = sys.argv[1:]
    score = "--score" in args
    rest = [a for a in args if a != "--score"]
    name = "borer.exe" if os.name == "nt" else "borer"
    exe = Path(rest[0]) if rest else ROOT / "target" / "release" / name
    if not exe.is_file():
        sys.exit(f"no borer binary at {exe}: build it or pass its path")
    npx = shutil.which("npx")
    if npx is None:
        sys.exit("npx not found: install Node 22 or newer")
    env = local_env()
    server = ["--command", exe.resolve().as_posix(), "--server-name", "borer"]
    code = subprocess.call([npx, "-y", TDQS, "lint", *server, "--format", "text"], env=env)
    if code or not score:
        return code
    if not env.get("TDQS_API_KEY"):
        sys.exit("TDQS_API_KEY is not set: add it to .env.local")
    run = [npx, "-y", TDQS, "score", *server, "--hosted", HOSTED, "--format", "markdown"]
    return subprocess.call(run, env=env)


if __name__ == "__main__":
    sys.exit(main())
