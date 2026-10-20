#!/usr/bin/env python3
"""Check the messages of every commit not yet pushed against the commit convention.

    python scripts/check/commits.py [base]

A title is one line, `type: summary`, at most 72 characters of plain ASCII:
the type one of the listed words, no scope in parentheses, no period at
the end. (Lowercase is left to review: a proper noun such as Qt may start
a summary.) Below the title the only
thing allowed is a blank line and `Co-Authored-By:` trailers. The base is
the upstream of the current branch, or `origin/main`; with neither, there
is nothing pushed to compare with and the check passes, saying so.

Merge commits and commits a bot authored (Dependabot's, say) are skipped:
nobody on the project wrote those messages, and whoever merges a bot's
pull request writes the title that lands.
"""

from __future__ import annotations

import os
import subprocess
import sys

TYPES = ("add", "fix", "improve", "refactor", "perf", "docs", "test", "chore", "revert")
TITLE_MAX = 72


def git(*args: str) -> subprocess.CompletedProcess[str]:
    """Run git and return the finished process, output as UTF-8 text."""
    return subprocess.run(["git", *args], capture_output=True, text=True, encoding="utf-8")


def has_commit(ref: str) -> bool:
    """Whether ref names a commit this clone holds."""
    return git("cat-file", "-e", f"{ref}^{{commit}}").returncode == 0


def base_ref(argv: list[str]) -> str | None:
    """The commit the unpushed range starts after, or None when none is known.

    An argument wins, then BORER_COMMITS_BASE (CI sets it to the commit the
    push started from, since after a push origin/main is the pushed commit
    itself), then the branch's upstream, then origin/main. A force push's
    start is fetched when the clone lacks it, since nothing reachable holds
    it any more; when it cannot be had the check fails rather than pass
    commits it never read.
    """
    if argv:
        return argv[0]
    env = os.environ.get("BORER_COMMITS_BASE", "").strip()
    if env and env.strip("0"):
        if not has_commit(env):
            git("fetch", "--quiet", "--no-tags", "origin", env)
        if has_commit(env):
            return env
        sys.exit(f"commits: the push started from {env}, which cannot be fetched; pass a base")
    for ref in ("@{upstream}", "origin/main"):
        if git("rev-parse", "--verify", "--quiet", ref).returncode == 0:
            return ref
    return None


def problems(message: str) -> list[str]:
    """Every way one commit message breaks the format, empty when it keeps it."""
    lines = message.rstrip("\n").split("\n")
    title, rest = lines[0], lines[1:]
    found: list[str] = []
    kind, sep, summary = title.partition(": ")
    if not sep or kind not in TYPES:
        found.append(f"type is not one of {', '.join(TYPES)}")
    if "(" in kind:
        found.append("no scope in parentheses")
    if len(title) > TITLE_MAX:
        found.append(f"title is {len(title)} characters, the cap is {TITLE_MAX}")
    if not title.isascii():
        found.append("title is not plain ASCII")
    if title.endswith("."):
        found.append("title ends with a period")
    body = [line for line in rest if line.strip()]
    if any(not line.startswith("Co-Authored-By:") for line in body):
        found.append("a body below the title; only Co-Authored-By trailers may follow it")
    if body and rest and rest[0].strip():
        found.append("no blank line between the title and the trailer")
    return found


def main(argv: list[str]) -> int:
    base = base_ref(argv)
    if base is None:
        print("commits: no upstream or origin/main to compare with; nothing checked")
        return 0
    log = git("log", "--no-merges", "--format=%h%x1f%an%x1f%B%x1e", f"{base}..HEAD")
    if log.returncode != 0:
        print(log.stderr.strip())
        return 1
    bad = 0
    records = [r.strip("\n") for r in log.stdout.split("\x1e") if r.strip()]
    for record in records:
        short, author, message = record.split("\x1f", 2)
        if author.endswith("[bot]"):
            continue
        for problem in problems(message):
            bad += 1
            print(f"{short} {message.splitlines()[0]}\n    {problem}")
    print(f"commits: {len(records)} after {base}, {bad} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
