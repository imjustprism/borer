#!/usr/bin/env python3
"""The gate: every check that must pass before a commit, in one command.

    python scripts/gate.py          format, then verify everything
    python scripts/gate.py --check  verify only (what CI runs; formatting must already be clean,
                                    and a missing tool fails instead of skipping)
    python scripts/gate.py --fast   skip the slow tail (smoke, deny, doc, dogfood)

Steps, in order: the unpushed commits' messages (scripts/commits.py), cargo fmt, cargo clippy -D warnings, cargo test, cargo doc
with warnings as errors (private items included), cargo deny (offline subset),
the dogfood sweep over a real binary, the readability benchmark against its
baseline (scripts/readability.py), typos, ruff check + format, the type
library regenerated (scripts/typelib.py --check),
scripts/smoke.py, scripts/agent_eval.py. The first failure stops the run and the exit status is
non-zero. Tools that are not installed are reported and skipped, never
silently passed.

The sweep decompiles every function of the workspace's own server binary
built with the `corpus` profile (unoptimized throughout, the debug codegen
the sweep finds lifter bugs in), and requires well-formed text from all of
it. Smoke runs the optimized dev server against that same corpus binary. It also checks the determinism contract, by analyzing that
binary twice in one process and comparing every renderer's bytes; running
the commands twice from the shell instead costs six minutes, which
scripts/determinism.py still does when a cross-process check is wanted. The fixture cannot stand in for this: a defect that only a
real binary's shapes reach, such as a header line repeating an assert's
quotes, has reached a commit before.
"""

from __future__ import annotations

import contextlib
import os
import shutil
import subprocess
import sys
import tempfile
import time
from collections.abc import Iterator

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def step(
    name: str,
    cmd: list[str],
    env: dict[str, str] | None = None,
    optional_tool: str | None = None,
    strict: bool = False,
) -> bool:
    """Run one gate step from the repo root; return True when it passed.

    A step whose tool is not installed is skipped locally, and fails when
    `strict` (the `--check` form CI runs): there a missing tool is a broken
    setup, and a skip would pass a check nobody ran.
    """
    if optional_tool and shutil.which(optional_tool) is None:
        if strict:
            print(f"[FAIL] {name}: `{optional_tool}` is not installed", flush=True)
            return False
        print(f"[skip] {name}: `{optional_tool}` is not installed")
        return True
    t0 = time.time()
    print(f"[run ] {name}: {' '.join(cmd)}", flush=True)
    full_env = dict(os.environ)
    if env:
        full_env.update(env)
    proc = subprocess.run(cmd, cwd=ROOT, env=full_env, **below_normal())
    status = "ok  " if proc.returncode == 0 else "FAIL"
    print(f"[{status}] {name} ({time.time() - t0:.1f}s)", flush=True)
    return proc.returncode == 0


def below_normal() -> dict:
    """Popen arguments that start a step below normal priority.

    A step's builds and tests use every core for minutes; at normal priority
    they starved the desktop. Cargo, rustc and the borer processes a
    step starts inherit the class, so the whole tree yields to interactive
    work and still takes every idle cycle.
    """
    if sys.platform == "win32":
        return {"creationflags": subprocess.BELOW_NORMAL_PRIORITY_CLASS}
    return {"preexec_fn": lambda: os.nice(10)}


@contextlib.contextmanager
def machine_lock() -> Iterator[None]:
    """Hold the one gate slot this machine has, waiting while another gate runs.

    A gate builds with every core and runs tests that each analyze a
    37 MB binary; two of them side by side (parallel worktrees) once ran
    forty such processes and stalled the machine. The lock is a byte-range
    lock on a file in the temp directory, so a crashed gate releases it.
    """
    path = os.path.join(tempfile.gettempdir(), "borer-gate.lock")
    with open(path, "a+b") as f:
        if sys.platform == "win32":
            import msvcrt

            waited = False
            while True:
                try:
                    f.seek(0)
                    msvcrt.locking(f.fileno(), msvcrt.LK_NBLCK, 1)
                    break
                except OSError:
                    if not waited:
                        print(f"[wait] another gate holds {path}", flush=True)
                        waited = True
                    time.sleep(2)
            try:
                yield
            finally:
                f.seek(0)
                msvcrt.locking(f.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl

            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError:
                print(f"[wait] another gate holds {path}", flush=True)
                fcntl.flock(f, fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(f, fcntl.LOCK_UN)


def main(argv: list[str]) -> int:
    check_only = "--check" in argv
    fast = "--fast" in argv
    fmt = ["cargo", "fmt", "--all"] + (["--check"] if check_only else [])
    steps: list[tuple[str, list[str], dict[str, str] | None, str | None]] = [
        ("commits", [sys.executable, os.path.join("scripts", "commits.py")], None, None),
        ("fmt", fmt, None, None),
        (
            "clippy",
            ["cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings"],
            None,
            None,
        ),
        # The crackme the ground-truth test decompiles is an example; the
        # engine's own examples are left to clippy, which compiles them
        # (--all-targets), since linking them in the test build bought
        # nothing but three more executables.
        ("examples", ["cargo", "build", "-p", "borer-fixtures", "--examples"], None, None),
        ("test", ["cargo", "test", "--workspace", "--lib", "--bins", "--tests"], None, None),
        ("doctest", ["cargo", "test", "--workspace", "--doc"], None, None),
    ]
    if not fast:
        # Named by platform, not by presence: the build step before the
        # sweep makes it, so it does not exist yet when this list is built.
        exe = "borer.exe" if sys.platform == "win32" else "borer"
        # The build lands where cargo puts it: CARGO_TARGET_DIR when set.
        target = os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")
        server = os.path.join(target, "debug", exe)
        dogfood = os.path.join(target, "corpus", exe)
        steps += [
            # `cargo test` builds no binary in a tree that has not been
            # built before (a fresh worktree), and the dogfood sweep and
            # the smoke test both load one.
            ("build", ["cargo", "build", "-p", "borer"], None, None),
            # link.exe, not the rust-lld .cargo/config.toml names: the binary
            # the sweep reads stays linked as it always was.
            (
                "build corpus",
                ["cargo", "build", "-p", "borer", "--profile", "corpus"],
                {"CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER": "link.exe"},
                None,
            ),
            (
                "dogfood",
                [
                    "cargo",
                    "test",
                    "-p",
                    "borer-engine",
                    "--profile",
                    "sweep",
                    "--test",
                    "dogfood",
                    "--",
                    "--ignored",
                    # The text check runs in a step of its own below.
                    "--skip",
                    "the_text_agrees_with_the_emulator_on_every_block",
                    # Not a gate yet: running the final text of the
                    # small functions finds defects the passes after the
                    # lifter leave (two-register returns, sunk stores, slot
                    # and shift widths, calls typed as values). The
                    # unwritten-frame-read model (2026-10-15) took the
                    # corpus from 3381 differing inputs to 34, each now a
                    # distinct width/callee-modeling defect; it joins at 0.
                    "--skip",
                    "the_final_text_agrees_with_the_emulator_on_small_functions",
                    # Not a gate yet: the closure sweep lists the lines that
                    # read a value no line sets (the decompile answer marks
                    # them `// !unset:`); most pass a register to a callee
                    # whose signature lists more parameters than the caller
                    # sets (corpus census 2026-10-15: 3850 lines in 2955
                    # functions, 90% register arity r8-15/rax/rcx/rdx),
                    # which the whole-callgraph arity work owns.
                    "--skip",
                    "every_value_the_text_reads_is_set_or_an_input",
                    # The arm64 sweeps read their own binary
                    # (BORER_DOGFOOD_A64), which a fresh clone does not have:
                    # set it to an arm64 build and run them by name.
                    "--skip",
                    "the_arm64_lifter_agrees_with_the_emulator_on_every_block",
                    "--skip",
                    "decompile_every_arm64_function",
                    "--skip",
                    "the_arm64_text_agrees_with_the_machine_on_every_block",
                ],
                {"BORER_DOGFOOD": dogfood},
                None,
            ),
            # The text check alone: its replay takes 35 s by itself and 409 s
            # beside the sweeps above, which hold every core as it does.
            (
                "dogfood text",
                [
                    "cargo",
                    "test",
                    "-p",
                    "borer-engine",
                    "--profile",
                    "sweep",
                    "--test",
                    "dogfood",
                    "--",
                    "--ignored",
                    "--exact",
                    "the_text_agrees_with_the_emulator_on_every_block",
                ],
                {"BORER_DOGFOOD": dogfood},
                None,
            ),
        ]
        # The corpus is x86-64 only. A 32-bit binary with x87 math catches
        # what it cannot: an fxch fix landed green here and broke 63 blocks of
        # d3dx9_43, which every 32-bit Windows carries the like of in msvcrt.
        x86 = os.path.join(os.environ.get("SYSTEMROOT", r"C:\Windows"), "SysWOW64", "msvcrt.dll")
        if os.path.isfile(x86):
            steps.append(
                (
                    "dogfood x86",
                    [
                        "cargo",
                        "test",
                        "-p",
                        "borer-engine",
                        "--profile",
                        "sweep",
                        "--test",
                        "dogfood",
                        "--",
                        "--ignored",
                        "--skip",
                        "the_final_text_agrees_with_the_emulator_on_small_functions",
                        "--skip",
                        "every_value_the_text_reads_is_set_or_an_input",
                        "--skip",
                        "the_arm64_lifter_agrees_with_the_emulator_on_every_block",
                        "--skip",
                        "decompile_every_arm64_function",
                        "--skip",
                        "the_arm64_text_agrees_with_the_machine_on_every_block",
                    ],
                    {"BORER_DOGFOOD": x86},
                    None,
                )
            )
        else:
            print(f"[skip] dogfood x86: no {x86} on this machine")
        # The pseudo-C's noise and distance to source against the baseline
        # (scripts/readability.py): a rate that rose beyond its tolerance
        # fails. Inputs this machine lacks (the sqlite builds without
        # BORER_READABILITY_CORPUS, the Windows binaries elsewhere) are
        # skipped by the script itself.
        steps.append(
            (
                "readability",
                [
                    sys.executable,
                    os.path.join("scripts", "readability.py"),
                    "run",
                    server,
                    "--baseline",
                    os.path.join("scripts", "readability.tsv"),
                    "--quiet",
                ],
                None,
                None,
            )
        )
        steps += [
            (
                "doc",
                ["cargo", "doc", "--workspace", "--no-deps", "--document-private-items"],
                {"RUSTDOCFLAGS": "-D warnings"},
                None,
            ),
            ("deny", ["cargo", "deny", "check", "bans", "licenses", "sources"], None, "cargo-deny"),
        ]
    steps += [
        ("typos", ["typos"], None, "typos"),
        (
            "comments",
            [sys.executable, os.path.join("scripts", "strip_comments.py"), "--check"],
            None,
            None,
        ),
        ("ruff check", ["ruff", "check", "scripts"], None, "ruff"),
        ("ruff format", ["ruff", "format", "--check", "scripts"], None, "ruff"),
        (
            "typelib",
            [sys.executable, os.path.join("scripts", "typelib.py"), "--check"],
            None,
            None,
        ),
    ]
    if not fast:
        steps.append(
            (
                "smoke",
                [sys.executable, os.path.join("scripts", "smoke.py"), server, dogfood],
                None,
                None,
            )
        )
        # Seconds: the tasks replay on the crackme the examples step built.
        steps.append(
            (
                "agent eval",
                [sys.executable, os.path.join("scripts", "agent_eval.py"), server],
                None,
                None,
            )
        )
    for name, cmd, env, tool in steps:
        if not step(name, cmd, env, tool, strict=check_only):
            print(f"\nGATE FAILED at: {name}")
            return 1
    print("\nGATE OK")
    return 0


if __name__ == "__main__":
    with machine_lock():
        sys.exit(main(sys.argv[1:]))
