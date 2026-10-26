#!/usr/bin/env python3
"""The gate: every check that must pass before a commit, in one command.

    python scripts/gate.py             format, then verify everything
    python scripts/gate.py --check     verify only (what CI runs; formatting must already be clean,
                                       a missing tool fails instead of skipping, nothing is cached)
    python scripts/gate.py --fast      skip the slow tail (smoke, deny, doc, dogfood)
    python scripts/gate.py --no-cache  rerun every step, passed before or not

Helpers are grouped under this directory. `check` fails when a generated
table, the commit messages, or a comment drifts. `run` drives a built server.
`dev` installs the server a local client launches. `harness` is the shared
root path and MCP client. This file is the only command CI runs.

The run is ordered for the fastest answer. The unpushed commits' messages
(scripts/check/commits.py) and cargo fmt go first, alone, since fmt rewrites
what the rest reads. Every other step then starts as soon as the steps it
needs have passed, side by side with the rest: the checks that take
seconds (typos, the comment check, ruff check and format, the type library
(scripts/check/typelib.py --check), the size budgets (scripts/check/sizes.py),
the duplicate scan (jscpd) and cargo deny (offline subset)); cargo clippy -D
warnings and then cargo doc with warnings as errors (private items
included); the debug build, cargo test and the doctests; the corpus and
sweep builds, then the dogfood sweeps over real binaries; and, once the
builds they drive are done, the readability benchmark against its baseline
(scripts/run/readability.py), the golden diff of the `index` output
(scripts/run/golden.py), scripts/run/smoke.py and scripts/run/agent_eval.py.
Each step's output goes to `gate-logs/<step>.log` in the target directory;
the log prints a line as a step starts and ends, a step's `[skip]` lines,
and the whole output of the step that failed. The first failure stops the
run: the steps still running are killed, and the exit status is non-zero.
Tools that are not installed are reported and skipped, never silently
passed. A machine with fewer than eight cores (a CI runner) runs one step at
a time, in the order the plan lists them.

Steps that share a cargo profile directory wait for each other, as cargo
would make them (its lock is per profile directory). Side by side, clippy
and doc build in a target directory of their own (`<target>/clippy`), so
the lint pass overlaps the test build instead of queueing behind it.

A step that passed is remembered by the hash of what it reads: the contents
of the tracked and untracked files under its inputs, its command, its
environment and the toolchain. The same step over the same inputs is
`[cached]` and skipped, so a gate after a change to the scripts reruns no
Rust test, and one after a change to the engine reruns all of them. The
memory lives beside the build (`gate-cache.json` in the target directory);
`--check` and `--no-cache` ignore it, and a build step is never skipped,
since cargo answers an up-to-date one in a second anyway.

A linked worktree builds in its own `target-worktrees/<name>` directory
beside the main checkout unless `CARGO_TARGET_DIR` says otherwise
(`shared_target`): two checkouts of one workspace write the same artifact
names, so sharing the main `target` would link one checkout's crates into
the other. The machine lock below keeps two gates from building at once.
A worktree's first gate copies the dependencies another worktree's gate
built into its own directory (`seed`), so it builds only the workspace's
own crates.

The sweep decompiles every function of the workspace's own server binary
built with the `corpus` profile (unoptimized throughout, the debug codegen
the sweep finds lifter bugs in), and requires well-formed text from all of
it. Smoke runs the optimized dev server against that same corpus binary. It
also checks the determinism contract, by analyzing that binary twice in one
process and comparing every renderer's bytes; running the commands twice
from the shell instead costs six minutes, which scripts/run/determinism.py
still does when a cross-process check is wanted. The fixture cannot stand in
for this: a defect that only a real binary's shapes reach, such as a header
line repeating an assert's quotes, has reached a commit before.
"""

from __future__ import annotations

import concurrent.futures
import contextlib
import dataclasses
import hashlib
import io
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Iterator
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harness.root import ROOT  # noqa: E402

RUST = (
    "crates/",
    "Cargo.toml",
    "Cargo.lock",
    ".cargo/",
    "rust-toolchain.toml",
    "clippy.toml",
    "deny.toml",
    "rustfmt.toml",
)
"""What a Rust build reads: the crates and every file that configures them."""

SCRIPTS = ("scripts/", "ruff.toml")
"""What the Python checks read."""

EVERYTHING = ("",)
"""Every file in the checkout."""

WIDE_CORES = 8
"""Cores a machine needs for the gate to run its steps side by side."""


@dataclasses.dataclass(frozen=True)
class Step:
    """One gate step: a command and what decides whether it can be skipped."""

    name: str
    """What the log calls it."""
    cmd: list[str]
    """The command, run from the repo root."""
    env: dict[str, str] | None = None
    """Variables set for it on top of the gate's own."""
    tool: str | None = None
    """An executable that may not be installed; the step is skipped without it."""
    inputs: tuple[str, ...] | None = None
    """Path prefixes the step reads; `None` never caches it."""
    extra: tuple[str, ...] = ()
    """Files outside the checkout it reads, keyed by size and modification time."""
    needs: tuple[str, ...] = ()
    """Steps that must pass before it starts; one the plan left out is not waited for."""
    rewrites: bool = False
    """Whether it rewrites files it reads (fmt), so its key is taken after it runs."""


class Runner:
    """Runs steps as child processes, each with its output in a log file."""

    def __init__(self, logs: Path, strict: bool) -> None:
        self.logs = logs
        self.strict = strict
        self.procs: dict[str, subprocess.Popen] = {}
        self.lock = threading.Lock()
        self.stopped = False
        logs.mkdir(parents=True, exist_ok=True)

    def log(self, step: Step) -> Path:
        """The file a step's output goes to."""
        return self.logs / (step.name.replace(" ", "-") + ".log")

    def run(self, step: Step) -> bool:
        """Runs one step from the repo root and tells whether it passed.

        A step whose tool is not installed is skipped locally, and fails
        when `strict` (the `--check` form CI runs): there a missing tool is
        a broken setup, and a skip would pass a check nobody ran.
        """
        if step.tool and shutil.which(step.tool) is None:
            if self.strict:
                print(f"[FAIL] {step.name}: `{step.tool}` is not installed", flush=True)
                return False
            print(f"[skip] {step.name}: `{step.tool}` is not installed", flush=True)
            return True
        t0 = time.time()
        print(f"[run ] {step.name}: {' '.join(step.cmd)}", flush=True)
        env = dict(os.environ)
        env.update(step.env or {})
        with open(self.log(step), "wb") as out, self.lock:
            if self.stopped:
                return False
            proc = subprocess.Popen(
                step.cmd,
                cwd=ROOT,
                env=env,
                stdin=subprocess.DEVNULL,
                stdout=out,
                stderr=subprocess.STDOUT,
                **spawn_flags(),
            )
            self.procs[step.name] = proc
        code = proc.wait()
        with self.lock:
            del self.procs[step.name]
            if self.stopped:
                return False
        status = "ok  " if code == 0 else "FAIL"
        print(f"[{status}] {step.name} ({time.time() - t0:.1f}s)", flush=True)
        text = self.log(step).read_text(encoding="utf-8", errors="replace")
        for line in text.splitlines():
            if line.lstrip().startswith("[skip]"):
                print(f"       {line.strip()}", flush=True)
        if code != 0:
            print(text.rstrip("\n"), flush=True)
        return code == 0

    def stop(self) -> None:
        """Kills every step still running, with the processes each started."""
        with self.lock:
            self.stopped = True
            procs = list(self.procs.values())
        for proc in procs:
            if sys.platform == "win32":
                subprocess.run(
                    ["taskkill", "/T", "/F", "/PID", str(proc.pid)],
                    capture_output=True,
                )
            else:
                with contextlib.suppress(OSError):
                    os.killpg(proc.pid, signal.SIGKILL)


def spawn_flags() -> dict:
    """Popen arguments that start a step below normal priority, in a group
    of its own.

    A step's builds and tests use every core for minutes; at normal priority
    they starved the desktop. Cargo, rustc and the borer processes a
    step starts inherit the class, so the whole tree yields to interactive
    work and still takes every idle cycle. The group (a session on POSIX, a
    process tree Windows' taskkill follows) lets a failure elsewhere kill
    the step with everything it started.
    """
    if sys.platform == "win32":
        return {"creationflags": subprocess.BELOW_NORMAL_PRIORITY_CLASS}
    return {"preexec_fn": lambda: os.nice(10), "start_new_session": True}


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


def git(*args: str) -> str:
    """Runs git in the repo root and returns its output, empty when it fails."""
    proc = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    return proc.stdout.strip() if proc.returncode == 0 else ""


def shared_target() -> str | None:
    """A linked worktree's own target directory beside the main checkout's.

    A worktree's own `.git` is a file naming the common directory; the main
    checkout's is that directory itself. Each worktree builds into
    `target-worktrees/<name>` next to the main checkout, never into the main
    `target`: cargo hashes a workspace's own crates by their path inside the
    workspace, so two checkouts of the same workspace write the same artifact
    names, and one checkout's build would link the other's crates.
    """
    git_dir = git("rev-parse", "--absolute-git-dir")
    common = git("rev-parse", "--path-format=absolute", "--git-common-dir")
    if not git_dir or not common or Path(git_dir) == Path(common):
        return None
    return str(Path(common).parent / "target-worktrees" / ROOT.name)


SEEDED = ("debug", "corpus", "sweep", os.path.join("clippy", "debug"))
"""The profile directories, under a target directory, a fresh worktree seeds."""


def workspace_names() -> set[str]:
    """The names the workspace's own packages and targets give their build units."""
    proc = subprocess.run(
        ["cargo", "metadata", "--no-deps", "--format-version", "1", "--offline"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    names: set[str] = set()
    if proc.returncode != 0:
        return names
    for package in json.loads(proc.stdout)["packages"]:
        names.add(package["name"])
        for target in package["targets"]:
            names.add(target["name"])
            names.add(target["name"].replace("-", "_"))
    return names


def seed(target: str) -> None:
    """Copies the dependencies another worktree's gate built into this
    worktree's target directory, for each profile it has not built yet.

    A fresh worktree's first gate built every dependency four times over
    (debug, clippy, corpus, sweep) before its own crates. Another gate's
    directory (`gate-cache.json` marks one, and the machine lock keeps it
    still while this gate holds the lock) holds the same units under the
    same names: a unit's name hashes its package, version, features,
    profile and compiler, and cargo reruns a build script whose output names
    the directory it moved from. The workspace's own units are left behind:
    their freshness is judged by file times, and the other worktree's
    sources are not these. Cargo then builds only those, and any dependency
    the other directory lacks.
    """
    here = Path(target)
    if not here.parent.is_dir():
        return
    donors = [d for d in here.parent.iterdir() if d != here and (d / "gate-cache.json").is_file()]
    todo = [p for p in SEEDED if not (here / p / ".fingerprint").exists()]
    if not donors or not todo:
        return
    own = workspace_names()
    if not own:
        return
    for profile in todo:
        built = [d / profile for d in donors if (d / profile / ".fingerprint").is_dir()]
        if not built:
            continue
        src = max(built, key=lambda d: (d / ".fingerprint").stat().st_mtime)
        t0 = time.time()
        for sub in (".fingerprint", "build", "deps"):
            if not (src / sub).is_dir():
                continue
            (here / profile / sub).mkdir(parents=True, exist_ok=True)
            for entry in (src / sub).iterdir():
                unit = entry.name.split(".")[0].rpartition("-")[0]
                if not unit or unit in own or unit.removeprefix("lib") in own:
                    continue
                dest = here / profile / sub / entry.name
                if entry.is_dir():
                    shutil.copytree(entry, dest, dirs_exist_ok=True)
                else:
                    shutil.copy2(entry, dest)
        units = sum(1 for _ in (here / profile / ".fingerprint").iterdir())
        print(f"[seed] {profile}: {units} dependency units from {src} ({time.time() - t0:.1f}s)")


class Inputs:
    """Content hashes of the checkout's files, read once per gate run."""

    def __init__(self) -> None:
        listing = subprocess.run(
            ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
            cwd=ROOT,
            capture_output=True,
        ).stdout
        self.files = sorted({p for p in listing.decode("utf-8", "replace").split("\0") if p})
        self.hashes: dict[str, str] = {}
        self.toolchain = subprocess.run(
            ["rustc", "-V"], cwd=ROOT, capture_output=True, text=True
        ).stdout.strip()

    def of(self, path: str) -> str:
        """The hash of one file's contents, `-` when it is gone."""
        if path not in self.hashes:
            try:
                self.hashes[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            except OSError:
                self.hashes[path] = "-"
        return self.hashes[path]

    def key(self, step: Step) -> str | None:
        """What the step's last pass is remembered by, `None` when it is never cached."""
        if step.inputs is None:
            return None
        h = hashlib.sha256()
        h.update(json.dumps([step.cmd, step.env or {}, self.toolchain]).encode())
        for path in self.files:
            if path.startswith(step.inputs):
                h.update(path.encode() + b"\0" + self.of(path).encode() + b"\n")
        for path in step.extra:
            try:
                st = os.stat(path)
                h.update(f"{path}\0{st.st_size}\0{st.st_mtime_ns}\n".encode())
            except OSError:
                h.update(f"{path}\0-\n".encode())
        return h.hexdigest()


class Cache:
    """The steps that passed, by the hash of their inputs."""

    def __init__(self, path: str, enabled: bool) -> None:
        self.path = path
        self.enabled = enabled
        self.passed: dict[str, str] = {}
        if enabled:
            with contextlib.suppress(OSError, ValueError):
                self.passed = json.loads(Path(path).read_text(encoding="utf-8"))

    def hit(self, name: str, key: str | None) -> bool:
        """Whether the step passed before over these inputs."""
        return self.enabled and key is not None and self.passed.get(name) == key

    def record(self, name: str, key: str | None) -> None:
        """Remembers a pass and writes the memory out at once."""
        if not self.enabled or key is None:
            return
        self.passed[name] = key
        with contextlib.suppress(OSError):
            Path(self.path).parent.mkdir(parents=True, exist_ok=True)
            Path(self.path).write_text(json.dumps(self.passed, indent=1), encoding="utf-8")


# The dogfood sweeps that read a binary of another arch than the corpus.
OWN_BINARY_SWEEPS = (
    "the_arm64_lifter_agrees_with_the_emulator_on_every_block",
    "decompile_every_arm64_function",
    "the_arm64_text_agrees_with_the_machine_on_every_block",
    "the_arm32_lifter_agrees_with_the_emulator_on_every_block",
    "decompile_every_arm32_function",
    "the_arm32_text_agrees_with_the_machine_on_every_block",
)


def dogfood_skips(*names: str) -> list[str]:
    """`--skip NAME` for each sweep a dogfood step leaves out."""
    out: list[str] = []
    for n in names:
        out += ["--skip", n]
    return out


def plan(check_only: bool, fast: bool, target: str, wide: bool) -> tuple[list[Step], list[Step]]:
    """The gate's steps: the ones run alone first, then the rest, listed in
    an order that starts no step before the steps it needs. `wide` plans
    them to run side by side."""
    py = sys.executable
    fmt = ["cargo", "fmt", "--all"] + (["--check"] if check_only else [])
    first = [
        Step("commits", [py, os.path.join("scripts", "check", "commits.py")]),
        Step("fmt", fmt, inputs=RUST, rewrites=not check_only),
    ]
    # Side by side, clippy and doc check where the test build does not: in a
    # directory of their own they hold no lock the test build waits on, and
    # doc reads the dependencies' metadata clippy left there.
    lint = {"CARGO_TARGET_DIR": os.path.join(target, "clippy")} if wide else {}
    rest = [
        Step("typos", ["typos"], tool="typos", inputs=EVERYTHING),
        Step(
            "comments",
            [py, os.path.join("scripts", "check", "strip_comments.py"), "--check"],
            inputs=RUST + SCRIPTS,
        ),
        Step("ruff check", ["ruff", "check", "scripts"], tool="ruff", inputs=SCRIPTS),
        Step("ruff format", ["ruff", "format", "--check", "scripts"], tool="ruff", inputs=SCRIPTS),
        Step(
            "typelib",
            [py, os.path.join("scripts", "check", "typelib.py"), "--check"],
            inputs=RUST + SCRIPTS,
        ),
        Step("sizes", [py, os.path.join("scripts", "check", "sizes.py")], inputs=RUST + SCRIPTS),
        # Duplicated Rust over the threshold in .jscpd.json fails.
        Step(
            "dupes",
            [shutil.which("npx") or "npx", "--yes", "jscpd@4.0.5", "."],
            tool="npx",
            inputs=("crates/", ".jscpd.json"),
        ),
        Step(
            "clippy",
            ["cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings"],
            lint,
        ),
        # The crackme the ground-truth test decompiles is an example; the
        # engine's own examples are left to clippy, which compiles them
        # (--all-targets), since linking them in the test build bought
        # nothing but three more executables.
        Step("examples", ["cargo", "build", "-p", "borer-fixtures", "--examples"]),
        # `cargo test` builds no binary in a tree that has not been built
        # before (a fresh worktree), and the steps that drive the server
        # load one; built before the tests, they run while the tests do.
        Step("build", ["cargo", "build", "-p", "borer"], needs=("examples",)),
        Step(
            "test",
            ["cargo", "test", "--workspace", "--lib", "--bins", "--tests"],
            inputs=RUST,
            needs=("build",),
        ),
        # Beside the tests, not after them: cargo holds the profile's lock
        # while it builds, not while the test binaries run.
        Step("doctest", ["cargo", "test", "--workspace", "--doc"], inputs=RUST, needs=("build",)),
    ]
    if fast:
        return first, rest
    # Named by platform, not by presence: the build step before the sweep
    # makes it, so it does not exist yet when this list is built.
    exe = "borer.exe" if sys.platform == "win32" else "borer"
    server = os.path.join(target, "debug", exe)
    dogfood = os.path.join(target, "corpus", exe)
    sweep = ["cargo", "test", "-p", "borer-engine", "--profile", "sweep", "--test", "dogfood"]
    rest += [
        # link.exe, not the rust-lld .cargo/config.toml names: the binary
        # the sweep reads stays linked as it always was.
        Step(
            "build corpus",
            ["cargo", "build", "-p", "borer", "--profile", "corpus"],
            {"CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER": "link.exe"},
        ),
        Step("build sweep", [*sweep, "--no-run"]),
        Step(
            "dogfood",
            [*sweep, "--", "--ignored"]
            + dogfood_skips(
                # The text check runs in a step of its own below.
                "the_text_agrees_with_the_emulator_on_every_block",
                # Not a gate yet: running the final text of the small
                # functions finds defects the passes after the lifter leave
                # (two-register returns, sunk stores, slot and shift widths,
                # calls typed as values). The unwritten-frame-read model
                # (2026-10-15) took the corpus from 3381 differing inputs to
                # 34, each now a distinct width/callee-modeling defect; it
                # joins at 0.
                "the_final_text_agrees_with_the_emulator_on_small_functions",
                # Not a gate yet: the closure sweep lists the lines that read
                # a value no line sets; most pass a register to a callee whose
                # signature lists more parameters than the caller sets
                # (corpus census 2026-10-15: 3850 lines in 2955 functions,
                # 90% register arity r8-15/rax/rcx/rdx), which the
                # whole-callgraph arity work owns.
                "every_value_the_text_reads_is_set_or_an_input",
                # The arm sweeps read their own binaries (BORER_DOGFOOD_A64,
                # BORER_DOGFOOD_A32), which a fresh clone does not have: set
                # one to a build of that arch and run them by name.
                *OWN_BINARY_SWEEPS,
            ),
            {"BORER_DOGFOOD": dogfood},
            inputs=RUST,
            needs=("build corpus", "build sweep"),
        ),
        # The text check alone: its replay takes 35 s by itself and 409 s
        # beside the sweeps above, which hold every core as it does.
        Step(
            "dogfood text",
            [
                *sweep,
                "--",
                "--ignored",
                "--exact",
                "the_text_agrees_with_the_emulator_on_every_block",
            ],
            {"BORER_DOGFOOD": dogfood},
            inputs=RUST,
            needs=("dogfood",),
        ),
    ]
    # The corpus is x86-64 only. A 32-bit binary with x87 math catches what
    # it cannot: an fxch fix landed green here and broke 63 blocks of
    # d3dx9_43, which every 32-bit Windows carries the like of in msvcrt.
    x86 = os.path.join(os.environ.get("SYSTEMROOT", r"C:\Windows"), "SysWOW64", "msvcrt.dll")
    if os.path.isfile(x86):
        rest.append(
            Step(
                "dogfood x86",
                [*sweep, "--", "--ignored"]
                + dogfood_skips(
                    "the_final_text_agrees_with_the_emulator_on_small_functions",
                    "every_value_the_text_reads_is_set_or_an_input",
                    *OWN_BINARY_SWEEPS,
                ),
                {"BORER_DOGFOOD": x86},
                inputs=RUST,
                extra=(x86,),
                needs=("build sweep", "dogfood text"),
            )
        )
    else:
        print(f"[skip] dogfood x86: no {x86} on this machine")
    rest += [
        # The pseudo-C's noise and distance to source against the baseline
        # (scripts/run/readability.py): a rate that rose beyond its
        # tolerance fails. Inputs this machine lacks (the sqlite builds
        # without BORER_READABILITY_CORPUS, the Windows binaries elsewhere)
        # are skipped by the script itself.
        Step(
            "readability",
            [
                py,
                os.path.join("scripts", "run", "readability.py"),
                "run",
                server,
                "--baseline",
                os.path.join("scripts", "run", "readability.tsv"),
                "--quiet",
            ],
            inputs=RUST + SCRIPTS,
            needs=("build",),
        ),
        # Every function's `index` text over the notepad, msvcrt32 and
        # sqlite3 corpus against the hashes in scripts/run/golden.tsv
        # (scripts/run/golden.py): a change of output names the functions
        # it changed, and a commit that means to change them records the
        # new hashes with `golden.py record`. A missing corpus is skipped.
        Step(
            "golden",
            [py, os.path.join("scripts", "run", "golden.py"), "check", server, "--quiet"],
            inputs=RUST + SCRIPTS,
            needs=("build",),
        ),
        Step(
            "doc",
            ["cargo", "doc", "--workspace", "--no-deps", "--document-private-items"],
            {**lint, "RUSTDOCFLAGS": "-D warnings"},
            inputs=RUST,
            needs=("clippy",),
        ),
        Step(
            "deny",
            ["cargo", "deny", "check", "bans", "licenses", "sources"],
            tool="cargo-deny",
            inputs=("Cargo.toml", "Cargo.lock", "deny.toml", "crates/"),
        ),
        Step(
            "smoke",
            [py, os.path.join("scripts", "run", "smoke.py"), server, dogfood],
            inputs=RUST + SCRIPTS,
            needs=("build", "build corpus"),
        ),
        # Seconds: the tasks replay on the crackme the examples step built.
        Step(
            "agent eval",
            [py, os.path.join("scripts", "run", "agent_eval.py"), server],
            inputs=RUST + SCRIPTS,
            needs=("examples", "build"),
        ),
    ]
    return first, rest


def schedule(steps: list[Step], runner: Runner, cache: Cache, inputs: Inputs, wide: bool) -> str:
    """Runs `steps`, each once the steps it needs have passed, and returns
    the name of the first that failed, empty when none did.

    A step that passed before over the same inputs is `[cache]`d and counts
    as passed. `wide` starts every step that may start; otherwise one runs
    at a time, in the order of `steps`.
    An interrupt (Ctrl-C) kills the running steps before it returns: a step
    in its own process group does not see it.
    """
    planned = {s.name for s in steps}
    passed: set[str] = set()
    pending = list(steps)
    running: dict[concurrent.futures.Future, Step] = {}
    failed = ""
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(steps)) as pool:
        try:
            while not failed and (pending or running):
                for s in list(pending):
                    if running and not wide:
                        break
                    if any(n in planned and n not in passed for n in s.needs):
                        continue
                    pending.remove(s)
                    if cache.hit(s.name, inputs.key(s)):
                        print(f"[cache] {s.name}", flush=True)
                        passed.add(s.name)
                        continue
                    running[pool.submit(runner.run, s)] = s
                if not running:
                    break
                # A timeout, so that Windows delivers Ctrl-C to this wait.
                done, _ = concurrent.futures.wait(
                    running, timeout=1, return_when=concurrent.futures.FIRST_COMPLETED
                )
                for f in done:
                    s = running.pop(f)
                    if f.result():
                        passed.add(s.name)
                        cache.record(s.name, (Inputs() if s.rewrites else inputs).key(s))
                    elif not failed:
                        failed = s.name
                        runner.stop()
        except BaseException:
            runner.stop()
            raise
    if pending and not failed:
        raise SystemExit(f"gate.py: {pending[0].name} needs a step that never ran")
    return failed


def main(argv: list[str]) -> int:
    for stream in (sys.stdout, sys.stderr):
        if isinstance(stream, io.TextIOWrapper):
            stream.reconfigure(encoding="utf-8", errors="replace")
    check_only = "--check" in argv
    fast = "--fast" in argv
    use_cache = not check_only and "--no-cache" not in argv
    if not os.environ.get("CARGO_TARGET_DIR") and (shared := shared_target()):
        os.environ["CARGO_TARGET_DIR"] = shared
        print(f"[info] linked worktree: building in {shared}", flush=True)
        seed(shared)
    # The build lands where cargo puts it: CARGO_TARGET_DIR when set.
    target = os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")
    wide = (os.cpu_count() or 1) >= WIDE_CORES
    first, rest = plan(check_only, fast, target, wide)
    cache = Cache(os.path.join(target, "gate-cache.json"), use_cache)
    runner = Runner(Path(target) / "gate-logs", check_only)
    t0 = time.time()

    def finish(failed: str) -> int:
        took = time.time() - t0
        if not failed:
            print(f"\nGATE OK ({took:.0f}s)")
            return 0
        print(f"\nGATE FAILED at: {failed} ({took:.0f}s); every step's log is in {runner.logs}")
        return 1

    # fmt rewrites files, so each first step's inputs are read after the one
    # before it, and the rest's after them all.
    for s in first:
        if failed := schedule([s], runner, cache, Inputs(), wide):
            return finish(failed)
    return finish(schedule(rest, runner, cache, Inputs(), wide))


if __name__ == "__main__":
    with machine_lock():
        sys.exit(main(sys.argv[1:]))
