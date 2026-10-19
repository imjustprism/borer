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

The run is ordered for the fastest answer. The checks that take seconds go
first, side by side: the unpushed commits' messages (scripts/check/commits.py),
then cargo fmt, then typos, the comment check, ruff check and format and the
type library (scripts/check/typelib.py --check) together. The builds and the
long checks follow one at a time: cargo clippy -D warnings, cargo test,
the dogfood sweeps over real binaries, the readability benchmark against its
baseline (scripts/run/readability.py), the golden diff of the `index` output
(scripts/run/golden.py), cargo doc with warnings as errors
(private items included), cargo deny (offline subset), scripts/run/smoke.py
and scripts/run/agent_eval.py. The first failure stops the run and the exit
status is non-zero. Tools that are not installed are reported and skipped,
never silently passed.

A step that passed is remembered by the hash of what it reads: the contents
of the tracked and untracked files under its inputs, its command, its
environment and the toolchain. The same step over the same inputs is
`[cached]` and skipped, so a gate after a change to the scripts reruns no
Rust test, and one after a change to the engine reruns all of them. The
memory lives beside the build (`gate-cache.json` in the target directory);
`--check` and `--no-cache` ignore it, and a build step is never skipped,
since cargo answers an up-to-date one in a second anyway.

A linked worktree builds in the main checkout's target directory unless
`CARGO_TARGET_DIR` says otherwise: its dependencies are already built
there, so a fresh worktree compiles only the workspace's own crates. The
machine lock below keeps two gates from building there at once.

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
import json
import os
import shutil
import subprocess
import sys
import tempfile
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


def run(step: Step, strict: bool, capture: bool) -> tuple[bool, str]:
    """Run one step from the repo root.

    A step whose tool is not installed is skipped locally, and fails when
    `strict` (the `--check` form CI runs): there a missing tool is a broken
    setup, and a skip would pass a check nobody ran. With `capture` the
    output is returned instead of streamed, for steps run side by side.

    Returns whether it passed and what it printed when captured.
    """
    if step.tool and shutil.which(step.tool) is None:
        if strict:
            print(f"[FAIL] {step.name}: `{step.tool}` is not installed", flush=True)
            return False, ""
        print(f"[skip] {step.name}: `{step.tool}` is not installed", flush=True)
        return True, ""
    t0 = time.time()
    if not capture:
        print(f"[run ] {step.name}: {' '.join(step.cmd)}", flush=True)
    env = dict(os.environ)
    env.update(step.env or {})
    proc = subprocess.run(
        step.cmd,
        cwd=ROOT,
        env=env,
        capture_output=capture,
        text=capture,
        encoding="utf-8" if capture else None,
        errors="replace" if capture else None,
        **below_normal(),
    )
    status = "ok  " if proc.returncode == 0 else "FAIL"
    print(f"[{status}] {step.name} ({time.time() - t0:.1f}s)", flush=True)
    out = (proc.stdout or "") + (proc.stderr or "") if capture else ""
    return proc.returncode == 0, out


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


def dogfood_skips(*names: str) -> list[str]:
    """`--skip NAME` for each sweep a dogfood step leaves out."""
    out: list[str] = []
    for n in names:
        out += ["--skip", n]
    return out


def plan(check_only: bool, fast: bool, target: str) -> tuple[list[Step], list[Step], list[Step]]:
    """The gate's steps: the first one alone, the ones side by side, then the rest in order."""
    py = sys.executable
    fmt = ["cargo", "fmt", "--all"] + (["--check"] if check_only else [])
    first = [
        Step("commits", [py, os.path.join("scripts", "check", "commits.py")]),
        Step("fmt", fmt, inputs=RUST),
    ]
    side = [
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
    ]
    rest = [
        Step("clippy", ["cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings"]),
        # The crackme the ground-truth test decompiles is an example; the
        # engine's own examples are left to clippy, which compiles them
        # (--all-targets), since linking them in the test build bought
        # nothing but three more executables.
        Step("examples", ["cargo", "build", "-p", "borer-fixtures", "--examples"]),
        Step("test", ["cargo", "test", "--workspace", "--lib", "--bins", "--tests"], inputs=RUST),
        Step("doctest", ["cargo", "test", "--workspace", "--doc"], inputs=RUST),
    ]
    if fast:
        return first, side, rest
    # Named by platform, not by presence: the build step before the sweep
    # makes it, so it does not exist yet when this list is built.
    exe = "borer.exe" if sys.platform == "win32" else "borer"
    server = os.path.join(target, "debug", exe)
    dogfood = os.path.join(target, "corpus", exe)
    sweep = ["cargo", "test", "-p", "borer-engine", "--profile", "sweep", "--test", "dogfood", "--"]
    rest += [
        # `cargo test` builds no binary in a tree that has not been built
        # before (a fresh worktree), and the dogfood sweep and the smoke
        # test both load one.
        Step("build", ["cargo", "build", "-p", "borer"]),
        # link.exe, not the rust-lld .cargo/config.toml names: the binary
        # the sweep reads stays linked as it always was.
        Step(
            "build corpus",
            ["cargo", "build", "-p", "borer", "--profile", "corpus"],
            {"CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER": "link.exe"},
        ),
        Step(
            "dogfood",
            sweep
            + ["--ignored"]
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
                # a value no line sets (the decompile answer marks them
                # `// !unset:`); most pass a register to a callee whose
                # signature lists more parameters than the caller sets
                # (corpus census 2026-10-15: 3850 lines in 2955 functions,
                # 90% register arity r8-15/rax/rcx/rdx), which the
                # whole-callgraph arity work owns.
                "every_value_the_text_reads_is_set_or_an_input",
                # The arm64 sweeps read their own binary (BORER_DOGFOOD_A64),
                # which a fresh clone does not have: set it to an arm64
                # build and run them by name.
                "the_arm64_lifter_agrees_with_the_emulator_on_every_block",
                "decompile_every_arm64_function",
                "the_arm64_text_agrees_with_the_machine_on_every_block",
            ),
            {"BORER_DOGFOOD": dogfood},
            inputs=RUST,
        ),
        # The text check alone: its replay takes 35 s by itself and 409 s
        # beside the sweeps above, which hold every core as it does.
        Step(
            "dogfood text",
            sweep + ["--ignored", "--exact", "the_text_agrees_with_the_emulator_on_every_block"],
            {"BORER_DOGFOOD": dogfood},
            inputs=RUST,
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
                sweep
                + ["--ignored"]
                + dogfood_skips(
                    "the_final_text_agrees_with_the_emulator_on_small_functions",
                    "every_value_the_text_reads_is_set_or_an_input",
                    "the_arm64_lifter_agrees_with_the_emulator_on_every_block",
                    "decompile_every_arm64_function",
                    "the_arm64_text_agrees_with_the_machine_on_every_block",
                ),
                {"BORER_DOGFOOD": x86},
                inputs=RUST,
                extra=(x86,),
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
        ),
        Step(
            "doc",
            ["cargo", "doc", "--workspace", "--no-deps", "--document-private-items"],
            {"RUSTDOCFLAGS": "-D warnings"},
            inputs=RUST,
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
        ),
        # Seconds: the tasks replay on the crackme the examples step built.
        Step(
            "agent eval",
            [py, os.path.join("scripts", "run", "agent_eval.py"), server],
            inputs=RUST + SCRIPTS,
        ),
    ]
    return first, side, rest


def main(argv: list[str]) -> int:
    check_only = "--check" in argv
    fast = "--fast" in argv
    use_cache = not check_only and "--no-cache" not in argv
    if not os.environ.get("CARGO_TARGET_DIR") and (shared := shared_target()):
        os.environ["CARGO_TARGET_DIR"] = shared
        print(f"[info] linked worktree: building in {shared}", flush=True)
    # The build lands where cargo puts it: CARGO_TARGET_DIR when set.
    target = os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")
    first, side, rest = plan(check_only, fast, target)
    cache = Cache(os.path.join(target, "gate-cache.json"), use_cache)
    t0 = time.time()

    def finish(ok: bool, name: str = "") -> int:
        took = time.time() - t0
        if ok:
            print(f"\nGATE OK ({took:.0f}s)")
            return 0
        print(f"\nGATE FAILED at: {name} ({took:.0f}s)")
        return 1

    # fmt rewrites files, so the checks that read them start once it is done.
    for s in first:
        inputs = Inputs()
        key = inputs.key(s)
        if cache.hit(s.name, key):
            print(f"[cache] {s.name}", flush=True)
            continue
        ok, _ = run(s, check_only, capture=False)
        if not ok:
            return finish(False, s.name)
        cache.record(s.name, Inputs().key(s))
    inputs = Inputs()
    todo = [s for s in side if not cache.hit(s.name, inputs.key(s))]
    for s in side:
        if s not in todo:
            print(f"[cache] {s.name}", flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, len(todo))) as pool:
        results = list(pool.map(lambda s: (s, *run(s, check_only, capture=True)), todo))
    for s, ok, out in results:
        if not ok:
            sys.stdout.write(out)
            return finish(False, s.name)
        cache.record(s.name, inputs.key(s))
    for s in rest:
        key = inputs.key(s)
        if cache.hit(s.name, key):
            print(f"[cache] {s.name}", flush=True)
            continue
        ok, _ = run(s, check_only, capture=False)
        if not ok:
            return finish(False, s.name)
        cache.record(s.name, key)
    return finish(True)


if __name__ == "__main__":
    with machine_lock():
        sys.exit(main(sys.argv[1:]))
