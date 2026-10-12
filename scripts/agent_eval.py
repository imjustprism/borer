#!/usr/bin/env python3
"""Agent-task eval: replay fixture tasks against the real server and report what
each one costs an agent.

Usage: python scripts/agent_eval.py [path-to-borer.exe] [--update]

Each task is a question with a known answer on the crackme fixture
(crates/borer-fixtures/examples/crackme.rs, which `cargo build -p
borer-fixtures --examples` puts beside the server in examples/), the
shortest call sequence an agent has for it, and the fact the answers must
hold. Every call goes over stdio JSON-RPC as an agent's would; a resource is
read through the `query` tool, as an agent on a host without resources reads
it. A task starts with load_binary, as a fresh session does, except
`front_door`, which is what a session is handed before its first call (the
instructions, tools/list and prompts/list), and `raw_code`, which loads a
few bytes of hand-assembled x86-64 (RAW_CODE, written to a temporary file
counted as `<blob>`) at a stated base instead of the crackme.

A row per task: the calls, the bytes returned (tool text, error messages,
or the protocol JSON, with the fixture's path counted as `<bin>` and the
repository's as `<root>`, so the directory a checkout sits in does not move
the count) and whether the
fact was found. The rows are compared with the baseline in
scripts/agent_eval.tsv: a fact the baseline found and this run does not
fails the run (exit 1); calls and bytes are reported as deltas, never as a
failure, so a change that costs or saves bytes shows its effect without
blocking. --update rewrites the baseline. Two runs print the same bytes.
"""

from __future__ import annotations

import json
import os
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

from mcp import Client  # noqa: E402

BASELINE = os.path.join(ROOT, "scripts", "agent_eval.tsv")

# A call is (tool, arguments); a tool name starting with "@" is a protocol
# read instead: "@instructions" is the initialize answer's instructions,
# any other the method after the "@".
LOAD = ("load_binary", {"path": "{bin}"})

# Headerless x86-64 code: a call to a local function that returns 42, plus
# one, so it returns 43 (rax=0x2b) from 0x10000.
RAW_CODE = bytes.fromhex(
    "e806000000"  # call 0x1000b
    "4883c001"  # add rax, 1
    "c3"  # ret
    "cc"  # int3
    "b82a000000"  # mov eax, 42
    "c3"  # ret
)

# (task, the question it answers, calls, the fact the answers must hold)
TASKS = [
    (
        "front_door",
        "what a session is handed before its first call, and whether it starts at the triage",
        [("@instructions", {}), ("@tools/list", {}), ("@prompts/list", {})],
        "load_binary, then query borer://triage",
    ),
    (
        "orient",
        "what the file is and which function to read first",
        [LOAD, ("query", {"uri": "borer://triage"})],
        "crackme::check_serial",
    ),
    (
        "serial_constant",
        "the value the serial check compares its accumulator with",
        [LOAD, ("decompile", {"address": "crackme::check_serial"})],
        "0xdeadbeef",
    ),
    (
        "marker_user",
        "which function uses the marker string",
        [LOAD, ("find_function_by_string", {"filter": "BORER-CRACKME"})],
        "crackme::check_serial",
    ),
    (
        "caller",
        "who calls the serial check",
        [LOAD, ("xrefs", {"address": "crackme::check_serial"})],
        "crackme::main",
    ),
    (
        "emulate_serial",
        "what the serial check returns for the key 0",
        [LOAD, ("query", {"uri": "borer://emulate/crackme::check_serial,a1=0"})],
        "rax=0x0 ",
    ),
    (
        "emulate_grammar",
        "how to pass arguments to an emulation, asked of the bare template",
        [LOAD, ("query", {"uri": "borer://emulate"})],
        "aN=",
    ),
    (
        "uri_typo",
        "a mistyped resource, answered with the one meant",
        [LOAD, ("query", {"uri": "borer://emulat"})],
        "borer://emulate/{address}",
    ),
    (
        "name_typo",
        "a mistyped function name, answered with the one meant",
        [LOAD, ("decompile", {"address": "chk_serial"})],
        "crackme::check_serial",
    ),
    (
        "playbook",
        "the triage playbook read as a resource, by an agent that cannot get prompts",
        [LOAD, ("query", {"uri": "borer://playbook/triage"})],
        "cheapest first",
    ),
    (
        "call_args",
        "every call site of the serial check with the argument each passes",
        [LOAD, ("query", {"uri": "borer://calls/crackme::check_serial"})],
        "crackme::check_serial(",
    ),
    (
        "next_hint",
        "which resource the serial check's summary says to read next",
        [LOAD, ("function_summary", {"address": "crackme::check_serial"})],
        "# next: borer://solve/",
    ),
    (
        "resume",
        "where the session stands after a paged read: what it read, cut and paged",
        [
            LOAD,
            ("query", {"uri": "borer://help!offset=10!limit=5"}),
            ("query", {"uri": "borer://session"}),
        ],
        "capped paged  borer://help!offset=10!limit=5",
    ),
    (
        "raw_code",
        "what headerless code loaded at a stated base returns",
        [
            ("load_binary", {"path": "{blob}", "arch": "x64", "base": "0x10000"}),
            ("query", {"uri": "borer://emulate/0x10000"}),
        ],
        "rax=0x2b ",
    ),
]


def server_exe(args: list[str]) -> str:
    """The server to drive: the first argument, else the debug build."""
    if args:
        return os.path.abspath(args[0])
    target = os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")
    return os.path.join(target, "debug", "borer.exe" if sys.platform == "win32" else "borer")


def fixture(exe: str) -> str:
    """The crackme example built beside the server, or exit 2 naming the build."""
    examples = os.path.join(os.path.dirname(exe), "examples")
    for name in ("crackme.exe", "crackme"):
        path = os.path.join(examples, name)
        if os.path.isfile(path):
            return path
    raise SystemExit(f"no crackme in {examples}; run cargo build -p borer-fixtures --examples")


def answer(client: Client, tool: str, args: dict) -> str:
    """What one call hands the agent: the tool's text or error, or a protocol read."""
    if tool == "@instructions":
        return client.instructions
    if tool.startswith("@"):
        return json.dumps(client.call(tool[1:], args))
    reply = client.request("tools/call", {"name": tool, "arguments": args})
    if "error" in reply:
        return reply["error"].get("message", "")
    return "\n".join(c.get("text", "") for c in reply["result"].get("content", []))


def spellings(path: str) -> list[str]:
    """A path as the answers may spell it: as given, and with either separator,
    plain or escaped as a C string writes a backslash."""
    forms = {path, path.replace("\\", "/"), path.replace("/", "\\")}
    forms |= {f.replace("\\", "\\\\") for f in list(forms)}
    return sorted(forms, key=len, reverse=True)


def run(exe: str, binary: str) -> list[tuple[str, int, int, int]]:
    """Every task's (name, calls, bytes, found), in task order."""
    with tempfile.NamedTemporaryFile(prefix="borer-eval-", suffix=".bin", delete=False) as f:
        f.write(RAW_CODE)
        blob = f.name
    try:
        return run_tasks(exe, binary, blob)
    finally:
        os.remove(blob)


def run_tasks(exe: str, binary: str, blob: str) -> list[tuple[str, int, int, int]]:
    """Every task's row, the crackme at `binary` and RAW_CODE at `blob`."""
    paths = (
        [(f, "<bin>") for f in spellings(binary)]
        + [(f, "<blob>") for f in spellings(blob)]
        + [(f, "<root>") for f in spellings(ROOT)]
    )
    rows = []
    client = Client(exe)
    try:
        for name, _, calls, fact in TASKS:
            texts = []
            for tool, args in calls:
                filled = {
                    k: v.replace("{bin}", binary).replace("{blob}", blob) for k, v in args.items()
                }
                text = answer(client, tool, filled)
                for form, mark in paths:
                    text = text.replace(form, mark)
                texts.append(text)
            size = sum(len(t.encode("utf-8")) for t in texts)
            found = int(any(fact in t for t in texts))
            rows.append((name, len(calls), size, found))
    finally:
        client.close()
    return rows


def read_baseline() -> dict[str, tuple[int, int, int]]:
    """The baseline's rows by task; empty when the file is missing."""
    if not os.path.isfile(BASELINE):
        return {}
    out = {}
    with open(BASELINE, encoding="utf-8") as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            name, calls, size, found = line.rstrip("\n").split("\t")
            out[name] = (int(calls), int(size), int(found))
    return out


def table(rows: list[tuple[str, int, int, int]]) -> str:
    """The rows as the baseline file holds them."""
    body = "".join(f"{n}\t{c}\t{b}\t{f}\n" for n, c, b, f in rows)
    return "# task\tcalls\tbytes\tfound\n" + body


def delta(now: tuple[int, int, int], then: tuple[int, int, int] | None) -> str:
    """How a row differs from its baseline row, `=` when it does not."""
    if then is None:
        return "new"
    parts = []
    for what, a, b in (("calls", now[0], then[0]), ("bytes", now[1], then[1])):
        if a != b:
            parts.append(f"{what} {a - b:+d}")
    if now[2] != then[2]:
        parts.append("found" if now[2] else "LOST")
    return ", ".join(parts) or "="


def main(argv: list[str]) -> int:
    update = "--update" in argv
    args = [a for a in argv if a != "--update"]
    exe = server_exe(args)
    rows = run(exe, fixture(exe))
    if update:
        with open(BASELINE, "w", encoding="utf-8", newline="\n") as f:
            f.write(table(rows))
    base = read_baseline()
    calls = sum(r[1] for r in rows)
    size = sum(r[2] for r in rows)
    found = sum(r[3] for r in rows)
    print(f"# agent eval: {len(rows)} tasks, {found} found, {calls} calls, {size} bytes")
    print("# task\tcalls\tbytes\tfound\tvs baseline")
    lost = []
    for name, c, b, f in rows:
        then = base.get(name)
        print(f"{name}\t{c}\t{b}\t{f}\t{delta((c, b, f), then)}")
        if then is not None and then[2] and not f:
            lost.append(name)
    if lost:
        print(f"# lost a fact the baseline found: {', '.join(lost)}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
