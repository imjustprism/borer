#!/usr/bin/env python3
"""Phase -1 termination test: drive the borer MCP server over stdio JSON-RPC.

Usage: python scripts/smoke.py [path-to-borer.exe] [path-to-binary-to-load]
Exits non-zero on any protocol or tool error. Default target binary: borer.exe
itself (a real PE, self-contained fixture).
"""

import atexit
import contextlib
import json
import os
import re
import subprocess
import sys
import tempfile
import threading

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXE = (
    os.path.abspath(sys.argv[1])
    if len(sys.argv) > 1
    else os.path.join(
        os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target"), "debug", "borer.exe"
    )
)
TARGET = os.path.abspath(sys.argv[2]) if len(sys.argv) > 2 else EXE

# The servers' stderr goes to a file, not a pipe nobody reads: a fault
# answers the call with its message alone, and the panic location the hook
# writes to stderr was lost with the pipe (a run under load once failed on
# "attempt to subtract with overflow" with no file or line to go on).
STDERR, STDERR_PATH = tempfile.mkstemp(prefix="borer-smoke-", suffix=".log")
STDERR_TAIL = 60
passed = False


def stderr_tail(lines=STDERR_TAIL):
    """Return the last `lines` lines the servers wrote to stderr."""
    with open(STDERR_PATH, encoding="utf-8", errors="replace") as f:
        return "".join(f.readlines()[-lines:])


def dump_stderr_on_failure():
    """Print the servers' stderr tail when the smoke test did not pass, then
    remove the file."""
    tail = "" if passed else stderr_tail()
    if tail:
        print(f"--- last {STDERR_TAIL} lines of the server's stderr ---", file=sys.stderr)
        print(tail, end="" if tail.endswith("\n") else "\n", file=sys.stderr)
    os.close(STDERR)
    with contextlib.suppress(OSError):
        os.remove(STDERR_PATH)


atexit.register(dump_stderr_on_failure)

proc = subprocess.Popen(
    [EXE],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=STDERR,
    text=True,
    encoding="utf-8",
)
# Hard watchdog against a hung server, not a performance budget: the diff,
# difffn and migrate resources each walk every function of the binary under
# test, which is borer itself, so their cost grows with every commit. At 60s
# this killed a healthy run whenever the gate's earlier steps had loaded the
# machine; at 300s the name-table job on the debug build under load did.
# A failed check exits mid-session; the server must not outlive it.
atexit.register(proc.kill)
watchdog = threading.Timer(900, proc.kill)
watchdog.daemon = True
watchdog.start()

_next_id = 0


def send(method, params=None, notify=False):
    global _next_id
    msg = {"jsonrpc": "2.0", "method": method}
    if params is not None:
        msg["params"] = params
    rid = None
    if not notify:
        _next_id += 1
        msg["id"] = _next_id
        rid = _next_id
    proc.stdin.write(json.dumps(msg) + "\n")
    proc.stdin.flush()
    return rid


def wait_for(rid, allow_error=False):
    while True:
        line = proc.stdout.readline()
        if not line:
            raise SystemExit("server closed stdout; its stderr follows")
        msg = json.loads(line)
        if msg.get("id") == rid:
            if "error" in msg and not allow_error:
                raise SystemExit(f"rpc error: {msg['error']}")
            return msg.get("result") if "result" in msg else msg


def call_tool(name, args):
    res = wait_for(send("tools/call", {"name": name, "arguments": args}))
    if res.get("isError"):
        raise SystemExit(f"tool {name} failed: {res}")
    return "\n".join(c.get("text", "") for c in res.get("content", []))


# 1. initialize
init = wait_for(
    send(
        "initialize",
        {
            "protocolVersion": "2025-06-18",
            "capabilities": {},
            "clientInfo": {"name": "borer-smoke", "version": "0.0.0"},
        },
    )
)
print(f"initialized: server={init['serverInfo']['name']} v{init['serverInfo']['version']}")
send("notifications/initialized", notify=True)

# 2. tools/list
tools = wait_for(send("tools/list", {}))
names = [t["name"] for t in tools["tools"]]
print("tools:", ", ".join(sorted(names)))
for expected in (
    "load_binary",
    "binary_info",
    "disassemble",
    "disassemble_function",
    "hexdump",
    "strings",
    "symbols",
    "read",
    "entropy",
    "find_crypto_constants",
    "function_summary",
    "function_strings",
    "find_function_by_string",
    "decompile",
    "decompile_batch",
    "query",
    "script",
):
    assert expected in names, f"missing tool: {expected}"

# 2b. prompts/list (newest-protocol surface) and tool annotations
prompts = wait_for(send("prompts/list", {}))
pnames = sorted(p["name"] for p in prompts["prompts"])
assert pnames == ["explain_function", "find_check", "protocol", "triage"], pnames
got = wait_for(send("prompts/get", {"name": "find_check", "arguments": {"what": "serial"}}))
assert "serial" in got["messages"][0]["content"]["text"], got
ann = {t["name"]: t.get("annotations") or {} for t in tools["tools"]}
assert ann["decompile"].get("readOnlyHint") is True, ann["decompile"]
assert ann["load_binary"].get("readOnlyHint") is False, ann["load_binary"]
print("prompts:", ", ".join(pnames))

# 3. load + info
info = call_tool("load_binary", {"path": os.path.abspath(TARGET), "pdb": False})
withpdb = call_tool("load_binary", {"path": os.path.abspath(TARGET)})
assert "pdb:" in withpdb and "symbols applied" in withpdb, withpdb.splitlines()[:6]
print("companion pdb OK: applied when not refused")
info = call_tool("load_binary", {"path": os.path.abspath(TARGET), "pdb": False})
print("--- binary_info (first lines) ---")
print("\n".join(info.splitlines()[:6]))
m = re.search(r"entry: (0x[0-9a-f]+)", info)
if not m:
    raise SystemExit("no entry point found in summary:\n" + info[:500])

# 4. disassemble at the entry point
dis = call_tool("disassemble", {"address": m.group(1), "count": 8})
print("--- disassemble @ entry ---")
print("\n".join(dis.splitlines()[:5]) + "\n...")
assert "0x" in dis, "no addresses in disassembly output"

# 5. hexdump
hd = call_tool("hexdump", {"address": m.group(1), "length": 32})
assert "|" in hd, "hexdump ascii column missing"
print("--- hexdump @ entry (first line) ---")
print(hd.splitlines()[0])

# 6. strings (server-side filter)
st = call_tool("strings", {"min_length": 6, "filter": "borer"})
print("--- strings(filter=borer) ---")
print("\n".join(st.splitlines()[:3]))

# 6b. analysis tools: functions / function / xrefs / callgraph / cfg
fns = call_tool("functions", {"limit": 5})
print("--- functions ---")
print("\n".join(fns.splitlines()[:3]))
assert "functions" in fns.splitlines()[0], "functions header missing"

fn = call_tool("function", {"address": m.group(1)})
assert "blocks:" in fn and "entry:" in fn, f"function detail malformed:\n{fn[:300]}"
print(f"--- function @ entry: {fn.splitlines()[0]}")

xr = call_tool("xrefs", {"address": m.group(1)})
assert "xrefs to" in xr, f"xrefs malformed:\n{xr[:200]}"

cg = call_tool("callgraph", {"address": m.group(1), "max_nodes": 10})
assert "graph TD" in cg and " --> " in cg, f"callgraph malformed:\n{cg[:200]}"
print("--- callgraph (first lines) ---")
print("\n".join(cg.splitlines()[:3]))

cf = call_tool("cfg", {"address": m.group(1)})
assert "graph TD" in cf, f"cfg malformed:\n{cf[:200]}"

# 6c2. decompile the entry function
dec = call_tool("decompile", {"address": m.group(1)})
assert "return" in dec or "=" in dec or "/*" in dec, f"decompile malformed:\n{dec[:300]}"
assert dec.count("\n") >= 2, f"decompile too short:\n{dec[:300]}"
assert "// checked vs binary: statements as emitted, " in dec, (
    f"decompile lacks the line saying what was checked:\n{dec[:300]}"
)
print("--- decompile @ entry (first lines) ---")
print("\n".join(dec.splitlines()[:5]))

# 6c1. agent-native tools: summary / strings-by-function / typed reads / entropy / crypto
summary = call_tool("function_summary", {"address": m.group(1)})
assert "callees:" in summary, f"summary malformed:\n{summary[:300]}"
print("--- function_summary @ entry ---")
print("\n".join(summary.splitlines()[:4]))

fstr = call_tool("function_strings", {"address": m.group(1)})
assert fstr.startswith("#"), f"function_strings malformed:\n{fstr[:200]}"

byname = call_tool("find_function_by_string", {"filter": "borer", "limit": 5})
assert byname.startswith("#"), f"find_function_by_string malformed:\n{byname[:200]}"
print("--- find_function_by_string('borer'): " + byname.splitlines()[0])

rd = call_tool("read", {"address": m.group(1), "kind": "u8", "count": 4})
assert rd.count("\n") >= 4, f"read returned too few rows:\n{rd}"
rd_str = call_tool("read", {"address": m.group(1), "kind": "cstr"})
assert rd_str.startswith("#"), rd_str

ent = call_tool("entropy", {"window": 4096, "threshold": 7.5})
assert "high-entropy regions" in ent, ent[:200]

cry = call_tool("find_crypto_constants", {})
assert "crypto/hash constant hits" in cry, cry[:200]
print("--- entropy: " + ent.splitlines()[0])
print("--- crypto:  " + cry.splitlines()[0])

dfn = call_tool("disassemble_function", {"address": m.group(1), "max_instrs": 50})
assert "instructions" in dfn.splitlines()[0] and "0x" in dfn, (
    f"disassemble_function malformed:\n{dfn[:300]}"
)

wide = call_tool("strings", {"encoding": "utf16", "min_length": 6, "limit": 5})
assert wide.startswith("# showing"), wide[:200]
paged = call_tool("symbols", {"limit": 3, "offset": 1})
assert paged.startswith("# showing"), paged[:200]
only = call_tool("functions", {"count_only": True})
assert only.count("\n") == 1 and only.startswith("# ") and "functions" in only, only
only_s = call_tool("strings", {"count_only": True, "filter": "borer"})
assert only_s.count("\n") == 1, only_s
with_bytes = call_tool("disassemble", {"address": m.group(1), "count": 2, "bytes": True})
assert len(with_bytes.splitlines()[1]) > len(dis.splitlines()[1]), (with_bytes, dis)

# 6c. search
txt = call_tool("search", {"query": "borer", "kind": "text"})
n_txt = int(txt.splitlines()[0].split()[1])
assert n_txt >= 1, f"text search found nothing:\n{txt[:200]}"
aob = call_tool("search", {"query": "48 83 ec 28", "kind": "bytes"})
n_aob = int(aob.splitlines()[0].split()[1])
print(f"--- search: text 'borer' -> {n_txt} hits, aob -> {n_aob} hits")

# 6d. annotations: dry-run, apply, save, clobber, load, restore
dry = call_tool("set_name", {"address": m.group(1), "name": "entry_thunk"})
assert "dry-run" in dry, dry
ren = call_tool("set_name", {"address": m.group(1), "name": "entry_thunk", "dry_run": False})
assert "renamed" in ren, ren
fnamed = call_tool("functions", {"filter": "entry_thunk"})
assert "entry_thunk" in fnamed, "renamed function not visible in functions list"
# names resolve wherever an address is accepted
byname_xr = call_tool("xrefs", {"address": "entry_thunk"})
assert "xrefs to" in byname_xr, byname_xr[:200]
byname_dec = call_tool("decompile", {"address": "entry_thunk"})
assert "entry_thunk" in byname_dec.splitlines()[0], byname_dec[:200]
bad_name = wait_for(
    send("tools/call", {"name": "decompile", "arguments": {"address": "no_such_symbol_xyz"}}),
    allow_error=True,
)
assert "error" in bad_name or bad_name.get("isError"), (
    f"unknown name should error: {str(bad_name)[:200]}"
)

import tempfile

proj = os.path.join(tempfile.gettempdir(), "borer_smoke_project.json")
sv = call_tool("save_project", {"path": proj})
assert "saved" in sv, sv
call_tool("set_name", {"address": m.group(1), "name": "clobbered", "dry_run": False})
ld = call_tool("load_project", {"path": proj})
assert "loaded" in ld, ld
fn2 = call_tool("functions", {"filter": "entry_thunk"})
assert "entry_thunk" in fn2, "project load did not restore names"
cm = call_tool("set_comment", {"address": m.group(1), "comment": "entry point", "dry_run": False})
assert "comment set" in cm, cm
an = call_tool("annotations", {})
assert "name: entry_thunk" in an and "found: entry point" in an, an
batch = call_tool("decompile_batch", {"filter": "entry_thunk", "max_functions": 1})
assert "==== entry_thunk" in batch, batch[:300]
# A comment opening with ? is an open question, and the ledger has to keep
# the two apart or it is just a pile of text.
call_tool("set_comment", {"address": m.group(1), "comment": "? a guess", "dry_run": False})
led = wait_for(send("resources/read", {"uri": "borer://annotations"}))["contents"][0]["text"]
assert "open question" in led, led[:300]
assert "open:  a guess" in led, led[:300]
print("--- annotations round-trip OK (dry-run, rename, save/load, open questions)")

# 7. error path: unmapped address must return a clean error, not a crash
bad = wait_for(
    send("tools/call", {"name": "disassemble", "arguments": {"address": "0x414141414141"}}),
    allow_error=True,
)
assert "error" in bad or bad.get("isError"), f"unmapped address should error, got: {str(bad)[:200]}"
print("error path OK (unmapped address -> clean error)")

# 7b. hostile parameters: a zero count and an unknown kind are refused, not guessed
zero = wait_for(
    send("tools/call", {"name": "functions", "arguments": {"limit": 0}}),
    allow_error=True,
)
assert "error" in zero or zero.get("isError"), f"limit=0 should error, got: {str(zero)[:200]}"
banana = wait_for(
    send("tools/call", {"name": "symbols", "arguments": {"kind": "banana"}}),
    allow_error=True,
)
assert "error" in banana or banana.get("isError"), (
    f"unknown kind should error, got: {str(banana)[:200]}"
)
empty = wait_for(
    send("tools/call", {"name": "search", "arguments": {"query": "", "kind": "text"}}),
    allow_error=True,
)
assert "error" in empty or empty.get("isError"), (
    f"empty query should error, got: {str(empty)[:200]}"
)
print("hostile parameters OK (limit=0, kind=banana, query='' -> clean errors)")

# 8. the server survived the error: another call still answers
after = call_tool("binary_info", {})
assert "format:" in after, "server did not survive an erroring tool call"
print("post-error call OK (server alive)")

# 9. protocol surface: the tool list stays lean (every session pays for it:
#    40 tools at about 650 bytes each, the live family, query and script
#    included), discover answers, resources and argument completion work
raw_tools = json.dumps(tools)
assert len(raw_tools) < 26000, (
    f"tools/list is {len(raw_tools)} bytes; keep descriptions and schemas lean"
)
for t in tools["tools"]:
    assert "$schema" not in t["inputSchema"], f"schema noise in {t['name']}"
    for prop in t["inputSchema"].get("properties", {}).values():
        assert "format" not in prop and "minimum" not in prop, f"schema noise in {t['name']}"
res = wait_for(send("resources/list", {}))
uris = sorted(r["uri"] for r in res["resources"])
assert uris == [
    "borer://annotations",
    "borer://antianalysis",
    "borer://asserts",
    "borer://attrs",
    "borer://capabilities",
    "borer://checks",
    "borer://classes",
    "borer://dynimports",
    "borer://enums",
    "borer://fingerprint",
    "borer://flat",
    "borer://hashes",
    "borer://hidden",
    "borer://index",
    "borer://info",
    "borer://map",
    "borer://messages",
    "borer://packs",
    "borer://ports",
    "borer://protection",
    "borer://qt",
    "borer://singletons",
    "borer://sources",
    "borer://stackstrings",
    "borer://triage",
    "borer://vm",
], uris
flat = wait_for(send("resources/read", {"uri": "borer://flat"}))["contents"][0]["text"]
assert flat.startswith("# "), flat[:200]
print("flat resource OK:", flat.splitlines()[0])

triage = wait_for(send("resources/read", {"uri": "borer://triage"}))["contents"][0]["text"]
assert triage.startswith("# triage:"), triage[:200]
for want in ("# protection:", "# capabilities:", "# next:"):
    assert want in triage, (want, triage[:400])
print("triage resource OK:", triage.splitlines()[1])

enums = wait_for(send("resources/read", {"uri": "borer://enums"}))["contents"][0]["text"]
assert enums.startswith("# ") and "name tables" in enums, enums[:200]
print("enums resource OK:", enums.splitlines()[0])
classes = wait_for(send("resources/read", {"uri": "borer://classes"}))["contents"][0]["text"]
assert "four-character code" in classes, classes[:200]
print("classes resource OK:", classes.splitlines()[0])
singletons = wait_for(send("resources/read", {"uri": "borer://singletons"}))["contents"][0]["text"]
assert "singletons" in singletons.splitlines()[0], singletons[:200]
assert "kind\tslot\tinstance\tclass" in singletons, singletons[:200]
print("singletons resource OK:", singletons.splitlines()[0])
sources = wait_for(send("resources/read", {"uri": "borer://sources"}))["contents"][0]["text"]
assert "directory" in sources, sources[:200]
print("sources resource OK:", sources.splitlines()[0])
asserts = wait_for(send("resources/read", {"uri": "borer://asserts"}))["contents"][0]["text"]
assert "field" in asserts, asserts[:200]
print("asserts resource OK:", asserts.splitlines()[0])
protection = wait_for(send("resources/read", {"uri": "borer://protection"}))["contents"][0]["text"]
assert protection.startswith("# "), protection[:200]
print("protection resource OK:", protection.splitlines()[0])
aa = wait_for(send("resources/read", {"uri": "borer://antianalysis"}))["contents"][0]["text"]
assert aa.startswith("# "), aa[:200]
print("antianalysis resource OK:", aa.splitlines()[0])
checks = wait_for(send("resources/read", {"uri": "borer://checks"}))["contents"][0]["text"]
assert checks.startswith("# "), checks[:200]
print("checks resource OK:", checks.splitlines()[0])
dyn = wait_for(send("resources/read", {"uri": "borer://dynimports"}))["contents"][0]["text"]
assert dyn.startswith("# "), dyn[:200]
print("dynimports resource OK:", dyn.splitlines()[0])
vm = wait_for(send("resources/read", {"uri": "borer://vm"}))["contents"][0]["text"]
assert "dispatch loop" in vm, vm[:200]
print("vm resource OK:", vm.splitlines()[0])
ss = wait_for(send("resources/read", {"uri": "borer://stackstrings"}))["contents"][0]["text"]
assert "stack string" in ss, ss[:200]
print("stackstrings resource OK:", ss.splitlines()[0])
bad = wait_for(send("tools/call", {"name": "functions", "arguments": {"nosuchfield": 5}}))
bad_text = json.dumps(bad)
assert "nosuchfield" in bad_text and ("unknown field" in bad_text or "isError" in bad_text), (
    bad_text[:300]
)
print("unknown parameter rejected OK")
hid = wait_for(send("resources/read", {"uri": "borer://hidden"}))["contents"][0]["text"]
# "1 generated string" or "N generated strings": the count depends on the binary
assert hid.startswith("# ") and "generated string" in hid, hid[:200]
print("hidden resource OK:", hid.splitlines()[0])
orc = wait_for(send("resources/read", {"uri": "borer://oracle/entry_thunk"}))["contents"][0]["text"]
assert orc.startswith("# "), orc[:200]
print("oracle resource OK:", orc.splitlines()[0])
packs = wait_for(send("resources/read", {"uri": "borer://packs"}))["contents"][0]["text"]
assert "pack\tversion\tfile\tloads\tmatch" in packs, packs[:300]
print("packs resource OK:", packs.splitlines()[0])
caps = wait_for(send("resources/read", {"uri": "borer://capabilities"}))["contents"][0]["text"]
assert "capabilities" in caps, caps[:200]
print("capabilities resource OK:", caps.splitlines()[0])
tmpl = wait_for(send("resources/templates/list", {}))
assert any(t["uriTemplate"] == "borer://decompile/{address}" for t in tmpl["resourceTemplates"]), (
    tmpl
)
rd = wait_for(send("resources/read", {"uri": "borer://info"}))
assert "format:" in rd["contents"][0]["text"], rd
rd2 = wait_for(send("resources/read", {"uri": "borer://decompile/entry_thunk"}))
assert "signature:" in rd2["contents"][0]["text"], rd2
fields = wait_for(send("resources/read", {"uri": "borer://fields/entry_thunk"}))["contents"][0][
    "text"
]
assert fields.startswith("# fields dereferenced by"), fields[:200]
assert "base\toffset\twidths\tdir" in fields, fields[:200]
assert any(t["uriTemplate"] == "borer://fields/{address}" for t in tmpl["resourceTemplates"]), tmpl
print("fields resource OK:", fields.splitlines()[0][:70])
emu = wait_for(send("resources/read", {"uri": "borer://emulate/entry_thunk"}))["contents"][0][
    "text"
]
assert emu.startswith("# ran"), emu[:200]
print("emulate resource OK:", emu.splitlines()[0][:70])
assert any(t["uriTemplate"] == "borer://devirt/{address}" for t in tmpl["resourceTemplates"]), tmpl
dev = wait_for(send("resources/read", {"uri": "borer://devirt/entry_thunk"}))["contents"][0]["text"]
assert dev.startswith("# "), dev[:200]
print("devirt resource OK:", dev.splitlines()[0][:70])
assert any(t["uriTemplate"] == "borer://unpack/{address}" for t in tmpl["resourceTemplates"]), tmpl
unp = wait_for(send("resources/read", {"uri": "borer://unpack/entry_thunk"}))["contents"][0]["text"]
assert "emulated unpacking" in unp, unp[:200]
print("unpack resource OK:", unp.splitlines()[0][:70])
assert any(t["uriTemplate"] == "borer://diff/{path}" for t in tmpl["resourceTemplates"]), tmpl
dif = wait_for(
    send("resources/read", {"uri": "borer://diff/" + os.path.abspath(TARGET).replace("\\", "/")})
)["contents"][0]["text"]
assert "identical" in dif, dif[:200]
print("diff resource OK:", dif.splitlines()[-1][:70])
assert any(
    t["uriTemplate"] == "borer://difffn/{function}/{path}" for t in tmpl["resourceTemplates"]
), tmpl
difffn = wait_for(
    send(
        "resources/read",
        {"uri": "borer://difffn/entry_thunk/" + os.path.abspath(TARGET).replace("\\", "/")},
    )
)["contents"][0]["text"]
assert "difffn" in difffn, difffn[:200]
print("difffn resource OK:", difffn.splitlines()[-1][:70])
assert any(
    t["uriTemplate"] == "borer://migrate/{function}/{path}" for t in tmpl["resourceTemplates"]
), tmpl
migrate = wait_for(
    send(
        "resources/read",
        {"uri": "borer://migrate/entry_thunk/" + os.path.abspath(TARGET).replace("\\", "/")},
    )
)["contents"][0]["text"]
assert migrate.startswith("# migrate "), migrate[:200]
assert "0 moved" in migrate, migrate[:200]  # a binary against itself moved nothing
print("migrate resource OK:", migrate.splitlines()[0][:70])
fp = wait_for(send("resources/read", {"uri": "borer://fingerprint"}))["contents"][0]["text"]
assert fp.startswith("# borer fingerprint v1 digest "), fp[:200]
assert "sidecar" in fp, fp[:300]  # the answer is a digest; the CLI writes the manifest
fp_path = os.path.join(tempfile.gettempdir(), f"borer-smoke-{os.getpid()}.bfp")
subprocess.run([EXE, "--no-pdb", "fingerprint", TARGET, fp_path], check=True, capture_output=True)
fpdiff = wait_for(send("resources/read", {"uri": "borer://diff/" + fp_path.replace("\\", "/")}))[
    "contents"
][0]["text"]
os.remove(fp_path)
assert "identical" in fpdiff, fpdiff[:200]
print("fingerprint resource OK:", fp.splitlines()[1])
missing = wait_for(send("resources/read", {"uri": "borer://nope"}), allow_error=True)
assert "error" in missing, missing
# query reads every resource through a tool, as resources/read answers it: one
# answer memory keyed by the URI. A read without a tag is whole every time
# (borer://info was read above: a second reader sharing the session may not
# hold it); with the tag its last line carries, on the URI or as `since`, it is
# a note naming the read that returns the text; `!fresh` is whole; and the
# same refusal
info = rd["contents"][0]["text"]
assert call_tool("query", {"uri": "borer://info"}) == info
tag = info.splitlines()[-1].removeprefix("# since=")
noted = call_tool("query", {"uri": f"borer://info!since={tag}"})
assert noted.startswith(f"# unchanged since the answer tagged {tag}: "), noted[:300]
assert "reading borer://info (resources/read or the query tool) returns it" in noted, noted
assert call_tool("query", {"uri": "borer://info", "since": tag}) == noted
assert call_tool("query", {"uri": f"borer://info!since={tag}!fresh"}) == info
qmissing = wait_for(
    send("tools/call", {"name": "query", "arguments": {"uri": "borer://nope"}}), allow_error=True
)
assert qmissing.get("error") == missing["error"], (qmissing, missing)
assert "borer://scenarios/{spec}" in missing["error"]["message"], missing
# script runs inline Rhai over the loaded binary, and its query() reads any
# resource through the same handlers resources/read uses
ran = call_tool(
    "script",
    {"code": 'print(functions().len > 0); print(query("borer://info").contains("format"));'},
)
assert ran.startswith("true\ntrue\n"), ran
# a repeated tool call is whole every time; the call with its tag passed back as
# `since` is a note naming the call that returns the text; a tag that is not one
# is refused
page = {"limit": 40, "offset": 1}
first = call_tool("functions", page)
assert call_tool("functions", page) == first
tag = first.splitlines()[-1].removeprefix("# since=")
note = call_tool("functions", {**page, "since": tag})
assert note.startswith(f"# unchanged since the answer tagged {tag}: "), note[:300]
assert 'calling functions {"limit":40,"offset":1} returns it in full' in note, note
bad = wait_for(
    send("tools/call", {"name": "functions", "arguments": {**page, "since": "zz"}}),
    allow_error=True,
)
assert "is not a tag" in json.dumps(bad), bad
print("query and answer memory OK (resources/read's text, errors; whole unless a tag is passed)")
comp = wait_for(
    send(
        "completion/complete",
        {
            "ref": {"type": "ref/prompt", "name": "explain_function"},
            "argument": {"name": "address", "value": "entry_"},
        },
    )
)
assert "entry_thunk" in comp["completion"]["values"], comp
comp2 = wait_for(
    send(
        "completion/complete",
        {
            "ref": {"type": "ref/prompt", "name": "find_check"},
            "argument": {"name": "what", "value": "lic"},
        },
    )
)
assert comp2["completion"]["values"] == ["license key"], comp2
print(f"protocol surface OK (tools/list {len(raw_tools)} bytes, resources, completions)")

proc.stdin.close()
rc = proc.wait(timeout=10)
if rc != 0:
    raise SystemExit(f"server exited {rc}")

# 10. the 2026-07-28 lifecycle: no initialize; every request carries _meta with
#     the protocol version and client capabilities; discover replaces
#     initialize; list results carry cache hints
p2 = subprocess.Popen(
    [EXE],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=STDERR,
    text=True,
    encoding="utf-8",
)
# Daemon and cancelled, like the first watchdog: a live non-daemon timer
# holds the interpreter open at exit until it fires, which added its whole
# budget to every green run.
atexit.register(p2.kill)
watchdog2 = threading.Timer(60, p2.kill)
watchdog2.daemon = True
watchdog2.start()
META = {
    "io.modelcontextprotocol/protocolVersion": "2026-07-28",
    "io.modelcontextprotocol/clientCapabilities": {},
}


def rpc2(i, method, params):
    p2.stdin.write(
        json.dumps({"jsonrpc": "2.0", "id": i, "method": method, "params": params}) + "\n"
    )
    p2.stdin.flush()
    while True:
        line = p2.stdout.readline()
        if not line:
            raise SystemExit("2026-07-28 session: server closed stdout; its stderr follows")
        r = json.loads(line)
        if r.get("id") == i:
            if "error" in r:
                raise SystemExit(f"2026-07-28 session rpc error: {r['error']}")
            return r["result"]


disc = rpc2(1, "server/discover", {"_meta": META})
assert "2026-07-28" in disc["supportedVersions"], disc
assert sorted(disc["capabilities"]) == ["completions", "prompts", "resources", "tools"], disc[
    "capabilities"
]
tl = rpc2(2, "tools/list", {"_meta": META})
assert tl.get("ttlMs", 0) >= 3_600_000 and tl.get("cacheScope") == "public", {
    k: v for k, v in tl.items() if k != "tools"
}
assert len(tl["tools"]) == len(tools["tools"]), "tool list differs between lifecycles"
loaded = rpc2(
    3,
    "tools/call",
    {"_meta": META, "name": "load_binary", "arguments": {"path": os.path.abspath(TARGET)}},
)
assert not loaded.get("isError"), loaded
info2 = rpc2(4, "tools/call", {"_meta": META, "name": "binary_info", "arguments": {}})
assert "format:" in info2["content"][0]["text"], info2
p2.stdin.close()
p2.wait(timeout=10)
watchdog2.cancel()
print("2026-07-28 lifecycle OK (discover, cache hints, per-request _meta)")
passed = True
print("SMOKE OK")
watchdog.cancel()
