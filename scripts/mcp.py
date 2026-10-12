#!/usr/bin/env python3
"""One-shot MCP client for borer: call any tool, prompt, resource or completion
from a shell, exactly as an agent would over stdio JSON-RPC.

  python scripts/mcp.py --list                             tools, prompts, resources
  python scripts/mcp.py BIN TOOL [key=value ...]           e.g. decompile address=main
  python scripts/mcp.py BIN --prompt NAME [key=value ...]  the prompt's text
  python scripts/mcp.py BIN --resource URI                 e.g. borer://decompile/0x401000
  python scripts/mcp.py BIN --complete PROMPT ARG PREFIX   argument completion

Options: --exe PATH   server binary (default target/release/borer.exe, else debug)
         --raw        print the JSON-RPC result instead of the text content
Values: integers, floats, true/false are typed; anything else is a string.
Exit status is non-zero on any protocol or tool error.
"""

import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def pick_exe(args):
    if "--exe" in args:
        i = args.index("--exe")
        exe = args[i + 1]
        del args[i : i + 2]
        return exe
    for profile in ("release", "debug"):
        p = os.path.join(ROOT, "target", profile, "borer.exe")
        if os.path.exists(p):
            return p
    raise SystemExit("no borer.exe built; run `cargo build --release`")


def typed(v):
    if v in ("true", "false"):
        return v == "true"
    for cast in (int, float):
        try:
            return cast(v)
        except ValueError:
            pass
    return v


class Client:
    def __init__(self, exe):
        self.proc = subprocess.Popen(
            [exe],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
        )
        self.next_id = 0
        r = self.call(
            "initialize",
            {
                "protocolVersion": "2025-11-25",
                "capabilities": {},
                "clientInfo": {"name": "borer-mcp.py", "version": "1"},
            },
        )
        self.server = r["serverInfo"]
        self.instructions = r.get("instructions", "")
        self.notify("notifications/initialized")

    def notify(self, method, params=None):
        msg = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            msg["params"] = params
        self.proc.stdin.write(json.dumps(msg) + "\n")
        self.proc.stdin.flush()

    def request(self, method, params=None):
        """Send a request and return its whole reply, `result` or `error`."""
        self.next_id += 1
        rid = self.next_id
        msg = {"jsonrpc": "2.0", "id": rid, "method": method}
        if params is not None:
            msg["params"] = params
        self.proc.stdin.write(json.dumps(msg) + "\n")
        self.proc.stdin.flush()
        while True:
            line = self.proc.stdout.readline()
            if not line:
                err = self.proc.stderr.read()
                raise SystemExit(f"server closed the pipe; stderr: {err[-1500:]}")
            reply = json.loads(line)
            if reply.get("id") == rid:
                return reply

    def call(self, method, params=None):
        reply = self.request(method, params)
        if "error" in reply:
            raise SystemExit(f"rpc error: {json.dumps(reply['error'])}")
        return reply["result"]

    def tool(self, name, args):
        res = self.call("tools/call", {"name": name, "arguments": args})
        text = "\n".join(c.get("text", "") for c in res.get("content", []))
        if res.get("isError"):
            raise SystemExit(f"tool error: {text}")
        return res, text

    def close(self):
        self.proc.stdin.close()
        self.proc.wait(timeout=10)


def main(argv):
    args = list(argv)
    exe = pick_exe(args)
    raw = "--raw" in args
    if raw:
        args.remove("--raw")
    if not args or args[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    c = Client(exe)
    try:
        if args[0] == "--list":
            tools = c.call("tools/list")
            print(f"# server {c.server['name']} v{c.server['version']}")
            print(f"# {len(tools['tools'])} tools ({len(json.dumps(tools))} bytes on the wire)")
            for t in tools["tools"]:
                params = ", ".join(sorted(t["inputSchema"].get("properties", {})))
                print(f"{t['name']}({params})\n    {t['description']}")
            prompts = c.call("prompts/list")["prompts"]
            print("# prompts: " + ", ".join(p["name"] for p in prompts))
            res = c.call("resources/list")["resources"]
            tmpl = c.call("resources/templates/list")["resourceTemplates"]
            print("# resources: " + ", ".join(r["uri"] for r in res))
            print("# templates: " + ", ".join(t["uriTemplate"] for t in tmpl))
            return 0
        binary = os.path.abspath(args[0])
        _, summary = c.tool("load_binary", {"path": binary})
        if len(args) < 2:
            print(summary)
            return 0
        if args[1] == "--prompt":
            kv = dict(a.split("=", 1) for a in args[3:])
            res = c.call("prompts/get", {"name": args[2], "arguments": kv})
            out = res if raw else "\n".join(m["content"].get("text", "") for m in res["messages"])
        elif args[1] == "--resource":
            res = c.call("resources/read", {"uri": args[2]})
            out = res if raw else "\n".join(x.get("text", "") for x in res["contents"])
        elif args[1] == "--complete":
            prompt, arg, prefix = args[2], args[3], args[4] if len(args) > 4 else ""
            res = c.call(
                "completion/complete",
                {
                    "ref": {"type": "ref/prompt", "name": prompt},
                    "argument": {"name": arg, "value": prefix},
                },
            )
            out = res if raw else "\n".join(res["completion"]["values"])
        else:
            kv = {}
            for a in args[2:]:
                k, _, v = a.partition("=")
                kv[k] = typed(v)
            res, text = c.tool(args[1], kv)
            out = res if raw else text
        print(json.dumps(out, indent=1) if raw else out)
        return 0
    finally:
        c.close()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
