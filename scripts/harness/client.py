"""One stdio session with a borer MCP server.

`call` is a JSON-RPC request. `tool` is `tools/call` and returns the raw
result plus its text. A protocol or tool error raises `SystemExit`, which
is what a one-shot script wants. `bench` and `smoke` do not use this: one
times each call, the other drives the handshake itself.
"""

from __future__ import annotations

import json
import os
import subprocess
from typing import Any

PROTOCOL = "2025-11-25"


class Client:
    """A borer process spoken to as an agent would, over stdio JSON-RPC."""

    def __init__(self, exe: str) -> None:
        # The measurements read whole answers, so no default byte budget.
        self.proc = subprocess.Popen(
            [exe],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            env=os.environ | {"BORER_BUDGET": "0"},
        )
        self.next_id = 0
        result = self.call(
            "initialize",
            {
                "protocolVersion": PROTOCOL,
                "capabilities": {},
                "clientInfo": {"name": "borer-mcp.py", "version": "1"},
            },
        )
        self.server: dict[str, Any] = result["serverInfo"]
        self.instructions: str = result.get("instructions", "")
        self.notify("notifications/initialized")

    def notify(self, method: str, params: dict[str, Any] | None = None) -> None:
        """Sends a notification and does not wait for a reply."""
        msg: dict[str, Any] = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            msg["params"] = params
        self._write(msg)

    def request(self, method: str, params: dict[str, Any] | None = None) -> dict[str, Any]:
        """Sends a request and returns its whole reply, `result` or `error`."""
        self.next_id += 1
        rid = self.next_id
        msg: dict[str, Any] = {"jsonrpc": "2.0", "id": rid, "method": method}
        if params is not None:
            msg["params"] = params
        self._write(msg)
        while True:
            line = self._stdout().readline()
            if not line:
                err = self._stderr().read()
                raise SystemExit(f"server closed the pipe; stderr: {err[-1500:]}")
            reply = json.loads(line)
            if reply.get("id") == rid:
                return reply

    def call(self, method: str, params: dict[str, Any] | None = None) -> Any:
        """Sends a request and returns its `result`, or exits on an error."""
        reply = self.request(method, params)
        if "error" in reply:
            raise SystemExit(f"rpc error: {json.dumps(reply['error'])}")
        return reply["result"]

    def tool(self, name: str, args: dict[str, Any]) -> tuple[dict[str, Any], str]:
        """Calls a tool. Returns the raw result and the joined text content."""
        res = self.call("tools/call", {"name": name, "arguments": args})
        text = "\n".join(c.get("text", "") for c in res.get("content", []))
        if res.get("isError"):
            raise SystemExit(f"tool error: {text}")
        return res, text

    def close(self) -> None:
        """Closes the server's input and waits for it to exit."""
        self._stdin().close()
        self.proc.wait(timeout=10)

    def _write(self, msg: dict[str, Any]) -> None:
        stdin = self._stdin()
        stdin.write(json.dumps(msg) + "\n")
        stdin.flush()

    def _stdin(self) -> Any:
        pipe = self.proc.stdin
        if pipe is None:
            raise SystemExit("server was started without an input pipe")
        return pipe

    def _stdout(self) -> Any:
        pipe = self.proc.stdout
        if pipe is None:
            raise SystemExit("server was started without an output pipe")
        return pipe

    def _stderr(self) -> Any:
        pipe = self.proc.stderr
        if pipe is None:
            raise SystemExit("server was started without an error pipe")
        return pipe
