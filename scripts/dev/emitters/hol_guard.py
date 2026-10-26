"""HOL Guard's MCP server contribution for borer (`guard.mcp-server-contribution.v1`).

HOL Guard (github.com/hashgraph-online/hol-guard) reads a reviewed entry per
MCP server from `contributions/mcp-servers/`, matched here by the `borer`
executable (`direct-command`, which may only `inherit`, `review` or `block`).
A tool that writes a file, uses the network, reads another process's
memory or restarts the server is `review`, so each such call waits for
approval; every other one keeps Guard's usual handling, including the
naming and typing tools, whose changes stay in borer's session and preview
until called with `dry_run=false`. A tool
borer adds later falls under `other`. Risk classes and safer alternatives
come from the effects the tools state, so a kind of effect no tool has
drops out. Bump `VERSION` when a regenerated entry differs from the one
submitted.
"""

from __future__ import annotations

from typing import Any

FILE = "mcp.borer.json"
"""The entry's file name in `contributions/mcp-servers/`."""

VERSION = "1.0.0"
"""The entry's own version, not borer's."""

RISK = {
    "reads-files": "local-data-access",
    "writes-files": "local-file-write",
    "network": "external-network-read",
    "reads-process-memory": "local-process-memory-read",
    "changes-session": None,
    "restarts-server": "local-process-restart",
}
"""The risk class each effect word carries; `changes-session` stays in the
server's memory and carries none. A word missing here stops the run."""

SAFER = {
    "writes-files": "Point BORER_OUTPUT_DIR at a scratch folder: every project or C file a tool "
    "writes lands under it, and an existing one is replaced only when the call says overwrite.",
    "network": "fetch_pdb downloads from Microsoft's symbol server, or from BORER_SYMBOL_SERVER "
    "when set; set it only to a server you trust, and keep the PDB cache local.",
    "reads-process-memory": "Live tools read memory of a running process of the loaded binary "
    "(Windows), never writing it; leave BORER_LIVE_ANY unset so no other process can be read.",
    "changes-session": "Names, comments and types live in borer's session and never touch the "
    "binary; the naming and typing tools preview until called with dry_run=false.",
}
"""One safer alternative per effect word that has one."""

REVIEWED = {"writes-files", "network", "reads-process-memory", "restarts-server"}
"""The effects that leave borer's own session, so a call with one waits for approval."""


def emit(manifest: dict[str, Any]) -> dict[str, Any]:
    """Returns the contribution for the tools `borer tools` listed."""
    tools = manifest["tools"]
    effects = sorted({word for t in tools for word in t["effects"]})
    unknown = [word for word in effects if word not in RISK]
    if unknown:
        raise SystemExit(f"hol_guard: no risk class for effect {', '.join(unknown)}")
    if "reads-process-memory" not in effects:
        raise SystemExit(
            "hol_guard: no live tools in the manifest; borer lists them only on Windows, and "
            "the entry matches every platform's borer, so generate it from a Windows build"
        )

    def state(tool: dict[str, Any]) -> str:
        return "review" if REVIEWED.intersection(tool["effects"]) else "inherit"

    return {
        "schemaVersion": "guard.mcp-server-contribution.v1",
        "id": "mcp.borer",
        "version": VERSION,
        "name": "borer MCP",
        "description": "Reviews borer's tools that write files, use the network, read another "
        "process's memory or restart the server; analysis and session-only naming keep Guard's "
        "usual handling. Off until you turn it on.",
        "trustClass": "external",
        "activation": "opt-in",
        "publisher": {
            "id": "io.github.imjustprism",
            "displayName": "imjustprism",
            "url": "https://github.com/imjustprism/borer",
        },
        "icon": {"kind": "react-icon", "name": "HiMiniCube", "background": "#0B0C0E"},
        "homepage": "https://borer.lol",
        "license": "AGPL-3.0-only",
        "launch": {"kind": "direct-command", "command": "borer"},
        "riskClasses": [RISK[w] for w in effects if RISK[w]],
        "tools": [{"name": t["name"], "state": state(t)} for t in tools]
        + [{"name": "other", "state": "inherit"}],
        "referenceUrls": [
            "https://github.com/imjustprism/borer",
            "https://borer.lol/docs",
        ],
        "saferAlternatives": [SAFER[w] for w in effects if w in SAFER],
    }
