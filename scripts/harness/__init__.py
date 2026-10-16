"""Pieces the helper scripts share: the checkout root, and one MCP client.

The commands themselves are grouped beside this package:

- `check` fails when a generated table, the commit messages, or a comment drifts
- `run` drives a built server and reports what it did
- `dev` installs the server a local MCP client launches
- `gate.py` is the one command CI runs
"""
