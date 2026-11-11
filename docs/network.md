# Network access

borer has no telemetry or crash reporting. Only these reach the network:

- A command line run at a terminal checks once a day for a newer release on
  GitHub. It never runs for the MCP server or under `CI`, and
  `BORER_NO_UPDATE_CHECK=1` turns it off.
- `fetch_pdb`, only when asked, sends the PDB's name, GUID and age to the
  symbol server, and `borer doctor` checks that server is reachable unless
  run as `borer doctor offline`.
- `borer update` and the installers download the release from GitHub. With
  `GH_TOKEN` or `GITHUB_TOKEN` set, `borer update` sends that token to
  GitHub's API (api.github.com) and nowhere else; the daily check never
  sends it.
