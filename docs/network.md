# Network access

borer has no telemetry or crash reporting. Only these reach the network:

- A command line run at a terminal checks once a day for a newer release on
  GitHub. It never runs for the MCP server or under `CI`, and
  `BORER_NO_UPDATE_CHECK=1` turns it off.
- The desktop app checks for a newer release 5 seconds after its window
  opens, once a day while it runs, and when Check for Updates is picked in
  its command palette: one `GET` of
  `https://api.github.com/repos/imjustprism/borer/releases/latest` with only
  `User-Agent: borer-app/<version>` and `Accept: application/vnd.github+json`,
  no redirect followed. `BORER_NO_UPDATE_CHECK=1` or `"auto_update": false`
  in its settings file turns it off, and so does a settings file that does
  not load in full; the app reads that file at launch, so a change made
  outside the app counts after a restart. Nothing is downloaded.
- The desktop app's chat, only once a person picks a provider, talks to that
  provider's host and nowhere else: Anthropic, OpenAI, Google AI or
  OpenRouter, or the Ollama or LM Studio address in the settings
  (`localhost` by default). It lists the provider's models, then sends each
  turn's conversation (the person's messages, the tools' descriptions and
  the tool results, which quote the open binary) with the provider's key,
  following no redirect.
- When the person picks Claude Code in the chat (offered only when a `claude`
  program is on `PATH`), the app itself sends nothing over the network. It
  starts that program on this machine, in the system's temporary folder,
  with no built-in tool, none of the person's Claude Code customizations and
  no saved session, and hands it each message over a pipe. Claude Code talks
  to its own service with its own sign-in, under Anthropic's terms for it;
  borer never reads its settings, credentials or tokens. Its tool calls come
  back over the same pipe and are answered by the app's tools, so what it
  sends holds the person's messages and the tool answers, which quote the
  open binary. Picking it starts the program once to list its models: no
  message is sent to a model then, though Claude Code may reach its service
  when it starts, as it does at a terminal.
- `fetch_pdb`, only when asked, sends the PDB's name, GUID and age to the
  symbol server, and `borer doctor` checks that server is reachable unless
  run as `borer doctor offline`.
- `borer update` and the installers download the release from GitHub. With
  `GH_TOKEN` or `GITHUB_TOKEN` set, `borer update` sends that token to
  GitHub's API (api.github.com) and nowhere else; the daily check never
  sends it.
