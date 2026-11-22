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
- When the person picks Claude Code in the chat, the app itself sends
  nothing over the network. This mode runs the installed Claude Code command
  line in its documented headless mode, under the person's own Claude Code
  sign-in and terms; borer reads no Claude Code file or credential. It is
  offered only when the program is on `PATH`, found by file name alone: on
  Windows the native installer's `claude.exe` (a `claude.cmd` from npm is not
  detected, and no row is shown for it), elsewhere `claude`. The app starts
  it on this machine, in a new empty folder of its own under the app's data
  folder, removed when it ends, with no built-in tool, no saved session and
  no Claude Code settings file (the person's, the project's or the local
  one), and hands it each message over a pipe. The provider keys the app reads (`ANTHROPIC_API_KEY`, `OPENAI_API_KEY`,
  `GEMINI_API_KEY`, `OPENROUTER_API_KEY`) and `ANTHROPIC_AUTH_TOKEN` and
  `ANTHROPIC_BASE_URL` are removed from its environment, so it runs on its
  own sign-in, not on a key set for the app's other providers. It runs
  in Claude Code's safe mode, so none of the person's Claude Code hooks,
  skills, plugins or CLAUDE.md files run or load: text from the binary
  reaches the model, and nothing configured for other work may act on it.
  Its tool calls come
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
