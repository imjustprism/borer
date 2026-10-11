# Security policy

borer reads untrusted binaries by design, so a file that makes it misbehave
is a bug worth reporting. Most of those are ordinary bugs and belong in a
public issue:

- a panic, hang or runaway memory use on a malformed or hostile file
- wrong output, including on a packed or obfuscated sample

Report privately instead when the problem could hurt the person running
borer:

- anything that gets code from an analyzed file to run natively on the
  host (the emulator and the Rhai sandbox must never allow that)
- a write outside the path you asked for (`unpack`, `fingerprint`,
  `snapshot`, project files)
- the live-process view doing anything beyond reading memory
- the symbol-server client fetching from or writing to somewhere it
  should not

Use **Report a vulnerability** on the repository's Security tab. Include
what you ran and, if you can share it, the file that triggers it.

Only the latest commit on `main` gets fixes.
