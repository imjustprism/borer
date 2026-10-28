#!/usr/bin/env node
"use strict";

// Runs the borer binary that the platform package (an optionalDependency
// npm installs only on its own os and cpu) holds. Arguments and stdio pass
// through untouched, since MCP speaks over stdio; the exit code and a
// terminating signal come back as this process's own.

const { spawn } = require("node:child_process");

const pkg = `@imjustprism/borer-${process.platform}-${process.arch}`;
const exe = process.platform === "win32" ? "borer.exe" : "borer";

let binary;
try {
  binary = require.resolve(`${pkg}/bin/${exe}`);
} catch {
  process.stderr.write(
    `borer: no borer binary for ${process.platform}-${process.arch} (package ${pkg} is not installed).\n` +
      "Prebuilt binaries exist for win32-x64, linux-x64 (glibc 2.35+), darwin-x64 and darwin-arm64.\n" +
      "On one of those, reinstall without --omit=optional or --no-optional.\n" +
      "Elsewhere, build from source: https://github.com/imjustprism/borer#install\n",
  );
  process.exit(1);
}

const child = spawn(binary, process.argv.slice(2), { stdio: "inherit" });
const signals = ["SIGINT", "SIGTERM", "SIGHUP"];
for (const signal of signals) {
  process.on(signal, () => child.kill(signal));
}
child.on("error", (err) => {
  process.stderr.write(`borer: could not run ${binary}: ${err.message}\n`);
  process.exit(1);
});
child.on("exit", (code, signal) => {
  if (signal) {
    for (const s of signals) process.removeAllListeners(s);
    process.kill(process.pid, signal);
  } else {
    process.exit(code ?? 1);
  }
});
