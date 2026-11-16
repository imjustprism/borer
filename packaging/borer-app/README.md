# borer-app

The desktop app of borer, a reverse-engineering engine: Zed's workspace with
borer's function list in the left dock and decompile tabs in the center. It is
a preview: rough edges are expected, and the app is unsigned.

## Run it

```bash
borer-app                  # then drop a file on it, or press Ctrl+O
borer-app path/to/program  # opens a PE, ELF or Mach-O file
```

- **Windows:** run `borer-app.exe`. SmartScreen may stop an unsigned program:
  choose "More info", then "Run anyway". A console window opens beside the
  app; leave it open.
- **macOS:** from Terminal, clear the download quarantine once, then run it:
  `xattr -dr com.apple.quarantine borer-app-*` and `./borer-app`. It draws
  with Metal.
- **Linux:** `./borer-app`, on X11 or Wayland with a Vulkan driver. Built on
  Ubuntu 22.04; it needs glibc 2.35 or newer and the fontconfig, freetype,
  OpenSSL 3, xkbcommon and Vulkan loader libraries (on Debian and Ubuntu:
  `sudo apt install libfontconfig1 libfreetype6 libssl3 libxkbcommon-x11-0
  libwayland-client0 libvulkan1`).

The command palette (Ctrl+Shift+P, Cmd+Shift+P on macOS) lists every action.
Settings, keymap and layout are kept in the local data directory, under
`borer-app` (`%LOCALAPPDATA%`, `~/Library/Application Support` or
`~/.local/share`); `--data-dir <dir>` as the first argument picks another.

## License

borer-app is licensed under the GNU Affero General Public License v3.0 only
(LICENSE), with the attributions in NOTICE. THIRD-PARTY-LICENSES lists every
crate the binary contains, Zed's among them, with its license text and where
its source is published; RUST-STD-COPYRIGHT.html covers the Rust standard
library. The source of this build is at https://github.com/imjustprism/borer.
