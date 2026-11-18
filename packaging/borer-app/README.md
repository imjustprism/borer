# borer-app

The desktop app of borer, the blazing fast, Rust-based reverse engineering
tool built for humans and AI: Zed's workspace with borer's function list in
the left dock and decompile tabs in the center. It is
a preview: rough edges are expected, and the app is unsigned.

## Install it

Each release has an installer per platform beside the archives, and
SHA256SUMS to check them with. None is signed yet, so each system warns once.

- **Windows:** run `borer-app-<version>-x86_64-pc-windows-msvc.msi`. If
  SmartScreen stops it, choose "More info", then "Run anyway". It installs
  for every user under `Program Files\borer`, adds borer to the Start menu
  and to Installed apps (uninstall it there), and another version's MSI
  replaces the installed one in place.
- **macOS:** open `borer-app-<version>-<arch>-apple-darwin.dmg` and drag
  borer to Applications. Gatekeeper refuses an app from an unidentified
  developer the first time: Control-click borer in Applications, choose Open,
  then Open again (on macOS 15 and later, open System Settings > Privacy &
  Security and choose "Open Anyway"). Or clear the download quarantine from
  Terminal: `xattr -dr com.apple.quarantine /Applications/borer.app`. It draws
  with Metal.
- **Linux:** unpack the `.tar.gz`. `./borer-app` runs it in place; to add it to
  the application menu, copy the binary onto your PATH and the desktop entry
  and icons into your data directory:
  `cp borer-app ~/.local/bin/ && cp -r share ~/.local/`. It runs on X11 or
  Wayland with a Vulkan driver. Built on Ubuntu 22.04, it needs glibc 2.35 or
  newer and the fontconfig, freetype, OpenSSL 3, xkbcommon and Vulkan loader
  libraries (on Debian and Ubuntu: `sudo apt install libfontconfig1
  libfreetype6 libssl3 libxkbcommon-x11-0 libwayland-client0 libvulkan1`).

The archives (`.zip` on Windows, `.tar.gz` elsewhere) hold the same binary
to run without installing; on macOS, clear its quarantine first with
`xattr -dr com.apple.quarantine borer-app-*`.

## Run it

```bash
borer-app                  # then drop a file on it, or press Ctrl+O
borer-app path/to/program  # opens a PE, ELF or Mach-O file
```

The command palette (Ctrl+Shift+P, Cmd+Shift+P on macOS) lists every action.
Settings, keymap and themes are kept in the config directory, under `borer`
(`%APPDATA%`, `~/Library/Application Support` or `~/.config`); the layout,
Recent and the tabs open at quit in the local data directory, under `borer`
(`%LOCALAPPDATA%`, `~/Library/Application Support` or `~/.local/share`).
The first run there copies in the settings, themes and layout an earlier build
kept under `borer-app` in the local data directory. `--data-dir <dir>` as the
first argument keeps everything in another directory.

## License

borer-app is licensed under the GNU Affero General Public License v3.0 only
(LICENSE), with the attributions in NOTICE. THIRD-PARTY-LICENSES lists every
crate the binary contains, Zed's among them, with its license text and where
its source is published; RUST-STD-COPYRIGHT.html covers the Rust standard
library. The source of this build is at https://github.com/imjustprism/borer.
