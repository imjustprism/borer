#!/usr/bin/env bash
# Keeps the borer binary in the plugin's data folder, where its MCP server
# entry points, at the plugin's own version: the release named by
# plugin.json's "version" (BORER_VERSION pins another tag, and a plugin.json
# with no version takes the latest), checked against the release's
# SHA256SUMS. The SessionStart hook runs it on every start: a binary of
# another version is replaced, so updating the plugin updates borer, and one
# already current is left alone. When a fetch fails and an older binary is
# there, that one stays and the failure is reported. On Windows this runs
# under Git Bash.
set -eu

main() {
  repo="imjustprism/borer"
  data="${CLAUDE_PLUGIN_DATA:-${CLAUDE_CONFIG_DIR:-$HOME/.claude}/plugins/data/borer-borer}"
  here="$(cd "$(dirname "$0")/.." && pwd)"

  case "$(uname -s)-$(uname -m)" in
    Linux-x86_64) target="x86_64-unknown-linux-gnu" ext="tar.gz" exe="borer" ;;
    Darwin-arm64) target="aarch64-apple-darwin" ext="tar.gz" exe="borer" ;;
    Darwin-x86_64) target="x86_64-apple-darwin" ext="tar.gz" exe="borer" ;;
    MINGW*-x86_64 | MSYS*-x86_64 | CYGWIN*-x86_64) target="x86_64-pc-windows-msvc" ext="zip" exe="borer.exe" ;;
    *) fail "no build for $(uname -s) $(uname -m)" ;;
  esac
  bin="$data/$exe"

  version=$(sed -n 's/^[[:space:]]*"version"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$here/.claude-plugin/plugin.json" 2>/dev/null | head -n 1)
  tag="${BORER_VERSION:-${version:+v$version}}"
  have=$(cat "$data/VERSION" 2>/dev/null || true)

  if [ ! -f "$bin" ] || [ -z "$tag" ] || [ "$have" != "$tag" ]; then
    if ! (fetch); then
      [ -f "$bin" ] || exit 1
      echo "borer: keeping the borer already installed (${have:-of an unknown version})" >&2
    fi
  fi
}

fail() {
  echo "borer: $*" >&2
  exit 1
}

# Fetches the release `tag` names (the latest when it names none) into
# $data, setting the old binary aside first so a running copy is not in the
# way, and records the tag in $data/VERSION. Runs in a subshell, as an `if`
# condition, where `set -e` does not hold, so every step checks itself.
fetch() {
  if [ -z "$tag" ]; then
    url=$(curl -fsSLI -o /dev/null -w '%{url_effective}' "https://github.com/$repo/releases/latest") ||
      fail "could not reach GitHub"
    tag="${url##*/}"
    [ "$tag" = "latest" ] && fail "no release published yet"
  fi
  [ "$have" = "$tag" ] && [ -f "$bin" ] && return 0

  name="borer-$tag-$target"
  base="${BORER_MIRROR:+$BORER_MIRROR/$tag}"
  base="${base:-https://github.com/$repo/releases/download/$tag}"
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT

  curl -fsSL -o "$tmp/$name.$ext" "$base/$name.$ext" || fail "no $name.$ext in release $tag"
  curl -fsSL -o "$tmp/SHA256SUMS" "$base/SHA256SUMS" || fail "no SHA256SUMS in release $tag"
  want=$(awk -v f="$name.$ext" '$2 == f || $2 == "*" f { print $1 }' "$tmp/SHA256SUMS")
  if command -v sha256sum >/dev/null 2>&1; then
    got=$(sha256sum "$tmp/$name.$ext" | awk '{ print $1 }')
  else
    got=$(shasum -a 256 "$tmp/$name.$ext" | awk '{ print $1 }')
  fi
  [ -n "$want" ] && [ "$got" = "$want" ] || fail "checksum mismatch for $name.$ext"

  if [ "$ext" = "zip" ]; then
    # unzip warns (and exits 1) on archives made on Windows, so judge it by the file it leaves.
    unzip -qo "$tmp/$name.zip" -d "$tmp" >/dev/null 2>&1 || true
    [ -f "$tmp/$name/$exe" ] ||
      powershell.exe -NoProfile -Command "Expand-Archive -Force -Path '$(cygpath -w "$tmp/$name.zip")' -DestinationPath '$(cygpath -w "$tmp")'"
  else
    tar -xzf "$tmp/$name.tar.gz" -C "$tmp" || fail "cannot unpack $name.$ext"
  fi
  [ -f "$tmp/$name/$exe" ] || fail "no $exe in $name.$ext"

  mkdir -p "$data" || fail "cannot make $data"
  cp "$tmp/$name/$exe" "$bin.new" && chmod 755 "$bin.new" || fail "cannot write $bin.new"
  if [ "$(uname -s)" = "Darwin" ]; then
    xattr -d com.apple.quarantine "$bin.new" 2>/dev/null || true
  fi
  if [ -f "$bin" ]; then
    mv -f "$bin" "$bin.old" 2>/dev/null || true
  fi
  mv -f "$bin.new" "$bin" || fail "cannot put the new borer in place"
  rm -f "$bin.old" 2>/dev/null || true
  printf '%s\n' "$tag" >"$data/VERSION" || fail "cannot write $data/VERSION"
  echo "borer $tag was installed for this plugin; run /mcp to connect it if it is not connected yet."
}

main "$@"
