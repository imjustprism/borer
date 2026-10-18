#!/usr/bin/env bash
# Puts the borer binary in the plugin's data folder, where its MCP server entry
# points, the first time a session starts: the latest release for this
# machine, checked against the release's SHA256SUMS. Later sessions find it
# there and do nothing. On Windows this runs under Git Bash.
set -eu

repo="imjustprism/borer"
data="${CLAUDE_PLUGIN_DATA:-${CLAUDE_CONFIG_DIR:-$HOME/.claude}/plugins/data/borer-borer}"

if [ -x "$data/borer" ] || [ -f "$data/borer.exe" ]; then
  exit 0
fi

fail() {
  echo "borer: $*" >&2
  exit 1
}

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) target="x86_64-unknown-linux-gnu" ext="tar.gz" ;;
  Darwin-arm64) target="aarch64-apple-darwin" ext="tar.gz" ;;
  Darwin-x86_64) target="x86_64-apple-darwin" ext="tar.gz" ;;
  MINGW*-x86_64 | MSYS*-x86_64 | CYGWIN*-x86_64) target="x86_64-pc-windows-msvc" ext="zip" ;;
  *) fail "no build for $(uname -s) $(uname -m)" ;;
esac

# BORER_VERSION pins a release; otherwise the latest, from where /releases/latest redirects.
tag="${BORER_VERSION:-}"
if [ -z "$tag" ]; then
  url=$(curl -fsSLI -o /dev/null -w '%{url_effective}' "https://github.com/$repo/releases/latest") ||
    fail "could not reach GitHub"
  tag="${url##*/}"
  [ "$tag" = "latest" ] && fail "no release published yet"
fi

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

mkdir -p "$data"
if [ "$ext" = "zip" ]; then
  # unzip warns (and exits 1) on archives made on Windows, so judge it by the file it leaves.
  unzip -qo "$tmp/$name.zip" -d "$tmp" >/dev/null 2>&1 || true
  [ -f "$tmp/$name/borer.exe" ] ||
    powershell.exe -NoProfile -Command "Expand-Archive -Force -Path '$(cygpath -w "$tmp/$name.zip")' -DestinationPath '$(cygpath -w "$tmp")'"
  cp "$tmp/$name/borer.exe" "$data/borer.exe"
else
  tar -xzf "$tmp/$name.tar.gz" -C "$tmp"
  cp "$tmp/$name/borer" "$data/borer"
  chmod 755 "$data/borer"
  [ "$(uname -s)" = "Darwin" ] && xattr -d com.apple.quarantine "$data/borer" 2>/dev/null || true
fi
echo "borer $tag was installed for this plugin; run /mcp to connect it if it is not connected yet."
