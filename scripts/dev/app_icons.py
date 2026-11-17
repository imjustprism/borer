#!/usr/bin/env python3
"""Write borer-app's icons from the brand's app icon and favicons.

    python scripts/dev/app_icons.py path/to/borer-web/packages/brand/assets

The sources are the borer-web repository's brand assets: `logo/icon-1024.png`,
the app icon (a dark rounded tile with the mark, transparent corners), for 64
px and up, and the favicons, the tile redrawn flat with a larger mark to stay
legible when small, below that (`favicon/favicon-16.png` and `-32.png` as
they are, `favicon-512.png` downscaled for the other sizes). Every downscale
is Lanczos. The outputs are written under `packaging/borer-app/icons/` and
checked in:

- `borer-app.ico`, 16 to 256 px: the icon resource `app/borer-app/build.rs`
  embeds in borer-app.exe, which Windows shows on the window, the taskbar,
  the MSI's Start menu shortcut and its uninstall entry.
- `borer-app.icns`, 16 to 512 px: the icon of the macOS borer.app bundle.
  It leaves out 1024 px (512 at 2x), the size the grain texture makes large.
- `<n>.png` at the hicolor sizes 16 to 256: the Linux tarball installs them
  beside `borer-app.desktop`, and the app gives the 128 px one to X11 as its
  window icon.

Needs Pillow (`pip install pillow`).
"""

from __future__ import annotations

import argparse
import io
import struct
from pathlib import Path

from PIL import Image

OUT = Path(__file__).resolve().parents[2] / "packaging" / "borer-app" / "icons"
"""Where the icons are written."""

SMALL_MAX = 48
"""The largest size drawn from the favicons rather than the app icon."""

ICO_SIZES = (16, 20, 24, 32, 40, 48, 64, 96, 128, 256)
"""The frames of the Windows icon: the shell's small, medium and large sizes
at 100 to 250 percent scaling."""

ICNS_TYPES = (("icp4", 16), ("icp5", 32), ("icp6", 64), ("ic07", 128), ("ic08", 256), ("ic09", 512))
"""The PNG entries of the macOS icon, by OSType and size."""

PNG_SIZES = (16, 32, 48, 64, 128, 256)
"""The hicolor theme sizes the Linux icons are written at."""


def png(image: Image.Image) -> bytes:
    """Returns `image` encoded as an optimized PNG."""
    out = io.BytesIO()
    image.save(out, "PNG", optimize=True)
    return out.getvalue()


def main() -> None:
    """Reads the brand assets and writes every output."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("assets", type=Path, help="borer-web's packages/brand/assets directory")
    args = parser.parse_args()

    def load(name: str, size: int) -> Image.Image:
        image = Image.open(args.assets / name).convert("RGBA")
        if image.size != (size, size):
            parser.error(f"{name} is {image.size[0]}x{image.size[1]}, not {size}x{size}")
        return image

    exact = {16: load("favicon/favicon-16.png", 16), 32: load("favicon/favicon-32.png", 32)}
    small = load("favicon/favicon-512.png", 512)
    large = load("logo/icon-1024.png", 1024)

    def icon(size: int) -> Image.Image:
        if size in exact:
            return exact[size]
        source = small if size <= SMALL_MAX else large
        return source.resize((size, size), Image.Resampling.LANCZOS)

    OUT.mkdir(parents=True, exist_ok=True)
    frames = [icon(size) for size in ICO_SIZES]
    frames[-1].save(
        OUT / "borer-app.ico",
        sizes=[(size, size) for size in ICO_SIZES],
        append_images=frames[:-1],
    )
    entries = b"".join(
        kind.encode("ascii") + struct.pack(">I", 8 + len(data)) + data
        for kind, data in ((kind, png(icon(size))) for kind, size in ICNS_TYPES)
    )
    (OUT / "borer-app.icns").write_bytes(b"icns" + struct.pack(">I", 8 + len(entries)) + entries)
    for size in PNG_SIZES:
        (OUT / f"{size}.png").write_bytes(png(icon(size)))


if __name__ == "__main__":
    main()
