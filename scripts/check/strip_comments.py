#!/usr/bin/env python3
"""Remove line notes from the Rust sources.

Rustdoc (`///`, `//!`, `/**`, `/*!`) stays. So does a `// SAFETY:` or
`// ASM:` note, including the `//` lines that continue a whole-line one.
Every other `//` comment and every `/* */` block comment is deleted.
Strings, character literals and lifetimes are not comments.

Usage: python scripts/check/strip_comments.py [--check]
`--check` exits 1 when a file would change and writes nothing.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.root import ROOT  # noqa: E402

CRATES = ROOT / "crates"


def strip(src: str) -> str:
    """Returns `src` with the comments this script removes taken out."""
    out: list[str] = []
    i = 0
    n = len(src)
    while i < n:
        j = i
        while j < n and src[j] not in "\"'/":
            j += 1
        if j > i:
            out.append(src[i:j])
            i = j
        if i >= n:
            break
        if src.startswith("//", i):
            i = _line_comment(src, i, out)
            continue
        if src.startswith("/*", i):
            i = _block_comment(src, i, out)
            continue
        if src[i] == '"':
            end = _string_end(src, i)
            out.append(src[i:end])
            i = end
            continue
        if src[i] == "'":
            end = _char_end(src, i)
            if end > i:
                out.append(src[i:end])
                i = end
                continue
        out.append(src[i])
        i += 1
    return "".join(out)


def _line_comment(src: str, i: int, out: list[str]) -> int:
    end = _eol(src, i)
    if _is_line_doc(src, i) or _kept_tag(src, i, end):
        block_end = end
        if _kept_tag(src, i, end) and _whole_line(src, i):
            block_end = _kept_block_end(src, i)
        out.append(src[i:block_end])
        return block_end
    if _whole_line(src, i):
        _trim_indent(out)
        return end + 1 if end < len(src) else end
    _trim_indent(out)
    return end


def _block_comment(src: str, i: int, out: list[str]) -> int:
    end = _block_end(src, i)
    if _is_block_doc(src, i):
        out.append(src[i:end])
        return end
    if _whole_line(src, i) and _only_ws_to_eol(src, end):
        _trim_indent(out)
        if end < len(src) and src[end] == "\n":
            return end + 1
        return end
    if not _whole_line(src, i):
        _trim_indent(out)
    return end


def _is_line_doc(src: str, i: int) -> bool:
    """`///` and `//!` are rustdoc. `////` is an ordinary comment."""
    if src.startswith("//!", i):
        return True
    return src.startswith("///", i) and not src.startswith("////", i)


def _is_block_doc(src: str, i: int) -> bool:
    """`/**` and `/*!` are rustdoc. `/***` and `/**/` are ordinary comments."""
    if src.startswith("/*!", i):
        return True
    if not src.startswith("/**", i):
        return False
    nxt = src[i + 3] if i + 3 < len(src) else ""
    return nxt not in ("*", "/")


def _kept_tag(src: str, i: int, end: int) -> bool:
    text = src[i + 2 : end].lstrip()
    return text.startswith(("SAFETY:", "ASM:"))


def _kept_block_end(src: str, start: int) -> int:
    """The end of a kept note, including continuation `//` lines."""
    i = start
    n = len(src)
    while i < n and src.startswith("//", i):
        end = _eol(src, i)
        nxt = end + 1
        nxt_code = _skip_ws(src, nxt)
        continues = (
            nxt_code < n and src.startswith("//", nxt_code) and not _is_line_doc(src, nxt_code)
        )
        if continues:
            i = nxt_code
            continue
        return end
    return i


def _block_end(src: str, i: int) -> int:
    """The index after a block comment, which nests."""
    depth = 0
    j = i
    n = len(src)
    while j < n - 1:
        if src.startswith("/*", j):
            depth += 1
            j += 2
            continue
        if src.startswith("*/", j):
            depth -= 1
            j += 2
            if depth == 0:
                return j
            continue
        j += 1
    return n


def _string_end(src: str, quote: int) -> int:
    """The index after the string whose opening quote is at `quote`."""
    hashes = _raw_hashes(src, quote)
    if hashes is not None:
        closer = '"' + ("#" * hashes)
        end = src.find(closer, quote + 1)
        return len(src) if end < 0 else end + len(closer)
    return _cooked_end(src, quote)


def _raw_hashes(src: str, quote: int) -> int | None:
    """The hash count of a raw string opening at `quote`, else None."""
    k = quote
    hashes = 0
    while k > 0 and src[k - 1] == "#":
        hashes += 1
        k -= 1
    if _raw_prefix_at(src, k):
        return hashes
    return None


def _raw_prefix_at(src: str, k: int) -> bool:
    """Whether `r`, `br` or `cr` ends at `k`."""
    if k >= 2 and src[k - 2 : k] in ("br", "cr") and not _ident_before(src, k - 2):
        return True
    return k >= 1 and src[k - 1] == "r" and not _ident_before(src, k - 1)


def _ident_before(src: str, k: int) -> bool:
    if k == 0:
        return False
    c = src[k - 1]
    return c == "_" or c.isalnum()


def _cooked_end(src: str, quote: int) -> int:
    """The index after a cooked string. Newlines are part of the literal."""
    j = quote + 1
    n = len(src)
    while j < n:
        c = src[j]
        if c == "\\":
            if j + 1 >= n:
                return n
            nxt = src[j + 1]
            if nxt == "\n":
                j += 2
                continue
            if nxt == "\r":
                j += 3 if j + 2 < n and src[j + 2] == "\n" else 2
                continue
            j += 2
            continue
        if c == '"':
            return j + 1
        j += 1
    return n


def _char_end(src: str, i: int) -> int:
    """The index after a character literal at `i`, else `i`.

    A lifetime (`'a`, `'static`) is not a literal.
    """
    n = len(src)
    if i >= n or src[i] != "'":
        return i
    j = i + 1
    if j >= n:
        return i
    if src[j] == "\\":
        if j + 1 >= n:
            return i
        if src[j + 1] == "u" and j + 2 < n and src[j + 2] == "{":
            close = src.find("}", j + 3)
            if close < 0:
                return i
            j = close + 1
        elif src[j + 1] == "x":
            j += 4
            if j > n:
                return i
        else:
            j += 2
    elif src[j] in ("'", "\n"):
        return i
    else:
        j += 1
    if j < n and src[j] == "'":
        return j + 1
    return i


def _trim_indent(out: list[str]) -> None:
    """Drops the indent already copied for a comment that occupied its line."""
    while out:
        stripped = out[-1].rstrip(" \t")
        if stripped == out[-1]:
            return
        if stripped:
            out[-1] = stripped
            return
        out.pop()


def _only_ws_to_eol(src: str, i: int) -> bool:
    n = len(src)
    while i < n and src[i] in " \t":
        i += 1
    return i == n or src[i] == "\n"


def _eol(src: str, i: int) -> int:
    end = src.find("\n", i)
    return len(src) if end < 0 else end


def _skip_ws(src: str, i: int) -> int:
    while i < len(src) and src[i] in " \t":
        i += 1
    return i


def _whole_line(src: str, i: int) -> bool:
    j = i
    while j > 0 and src[j - 1] in " \t":
        j -= 1
    return j == 0 or src[j - 1] == "\n"


def _self_check() -> None:
    src = (
        "/// Keeps this.\n"
        "//// not doc\n"
        "fn f() {\n"
        "    // a note\n"
        '    let s = "http://x/*no*/"; // trailing\n'
        '    let q = "say \\"http://x\\" now";\n'
        '    let r = r#" // not a comment "#;\n'
        '    let raw = r"http://keep";\n'
        '    let bytes = b"\\"borer://x\\"";\n'
        '    let wide = br#" // x "#;\n'
        "    // SAFETY: the pointer is live\n"
        "    // for this call.\n"
        "    let b = [0x90]; // ASM: nop\n"
        "    // ---- section ----\n"
        "    let c = '\\\\n';\n"
        "    let u = '\\u{41}';\n"
        "    fn g<'a>(x: &'a str) -> &'a str { x }\n"
        "    let raw_ident = r#type;\n"
        '    let help = "\\\n'
        'query(\\"borer://grep/CreateFileA\\");\n'
        '";\n'
        '    let multi = "head\n// kept\n"; // trailing\n'
        "    /* outer /* inner */ still */\n"
        "    let x = 1; /* gone */\n"
        "    /** kept doc */\n"
        "    /*** dropped */\n"
        "    let y = 2;\n"
        '    let dash = "em — café";\n'
        "}\n"
    )
    got = strip(src)
    expect = (
        "/// Keeps this.\n"
        "fn f() {\n"
        '    let s = "http://x/*no*/";\n'
        '    let q = "say \\"http://x\\" now";\n'
        '    let r = r#" // not a comment "#;\n'
        '    let raw = r"http://keep";\n'
        '    let bytes = b"\\"borer://x\\"";\n'
        '    let wide = br#" // x "#;\n'
        "    // SAFETY: the pointer is live\n"
        "    // for this call.\n"
        "    let b = [0x90]; // ASM: nop\n"
        "    let c = '\\\\n';\n"
        "    let u = '\\u{41}';\n"
        "    fn g<'a>(x: &'a str) -> &'a str { x }\n"
        "    let raw_ident = r#type;\n"
        '    let help = "\\\n'
        'query(\\"borer://grep/CreateFileA\\");\n'
        '";\n'
        '    let multi = "head\n// kept\n";\n'
        "    let x = 1;\n"
        "    /** kept doc */\n"
        "    let y = 2;\n"
        '    let dash = "em — café";\n'
        "}\n"
    )
    if got != expect:
        raise SystemExit(f"strip self-check failed:\n{got}")
    if strip(got) != got:
        raise SystemExit("strip is not idempotent")


def main(argv: list[str]) -> int:
    _self_check()
    check = "--check" in argv
    changed = 0
    for path in sorted(CRATES.rglob("*.rs")):
        src = path.read_text(encoding="utf-8")
        nxt = strip(src)
        if nxt == src:
            continue
        changed += 1
        if not check:
            path.write_text(nxt, encoding="utf-8", newline="\n")
    print(f"{changed} files {'would change' if check else 'rewritten'}")
    return 1 if check and changed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
