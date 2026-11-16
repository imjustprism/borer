#!/usr/bin/env python3
"""Hold the duplicated Rust lines to a recorded count, with a ratchet.

    python scripts/check/dupes.py           fail when the count is not the recorded one
    python scripts/check/dupes.py --record  lower the recorded count to today's

The count is the duplicated lines jscpd 4.0.5 reports over every tracked file
that `.jscpd.json`'s `pattern` names, with that file's token and line floors,
computed here instead of by jscpd: its Prism Rust grammar (reprism 0.0.11,
with jscpd's ignore markers and whitespace tokens) tokenizes each file, and
its Rabin-Karp pass counts a clone's lines in the file read later. The scan
reads the files in the order jscpd read the sorted list it was handed (by
parent directory in order of first appearance, then last to first), since a
clone counts against the files read earlier. `dupes.tsv` holds the count:
more duplicated lines fail, and so do fewer until `--record` lowers the
number, so it is always today's and can only shrink (ratchet.py). A file
above `maxLines` or `maxSize` fails the check, and so does one holding a
`jscpd:ignore` marker.

The port has one known divergence from jscpd: an ignore block with an empty
body (`jscpd:ignore-start` straight before `jscpd:ignore-end`). There jscpd
emits an empty token whose value is not text and whose line count runs one
backwards, and the port does not. Since no tracked file may hold a marker,
the case cannot reach the count.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from array import array
from concurrent.futures import ProcessPoolExecutor
from functools import partial
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check import ratchet  # noqa: E402
from harness.root import ROOT  # noqa: E402

BASELINE = Path(__file__).with_name("dupes.tsv")
"""The duplicated lines recorded, which the count may not exceed."""

HEAD = "# duplicated lines jscpd finds in the tracked Rust: may shrink, never grow"
"""The baseline's first line."""

SPACE = "\\t\\n\\v\\f\\r \\u00a0\\u1680\\u2000-\\u200a\\u2028\\u2029\\u202f\\u205f\\u3000\\ufeff"
"""JavaScript's `\\s` class, which Python's differs from."""

DOT = "[^\\n\\r\\u2028\\u2029]"
"""JavaScript's `.`, which also stops at `\\r` and the Unicode line breaks."""

KEYWORDS = (
    "abstract|alignof|as|be|box|break|const|continue|crate|do|else|enum|extern|false|final|fn|"
    "for|if|impl|in|let|loop|match|mod|move|mut|offsetof|once|override|priv|pub|pure|ref|return|"
    "sizeof|static|self|struct|super|true|trait|type|typeof|unsafe|unsized|use|virtual|where|"
    "while|yield"
)
"""Prism's Rust keywords."""


class Pattern:
    """One Prism pattern: its regex and the flags that steer the match.

    `WS` and `DOT` in `rx` stand for JavaScript's `\\s` and `.`; `\\w`, `\\d`
    and `\\b` are ASCII, as in JavaScript.
    """

    def __init__(self, rx: str, lookbehind=False, greedy=False, inside=None) -> None:
        self.rx = re.compile(rx.replace("WS", f"[{SPACE}]").replace("DOT", DOT), re.ASCII)
        self.lookbehind = lookbehind
        self.greedy = greedy
        self.inside = inside


CLOSURE = [("punctuation", [Pattern(r"[|:,]")]), ("operator", [Pattern(r"[&*]")])]
"""The grammar inside closure parameters."""

GRAMMAR = [
    (
        "ignore",
        [
            Pattern(r"(jscpd:ignore-start)[\s\S]*?(?=jscpd:ignore-end)", True, True),
            Pattern(r"jscpd:ignore-start"),
            Pattern(r"jscpd:ignore-end"),
        ],
    ),
    (
        "comment",
        [Pattern(r"(^|[^\\])/\*[\s\S]*?\*/", True), Pattern(r"(^|[^\\:])//DOT*", True)],
    ),
    (
        "string",
        [
            Pattern(r'b?r(#*)"(?:\\DOT|(?!"\1)[^\\\r\n])*"\1', greedy=True),
            Pattern(r'b?"(?:\\DOT|[^\\\r\n"])*"', greedy=True),
        ],
    ),
    (
        "char",
        [Pattern(r"b?'(?:\\(?:x[0-7][\da-fA-F]|u\{(?:[\da-fA-F]_*){1,6}|DOT)|[^\\\r\n\t'])'")],
    ),
    ("lifetime-annotation", [Pattern(f"'[^{SPACE}>']+")]),
    ("keyword", [Pattern(f"\\b(?:{KEYWORDS})\\b")]),
    ("attribute", [Pattern(r"#!?\[DOT+?\]", greedy=True)]),
    ("function", [Pattern(r"\w+(?=WS*\()"), Pattern(r"\w+!(?=WS*\(|\[)")]),
    ("macro-rules", [Pattern(r"\w+!")]),
    (
        "number",
        [
            Pattern(
                r"\b(?:0x[\dA-Fa-f](?:_?[\dA-Fa-f])*|0o[0-7](?:_?[0-7])*|0b[01](?:_?[01])*"
                r"|(\d(?:_?\d)*)?\.?\d(?:_?\d)*(?:[Ee][+-]?\d+)?)(?:_?(?:[iu](?:8|16|32|64)?|f32|f64))?\b"
            )
        ],
    ),
    ("closure-params", [Pattern(r"\|[^|]*\|(?=WS*[{-])", inside=CLOSURE)]),
    ("punctuation", [Pattern(r"[{}\[\];(),:]|\.+|->")]),
    ("operator", [Pattern(r"[-+*/%!^]=?|=[=>]?|@|&[&=]?|\|[|=]?|<<?=?|>>?=?")]),
    ("new_line", [Pattern(r"\n")]),
    ("empty", [Pattern(r"WS+")]),
]
"""jscpd's Rust grammar: its ignore markers, Prism's Rust tokens, then whitespace, in match order."""

MARKER = "jscpd:ignore"
"""The prefix of jscpd's ignore markers, which no tracked file may hold: the
text between them leaves the count, even inside a comment or rustdoc."""

SKIPPED = {"ignore", "new_line", "empty"}
"""The token types jscpd's default `mild` mode leaves out of a clone."""


class Token:
    """A Prism token: its type, its text or nested tokens, and the length it matched."""

    __slots__ = ("type", "content", "length", "greedy")

    def __init__(self, kind: str, content, length: int, greedy: bool) -> None:
        self.type = kind
        self.content = content
        self.length = length
        self.greedy = greedy


def size(item) -> int:
    """Returns the characters an entry of Prism's token list covers."""
    return item.length if isinstance(item, Token) else len(item)


def split_all(items: list, name: str, pat: Pattern) -> list:
    """Returns `items` with every string split at each match of a non-greedy pattern.

    This is Prism's pass for such a pattern over the whole list: each string
    is matched, and what follows a match is matched again on its own.
    """
    out: list = []
    for item in items:
        if isinstance(item, Token):
            out.append(item)
            continue
        while item:
            m = pat.rx.search(item)
            if not m:
                out.append(item)
                break
            start = m.start() + (len(m.group(1) or "") if pat.lookbehind else 0)
            if start > 0:
                out.append(item[:start])
            text = item[start : m.end()]
            out.append(
                Token(name, tokenize(text, pat.inside) if pat.inside else text, len(text), False)
            )
            item = item[m.end() :]
    return out


def match_grammar(text, items, grammar, index, pos0, oneshot, target) -> None:
    """Runs Prism's `matchGrammar` over `items` in place, one pattern after another."""
    for name, pats in grammar:
        if name == target:
            continue
        for pat in pats:
            if not oneshot and not pat.greedy:
                items[:] = split_all(items, name, pat)
                continue
            i, pos = index, pos0
            while i < len(items):
                s = items[i]
                if isinstance(s, Token):
                    pos, i = pos + s.length, i + 1
                    continue
                if pat.greedy and i != len(items) - 1:
                    m = pat.rx.search(text, pos)
                    if not m:
                        break
                    start = m.start() + (len(m.group(1)) if pat.lookbehind else 0)
                    k, p = i, pos
                    while k < len(items) and (
                        p < m.end()
                        or not isinstance(items[k], Token)
                        and not (isinstance(items[k - 1], Token) and items[k - 1].greedy)
                    ):
                        p += size(items[k])
                        if start >= p:
                            i, pos = i + 1, p
                        k += 1
                    if isinstance(items[i], Token):
                        pos, i = pos + items[i].length, i + 1
                        continue
                    span, s, at = k - i, text[pos:p], m.start() - pos
                else:
                    m = pat.rx.search(s)
                    if not m:
                        if oneshot:
                            break
                        pos, i = pos + len(s), i + 1
                        continue
                    span, at = 1, m.start()
                behind = len(m.group(1) or "") if pat.lookbehind else 0
                matched = m.group(0)[behind:]
                start = at + behind
                end = start + len(matched)
                at_i = i
                args: list = []
                if start > 0:
                    i, pos = i + 1, pos + start
                    args.append(s[:start])
                inner = tokenize(matched, pat.inside) if pat.inside else matched
                args.append(Token(name, inner, len(matched), pat.greedy))
                if s[end:]:
                    args.append(s[end:])
                items[at_i : at_i + span] = args
                if span != 1:
                    match_grammar(text, items, grammar, i, pos, True, name)
                if oneshot:
                    break
                pos, i = pos + items[i].length, i + 1


def tokenize(text: str, grammar) -> list:
    """Returns Prism's token list for `text`: tokens and the plain strings between them."""
    items: list = [text]
    match_grammar(text, items, grammar, 0, 0, False, None)
    return items


def flatten(items, out: list[tuple[str, str]]) -> None:
    """Appends jscpd's flat `(type, text)` tokens for Prism's list; a plain string is `default`."""
    for item in items:
        if not isinstance(item, Token):
            out.append(("default", item))
        elif isinstance(item.content, str):
            out.append((item.type, item.content))
        else:
            flatten(item.content, out)


def utf16(text: str) -> str:
    """Returns `text` as JavaScript sees it: one character per UTF-16 code unit."""
    if text.isascii() or max(text) <= "\uffff":
        return text
    units = text.encode("utf-16-le", "surrogatepass")
    return "".join(chr(int.from_bytes(units[j : j + 2], "little")) for j in range(0, len(units), 2))


def tokens(text: str) -> tuple[list[int], list[int], list[str]]:
    """Returns the kept tokens' start lines, end lines and `type` + text keys, as jscpd counts them."""
    flat: list[tuple[str, str]] = []
    flatten(tokenize(utf16(text), GRAMMAR), flat)
    starts, ends, keys = [], [], []
    line = 1
    for kind, value in flat:
        first = line
        line += value.count("\n")
        if kind not in SKIPPED:
            starts.append(first)
            ends.append(line)
            keys.append(kind + "\0" + value)
    return starts, ends, keys


def read_order(files: list[str]) -> list[str]:
    """Returns `files` in the order jscpd reads them: grouped by parent directory, then reversed."""
    groups: dict[str, list[str]] = {}
    for f in files:
        groups.setdefault(f.rpartition("/")[0], []).append(f)
    return [f for group in groups.values() for f in group][::-1]


def git_globs(pattern: str) -> list[str]:
    """Expands one optional `{a,b}` brace group in `pattern` into `git ls-files` globs."""
    m = re.search(r"\{([^{}]+)\}", pattern)
    if not m:
        return [f":(glob){pattern}"]
    head, tail = pattern[: m.start()], pattern[m.end() :]
    return [f":(glob){head}{part}{tail}" for part in m.group(1).split(",")]


def lex(root: Path, path: str) -> tuple[int, int, bool, tuple[list[int], list[int], list[str]]]:
    """Returns a tracked file's size in bytes, its line count, whether it holds
    a `jscpd:ignore` marker, and its [`tokens`]."""
    raw = (root / path).read_bytes()
    text = raw.decode("utf-8", "replace")
    return len(raw), text.count("\n") + 1, MARKER in text, tokens(text)


def scan(root: Path = ROOT) -> dict[str, int]:
    """Returns the files read, the clones and the duplicated lines over the tracked files.

    Files are tokenized in parallel and scanned in jscpd's order.
    """
    config = json.loads((root / ".jscpd.json").read_text(encoding="utf-8"))
    floor, min_lines = config["minTokens"], config["minLines"]
    size_cap = int(config["maxSize"].removesuffix("mb")) << 20
    listing = subprocess.run(
        ["git", "ls-files", "-z", "--", *git_globs(config["pattern"])],
        cwd=root,
        capture_output=True,
        check=True,
    ).stdout.decode("utf-8")
    order = read_order(sorted({p for p in listing.split("\0") if p}))
    seen: set[bytes] = set()
    interned: dict[str, int] = {}
    total = {"sources": 0, "clones": 0, "duplicated": 0}
    with ProcessPoolExecutor() as pool:
        lexed = pool.map(partial(lex, root), order, chunksize=4)
        for path, (size, lines, marked, (starts, ends, keys)) in zip(order, lexed, strict=True):
            if size > size_cap or lines > config["maxLines"]:
                sys.exit(f"{path}: {lines} lines, {size} bytes: lift the caps in .jscpd.json")
            if marked:
                sys.exit(f"{path}: holds `{MARKER}`, which would hide its clones from the count")
            if lines < min_lines or not keys:
                continue
            ids = array("I", (interned.setdefault(k, len(interned)) for k in keys)).tobytes()
            found = [n for n in clones(ids, starts, ends, seen, floor) if n >= min_lines]
            total["sources"] += 1
            total["clones"] += len(found)
            total["duplicated"] += sum(found)
    return total


def clones(ids: bytes, starts: list[int], ends: list[int], seen: set[bytes], floor: int):
    """Yields the lines each clone in one file spans, as jscpd's Rabin-Karp pass finds them.

    `ids` holds the file's interned tokens, four bytes each, and `seen` the
    windows of `floor` tokens read so far, which it adds this file's new ones
    to. A run of windows seen before is one clone, from its first window's
    first line to the line after its last window ends (jscpd's frame ends one
    token late); the file's last window is never compared.
    """
    first, last = None, 0
    for p in range(len(starts) - floor):
        frame = hashlib.blake2b(ids[4 * p : 4 * (p + floor)], digest_size=16).digest()
        if frame in seen:
            first = starts[p] if first is None else first
            last = ends[p + floor]
            continue
        if first is not None:
            yield last - first
        first = None
        seen.add(frame)
    if first is not None:
        yield last - first


def main(argv: list[str]) -> int:
    total = scan()
    print(f"{total['sources']} files, {total['clones']} clones")
    return ratchet.run(BASELINE, HEAD, {"duplicated": total["duplicated"]}, argv, "lines")


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
