"""A baseline of counts that may shrink and never grow, shared by the checks
that hold a debt to its recorded size.

A baseline is a `#` line, then `key<TAB>count` rows. The check fails when a
count is above its row or has none, and when a row is above its count, until
`--record` lowers it: the baseline is always today's numbers, so a debt paid
cannot come back. `--record` lowers rows and drops the ones that left. It
never raises a row, and it adds one only in place of a row that left in the
same run and was at least as large (a rename or a move), which it names.
"""

from __future__ import annotations

from pathlib import Path


def read(baseline: Path) -> dict[str, int]:
    """Returns the baseline's rows, none when the file is missing."""
    rows: dict[str, int] = {}
    if baseline.exists():
        for line in baseline.read_text(encoding="utf-8").splitlines():
            if line and not line.startswith("#"):
                key, n = line.split("\t")
                rows[key] = int(n)
    return rows


def moved(new: dict[str, int], gone: dict[str, int]) -> list[tuple[str, str | None]]:
    """Pairs each key new to the baseline with a row that left it, largest first.

    A pair's second half is `None` when no row is left, or the largest left
    is smaller than the new key: that key grew or is new debt.
    """
    left = sorted(gone, key=lambda k: (-gone[k], k))
    pairs: list[tuple[str, str | None]] = []
    for k in sorted(new, key=lambda k: (-new[k], k)):
        fits = bool(left) and gone[left[0]] >= new[k]
        pairs.append((k, left.pop(0) if fits else None))
    return pairs


def run(baseline: Path, head: str, now: dict[str, int], argv: list[str], unit: str) -> int:
    """Checks today's counts against the baseline, or records them under `--record`.

    `head` is the baseline's first line and `unit` what a count is called.
    Returns the exit status: 0 when the counts are the baseline's, or were recorded.
    """
    base = read(baseline)
    new = {k: n for k, n in now.items() if k not in base}
    gone = {k: n for k, n in base.items() if k not in now}
    grew = [
        f"{k}: {n} {unit}, recorded {base[k]}" for k, n in sorted(now.items()) if n > base.get(k, n)
    ]
    if "--record" in argv:
        pairs = moved(new, gone)
        for k, was in pairs:
            if was is not None:
                print(f"{k}: {new[k]} {unit}, recorded in place of {was} ({gone[was]})")
        grew += [
            f"{k}: {new[k]} {unit}, and no row that left covers it"
            for k, was in pairs
            if was is None
        ]
        for line in grew:
            print(line)
        if grew:
            print("nothing recorded: `--record` never raises a row or adds one")
            return 1
        rows = [f"{k}\t{n}" for k, n in sorted(now.items())]
        baseline.write_text("\n".join([head, *rows]) + "\n", encoding="utf-8", newline="\n")
        print(f"recorded {len(rows)} rows")
        return 0
    grew += [f"{k}: {n} {unit}, not in the baseline" for k, n in sorted(new.items())]
    stale = [
        f"{k}: recorded {n}, now {now[k]}" for k, n in sorted(base.items()) if n > now.get(k, n)
    ]
    stale += [f"{k}: recorded {n}, no longer over" for k, n in sorted(gone.items())]
    for line in grew + stale:
        print(line)
    if grew:
        print("pay the debt down; `--record` only when a row was renamed or moved")
    if stale:
        print("the baseline is above the code: run `--record` to lower it")
    return 1 if grew or stale else 0
