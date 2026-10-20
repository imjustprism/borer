#!/usr/bin/env python3
"""Mechanical readability metrics for borer's pseudo-C, with a baseline gate.

Usage:
  python scripts/run/readability.py run <borer.exe> [--baseline FILE [--update]]
                                [--only TAG,TAG] [--out DIR] [--quiet]
  python scripts/run/readability.py measure <dir> [--source <tag>=<file.c> ...] [--tsv FILE]
  (both take --examples N: example lines printed per pattern, default 2)

`run` decompiles a deterministic sample of each input in INPUTS (all its
functions up to WANT, else every k-th by entry, functions over INSTR_MAX
instructions left out), one MCP session per binary, and measures it. With
--baseline (the gate passes scripts/run/readability.tsv) it compares the counts
with the stored ones, prints every metric that moved as better, worse or
WORSE, and exits 1 when any is WORSE: beyond its tolerance (see `compare`);
--update merges this run's rows into the baseline instead, which a commit
that moves a metric does in the same commit. The sqlite inputs are read from
BORER_READABILITY_CORPUS (a folder holding sqlite3.x64.elf, sqlite3.full.elf
and sqlite3.c) and skipped without it; every missing input prints `[skip]`.
`measure` reads dumps `==== <entry> <name> <instrs>` + text, as --out writes
them.

The table prints rates per 100 body lines; the baseline stores counts over
the sample, so a change that deletes noise lines does not raise every other
rate with it. Two runs print the same rows.

Every metric is a pure function of the text: no human judging, no timing.
Each is a count per 100 body lines (declarations and the `//` header apart).
Names follow the decompiler's conventions: registers as variables (`rax`,
`x0`, `xmm0`), stack slots `local_N`/`home_N`, temporaries `tmp_N`,
parameters `aN`, unnamed callees `sub_<hex>`, a second call result
`f__rdx(...)`, unproven flow `goto L_<hex>` and `/* asm: ... */` for an
unmodelled instruction.

Source distance (a binary built with symbols from a C file beside it): every
decompiled function whose name the file defines is compared with its
definition: statements, lines, distinct variables, calls and brace depth as
decompiled / source (median and geometric mean), the share of signatures with
the source's arity, gotos beyond the source's, and the share of calls to a
function the file defines whose argument count differs from its definition.
"""

from __future__ import annotations

import collections
import hashlib
import math
import os
import re
import subprocess
import sys
import time
from pathlib import Path

# ---- lexical sets ----

X64_REGS = {
    *[
        "rax",
        "rbx",
        "rcx",
        "rdx",
        "rsi",
        "rdi",
        "rbp",
        "rsp",
        "eax",
        "ebx",
        "ecx",
        "edx",
        "esi",
        "edi",
        "ebp",
        "esp",
    ],
    *[
        "ax",
        "bx",
        "cx",
        "dx",
        "si",
        "di",
        "bp",
        "sp",
        "al",
        "bl",
        "cl",
        "dl",
        "ah",
        "bh",
        "ch",
        "dh",
        "sil",
        "dil",
        "bpl",
        "spl",
    ],
    *(f"r{i}" for i in range(8, 16)),
    *(f"r{i}{s}" for i in range(8, 16) for s in ("d", "w", "b")),
    *(f"xmm{i}" for i in range(32)),
    *(f"ymm{i}" for i in range(32)),
    *(f"st{i}" for i in range(8)),
}
A64_REGS = {
    *(f"{p}{i}" for p in "xwvqdsh" for i in range(32)),
    "sp",
    "fp",
    "lr",
    "xzr",
    "wzr",
}
REGS = X64_REGS | A64_REGS
CALLEE_SAVED = {
    *["rbx", "rbp", "r12", "r13", "r14", "r15", "rsi", "rdi", "ebx", "ebp", "esi", "edi"],
    *(f"x{i}" for i in range(19, 31)),
}
FLOAT_REGS = re.compile(r"^(?:xmm\d+|ymm\d+|st\d|[vqdsh]\d+)$")
KEYWORDS = {
    *[
        "if",
        "else",
        "while",
        "for",
        "do",
        "switch",
        "case",
        "default",
        "break",
        "continue",
        "return",
        "goto",
        "sizeof",
    ],
    *[
        "void",
        "char",
        "short",
        "int",
        "long",
        "unsigned",
        "signed",
        "float",
        "double",
        "struct",
        "union",
        "enum",
        "const",
    ],
    *[
        "uint8_t",
        "uint16_t",
        "uint32_t",
        "uint64_t",
        "int8_t",
        "int16_t",
        "int32_t",
        "int64_t",
        "uintptr_t",
    ],
    *["intptr_t", "size_t", "bool", "true", "false", "this"],
}
TYPES = re.compile(r"\b(?:u?int(?:8|16|32|64|ptr)_t|void|char|float|double|bool|size_t)\b")

IDENT = re.compile(r"[A-Za-z_]\w*")
STRING = re.compile(r'"(?:[^"\\]|\\.)*"' r"|'(?:[^'\\]|\\.)*'")
BLOCK_COMMENT = re.compile(r"/\*.*?\*/")
# The C definitions of the helpers a text calls, which follow its header:
# no declaration of the function's own.
HELPER_DEFINITION = ("static inline ", "#define ", "#undef ", "extern ")
ASSIGN = re.compile(r"^((?:[A-Za-z_]\w*\s*=(?!=)\s*)+)(.*);$")
COMPOUND = re.compile(r"^([A-Za-z_]\w*)\s*(?:[-+*/%&|^]|<<|>>)=\s*(.*);$")
INCDEC = re.compile(r"^([A-Za-z_]\w*)\s*(?:\+\+|--);$")
CALL = re.compile(r"([A-Za-z_][\w:~<>]*)\s*\(")
PHANTOM = re.compile(r"^\s*([A-Za-z_]\w*)\s*=\s*[\w:~]+__(?:rdx|edx|x1)\(")
DEREF_CAST = re.compile(r"\*\s*\(\s*(?:const\s+)?[A-Za-z_]\w*\s*\*+\s*\)")
INDEX_CAST = re.compile(r"\(\(\s*[A-Za-z_]\w*\s*\*+\s*\)")
VALUE_CAST = re.compile(r"\((?:u?int(?:8|16|32|64)_t)\)\s*[\w(*]")
ABS_DEREF = re.compile(
    r"\*\s*\(\s*\w+\s*\*\s*\)\s*\(?0x[0-9a-f]{5,}|\(\(\s*\w+\s*\*\s*\)\s*\(?0x[0-9a-f]{5,}"
)
MASK = re.compile(r"&\s*0x(?:ff|ffff|ffffffff)\b(?!\w)")
PARTIAL = re.compile(r"&\s*~0x(?:ff|ffff|ff00)\)\s*\|")
GOTO = re.compile(r"\bgoto\s+L_[0-9a-f]+\s*;")
LABEL = re.compile(r"^L_[0-9a-f]+:$")
SLOT = re.compile(r"^(?:local|home|stack|arg|var)_[0-9a-f]+$")
TMP = re.compile(r"^tmp_\d+$")
PARAM = re.compile(r"^a\d+$")
GLOBAL_AUTO = re.compile(r"^g(?:8|16|32|64|f32|f64)?_[0-9a-f]+$")
SUB_CALL = re.compile(r"\bsub_[0-9a-f]+\s*\(")
NUMBER = re.compile(r"^-?(?:0x[0-9a-f]+|\d+)$")
CAMEL_API = re.compile(r"^[A-Z][a-z0-9]+[A-Z]\w*$")
CONTROL = re.compile(r"^(?:if|while|for|switch|do|else|case|default)\b|^\}")
ESCAPE_NOTE = re.compile(r"&(local_[0-9a-f]+|home_[0-9a-f]+) escapes")

# ---- parsing ----


class Function:
    """One decompiled function split into header, declarations and body."""

    def __init__(self, entry: str, name: str, text: str):
        self.entry = entry
        self.name = name
        self.text = text
        self.header: list[str] = []
        self.decls: list[str] = []
        self.body: list[str] = []
        lines = [ln for ln in text.split("\n") if not ln.startswith("# since=")]
        while lines and not lines[-1].strip():
            lines.pop()
        i = 0
        while i < len(lines) and lines[i].startswith("//"):
            self.header.append(lines[i])
            i += 1
        while i < len(lines) and lines[i].startswith(HELPER_DEFINITION):
            i += 1
        while i < len(lines) and lines[i].strip():
            self.decls.append(lines[i])
            i += 1
        while i < len(lines) and not lines[i].strip():
            i += 1
        self.body = lines[i:]


def split_dump(path: str) -> list[Function]:
    """Reads a `collect` output file into its functions."""
    with open(path, encoding="utf-8") as f:
        chunks = f.read().split("==== ")
    out = []
    for ch in chunks:
        if not ch.strip():
            continue
        head, _, text = ch.partition("\n")
        parts = head.split()
        out.append(Function(parts[0], parts[1] if len(parts) > 1 else "", text))
    return out


def clean(line: str) -> str:
    """Drops strings and comments so identifiers are real ones."""
    s = STRING.sub('""', line)
    s = BLOCK_COMMENT.sub(" ", s)
    i = s.find("//")
    if i >= 0:
        s = s[:i]
    return s.strip()


def declared(fn: Function) -> tuple[dict[str, str], list[tuple[str, str]], int]:
    """Variables the declarations name: {name: type}, global decls, comment lines."""
    names: dict[str, str] = {}
    globals_: list[tuple[str, str]] = []
    comments = 0
    for d in fn.decls:
        s = d.strip()
        if s.startswith("//"):
            comments += 1
            continue
        m = re.match(r"^(.*?)\s*;\s*(//.*)?$", s)
        if not m:
            continue
        body, comment = m.group(1), m.group(2) or ""
        tm = re.match(r"^((?:const\s+|struct\s+|unsigned\s+)*[A-Za-z_]\w*)\s+(.*)$", body)
        if not tm:
            continue
        ty, rest = tm.group(1), tm.group(2)
        for part in rest.split(","):
            part = re.sub(r"\[.*?\]", "", part).strip().lstrip("*").strip()
            if IDENT.fullmatch(part):
                names[part] = ty
                if "// @" in comment:
                    globals_.append((part, d))
    return names, globals_, comments


def indent(line: str) -> int:
    return (len(line) - len(line.lstrip(" "))) // 2


class Stmt:
    """One body line with its writes and reads."""

    __slots__ = ("raw", "text", "defs", "reads", "kind", "has_call", "depth", "self_reads")

    def __init__(self, raw: str):
        self.raw = raw
        self.text = clean(raw)
        self.depth = indent(raw)
        self.defs: list[str] = []
        self.reads: collections.Counter = collections.Counter()
        self.self_reads: set[str] = set()
        self.has_call = False
        t = self.text
        if raw.strip().startswith("/* asm"):
            self.kind = "asm"
            return
        if not t:
            self.kind = "comment" if raw.strip() else "blank"
            return
        if LABEL.match(t):
            self.kind = "label"
            return
        if t in ("}", "{", "} else {"):
            self.kind = "brace"
            return
        rhs = t
        if m := ASSIGN.match(t):
            self.defs = [x.strip() for x in m.group(1).split("=") if x.strip()]
            rhs = m.group(2)
            self.kind = "assign"
        elif (m := COMPOUND.match(t)) or (m := INCDEC.match(t)):
            self.defs = [m.group(1)]
            self.self_reads = {m.group(1)}
            rhs = t
            self.kind = "assign"
        elif t.startswith("return"):
            self.kind = "return"
        elif GOTO.search(t) and t.startswith("goto"):
            self.kind = "goto"
        elif CONTROL.match(t):
            self.kind = "control"
        elif t in ("break;", "continue;"):
            self.kind = "jump"
        elif CALL.match(t):
            self.kind = "call"
        else:
            self.kind = "store"
        callees = {m.group(1) for m in CALL.finditer(rhs)}
        self.has_call = any(c not in KEYWORDS and not TYPES.fullmatch(c) for c in callees)
        stripped = re.sub(r"(?:->|\.)\s*[A-Za-z_]\w*", " ", rhs)
        for m in IDENT.finditer(stripped):
            tok = m.group(0)
            nxt = stripped[m.end() :].lstrip()[:1]
            if tok in KEYWORDS or TYPES.fullmatch(tok) or (nxt == "(" and tok in callees):
                continue
            self.reads[tok] += 1


def is_var(name: str, decl: dict[str, str]) -> bool:
    """A name the function owns: a register, slot, temporary or parameter."""
    return (
        name in REGS
        or bool(SLOT.match(name) or TMP.match(name) or PARAM.match(name))
        or (name in decl and not GLOBAL_AUTO.match(name))
    )


def slot_offset(name: str) -> int:
    return int(name.split("_", 1)[1], 16)


# ---- measurement ----

PATTERNS = [
    ("reg_var_lines", "lines naming a raw register as a variable (rax, x0, xmm0, ...)"),
    ("reg_vars", "distinct register variables declared"),
    ("phantom_pair", "second-result lines: v = f__rdx(...)"),
    ("phantom_dead", "of which the second result is never read (or overwritten first)"),
    ("dead_store", "assignments nothing reads (no call on the right)"),
    ("dead_call_result", "v = call(...) where v is never read: the v = is noise"),
    ("float_dead_result", "float register = call(...) never read"),
    ("dead_before_return", "dead assignment straight before a return"),
    ("dead_escaped_slot", "slot stores never read by name, but the slot may escape"),
    ("import_as_var", "declarations of a name the body calls (an import as a variable)"),
    ("global_decl", "global declaration lines (// @ 0x...)"),
    ("overlap_comment", "// x overlaps y declaration comments"),
    ("deref_cast", "*(T*) / ((T*)p)[i] casts"),
    ("value_cast", "(uintN_t)x value casts"),
    ("abs_deref", "dereference of a raw address *(T*)0x..."),
    ("single_use_tmp", "a variable set once and read once on the next line (inlinable)"),
    ("reg_copy", "reg = var; copies into a register or temporary"),
    ("slot_spill", "slot = var; copies into a stack slot"),
    ("callee_save_spill", "slot = a callee-saved register still holding the caller's value"),
    ("align_push", "slot = a scratch register nothing set (a push that only aligns the stack)"),
    ("undef_reg_arg", "call arguments naming a register the function never sets"),
    ("repeated_subexpr", "lines repeating a 24+ char subexpression seen on 3+ lines"),
    ("chain_assign3", "chained assignments of 3+ targets (a = b = c = x)"),
    ("goto", "goto statements"),
    ("label", "labels"),
    ("asm", "/* asm */ lines"),
    ("api_magic", "integer literals (not -1..1) passed to CamelCase APIs"),
    ("mask", "& 0xff / 0xffff / 0xffffffff masks"),
    ("partial_reg", "(v & ~0xff) | ... partial register merges"),
    ("slot_names", "distinct local_N / home_N slot names"),
    ("slot_uses", "local_N / home_N occurrences"),
    ("sub_call", "calls to unnamed sub_<hex>"),
    ("call", "calls of any callee"),
    ("while1", "while (1) loops"),
    ("float_params", "float parameters in the signature"),
]


def measure(fn: Function) -> tuple[collections.Counter, dict[str, list[str]]]:
    """Counts every pattern in one function, with the lines that showed each."""
    c: collections.Counter = collections.Counter()
    ex: dict[str, list[str]] = collections.defaultdict(list)

    def hit(key: str, line: str, n: int = 1) -> None:
        c[key] += n
        if len(ex[key]) < 3:
            ex[key].append(line.strip())

    decl, globals_, comments = declared(fn)
    stmts = [Stmt(ln) for ln in fn.body]
    body = [s for s in stmts if s.kind not in ("blank",)]
    c["functions"] = 1
    c["header_lines"] = len(fn.header)
    c["decl_lines"] = len(fn.decls)
    c["body_lines"] = len(body)
    c["statements"] = sum(s.kind not in ("brace", "comment", "label") for s in body)
    c["overlap_comment"] = comments
    c["max_depth"] = max((s.depth for s in body), default=0)
    sig = next((h for h in fn.header if h.startswith("// signature:")), "")
    c["float_params"] = len(re.findall(r"\b(?:float|double) a\d+", sig))

    reads: collections.Counter = collections.Counter()
    defs: collections.defaultdict[str, list[int]] = collections.defaultdict(list)
    for i, s in enumerate(stmts):
        reads.update(s.reads)
        for v in s.self_reads:
            reads[v] += 0
        for d in s.defs:
            defs[d].append(i)
    text_all = "\n".join(s.text for s in stmts)
    escaped_top = -1
    for h in fn.header:
        for m in ESCAPE_NOTE.finditer(h):
            escaped_top = max(escaped_top, slot_offset(m.group(1)))
    addr_taken = set(re.findall(r"&\s*((?:local|home)_[0-9a-f]+)", text_all))

    def escapes(v: str) -> bool:
        if v in addr_taken:
            return True
        return bool(SLOT.match(v)) and escaped_top >= 0 and slot_offset(v) <= escaped_top

    hands = {"rdx", "edx"} if any(h.startswith("// hands back") for h in fn.header) else set()
    regs = {n for n in decl if n in REGS}
    c["reg_vars"] = len(regs)
    for name, line in globals_:
        hit("global_decl", line)
        if re.search(r"\b" + re.escape(name) + r"\s*\(", text_all):
            hit("import_as_var", line)

    def dead_after(i: int, v: str) -> bool:
        """The value set on line i is overwritten or the function returns before a read."""
        d = stmts[i].depth
        for s in stmts[i + 1 :]:
            if s.kind in ("blank", "comment"):
                continue
            if s.depth != d or s.kind in ("label", "control", "brace", "goto", "jump", "asm"):
                return False
            if s.reads[v] or v in s.self_reads:
                return False
            if s.kind == "return":
                return v not in hands
            if v in s.defs:
                return True
        return False

    for i, s in enumerate(stmts):
        raw = s.raw
        if s.kind == "blank":
            continue
        toks = set(IDENT.findall(s.text))
        if toks & regs or (toks & REGS and any(t in decl for t in toks & REGS)):
            c["reg_var_lines"] += 1
            if len(ex["reg_var_lines"]) < 3:
                ex["reg_var_lines"].append(raw.strip())
        if s.kind == "asm":
            hit("asm", raw)
            continue
        if s.kind == "label":
            hit("label", raw)
            continue
        if GOTO.search(s.text):
            hit("goto", raw)
        if PHANTOM.match(s.text):
            hit("phantom_pair", raw)
        for _ in DEREF_CAST.finditer(s.text):
            hit("deref_cast", raw)
        for _ in INDEX_CAST.finditer(s.text):
            hit("deref_cast", raw)
        for _ in VALUE_CAST.finditer(s.text):
            hit("value_cast", raw)
        for _ in ABS_DEREF.finditer(s.text):
            hit("abs_deref", raw)
        for _ in MASK.finditer(s.text):
            hit("mask", raw)
        if PARTIAL.search(s.text):
            hit("partial_reg", raw)
        if s.text.startswith("while (1)"):
            hit("while1", raw)
        for _ in SUB_CALL.finditer(s.text):
            hit("sub_call", raw)
        for m in CALL.finditer(s.text):
            name = m.group(1)
            if name in KEYWORDS or TYPES.fullmatch(name):
                continue
            c["call"] += 1
            if CAMEL_API.match(name):
                args = call_args(s.text, m.end())
                for a in args:
                    if NUMBER.match(a) and int(a, 0) not in (-1, 0, 1):
                        hit("api_magic", raw)
        for t in toks:
            if SLOT.match(t) and t.startswith(("local_", "home_")):
                c["slot_uses"] += s.text.count(t)
        if len(s.defs) >= 3:
            hit("chain_assign3", raw)
        for m in CALL.finditer(s.text):
            if m.group(1) in KEYWORDS or TYPES.fullmatch(m.group(1)):
                continue
            for a in call_args(s.text, m.end()):
                if a in REGS and not defs.get(a):
                    hit("undef_reg_arg", raw)
        m = ASSIGN.match(s.text)
        if (
            m
            and len(s.defs) == 1
            and IDENT.fullmatch(m.group(2).strip())
            and is_var(m.group(2).strip(), decl)
        ):
            lhs = s.defs[0]
            if lhs in REGS or TMP.match(lhs):
                hit("reg_copy", raw)
            elif SLOT.match(lhs):
                hit("slot_spill", raw)
                src = m.group(2).strip()
                if src in REGS and not any(j < i for j in defs.get(src, [])):
                    if src in CALLEE_SAVED:
                        hit("callee_save_spill", raw)
                    elif reads[lhs] == 0:
                        hit("align_push", raw)
        if pm := PHANTOM.match(s.text):
            v = pm.group(1)
            if v not in hands and (reads[v] == 0 or dead_after(i, v)):
                hit("phantom_dead", raw)
        if s.kind != "assign" or PHANTOM.match(s.text):
            continue
        owned = [v for v in s.defs if is_var(v, decl)]
        if not owned or len(owned) != len(s.defs):
            continue
        dead = [v for v in owned if (reads[v] == 0 and v not in hands) or dead_after(i, v)]
        if len(dead) != len(owned):
            continue
        if any(escapes(v) for v in dead):
            hit("dead_escaped_slot", raw)
            continue
        if s.has_call:
            hit("dead_call_result", raw)
            if any(FLOAT_REGS.match(v) for v in dead):
                hit("float_dead_result", raw)
        else:
            hit("dead_store", raw)
        if next_is_return(stmts, i) and any(dead_after(i, v) for v in dead):
            hit("dead_before_return", raw)

    subexpr: collections.Counter = collections.Counter()
    per_line: list[set[str]] = []
    for s in stmts:
        groups = set(paren_groups(s.text))
        per_line.append(groups)
        subexpr.update(groups)
    for s, groups in zip(stmts, per_line, strict=True):
        if any(subexpr[g] >= 3 for g in groups):
            hit("repeated_subexpr", s.raw)

    for v, lines in defs.items():
        if len(lines) != 1 or reads[v] != 1 or not (v in regs or TMP.match(v)):
            continue
        i = lines[0]
        nxt = next(
            (j for j in range(i + 1, len(stmts)) if stmts[j].kind not in ("blank", "comment")), None
        )
        if (
            nxt is not None
            and stmts[nxt].reads[v] == 1
            and stmts[i].depth == stmts[nxt].depth
            and len(stmts[i].defs) == 1
        ):
            hit("single_use_tmp", stmts[i].raw)
    c["slot_names"] = len({n for n in decl if n.startswith(("local_", "home_"))})
    return c, ex


CAST_TYPE = re.compile(r"\((?:const )?[A-Za-z_][\w ]*(?:\*+|\(\*\)\([\w ,*]*\))\)")


def paren_groups(text: str) -> list[str]:
    """Balanced parenthesized groups of 24+ characters that are not call
    argument lists or cast types (a function pointer cast names a type, not
    a computation)."""
    out = []
    stack = []
    for i, ch in enumerate(text):
        if ch == "(":
            stack.append(i)
        elif ch == ")" and stack:
            j = stack.pop()
            before = text[:j].rstrip()[-1:]
            group = text[j : i + 1]
            pointer_params = text[:j].endswith("(*)")
            if (
                i - j >= 24
                and not (before.isalnum() or before == "_")
                and not CAST_TYPE.fullmatch(group)
                and not pointer_params
            ):
                out.append(group)
    return out


def next_is_return(stmts: list[Stmt], i: int) -> bool:
    for s in stmts[i + 1 :]:
        if s.kind in ("blank", "comment"):
            continue
        return s.kind == "return"
    return False


def call_args(text: str, start: int) -> list[str]:
    """Top-level comma-separated arguments of the call whose `(` ends at start."""
    depth = 1
    cur = ""
    out = []
    for ch in text[start:]:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
            if depth == 0:
                out.append(cur.strip())
                return out
        elif ch == "," and depth == 1:
            out.append(cur.strip())
            cur = ""
            continue
        cur += ch
    return out


# ---- source distance ----


def source_functions(path: str) -> dict[str, list[str]]:
    """Function bodies of a C file by name: column-0 definitions up to the column-0 `}`."""
    with open(path, encoding="utf-8", errors="replace") as f:
        lines = f.read().split("\n")
    out: dict[str, list[str]] = {}
    i = 0
    head = re.compile(r"^(?:[A-Za-z_][\w \*]*?[\s\*])?([A-Za-z_]\w*)\s*\(([^;]*)$")
    while i < len(lines):
        ln = lines[i]
        m = head.match(ln)
        if m and not ln.startswith((" ", "\t", "#", "/", "*")) and not ln.rstrip().endswith(";"):
            j = i
            sig = ln
            while (
                j < len(lines)
                and "{" not in lines[j]
                and not lines[j].rstrip().endswith(";")
                and j - i < 12
            ):
                j += 1
                sig += " " + lines[j] if j < len(lines) else ""
            if j < len(lines) and "{" in lines[j] and not lines[j].rstrip().endswith(";"):
                k = j + 1
                while k < len(lines) and not lines[k].startswith("}"):
                    k += 1
                name = m.group(1)
                if name not in out and k - j < 3000:
                    out[name] = [sig] + lines[j + 1 : k]
                i = k + 1
                continue
        i += 1
    return out


def strip_c(lines: list[str]) -> list[str]:
    """Removes comments, strings and preprocessor lines from C source."""
    text = "\n".join(lines[1:])
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    text = re.sub(r"//[^\n]*", "", text)
    text = STRING.sub('""', text)
    return [ln for ln in text.split("\n") if not ln.strip().startswith("#")]


NOOP_MACROS = re.compile(
    r"^\s*(?:assert|testcase|VVA_ONLY|UNUSED_PARAMETER2?|SQLITE_DEBUG_ONLY|ALWAYS_ASSERT)\s*\("
)


def arity_of(sig: str) -> int:
    """Parameters a C prototype or a decompiled signature lists."""
    args = sig[sig.find("(") + 1 : sig.rfind(")")]
    if args.strip() in ("", "void"):
        return 0
    depth = 0
    n = 1
    for ch in args:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif ch == "," and depth == 0:
            n += 1
    return n


def c_metrics(lines: list[str]) -> dict[str, float]:
    """Statement, variable, goto, call, arity, depth and line counts of one C body."""
    sig = lines[0]
    body = [ln for ln in strip_c(lines) if not NOOP_MACROS.match(ln)]
    text = "\n".join(body)
    semis = text.count(";") - 2 * len(re.findall(r"\bfor\s*\(", text))
    ctrl = len(re.findall(r"\b(?:if|while|for|switch|case|default|do)\b", text))
    arity = arity_of(sig)
    decls = re.findall(
        r"^\s*(?:const\s+|static\s+|unsigned\s+|struct\s+)*[A-Za-z_]\w*[\s\*]+([A-Za-z_]\w*)\s*(?:=[^;]*|\[[^\]]*\])?\s*(?:,\s*\**\s*([A-Za-z_]\w*)[^,;]*)*;",
        text,
        flags=re.M,
    )
    nvars = len({d for grp in decls for d in grp if d}) + arity
    calls = len(
        [
            m
            for m in CALL.finditer(text)
            if m.group(1) not in KEYWORDS and m.group(1) != "sizeof" and not m.group(1).isupper()
        ]
    )
    depth = 0
    maxd = 0
    for ch in text:
        if ch == "{":
            depth += 1
            maxd = max(maxd, depth)
        elif ch == "}":
            depth -= 1
    return {
        "statements": semis + ctrl,
        "vars": nvars,
        "goto": len(re.findall(r"\bgoto\b", text)),
        "calls": calls,
        "arity": arity,
        "depth": maxd,
        "lines": sum(1 for ln in body if ln.strip() and ln.strip() not in ("{", "}")),
    }


def d_metrics(fn: Function) -> dict[str, float]:
    """The same counts for one decompiled function."""
    decl, globals_, _ = declared(fn)
    stmts = [Stmt(ln) for ln in fn.body]
    gnames = {g for g, _ in globals_}
    sig = next((h for h in fn.header if h.startswith("// signature:")), "")
    arity = arity_of(sig)
    used = set()
    for s in stmts:
        used |= {t for t in IDENT.findall(s.text) if is_var(t, decl) or PARAM.match(t)}
    return {
        "statements": sum(
            s.kind not in ("brace", "comment", "label", "blank", "asm") for s in stmts
        )
        + sum(1 for s in stmts if s.text.startswith("} else if")),
        "vars": len({n for n in decl if n not in gnames} | {u for u in used if PARAM.match(u)}),
        "goto": sum(1 for s in stmts if GOTO.search(s.text)),
        "calls": sum(
            1
            for s in stmts
            for m in CALL.finditer(s.text)
            if m.group(1) not in KEYWORDS
            and not TYPES.fullmatch(m.group(1))
            and not m.group(1).endswith("__rdx")
        ),
        "arity": arity,
        "depth": max((s.depth for s in stmts if s.kind != "blank"), default=0),
        "lines": sum(1 for s in stmts if s.kind not in ("blank", "brace")),
    }


def source_distance(funcs: list[Function], src: str) -> dict[str, float]:
    """Medians and geometric means of decompiled/source ratios over matched functions.

    Also the share of signatures with the source's arity, gotos beyond the
    source's, and how far each call's argument count is from its callee's
    source arity (`call_arity_off`: per 100 calls to a callee the file
    defines, the calls whose argument count differs from it).
    """
    table = source_functions(src)
    src_arity = {name: arity_of(body[0]) for name, body in table.items()}
    ratios: dict[str, list[float]] = collections.defaultdict(list)
    arity_hit = matched = 0
    goto_excess = goto_src = goto_dec = 0
    calls_checked = calls_off = 0
    for fn in funcs:
        for s in fn.body:
            t = clean(s)
            for m in CALL.finditer(t):
                want = src_arity.get(m.group(1))
                if (
                    want is None
                    or "variadic" in table[m.group(1)][0]
                    or "..." in table[m.group(1)][0]
                ):
                    continue
                calls_checked += 1
                calls_off += len([a for a in call_args(t, m.end()) if a]) != want
        body = table.get(fn.name)
        if body is None:
            continue
        sm = c_metrics(body)
        if sm["statements"] < 3:
            continue
        dm = d_metrics(fn)
        matched += 1
        for k in ("statements", "vars", "calls", "lines"):
            ratios[k].append((dm[k] + 1) / (sm[k] + 1))
        arity_hit += dm["arity"] == sm["arity"]
        goto_src += sm["goto"]
        goto_dec += dm["goto"]
        goto_excess += max(0, dm["goto"] - sm["goto"])
        ratios["depth"].append((dm["depth"] + 1) / (sm["depth"] + 1))
    out: dict[str, float] = {"matched": matched}
    for k, v in ratios.items():
        v.sort()
        out[f"{k}_ratio_median"] = round(v[len(v) // 2], 3)
        out[f"{k}_ratio_geomean"] = round(math.exp(sum(math.log(x) for x in v) / len(v)), 3)
    if matched:
        out["arity_match_pct"] = round(100 * arity_hit / matched, 1)
        out["goto_src"] = goto_src
        out["goto_dec"] = goto_dec
        out["goto_excess"] = goto_excess
    if calls_checked:
        out["call_arity_off_pct"] = round(100 * calls_off / calls_checked, 1)
    return out


# ---- reporting ----


def measure_funcs(
    funcs: list[Function],
) -> tuple[collections.Counter, dict[str, list[tuple[str, str]]]]:
    """Sums every pattern over a binary's functions, with up to three examples each."""
    total: collections.Counter = collections.Counter()
    examples: dict[str, list[tuple[str, str]]] = collections.defaultdict(list)
    depths = []
    for fn in funcs:
        c, ex = measure(fn)
        depths.append(c.pop("max_depth"))
        total.update(c)
        for k, lines in ex.items():
            if len(examples[k]) < 3 and lines and all(e[0] != fn.name for e in examples[k]):
                examples[k].append((fn.name or fn.entry, lines[0]))
    depths.sort()
    total["depth_p90"] = depths[int(len(depths) * 0.9)] if depths else 0
    total["depth_ge5"] = sum(d >= 5 for d in depths)
    return total, examples


REMOVABLE = ("phantom_pair", "dead_store", "single_use_tmp", "align_push")
"""Patterns whose every hit is a line a fix deletes outright."""

LOWER_IS_WORSE = {"src_arity_match_pct"}
"""Columns where a fall, not a rise, is the regression."""

INFO = {"input", "functions", "body_lines", "statements", "src_matched", "src_goto_src"}
"""Columns that describe the sample rather than score it: never compared."""


def row_of(tag: str, funcs: list[Function], source: str | None, nex: int, quiet: bool) -> dict:
    """One binary's counts (the baseline's row), its table printed unless quiet."""
    total, examples = measure_funcs(funcs)
    body = max(1, total["body_lines"])
    row: dict = {
        k: total[k] for k in ("functions", "body_lines", "statements", "header_lines", "decl_lines")
    }
    if not quiet:
        print(
            f"\n## {tag}: {total['functions']} functions, {total['body_lines']} body lines, "
            f"{total['statements']} statements, {total['header_lines']} header + "
            f"{total['decl_lines']} declaration lines"
        )
        print(f"{'pattern':<22} {'count':>7} {'/100':>7}  example")
    for key, _desc in PATTERNS:
        n = row[key] = total[key]
        exs = examples.get(key, [])
        if not quiet:
            print(f"{key:<22} {n:>7} {100 * n / body:>7.2f}  {exs[0][1][:90] if exs else ''}")
            for _name, line in exs[1:nex]:
                print(f"{'':<38}{line[:90]}")
    row["removable"] = sum(total[k] for k in REMOVABLE)
    row["depth_p90"] = total["depth_p90"]
    if not quiet:
        rate = 100 * row["removable"] / body
        print(f"{'removable lines':<22} {row['removable']:>7} {rate:>7.2f}")
        print(
            f"nesting: p90 depth {total['depth_p90']}, {total['depth_ge5']} functions at depth >= 5"
        )
    if source:
        dist = source_distance(funcs, source)
        if not quiet:
            print("source distance:", "  ".join(f"{k}={v}" for k, v in dist.items()))
        row.update({f"src_{k}": v for k, v in dist.items()})
    return row


# ---- collection ----

INPUTS = [
    ("findstr", "SystemRoot", ("System32", "findstr.exe"), None),
    ("msvcrt32", "SystemRoot", ("SysWOW64", "msvcrt.dll"), None),
    ("sqlite_x64", "BORER_READABILITY_CORPUS", ("sqlite3.x64.elf",), "sqlite3.c"),
    ("sqlite_a64", "BORER_READABILITY_CORPUS", ("sqlite3.full.elf",), "sqlite3.c"),
]
"""The benchmark's inputs: tag, the environment variable naming the folder,
the path below it and the source file beside it, if any. A missing input is
skipped and said so."""

WANT = 400
"""Functions decompiled per binary: all of them up to this, else every k-th."""

INSTR_MAX = 3000
"""Functions longer than this are left out of the sample (one sqlite3VdbeExec
takes 22 s alone and says nothing the others do not)."""


def digest(path: str) -> str:
    """First 16 hex digits of the file's SHA-256: the input's identity in the baseline."""
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()[:16]


def collect(client, binary: str, want: int = WANT) -> list[Function]:
    """Decompiles a deterministic sample of one binary's functions over an MCP session."""
    client.tool("load_binary", {"path": os.path.abspath(binary)})
    rows = []
    offset = 0
    while True:
        _, text = client.tool("functions", {"offset": offset, "limit": 300})
        page = [ln.split(maxsplit=7) for ln in text.splitlines() if ln.startswith("0x")]
        if not page:
            break
        rows += [(int(c[0], 16), c[0], int(c[3]), c[7] if len(c) > 7 else "") for c in page]
        offset += 300
    rows = sorted(r for r in rows if r[2] <= INSTR_MAX)
    step = max(1, math.ceil(len(rows) / want))
    out = []
    for _, entry, _, name in rows[::step]:
        _, text = client.tool("decompile", {"address": entry, "limit": 1_000_000})
        out.append(Function(entry, name, text))
    return out


EXIT_WAIT = 120
"""Seconds a server is given to exit once its input closes: dropping a
large binary's analysis takes more than the ten seconds the shared client waits on a machine
busy with builds, and the measurement is already in hand."""


def shut(client) -> None:
    """Closes a session's input and waits for the server to exit, else kills it."""
    client.proc.stdin.close()
    try:
        client.proc.wait(timeout=EXIT_WAIT)
    except subprocess.TimeoutExpired:
        client.proc.kill()
        client.proc.wait()


def read_tsv(path: str) -> dict[str, dict[str, str]]:
    """A baseline: {tag: {column: value}}."""
    if not os.path.exists(path):
        return {}
    with open(path, encoding="utf-8") as f:
        head, *rows = [ln.rstrip("\n").split("\t") for ln in f if ln.strip()]
    return {r[0]: dict(zip(head[1:], r[1:], strict=False)) for r in rows}


def write_tsv(path: str, rows: dict[str, dict]) -> None:
    """Writes rows as one TSV, columns sorted, so a diff shows what moved."""
    keys = sorted({k for r in rows.values() for k in r})
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write("tag\t" + "\t".join(keys) + "\n")
        for tag in sorted(rows):
            f.write(tag + "\t" + "\t".join(str(rows[tag].get(k, "")) for k in keys) + "\n")


def slack(key: str, old: float, counted: bool) -> float:
    """How far a column may move the wrong way before it fails the run.

    A count over an unchanged sample may rise by 2% of itself plus 2 lines;
    a source ratio (decompiled / source) by 0.02; a rate per 100 body lines
    (a count when the sample changed) or a percentage by 2% of itself plus
    0.05.
    """
    if counted:
        return 0.02 * abs(old) + 2
    if key.startswith("src_") and "ratio" in key:
        return 0.02
    return 0.02 * abs(old) + 0.05


def compare(rows: dict[str, dict], base: dict[str, dict[str, str]]) -> int:
    """Prints every metric that moved; returns how many got worse beyond tolerance.

    Counts are compared as counts while the sample holds the same functions,
    so deleting noise lines moves only the metrics it should; when the
    sample changed they are compared per 100 body lines. An input whose
    digest differs from the baseline's is not compared: the binary changed,
    not the decompiler.
    """
    worse = 0
    for tag, row in rows.items():
        old = base.get(tag)
        if old is None:
            print(f"{tag}: no baseline row (run with --update)")
            continue
        if old.get("input") != row["input"]:
            print(f"{tag}: input changed ({old.get('input')} -> {row['input']}), not compared")
            continue
        body_old = max(1.0, float(old.get("body_lines") or 1))
        body_new = max(1, row["body_lines"])
        same = str(row["functions"]) == old.get("functions")
        print(
            f"{tag}: {old.get('functions')} -> {row['functions']} functions, "
            f"{old.get('body_lines')} -> {row['body_lines']} body lines"
        )
        for k, v in row.items():
            if k in INFO or not isinstance(v, (int, float)):
                continue
            try:
                b = float(old.get(k, ""))
            except ValueError:
                continue
            count = isinstance(v, int) and not k.startswith("src_") and k != "depth_p90"
            rate = f"  ({100 * b / body_old:.2f} -> {100 * v / body_new:.2f} /100)"
            if count and not same:
                b, v = round(100 * b / body_old, 2), round(100 * v / body_new, 2)
            if v == b:
                continue
            bad = (v > b) != (k in LOWER_IS_WORSE)
            fail = bad and abs(v - b) > slack(k, b, count and same)
            worse += fail
            mark = "WORSE" if fail else ("worse" if bad else "better")
            print(f"{tag:<12} {k:<34} {b:>9g} -> {v:<9g} {mark}{rate if count and same else ''}")
    return worse


def main(argv: list[str]) -> int:
    args = argv[1:]
    if not args or args[0] in ("-h", "--help"):
        print(__doc__)
        return 2

    def opt(name: str) -> str | None:
        return args[args.index(name) + 1] if name in args else None

    sources = {
        key: value
        for i, a in enumerate(args)
        if i and args[i - 1] == "--source"
        for key, _, value in (a.partition("="),)
    }
    nex = int(opt("--examples") or 2)
    quiet = "--quiet" in args
    rows: dict[str, dict] = {}
    if args[0] == "measure":
        outdir = args[1]
        for tag in sorted(f[:-4] for f in os.listdir(outdir) if f.endswith(".txt")):
            path = os.path.join(outdir, f"{tag}.txt")
            rows[tag] = row_of(tag, split_dump(path), sources.get(tag), nex, quiet)
        tsv = opt("--tsv")
        if tsv:
            write_tsv(tsv, rows)
        return 0
    if args[0] != "run":
        print(__doc__)
        return 2
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from harness.client import Client

    exe = os.path.abspath(args[1])
    only_arg = opt("--only")
    only = set(only_arg.split(",")) if only_arg else None
    t0 = time.time()
    for tag, var, parts, src in INPUTS:
        if only is not None and tag not in only:
            continue
        folder = os.environ.get(var)
        path = os.path.join(folder, *parts) if folder else os.path.join(f"${var}", *parts)
        if not folder or not os.path.isfile(path):
            print(f"[skip] {tag}: no {path}")
            continue
        client = Client(exe)
        try:
            funcs = collect(client, path)
        finally:
            shut(client)
        out = opt("--out")
        if out:
            os.makedirs(out, exist_ok=True)
            with open(os.path.join(out, f"{tag}.txt"), "w", encoding="utf-8") as f:
                f.writelines(f"==== {fn.entry} {fn.name} 0\n{fn.text}\n" for fn in funcs)
        source = os.path.join(os.path.dirname(path), src) if src else None
        rows[tag] = {"input": digest(path), **row_of(tag, funcs, source, nex, quiet)}
        print(f"[ok  ] {tag}: {len(funcs)} functions ({time.time() - t0:.0f}s)", flush=True)
    baseline = opt("--baseline")
    if not baseline:
        return 0
    if "--update" in args:
        write_tsv(baseline, {**read_tsv(baseline), **rows})
        print(f"baseline written: {baseline}")
        return 0
    worse = compare(rows, read_tsv(baseline))
    print(f"\n{worse} metric(s) worse beyond tolerance" if worse else "\nno regression")
    return 1 if worse else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
