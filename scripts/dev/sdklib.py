#!/usr/bin/env python3
"""Write borer's SDK type library from the Windows SDK headers on this machine.

    python scripts/dev/sdklib.py    write the tables and their manifest

Every declaration is compiled beside the headers it came from, spelled as
borer spells it (`analysis::sdk::spell`); the few clang rejects are left
out and named in the manifest.

The tables live in crates/borer-engine/src/analysis/sdk/. Spelled types and
names are interned to keep the shipped data small: a row cites them by a
base-36 index into `words.tsv` and `names.tsv`, which list each once, most
used first.

  words.tsv      one spelled C type per line (`DWORD`, `const char *`)
  names.tsv      one parameter or field name per line, `-` for none
  functions.tsv  name; calling convention (`s` stdcall, `f` fastcall, `c`
                 cdecl) and origin (`u` user mode, `k` kernel, `r` the C
                 runtime, `c` a C standard function whose types mean the
                 same on every platform) as two letters; the return type's
                 word; then `word.name` per parameter, and `...` last for a
                 variable list
  types.tsv      a typedef name, what the machine passes it as (the words of
                 `ctypes.tsv`, `-` for a structure by value), and the
                 structure it names or points at, with the pointer count
  structs.tsv    a structure's tag, its size on x64 and on x86 (`-` when x86
                 lacks it), then `name.word.off64.off32` per field

Where the data comes from. clang parses the SDK headers (`um`, `shared`,
`ucrt` and, in a translation unit of its own, `km`) with
`-ast-dump=json` and `-fdump-record-layouts-complete` for the x86-64 and
i686 Windows targets. Each row restates a declaration as facts: a name,
a calling convention, parameter types and names, a typedef's
representation, a structure's field names, types and offsets. No header
text is copied. `manifest.tsv` records the SDK and clang versions, the
headers each unit includes and the row counts.

A kernel declaration takes its convention from an i686 parse of its unit,
where one that states none is `__stdcall`: the kernel builds with `/Gz`.
A user-mode one states its own (`WINAPI`); none is `__cdecl`.

Compiler intrinsics (a clang builtin whose name starts with `_` and that no
library imports) and functions the headers define inline are left out. A
name both units declare keeps the user-mode row.

The output is deterministic: rows are sorted by name, nothing depends on
the clock, and running this twice on one machine writes the same bytes.
"""

from __future__ import annotations

import glob
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "crates" / "borer-engine" / "src" / "analysis" / "sdk"

CLANG_CANDIDATES = [
    r"C:\Program Files\LLVM\bin\clang.exe",
    "clang",
]
KITS = r"C:\Program Files (x86)\Windows Kits\10\Include"
MSVC_GLOB = r"C:\Program Files\Microsoft Visual Studio\*\*\VC\Tools\MSVC\*\include"

DEFINES = [
    "_WIN32_WINNT=0x0A00",
    "NTDDI_VERSION=0x0A00000F",
    "WINVER=0x0A00",
    "_CRT_SECURE_NO_WARNINGS",
    "_NO_CRT_STDIO_INLINE",
    "SECURITY_WIN32",
]

UM_HEADERS = [
    "winsock2.h",
    "ws2tcpip.h",
    "mswsock.h",
    "windows.h",
    "winternl.h",
    "ntsecapi.h",
    "shlobj.h",
    "shlwapi.h",
    "shellapi.h",
    "wincrypt.h",
    "bcrypt.h",
    "ncrypt.h",
    "wintrust.h",
    "softpub.h",
    "wininet.h",
    "urlmon.h",
    "psapi.h",
    "tlhelp32.h",
    "dbghelp.h",
    "iphlpapi.h",
    "setupapi.h",
    "winsvc.h",
    "userenv.h",
    "wtsapi32.h",
    "lm.h",
    "sddl.h",
    "aclapi.h",
    "accctrl.h",
    "security.h",
    "wincred.h",
    "dpapi.h",
    "commctrl.h",
    "commdlg.h",
    "objbase.h",
    "oleauto.h",
    "ole2.h",
    "winver.h",
    "mmsystem.h",
    "winspool.h",
    "uxtheme.h",
    "dwmapi.h",
    "winevt.h",
    "evntprov.h",
    "evntrace.h",
    "pdh.h",
    "powrprof.h",
    "d3d9.h",
    "d3d11.h",
    "dxgi.h",
    "imagehlp.h",
    "winioctl.h",
    "netfw.h",
    "wlanapi.h",
    "dnsapi.h",
    "icmpapi.h",
    "shlguid.h",
    "propsys.h",
    "msi.h",
    "cfgmgr32.h",
    "hidsdi.h",
    "winusb.h",
    "rpc.h",
    "rpcdce.h",
    "ktmw32.h",
    "restartmanager.h",
    "processsnapshot.h",
    "werapi.h",
    "winscard.h",
    "wtypes.h",
    "assert.h",
    "conio.h",
    "ctype.h",
    "direct.h",
    "errno.h",
    "fcntl.h",
    "float.h",
    "io.h",
    "locale.h",
    "malloc.h",
    "math.h",
    "mbstring.h",
    "memory.h",
    "process.h",
    "search.h",
    "setjmp.h",
    "signal.h",
    "stdint.h",
    "stdio.h",
    "stdlib.h",
    "string.h",
    "sys/stat.h",
    "sys/timeb.h",
    "sys/utime.h",
    "time.h",
    "wchar.h",
    "wctype.h",
    "uchar.h",
]

KM_HEADERS = ["ntifs.h", "fltKernel.h", "ntstrsafe.h", "wdmsec.h", "aux_klib.h"]

C_STANDARD = set(
    """
abort abs acos acosf acosh acoshf acoshl acosl asctime asin asinf asinh asinhf
asinhl asinl atan atan2 atan2f atan2l atanf atanh atanhf atanhl atanl atexit
atof atoi atol atoll bsearch btowc calloc cbrt cbrtf cbrtl ceil ceilf ceill
clearerr clock copysign copysignf copysignl cos cosf cosh coshf coshl cosl
ctime difftime div erf erfc erfcf erfcl erff erfl exit exp exp2 exp2f exp2l
expf expl expm1 expm1f expm1l fabs fabsf fabsl fclose fdim fdimf fdiml feof
ferror fflush fgetc fgetpos fgets fgetwc fgetws floor floorf floorl fma fmaf
fmal fmax fmaxf fmaxl fmin fminf fminl fmod fmodf fmodl fopen fprintf fputc
fputs fputwc fputws fread free freopen frexp frexpf frexpl fscanf fseek
fsetpos ftell fwide fwprintf fwrite fwscanf getc getchar getenv gets getwc
getwchar gmtime hypot hypotf hypotl ilogb ilogbf ilogbl isalnum isalpha
isblank iscntrl isdigit isgraph islower isprint ispunct isspace isupper
iswalnum iswalpha iswblank iswcntrl iswctype iswdigit iswgraph iswlower
iswprint iswpunct iswspace iswupper iswxdigit isxdigit labs ldexp ldexpf
ldexpl ldiv lgamma lgammaf lgammal llabs lldiv llrint llrintf llrintl llround
llroundf llroundl localeconv localtime log log10 log10f log10l log1p log1pf
log1pl log2 log2f log2l logb logbf logbl logf logl longjmp lrint lrintf
lrintl lround lroundf lroundl malloc mblen mbrlen mbrtowc mbsinit mbsrtowcs
mbstowcs mbtowc memchr memcmp memcpy memmove memset mktime modf modff modfl
nan nanf nanl nearbyint nearbyintf nearbyintl nextafter nextafterf
nextafterl perror pow powf powl printf putc putchar puts putwc putwchar qsort
quick_exit raise rand realloc remainder remainderf remainderl remove remquo
remquof remquol rename rewind rint rintf rintl round roundf roundl scalbln
scalblnf scalblnl scalbn scalbnf scalbnl scanf setbuf setlocale setvbuf
signal sin sinf sinh sinhf sinhl sinl snprintf sprintf sqrt sqrtf sqrtl srand
sscanf strcat strchr strcmp strcoll strcpy strcspn strerror strftime strlen
strncat strncmp strncpy strpbrk strrchr strspn strstr strtod strtof strtok
strtol strtold strtoll strtoul strtoull strxfrm swprintf swscanf system tan
tanf tanh tanhf tanhl tanl tgamma tgammaf tgammal time tmpfile tmpnam tolower
toupper towctrans towlower towupper trunc truncf truncl ungetc ungetwc
vfprintf vfscanf vfwprintf vfwscanf vprintf vscanf vsnprintf vsprintf
vsscanf vswprintf vswscanf vwprintf vwscanf wcrtomb wcscat wcschr wcscmp
wcscoll wcscpy wcscspn wcsftime wcslen wcsncat wcsncmp wcsncpy wcspbrk
wcsrchr wcsrtombs wcsspn wcsstr wcstod wcstof wcstok wcstol wcstold wcstoll
wcstombs wcstoul wcstoull wcsxfrm wctob wctomb wctrans wctype wmemchr wmemcmp
wmemcpy wmemmove wmemset wprintf wscanf aligned_alloc at_quick_exit
""".split()
)

BUILTIN_WORDS = {
    "void": "void",
    "char": "char",
    "signed char": "i8",
    "unsigned char": "u8",
    "short": "i16",
    "unsigned short": "u16",
    "int": "i32",
    "unsigned int": "u32",
    "long": "i32",
    "unsigned long": "u32",
    "long long": "i64",
    "unsigned long long": "u64",
    "__int64": "i64",
    "unsigned __int64": "u64",
    "float": "f32",
    "double": "f64",
    "long double": "f64",
    "_Bool": "u8",
    "__wchar_t": "u16",
    "wchar_t": "u16",
    "char16_t": "u16",
    "char32_t": "u32",
}

QUALIFIERS = {"const", "volatile", "restrict", "__restrict", "__unaligned", "__ptr32", "__ptr64"}

NULLABILITY = ("_Nonnull", "_Nullable", "_Null_unspecified")

WORD_TYPEDEFS = {
    "ULONG_PTR": "word",
    "UINT_PTR": "word",
    "DWORD_PTR": "word",
    "SIZE_T": "word",
    "size_t": "word",
    "uintptr_t": "word",
    "LONG_PTR": "sword",
    "INT_PTR": "sword",
    "SSIZE_T": "sword",
    "ptrdiff_t": "sword",
    "intptr_t": "sword",
}

ATTR = re.compile(r"\s*__attribute__\(\((\w+)\)\)")


def clang() -> str:
    """Return the clang executable found on this machine."""
    for c in CLANG_CANDIDATES:
        if os.path.isabs(c) and os.path.exists(c):
            return c
    return CLANG_CANDIDATES[-1]


def sdk_include() -> tuple[str, str]:
    """Return the newest SDK version and its include directory."""
    versions = sorted(p for p in os.listdir(KITS) if p[:1].isdigit())
    if not versions:
        raise SystemExit(f"no Windows SDK under {KITS}")
    return versions[-1], os.path.join(KITS, versions[-1])


def msvc_include() -> str:
    """Return the newest MSVC include directory."""
    found = sorted(glob.glob(MSVC_GLOB))
    if not found:
        raise SystemExit("no MSVC include directory")
    return found[-1]


def unit_args(target: str, dirs: list[str], defines: list[str]) -> list[str]:
    """Return the clang arguments that parse one unit for `target`."""
    args = [clang(), "-fsyntax-only", f"--target={target}", "-x", "c", "-std=c17"]
    args += ["-fms-extensions", "-fms-compatibility", "-Wno-everything"]
    for d in dirs:
        args += ["-isystem", d]
    for d in defines:
        args.append(f"-D{d}")
    return args


def run_unit(headers: list[str], target: str, dirs: list[str], defines: list[str], extra: list[str]) -> str:
    """Parse a unit including `headers` and return clang's stdout."""
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "unit.c")
        with open(src, "w", encoding="utf-8") as f:
            for h in headers:
                f.write(f"#include <{h}>\n")
        out = subprocess.run(
            unit_args(target, dirs, defines) + extra + [src],
            capture_output=True,
            check=False,
        )
        if out.returncode != 0:
            sys.stderr.write(out.stderr.decode("utf-8", "replace")[:4000])
            raise SystemExit(f"clang failed on {target} {headers[:3]}...")
        return out.stdout.decode("utf-8", "replace")


def usable(headers: list[str], target: str, dirs: list[str], defines: list[str]) -> list[str]:
    """Return the headers of `headers` that parse together, in order."""
    kept: list[str] = []
    for h in headers:
        try:
            run_unit(kept + [h], target, dirs, defines, [])
        except SystemExit:
            sys.stderr.write(f"  skip {h}\n")
            continue
        kept.append(h)
    return kept


def strip_quals(t: str) -> str:
    """Return a type with its qualifiers dropped and spaces normalized."""
    words = [w for w in t.replace("*", " * ").split() if w not in QUALIFIERS]
    return " ".join(words).replace(" *", "*").replace("* ", "*")


def ret_of(qual: str) -> str | None:
    """Return the return type spelled in a function type, or None."""
    t = ATTR.sub("", qual).strip()
    if not t.endswith(")"):
        return None
    depth = 0
    for i in range(len(t) - 1, -1, -1):
        c = t[i]
        if c == ")":
            depth += 1
        elif c == "(":
            depth -= 1
            if depth == 0:
                ret = t[:i].strip()
                return None if "(" in ret else ret
    return None


def conv_of(qual: str) -> str:
    """Return the calling convention letter of a function type."""
    attrs = ATTR.findall(qual)
    if "stdcall" in attrs:
        return "s"
    if "fastcall" in attrs:
        return "f"
    if "cdecl" in attrs:
        return "c"
    return ""


def norm_type(t: str, decay: bool = True) -> str:
    """Return a parameter type in the form the tables write.

    An array parameter decays to a pointer unless `decay` is false (a
    field's array keeps its length); `__attribute__` sugar goes.
    """
    t = ATTR.sub("", t).strip()
    t = re.sub(r"\b__(size_t|ptrdiff_t)\b", r"\1", t)
    for q in NULLABILITY:
        t = re.sub(r"\b" + q + r"\b", "", t)
    t = re.sub(r"\*\s*const\s*$", "*", t.strip())
    if decay:
        t = re.sub(r"\s*\[[^\]]*\]", " *", t)
    t = re.sub(r"\s+", " ", t)
    t = t.replace(" *", "*").replace("*", " *").replace("* *", "**").replace("* *", "**")
    return t.replace("( *", "(*").strip()


class Unit:
    """The declarations one parse produced."""

    def __init__(self, ast: dict) -> None:
        self.typedefs: dict[str, str] = {}
        self.funcs: dict[str, dict] = {}
        self.enums: set[str] = set()
        file = ""
        for node in ast.get("inner", []):
            file = self.file_of(node, file)
            kind = node.get("kind")
            name = node.get("name")
            if not name:
                continue
            if kind == "TypedefDecl":
                self.typedefs.setdefault(name, node["type"]["qualType"])
            elif kind == "EnumDecl":
                self.enums.add(name)
            elif kind == "FunctionDecl":
                self.take(node, name, file)

    @staticmethod
    def file_of(node: dict, last: str) -> str:
        """Return the file a node's location names, else the last one."""
        loc = node.get("loc", {})
        for k in (loc, loc.get("expansionLoc", {}), loc.get("spellingLoc", {})):
            if "file" in k:
                return k["file"]
        rng = node.get("range", {}).get("begin", {})
        for k in (rng, rng.get("expansionLoc", {})):
            if "file" in k:
                return k["file"]
        return last

    def take(self, node: dict, name: str, file: str) -> None:
        """Record one function declaration, the first named one winning."""
        inner = node.get("inner", [])
        kinds = {i.get("kind") for i in inner}
        if "CompoundStmt" in kinds or node.get("inline"):
            self.funcs[name] = {"skip": True}
            return
        prev = self.funcs.get(name)
        if prev is not None and (prev.get("skip") or prev.get("named")):
            return
        builtin = "BuiltinAttr" in kinds
        imported = "DLLImportAttr" in kinds
        lowered = file.replace("\\", "/").lower()
        if (builtin and name.startswith("_") and not imported) or "/llvm/" in lowered:
            self.funcs[name] = {"skip": True}
            return
        if "intrin" in os.path.basename(lowered):
            self.funcs[name] = {"skip": True}
            return
        qual = node["type"]["qualType"]
        ret = ret_of(qual)
        if ret is None:
            return
        params = []
        for p in inner:
            if p.get("kind") != "ParmVarDecl":
                continue
            params.append((norm_type(p["type"]["qualType"]), p.get("name", "")))
        named = all(n for _, n in params) and params != []
        self.funcs[name] = {
            "ret": norm_type(ret),
            "conv": conv_of(qual) or "c",
            "conv32": conv_of(qual),
            "params": params,
            "variadic": bool(node.get("variadic")),
            "named": named or not params,
            "file": lowered,
        }


def origin_of(file: str, km: bool) -> str:
    """Return the origin column for a declaration's header."""
    if km:
        return "km"
    if "/ucrt/" in file or "/msvc/" in file:
        return "crt"
    return "um"


def param_name(name: str, origin: str) -> str:
    """Return a parameter's name as the table writes it.

    The C runtime's reserved spellings (`_Buffer`) lose the underscore a
    reader does not write; a missing name is `-`.
    """
    if not name:
        return "-"
    if origin in ("crt", "c") and name.startswith("_") and len(name) > 1 and not name.startswith("__"):
        return name[1:]
    return name


def resolve(name: str, typedefs: dict[str, str], enums: set[str], depth: int = 0) -> tuple[str, str | None, int]:
    """Return a typedef's pass word, the structure under it and its pointer count."""
    if name in WORD_TYPEDEFS:
        return (WORD_TYPEDEFS[name], None, 0)
    if depth > 32:
        return ("-", None, 0)
    t = strip_quals(ATTR.sub("", typedefs[name]))
    if "(" in t:
        return ("ptr", None, 0)
    if "[" in t:
        return ("-", None, 0)
    stars = t.count("*")
    base = t.replace("*", "").strip()
    tag = None
    word = None
    if base.startswith(("struct ", "union ")):
        tag = base.split(" ", 1)[1]
    elif base.startswith("enum "):
        word = "i32"
    elif base in BUILTIN_WORDS:
        word = BUILTIN_WORDS[base]
    elif base in typedefs and base != name:
        w, tag, inner = resolve(base, typedefs, enums, depth + 1)
        if stars:
            return ("ptr", tag, inner + stars)
        return (w, tag, inner)
    if stars:
        return ("ptr", tag, stars)
    if tag is not None:
        return ("-", tag, 0)
    return (word or "-", None, 0)


def parse_layouts(text: str) -> dict[str, tuple[int, list[tuple[str, str, int]]]]:
    """Read clang's record layout dump: per named structure, its size and
    its direct fields (anonymous members flattened one level)."""
    out: dict[str, tuple[int, list[tuple[str, str, int]]]] = {}
    blocks = text.split("*** Dumping AST Record Layout")
    line_re = re.compile(r"^\s*([0-9]+)(?::[0-9-]+)? \| (\s*)(.*)$")
    size_re = re.compile(r"\[sizeof=([0-9]+)")
    for block in blocks[1:]:
        lines = [l for l in block.splitlines() if "|" in l]
        if not lines:
            continue
        head = line_re.match(lines[0])
        if not head:
            continue
        title = head.group(3).strip()
        parts = title.split(" ", 1)
        if len(parts) != 2 or parts[0] not in ("struct", "union") or "(" in parts[1] or "::" in parts[1]:
            continue
        tag = parts[1]
        size = None
        fields: list[tuple[str, str, int]] = []
        anon_depth = None
        for l in lines[1:]:
            s = size_re.search(l)
            if s:
                size = int(s.group(1))
                continue
            m = line_re.match(l)
            if not m:
                continue
            off = int(m.group(1))
            indent = len(m.group(2))
            body = m.group(3).strip()
            bitfield = re.match(r"^\s*[0-9]+:[0-9]", l) is not None
            if indent == 2:
                anon_depth = None
                if "(anonymous" in body:
                    anon_depth = 4
                    continue
            elif indent != anon_depth:
                continue
            if bitfield:
                continue
            body = re.sub(r"\(unnamed at [^)]*\)", "", body)
            body = re.sub(r"\(anonymous at [^)]*\)", "", body)
            mm = re.match(r"^(.*?)\s*([A-Za-z_][A-Za-z0-9_]*)$", body)
            if not mm or not mm.group(1):
                continue
            ftype = norm_type(mm.group(1), decay=False)
            if "::" in ftype or ":" in ftype:
                ftype = "-"
            fields.append((mm.group(2), ftype, off))
        if size is None or tag in out:
            continue
        out[tag] = (size, fields)
    return out


ORIGIN = {"um": "u", "km": "k", "crt": "r", "c": "c"}

PORTABLE = {
    "void", "char", "signed char", "unsigned char", "short", "unsigned short",
    "int", "unsigned int", "long", "unsigned long", "long long",
    "unsigned long long", "float", "double", "size_t", "FILE", "time_t",
    "va_list", "fpos_t", "div_t", "ldiv_t", "lldiv_t", "clock_t",
    "struct tm", "struct lconv", "intmax_t",
}


def portable(f: dict) -> bool:
    """Tell whether a C runtime declaration means the same on every
    platform: every type a standard C word."""
    for ty in [f["ret"]] + [t for t, _ in f["params"]]:
        base = strip_quals(ty).replace("*", "").strip()
        if base not in PORTABLE:
            return False
    return True


def b36(n: int) -> str:
    """Return `n` in base 36, lowercase."""
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"
    out = ""
    while True:
        n, r = divmod(n, 36)
        out = digits[r] + out
        if n == 0:
            return out


def write(path: Path, rows: list[str]) -> int:
    """Write rows as lines and return the byte count."""
    text = "".join(r + "\n" for r in rows)
    path.write_text(text, encoding="utf-8", newline="")
    return len(text.encode("utf-8"))


def main(argv: list[str]) -> int:
    """Generate the tables."""
    version, inc = sdk_include()
    msvc = msvc_include()
    um_dirs = [msvc, os.path.join(inc, "ucrt"), os.path.join(inc, "shared"), os.path.join(inc, "um")]
    km_dirs = [msvc, os.path.join(inc, "km"), os.path.join(inc, "ucrt"), os.path.join(inc, "shared")]
    km_defines = DEFINES + ["_AMD64_", "_KERNEL_MODE"]
    um = usable(UM_HEADERS, "x86_64-pc-windows-msvc", um_dirs, DEFINES)
    km = usable(KM_HEADERS, "x86_64-pc-windows-msvc", km_dirs, km_defines)
    um_unit = Unit(json.loads(run_unit(um, "x86_64-pc-windows-msvc", um_dirs, DEFINES, ["-Xclang", "-ast-dump=json"])))
    km_unit = Unit(json.loads(run_unit(km, "x86_64-pc-windows-msvc", km_dirs, km_defines, ["-Xclang", "-ast-dump=json"])))
    km32 = [d for d in km_defines if d != "_AMD64_"] + ["_X86_"]
    km_x86 = Unit(json.loads(run_unit(km, "i686-pc-windows-msvc", km_dirs, km32, ["-Xclang", "-ast-dump=json"])))
    for name, f in km_unit.funcs.items():
        x86 = km_x86.funcs.get(name, {})
        if f.get("skip") or x86.get("skip") or "conv32" not in x86:
            continue
        f["conv"] = x86["conv32"] or ("c" if f["variadic"] else "s")

    funcs: dict[str, tuple[dict, bool]] = {}
    for unit, is_km in ((um_unit, False), (km_unit, True)):
        for name, f in unit.funcs.items():
            if f.get("skip") or name in funcs:
                continue
            funcs[name] = (f, is_km)
    typedefs = dict(km_unit.typedefs)
    typedefs.update(um_unit.typedefs)
    enums = um_unit.enums | km_unit.enums

    used_words: set[str] = set()
    decls = []
    for name in sorted(funcs):
        f, is_km = funcs[name]
        origin = origin_of(f["file"], is_km)
        if origin == "crt" and name in C_STANDARD and portable(f):
            origin = "c"
        params = [(ty, param_name(pn, origin)) for ty, pn in f["params"]]
        decls.append((name, f["conv"], origin, f["ret"], params, f["variadic"]))
        for ty in [f["ret"]] + [t for t, _ in f["params"]]:
            used_words.add(strip_quals(ty).replace("*", "").strip())
    refused = keep_valid(decls, um, um_dirs, DEFINES, lambda d: d[2] != "km")
    refused += keep_valid(decls, km, km_dirs, km_defines, lambda d: d[2] == "km")
    decls = [d for d in decls if d[0] not in refused]
    OUT.mkdir(parents=True, exist_ok=True)

    dump = ["-Xclang", "-fdump-record-layouts-complete"]
    lay64 = parse_layouts(run_unit(um, "x86_64-pc-windows-msvc", um_dirs, DEFINES, dump))
    lay32 = parse_layouts(run_unit(um, "i686-pc-windows-msvc", um_dirs, DEFINES, dump))
    klay64 = parse_layouts(run_unit(km, "x86_64-pc-windows-msvc", km_dirs, km_defines, dump))
    klay32 = parse_layouts(run_unit(km, "i686-pc-windows-msvc", km_dirs, km32, dump))
    for k, v in klay64.items():
        lay64.setdefault(k, v)
    for k, v in klay32.items():
        lay32.setdefault(k, v)

    type_rows = []
    wanted: set[str] = set()
    pending = sorted(w for w in used_words if w in typedefs)
    seen: set[str] = set()
    while pending:
        w = pending.pop()
        if w in seen:
            continue
        seen.add(w)
        word, tag, stars = resolve(w, typedefs, enums)
        type_rows.append((w, word, tag, stars))
        if tag:
            wanted.add(tag)
    for _, _, _, ret, params, _ in decls:
        for ty in [ret] + [t for t, _ in params]:
            base = strip_quals(ty).replace("*", "").strip()
            if base.startswith(("struct ", "union ")):
                wanted.add(base.split(" ", 1)[1])
    structs = []
    done: set[str] = set()
    queue = sorted(wanted)
    while queue:
        tag = queue.pop()
        if tag in done or tag not in lay64:
            continue
        done.add(tag)
        size64, fields64 = lay64[tag]
        size32, fields32 = lay32.get(tag, (None, []))
        off32 = {n: o for n, _, o in fields32}
        fields = []
        for fname, ftype, off in sorted(fields64, key=lambda f: f[2]):
            fields.append((fname, ftype, off, off32.get(fname)))
            base = strip_quals(ftype).replace("*", "").strip()
            if base in typedefs and base not in seen:
                seen.add(base)
                word, ftag, stars = resolve(base, typedefs, enums)
                type_rows.append((base, word, ftag, stars))
                if ftag and stars == 0:
                    queue.append(ftag)
            elif base.startswith(("struct ", "union ")) and "*" not in ftype:
                queue.append(base.split(" ", 1)[1])
        structs.append((tag, size64, size32, fields))
    structs.sort()

    spelled: dict[str, int] = {}
    named: dict[str, int] = {}
    for _, _, _, ret, params, _ in decls:
        spelled[ret] = spelled.get(ret, 0) + 1
        for ty, pn in params:
            spelled[ty] = spelled.get(ty, 0) + 1
            named[pn] = named.get(pn, 0) + 1
    for _, _, _, fields in structs:
        for fname, ftype, _, _ in fields:
            spelled[ftype] = spelled.get(ftype, 0) + 1
            named[fname] = named.get(fname, 0) + 1
    words = sorted(spelled, key=lambda w: (-spelled[w], w))
    names = sorted(named, key=lambda w: (-named[w], w))
    wi = {w: b36(i) for i, w in enumerate(words)}
    ni = {w: b36(i) for i, w in enumerate(names)}
    rows = []
    for name, conv, origin, ret, params, variadic in decls:
        cols = [name, conv + ORIGIN[origin], wi[ret]]
        cols += [f"{wi[ty]}.{ni[pn]}" for ty, pn in params]
        if variadic:
            cols.append("...")
        rows.append("\t".join(cols))
    struct_rows = []
    for tag, size64, size32, fields in structs:
        cols = [tag, str(size64), "-" if size32 is None else str(size32)]
        for fname, ftype, off, o32 in fields:
            cols.append(f"{ni[fname]}.{wi[ftype]}.{off}.{'-' if o32 is None else o32}")
        struct_rows.append("\t".join(cols))
    type_text = sorted("\t".join([n, w, t or "-", str(s)]) for n, w, t, s in type_rows)
    sizes = {
        "functions.tsv": write(OUT / "functions.tsv", rows),
        "words.tsv": write(OUT / "words.tsv", words),
        "names.tsv": write(OUT / "names.tsv", names),
        "types.tsv": write(OUT / "types.tsv", type_text),
        "structs.tsv": write(OUT / "structs.tsv", struct_rows),
    }
    version_line = subprocess.run([clang(), "--version"], capture_output=True, check=False)
    clang_version = version_line.stdout.decode().splitlines()[0]
    counts = {
        "functions.tsv": len(rows),
        "words.tsv": len(words),
        "names.tsv": len(names),
        "types.tsv": len(type_text),
        "structs.tsv": len(struct_rows),
    }
    origins = {o: sum(1 for d in decls if d[2] == o) for o in sorted(ORIGIN)}
    manifest = [
        "# borer SDK type library: facts restated from the Windows SDK headers, no header text",
        f"# sdk\tWindows SDK {version}",
        f"# parser\t{clang_version}",
        "# targets\tx86_64-pc-windows-msvc, i686-pc-windows-msvc (structure offsets)",
        f"# um\t{' '.join(um)}",
        f"# km\t{' '.join(km)}",
        "# refused\t" + (" ".join(sorted(refused)) or "-"),
        "# origins\t" + " ".join(f"{o}={n}" for o, n in origins.items()),
        "file\trows\tbytes",
    ] + [f"{k}\t{counts[k]}\t{sizes[k]}" for k in sorted(sizes)]
    write(OUT / "manifest.tsv", manifest)
    for k in sorted(sizes):
        print(f"{k}: {counts[k]} rows, {sizes[k]} bytes")
    print("origins:", origins)
    return 0


def declarator(ty: str, name: str) -> str:
    """Return `ty name` as a C declarator, a function pointer's name inside it."""
    if "(*)" in ty:
        return ty.replace("(*)", f"(*{name})", 1)
    return f"{ty}{name}" if ty.endswith("*") else f"{ty} {name}"


def spell(decl: tuple) -> str:
    """Return a declaration as C, its name parenthesized so a macro of the
    same name does not expand."""
    conv = {"s": "__stdcall ", "f": "__fastcall ", "c": ""}
    name, cc, _, ret, params, variadic = decl
    ps = [declarator(ty, pn if pn != "-" else f"a{i + 1}") for i, (ty, pn) in enumerate(params)]
    if variadic:
        ps.append("...")
    return f"{ret} ({conv[cc]}{name})({', '.join(ps) or 'void'});"


def verify(decls: list[tuple], headers: list[str], dirs: list[str], defines: list[str]) -> set[str]:
    """Compile declarations beside the headers they came from and return
    the names of the ones clang rejects."""
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "verify.c")
        with open(src, "w", encoding="utf-8") as f:
            for h in headers:
                f.write(f"#include <{h}>\n")
            for d in decls:
                f.write(spell(d) + "\n")
        args = unit_args("x86_64-pc-windows-msvc", dirs, defines) + ["-ferror-limit=0", src]
        out = subprocess.run(args, capture_output=True, check=False)
        errs = out.stderr.decode("utf-8", "replace")
    bad: set[str] = set()
    for m in re.finditer(r"verify\.c:([0-9]+):[0-9]+: error:", errs):
        k = int(m.group(1)) - len(headers) - 1
        if 0 <= k < len(decls):
            bad.add(decls[k][0])
            sys.stderr.write(f"refuse {spell(decls[k])}\n")
    if "error:" in errs and not bad:
        sys.stderr.write(errs[:4000])
        raise SystemExit("verify failed outside the declarations")
    return bad


def keep_valid(decls: list[tuple], headers: list[str], dirs: list[str], defines: list[str], picks) -> list[str]:
    """Return the names of the declarations `picks` selects that do not
    compile beside their headers, rechecking until the rest all do."""
    chosen = [d for d in decls if picks(d)]
    refused: list[str] = []
    for _ in range(4):
        bad = verify(chosen, headers, dirs, defines)
        print(f"verify: {len(chosen)} declarations, {len(bad)} refused")
        if not bad:
            return refused
        refused += sorted(bad)
        chosen = [d for d in chosen if d[0] not in bad]
    raise SystemExit("declarations still fail after four rounds")

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
