#!/usr/bin/env python3
"""Agent-task eval: replay fixture tasks against the real server and report what
each one costs an agent.

Usage: python scripts/agent_eval.py [path-to-borer.exe] [--update]

Each task is a question with a known answer on the crackme fixture
(crates/borer-fixtures/examples/crackme.rs, which `cargo build -p
borer-fixtures --examples` puts beside the server in examples/), the
shortest call sequence an agent has for it, and the fact the answers must
hold. Every call goes over stdio JSON-RPC as an agent's would; a resource is
read through the `query` tool, as an agent on a host without resources reads
it. A task starts with load_binary, as a fresh session does, except
`front_door`, which is what a session is handed before its first call (the
instructions, tools/list and prompts/list), and `raw_code`, which loads a
few bytes of hand-assembled x86-64 (RAW_CODE, written to a temporary file
counted as `<blob>`) at a stated base instead of the crackme; the other
blob tasks load their own hand-assembled bytes the same way (BLOBS).

A row per task: the calls, the bytes returned (tool text, error messages,
or the protocol JSON, with the fixture's path counted as `<bin>` and the
repository's as `<root>`, so the directory a checkout sits in does not move
the count) and whether the
fact was found. The rows are compared with the baseline in
scripts/agent_eval.tsv: a fact the baseline found and this run does not
fails the run (exit 1); calls and bytes are reported as deltas, never as a
failure, so a change that costs or saves bytes shows its effect without
blocking. --update rewrites the baseline. Two runs print the same bytes.
"""

from __future__ import annotations

import json
import os
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

from mcp import Client  # noqa: E402

BASELINE = os.path.join(ROOT, "scripts", "agent_eval.tsv")

# A call is (tool, arguments); a tool name starting with "@" is a protocol
# read instead: "@instructions" is the initialize answer's instructions,
# any other the method after the "@".
LOAD = ("load_binary", {"path": "{bin}"})

# Headerless x86-64 code: a call to a local function that returns 42, plus
# one, so it returns 43 (rax=0x2b) from 0x10000.
RAW_CODE = bytes.fromhex(
    "e806000000"  # call 0x1000b
    "4883c001"  # add rax, 1
    "c3"  # ret
    "cc"  # int3
    "b82a000000"  # mov eax, 42
    "c3"  # ret
)

# Headerless x86-64 code that opens a path through a Linux syscall: the
# emulator records it by name with the path decoded. Loaded at 0x10000, the
# path "/tmp/x" sits just past the `ret`.
SYSCALL_CODE = bytes.fromhex(
    "b802000000"  # mov eax, 2 (open)
    "488d3d03000000"  # lea rdi, [rip+3] -> the path
    "0f05"  # syscall
    "c3"  # ret
    "2f746d702f7800"  # "/tmp/x\0"
)

# The single-byte XOR decoder (key 0x5a) the decoder blob calls.
XOR_DECODE = bytes.fromhex(
    "4885d2"  # test rdx, rdx
    "7415"  # je ret
    "4531c0"  # xor r8d, r8d
    "428a0401"  # mov al, [rcx+r8]
    "345a"  # xor al, 0x5a
    "42880401"  # mov [rcx+r8], al
    "49ffc0"  # inc r8
    "4939d0"  # cmp r8, rdx
    "72ee"  # jb loop
    "c3"  # ret
)


def _decoder_blob() -> bytes:
    """A headerless x64 blob: a caller that decodes one planted ciphertext
    from three sites, and the XOR decoder it calls. Mapped with a code
    region at 0x10000 (rx) and a data region at 0x20000 (rw), so the
    ciphertext pointer reads as data."""
    plaintext = b"http://x3.test/c2"
    ciphertext = bytes(b ^ 0x5A for b in plaintext)
    caller = bytearray()
    for k in range(3):
        off = 15 * k  # each site is mov ecx,imm + mov edx,imm + call (5+5+5).
        caller += b"\xb9" + (0x20000).to_bytes(4, "little")
        caller += b"\xba" + len(plaintext).to_bytes(4, "little")
        disp = 0x100 - off - 15  # the decoder sits at file offset 0x100.
        caller += b"\xe8" + disp.to_bytes(4, "little", signed=True)
    caller += b"\xc3"
    blob = bytearray(0x220)
    blob[0 : len(caller)] = caller
    blob[0x100 : 0x100 + len(XOR_DECODE)] = XOR_DECODE
    blob[0x200 : 0x200 + len(ciphertext)] = ciphertext
    return bytes(blob)


DECODER_CODE = _decoder_blob()


def _children_blob() -> bytes:
    """A headerless blob holding a PE32+ x86-64 exe at file offset 0x200:
    0x400 bytes of headers and one .text section whose code returns 7."""
    pe = bytearray(0x400)

    def put(at: int, data: bytes) -> None:
        pe[at : at + len(data)] = data

    sig, opt = 0x80, 0x80 + 24
    row = opt + 0xF0
    put(0, b"MZ")
    put(0x3C, (0x80).to_bytes(4, "little"))
    put(sig, b"PE\0\0")
    put(sig + 4, (0x8664).to_bytes(2, "little"))
    put(sig + 6, (1).to_bytes(2, "little"))
    put(sig + 20, (0xF0).to_bytes(2, "little"))
    put(sig + 22, (0x22).to_bytes(2, "little"))
    put(opt, (0x20B).to_bytes(2, "little"))
    put(opt + 16, (0x1000).to_bytes(4, "little"))
    put(opt + 24, (0x140000000).to_bytes(8, "little"))
    put(opt + 32, (0x1000).to_bytes(4, "little"))
    put(opt + 36, (0x200).to_bytes(4, "little"))
    put(opt + 48, (6).to_bytes(2, "little"))
    put(opt + 56, (0x2000).to_bytes(4, "little"))
    put(opt + 60, (0x200).to_bytes(4, "little"))
    put(opt + 68, (3).to_bytes(2, "little"))
    put(opt + 108, (16).to_bytes(4, "little"))
    put(row, b".text")
    for at, v in ((8, 0x200), (12, 0x1000), (16, 0x200), (20, 0x200), (36, 0x60000020)):
        put(row + at, v.to_bytes(4, "little"))
    put(0x200, bytes.fromhex("b807000000c3"))  # mov eax, 7; ret
    return bytes(0x200) + bytes(pe)


CHILDREN_BLOB = _children_blob()

# How the decoder blob's code and data map: rx code at 0x10000, rw data at
# 0x20000, so the ciphertext pointer is a data pointer.
DECODER_REGIONS = "0x10000@0:0x200:rx,0x20000@0x200:0x20:rw"


def _elf(e_type: int, entry: int, sections: list[tuple]) -> bytes:
    """A little-endian x86-64 ELF64: each section (name, sh_type, flags,
    addr, data, link, entsize) at the file offset equal to its address, one
    RWX PT_LOAD over the file from address 0, and a PT_DYNAMIC over the
    SHT_DYNAMIC section when there is one."""
    out = bytearray(0x1000)
    for _, _, _, addr, data, _, _ in sections:
        if len(out) < addr + len(data):
            out += bytes(addr + len(data) - len(out))
        out[addr : addr + len(data)] = data
    loaded = len(out)
    shstr = bytearray(b"\0")
    names = []
    for name in [s[0] for s in sections] + [".shstrtab"]:
        names.append(len(shstr))
        shstr += name.encode() + b"\0"
    shstr_off = len(out)
    out += shstr
    shoff = (len(out) + 7) & ~7
    count = len(sections) + 2
    out += bytes(shoff + count * 64 - len(out))
    rows = [(0, 0, 0, 0, 0, 0, 0, 0)]
    for i, (_, ty, flags, addr, data, link, entsize) in enumerate(sections):
        rows.append((names[i], ty, flags, addr, addr, len(data), link, entsize))
    rows.append((names[-1], 3, 0, 0, shstr_off, len(shstr), 0, 0))
    for i, (name, ty, flags, addr, off, size, link, entsize) in enumerate(rows):
        out[shoff + i * 64 : shoff + i * 64 + 64] = (
            name.to_bytes(4, "little")
            + ty.to_bytes(4, "little")
            + flags.to_bytes(8, "little")
            + addr.to_bytes(8, "little")
            + off.to_bytes(8, "little")
            + size.to_bytes(8, "little")
            + link.to_bytes(4, "little")
            + bytes(4)
            + (8).to_bytes(8, "little")
            + entsize.to_bytes(8, "little")
        )
    dynamic = [s for s in sections if s[1] == 6]
    out[0:16] = b"\x7fELF\x02\x01\x01" + bytes(9)
    out[16:64] = (
        e_type.to_bytes(2, "little")
        + (62).to_bytes(2, "little")
        + (1).to_bytes(4, "little")
        + entry.to_bytes(8, "little")
        + (64).to_bytes(8, "little")
        + shoff.to_bytes(8, "little")
        + bytes(4)
        + (64).to_bytes(2, "little")
        + (56).to_bytes(2, "little")
        + (1 + len(dynamic)).to_bytes(2, "little")
        + (64).to_bytes(2, "little")
        + count.to_bytes(2, "little")
        + (count - 1).to_bytes(2, "little")
    )

    def phdr(ty: int, at: int, size: int) -> bytes:
        return (
            ty.to_bytes(4, "little")
            + (7).to_bytes(4, "little")
            + at.to_bytes(8, "little") * 3
            + size.to_bytes(8, "little") * 2
            + (0x1000).to_bytes(8, "little")
        )

    out[64:120] = phdr(1, 0, loaded)
    for _, _, _, addr, data, _, _ in dynamic:
        out[120:176] = phdr(2, addr, len(data))
    return bytes(out)


# An ELF whose entry is `lea eax, [rdi+1]; ret`: the System V first argument
# is rdi, which `emulate`'s a1= sets on an ELF.
ELF_ARG_CODE = _elf(2, 0x1000, [(".text", 1, 6, 0x1000, bytes.fromhex("8d4701c3"), 0, 0)])


def _pie_blob() -> bytes:
    """An x86-64 PIE as lld links one: the function at 0x1010 (`mov eax,42;
    ret`) is reached only through the .data.rel.ro slot at 0x2000, zero on
    disk, which one R_X86_64_RELATIVE entry fills."""
    text = bytearray(b"\xcc" * 0x20)
    text[0:3] = bytes.fromhex("31c0c3")  # xor eax, eax; ret
    text[0x10:0x16] = bytes.fromhex("b82a000000c3")  # mov eax, 42; ret
    rela = (
        (0x2000).to_bytes(8, "little") + (8).to_bytes(8, "little") + (0x1010).to_bytes(8, "little")
    )
    dyn = b"".join(
        t.to_bytes(8, "little") + v.to_bytes(8, "little")
        for t, v in [(7, 0x3000), (8, len(rela)), (9, 24), (0, 0)]
    )
    return _elf(
        3,
        0x1000,
        [
            (".text", 1, 6, 0x1000, bytes(text), 0, 0),
            (".data.rel.ro", 1, 3, 0x2000, bytes(16), 0, 0),
            (".rela.dyn", 4, 2, 0x3000, rela, 0, 24),
            (".dynamic", 6, 3, 0x3400, dyn, 0, 16),
        ],
    )


PIE_CODE = _pie_blob()


def _go_blob() -> bytes:
    """A stripped Go 1.20 executable: no symbol table, only the pclntab in
    .gopclntab naming main.main (0x1000) and main.add (0x1010, `lea rax,
    [rax+rbx]; ret`, Go's a + b in its register ABI)."""
    text = bytearray(b"\xcc" * 0x20)
    text[0:3] = bytes.fromhex("31c0c3")  # xor eax, eax; ret
    text[0x10:0x15] = bytes.fromhex("488d0418c3")  # lea rax, [rax+rbx]; ret
    funcs = [(0x00, "main.main"), (0x10, "main.add")]
    names = b"".join(n.encode() + b"\0" for _, n in funcs)
    pcln = (72 + len(names) + 7) & ~7
    functab = (len(funcs) + 1) * 8
    table = bytearray(pcln + functab + len(funcs) * 44)
    table[0:8] = bytes.fromhex("f1ffffff00000108")
    for k, v in enumerate([len(funcs), 0, 0x1000, 72, pcln, pcln, pcln, pcln]):
        table[8 + k * 8 : 16 + k * 8] = v.to_bytes(8, "little")
    table[72 : 72 + len(names)] = names
    name_off = 0
    for i, (entry, name) in enumerate(funcs):
        record = functab + i * 44
        table[pcln + i * 8 : pcln + i * 8 + 8] = entry.to_bytes(4, "little") + record.to_bytes(
            4, "little"
        )
        table[pcln + record : pcln + record + 8] = entry.to_bytes(4, "little") + name_off.to_bytes(
            4, "little"
        )
        name_off += len(name) + 1
    end = pcln + len(funcs) * 8
    table[end : end + 4] = (0x20).to_bytes(4, "little")
    return _elf(
        2,
        0x1000,
        [
            (".text", 1, 6, 0x1000, bytes(text), 0, 0),
            (".gopclntab", 1, 2, 0x2000, bytes(table), 0, 0),
        ],
    )


GO_CODE = _go_blob()

# A static x86-64 ELF with no imports whose entry opens a socket and
# connects it through `syscall`: its reach shows only in its syscall sites.
STATIC_CODE = _elf(
    2,
    0x1000,
    [
        (
            ".text",
            1,
            6,
            0x1000,
            bytes.fromhex(
                "b829000000"  # mov eax, 41 (socket)
                "bf02000000"  # mov edi, 2
                "be01000000"  # mov esi, 1
                "31d2"  # xor edx, edx
                "0f05"  # syscall
                "89c7"  # mov edi, eax
                "b82a000000"  # mov eax, 42 (connect)
                "0f05"  # syscall
                "c3"  # ret
            ),
            0,
            0,
        )
    ],
)


def _le(*fields: tuple[int, int]) -> bytes:
    """Little-endian fields, each (value, width in bytes), back to back."""
    return b"".join(v.to_bytes(n, "little") for v, n in fields)


def _macho(cpu: int, segs: list[tuple], extra: list[bytes]) -> bytes:
    """A little-endian 64-bit Mach-O PIE executable: each segment (name,
    vmaddr, fileoff, data, prot, sections) at its file offset with its
    sections (name, addr, size, flags), then the extra load commands; the
    header and commands lie over the first segment's first bytes."""
    out = bytearray()
    cmds = bytearray()
    for name, vmaddr, fileoff, data, prot, sections in segs:
        if len(out) < fileoff + len(data):
            out += bytes(fileoff + len(data) - len(out))
        out[fileoff : fileoff + len(data)] = data
        seg = name.encode().ljust(16, b"\0")
        vmsize = (len(data) + 0xFFF) & ~0xFFF
        cmds += _le((0x19, 4), (72 + 80 * len(sections), 4)) + seg
        cmds += _le((vmaddr, 8), (vmsize, 8), (fileoff, 8), (len(data), 8))
        cmds += _le((prot, 4), (prot, 4), (len(sections), 4), (0, 4))
        for sect, addr, size, flags in sections:
            cmds += sect.encode().ljust(16, b"\0") + seg
            cmds += _le((addr, 8), (size, 8), (fileoff + addr - vmaddr, 4), (0, 12))
            cmds += _le((flags, 4), (0, 12))
    for c in extra:
        cmds += c
    head = _le((0xFEEDFACF, 4), (cpu, 4), (3, 4), (2, 4), (len(segs) + len(extra), 4))
    out[0 : 32 + len(cmds)] = head + _le((len(cmds), 4), (0x200000, 4), (0, 4)) + cmds
    return bytes(out)


def _chained_pie(text: bytes, code: tuple, data: bytes, sections: list[tuple], name: str) -> bytes:
    """An x86-64 Mach-O PIE at 0x100000000: __TEXT is `text`, its code in
    __text at `code` (offset past the base, size), entered at its start;
    __DATA_CONST at 0x100001000 is `data`, which holds one
    DYLD_CHAINED_PTR_64_OFFSET chain starting at its first word; `sections`
    (name, address, size, flags) lie in either; the one import, `name`,
    comes from libSystem."""
    entry, size = code
    base = 0x100000000
    starts = _le((24, 4), (0x1000, 2), (6, 2), (0x1000, 8), (0, 4), (1, 2), (0, 2))
    image = _le((3, 4), (0, 4), (16, 4), (0, 4)) + starts
    names = b"\0" + name.encode() + b"\0"
    fixups = _le((0, 4), (32, 4), (72, 4), (76, 4), (1, 4), (1, 4), (0, 4), (0, 4))
    fixups += image + _le((1 | 1 << 9, 4)) + names
    lib = b"/usr/lib/libSystem.B.dylib".ljust(32, b"\0")
    dylib = _le((0xC, 4), (56, 4), (24, 4), (0, 12)) + lib
    at = 0x1000 + len(data)
    text_sections = [("__text", base + entry, size, 0x80000400)]
    text_sections += [s for s in sections if s[1] < base + 0x1000]
    return _macho(
        0x01000007,
        [
            ("__TEXT", base, 0, text, 5, text_sections),
            (
                "__DATA_CONST",
                base + 0x1000,
                0x1000,
                data,
                3,
                [s for s in sections if s[1] >= base + 0x1000],
            ),
            ("__LINKEDIT", base + 0x10000, at, fixups, 1, []),
        ],
        [
            _le((0x80000028, 4), (24, 4), (entry, 8), (0, 8)),
            _le((0x80000034, 4), (16, 4), (at, 4), (len(fixups), 4)),
            dylib,
        ],
    )


def _macho_blob() -> bytes:
    """An x86-64 Mach-O PIE with chained fixups as ld64 writes them for
    macOS 12: the function at 0x100000410 (`mov eax,42; ret`) is reached
    only through the __DATA_CONST slot at 0x100001000, which on disk holds
    its DYLD_CHAINED_PTR_64_OFFSET rebase (offset 0x410, next 2 strides),
    and the slot after it binds _malloc."""
    text = bytearray(0x1000)
    text[0x400:0x403] = bytes.fromhex("31c0c3")  # xor eax, eax; ret
    text[0x410:0x416] = bytes.fromhex("b82a000000c3")  # mov eax, 42; ret
    data = _le((0x410 | 2 << 51, 8), (1 << 63, 8))
    const = [("__const", 0x100001000, 16, 0)]
    return _chained_pie(bytes(text), (0x400, 0x20), data, const, "_malloc")


def _objc_blob() -> bytes:
    """An x86-64 Mach-O PIE sending Objective-C messages: main (0x100000800)
    loads the class reference to Foo into rdi and the selector reference to
    `shared` into rsi and calls objc_msgSend through its slot, then sends
    `bar` to the result. The references, Foo's class_t and its class_ro_t
    are pointers only the chained fixups make."""
    text = bytearray(0x1000)
    main = bytes.fromhex("488b3d31080000")  # mov rdi, [rip+0x831] -> classref
    main += bytes.fromhex("488b351a080000")  # mov rsi, [rip+0x81a] -> selref shared
    main += bytes.fromhex("ff15ec070000")  # call [rip+0x7ec] -> objc_msgSend
    main += bytes.fromhex("4889c7")  # mov rdi, rax
    main += bytes.fromhex("488b3502080000")  # mov rsi, [rip+0x802] -> selref bar
    main += bytes.fromhex("ff15dc070000")  # call [rip+0x7dc] -> objc_msgSend
    main += b"\xc3"  # ret
    text[0x800 : 0x800 + len(main)] = main
    text[0xC00:0xC0B] = b"bar\0shared\0"
    text[0xC40:0xC44] = b"Foo\0"
    data = bytearray(0xC0)
    chain = [(0x00, 1 << 63), (0x20, 0xC00), (0x28, 0xC04), (0x38, 0x1040)]
    chain += [(0x60, 0x1070), (0x88, 0xC40)]
    for k, (at, word) in enumerate(chain):
        nxt = (chain[k + 1][0] - at) // 4 if k + 1 < len(chain) else 0
        data[at : at + 8] = (word | nxt << 51).to_bytes(8, "little")
    sections = [
        ("__objc_methname", 0x100000C00, 0x10, 2),
        ("__objc_classname", 0x100000C40, 0x10, 2),
        ("__got", 0x100001000, 8, 6),
        ("__objc_selrefs", 0x100001020, 0x10, 5),
        ("__objc_classrefs", 0x100001038, 8, 0),
        ("__objc_data", 0x100001040, 0x28, 0),
        ("__objc_const", 0x100001070, 0x48, 0),
    ]
    return _chained_pie(bytes(text), (0x800, 0x30), bytes(data), sections, "_objc_msgSend")


MACHO_CODE = _macho_blob()
OBJC_CODE = _objc_blob()


def _dotnet_blob() -> bytes:
    """A PE32+ .NET assembly `Hello`: `Ns.Program` with `Main` (an IL body
    at RVA 0x1050) and `MessageBox` (a P/Invoke of user32.dll!MessageBoxW),
    and one user string; the CLR header at 0x1000, the metadata at 0x1080."""
    strings = bytearray(b"\0")

    def s(name: str) -> bytes:
        at = len(strings)
        strings.extend(name.encode() + b"\0")
        return at.to_bytes(2, "little")

    def c(v: int) -> bytes:
        return v.to_bytes(2, "little")

    def d(v: int) -> bytes:
        return v.to_bytes(4, "little")

    def row(*cells: bytes) -> bytes:
        return b"".join(cells)

    tables = [
        (0x00, [row(c(0), s("Hello.exe"), c(1), c(0), c(0))]),
        # <Module>, then Ns.Program owning both methods.
        (
            0x02,
            [
                row(d(0), s("<Module>"), c(0), c(0), c(1), c(1)),
                row(d(0x100001), s("Program"), s("Ns"), c(0), c(1), c(1)),
            ],
        ),
        # Main, an IL body, then MessageBox, a P/Invoke: no body, PinvokeImpl set.
        (
            0x06,
            [
                row(d(0x1050), c(0), c(0x96), s("Main"), c(1), c(1)),
                row(d(0), c(0x80), c(0x2096), s("MessageBox"), c(1), c(1)),
            ],
        ),
        (0x1A, [s("user32.dll")]),
        # MessageBox (MethodDef 2, MemberForwarded tag 1) bound to MessageBoxW.
        (0x1C, [row(c(0x104), c((2 << 1) | 1), s("MessageBoxW"), c(1))]),
        (0x20, [row(d(0x8004), c(1), c(0), c(0), c(0), d(0), c(0), s("Hello"), c(0))]),
    ]
    stream = bytearray(bytes.fromhex("0000000002000001"))
    stream += sum(1 << t for t, _ in tables).to_bytes(8, "little") + bytes(8)
    stream += b"".join(d(len(rs)) for _, rs in tables) + b"".join(b"".join(rs) for _, rs in tables)
    text = "http://c2.example.test/gate.php".encode("utf-16-le")
    us = bytes([0, len(text) + 1]) + text + b"\0"
    pad = lambda b: bytes(b) + bytes(-len(b) % 4)  # noqa: E731
    streams = [
        (b"#~", pad(stream)),
        (b"#Strings", pad(strings)),
        (b"#US", pad(us)),
        (b"#GUID", bytes(16)),
        (b"#Blob", pad(b"\0\x03\x20\0")),
    ]
    head = b"BSJB" + c(1) + c(1) + d(0) + d(12) + b"v4.0.30319\0\0" + c(0) + c(len(streams))
    off = len(head) + sum(8 + len(pad(n + b"\0")) for n, _ in streams)
    body = b""
    for name, data in streams:
        head += d(off + len(body)) + d(len(data)) + pad(name + b"\0")
        body += data
    meta = head + body
    text_sec = bytearray(0x80) + meta
    text_sec[0:24] = d(72) + c(2) + c(5) + d(0x1080) + d(len(meta)) + d(1) + d(0x06000001)
    text_sec[0x50:0x53] = bytes.fromhex("0a002a")  # tiny IL header; nop; ret
    pe = bytearray(0x200)

    def put(at: int, data: bytes) -> None:
        pe[at : at + len(data)] = data

    sig, opt = 0x80, 0x80 + 24
    row = opt + 0xF0
    put(0, b"MZ")
    put(0x3C, d(0x80))
    put(sig, b"PE\0\0")
    put(sig + 4, c(0x8664) + c(1))
    put(sig + 20, c(0xF0) + c(0x22))
    put(opt, c(0x20B))
    put(opt + 24, (0x140000000).to_bytes(8, "little"))
    put(opt + 32, d(0x1000) + d(0x200))
    put(opt + 48, c(6))
    put(opt + 56, d(0x2000) + d(0x200))
    put(opt + 68, c(3))
    put(opt + 108, d(16))
    put(opt + 112 + 14 * 8, d(0x1000) + d(72))
    raw = len(text_sec) + (-len(text_sec) % 0x200)
    put(row, b".text")
    for at, v in ((8, len(text_sec)), (12, 0x1000), (16, raw), (20, 0x200), (36, 0x60000020)):
        put(row + at, d(v))
    return bytes(pe) + pad(text_sec) + bytes(raw - len(pad(text_sec)))


DOTNET_CODE = _dotnet_blob()

# Headerless x86-64 code under the /GS cookie, loaded at 0x10000: the
# prologue stores the cookie (at 0x10100) mixed with rsp, the epilogue hands
# it back to the cookie check at 0x10040, which is named by its shape.
GS_CODE = (
    bytes.fromhex(
        "4883ec28"  # sub rsp, 0x28
        "488b05f5000000"  # mov rax, [rip+0xf5] -> the cookie
        "4831e0"  # xor rax, rsp
        "4889442420"  # mov [rsp+0x20], rax
        "488d4101"  # lea rax, [rcx+1]
        "488b4c2420"  # mov rcx, [rsp+0x20]
        "4831e1"  # xor rcx, rsp
        "e81c000000"  # call 0x10040
        "4883c428"  # add rsp, 0x28
        "c3"  # ret
    ).ljust(0x40, b"\xcc")
    + bytes.fromhex(
        "483b0db9000000"  # cmp rcx, [rip+0xb9] -> the cookie
        "7510"  # jne fail
        "48c1c110"  # rol rcx, 16
        "66f7c1ffff"  # test cx, 0xffff
        "7501"  # jne fail2
        "c3"  # ret
        "48c1c910"  # ror rcx, 16 (fail2)
        "cc"  # int3 (fail)
    ).ljust(0xC0, b"\xcc")
    + (0x2B992DDFA232).to_bytes(8, "little")
)


def _panic_blob() -> bytes:
    """Headerless x86-64 code, loaded at 0x10000, whose bounds check raises
    a Rust panic: `panic_bounds_check` at 0x10040, named by the message it
    formats (at 0x10200), is handed the `core::panic::Location` at 0x10300,
    which names a crate file (at 0x10110), line 1015, column 32."""
    path = (
        b"C:\\Users\\me\\.cargo\\registry\\src\\index.crates.io-1949cf8c6b5b557f"
        b"\\rhai-1.26.1\\src\\parser.rs"
    )
    code = (
        bytes.fromhex(
            "4839d1"  # cmp rcx, rdx
            "7305"  # jae fail
            "498b04c8"  # mov rax, [r8+rcx*8]
            "c3"  # ret
            "4c8d05ef020000"  # lea r8, [rip+0x2ef] -> the location
            "e82a000000"  # call 0x10040
        ).ljust(0x40, b"\xcc")
        + bytes.fromhex(
            "55"  # push rbp
            "4883ec50"  # sub rsp, 0x50
            "48894c2448"  # mov [rsp+0x48], rcx
            "4889542440"  # mov [rsp+0x40], rdx
            "4c89442438"  # mov [rsp+0x38], r8
            "488d0da5010000"  # lea rcx, [rip+0x1a5] -> the message
            "e820000000"  # call 0x10080
        ).ljust(0x40, b"\xcc")
        + bytes.fromhex("0f0b")  # ud2
    )
    blob = code.ljust(0x110, b"\xcc") + path
    blob = blob.ljust(0x200, b"\x00") + b"\x20index out of bounds: the len is \xc0\x12 but"
    blob = blob.ljust(0x300, b"\x00") + (0x10110).to_bytes(8, "little")
    blob += len(path).to_bytes(8, "little") + (1015).to_bytes(4, "little")
    return blob + (32).to_bytes(4, "little")


PANIC_CODE = _panic_blob()

# Each extra blob the tasks load: its bytes and the marker a path counts as,
# so the directory a checkout sits in does not move the byte count.
BLOBS = {
    "blob": (RAW_CODE, "<blob>"),
    "syscall": (SYSCALL_CODE, "<syscall>"),
    "decoder": (DECODER_CODE, "<decoder>"),
    "elfargs": (ELF_ARG_CODE, "<elfargs>"),
    "pie": (PIE_CODE, "<pie>"),
    "go": (GO_CODE, "<go>"),
    "children": (CHILDREN_BLOB, "<children>"),
    "static": (STATIC_CODE, "<static>"),
    "macho": (MACHO_CODE, "<macho>"),
    "objc": (OBJC_CODE, "<objc>"),
    "dotnet": (DOTNET_CODE, "<dotnet>"),
    "gs": (GS_CODE, "<gs>"),
    "panic": (PANIC_CODE, "<panic>"),
}

# (task, the question it answers, calls, the fact the answers must hold)
TASKS = [
    (
        "front_door",
        "what a session is handed before its first call, and whether it starts at the triage",
        [("@instructions", {}), ("@tools/list", {}), ("@prompts/list", {})],
        "load_binary, then query borer://triage",
    ),
    (
        "orient",
        "what the file is and which function to read first",
        [LOAD, ("query", {"uri": "borer://triage"})],
        "crackme::check_serial",
    ),
    (
        "serial_constant",
        "the value the serial check compares its accumulator with",
        [LOAD, ("decompile", {"address": "crackme::check_serial"})],
        "0xdeadbeef",
    ),
    (
        "marker_user",
        "which function uses the marker string",
        [LOAD, ("find_function_by_string", {"filter": "BORER-CRACKME"})],
        "crackme::check_serial",
    ),
    (
        "caller",
        "who calls the serial check",
        [LOAD, ("xrefs", {"address": "crackme::check_serial"})],
        "crackme::main",
    ),
    (
        "emulate_serial",
        "what the serial check returns for the key 0",
        [LOAD, ("query", {"uri": "borer://emulate/crackme::check_serial,a1=0"})],
        "rax=0x0 ",
    ),
    (
        "emulate_grammar",
        "how to pass arguments to an emulation, asked of the bare template",
        [LOAD, ("query", {"uri": "borer://emulate"})],
        "aN=",
    ),
    (
        "uri_typo",
        "a mistyped resource, answered with the one meant",
        [LOAD, ("query", {"uri": "borer://emulat"})],
        "borer://emulate/{address}",
    ),
    (
        "name_typo",
        "a mistyped function name, answered with the one meant",
        [LOAD, ("decompile", {"address": "chk_serial"})],
        "crackme::check_serial",
    ),
    (
        "playbook",
        "the triage playbook read as a resource, by an agent that cannot get prompts",
        [LOAD, ("query", {"uri": "borer://playbook/triage"})],
        "cheapest first",
    ),
    (
        "call_args",
        "every call site of the serial check with the argument each passes",
        [LOAD, ("query", {"uri": "borer://calls/crackme::check_serial"})],
        "crackme::check_serial(",
    ),
    (
        "next_hint",
        "which resource the serial check's summary says to read next",
        [LOAD, ("function_summary", {"address": "crackme::check_serial"})],
        "# next: borer://solve/",
    ),
    (
        "resume",
        "where the session stands after a paged read: what it read, cut and paged",
        [
            LOAD,
            ("query", {"uri": "borer://help!offset=10!limit=5"}),
            ("query", {"uri": "borer://session"}),
        ],
        "capped paged  borer://help!offset=10!limit=5",
    ),
    (
        "raw_code",
        "what headerless code loaded at a stated base returns",
        [
            ("load_binary", {"path": "{blob}", "arch": "x64", "base": "0x10000"}),
            ("query", {"uri": "borer://emulate/0x10000"}),
        ],
        "rax=0x2b ",
    ),
    (
        "emulate_syscall",
        "which syscall emulated headerless code makes, with its path decoded",
        [
            ("load_binary", {"path": "{syscall}", "arch": "x64", "base": "0x10000"}),
            ("query", {"uri": "borer://emulate/0x10000"}),
        ],
        'syscall 2 open("/tmp/x"',
    ),
    (
        "emulate_elf_args",
        "what an ELF function returns for a1=5, its first argument in rdi",
        [
            ("load_binary", {"path": "{elfargs}"}),
            ("query", {"uri": "borer://emulate/0x1000,a1=5"}),
        ],
        "rax=0x6 ",
    ),
    (
        "pie_table_xref",
        "where a PIE's function reached only through a relocated table is referenced",
        [
            ("load_binary", {"path": "{pie}"}),
            ("xrefs", {"address": "0x1010"}),
        ],
        "-: 0x2000 table",
    ),
    (
        "go_names",
        "what a stripped Go binary's function computes, named by its pclntab",
        [
            ("load_binary", {"path": "{go}"}),
            ("decompile", {"address": "main.add"}),
        ],
        "return a1 + a2;",
    ),
    (
        "static_capabilities",
        "what a static ELF with no imports can do, read from its syscall sites",
        [
            ("load_binary", {"path": "{static}"}),
            ("query", {"uri": "borer://capabilities"}),
        ],
        "connect (syscall), socket (syscall)",
    ),
    (
        "dotnet_pinvoke",
        "which native function a .NET assembly calls through P/Invoke, read from its metadata",
        [
            ("load_binary", {"path": "{dotnet}"}),
            ("query", {"uri": "borer://clr/pinvoke"}),
        ],
        "Ns.Program::MessageBox	user32.dll!MessageBoxW",
    ),
    (
        "decoded_strings",
        "the strings a decoder produces, recovered by running it at its call sites",
        [
            (
                "load_binary",
                {"path": "{decoder}", "arch": "x64", "regions": DECODER_REGIONS},
            ),
            ("query", {"uri": "borer://decoded"}),
        ],
        "http://x3.test/c2",
    ),
    (
        "test_vectors",
        "test vectors and a harness for reimplementing the serial check",
        [LOAD, ("query", {"uri": "borer://vectors/crackme::check_serial"})],
        "got = check_serial(",
    ),
    (
        "tlsh_digest",
        "the TLSH string a threat feed would carry for the file",
        [LOAD, ("query", {"uri": "borer://hashes"})],
        "tlsh          T1",
    ),
    (
        "child_program",
        "the program a blob holds, listed and then opened as one of its own",
        [
            ("load_binary", {"path": "{children}"}),
            ("query", {"uri": "borer://children"}),
            ("load_binary", {"path": "{children}@0x200"}),
        ],
        "parent:  <children> at file offset 0x200, 0x400 bytes",
    ),
    (
        "macho_chained_xref",
        "where a chained-fixups Mach-O's function reached only through a rebased slot is referenced",
        [
            ("load_binary", {"path": "{macho}"}),
            ("xrefs", {"address": "0x100000410"}),
        ],
        "-: 0x100001000 table",
    ),
    (
        "objc_messages",
        "which Objective-C messages a stripped Mach-O's entry sends, read from its selector and class references",
        [
            ("load_binary", {"path": "{objc}"}),
            ("function_summary", {"address": "0x100000800"}),
        ],
        "messages: 2 [[Foo shared], [[Foo shared] bar]]",
    ),
    (
        "gs_cookie_folded",
        "what a function under the /GS cookie computes, its cookie left out",
        [
            ("load_binary", {"path": "{gs}", "arch": "x64", "base": "0x10000"}),
            ("decompile", {"address": "0x10000"}),
        ],
        "// folded: /GS cookie, 1 check",
    ),
    (
        "rust_panic_location",
        "where in the source a Rust function's bounds check panics",
        [
            ("load_binary", {"path": "{panic}", "arch": "x64", "base": "0x10000"}),
            ("decompile", {"address": "0x10000"}),
        ],
        "// at rhai-1.26.1/src/parser.rs:1015:32",
    ),
]


def server_exe(args: list[str]) -> str:
    """The server to drive: the first argument, else the debug build."""
    if args:
        return os.path.abspath(args[0])
    target = os.environ.get("CARGO_TARGET_DIR") or os.path.join(ROOT, "target")
    return os.path.join(target, "debug", "borer.exe" if sys.platform == "win32" else "borer")


def fixture(exe: str) -> str:
    """The crackme example built beside the server, or exit 2 naming the build."""
    examples = os.path.join(os.path.dirname(exe), "examples")
    for name in ("crackme.exe", "crackme"):
        path = os.path.join(examples, name)
        if os.path.isfile(path):
            return path
    raise SystemExit(f"no crackme in {examples}; run cargo build -p borer-fixtures --examples")


def answer(client: Client, tool: str, args: dict) -> str:
    """What one call hands the agent: the tool's text or error, or a protocol read."""
    if tool == "@instructions":
        return client.instructions
    if tool.startswith("@"):
        return json.dumps(client.call(tool[1:], args))
    reply = client.request("tools/call", {"name": tool, "arguments": args})
    if "error" in reply:
        return reply["error"].get("message", "")
    return "\n".join(c.get("text", "") for c in reply["result"].get("content", []))


def spellings(path: str) -> list[str]:
    """A path as the answers may spell it: as given, and with either separator,
    plain or escaped as a C string writes a backslash."""
    forms = {path, path.replace("\\", "/"), path.replace("/", "\\")}
    forms |= {f.replace("\\", "\\\\") for f in list(forms)}
    return sorted(forms, key=len, reverse=True)


def run(exe: str, binary: str) -> list[tuple[str, int, int, int]]:
    """Every task's (name, calls, bytes, found), in task order."""
    paths = {}
    try:
        for key, (code, _) in BLOBS.items():
            with tempfile.NamedTemporaryFile(
                prefix="borer-eval-", suffix=".bin", delete=False
            ) as f:
                f.write(code)
                paths[key] = f.name
        return run_tasks(exe, binary, paths)
    finally:
        for p in paths.values():
            os.remove(p)


def run_tasks(exe: str, binary: str, blobs: dict[str, str]) -> list[tuple[str, int, int, int]]:
    """Every task's row, the crackme at `binary` and each blob at its path."""
    paths = [(f, "<bin>") for f in spellings(binary)]
    for key, path in blobs.items():
        paths += [(f, BLOBS[key][1]) for f in spellings(path)]
    paths += [(f, "<root>") for f in spellings(ROOT)]
    paths.sort(key=lambda fm: len(fm[0]), reverse=True)
    rows = []
    client = Client(exe)
    try:
        for name, _, calls, fact in TASKS:
            texts = []
            for tool, args in calls:
                filled = {}
                for k, v in args.items():
                    v = v.replace("{bin}", binary)
                    for key, path in blobs.items():
                        v = v.replace("{" + key + "}", path)
                    filled[k] = v
                text = answer(client, tool, filled)
                for form, mark in paths:
                    text = text.replace(form, mark)
                texts.append(text)
            size = sum(len(t.encode("utf-8")) for t in texts)
            found = int(any(fact in t for t in texts))
            rows.append((name, len(calls), size, found))
    finally:
        client.close()
    return rows


def read_baseline() -> dict[str, tuple[int, int, int]]:
    """The baseline's rows by task; empty when the file is missing."""
    if not os.path.isfile(BASELINE):
        return {}
    out = {}
    with open(BASELINE, encoding="utf-8") as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            name, calls, size, found = line.rstrip("\n").split("\t")
            out[name] = (int(calls), int(size), int(found))
    return out


def table(rows: list[tuple[str, int, int, int]]) -> str:
    """The rows as the baseline file holds them."""
    body = "".join(f"{n}\t{c}\t{b}\t{f}\n" for n, c, b, f in rows)
    return "# task\tcalls\tbytes\tfound\n" + body


def delta(now: tuple[int, int, int], then: tuple[int, int, int] | None) -> str:
    """How a row differs from its baseline row, `=` when it does not."""
    if then is None:
        return "new"
    parts = []
    for what, a, b in (("calls", now[0], then[0]), ("bytes", now[1], then[1])):
        if a != b:
            parts.append(f"{what} {a - b:+d}")
    if now[2] != then[2]:
        parts.append("found" if now[2] else "LOST")
    return ", ".join(parts) or "="


def main(argv: list[str]) -> int:
    update = "--update" in argv
    args = [a for a in argv if a != "--update"]
    exe = server_exe(args)
    rows = run(exe, fixture(exe))
    if update:
        with open(BASELINE, "w", encoding="utf-8", newline="\n") as f:
            f.write(table(rows))
    base = read_baseline()
    calls = sum(r[1] for r in rows)
    size = sum(r[2] for r in rows)
    found = sum(r[3] for r in rows)
    print(f"# agent eval: {len(rows)} tasks, {found} found, {calls} calls, {size} bytes")
    print("# task\tcalls\tbytes\tfound\tvs baseline")
    lost = []
    for name, c, b, f in rows:
        then = base.get(name)
        print(f"{name}\t{c}\t{b}\t{f}\t{delta((c, b, f), then)}")
        if then is not None and then[2] and not f:
            lost.append(name)
    if lost:
        print(f"# lost a fact the baseline found: {', '.join(lost)}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
