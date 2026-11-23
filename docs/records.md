# Export records

`borer export <binary> --c out.c --records` writes `out.records.jsonl` beside
the C file: what borer states about each definition in `out.c`, so a
benchmark or another tool can map variables and lines to the binary without
reading borer's source. Without `--records` the C file is the same bytes,
and with it too.

## Compatibility

A reader ignores keys it does not know and `home` kinds it does not know
(reading them as `unknown`). `version` rises only when a change would break
a reader of the version before; adding a key or a `home` kind does not
raise it.

## The file

JSON Lines, UTF-8. The first line says what the file is and which C file
it describes:

```json
{"c":"out.c","c_bytes":8232026,"c_fnv1a64":"9ae16a3b2f90c76b","format":"borer-records","version":1}
```

`c` is the C file's bare name, no directory. `c_bytes` is its length in
bytes and `c_fnv1a64` the 64-bit FNV-1a hash of all its bytes (offset basis
0xcbf29ce484222325, prime 0x100000001b3), 16 lowercase hex digits. A reader
checks both against the C file beside it before trusting a record: a
records file whose check fails belongs to another export (an export without
`--records` leaves an older records file where it was, and a failure
between writing the two files leaves the old one), and its line numbers do
not apply.

Every further line is one definition, in the order `out.c` holds them. An
example, wrapped here (each record is one line in the file):

```json
{"blocks":[{"cut":false,"start":"0x1000","starts":["0x1000","0x1006","0x1009","0x100c"]}],
 "entry":"0x1000","line":17,"lines":[{"block":"0x1000","line":4}],"name":"sub_1000",
 "variables":[{"home":{"kind":"register","name":"rcx"},"lines":[1,4],"name":"a1",
               "param":0,"type":"uint32_t"}]}
```

| field | meaning |
|---|---|
| `line` | Line of `out.c`, from 1, holding the definition's head: its signature, right under the `// <name> @ 0x<entry>:` comment. Every other line number in the record counts from this head as line 1, the numbering a reader that cuts the file at each definition sees. |
| `name` | The function's name as the head spells it. |
| `entry` | The function's entry, an address. |
| `variables` | The head's parameters in order, then the locals the body declares, in declaration order. |
| `variables[].name` | The name as printed. |
| `variables[].type` | The C type as printed: `uint32_t`, `char *` (stars after a space), `uint8_t[48]` for an array (its extent included). |
| `variables[].param` | Position in the head, from 0; `null` for a local. |
| `variables[].home` | Where the variable lives, an object whose `kind` says which (below). |
| `variables[].lines` | Lines naming the variable as an identifier, ascending. Comments, string literals and the `extern` prototypes a body declares (their parameter names are their own) name nothing. |
| `lines` | `{"line": n, "block": "0x…"}` for each line that stands for one basic block, ascending by `line`. A line no block spells (braces, `if` and loop tests the structurer wrote, declarations, lines a rewrite made from several) is absent, never guessed. |
| `blocks` | Every block a `lines` entry names, ascending by `start`. |
| `blocks[].start` | The block's first instruction, an address. |
| `blocks[].starts` | Its instruction starts, ascending. A line came from some of them, not necessarily all. |
| `blocks[].cut` | True when `starts` lists only some of the block's instructions, or none: its bytes could not all be decoded; the block a line names is no block of the function's own (`starts` is then empty); the record reached 4096 starts over all its blocks; or the export reached its budget of starts, the input file's size in bytes plus 4096, over all its records (functions that overlap would otherwise list their shared instructions once each, the square of the file). A block past a limit lists what was left, or none. |

### `home`

| kind | keys | meaning |
|---|---|---|
| `register` | `name` | The register, by its full name at the binary's word size: `rcx`, `xmm0` on x86-64; `ecx` on 32-bit x86; `x0`, `v0` on arm64; `r0` on ARM32; `a0` on RISC-V. A parameter's is where its calling convention passes it at entry; a local's is the register whose value it is (borer keeps a register's name only for such a variable). |
| `frame` | `base`, `offset` | A stack slot. `base` names what `offset` counts from; version 1 always writes `"cfa"`, the canonical frame address. `offset` is signed bytes from it, negative below it. |
| `unknown` | | borer states no single home: a parameter its convention passes in several pieces or that borer cannot place, a stack slot the code addressed through a stack pointer it rounded down (`and rsp, -32`; the true place is up to the alignment lower) or through a frame pointer set after the rounding, a `varN` value, and any other name. |

The canonical frame address (CFA) is the stack pointer's value just before
the call instruction ran: the entry stack pointer plus the return address the
call pushed on x86-64 (8 bytes) and 32-bit x86 (4 bytes), and the entry stack
pointer itself on arm64, ARM32 and RISC-V. It is a fact of the machine, the
same whichever compiler built the code; a compiler's own frame base (DWARF's
`DW_AT_frame_base`) is not something borer states, and a reader that scores
against one converts per function.

- x86-64: after `push rbp; mov rbp, rsp`, `rbp` is CFA-16. A local at
  `[rbp-0x10]` is `offset` -32 (borer names it `local_10`); the first stack
  argument under System V, at entry `rsp`+8, is `offset` 0, and under
  Microsoft x64, past the 32-byte home space, 32.
- 32-bit x86: the first cdecl argument, at entry `esp`+4, is `offset` 0 and
  the second 4; a local at `[ebp-8]` after `push ebp; mov ebp, esp` is
  `offset` -16.
- arm64: after `stp x29, x30, [sp, #-32]!`, a local at `[sp, #24]` is
  `offset` -8 (borer names it `local_8`); a stack argument at entry `sp`+0
  is `offset` 0.

A local named `local_<hex>` with no agent's name on it is at `offset`
-(0x`<hex>` + 16) on x86-64, -(0x`<hex>` + 8) on 32-bit x86 and -0x`<hex>`
elsewhere. A home comes from the variable's key, not its name: a slot an
agent renamed keeps its `frame` home.

## Addresses

Every address is a string, `0x` and lowercase hex, a virtual address in the
binary's own space: a PE's image base is included and an ARM Thumb address
is even. A file offset never appears.

## Order and determinism

The file is the same bytes for the same binary and borer at any thread
count. A function `out.c` writes as a comment (cut over the block budget,
or not decompiled) has no record. A record lists at most 4096 instruction
starts, and all records together at most the input file's size in bytes
plus 4096.

## Reading it as DecBench does

DecBench scores types through its address correspondence when a producer
gives, per function, `line_mappings` (each snippet line's instruction
addresses) and `variables`. From one record:

- `line_mappings`: for each `lines` entry, line `line` with the `starts` of
  its `block`, parsed from hex;
- `variables`: `name`, `type` (DecBench's own parser reads an array as its
  element type), `arg_index` = `param`, `stack_offset` from `home.offset` for
  a `frame` home plus 16: DecBench states its ground truth as the
  `DW_OP_fbreg` operand plus 16, and a CFA-based compiler's frame base is
  the CFA; the scorer calibrates the rest, and
  `line_numbers` = `lines`.

Variables DecBench takes from inlined callees have no addresses in its own
source evidence, so no producer matches them there.
