# Recall against ground truth

`python scripts/run/recall.py --bench D:\Projects\bench --label NAME`, then
`--compare before,after`. borer reads every binary without its symbols; the
truth comes from the symbol tables, PDBs, llvm-objdump, llvm-readobj and the
C sources (see the script's docstring for each category).

Binaries: hard and suite (`D:\Projects\bench\src`) built O0/O2/Os for x64,
arm64 and x86 ELF, stripped; sqlite 3.54.1 built by clang-cl /O2 with a full
PDB (1804 functions, 72 switch tables); notepad.exe and kernelbase.dll with
their public PDBs.

Every cell not listed below is 100% in both runs. `before` is local main at
2aea0e7, `after` this branch.

| binary | category | before | after |
|---|---|---|---|
| hard_O2.x64 | functions | 98.8% (80/81) | 100.0% (81/81) |
| hard_Os.x64 | functions | 98.8% (80/81) | 100.0% (81/81) |
| hard_O0.x64 | fn:precision | 91.7% (88/96) | 100.0% (88/88) |
| suite_O0.x64 | fn:precision | 92.8% (64/69) | 100.0% (64/64) |
| suite_O0.x64 | extent | 98.4% (62/63) | 100.0% (63/63) |
| hard x64 (O0, O2, Os) | crypto | 33.3% (1/3) | 100.0% (3/3) |
| suite x64 (O0, O2, Os) | crypto | 0.0% (0/1) | 100.0% (1/1) |
| hard x86 (O0, O2) | crypto | 0.0% (0/3) | 33.3% (1/3) |
| hard, suite arm64 | crypto | 0.0% | 0.0% |
| sqlite3 | functions | 99.5% (1795/1804) | 99.6% (1797/1804) |
| sqlite3 | extent | 99.8% (1681/1684) | 99.9% (1685/1686) |
| sqlite3 | calls | 99.5% (10227/10283) | 100.0% (10283/10283) |
| sqlite3 | tails | 97.2% (308/317) | 99.4% (315/317) |
| sqlite3 | data | 99.5% (7958/7995) | 99.9% (7991/7995) |
| sqlite3 | imports | 98.8% (2425/2454) | 100.0% (2454/2454) |
| sqlite3 | switch | 96.7% (1051/1087) | 100.0% (1087/1087) |
| sqlite3 | xstring | 98.4% (492/500) | 99.2% (496/500) |
| notepad | calls | 95.4% (1585/1661) | 100.0% (1661/1661) |
| notepad | data | 96.7% (2226/2301) | 100.0% (2301/2301) |
| notepad | imports | 98.7% (1559/1579) | 100.0% (1579/1579) |
| notepad | strings | 99.2% (124/125) | 100.0% (125/125) |
| notepad | xstring | 98.3% (117/119) | 99.2% (118/119) |
| kernelbase | calls | 81.7% (9551/11689) | 88.2% (10314/11689) |
| kernelbase | tails | 98.2% (164/167) | 100.0% (167/167) |
| kernelbase | data | 89.9% (7843/8724) | 93.9% (8195/8724) |
| kernelbase | imports | 98.2% (8607/8763) | 99.8% (8746/8763) |
| kernelbase | xstring | 98.4% (492/500) | 98.8% (494/500) |

Precision held: no category's precision dropped. Function precision on the
O0 builds rose to 100% (a jump onto a short jump split `h_parse_int` in
three), and call-site precision is 100% everywhere but one kernelbase site.

What is left:

- kernelbase calls and data: every remaining site is in a function `xrefs`
  folds into a row as running the same code, past the eight names a row
  shows (`calls+folds` and `data+folds` are both 100%): a helper with
  948 callers lists each shape once.
- Crypto constants an arm64 build makes with `movz`/`movk` and an x86 build
  splits into two 32-bit immediates are not seen by the byte scan.
- sqlite: seven unreferenced CRT and castguard stubs, two tail jumps from
  them, and four data references from the same stubs.
- xstring: four sqlite, one notepad and six kernelbase literals are not
  traced to the function that references them; not investigated yet.
