# Limits

- 32-bit ARM and RISC-V are not emulated, so the emulator-backed analyses
  refuse them. On arm64, `taint`, `layout`, `solve`, `unpack` and `devirt`
  refuse to run.
- Shapes the structurer cannot prove stay as labels and gotos; SIMD code
  prints as intrinsics.
- No debugger: no breakpoints and no writes. Live access is Windows only.
- .NET IL and Swift are not decompiled, and DWARF supplies names and types,
  not line tables.
- Library signatures ship for LLVM compiler-rt, the Microsoft C++ standard
  library and the Rust standard library; build a pack for any other with
  `borer sigmake`.
