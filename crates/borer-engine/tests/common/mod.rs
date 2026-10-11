//! Shared test fixture: hand-assembled functions in `.text` (0x1000..0x2000)
//! and `.text2` (0x4000..0x6000, a second code section for the latest
//! shapes).
//!
//! `.rdata` (0x2000..0x3000) holds a jump table, pointers, strings and
//! vtables; `.data` (0x3000..0x3100, writable, zeroed) holds a class
//! descriptor object and a singleton global.

use borer_engine::num::saturating_usize;
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};

/// Builds the fixture program (x86-64, raw format, image base 0).
///
/// `.text` functions; entry 0x1000, the exported ones are seeded by symbol:
///
/// * `main` 0x1000: `call A; test ecx,ecx; jz 0x100e; call B; xor eax,eax; ret`.
/// * `A` 0x1020 and `B` 0x1030: return 1 and 2.
/// * `C` 0x1040: rip-relative load from 0x2007.
/// * `D` 0x1060: `switch (ecx)` over a 4-entry absolute-qword table at 0x2000;
///   cases at 0x1090..0x10c0 return 1..4, default 0x1080 returns 0.
/// * `E` 0x10e0: `ret`, referenced only by the qword pointer at 0x2030.
/// * `F` 0x1100: `while (ecx < 5) { eax += ecx; ecx += 1; }`, loop head 0x1107.
/// * `G` 0x1130: `eax = 7` survives a join where only `ecx` differs.
/// * `H` 0x1150: `if (ecx != 0) *(uint32_t*)rdx = ecx;` (if-body with a live store).
/// * `K` 0x1180: `while (rax < 5) { if (rbx != 0) break; rax++; } return rax;`.
/// * `P` 0x11c0: sets `rcx = 10`, `rdx = 20`, then calls `Q` 0x11e0 (a bare `ret`).
/// * `S` 0x1200: `lea rcx` to the string at 0x2040, then calls `Q`.
/// * `T` 0x1210: import thunk `jmp [0x2050]` (pointer-seeded from 0x2038).
/// * `U` 0x1220: `call T` (pointer-seeded from 0x2058).
/// * `V` 0x1230: `call [0x2050]` (pointer-seeded from 0x2060).
/// * `W` 0x1240: `mov ecx, 1; jmp A`, a tail call into a function that is
///   only known once `main` has been walked.
/// * `X` 0x1250: `mov rcx, E; mov rdx, string; call Q`, a function pointer
///   and a string literal passed as arguments.
/// * `Y` 0x1270: `mov ecx, 1; call [ExitProcess]` with `Z` 0x127b (`mov eax, 3;
///   ret`) starting right after the call: a noreturn import by name.
/// * `NR` 0x12b0: `jmp $`, a function that never returns and has no name.
/// * `Y3` 0x12c0: `mov ecx, 2; call NR` with `Z3` 0x12ca (`mov eax, 4; ret`)
///   right after the call: `NR` is discovered to be noreturn.
/// * `W3` 0x12d0: `mov ecx, 3; call NR; mov eax, 5; ret`: walked before `Y3`,
///   re-walked once `NR` is known, so the dead tail is dropped.
/// * `FL` 0x1300: `movss xmm0, [rcx]; addss xmm0, [rcx+4]; mulss xmm0, [rcx+8];
///   sqrtss xmm0, xmm0; cvttss2si eax, xmm0; ret`, scalar float arithmetic.
/// * `FL2` 0x1320: `xorps` with the sign mask at 0x2070 and `andps` with the
///   magnitude mask at 0x2080, stored to `[rdx]` and `[rdx+4]`.
/// * `FL3` 0x1340: `cvtsi2ss xmm0, ecx; mulss xmm0, xmm0; cvtss2sd xmm0, xmm0;
///   movsd [rdx], xmm0; shufps xmm1, xmm0, 0x1b; movaps [rdx+0x10], xmm1;
///   ret`, conversions and a vector op left as an intrinsic.
/// * `M` 0x1360: `xchg [rcx], rdx; bts qword [rcx+8], rdx; vmovaps xmm0,
///   [rcx+0x10]; vmovaps [rcx+0x20], xmm0; stmxcsr [rcx+0x30]; mov rax, rdx;
///   ret`, memory exchange, bit set, AVX moves and the MXCSR store.
/// * `D1` 0x1380: `mov rdi, rdx; test ecx, ecx; jz L; call Q; L: mov rax, rdi;
///   ret`: the copy is written once before the branch, not again before the call.
/// * `E1` 0x13c0: `test rcx, rcx; jne L; lea eax, [rcx+0x19]; ret; L: mov eax, 1;
///   ret`: on the fall-through edge `rcx` is zero, so the `lea` is `25`.
/// * `FR` 0x13f0: `call FRET; movss [rcx], xmm0; ret` with `FRET` 0x1400
///   (`xorps xmm0, xmm0; ret`): a float result bound to `xmm0`.
/// * `CS` 0x13d0: `mov [rsp+8], rbx; mov rbx, rcx; call Q; mov rax, rbx;
///   mov rbx, [rsp+8]; ret`: the callee-saved save and restore never render.
/// * `ES` 0x1410: `sub rsp, 0x28; and [rsp+0x20], 0; lea r9, [rsp+0x20];
///   call AR; mov rax, [rsp+0x20]; add rsp, 0x28; ret`: the local's address
///   escapes through `r9` although `AR` reads only `rcx`.
/// * `CC` 0x1430: `xor edx, edx; test ecx, ecx; jne R; test edx, edx; je R;
///   mov eax, 1; ret; R: xor eax, eax; ret`: the second test is constant.
/// * `FJ` 0x1450: `mov eax, ecx; test eax, eax; jne J; mov eax, edx;
///   test eax, eax; J: sete al; movzx eax, al; ret`: both edges into `J`
///   test `eax`, with different values in it.
/// * `FA` 0x1470: `mov eax, ecx; cmp eax, 5; mov edx, eax; jl J; mov edx, 3;
///   cmp edx, 5; J: setl al; movzx eax, al; ret`: one edge compares `eax`
///   while `edx` aliases it, the other compares `edx`.
/// * `E2` 0x14b0: `test eax, eax; jne L; mov eax, [rdx]; mov [rdx], 1;
///   lea eax, [rax+0x19]; ret; L: mov eax, 1; ret`: the store writes `rax`
///   out, after which the fall-through edge's `rax == 0` no longer holds.
/// * `FJ8` 0x1490: `FJ` on bytes (`mov al, cl; test al, al; jne J; mov al, dl;
///   test al, al; J: sete al; movzx eax, al; ret`): the byte writes merge into
///   `rax`, so the operand is `rax & 0xff` on both edges once `rax` is written.
/// * `FM` 0x14d0: `test ecx, ecx; jne C; B: cmp [rdx], 5; jmp J; C: cmp
///   [rdx+4], 5; J: setl al; movzx eax, al; ret`: the edges compare memory at
///   different addresses.
/// * `FS` 0x14f0: `cmp eax, 5; mov eax, edx; jl B; C: ret; B: setl al;
///   movzx eax, al; jmp C`: the join at `C` makes the first block write
///   `rax` out at its end, so the flags over the old `rax` cannot cross
///   into `B` as they are.
/// * `AC2` 0x1510: `test ecx, ecx; jne B; add rax, rdx; jmp J; B: add rax,
///   rcx; J: adc rax, rdx; ret`: the carry reaching `J` comes from a
///   different addition on each edge.
/// * `ADC3` 0x1520: `bt ecx, 0; adc [rdx], eax; adc [rdx+4], r8d; setb cl;
///   ret`: a multiword add whose carry chains through two `adc`.
/// * `DC` 0x1530: `sub ecx, 1; cmp ecx, 1; jne L; mov eax, 2; ret; L: xor eax,
///   eax; ret`: a `dec`-chain comparison, `a1 - 1 == 1`.
/// * `LD` 0x1550: a compare ladder split in two halves (`cmp ecx, 5; jg U;
///   cmp ecx, 1; jne; mov edx, 10; jmp T; cmp ecx, 2; jne D; mov edx, 20;
///   jmp T; U: cmp ecx, 6; jne D; mov edx, 60; jmp T; D: mov edx, 0; T: mov
///   eax, edx; call Q; ret`) whose default arm `D` both halves share; the
///   call keeps the tail from being copied into the arms.
/// * `LD2` 0x1590: `test ecx, ecx; jz D; mov [rdx], 1; cmp ecx, 6; je X;
///   D: mov edx, 0; jmp T; X: mov edx, 60; T: mov eax, edx; ret`: the shared
///   block `D` is both a branch target and a fall-through, and jumps over
///   `X`; the store keeps the two conditions from merging into one guard.
/// * `LX` 0x15b0: `test ecx, ecx; jz A; or rax, -1; H: inc rax; cmp [rcx+rax],
///   0x20; jne H; jmp J; A: xor eax, eax; J: call Q; ret`: a scan for a space
///   leaving through a `jmp` to the block `J` the other arm falls into; `J`
///   ends in a call, so it leads one way.
/// * `NM` 0x15d0: `lea rdx, [Foo::Bar sig]; call Q; ret` and `NM2` 0x15e0:
///   `lea rdx, [Foo::Baz sig]; lea r8, [Foo::Bar sig]; call NM; ret`
///   (pointer-seeded from 0x2090): `NM2` is named `Foo::Baz` by its unique
///   string, after which `Foo::Bar` has one unnamed referrer left, `NM`.
/// * `VD2` 0x1600: `mov eax, [rcx]; call AR; mov [rcx+4], 1; ret`, whose only
///   caller `VC` 0x1610 (`call VD2; mov eax, 0; ret`) overwrites `rax` right
///   after the call: the stale `rax` at `ret` is not a return value. `VT`
///   0x1620 (`call VD2; ret`) hands `VD2`'s result on, and its own caller
///   `VC2` 0x1630 (`call VT; mov eax, 0; ret`) discards it.
/// * `CL1` 0x1640: `mov [rcx+8], edx; mov rax, [rcx]; mov [rcx+0x10], rax;
///   lea rdx, [Cls::Set sig]; lea rcx, [rcx+0x20]; call CL3; ret`
///   (pointer-seeded from 0x2098): a method of `Cls` reading field 0, writing
///   fields 8 and 0x10 and passing the embedded object at 0x20 to `Other::Get`.
/// * `CL3` 0x1670: `mov eax, [rcx+4]; lea rdx, [Other::Get sig]; ret`
///   (pointer-seeded from 0x2170), the `const` method `int Other::Get(void)`.
/// * `HR` 0x1680: `mov [rcx], edx; mov rax, rcx; lea rdx, [Name::Of sig]; ret`
///   (pointer-seeded from 0x21b0), `class Util::String Name::Of(int)`: the
///   class returned by value arrives through a hidden pointer in `rcx`.
/// * `PW` 0x1690: `mov eax, 0x100; test ecx, ecx; jz B2; B1: mov al, [rcx];
///   jmp J; B2: mov al, [rcx+1]; J: mov [rdx], eax; ret` (pointer-seeded from
///   0x21b8): the byte writes keep the upper bits of a value the join reads.
/// * `PC` 0x16b0: `mov al, [rcx]; mov [rdx], al; mov al, [rcx+1];
///   mov [rdx+1], al; mov eax, 0; ret` (pointer-seeded from 0x21c0): a byte
///   chain whose upper bits nothing reads.
/// * `RL` 0x16c0: `test ecx, ecx; jz L; mov al, 1; jmp R; L: mov al, 0;
///   R: ret` (pointer-seeded from 0x21c8): the shared `ret` block writes no
///   register itself, but every path into it ends with a byte write of
///   `rax`, so the function returns that lane.
/// * `BC` 0x16d0: `lea rax, [0x2280]; mov [rcx], rax; lea rdx, [Base::Base
///   sig]; ret`, the constructor of `Base` storing its vtable (slots 0x1200,
///   0x11e0, then a zero word).
/// * `CC` 0x16f0: `mov rbx, rcx; call BC; lea rax, [0x22a0]; mov [rbx], rax;
///   lea rdx, [Der::Der sig]; ret`, the constructor of `Der`: base
///   constructor first, then its own vtable (slots `DV` 0x1870, 0x1200).
/// * `CD` 0x1710: `lea rax, [0x22a0]; mov [rcx], rax; lea rdx, [Der::~Der
///   sig]; ret`, the destructor of `Der`.
/// * `UC` 0x1730: `lea rax, [0x22a0]; mov [rcx], rax; ret`, an unnamed
///   function storing `Der`'s vtable, which names it `Der::ctor_or_dtor`.
///   All four are pointer-seeded from 0x2200..0x2220.
/// * `DF` 0x1740: `mov eax, [rcx+8]; lea rdx, [Der2::Foo sig]; ret`, a method
///   of `Der2`, which has no named constructor.
/// * `UC2` 0x1750: `mov rbx, rcx; call CC; lea rax, [0x22c0]; mov [rbx], rax;
///   ret`: stores the table 0x22c0 (slots `DF`, 0x1200), which its unique
///   slot `Der2::Foo` names `Der2`'s vtable, so the function becomes
///   `Der2::ctor_or_dtor` with parent `Der`. Both pointer-seeded from 0x2300.
/// * `VR` 0x1770: `mov rax, [rcx]; call [rax+8]; lea rdx, [Der::Run sig];
///   ret` (pointer-seeded from 0x2330): a method of `Der` calling slot 1 of
///   `this`'s vtable, which resolves to 0x1200.
/// * `FG` 0x17a0: `lea rax, [0x2380]; lea rdx, [Fac::Get sig]; ret`, declared
///   `class Der *__cdecl Fac::Get(void)`.
/// * `VR2` 0x1780: `call FG; mov rcx, rax; mov rax, [rcx]; call [rax+8]; ret`:
///   the call result is a `Der *`, so the virtual call resolves through
///   `Der`'s table. Both pointer-seeded from 0x2368.
/// * `PU` 0x17b0: `mov rax, [rdx]; mov [rcx+0x10], rax; mov rcx, rax; mov rax,
///   [rax]; call [rax+8]; lea rdx, [Der::Use sig]; ret` (pointer-seeded from
///   0x2378), declared
///   `void Der::Use(const Core::Ptr<Der> &)`: the word the smart pointer
///   holds is a `Der`, so the call resolves and reads `a2->...`.
/// * `UR` 0x17d0: `call P; mov edx, 5; mov rcx, rax; call Q; ret`
///   (pointer-seeded from 0x2388): the result of `P` is read two
///   instructions later.
/// * `PK` 0x17f0: `mov eax, edx; lea rdx, [Pk::Pick sig]; ret` (pointer-seeded
///   from 0x23f0), declared `int Pk::Pick(int)`: the method never reads
///   `this`, but its one parameter arrives in the second argument register.
/// * `RC` 0x1800: `call NM; ret` (pointer-seeded from 0x23f8): `Foo::Bar`
///   declares an `int`, so its result is the function's result.
/// * `AS` 0x1810: `lea rcx, ["f.IsValid()"]; lea rdx, [path]; mov r8d, 191;
///   lea r9, [As::Chk sig]; call [ReportAssertFailure]; ret` (pointer-seeded from
///   0x2460): an assert call whose path and own signature literals render
///   compactly.
/// * `AG` 0x1840: `test ecx, ecx; jnz R; lea rcx, ["f.IsValid()"]; lea rdx,
///   [path]; mov r8d, 191; lea r9, [Ag::Run sig]; call [ReportAssertFailure]; R:
///   ret` (pointer-seeded from 0x2490): a guarded assert, which the skeleton
///   folds to `assert(f.IsValid());`.
/// * `DV` 0x1870: `mov eax, 7; ret` (pointer-seeded from 0x2498), slot 0 of
///   `Der`'s table; `Der2::Foo` overrides that slot, so it becomes
///   `Der::Foo`.
/// * `SC` 0x1880: `mov eax, ecx; shr eax, 5; adc eax, 0; ret` (pointer-seeded
///   from 0x24a0): the shift's carry (bit 4 of `a1`) feeds the `adc`.
/// * `RR` 0x1890: `mov eax, r8d; cmp ecx, edx; rcr eax, 1; cmovae eax, edx;
///   ret` (pointer-seeded from 0x24a8): the compare's carry rotates in, and
///   the `cmovae` reads the bit rotated out.
/// * `SD` 0x18a0: `mov eax, ecx; shld eax, edx, 8; ret` (pointer-seeded from
///   0x24b0), a double-precision shift by a constant.
/// * `XG` 0x18b0: `xgetbv; ret` (pointer-seeded from 0x24b8), an intrinsic
///   whose result the function returns.
/// * `HC` 0x18c0: `mov eax, [rcx]; call HT; lea rdx, [Der::Tick sig]; ret`
///   (pointer-seeded from 0x24e0): the method `Der::Tick` passes its `this`
///   to `HT`.
/// * `HT` 0x18d0: `mov eax, [rcx+8]; ret` (pointer-seeded from 0x24e8): an
///   undeclared function whose first parameter is hinted `Der *`.
/// * `GT` 0x18e0: `mov rax, [rcx+0x10]; ret` (pointer-seeded from 0x2520), an
///   undeclared getter whose result `Der::Poll` passes to `Base::Base`.
/// * `HC2` 0x18f0: `mov rbx, rcx; call GT; mov rcx, rax; call BC; mov rcx,
///   [rbx+0x10]; call BC; mov rax, [rbx+0x10]; mov rcx, rax; mov rax, [rax];
///   call [rax+8]; lea rdx, [Der::Poll sig]; ret` (pointer-seeded from
///   0x2528): `Der::Poll` types `GT`'s result and `Der`'s field at 0x10 as
///   `Base`, so its virtual call through the field resolves.
/// * `HC3` 0x1920: `mov rbx, rcx; lea rdx, [rbx+0x28]; call PU; mov rax,
///   [rbx+0x28]; mov rcx, rax; mov rax, [rax]; call [rax+8]; lea rdx,
///   [Der::Wait sig]; ret` (pointer-seeded from 0x2560): `Der::Wait` passes
///   the address of its field at 0x28 for `Der::Use`'s `const Core::Ptr<Der>
///   &`, so the field is an embedded `Core::Ptr<Der>` and the virtual call
///   through the pointer it holds resolves to `Der`'s slot 1.
/// * `ACC` 0x1950: `mov rax, [rcx]; ret` (pointer-seeded from 0x2590), an
///   undeclared accessor like `Core::Ptr<T>::operator->`.
/// * `HC4` 0x1960: `mov rbx, rcx; lea rcx, [rbx+0x28]; call ACC; mov rcx,
///   rax; mov rax, [rax]; call [rax+8]; lea rdx, [Der::Peek sig]; ret`
///   (pointer-seeded from 0x2598): the accessor is called on the embedded
///   `Core::Ptr<Der>`, so its result is a `Der` and the call resolves.
/// * `AM1` 0x1980: `mov eax, [rcx+4]; lea rdx, [Acc::Get sig]; ret` and
///   `AM2` 0x1990: `mov eax, [rcx+4]; add eax, edx; lea rdx, [Acc::Get sig];
///   ret` (pointer-seeded from 0x25c8): both reference `int Acc::Get(void)
///   const`, neither has a signature of its own; `AM1` reads only `this`, so
///   it is the accessor and `AM2` the function that inlined it.
/// * `DC2` 0x19a0: `mov eax, [rcx+8]; test eax, eax; jnz R; lea rcx,
///   ["this->count"]; lea rdx, [path]; mov r8d, 7; lea r9, [Der::Chk sig];
///   call [ReportAssertFailure]; R: ret` (pointer-seeded from 0x2620): the guarded
///   assert names `Der`'s field at 8 `count`.
/// * `DP` 0x19d0: `mov eax, [rdx+8]; mov [rcx+8], eax; lea rdx, [Der::Cmp
///   sig]; ret` (pointer-seeded from 0x2658), declared `void Der::Cmp(Der
///   *)`: copies the named field from a class-typed parameter.
/// * `FM2` 0x19e0: `mov dword [rcx], 0; mov rax, rcx; lea rdx, [Fac::Make
///   sig]; ret`, declared `class Core::Ptr<class Der> __cdecl
///   Fac::Make(void)`: returns a smart pointer by value.
/// * `LP` 0x1a00: `sub rsp, 0x28; lea rcx, [rsp+0x20]; call FM2; mov rcx,
///   [rsp+0x20]; mov rax, [rcx]; call [rax+8]; lea rdx, [Der::Local sig];
///   add rsp, 0x28; ret` (both pointer-seeded from 0x26c0): the local that
///   receives the `Core::Ptr<Der>` holds a `Der`, so the call through it
///   resolves to `Der`'s slot 1.
/// * `HC5` 0x1a50 (`Der::Tick2`): `mov eax, [rcx]; call HU; lea rdx, [sig];
///   ret`, `HU` 0x1a30: `mov eax, [rcx+0x10]; call HU2; ret`, `HU2` 0x1a40:
///   `mov eax, [rcx+0xc]; ret` (pointer-seeded from 0x2700): `this` travels
///   two calls, so `HU2` is hinted `Der` in the second round.
/// * `TC` 0x1a60 (`Tls::Tls`): `mov rbx, rcx; mov rax, gs:[0x58]; mov ecx,
///   [_tls_index]; mov rax, [rax+rcx*8]; mov ebp, 0x10; mov [rax+rbp], rbx;
///   lea rdx, [sig]; ret`, a constructor registering its singleton at TLS
///   offset 0x10 through an index register holding the offset.
/// * `TU` 0x1a90: the same TLS walk, `mov rcx, [rax+0x10]; mov rax, [rcx];
///   call [rax+8]; ret`: a call through the singleton. Both pointer-seeded
///   from 0x2760; `_tls_index` is the word at 0x2720.
/// * `TG` 0x1ab0: the TLS walk then `mov rax, [rax+0x10]; ret`, an unnamed
///   getter returning the singleton, called by `TU2` 0x1ad0 (`Tls::Use`:
///   `mov eax, [rcx]; call TG; lea rdx, [sig]; ret`); both pointer-seeded
///   from 0x27a0.
/// * `GC` 0x1ae0 (`Glob::Glob`): `lea rax, [0x27b0]; mov [rcx], rax; mov
///   [0x27c0], rcx; lea rdx, [sig]; ret`, a constructor storing its vtable
///   (slots 0x1200, 0x13a0) and registering `this` in the global at 0x27c0.
/// * `GU` 0x1b00: `mov rcx, [0x27c0]; mov rax, [rcx]; call [rax+8]; ret`, a
///   call through the global singleton. Both pointer-seeded from 0x27e8.
/// * `UT` 0x1b10: `lea rax, [0x2800]; mov [rcx], rax; ret` (pointer-seeded
///   from 0x2818): stores a table nothing names (slots `S1` 0x1b20 and `S2`
///   0x1b30, `mov eax, N; ret`), which becomes the class `class_2800`.
/// * `AH` 0x1b50: `lea rcx, ["n == 1"]; lea rdx, ["n must be one"]; lea r8,
///   ["src/ah.cc"]; mov r9d, 0x1c2; call AK; xor eax, eax; ret`
///   (pointer-seeded from 0x2850): an assert helper `AK` 0x1b40 (`ret`)
///   called outright with expression, message, path and line.
/// * `VU` 0x1b80: `mov rax, [rcx]; call [rax+0x10]; ret` (pointer-seeded
///   from 0x2858): a virtual call through slot 2 of a receiver whose class
///   nothing declares.
/// * `PA` 0x1b90: `mov rax, [rcx]; lea rdx, [sig]; ret` (pointer-seeded from
///   0x28a8), declared `class Der *__cdecl Core::Ptr<class Der>::operator
///   ->(void) const`: the arrow operator of a smart pointer, whose `->`
///   is no template bracket. `PB` 0x1ba0: `call PA; mov rcx, rax; mov rax,
///   [rax]; call [rax+8]; ret` (pointer-seeded from 0x28b0) calls slot 1
///   through `PA`'s declared `Der *` result.
/// * `DK` 0x1bb0: `lea rax, [0x28c0]; mov [rcx], rax; ret`, a constructor
///   storing a table nothing names (slots `S3` 0x1be0 and `S4` 0x1bf0, `mov
///   eax, N; ret`). `DC` 0x1bc0: `lea rax, [0x3000]; call DK; ret`
///   (pointer-seeded from 0x28f0), a creator referencing the descriptor
///   object at 0x3000. `DR` 0x1bd0: `lea rcx, [0x3000]; lea rdx,
///   ["Ns::Thing"]; ret` (pointer-seeded from 0x28f8), a registration
///   spelling the class name beside the object, which names the table
///   `Ns::Thing`. `DR2` 0x1e40: `lea rcx, [0x3040]; lea rdx, ["Ns::T2"];
///   ret`, the registration naming the object at 0x3040 `Ns::T2`; `DI`
///   0x1eb0: `lea rcx, [0x3040]; lea rdx, ["Ns::T2"]; lea rax, [0x3000];
///   call DR2; ret` (pointer-seeded from 0x29f8), the initializer spelling
///   the name beside its own object and `Ns::Thing`'s, which makes
///   `Ns::Thing` the parent of `Ns::T2`. `DI3` 0x1290: `lea rcx, [0x3080];
///   lea rdx, ["Ns::T3"]; lea rax, [0x3000]; call Q; ret` (pointer-seeded
///   from 0x2a50), the initializer of a class no registration spells: the
///   object at 0x3080 is named `Ns::T3` by the literal beside the named
///   `Ns::Thing` descriptor, which is its parent. `TT2` 0x1160: `lea rax,
///   [0x2a00]; mov [rcx], rax; lea rax, [0x2a60]; mov [rcx], rax; ret`, a
///   constructor storing the two-slot table before its own three-slot table
///   at 0x2a60; `CR` 0x1ed0: `lea rax, [0x30c0]; call TT2; ret`
///   (pointer-seeded from 0x2a98), its creator, allocating from the object
///   `DR4` 0x12e0 (`lea rcx, [0x30c0]; lea rdx, ["Ns::T4"]; ret`,
///   pointer-seeded from 0x2a88) registers as `Ns::T4`, whose initializer
///   `DI4` 0x11a0 (`lea rcx, [0x30c0]; lea rdx, ["Ns::T4"]; lea rax,
///   [0x3040]; call Q; ret`, pointer-seeded from 0x2a90) names `Ns::T2`, a
///   class without a table of its own, as the parent. `DC3` 0x1050: `lea
///   rax, [0x3040]; call DK; ret` (pointer-seeded from 0x2aa0), a creator
///   allocating from `Ns::T2`'s descriptor that calls `Ns::Thing`'s
///   constructor `DK`, as a derived class's creator does once its own
///   constructor is inlined. `TT3` 0x10e1: `lea rax, [0x2a00]; mov [rcx],
///   rax; lea rax, [0x2a20]; mov [rcx], rax; lea rax, [0x2ab0]; mov [rcx],
///   rax; ret` (pointer-seeded from 0x2af0), a constructor with two levels
///   of base constructors inlined, storing the two-, three- and four-slot
///   tables in turn. `CI` 0x11e4: `call Q; lea rcx, [0x2ad8]; mov [rax],
///   rcx; lea rdx, [0x3080]; ret` (pointer-seeded from 0x2af8), a creator
///   constructing in place: it stores the two-slot table at 0x2ad8 through
///   the allocation the call returned and references `Ns::T3`'s descriptor.
/// * `TP` 0x1118: `lea rdx, [Der::Pass sig]; lea rcx, [rcx+0x28]; call UP;
///   ret` (pointer-seeded from 0x2b00), `Der::Pass` passing the address of
///   its `Core::Ptr<Der>` field at 0x28 to `UP` 0x12f0: `mov rax, [rcx];
///   mov rcx, rax; mov rax, [rcx]; call [rax+8]; ret` (pointer-seeded from
///   0x2b08), which calls slot 1 of the object the pointer holds.
/// * `GJ` 0x4000 (in `.text2`): `test ecx, ecx; jz A; mov eax, 1; jmp L;
///   A: test edx, edx; jz B; call Q; test al, al; je B; mov eax, 1; jmp L;
///   B: xor eax, eax; L: mov eax, 5; add eax, 1 (eight times); ret`
///   (pointer-seeded from 0x2b30): inside the taken arm, a branch on the
///   call's result whose two assignments `L` kills, so both its arms are
///   empty, one jumping to the join and one falling into it; the other
///   outer path, dead too, jumps to the join, which is too long to be
///   copied anywhere.
/// * `CK` 0x4041: `cmp rcx, [0x3008]; jne F; ret; F: jmp Q`, a
///   stack-cookie check: nothing on the way to its `ret` writes `rax`.
///   `CC` 0x4050: `mov eax, 7; mov rcx, [0x3008]; call CK; ret`
///   (pointer-seeded from 0x2b38) sets its result before the check.
/// * `LD3` 0x4090: `cmp ecx, 9; je S; cmp ecx, 1; jne A2; mov edx, 1; jmp
///   T; A2: cmp ecx, 2; jne A3; mov edx, 2; jmp T; A3: cmp ecx, 3; jne S;
///   mov edx, 3; T: call Q; add eax, 1 (eight times); ret; S: mov eax, 5;
///   add eax, 1 (eight times); ret` (pointer-seeded from 0x2b40): a
///   compare ladder whose arms set a value and jump to a shared tail, the
///   last test skipping to a block an outer guard reaches too; both tails
///   are too long to be copied.
/// * `IG` 0x40f4: `call CL2; xor eax, eax; ret` (pointer-seeded from
///   0x2b48): the one caller of `Cls::Has` overwrites its result at once.
/// * `BR` 0x4100: `push rbx; mov ebx, ecx; lea rdx, [Ns::Flag sig]; xor ecx,
///   ecx; call Q; mov al, bl; pop rbx; ret`, `bool Ns::Flag(void)` keeping its result
///   in `rbx` across a call and handing it back as a byte; `IG2` 0x4120:
///   `call BR; xor eax, eax; ret` (pointer-seeded from 0x2b70), its one
///   caller, overwrites the result at once. `BR2` 0x4130: `push rbx; mov
///   ebx, ecx; test ecx, ecx; jz X; mov ebx, 1; X: lea rdx, [Ns::Flag2
///   sig]; xor ecx, ecx; call Q; mov al, bl; pop rbx; ret`, `bool Ns::Flag2(void)`
///   handing back as a byte a value two paths set, after a call; `IG3`
///   0x4150: `call BR2; xor eax, eax; ret` (pointer-seeded from 0x2b78),
///   its one caller, overwrites the result at once.
/// * `SS` 0x4160: `lea rdx, ["%d"]; xor ecx, ecx; call Q; ret`
///   (pointer-seeded from 0x2ba8): passes a two-character literal from
///   read-only data.
/// * `WL` 0x4170: `lea rdx, [L"AES"]; xor ecx, ecx; call Q; ret`
///   (pointer-seeded from 0x2c90): passes a UTF-16LE literal from read-only
///   data, whose first byte pair also reads as a one-character narrow string.
/// * `GC` 0x4180: `test ecx, ecx; jz J; call Q; test eax, eax; jz F; J: mov
///   [rdx+k], ecx (nine times); F: mov eax, 5; add eax, 1 (eight times);
///   ret` (pointer-seeded from 0x2bb0): the guarded arm leaves both to the
///   join `J` and to `F`, which the join falls into, and both are too long
///   to copy, so neither side structures and the guard stays a conditional
///   jump over the arm's two lines.
/// * `SH` 0x41d0: `mov rax, rcx; shld rax, rdx, cl; ret` and `SH2` 0x41e0
///   with `shrd` (pointer-seeded from 0x2bb8 and 0x2bc0): the double-width
///   shifts, whose count comes from `cl`.
/// * `ML8` 0x4200: `mov al, cl; mul dl; movzx eax, ax; ret` and `DV8`
///   0x4210: `mov ax, cx; div dl; movzx eax, ah; ret` (pointer-seeded from
///   0x2bc8 and 0x2bd0): the byte multiply and divide, which keep both
///   halves of their result in `ax`.
/// * `CL_A` 0x4220 and `CL_B` 0x4240: `mov rax, [G]; test rax, rax; jz E;
///   call Q; E: xor eax, eax; ret` over two different globals, so they are
///   clones of one another; `CL_C` 0x4260 is the same over a third global
///   but ends `mov al, 1`, so it is not (pointer-seeded from 0x2bd8,
///   0x2be0 and 0x2be8).
/// * `DEEP` 0x4300: seventy-two nested levels of `cmp byte [rcx+k], 0; je
///   deeper; mov eax, k; jmp common`, then `mov eax, 0xff; common: ret`
///   (pointer-seeded from 0x2bf0): a compare ladder nesting past the old
///   structuring depth limit, in the shape of the client's key-name
///   parser.
/// * `LK` 0x4790: `lock dec dword [rcx+8]; jne Z; mov eax, 1; ret; Z: xor
///   eax, eax; ret` (pointer-seeded from 0x2bf8): a reference-count drop
///   whose branch reads the atomic's result.
/// * `LKO` 0x5900: `lock or dword [rcx+0x10], 0x40; mov eax, 1; ret`
///   (pointer-seeded from 0x39e0): a `lock or` nothing branches after, so
///   the atomic renders as a statement the way every locked read-modify-
///   write but `LK` does.
/// * `XA` 0x5910: `mov [rsp+0x18], edx; mov eax, 0x10; xadd [rsp+0x18],
///   eax; jz Z; mov eax, 2; ret; Z: xor eax, eax; ret` (pointer-seeded
///   from 0x39e8): an exchange-and-add whose zero flag the branch reads as
///   the sum of the value stored and the addend.
/// * `CX` 0x5930: `mov eax, 5; cmpxchg [rcx], edx; jz S; mov eax, 2; ret;
///   S: xor eax, eax; ret` (pointer-seeded from 0x39f0): a compare-and-
///   exchange whose zero flag the branch reads as the old value having
///   matched the accumulator.
/// * `LP` 0x47a0: `xor byte [rcx+0x34], 1; mov rcx, [rcx]; test rcx, rcx;
///   jne LP; ret` (pointer-seeded from 0x2c00): a linked-list walk whose
///   loop head is the function's entry block.
/// * `EN` 0x47b0: four levels of `mov rcx, [rsp+8]; lea rdx, ["Back"];
///   call Q; test eax, eax; jz next; mov eax, k; ret`, then `xor eax, eax;
///   ret` (pointer-seeded from 0x2c08; literals at 0x2c10..0x2c2f): a
///   string-to-constant parser.
/// * `EN2` 0x4830: four levels of `cmp ecx, k; jne next; lea rax,
///   ["Normal"]; ret`, then `xor eax, eax; ret` (pointer-seeded from
///   0x2c50; literals at 0x2c30..0x2c4f): a constant-to-string table.
/// * `ET` 0x4870: `test ecx, ecx; jz E; call Q; test eax, eax; jz E; mov
///   [rdx+k], ecx (nine times); mov eax, 5; add eax, 1 (eight times); ret;
///   E: call Q; mov eax, 7; ret` (pointer-seeded from 0x2c58): two guards
///   sharing an error tail that holds a call; the structurer nests the
///   second guard's else side, so it needs no jump.
/// * `ET2` 0x48d0: `L: cmp dword [rcx], 0; je X; call Q; test eax, eax; jz
///   E; add rcx, 8; jmp L; X: xor eax, eax; ret; E: call Q; mov eax, 7;
///   ret` (pointer-seeded from 0x2c60): a loop escaping to a returning tail
///   that holds a call; the loop emitter absorbs a tail one escape reaches.
/// * `ET3` 0x4900: the same loop with two escapes to the tail (pointer-
///   seeded from 0x2c68): the loop emitter copies the tail into both
///   escapes, as it does for one.
/// * `FC` 0x4930: `GC` with a nested test inside the guarded arm (`test
///   ecx, ecx; jz J; call Q; test eax, eax; jz S; mov [rdx], ecx; S: mov
///   [rdx+4], ecx; call Q; test eax, eax; jz F; J: nine stores; F: mov eax,
///   5; eight adds; ret`, pointer-seeded from 0x2c70): the run the guard
///   jumps over holds an `if` block, so only a fold that allows nested
///   blocks wraps it.
/// * `SP1` 0x4990: `mov eax, 5; add eax, 0x11; ret` and `SP2` 0x49a0: `mov
///   eax, 9; add eax, 0x22; ret` (pointer-seeded from 0x2c78 and 0x2c80):
///   one instruction shape over different constants, so they share a
///   shape class but not a clone class.
/// * `FG` 0x49b0: `test ecx, ecx; jz END; A; call Q; test eax, eax; jz D;
///   B; call Q; test eax, eax; jne MID; C; D: store; MID: store; END: nine
///   stores; mov eax, 5; eight adds; ret` (pointer-seeded from 0x2c88):
///   the guarded run holds a jump out of a nested `if` to `MID`, a label
///   inside the run that nothing outside targets; the structurer itself
///   inverts this guard, so it pins that no jump is left.
/// * `CE1` 0x4a20: `call EN; cmp eax, 3; jne Z; mov eax, 1; ret; Z: xor eax,
///   eax; ret` and `CE2` 0x4a40: `mov ecx, 2; call EN2; ret` (pointer-seeded
///   from 0x2c98 and 0x2ca0): a caller comparing a parser's result and a
///   caller passing a constant to a constant-to-string table.
/// * `EN3` 0x4a50: three levels of `cmp ecx, k; jne next; lea rdx, [lit];
///   jmp END`, then `cmp ecx, 4; jne D; lea rdx, ["Down"]; jmp END; D: lea
///   rdx, ["Normal"]; END: call Q; ret` (pointer-seeded from 0x2ca8): a
///   `ToString` whose arms share one call, its last level testing `!= 4`
///   with the default in the taken arm and `"Down"` in the `else`.
/// * `DV5` 0x4aa0: `mov rax, 0x6666666666666667; imul rcx; sar rdx, 1; mov
///   rax, rdx; shr rax, 63; add rax, rdx; ret` and `DV10` 0x4ac0: `mov rax,
///   0xcccccccccccccccd; mul rcx; shr rdx, 3; mov rax, rdx; ret`
///   (pointer-seeded from 0x2cb0 and 0x2cb8): the compiler's forms of a
///   signed `a1 / 5` and an unsigned `a1 / 10`.
/// * `DM10` 0x4ae0: `DV10`'s quotient times ten (`lea rax, [rdx+rdx*4]; add
///   rax, rax`) subtracted from the dividend (pointer-seeded from 0x2cc0):
///   the compiler's form of an unsigned `a1 % 10`.
/// * `OR` 0x4b30: `or rax, -1; ret` (pointer-seeded from 0x2cc8): a
///   register seeded with all ones the compiler's way.
/// * `SE` 0x4b20: `xor eax, eax; test rcx, rcx; setg al; neg rax; and eax,
///   0x22; ret` (pointer-seeded from 0x2cd0): a branchless select of
///   `0x22` or `0` on `0 < a1`.
/// * `IX` 0x4b10: `mov eax, [rcx + rdx * 4]; ret` (pointer-seeded from
///   0x2cd8): element `a2` of a 32-bit array at `a1`.
/// * `SL` 0x4b00: `or rax, -1; L: inc rax; cmp byte [rcx + rax], 0; jne L;
///   ret` (pointer-seeded from 0x2ce0): the inline `strlen` of `a1`.
/// * `QS` 0x4b40: `mov rax, 0x4ec4ec4ec4ec4ec5; imul rcx; sar rdx, 6; mov
///   rax, rdx; shr rax, 63; ret` (pointer-seeded from 0x2ce8): the sign
///   bit of the magic quotient of `a1 / 208`, on its own.
/// * `SA` 0x4b60: `mov eax, 16; mul rcx; mov rcx, -1; cmovb rax, rcx; add
///   rax, 8; mov rcx, -1; cmovb rax, rcx; ret` (pointer-seeded from
///   0x2cf0): an allocation-size guard, `16 * a1 + 8` saturating at each
///   step.
/// * `TI` 0x4b90: `xor eax, eax; lea r8, [rdx + 1]; cmp rdx, 3; cmovne
///   rax, r8; mov eax, [rcx + rax * 4]; ret` (pointer-seeded from 0x2cf8):
///   a ring index selecting the element to read.
/// * `AM` 0x4bb0: `and rcx, -16; mov rax, rcx; ret` (pointer-seeded from
///   0x2d00): `a1` aligned down to sixteen.
/// * `DV7` 0x4bc0: `mov rax, 0x2492492492492493; mul rcx; sub rcx, rdx; shr
///   rcx, 1; add rcx, rdx; shr rcx, 2; mov rax, rcx; ret` (pointer-seeded
///   from 0x2d08): the overflow form of an unsigned `a1 / 7`.
/// * `SX` 0x4be0: `movsxd rax, dword [rcx]; ret` (pointer-seeded from
///   0x2d10): a sign-extended 32-bit load.
/// * `SX2` 0x4bf0: `movsxd rax, dword [rcx + rdx * 4]; ret` (pointer-seeded
///   from 0x2d18): a sign-extended 32-bit array element.
/// * `SC` 0x4c00: `movsxd rax, ecx; cmp rax, rdx; setg al; movzx eax, al;
///   add rax, rcx; ret` (pointer-seeded from 0x2d20): a signed compare of a
///   sign-extended operand that is also used whole, so it stays untyped.
/// * `LY` 0x4c10: `mov eax, [rcx + 0x18]; add eax, [rcx + 0x1c]; mov [rcx +
///   0x20], eax; ret` (pointer-seeded from 0x2d28): three dword fields of
///   the object `a1` points to.
/// * `UT` 0x55c0: `mov rax, [0x3400]; mov ecx, [rax + 0x18]; add ecx,
///   [rax + 0x1c]; mov [rax + 0x20], ecx; mov eax, [rax + 0x18]; ret`
///   (pointer-seeded from 0x3410): fields read through a global pointer,
///   for a user-applied struct to name.
/// * `EN` 0x55e0: `mov eax, [0x3420]; cmp eax, 1; je A; cmp eax, 2; je B;
///   xor eax, eax; ret; A: mov eax, 10; ret; B: mov eax, 20; ret`
///   (pointer-seeded from 0x3418, the dword global at 0x3420): a function
///   comparing a global against constants, for a user-applied enum to name.
/// * `EF` 0x56c0: `mov rax, [0x3490]; mov ecx, [rax + 8]; cmp ecx, 1; je
///   A; cmp ecx, 2; je B; xor eax, eax; ret; A: mov eax, 10; ret; B: mov
///   eax, 20; ret` (pointer-seeded from 0x3438, the object pointer at
///   0x3430): compares a field read through a global pointer, for a
///   user-applied struct with an enum-typed field to name.
/// * `T2::T2` 0x5760: `Tls::Tls` with a table, storing its vtable (slots
///   `T2S0` 0x57c0 and `T2S1` 0x57c6, `mov eax, N; ret`) at `[this]` before
///   registering its singleton at TLS offset 0x18 through an index register;
///   `TW` 0x57a0: `TU`'s walk over offset 0x18, `mov rcx, [rax+0x18]; mov
///   rax, [rcx]; call [rax+8]; ret`, a call through the singleton. Both
///   pointer-seeded from 0x3560 and 0x3568; the table and the signature
///   sit at 0x3520 and 0x3540 in `.data`.
/// * `WBase::WBase` 0x57e0: `lea rax, [0x3580]; mov [rcx], rax; lea rdx,
///   [sig]; ret`, the constructor of the embedded base storing its vtable
///   (slots `W2` 0x5870 and `W3` 0x5876, `mov eax, N; ret`).
/// * `Wrap::Wrap` 0x5800: `mov rbx, rcx; lea rax, [0x35a0]; mov [rbx],
///   rax; lea rax, [0x3580]; mov [rbx+8], rax; lea rdx, [sig]; ret`, the
///   constructor that inlines the base's initializing store at `[this+8]`
///   (its own table at 0x35a0 holds `W4` 0x587c and `W5` 0x5882).
/// * `Wrap::Call` 0x5830: `mov rax, [rcx+8]; call [rax+8]; lea rdx, [sig];
///   ret`, a call through the embedded base's vtable, which resolves to
///   `WBase`'s slot 1; `Wrap::Miss` 0x5850: the same over the field at
///   0x10, which nothing types. All pointer-seeded from 0x3470..0x3488.
/// * `TP` 0x4c20: `movsxd rax, ecx; imul rax, rax, 3; ret` (pointer-seeded
///   from 0x2d30): a parameter used only sign-extended from 32 bits.
/// * `TP2` 0x4c30: `movzx eax, cl; add eax, 1; ret` (pointer-seeded from
///   0x2d38): a parameter used only as its low byte.
/// * `RU` 0x4c40: `lea rax, [rcx + rdx * 8 + 0x10]; mov [rcx], rax; mov
///   [rcx + 8], rax; ret` (pointer-seeded from 0x2d40): one computed value
///   stored twice.
/// * `DV208` 0x4c60: `mov rax, 0x4ec4ec4ec4ec4ec5; sub rcx, rdx; imul rcx;
///   sar rdx, 6; mov rax, rdx; shr rax, 63; add rax, rdx; ret`
///   (pointer-seeded from 0x2d48): a signed `(a1 - a2) / 208` whose
///   quotient the block reads twice.
/// * `SP5` 0x4c90: `mov rax, [rsp + 0x28]; add rax, [rsp + 0x30]; ret`
///   (pointer-seeded from 0x2d50): the fifth and sixth arguments, which
///   the Microsoft convention passes on the stack.
/// * `JTG` 0x4cb0: `cmp ecx, 2; ja DEF; mov eax, ecx` and then a jump
///   through `qword [rax * 8 + 0x2e00]` over three `mov eax, N; ret` cases
///   (pointer-seeded from 0x2d58): a jump table the jump's own operand
///   names, holding absolute targets, as GCC emits.
/// * `JTM` 0x4ce0: `cmp ecx, 2; ja DEF; lea rdx, [0x1000]; mov ecx, [rdx +
///   rcx * 4 + 0x1e20]; add rcx, rdx; jmp rcx` over three cases
///   (pointer-seeded from 0x2d60): a table of offsets from a `lea`-loaded
///   base, as MSVC emits.
/// * `AQ` 0x4d20: the shape of `AS` over a condition that names a string
///   literal, `StringAtom("x") != f`, and then `test ecx, ecx; jz R; mov
///   eax, 1; R: ret` (pointer-seeded from 0x2d68): the quotes must not
///   leave a reader inside a literal, which the braces below them show.
/// * `PF` 0x4d50 and `PG` 0x4d70: `lea rax, [signature]; mov rcx, rdx;
///   call PG; ret` over `mov rax, [rcx]; ret` (pointer-seeded from
///   0x2d70). The signature string names `PF` and types its second
///   parameter `Ns::Thing *`, which it passes straight to `PG`, so `PG`
///   learns the class of its own parameter from the call.
/// * `TS1` 0x4d80 and `TS2` 0x4d90: `lea rdx, ["hello, borer world"];
///   lea rcx, [a data slot]; ret` over two different slots (pointer-seeded
///   from 0x2d78 and 0x2d80): a registration pair, one shape naming one
///   string, which a string lookup lists once with a count.
/// * `NR` 0x4da0: `mov eax, 5; imul eax, ecx; ret`, called only by `NRC`
///   0x4dc0: `call NR; xor eax, eax; ret` (pointer-seeded from 0x2d88).
///   The one caller drops the result `NR` computes itself.
/// * `ES` 0x4de0: `lea rax, [0x2f60]; ret` over a lone terminator the
///   literal `"ok"` follows in read-only data, as in a string pool
///   (pointer-seeded from 0x2d90): the empty string.
/// * `TB` 0x4e00: `lea rax, [0x2f80]; ret` over `" \t-+0"` (pointer-seeded
///   from 0x2d98): a charset table, the shape a number parser carries.
/// * `LKC` 0x4e20 (`Lk::Chk`): `DC2`'s shape with the condition
///   `"this->IsSet()"` (pointer-seeded from 0x2da0): the assert names a
///   method, which says what reads the field at 8, not what the field is
///   called, so `Lk` gets no field name.
/// * `AIA` 0x4e50 (`Arr<int>::Add`): `DC2`'s shape with the condition
///   `"this->size"` (pointer-seeded from 0x2da8): names `Arr<int>`'s field
///   at 8 `size`.
/// * `ACA` 0x4e80 (`Arr<char>::Add`): `mov eax, [rcx+8]; lea rdx,
///   [Arr<char>::Add sig]; ret` (pointer-seeded from 0x2db0): the only
///   method of its instantiation and it asserts nothing, so its field at 8
///   is named only by what `AIA` proved about the same template.
/// * `FW1` 0x4e90: `sub rsp, 0x28; mov ecx, 0x77; call FW2; add rsp, 0x28;
///   ret` (pointer-seeded from 0x2db8), calling `FW2` 0x4eb0: `sub rsp,
///   0x28; call FW3; add rsp, 0x28; ret` and `FW3` 0x4ec0: `mov eax, [rcx];
///   ret`. `FW2` reads no argument register of its own, it passes `rcx` to
///   `FW3`, so the call in `FW1` still takes one.
/// * `LT` 0x4f00: `sub rsp, 0x28; lea rcx, [TH]; call CS; add rsp, 0x28;
///   ret` (pointer-seeded from 0x2df0), calling `CS` 0x4ed0: `test ecx,
///   ecx; jz 0x4ef0; mov eax, 1; ret` with its other arm at 0x4ef0, and
///   naming `TH` 0x4ee0: `mov eax, 9; ret`. `TH` lies in the gap between
///   `CS`'s blocks, so it is inside `CS`'s range and behind padding; nothing
///   calls it and no data pointer names it, and only the `lea` says it is
///   there at all.
/// * `JTX` 0x4f20: `cmp ecx, 4; ja DEF; lea rdx, [0x1000]; movzx eax, byte
///   [rdx + rcx + 0x1eb0]; mov ecx, [rdx + rax * 4 + 0x1ea0]; add rcx, rdx;
///   jmp rcx` over two bodies (pointer-seeded from 0x2df8): the byte table
///   at 0x2eb0 reads `0, 1, 0, 1, 0`, so values 0, 2 and 4 share one body
///   and 1 and 3 the other. The case labels are the values, so the switch
///   is written on the value and not on the byte the compiler looked up.
/// * `TC` 0x4f70: `sub rsp, 0x28; mov ecx, 0x55; mov edx, 0x66; call TJ;
///   add rsp, 0x28; ret` (pointer-seeded from 0x2ec0), calling `TJ` 0x4f60:
///   `jmp FW3`. `TJ` reads nothing of its own, and knowing nothing about it
///   the call would print every argument register that held a value; `FW3`
///   reads `rcx` alone, so the call takes one.
/// * `PV` 0x4f90 and `PW` 0x4fb0 (pointer-seeded from 0x2ec8 and 0x2ed0):
///   `sub rsp, 0x28; mov ecx, N; call PT; add rsp, 0x28; ret` with `N` 7 and
///   9, calling `PT` 0x4fd0: `mov eax, ecx; ret`. Two callers pass two
///   constants to the one parameter `PT` reads, which is what its header
///   reports.
/// * `GZ` 0x5000 (`Gz::Chk`): `mov eax, [rcx]; test eax, eax; jnz R; lea
///   rcx, ["this->head"]; ...; call [ReportAssertFailure]; R: ret` (pointer-seeded
///   from 0x2ed8): the guarded field is at offset zero, which has a
///   spelling of its own.
/// * `GG` 0x5040 (`Gg::Chk`): the same over the field at 8, with a call to
///   `ReportAssertFailure` between the guard and the assertion (pointer-seeded
///   from 0x2ee0): the assertion is not always the line after its guard.
/// * `SN` 0x5080: `lea rcx, [0x3800]; ret` (pointer-seeded from 0x2ee8),
///   naming a 91-character build path at 0x3800 whose file name,
///   `probe/needle.h`, begins past the eightieth character. A real build
///   writes every assertion's path that way, so a search that reads only
///   the start of a string cannot find the file it names.
/// * `EC` 0x50c0: `sub rsp, 0x38; mov rbx, rcx; mov eax, [rbx+0x20]; mov
///   [rsp+0x20], eax; mov rcx, rdx; call WS; lea rdx, [rsp+0x20]; mov r8d,
///   32; call WR` and the same again for the byte at 0x24 with a width of 1
///   (pointer-seeded from 0x2ef0). `WS` 0x50a0 is
///   `Core::Ptr<Network::Bs>::operator ->`, named by the signature at
///   0x3900, and `WR` 0x50b0 the write it hands the stream. The two fields
///   and their widths are the message's wire format.
/// * `FF` 0x5130 (`Fr::Get`): `movss xmm0, [rcx+0x10]; mulss xmm0,
///   [rcx+0x14]; lea rdx, [Fr::Get sig]; ret` (pointer-seeded from 0x2ef8):
///   the value it returns never touches `rax`, so reading `rax` at the
///   return would leave the multiply dead and hand back a register the
///   function never set.
/// * `FZ` 0x5150 (`Fz::Set`): `mov qword [rcx+0x10], 0; lea rdx, [sig];
///   ret` and `FG` 0x5170 (`Fz::Get`): `movss xmm0, [rcx+0x10]; lea rdx,
///   [sig]; ret` (pointer-seeded from 0x2ff0 and 0x2ff8): the store zeroes
///   eight bytes across the float at 0x10 and the one after it, so the
///   widest access to the field is not the width of the field.
/// * `RG` 0x5190: `sub rsp, 0x28; lea rdx, ["Zz::Thing"]; mov r8d,
///   0x41424344; call WR; add rsp, 0x28; ret` (pointer-seeded from 0x2f18):
///   a class registration, handing a registrar the class's name and the
///   four-character code `ABCD` that identifies it on the wire.
/// * `HG` 0x51c0: `test ecx, ecx; jz 0x51e0; mov eax, 1; ret` with its
///   other arm at 0x51e0 (pointer-seeded from 0x2f50), and `HD` 0x51d0:
///   `mov eax, 99; ret` in the padding between them. Nothing calls `HD` and
///   no pointer names it; only the padding before it says it is there, and
///   it lies inside `HG`'s range while no block of `HG` covers it.
/// * `CM` 0x5200: `mov eax, [rcx+0x10]; add eax, [rcx+0x14]; add eax,
///   [rcx+0x18]; add eax, [rcx+rdx*8+0x10]; ret` (pointer-seeded from
///   0x2f58): three plain fields earn the object a layout, and the fourth
///   read indexes an array that begins at the same offset. Reading the
///   first term of that operand as the field cuts the expression apart.
/// * `LB` 0x5240: nine blocks that each add one to `ecx` and then jump,
///   `jmp 0x5258`, `jb 0x525f`, `jmp 0x5287`, `jmp 0x5273`, `jb 0x527d`,
///   `jb 0x5247`, `jb 0x525f`, `jb 0x5251` and `jmp 0x5287` (pointer-seeded
///   from 0x2f68): the loop 0x5247 -> 0x525f -> 0x5269 -> 0x5247 is only
///   ever entered at 0x525f, below its lowest block, and the blocks the
///   text writes first sit between the two. The emitter reaches 0x5247
///   first and hands the loop to its entry, which cannot structure past
///   the written blocks.
/// * `JO` 0x52a0: `test ecx, ecx; jz 0x3000; xor eax, eax; ret`
///   (pointer-seeded from 0x2f68 + 8): the branch leaves for `.data`, which
///   holds no code, so no block of this function starts there and there is
///   no label to jump to.
/// * `BC` 0x52c0: `call 0x5300; jmp 0x52d7`, `call 0x5306; cmp ecx, edx;
///   jb 0x52c0`, `call 0x530c; cmp ecx, edx; jb 0x52ca`, `call 0x5312; ret`
///   (pointer-seeded from 0x2f78), over four one-line callees at
///   0x5300..0x5312: two loops, one inside the other, and the only way out
///   of either is a `jb` that falls through. Both become `if (...) break;`,
///   and a loop whose break carries a condition still leaves.
/// * `NL` 0x5320: `call 0x5360; jmp 0x532a`, `call 0x5366; cmp ecx, edx; jb
///   0x532a`, `call 0x536c; cmp ecx, edx; jb 0x5320`, `call 0x5372; cmp
///   ecx, edx; jb 0x532a`, `call 0x5378; jmp 0x5351` (pointer-seeded from
///   0x2ea8), over five one-line callees at 0x5360..0x5378: a loop inside a
///   loop inside a loop, so the outer one's break stands below a closing
///   brace two levels in. Counting nested loops without minding what
///   indent each closes at left the outer one looking endless.
/// * `NB` 0x5390: eleven blocks that each hand their own number to the one
///   callee at 0x5445 and then branch, `jb 0x5428`, `jb 0x5390`, `jb
///   0x543a`, `jb 0x5407`, `jb 0x53a2`, `jb 0x5390`, `ret`, `jb 0x5390`,
///   `jmp 0x5428`, `jb 0x5419` and `ret` (pointer-seeded from 0x2eb8):
///   a loop inside a loop, where the inner body jumps to the outer loop's
///   header and to what follows it. Written as this loop's `continue` and
///   `break` those jumps leave the inner loop instead, and block 9's call
///   is then reached by nothing.
/// * `SL` 0x5450: eight blocks that each hand their own number to the one
///   callee at 0x54cd and then branch, `jmp 0x548f`, `jmp 0x547d`, `jmp
///   0x545f`, `jb 0x545f`, `jmp 0x54b0`, `jb 0x546e`, `jb 0x549e` and `ret`
///   (pointer-seeded from 0x2f90): two loops side by side, and one of them
///   jumps into the middle of the other. The block landed on continues its
///   own loop, so moving it to the jump changes which loop that is.
/// * `MS` 0x54e0: `movups xmm0, [rcx+0x10]; movss xmm1, [rdx+0x20]; movss
///   xmm0, xmm1; movups [rcx+0x30], xmm0; ret` (pointer-seeded from
///   0x2f98): the second `movss` writes one float into a register that
///   already holds four, and the three it does not touch stay. Read as a
///   whole-register copy, the vector loaded from `rcx+0x10` is lost.
/// * `SW` 0x5500: `mov ecx, 1; call 0x553f; jmp 0x5525`, two blocks that
///   mark themselves and return, and `mov ecx, 4; call 0x553f; cmp eax, 2;
///   ja 0x5500; jmp qword [rax*8+0x21d0]` over the three-entry table at
///   0x21d0 (pointer-seeded from 0x2728): the dispatch is reached first and
///   its arms are written as the loop around it unwinds, so by the time the
///   `switch` is printed every arm it names is already on the page.
/// * `TR` 0x5550: `mov ecx, 7; jmp 0x5560`, tail-calling `TG` 0x5560
///   (`mov eax, ecx; ret`), with `TC` 0x5570 (`call TR; xor eax, eax; ret`)
///   as its only caller (`call TR; call TG; xor eax, eax; ret`,
///   pointer-seeded from 0x2730): `TC` calls `TG` itself, which is what
///   makes `TR`'s jump a tail call, and it ignores what `TR`
///   hands back, so `TR` reads as returning nothing, and the value it drops
///   is a call.
/// * `FP` 0x5580: `mulss xmm1, xmm1; movss [rcx], xmm1; ret` takes its
///   second argument in `xmm1`, where the Microsoft x64 convention puts a
///   float; `FC` 0x5590: `mov rcx, rdx; movss xmm1, [rdx]; call FP; ret`
///   (pointer-seeded from 0x2738) passes one there. Reading only the integer registers
///   leaves the argument out of both the callee's parameters and the call.
/// * `GS` 0x1c00: `call DC; mov [0x3008], rax; ret` (pointer-seeded from
///   0x2900) stores the creator's result in a global; `GG` 0x1c10: `mov rax,
///   [0x3008]; ret` is the global's getter; `GV` 0x1c20: `call GG; mov rcx,
///   rax; mov rax, [rax]; call [rax+8]; ret` (pointer-seeded from 0x2908)
///   calls slot 1 through the getter's result. `DC` returns `DK`'s result,
///   so it creates a `Ns::Thing`, the global holds one and `GG` returns one.
/// * `DK3` 0x1c30: `push rbx; mov rbx, rcx; lea rax, [0x2910]; mov [rbx],
///   rax; mov [0x3010], rbx; call DC; mov [rbx+8], rax; pop rbx; ret`
///   (pointer-seeded from 0x2930), a constructor storing a table nothing
///   names (slots `S3`, `S4` and `FG` 0x1c50: `mov rax, [rcx+8]; ret`) that
///   registers `this` at a global (the singleton of `class_2910`) and
///   stores the creator's result at `this + 8` (a `Ns::Thing` field, which
///   `FG` returns).
/// * `TC` 0x1c60: `test ecx, ecx; jz L; test edx, edx; jz L; mov eax, ecx;
///   jmp R; L: or eax, -1; R: ret` (pointer-seeded from 0x2938): two
///   guards share the one-way block `L`, which falls into the shared
///   return `R`.
/// * `LP` 0x1c80: `xor eax, eax; L: cmp [rcx+rax], 0; jz A; cmp [rcx+rax],
///   0x20; jz B; inc rax; cmp rax, 8; jl L; or rax, -1; jmp R; A: mov eax,
///   1; jmp R; B: mov eax, 2; R: ret` (pointer-seeded from 0x2940): a scan
///   loop whose two break arms and fall-through each set the result before
///   the one shared return.
/// * `LP2` 0x1cb0: `xor eax, eax; mov r8, rcx; H: cmp [r8], 0x40; ja X; cmp
///   [r8], 0; jne A; mov eax, 16; jmp J; X: cmp [r8], 0x41; je C; cmp [r8],
///   0x42; je B; mov eax, 2; J: add r8, rax; jmp H; A: mov eax, 3; jmp R; B:
///   xor eax, eax; jmp R; C: mov rax, r8; R: ret` (pointer-seeded from
///   0x2948): a scan loop with an if/else body whose three break arms each
///   set the result before the shared return that the last one falls into.
/// * `LP3` 0x1cf0: `xor eax, eax; test edx, edx; jz F; H: cmp [rcx+rax],
///   0x40; ja X; cmp [rcx+rax], 0; jz E; mov edx, 1; jmp J; X: cmp rax, 8;
///   jge F; mov edx, 2; J: add rax, rdx; jmp H; F: or rax, -1; R: ret; E:
///   mov rax, rcx; jmp R` (pointer-seeded from 0x2950): a `while (1)` loop
///   with an if/else body whose two continuations differ, the fall-through
///   `F` the prologue also reaches and the exit `E` that only returns.
/// * `TE` 0x1d30: `LP3` again behind eight pushes and `sub rsp, 0x20`, its
///   shared return `R` an epilogue of `add rsp`, eight pops and `ret`
///   (pointer-seeded from 0x2958): ten instructions that render as one
///   `return`.
/// * `TL` 0x1d90: `LP3` whose continuation `F` is `mov ecx, 0` falling into
///   `T: call Q; ret` and whose returning exit `E` is `mov ecx, 1; jmp T`
///   (pointer-seeded from 0x2960): the exit's tail calls before it returns
///   and the loop's exits meet nowhere.
/// * `BC` 0x1e00: `lea rax, [0x2970]; mov [rcx], rax; ret`, the constructor
///   of a base class whose table holds `BF0` 0x1dd0 and `BF1` 0x1de0 (`mov
///   eax, N; ret`); `DC2` 0x1e10: `push rbx; mov rbx, rcx; call BC; lea
///   rax, [0x2988]; mov [rbx], rax; pop rbx; ret` (pointer-seeded from
///   0x29a0), the derived constructor whose table holds `BF0` and the
///   override `DF1` 0x1df0; `CB` 0x1e30: `call BF1; mov [rdx], rax; ret`
///   (pointer-seeded from 0x29a8) reads the
///   result of `BF1`, so the override `DF1`, which nothing calls, returns a
///   value too. `TT` 0x1e50: `lea rax, [0x2a00]; mov [rcx], rax; lea rax,
///   [0x2a20]; mov [rcx], rax; ret` (pointer-seeded from 0x2a40), a
///   constructor with its base's constructor inlined: it stores the base's
///   two-slot table (`BF0`, `BF1`) at 0x2a00 and then its own three-slot
///   table (`BF0`, `BF1`, `DF1`) at 0x2a20.
/// * `JT` 0x1e70: `test edx, edx; jnz E; call Q; test eax, eax; jz R; mov
///   ecx, 1; jmp T; E: cmp edx, 1; jnz R; call Q; test eax, eax; jz R; mov
///   ecx, 2; T: call Q; mov ecx, eax; call Q; R: ret` (pointer-seeded from
///   0x29b8): two arms meeting at a two-call tail, the second arm returning
///   early from two sites.
/// * `RL` 0x1ee0: `xor eax, eax; jmp C; B: inc rax; call Q; C: cmp rax, 8;
///   jl B; ret` (pointer-seeded from 0x29c0): a rotated loop, its condition
///   placed after the body and entered by a jump.
/// * `GX` 0x1f00: `test ecx, ecx; jz X; call Q; test eax, eax; jnz X; mov
///   edi, 1; J: test edi, edi; jz R; call Q; R: mov eax, edi; ret; X: xor
///   edi, edi; jmp J` (pointer-seeded from 0x29c8): two guards share the
///   one-way block `X`, which leads into the join `J` the main path falls
///   into.
/// * `BL` 0x1f30: `mov eax, 1; ret`, called only by `CW` 0x1f40: `call BL;
///   test al, al; jz X; mov eax, 5; ret; X: xor eax, eax; ret`
///   (pointer-seeded from 0x29d0): the one caller reads a byte of the result.
/// * `BB` 0x1f60: `xor eax, eax; cmp ecx, 1; sete al; ret`, called only by
///   `CB2` 0x1f70: `call BB; mov ecx, eax; test cl, cl; jz X; mov eax, 5;
///   ret; X: xor eax, eax; ret` (pointer-seeded from 0x29d8): the body ends
///   every return with a byte write while the caller copies the result whole.
/// * `BZ` 0x1f90: `movzx eax, byte [rcx+0x10]; ret`, called only by `CZ`
///   0x1fa0: `call BZ; mov edx, eax; test dl, dl; jz X; mov eax, 5; ret; X:
///   xor eax, eax; ret` (pointer-seeded from 0x29e0): the body writes the
///   whole of eax with a value that fits a byte while the caller copies it
///   whole.
/// * `BN` 0x1fc0: `mov rax, [rcx]; test rax, rax; jz Z; movzx eax, byte
///   [rax+8]; ret; Z: ret`, called only by `CN` 0x1fd0: `call BN; mov edx,
///   eax; test dl, dl; jz X; mov eax, 5; ret; X: xor eax, eax; ret`
///   (pointer-seeded from 0x29e8): one return hands back the loaded pointer,
///   reached only when it is zero.
/// * `MB` 0x1fe4: `cmp dword [rcx], 1; sete bl; call Q; test bl, bl; jz X;
///   mov eax, 5; ret; X: xor eax, eax; ret` (pointer-seeded from 0x29f0): a
///   truth value kept in a callee-saved register across a call.
/// * `CL2` 0x1660: `mov eax, [rcx+8]; lea rdx, [Cls::Has sig]; ret`
///   (pointer-seeded from 0x2130), whose signature `bool Cls::Has(int) const`
///   declares as many parameters as the method reads registers: `const`
///   alone makes it a member; the load is returned so it stays live.
/// * `AR` 0x13a0: `mov eax, ecx; ret`, a callee that reads one argument.
/// * `AC` 0x13b0: `mov ecx, 1; mov edx, 2; call AR; ret`: the second value is
///   not an argument of `AR`.
/// * `RM` 0x5640: `mov rax, 0x3730; mov [rcx], rax; ret` (pointer-seeded
///   from 0x3770), an unnamed constructor storing a table nothing else
///   names, `class_3730`. Its slot 1 is the datum `0x9999`, which the
///   reading skips, so `F0` 0x5650 (`mov eax, 3; ret`) is `vfunc_0` and
///   `F1` 0x5660 (`mov rax, [rcx]; call [rax]; ret`) stays at slot 2 as
///   `vfunc_2`, calling slot 0 of its own table.
/// * `R1` 0x5600: `mov rax, 0x3678; mov [rcx], rax; ret` (pointer-seeded
///   from 0x3780), an unnamed constructor storing the two-slot table a
///   complete object locator at 0x3658 names `Ns::Rtti`: `M0` 0x5620
///   (`mov eax, 5; ret`) is `vfunc_0` and `M1` 0x5630 (`mov rax, [rcx];
///   call [rax]; ret`) is `vfunc_1`, calling slot 0 of its own table.
/// * `R2` 0x5680: `mov rbx, rcx; mov rax, 0x3718; mov [rbx], rax; mov
///   rcx, rbx; call 0x56b0; ret` (pointer-seeded from 0x3790), the
///   constructor of `Ns::Solo`, a class whose locator-named table 0x3718
///   holds one slot (`S0` 0x56a0, `mov eax, [rcx+8]; ret`, `vfunc_0`
///   reading the field at 8), and whose init helper `X` 0x56b0 (`mov rax,
///   [rcx]; call [rax]; ret`) is handed `this` after the store, so its
///   call resolves to `Ns::Solo::vfunc_0`.
/// * `RW` 0x5700: `mov rax, 0x32b0; mov [rcx], rax; mov rax, 0x32f0; mov
///   [rcx+0x10], rax; ret` (pointer-seeded from 0x3320), the constructor
///   of `Ns::Wide`, a class whose further base `Ns::Tail` sits at
///   subobject offset 0x10 with the two-slot table 0x32f0 (`T0` 0x5740
///   and `T1` 0x5750, `mov eax, [rcx+N]; ret`), named
///   `Ns::Wide::vftable_Ns::Tail` and carrying `Ns::Tail`'s methods.
/// * `FX` 0x5c00: `lea rcx, [an is_unlocked assertion]; cmp rax,
///   0x40000000; cmp rax, 0xc0000000; ret` (pointer-seeded from 0x3e00):
///   a synchronization wrapper that mentions a check phrase while
///   comparing rwlock state bits.
/// * `KC` 0x5c40: `push rbx; mov rbx, rcx; lea rcx, ["%d"]; mov rdx, rbx;
///   call [scanf]; movzx ecx, byte [rbx]; cmp ecx, eax; sete al; movzx
///   eax, al; pop rbx; ret` (pointer-seeded from 0x3e08): a check no
///   phrase names, reading input through scanf and comparing a byte of
///   what it read against the parsed value.
///
/// `.rdata` (file offset 0x1000): the jump table at 0x2000, code pointers at
/// 0x2030, 0x2038, 0x2058 and 0x2060, `"hello, borer world"` at 0x2040, and
/// the imports `KERNEL32.dll!ReportAssertFailure` at slot 0x2050 and
/// `KERNEL32.dll!ExitProcess` at slot 0x2068. The assert reporter is named
/// after no function the SDK declares, so its arity is the four arguments
/// the assert sets up; a real API would be held to its prototype. `.data`
/// (file offset 0x2000) also carries the phrase `FX` references at
/// 0x3d20, `"%d"` at 0x3d60 and the import `ucrtbase.dll!scanf` at
/// slot 0x3da0 for `KC`, and the seeds 0x3e00 (`FX`) and 0x3e08
/// (`KC`).
pub(crate) fn fixture() -> Program {
    reset_claims();
    let mut bytes = vec![0xcc; 0x2000];
    bytes.resize(0x2100, 0);
    bytes.resize(0x5000, 0xcc);
    code_bytes(&mut bytes);
    data_bytes(&mut bytes);

    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
            Section::mapped(".data", 0x3000, 0x2000, 0x1000, true, false),
            Section::mapped(".text2", 0x4000, 0x3000, 0x2000, false, true),
        ],
    );
    p.symbols = vec![
        Symbol {
            name: "exported_c".to_owned(),
            addr: 0x1040,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_d".to_owned(),
            addr: 0x1060,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_f".to_owned(),
            addr: 0x1100,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_g".to_owned(),
            addr: 0x1130,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_h".to_owned(),
            addr: 0x1150,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_k".to_owned(),
            addr: 0x1180,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_p".to_owned(),
            addr: 0x11c0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_s".to_owned(),
            addr: 0x1200,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_w".to_owned(),
            addr: 0x1240,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_x".to_owned(),
            addr: 0x1250,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_y".to_owned(),
            addr: 0x1270,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_z".to_owned(),
            addr: 0x127b,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_y3".to_owned(),
            addr: 0x12c0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_z3".to_owned(),
            addr: 0x12ca,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_w3".to_owned(),
            addr: 0x12d0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fl".to_owned(),
            addr: 0x1300,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fl2".to_owned(),
            addr: 0x1320,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fl3".to_owned(),
            addr: 0x1340,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_m".to_owned(),
            addr: 0x1360,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_ac".to_owned(),
            addr: 0x13b0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_d1".to_owned(),
            addr: 0x1380,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_e1".to_owned(),
            addr: 0x13c0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_cs".to_owned(),
            addr: 0x13d0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fr".to_owned(),
            addr: 0x13f0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_es".to_owned(),
            addr: 0x1410,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_cc".to_owned(),
            addr: 0x1430,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fj".to_owned(),
            addr: 0x1450,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fa".to_owned(),
            addr: 0x1470,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fj8".to_owned(),
            addr: 0x1490,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_e2".to_owned(),
            addr: 0x14b0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fm".to_owned(),
            addr: 0x14d0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_fs".to_owned(),
            addr: 0x14f0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_ac2".to_owned(),
            addr: 0x1510,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_adc3".to_owned(),
            addr: 0x1520,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_dc".to_owned(),
            addr: 0x1530,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_ld".to_owned(),
            addr: 0x1550,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_ld2".to_owned(),
            addr: 0x1590,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_vd2".to_owned(),
            addr: 0x1600,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_vc".to_owned(),
            addr: 0x1610,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_vt".to_owned(),
            addr: 0x1620,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_vc2".to_owned(),
            addr: 0x1630,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "exported_lx".to_owned(),
            addr: 0x15b0,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "KERNEL32.dll!ExitProcess".to_owned(),
            addr: 0x2068,
            kind: SymbolKind::Import,
        },
        Symbol {
            name: "KERNEL32.dll!ReportAssertFailure".to_owned(),
            addr: 0x2050,
            kind: SymbolKind::Import,
        },
        Symbol {
            name: "ucrtbase.dll!scanf".to_owned(),
            addr: 0x3da0,
            kind: SymbolKind::Import,
        },
    ];
    p
}

/// Lays down every instruction of the fixture image.
///
/// Writes `b` at a virtual address of a code section.
///
/// The image's `.text` and `.text2` sit consecutively from file offset 0,
/// so the address alone names the offset.
///
/// # Arguments
///
/// * `bytes` - The image being built.
/// * `va` - The virtual address to write at, in any code section.
/// * `b` - The bytes to write.
pub(crate) fn put(bytes: &mut [u8], va: u64, b: &[u8]) {
    claim(va, b.len(), "code");
    let off = saturating_usize(va) - 0x1000;
    bytes[off..off + b.len()].copy_from_slice(b);
}

/// Writes `b` at a virtual address of `.rdata` or `.data`.
///
/// The two sit consecutively from file offset 0x1000, so the address
/// alone names the offset.
///
/// # Arguments
///
/// * `bytes` - The image being built.
/// * `rva` - The virtual address to write at, in `.rdata` or `.data`.
/// * `b` - The bytes to write.
pub(crate) fn put_rdata(bytes: &mut [u8], rva: u64, b: &[u8]) {
    claim(rva, b.len(), "data");
    let off = 0x1000 + (saturating_usize(rva) - 0x2000);
    bytes[off..off + b.len()].copy_from_slice(b);
}
// Every span one build of the fixture writes, so a write over a span
// another fixture already claimed panics where it happens, naming both
// writers, instead of quietly corrupting a neighbor's string or pointer -
// the failure mode of three separate address collisions between fixtures
// written in parallel. The map is cleared at each build of `fixture`:
// overlaps within one build are the bug; a later build (another test,
// another process) starts clean.
thread_local! {
    /// Each test runs on its own thread, so each build sees its own
    /// claims: a parallel test's build cannot wipe or read another's.
    static CLAIMS: std::cell::RefCell<Option<std::collections::BTreeMap<(u64, u64), String>>> =
        const { std::cell::RefCell::new(None) };
}

/// Records a write of `len` bytes at `va` in the claim map, refusing an
/// overlap with a claim already there.
///
/// # Panics
///
/// When another write of the same build already covers any byte of the
/// span: the message names both writers' source lines.
#[track_caller]
#[allow(
    clippy::panic,
    reason = "a corrupted fixture is worthless; the panic names both writers"
)]
fn claim(va: u64, len: usize, kind: &str) {
    let end = va + u64::try_from(len).unwrap_or(0);
    let here = format!("{kind} {}", std::panic::Location::caller());
    CLAIMS.with_borrow_mut(|claims| {
        let Some(map) = claims.as_mut() else {
            return;
        };
        for (&(start, stop), first) in map.range(..(end, u64::MAX)) {
            // An exactly-identical span re-claimed is a deliberate
            // rewrite of the same words (two complete-object locators
            // sharing one type descriptor); only a partial overlap of
            // different spans corrupts a neighbor.
            if start < end && stop > va && (start, stop) != (va, end) {
                panic!(
                    "the fixture writes {kind} at {va:#x}..{end:#x} ({here}) over                      {start:#x}..{stop:#x} ({first}); two fixtures claim one span"
                );
            }
        }
        map.insert((va, end), here);
    });
}

/// Clears the claim map at the start of a build; a later build (another
/// test, another process) starts clean.
pub(crate) fn reset_claims() {
    CLAIMS.with_borrow_mut(|claims| *claims = Some(std::collections::BTreeMap::new()));
}

/// The next free address of a kind above every claim, rounded up to 16.
///
/// For a new fixture to allocate from, instead of hand-picking an address
/// another fixture may already hold; zero when no build has claimed.
///
#[allow(
    dead_code,
    reason = "the analysis test reads it; the other test binaries build the module whole"
)]
pub(crate) fn next_free(kind: &str) -> u64 {
    CLAIMS.with_borrow(|claims| {
        let end = claims.as_ref().map_or(0, |map| {
            map.iter()
                .filter(|(_, first)| first.starts_with(kind))
                .map(|(&(start, stop), _)| stop.max(start))
                .max()
                .unwrap_or(0)
        });
        (end + 0xf) & !0xf
    })
}

/// The virtual-call fixtures, split out for the same reason.
mod interlocked;
mod vcall;

/// The license-check fixtures, split out for the same reason.
mod checks;

/// Split out of [`fixture`] because one function of two thousand statements
/// overflows the formatter's stack.
///
/// # Arguments
///
/// * `bytes` - The image being built, `.text` at file offset 0.
fn code_bytes(bytes: &mut [u8]) {
    put(bytes, 0x1000, &[0xe8, 0x1b, 0x00, 0x00, 0x00]); // ASM: call 0x1020
    put(bytes, 0x1005, &[0x85, 0xc9]); // ASM: test ecx,ecx
    put(bytes, 0x1007, &[0x74, 0x05]); // ASM: jz 0x100e
    put(bytes, 0x1009, &[0xe8, 0x22, 0x00, 0x00, 0x00]); // ASM: call 0x1030
    put(bytes, 0x100e, &[0x31, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1010, &[0xc3]); // ASM: ret
    put(bytes, 0x1020, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x1025, &[0xc3]); // ASM: ret
    put(bytes, 0x1030, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x1035, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x1040,
        &[0x48, 0x8b, 0x05, 0xc0, 0x0f, 0x00, 0x00], // ASM: mov rax,[rip+0xfc0] -> 0x2007
    );
    put(bytes, 0x1047, &[0xc3]); // ASM: ret

    put(bytes, 0x1060, &[0x89, 0xc8]); // ASM: mov eax,ecx
    put(bytes, 0x1062, &[0x83, 0xf9, 0x03]); // ASM: cmp ecx,3
    put(bytes, 0x1065, &[0x77, 0x19]); // ASM: ja 0x1080
    put(
        bytes,
        0x1067,
        &[0x48, 0x8d, 0x05, 0x92, 0x0f, 0x00, 0x00], // ASM: lea rax,[rip+0xf92] -> 0x2000
    );
    put(bytes, 0x106e, &[0x48, 0x63, 0xc9]); // ASM: movsxd rcx,ecx
    put(bytes, 0x1071, &[0xff, 0x24, 0xc8]); // ASM: jmp qword [rax+rcx*8]
    put(bytes, 0x1074, &[0xc3]); // ASM: ret (unreachable)
    put(bytes, 0x1080, &[0x31, 0xc0, 0xc3]); // ASM: xor eax,eax; ret (default)
    put(bytes, 0x1090, &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret (case 0)
    put(bytes, 0x10a0, &[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,2; ret (case 1)
    put(bytes, 0x10b0, &[0xb8, 0x03, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,3; ret (case 2)
    put(bytes, 0x10c0, &[0xb8, 0x04, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,4; ret (case 3)
    put(bytes, 0x10e0, &[0xc3]); // ASM: ret (E)

    put(bytes, 0x1100, &[0x31, 0xc9]); // ASM: xor ecx,ecx
    put(bytes, 0x1102, &[0xb8, 0x00, 0x00, 0x00, 0x00]); // ASM: mov eax,0
    put(bytes, 0x1107, &[0x83, 0xf9, 0x05]); // ASM: cmp ecx,5
    put(bytes, 0x110a, &[0x7d, 0x0a]); // ASM: jge 0x1116
    put(bytes, 0x110c, &[0x01, 0xc8]); // ASM: add eax,ecx
    put(bytes, 0x110e, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x1110, &[0xeb, 0xf5]); // ASM: jmp 0x1107
    put(bytes, 0x1116, &[0xc3]); // ASM: ret
    put(bytes, 0x1130, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,7
    put(bytes, 0x1135, &[0x85, 0xc9]); // ASM: test ecx,ecx
    put(bytes, 0x1137, &[0x74, 0x03]); // ASM: jz 0x113c
    put(bytes, 0x1139, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x113b, &[0x90]); // ASM: nop
    put(bytes, 0x113c, &[0xc3]); // ASM: ret
    put(bytes, 0x1150, &[0x85, 0xc9]); // ASM: test ecx,ecx
    put(bytes, 0x1152, &[0x74, 0x02]); // ASM: jz 0x1156
    put(bytes, 0x1154, &[0x89, 0x0a]); // ASM: mov [rdx],ecx
    put(bytes, 0x1156, &[0xc3]); // ASM: ret
    put(bytes, 0x1180, &[0xb8, 0x00, 0x00, 0x00, 0x00]); // ASM: mov eax,0
    put(bytes, 0x1185, &[0x83, 0xf8, 0x05]); // ASM: cmp eax,5
    put(bytes, 0x1188, &[0x7d, 0x0e]); // ASM: jge 0x1198
    put(bytes, 0x118a, &[0x85, 0xdb]); // ASM: test ebx,ebx
    put(bytes, 0x118c, &[0x75, 0x0a]); // ASM: jne 0x1198
    put(bytes, 0x118e, &[0xff, 0xc0]); // ASM: inc eax
    put(bytes, 0x1190, &[0xeb, 0xf3]); // ASM: jmp 0x1185
    put(bytes, 0x1198, &[0xc3]); // ASM: ret
    put(bytes, 0x11c0, &[0xb9, 0x0a, 0x00, 0x00, 0x00]); // ASM: mov ecx,10
    put(bytes, 0x11c5, &[0xba, 0x14, 0x00, 0x00, 0x00]); // ASM: mov edx,20
    put(bytes, 0x11ca, &[0xe8, 0x11, 0x00, 0x00, 0x00]); // ASM: call 0x11e0
    put(bytes, 0x11cf, &[0xc3]); // ASM: ret
    put(bytes, 0x11e0, &[0xc3]); // ASM: ret (Q)
    put(
        bytes,
        0x1200,
        &[0x48, 0x8d, 0x0d, 0x39, 0x0e, 0x00, 0x00], // ASM: lea rcx,[rip+0xe39] -> 0x2040
    );
    put(bytes, 0x1207, &[0xe8, 0xd4, 0xff, 0xff, 0xff]); // ASM: call 0x11e0
    put(bytes, 0x120c, &[0xc3]); // ASM: ret
    put(bytes, 0x1210, &[0xff, 0x25, 0x3a, 0x0e, 0x00, 0x00]); // ASM: jmp qword [rip+0xe3a] -> 0x2050
    put(bytes, 0x1220, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1210
    put(bytes, 0x1225, &[0xc3]); // ASM: ret
    put(bytes, 0x1230, &[0xff, 0x15, 0x1a, 0x0e, 0x00, 0x00]); // ASM: call qword [rip+0xe1a] -> 0x2050
    put(bytes, 0x1236, &[0xc3]); // ASM: ret
    put(bytes, 0x1240, &[0xb9, 0x01, 0x00, 0x00, 0x00]); // ASM: mov ecx,1
    put(bytes, 0x1245, &[0xe9, 0xd6, 0xfd, 0xff, 0xff]); // ASM: jmp 0x1020 (A)
    put(bytes, 0x1250, &[0x48, 0xc7, 0xc1, 0xe0, 0x10, 0x00, 0x00]); // ASM: mov rcx,0x10e0 (E)
    put(bytes, 0x1257, &[0x48, 0xc7, 0xc2, 0x40, 0x20, 0x00, 0x00]); // ASM: mov rdx,0x2040 (string)
    put(bytes, 0x125e, &[0xe8, 0x7d, 0xff, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1263, &[0xc3]); // ASM: ret
    put(bytes, 0x1270, &[0xb9, 0x01, 0x00, 0x00, 0x00]); // ASM: mov ecx,1
    put(bytes, 0x1275, &[0xff, 0x15, 0xed, 0x0d, 0x00, 0x00]); // ASM: call qword [rip+0xded] -> 0x2068 (ExitProcess)
    put(bytes, 0x127b, &[0xb8, 0x03, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,3; ret (Z)
    put(bytes, 0x12b0, &[0xeb, 0xfe]); // ASM: jmp $ (NR)
    put(bytes, 0x12c0, &[0xb9, 0x02, 0x00, 0x00, 0x00]); // ASM: mov ecx,2
    put(bytes, 0x12c5, &[0xe8, 0xe6, 0xff, 0xff, 0xff]); // ASM: call 0x12b0 (NR)
    put(bytes, 0x12ca, &[0xb8, 0x04, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,4; ret (Z3)
    put(bytes, 0x12d0, &[0xb9, 0x03, 0x00, 0x00, 0x00]); // ASM: mov ecx,3
    put(bytes, 0x12d5, &[0xe8, 0xd6, 0xff, 0xff, 0xff]); // ASM: call 0x12b0 (NR)
    put(bytes, 0x12da, &[0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,5; ret (dead)
    put(bytes, 0x1300, &[0xf3, 0x0f, 0x10, 0x01]); // ASM: movss xmm0,[rcx]
    put(bytes, 0x1304, &[0xf3, 0x0f, 0x58, 0x41, 0x04]); // ASM: addss xmm0,[rcx+4]
    put(bytes, 0x1309, &[0xf3, 0x0f, 0x59, 0x41, 0x08]); // ASM: mulss xmm0,[rcx+8]
    put(bytes, 0x130e, &[0xf3, 0x0f, 0x51, 0xc0]); // ASM: sqrtss xmm0,xmm0
    put(bytes, 0x1312, &[0xf3, 0x0f, 0x2c, 0xc0]); // ASM: cvttss2si eax,xmm0
    put(bytes, 0x1316, &[0xc3]); // ASM: ret
    put(bytes, 0x1320, &[0xf3, 0x0f, 0x10, 0x01]); // ASM: movss xmm0,[rcx]
    put(bytes, 0x1324, &[0x0f, 0x57, 0x05, 0x45, 0x0d, 0x00, 0x00]); // ASM: xorps xmm0,[rip+0xd45] -> 0x2070
    put(bytes, 0x132b, &[0xf3, 0x0f, 0x11, 0x02]); // ASM: movss [rdx],xmm0
    put(bytes, 0x132f, &[0xf3, 0x0f, 0x10, 0x49, 0x04]); // ASM: movss xmm1,[rcx+4]
    put(bytes, 0x1334, &[0x0f, 0x54, 0x0d, 0x45, 0x0d, 0x00, 0x00]); // ASM: andps xmm1,[rip+0xd45] -> 0x2080
    put(bytes, 0x133b, &[0xf3, 0x0f, 0x11, 0x4a, 0x04]); // ASM: movss [rdx+4],xmm1
    put(bytes, 0x1340, &[0xf3, 0x0f, 0x2a, 0xc1]); // ASM: cvtsi2ss xmm0,ecx
    put(bytes, 0x1344, &[0xf3, 0x0f, 0x59, 0xc0]); // ASM: mulss xmm0,xmm0
    put(bytes, 0x1348, &[0xf3, 0x0f, 0x5a, 0xc0]); // ASM: cvtss2sd xmm0,xmm0
    put(bytes, 0x134c, &[0xf2, 0x0f, 0x11, 0x02]); // ASM: movsd [rdx],xmm0
    put(bytes, 0x1350, &[0x0f, 0xc6, 0xc8, 0x1b]); // ASM: shufps xmm1,xmm0,0x1b
    put(bytes, 0x1354, &[0x0f, 0x29, 0x4a, 0x10]); // ASM: movaps [rdx+0x10],xmm1
    put(bytes, 0x1358, &[0xc3]); // ASM: ret
    put(bytes, 0x1360, &[0x48, 0x87, 0x11]); // ASM: xchg [rcx],rdx
    put(bytes, 0x1363, &[0x48, 0x0f, 0xab, 0x51, 0x08]); // ASM: bts qword [rcx+8],rdx
    put(bytes, 0x1368, &[0xc5, 0xf8, 0x28, 0x41, 0x10]); // ASM: vmovaps xmm0,[rcx+0x10]
    put(bytes, 0x136d, &[0xc5, 0xf8, 0x29, 0x41, 0x20]); // ASM: vmovaps [rcx+0x20],xmm0
    put(bytes, 0x1372, &[0x0f, 0xae, 0x59, 0x30]); // ASM: stmxcsr [rcx+0x30]
    put(bytes, 0x1376, &[0x48, 0x89, 0xd0]); // ASM: mov rax,rdx
    put(bytes, 0x1379, &[0xc3]); // ASM: ret
    put(bytes, 0x1380, &[0x48, 0x89, 0xd7]); // ASM: mov rdi,rdx
    put(bytes, 0x1383, &[0x85, 0xc9]); // ASM: test ecx,ecx
    put(bytes, 0x1385, &[0x74, 0x05]); // ASM: jz 0x138c
    put(bytes, 0x1387, &[0xe8, 0x54, 0xfe, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x138c, &[0x48, 0x89, 0xf8]); // ASM: mov rax,rdi
    put(bytes, 0x138f, &[0xc3]); // ASM: ret
    put(bytes, 0x13a0, &[0x89, 0xc8, 0xc3]); // ASM: mov eax,ecx; ret (AR)
    put(bytes, 0x13b0, &[0xb9, 0x01, 0x00, 0x00, 0x00]); // ASM: mov ecx,1
    put(bytes, 0x13b5, &[0xba, 0x02, 0x00, 0x00, 0x00]); // ASM: mov edx,2
    put(bytes, 0x13ba, &[0xe8, 0xe1, 0xff, 0xff, 0xff]); // ASM: call 0x13a0 (AR)
    put(bytes, 0x13bf, &[0xc3]); // ASM: ret
    put(bytes, 0x13c0, &[0x48, 0x85, 0xc9]); // ASM: test rcx,rcx
    put(bytes, 0x13c3, &[0x75, 0x04]); // ASM: jne 0x13c9
    put(bytes, 0x13c5, &[0x8d, 0x41, 0x19]); // ASM: lea eax,[rcx+0x19]
    put(bytes, 0x13c8, &[0xc3]); // ASM: ret
    put(bytes, 0x13c9, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x13ce, &[0xc3]); // ASM: ret
    put(bytes, 0x13d0, &[0x48, 0x89, 0x5c, 0x24, 0x08]); // ASM: mov [rsp+8],rbx
    put(bytes, 0x13d5, &[0x48, 0x89, 0xcb]); // ASM: mov rbx,rcx
    put(bytes, 0x13d8, &[0xe8, 0x03, 0xfe, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x13dd, &[0x48, 0x89, 0xd8]); // ASM: mov rax,rbx
    put(bytes, 0x13e0, &[0x48, 0x8b, 0x5c, 0x24, 0x08]); // ASM: mov rbx,[rsp+8]
    put(bytes, 0x13e5, &[0xc3]); // ASM: ret
    put(bytes, 0x13f0, &[0xe8, 0x0b, 0x00, 0x00, 0x00]); // ASM: call 0x1400 (FRET)
    put(bytes, 0x13f5, &[0xf3, 0x0f, 0x11, 0x01]); // ASM: movss [rcx],xmm0
    put(bytes, 0x13f9, &[0xc3]); // ASM: ret
    put(bytes, 0x1400, &[0x0f, 0x57, 0xc0, 0xc3]); // ASM: xorps xmm0,xmm0; ret (FRET)
    put(bytes, 0x1410, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (ES)
    put(bytes, 0x1414, &[0x48, 0x83, 0x64, 0x24, 0x20, 0x00]); // ASM: and qword [rsp+0x20],0
    put(bytes, 0x141a, &[0x4c, 0x8d, 0x4c, 0x24, 0x20]); // ASM: lea r9,[rsp+0x20]
    put(bytes, 0x141f, &[0xe8, 0x7c, 0xff, 0xff, 0xff]); // ASM: call 0x13a0 (AR)
    put(bytes, 0x1424, &[0x48, 0x8b, 0x44, 0x24, 0x20]); // ASM: mov rax,[rsp+0x20]
    put(bytes, 0x1429, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x142d, &[0xc3]); // ASM: ret
    put(bytes, 0x1430, &[0x31, 0xd2]); // ASM: xor edx,edx (CC)
    put(bytes, 0x1432, &[0x85, 0xc9]); // ASM: test ecx,ecx
    put(bytes, 0x1434, &[0x75, 0x0a]); // ASM: jne 0x1440
    put(bytes, 0x1436, &[0x85, 0xd2]); // ASM: test edx,edx
    put(bytes, 0x1438, &[0x74, 0x06]); // ASM: je 0x1440
    put(bytes, 0x143a, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x143f, &[0xc3]); // ASM: ret
    put(bytes, 0x1440, &[0x31, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1442, &[0xc3]); // ASM: ret
    put(bytes, 0x1450, &[0x8b, 0xc1]); // ASM: mov eax,ecx (FJ)
    put(bytes, 0x1452, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x1454, &[0x75, 0x04]); // ASM: jne 0x145a
    put(bytes, 0x1456, &[0x8b, 0xc2]); // ASM: mov eax,edx
    put(bytes, 0x1458, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x145a, &[0x0f, 0x94, 0xc0]); // ASM: sete al
    put(bytes, 0x145d, &[0x0f, 0xb6, 0xc0]); // ASM: movzx eax,al
    put(bytes, 0x1460, &[0xc3]); // ASM: ret
    put(bytes, 0x1470, &[0x8b, 0xc1]); // ASM: mov eax,ecx (FA)
    put(bytes, 0x1472, &[0x83, 0xf8, 0x05]); // ASM: cmp eax,5
    put(bytes, 0x1475, &[0x8b, 0xd0]); // ASM: mov edx,eax
    put(bytes, 0x1477, &[0x7c, 0x08]); // ASM: jl 0x1481
    put(bytes, 0x1479, &[0xba, 0x03, 0x00, 0x00, 0x00]); // ASM: mov edx,3
    put(bytes, 0x147e, &[0x83, 0xfa, 0x05]); // ASM: cmp edx,5
    put(bytes, 0x1481, &[0x0f, 0x9c, 0xc0]); // ASM: setl al
    put(bytes, 0x1484, &[0x0f, 0xb6, 0xc0]); // ASM: movzx eax,al
    put(bytes, 0x1487, &[0xc3]); // ASM: ret
    put(bytes, 0x1490, &[0x8a, 0xc1]); // ASM: mov al,cl (FJ8)
    put(bytes, 0x1492, &[0x84, 0xc0]); // ASM: test al,al
    put(bytes, 0x1494, &[0x75, 0x04]); // ASM: jne 0x149a
    put(bytes, 0x1496, &[0x8a, 0xc2]); // ASM: mov al,dl
    put(bytes, 0x1498, &[0x84, 0xc0]); // ASM: test al,al
    put(bytes, 0x149a, &[0x0f, 0x94, 0xc0]); // ASM: sete al
    put(bytes, 0x149d, &[0x0f, 0xb6, 0xc0]); // ASM: movzx eax,al
    put(bytes, 0x14a0, &[0xc3]); // ASM: ret
    put(bytes, 0x14b0, &[0x85, 0xc0]); // ASM: test eax,eax (E2)
    put(bytes, 0x14b2, &[0x75, 0x0c]); // ASM: jne 0x14c0
    put(bytes, 0x14b4, &[0x8b, 0x02]); // ASM: mov eax,[rdx]
    put(bytes, 0x14b6, &[0xc7, 0x02, 0x01, 0x00, 0x00, 0x00]); // ASM: mov dword [rdx],1
    put(bytes, 0x14bc, &[0x8d, 0x40, 0x19]); // ASM: lea eax,[rax+0x19]
    put(bytes, 0x14bf, &[0xc3]); // ASM: ret
    put(bytes, 0x14c0, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x14c5, &[0xc3]); // ASM: ret
    put(bytes, 0x14d0, &[0x85, 0xc9]); // ASM: test ecx,ecx (FM)
    put(bytes, 0x14d2, &[0x75, 0x05]); // ASM: jne 0x14d9
    put(bytes, 0x14d4, &[0x83, 0x3a, 0x05]); // ASM: cmp dword [rdx],5
    put(bytes, 0x14d7, &[0xeb, 0x04]); // ASM: jmp 0x14dd
    put(bytes, 0x14d9, &[0x83, 0x7a, 0x04, 0x05]); // ASM: cmp dword [rdx+4],5
    put(bytes, 0x14dd, &[0x0f, 0x9c, 0xc0]); // ASM: setl al
    put(bytes, 0x14e0, &[0x0f, 0xb6, 0xc0]); // ASM: movzx eax,al
    put(bytes, 0x14e3, &[0xc3]); // ASM: ret
    put(bytes, 0x14f0, &[0x3d, 0x05, 0x00, 0x00, 0x00]); // ASM: cmp eax,5 (FS)
    put(bytes, 0x14f5, &[0x8b, 0xc2]); // ASM: mov eax,edx
    put(bytes, 0x14f7, &[0x7c, 0x01]); // ASM: jl 0x14fa
    put(bytes, 0x14f9, &[0xc3]); // ASM: ret (C)
    put(bytes, 0x14fa, &[0x0f, 0x9c, 0xc0]); // ASM: setl al (B)
    put(bytes, 0x14fd, &[0x0f, 0xb6, 0xc0]); // ASM: movzx eax,al
    put(bytes, 0x1500, &[0xeb, 0xf7]); // ASM: jmp 0x14f9
    put(bytes, 0x1510, &[0x85, 0xc9]); // ASM: test ecx,ecx (AC2)
    put(bytes, 0x1512, &[0x75, 0x05]); // ASM: jne 0x1519
    put(bytes, 0x1514, &[0x48, 0x01, 0xd0]); // ASM: add rax,rdx
    put(bytes, 0x1517, &[0xeb, 0x03]); // ASM: jmp 0x151c
    put(bytes, 0x1519, &[0x48, 0x01, 0xc8]); // ASM: add rax,rcx
    put(bytes, 0x151c, &[0x48, 0x11, 0xd0]); // ASM: adc rax,rdx
    put(bytes, 0x151f, &[0xc3]); // ASM: ret
    put(bytes, 0x1520, &[0x0f, 0xba, 0xe1, 0x00]); // ASM: bt ecx,0 (ADC3)
    put(bytes, 0x1524, &[0x11, 0x02]); // ASM: adc [rdx],eax
    put(bytes, 0x1526, &[0x44, 0x11, 0x42, 0x04]); // ASM: adc [rdx+4],r8d
    put(bytes, 0x152a, &[0x0f, 0x92, 0xc1]); // ASM: setb cl
    put(bytes, 0x152d, &[0xc3]); // ASM: ret
    put(bytes, 0x1530, &[0x83, 0xe9, 0x01]); // ASM: sub ecx,1 (DC)
    put(bytes, 0x1533, &[0x83, 0xf9, 0x01]); // ASM: cmp ecx,1
    put(bytes, 0x1536, &[0x75, 0x06]); // ASM: jne 0x153e
    put(bytes, 0x1538, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x153d, &[0xc3]); // ASM: ret
    put(bytes, 0x153e, &[0x31, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1540, &[0xc3]); // ASM: ret
    put(bytes, 0x1550, &[0x83, 0xf9, 0x05]); // ASM: cmp ecx,5 (LD)
    put(bytes, 0x1553, &[0x7f, 0x18]); // ASM: jg 0x156d
    put(bytes, 0x1555, &[0x83, 0xf9, 0x01]); // ASM: cmp ecx,1
    put(bytes, 0x1558, &[0x75, 0x07]); // ASM: jne 0x1561
    put(bytes, 0x155a, &[0xba, 0x0a, 0x00, 0x00, 0x00]); // ASM: mov edx,10
    put(bytes, 0x155f, &[0xeb, 0x1d]); // ASM: jmp 0x157e
    put(bytes, 0x1561, &[0x83, 0xf9, 0x02]); // ASM: cmp ecx,2
    put(bytes, 0x1564, &[0x75, 0x13]); // ASM: jne 0x1579
    put(bytes, 0x1566, &[0xba, 0x14, 0x00, 0x00, 0x00]); // ASM: mov edx,20
    put(bytes, 0x156b, &[0xeb, 0x11]); // ASM: jmp 0x157e
    put(bytes, 0x156d, &[0x83, 0xf9, 0x06]); // ASM: cmp ecx,6 (U)
    put(bytes, 0x1570, &[0x75, 0x07]); // ASM: jne 0x1579
    put(bytes, 0x1572, &[0xba, 0x3c, 0x00, 0x00, 0x00]); // ASM: mov edx,60
    put(bytes, 0x1577, &[0xeb, 0x05]); // ASM: jmp 0x157e
    put(bytes, 0x1579, &[0xba, 0x00, 0x00, 0x00, 0x00]); // ASM: mov edx,0 (D)
    put(bytes, 0x157e, &[0x8b, 0xc2]); // ASM: mov eax,edx (T)
    put(bytes, 0x1580, &[0xe8, 0x5b, 0xfc, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1585, &[0xc3]); // ASM: ret
    put(bytes, 0x1590, &[0x85, 0xc9]); // ASM: test ecx,ecx (LD2)
    put(bytes, 0x1592, &[0x74, 0x0b]); // ASM: jz 0x159f
    put(bytes, 0x1594, &[0xc7, 0x02, 0x01, 0x00, 0x00, 0x00]); // ASM: mov dword [rdx],1
    put(bytes, 0x159a, &[0x83, 0xf9, 0x06]); // ASM: cmp ecx,6
    put(bytes, 0x159d, &[0x74, 0x07]); // ASM: je 0x15a6
    put(bytes, 0x159f, &[0xba, 0x00, 0x00, 0x00, 0x00]); // ASM: mov edx,0 (D)
    put(bytes, 0x15a4, &[0xeb, 0x05]); // ASM: jmp 0x15ab
    put(bytes, 0x15a6, &[0xba, 0x3c, 0x00, 0x00, 0x00]); // ASM: mov edx,60 (X)
    put(bytes, 0x15ab, &[0x8b, 0xc2]); // ASM: mov eax,edx (T)
    put(bytes, 0x15ad, &[0xc3]); // ASM: ret
    put(bytes, 0x15b0, &[0x85, 0xc9]); // ASM: test ecx,ecx (LX)
    put(bytes, 0x15b2, &[0x74, 0x0f]); // ASM: jz 0x15c3
    put(bytes, 0x15b4, &[0x48, 0x83, 0xc8, 0xff]); // ASM: or rax,-1
    put(bytes, 0x15b8, &[0x48, 0xff, 0xc0]); // ASM: inc rax (H)
    put(bytes, 0x15bb, &[0x80, 0x3c, 0x01, 0x20]); // ASM: cmp byte [rcx+rax],0x20
    put(bytes, 0x15bf, &[0x75, 0xf7]); // ASM: jne 0x15b8
    put(bytes, 0x15c1, &[0xeb, 0x02]); // ASM: jmp 0x15c5
    put(bytes, 0x15c3, &[0x31, 0xc0]); // ASM: xor eax,eax (A)
    put(bytes, 0x15c5, &[0xe8, 0x16, 0xfc, 0xff, 0xff]); // ASM: call 0x11e0 (Q) (J)
    put(bytes, 0x15ca, &[0xc3]); // ASM: ret
    put(bytes, 0x15d0, &[0x48, 0x8d, 0x15, 0xc9, 0x0a, 0x00, 0x00]); // ASM: lea rdx,[rip+0xac9] -> 0x20a0 (NM)
    put(bytes, 0x15d7, &[0xe8, 0x04, 0xfc, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x15dc, &[0xc3]); // ASM: ret
    put(bytes, 0x15e0, &[0x48, 0x8d, 0x15, 0xd9, 0x0a, 0x00, 0x00]); // ASM: lea rdx,[rip+0xad9] -> 0x20c0 (NM2)
    put(bytes, 0x15e7, &[0x4c, 0x8d, 0x05, 0xb2, 0x0a, 0x00, 0x00]); // ASM: lea r8,[rip+0xab2] -> 0x20a0
    put(bytes, 0x15ee, &[0xe8, 0xdd, 0xff, 0xff, 0xff]); // ASM: call 0x15d0 (NM)
    put(bytes, 0x15f3, &[0xc3]); // ASM: ret
    put(bytes, 0x1600, &[0x8b, 0x01]); // ASM: mov eax,[rcx] (VD2)
    put(bytes, 0x1602, &[0xe8, 0x99, 0xfd, 0xff, 0xff]); // ASM: call 0x13a0 (AR)
    put(bytes, 0x1607, &[0xc7, 0x41, 0x04, 0x01, 0x00, 0x00, 0x00]); // ASM: mov dword [rcx+4],1
    put(bytes, 0x160e, &[0xc3]); // ASM: ret
    put(bytes, 0x1610, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1600 (VD2) (VC)
    put(bytes, 0x1615, &[0xb8, 0x00, 0x00, 0x00, 0x00]); // ASM: mov eax,0
    put(bytes, 0x161a, &[0xc3]); // ASM: ret
    put(bytes, 0x1620, &[0xe8, 0xdb, 0xff, 0xff, 0xff]); // ASM: call 0x1600 (VD2) (VT)
    put(bytes, 0x1625, &[0xc3]); // ASM: ret
    put(bytes, 0x1630, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1620 (VT) (VC2)
    put(bytes, 0x1635, &[0xb8, 0x00, 0x00, 0x00, 0x00]); // ASM: mov eax,0
    put(bytes, 0x163a, &[0xc3]); // ASM: ret
    put(bytes, 0x1640, &[0x89, 0x51, 0x08]); // ASM: mov [rcx+8],edx (CL1)
    put(bytes, 0x1643, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
    put(bytes, 0x1646, &[0x48, 0x89, 0x41, 0x10]); // ASM: mov [rcx+0x10],rax
    put(bytes, 0x164a, &[0x48, 0x8d, 0x15, 0x8f, 0x0a, 0x00, 0x00]); // ASM: lea rdx,[rip+0xa8f] -> 0x20e0
    put(bytes, 0x1651, &[0x48, 0x8d, 0x49, 0x20]); // ASM: lea rcx,[rcx+0x20]
    put(bytes, 0x1655, &[0xe8, 0x16, 0x00, 0x00, 0x00]); // ASM: call 0x1670 (CL3)
    put(bytes, 0x165a, &[0xc3]); // ASM: ret
    put(bytes, 0x1670, &[0x8b, 0x41, 0x04]); // ASM: mov eax,[rcx+4] (CL3)
    put(bytes, 0x1673, &[0x48, 0x8d, 0x15, 0xc6, 0x0a, 0x00, 0x00]); // ASM: lea rdx,[rip+0xac6] -> 0x2140
    put(bytes, 0x167a, &[0xc3]); // ASM: ret
    put(bytes, 0x1680, &[0x89, 0x11]); // ASM: mov [rcx],edx (HR)
    put(bytes, 0x1682, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx
    put(bytes, 0x1685, &[0x48, 0x8d, 0x15, 0xf4, 0x0a, 0x00, 0x00]); // ASM: lea rdx,[rip+0xaf4] -> 0x2180
    put(bytes, 0x168c, &[0xc3]); // ASM: ret
    put(bytes, 0x1690, &[0xb8, 0x00, 0x01, 0x00, 0x00]); // ASM: mov eax,0x100 (PW)
    put(bytes, 0x1695, &[0x85, 0xc9]); // ASM: test ecx,ecx
    put(bytes, 0x1697, &[0x74, 0x04]); // ASM: jz 0x169d
    put(bytes, 0x1699, &[0x8a, 0x01]); // ASM: mov al,[rcx]
    put(bytes, 0x169b, &[0xeb, 0x03]); // ASM: jmp 0x16a0
    put(bytes, 0x169d, &[0x8a, 0x41, 0x01]); // ASM: mov al,[rcx+1]
    put(bytes, 0x16a0, &[0x89, 0x02]); // ASM: mov [rdx],eax
    put(bytes, 0x16a2, &[0xc3]); // ASM: ret
    put(bytes, 0x16b0, &[0x8a, 0x01]); // ASM: mov al,[rcx] (PC)
    put(bytes, 0x16b2, &[0x88, 0x02]); // ASM: mov [rdx],al
    put(bytes, 0x16b4, &[0x8a, 0x41, 0x01]); // ASM: mov al,[rcx+1]
    put(bytes, 0x16b7, &[0x88, 0x42, 0x01]); // ASM: mov [rdx+1],al
    put(bytes, 0x16ba, &[0xb8, 0x00, 0x00, 0x00, 0x00]); // ASM: mov eax,0
    put(bytes, 0x16bf, &[0xc3]); // ASM: ret
    put(bytes, 0x16c0, &[0x85, 0xc9]); // ASM: test ecx,ecx (RL)
    put(bytes, 0x16c2, &[0x74, 0x04]); // ASM: jz 0x16c8
    put(bytes, 0x16c4, &[0xb0, 0x01]); // ASM: mov al,1
    put(bytes, 0x16c6, &[0xeb, 0x02]); // ASM: jmp 0x16ca
    put(bytes, 0x16c8, &[0xb0, 0x00]); // ASM: mov al,0
    put(bytes, 0x16ca, &[0xc3]); // ASM: ret
    put(bytes, 0x16d0, &[0x48, 0x8d, 0x05, 0xa9, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2280 (BC)
    put(bytes, 0x16d7, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x16da, &[0x48, 0x8d, 0x15, 0x3f, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2220
    put(bytes, 0x16e1, &[0xc3]); // ASM: ret
    put(bytes, 0x16f0, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx (CC)
    put(bytes, 0x16f3, &[0xe8, 0xd8, 0xff, 0xff, 0xff]); // ASM: call 0x16d0 (BC)
    put(bytes, 0x16f8, &[0x48, 0x8d, 0x05, 0xa1, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x22a0
    put(bytes, 0x16ff, &[0x48, 0x89, 0x03]); // ASM: mov [rbx],rax
    put(bytes, 0x1702, &[0x48, 0x8d, 0x15, 0x37, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2240
    put(bytes, 0x1709, &[0xc3]); // ASM: ret
    put(bytes, 0x1710, &[0x48, 0x8d, 0x05, 0x89, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x22a0 (CD)
    put(bytes, 0x1717, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x171a, &[0x48, 0x8d, 0x15, 0x3f, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2260
    put(bytes, 0x1721, &[0xc3]); // ASM: ret
    put(bytes, 0x1730, &[0x48, 0x8d, 0x05, 0x69, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x22a0 (UC)
    put(bytes, 0x1737, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x173a, &[0xc3]); // ASM: ret
    put(bytes, 0x1740, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (DF)
    put(bytes, 0x1743, &[0x48, 0x8d, 0x15, 0x8e, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x22d8
    put(bytes, 0x174a, &[0xc3]); // ASM: ret
    put(bytes, 0x1750, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx (UC2)
    put(bytes, 0x1753, &[0xe8, 0x98, 0xff, 0xff, 0xff]); // ASM: call 0x16f0 (CC)
    put(bytes, 0x1758, &[0x48, 0x8d, 0x05, 0x61, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x22c0
    put(bytes, 0x175f, &[0x48, 0x89, 0x03]); // ASM: mov [rbx],rax
    put(bytes, 0x1762, &[0xc3]); // ASM: ret
    put(bytes, 0x1770, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (VR)
    put(bytes, 0x1773, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x1776, &[0x48, 0x8d, 0x15, 0x93, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2310
    put(bytes, 0x177d, &[0xc3]); // ASM: ret
    put(bytes, 0x1780, &[0xe8, 0x1b, 0x00, 0x00, 0x00]); // ASM: call 0x17a0 (FG) (VR2)
    put(bytes, 0x1785, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x1788, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
    put(bytes, 0x178b, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x178e, &[0xc3]); // ASM: ret
    put(bytes, 0x17a0, &[0x48, 0x8d, 0x05, 0xd9, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2380 (FG)
    put(bytes, 0x17a7, &[0x48, 0x8d, 0x15, 0x92, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2340
    put(bytes, 0x17ae, &[0xc3]); // ASM: ret
    put(bytes, 0x17b0, &[0x48, 0x8b, 0x02]); // ASM: mov rax,[rdx] (PU)
    put(bytes, 0x17b3, &[0x48, 0x89, 0x41, 0x10]); // ASM: mov [rcx+0x10],rax
    put(bytes, 0x17b7, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x17ba, &[0x48, 0x8b, 0x00]); // ASM: mov rax,[rax]
    put(bytes, 0x17bd, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x17c0, &[0x48, 0x8d, 0x15, 0xc9, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2390
    put(bytes, 0x17c7, &[0xc3]); // ASM: ret
    put(bytes, 0x17d0, &[0xe8, 0x2b, 0xfa, 0xff, 0xff]); // ASM: call 0x1200 (UR)
    put(bytes, 0x17d5, &[0xba, 0x05, 0x00, 0x00, 0x00]); // ASM: mov edx,5
    put(bytes, 0x17da, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x17dd, &[0xe8, 0xfe, 0xf9, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x17e2, &[0xc3]); // ASM: ret
    put(bytes, 0x17f0, &[0x8b, 0xc2]); // ASM: mov eax,edx (PK)
    put(bytes, 0x17f2, &[0x48, 0x8d, 0x15, 0xd7, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x23d0
    put(bytes, 0x17f9, &[0xc3]); // ASM: ret
    put(bytes, 0x1800, &[0xe8, 0xcb, 0xfd, 0xff, 0xff]); // ASM: call 0x15d0 (RC)
    put(bytes, 0x1805, &[0xc3]); // ASM: ret
    put(bytes, 0x1810, &[0x48, 0x8d, 0x0d, 0xe9, 0x0b, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x2400 (AS)
    put(bytes, 0x1817, &[0x48, 0x8d, 0x15, 0xf2, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2410
    put(bytes, 0x181e, &[0x41, 0xb8, 0xbf, 0x00, 0x00, 0x00]); // ASM: mov r8d,191
    put(bytes, 0x1824, &[0x4c, 0x8d, 0x0d, 0x15, 0x0c, 0x00, 0x00]); // ASM: lea r9,[rip+..] -> 0x2440
    put(bytes, 0x182b, &[0xff, 0x15, 0x1f, 0x08, 0x00, 0x00]); // ASM: call qword [rip+..] -> 0x2050 (ReportAssertFailure)
    put(bytes, 0x1831, &[0xc3]); // ASM: ret
    put(bytes, 0x1840, &[0x85, 0xc9]); // ASM: test ecx,ecx (AG)
    put(bytes, 0x1842, &[0x75, 0x21]); // ASM: jnz 0x1865
    put(bytes, 0x1844, &[0x48, 0x8d, 0x0d, 0xb5, 0x0b, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x2400
    put(bytes, 0x184b, &[0x48, 0x8d, 0x15, 0xbe, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2410
    put(bytes, 0x1852, &[0x41, 0xb8, 0xbf, 0x00, 0x00, 0x00]); // ASM: mov r8d,191
    put(bytes, 0x1858, &[0x4c, 0x8d, 0x0d, 0x11, 0x0c, 0x00, 0x00]); // ASM: lea r9,[rip+..] -> 0x2470
    put(bytes, 0x185f, &[0xff, 0x15, 0xeb, 0x07, 0x00, 0x00]); // ASM: call qword [rip+..] -> 0x2050 (ReportAssertFailure)
    put(bytes, 0x1865, &[0xc3]); // ASM: ret
    put(bytes, 0x1870, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,7 (DV)
    put(bytes, 0x1875, &[0xc3]); // ASM: ret
    put(bytes, 0x1880, &[0x8b, 0xc1]); // ASM: mov eax,ecx (SC)
    put(bytes, 0x1882, &[0xc1, 0xe8, 0x05]); // ASM: shr eax,5
    put(bytes, 0x1885, &[0x83, 0xd0, 0x00]); // ASM: adc eax,0
    put(bytes, 0x1888, &[0xc3]); // ASM: ret
    put(bytes, 0x1890, &[0x41, 0x8b, 0xc0]); // ASM: mov eax,r8d (RR)
    put(bytes, 0x1893, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x1895, &[0xd1, 0xd8]); // ASM: rcr eax,1
    put(bytes, 0x1897, &[0x0f, 0x43, 0xc2]); // ASM: cmovae eax,edx
    put(bytes, 0x189a, &[0xc3]); // ASM: ret
    put(bytes, 0x18a0, &[0x8b, 0xc1]); // ASM: mov eax,ecx (SD)
    put(bytes, 0x18a2, &[0x0f, 0xa4, 0xd0, 0x08]); // ASM: shld eax,edx,8
    put(bytes, 0x18a6, &[0xc3]); // ASM: ret
    put(bytes, 0x18b0, &[0x0f, 0x01, 0xd0]); // ASM: xgetbv (XG)
    put(bytes, 0x18b3, &[0xc3]); // ASM: ret
    put(bytes, 0x18c0, &[0x8b, 0x01]); // ASM: mov eax,[rcx] (HC)
    put(bytes, 0x18c2, &[0xe8, 0x09, 0x00, 0x00, 0x00]); // ASM: call 0x18d0 (HT)
    put(bytes, 0x18c7, &[0x48, 0x8d, 0x15, 0xf2, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x24c0
    put(bytes, 0x18ce, &[0xc3]); // ASM: ret
    put(bytes, 0x18d0, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (HT)
    put(bytes, 0x18d3, &[0xc3]); // ASM: ret
    put(bytes, 0x18e0, &[0x48, 0x8b, 0x41, 0x10]); // ASM: mov rax,[rcx+0x10] (GT)
    put(bytes, 0x18e4, &[0xc3]); // ASM: ret
    put(bytes, 0x18f0, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx (HC2)
    put(bytes, 0x18f3, &[0xe8, 0xe8, 0xff, 0xff, 0xff]); // ASM: call 0x18e0 (GT)
    put(bytes, 0x18f8, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x18fb, &[0xe8, 0xd0, 0xfd, 0xff, 0xff]); // ASM: call 0x16d0 (BC)
    put(bytes, 0x1900, &[0x48, 0x8b, 0x4b, 0x10]); // ASM: mov rcx,[rbx+0x10]
    put(bytes, 0x1904, &[0xe8, 0xc7, 0xfd, 0xff, 0xff]); // ASM: call 0x16d0 (BC)
    put(bytes, 0x1909, &[0x48, 0x8b, 0x43, 0x10]); // ASM: mov rax,[rbx+0x10]
    put(bytes, 0x190d, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x1910, &[0x48, 0x8b, 0x00]); // ASM: mov rax,[rax]
    put(bytes, 0x1913, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x1916, &[0x48, 0x8d, 0x15, 0xe3, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2500
    put(bytes, 0x191d, &[0xc3]); // ASM: ret
    put(bytes, 0x1920, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx (HC3)
    put(bytes, 0x1923, &[0x48, 0x8d, 0x53, 0x28]); // ASM: lea rdx,[rbx+0x28]
    put(bytes, 0x1927, &[0xe8, 0x84, 0xfe, 0xff, 0xff]); // ASM: call 0x17b0 (PU, Der::Use)
    put(bytes, 0x192c, &[0x48, 0x8b, 0x43, 0x28]); // ASM: mov rax,[rbx+0x28]
    put(bytes, 0x1930, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x1933, &[0x48, 0x8b, 0x00]); // ASM: mov rax,[rax]
    put(bytes, 0x1936, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x1939, &[0x48, 0x8d, 0x15, 0x00, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2540
    put(bytes, 0x1940, &[0xc3]); // ASM: ret
    put(bytes, 0x1950, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (ACC)
    put(bytes, 0x1953, &[0xc3]); // ASM: ret
    put(bytes, 0x1960, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx (HC4)
    put(bytes, 0x1963, &[0x48, 0x8d, 0x4b, 0x28]); // ASM: lea rcx,[rbx+0x28]
    put(bytes, 0x1967, &[0xe8, 0xe4, 0xff, 0xff, 0xff]); // ASM: call 0x1950 (ACC)
    put(bytes, 0x196c, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x196f, &[0x48, 0x8b, 0x00]); // ASM: mov rax,[rax]
    put(bytes, 0x1972, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x1975, &[0x48, 0x8d, 0x15, 0xf4, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2570
    put(bytes, 0x197c, &[0xc3]); // ASM: ret
    put(bytes, 0x1980, &[0x8b, 0x41, 0x04]); // ASM: mov eax,[rcx+4] (AM1)
    put(bytes, 0x1983, &[0x48, 0x8d, 0x15, 0x16, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x25a0
    put(bytes, 0x198a, &[0xc3]); // ASM: ret
    put(bytes, 0x1990, &[0x8b, 0x41, 0x04]); // ASM: mov eax,[rcx+4] (AM2)
    put(bytes, 0x1993, &[0x03, 0xc2]); // ASM: add eax,edx
    put(bytes, 0x1995, &[0x48, 0x8d, 0x15, 0x04, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x25a0
    put(bytes, 0x199c, &[0xc3]); // ASM: ret
    put(bytes, 0x19a0, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (DC2)
    put(bytes, 0x19a3, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x19a5, &[0x75, 0x21]); // ASM: jnz 0x19c8
    put(bytes, 0x19a7, &[0x48, 0x8d, 0x0d, 0x32, 0x0c, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x25e0
    put(bytes, 0x19ae, &[0x48, 0x8d, 0x15, 0x5b, 0x0a, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2410
    put(bytes, 0x19b5, &[0x41, 0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov r8d,7
    put(bytes, 0x19bb, &[0x4c, 0x8d, 0x0d, 0x3e, 0x0c, 0x00, 0x00]); // ASM: lea r9,[rip+..] -> 0x2600
    put(bytes, 0x19c2, &[0xff, 0x15, 0x88, 0x06, 0x00, 0x00]); // ASM: call qword [rip+..] -> 0x2050 (ReportAssertFailure)
    put(bytes, 0x19c8, &[0xc3]); // ASM: ret
    put(bytes, 0x19d0, &[0x8b, 0x42, 0x08]); // ASM: mov eax,[rdx+8] (DP)
    put(bytes, 0x19d3, &[0x89, 0x41, 0x08]); // ASM: mov [rcx+8],eax
    put(bytes, 0x19d6, &[0x48, 0x8d, 0x15, 0x53, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2630
    put(bytes, 0x19dd, &[0xc3]); // ASM: ret
    put(bytes, 0x19e0, &[0xc7, 0x01, 0x00, 0x00, 0x00, 0x00]); // ASM: mov dword [rcx],0 (FM2)
    put(bytes, 0x19e6, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx
    put(bytes, 0x19e9, &[0x48, 0x8d, 0x15, 0x70, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2660
    put(bytes, 0x19f0, &[0xc3]); // ASM: ret
    put(bytes, 0x1a00, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (LP)
    put(bytes, 0x1a04, &[0x48, 0x8d, 0x4c, 0x24, 0x20]); // ASM: lea rcx,[rsp+0x20]
    put(bytes, 0x1a09, &[0xe8, 0xd2, 0xff, 0xff, 0xff]); // ASM: call 0x19e0 (FM2)
    put(bytes, 0x1a0e, &[0x48, 0x8b, 0x4c, 0x24, 0x20]); // ASM: mov rcx,[rsp+0x20]
    put(bytes, 0x1a13, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
    put(bytes, 0x1a16, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x1a19, &[0x48, 0x8d, 0x15, 0x80, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x26a0
    put(bytes, 0x1a20, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x1a24, &[0xc3]); // ASM: ret
    put(bytes, 0x1a30, &[0x8b, 0x41, 0x10]); // ASM: mov eax,[rcx+0x10] (HU)
    put(bytes, 0x1a33, &[0xe8, 0x08, 0x00, 0x00, 0x00]); // ASM: call 0x1a40 (HU2)
    put(bytes, 0x1a38, &[0xc3]); // ASM: ret
    put(bytes, 0x1a40, &[0x8b, 0x41, 0x0c]); // ASM: mov eax,[rcx+0xc] (HU2)
    put(bytes, 0x1a43, &[0xc3]); // ASM: ret
    put(bytes, 0x1a50, &[0x8b, 0x01]); // ASM: mov eax,[rcx] (HC5)
    put(bytes, 0x1a52, &[0xe8, 0xd9, 0xff, 0xff, 0xff]); // ASM: call 0x1a30 (HU)
    put(bytes, 0x1a57, &[0x48, 0x8d, 0x15, 0x82, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x26e0
    put(bytes, 0x1a5e, &[0xc3]); // ASM: ret
    put(bytes, 0x1a60, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx (TC)
    put(
        bytes,
        0x1a63,
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,gs:[0x58]
    put(bytes, 0x1a6c, &[0x8b, 0x0d, 0xae, 0x0c, 0x00, 0x00]); // ASM: mov ecx,[rip+..] -> 0x2720 (_tls_index)
    put(bytes, 0x1a72, &[0x48, 0x8b, 0x04, 0xc8]); // ASM: mov rax,[rax+rcx*8]
    put(bytes, 0x1a76, &[0xbd, 0x10, 0x00, 0x00, 0x00]); // ASM: mov ebp,0x10
    put(bytes, 0x1a7b, &[0x48, 0x89, 0x1c, 0x28]); // ASM: mov [rax+rbp],rbx
    put(bytes, 0x1a7f, &[0x48, 0x8d, 0x15, 0xba, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2740
    put(bytes, 0x1a86, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x1a90,
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,gs:[0x58] (TU)
    put(bytes, 0x1a99, &[0x8b, 0x0d, 0x81, 0x0c, 0x00, 0x00]); // ASM: mov ecx,[rip+..] -> 0x2720
    put(bytes, 0x1a9f, &[0x48, 0x8b, 0x04, 0xc8]); // ASM: mov rax,[rax+rcx*8]
    put(bytes, 0x1aa3, &[0x48, 0x8b, 0x48, 0x10]); // ASM: mov rcx,[rax+0x10]
    put(bytes, 0x1aa7, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
    put(bytes, 0x1aaa, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x1aad, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x1ab0,
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,gs:[0x58] (TG)
    put(bytes, 0x1ab9, &[0x8b, 0x0d, 0x61, 0x0c, 0x00, 0x00]); // ASM: mov ecx,[rip+..] -> 0x2720
    put(bytes, 0x1abf, &[0x48, 0x8b, 0x04, 0xc8]); // ASM: mov rax,[rax+rcx*8]
    put(bytes, 0x1ac3, &[0x48, 0x8b, 0x40, 0x10]); // ASM: mov rax,[rax+0x10]
    put(bytes, 0x1ac7, &[0xc3]); // ASM: ret
    put(bytes, 0x1ad0, &[0x8b, 0x01]); // ASM: mov eax,[rcx] (TU2)
    put(bytes, 0x1ad2, &[0xe8, 0xd9, 0xff, 0xff, 0xff]); // ASM: call 0x1ab0 (TG)
    put(bytes, 0x1ad7, &[0x48, 0x8d, 0x15, 0xa2, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2780
    put(bytes, 0x1ade, &[0xc3]); // ASM: ret
    put(bytes, 0x1ae0, &[0x48, 0x8d, 0x05, 0xc9, 0x0c, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x27b0 (GC)
    put(bytes, 0x1ae7, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x1aea, &[0x48, 0x89, 0x0d, 0xcf, 0x0c, 0x00, 0x00]); // ASM: mov [rip+..],rcx -> 0x27c0
    put(bytes, 0x1af1, &[0x48, 0x8d, 0x15, 0xd0, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x27c8
    put(bytes, 0x1af8, &[0xc3]); // ASM: ret
    put(bytes, 0x1b00, &[0x48, 0x8b, 0x0d, 0xb9, 0x0c, 0x00, 0x00]); // ASM: mov rcx,[rip+..] -> 0x27c0 (GU)
    put(bytes, 0x1b07, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
    put(bytes, 0x1b0a, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x1b0d, &[0xc3]); // ASM: ret
    put(bytes, 0x1b10, &[0x48, 0x8d, 0x05, 0xe9, 0x0c, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2800 (UT)
    put(bytes, 0x1b17, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x1b1a, &[0xc3]); // ASM: ret
    put(bytes, 0x1b20, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1 (S1)
    put(bytes, 0x1b25, &[0xc3]); // ASM: ret
    put(bytes, 0x1b30, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2 (S2)
    put(bytes, 0x1b35, &[0xc3]); // ASM: ret
    put(bytes, 0x1b40, &[0xc3]); // ASM: ret (AK)
    put(bytes, 0x1b50, &[0x48, 0x8d, 0x0d, 0xc9, 0x0c, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> "n == 1" (AH)
    put(bytes, 0x1b57, &[0x48, 0x8d, 0x15, 0xd2, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> "n must be one"
    put(bytes, 0x1b5e, &[0x4c, 0x8d, 0x05, 0xdb, 0x0c, 0x00, 0x00]); // ASM: lea r8,[rip+..] -> "src/ah.cc"
    put(bytes, 0x1b65, &[0x41, 0xb9, 0xc2, 0x01, 0x00, 0x00]); // ASM: mov r9d,0x1c2
    put(bytes, 0x1b6b, &[0xe8, 0xd0, 0xff, 0xff, 0xff]); // ASM: call 0x1b40 (AK)
    put(bytes, 0x1b70, &[0x31, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1b72, &[0xc3]); // ASM: ret
    put(bytes, 0x1b80, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (VU)
    put(bytes, 0x1b83, &[0xff, 0x50, 0x10]); // ASM: call [rax+0x10]
    put(bytes, 0x1b86, &[0xc3]); // ASM: ret
    put(bytes, 0x1b90, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (PA)
    put(bytes, 0x1b93, &[0x48, 0x8d, 0x15, 0xc6, 0x0c, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x2860
    put(bytes, 0x1b9a, &[0xc3]); // ASM: ret
    put(bytes, 0x1ba0, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1b90 (PB, PA)
    put(bytes, 0x1ba5, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x1ba8, &[0x48, 0x8b, 0x00]); // ASM: mov rax,[rax]
    put(bytes, 0x1bab, &[0xff, 0x50, 0x08]); // ASM: call [rax+8]
    put(bytes, 0x1bae, &[0xc3]); // ASM: ret
    put(bytes, 0x1bb0, &[0x48, 0x8d, 0x05, 0x09, 0x0d, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x28c0 (DK)
    put(bytes, 0x1bb7, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x1bba, &[0xc3]); // ASM: ret
    put(bytes, 0x1bc0, &[0x48, 0x8d, 0x05, 0x39, 0x14, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x3000 (DC)
    put(bytes, 0x1bc7, &[0xe8, 0xe4, 0xff, 0xff, 0xff]); // ASM: call 0x1bb0 (DK)
    put(bytes, 0x1bcc, &[0xc3]); // ASM: ret
    put(bytes, 0x1bd0, &[0x48, 0x8d, 0x0d, 0x29, 0x14, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x3000 (DR)
    put(bytes, 0x1bd7, &[0x48, 0x8d, 0x15, 0x02, 0x0d, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> "Ns::Thing"
    put(bytes, 0x1bde, &[0xc3]); // ASM: ret
    put(bytes, 0x1be0, &[0xb8, 0x03, 0x00, 0x00, 0x00]); // ASM: mov eax,3 (S3)
    put(bytes, 0x1be5, &[0xc3]); // ASM: ret
    put(bytes, 0x1bf0, &[0xb8, 0x04, 0x00, 0x00, 0x00]); // ASM: mov eax,4 (S4)
    put(bytes, 0x1bf5, &[0xc3]); // ASM: ret
    put(bytes, 0x1c00, &[0xe8, 0xbb, 0xff, 0xff, 0xff]); // ASM: call 0x1bc0 (GS, DC)
    put(bytes, 0x1c05, &[0x48, 0x89, 0x05, 0xfc, 0x13, 0x00, 0x00]); // ASM: mov [rip+..],rax -> 0x3008
    put(bytes, 0x1c0c, &[0xc3]); // ASM: ret
    put(bytes, 0x1c10, &[0x48, 0x8b, 0x05, 0xf1, 0x13, 0x00, 0x00]); // ASM: mov rax,[rip+..] -> 0x3008 (GG)
    put(bytes, 0x1c17, &[0xc3]); // ASM: ret
    put(bytes, 0x1c20, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1c10 (GV, GG)
    put(bytes, 0x1c25, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x1c28, &[0x48, 0x8b, 0x00]); // ASM: mov rax,[rax]
    put(bytes, 0x1c2b, &[0xff, 0x50, 0x08]); // ASM: call [rax+8]
    put(bytes, 0x1c2e, &[0xc3]); // ASM: ret
    put(bytes, 0x1c30, &[0x53]); // ASM: push rbx (DK3)
    put(bytes, 0x1c31, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx
    put(bytes, 0x1c34, &[0x48, 0x8d, 0x05, 0xd5, 0x0c, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2910
    put(bytes, 0x1c3b, &[0x48, 0x89, 0x03]); // ASM: mov [rbx],rax
    put(bytes, 0x1c3e, &[0x48, 0x89, 0x1d, 0xcb, 0x13, 0x00, 0x00]); // ASM: mov [rip+..],rbx -> 0x3010
    put(bytes, 0x1c45, &[0xe8, 0x76, 0xff, 0xff, 0xff]); // ASM: call 0x1bc0 (DC)
    put(bytes, 0x1c4a, &[0x48, 0x89, 0x43, 0x08]); // ASM: mov [rbx+8],rax
    put(bytes, 0x1c4e, &[0x5b]); // ASM: pop rbx
    put(bytes, 0x1c4f, &[0xc3]); // ASM: ret
    put(bytes, 0x1c50, &[0x48, 0x8b, 0x41, 0x08]); // ASM: mov rax,[rcx+8] (FG)
    put(bytes, 0x1c54, &[0xc3]); // ASM: ret
    put(bytes, 0x1c60, &[0x85, 0xc9]); // ASM: test ecx,ecx (TC)
    put(bytes, 0x1c62, &[0x74, 0x0c]); // ASM: jz 0x1c70
    put(bytes, 0x1c64, &[0x85, 0xd2]); // ASM: test edx,edx
    put(bytes, 0x1c66, &[0x74, 0x08]); // ASM: jz 0x1c70
    put(bytes, 0x1c68, &[0x8b, 0xc1]); // ASM: mov eax,ecx
    put(bytes, 0x1c6a, &[0xeb, 0x07]); // ASM: jmp 0x1c73
    put(bytes, 0x1c70, &[0x83, 0xc8, 0xff]); // ASM: or eax,-1
    put(bytes, 0x1c73, &[0xc3]); // ASM: ret
    put(bytes, 0x1c80, &[0x31, 0xc0]); // ASM: xor eax,eax (LP)
    put(bytes, 0x1c82, &[0x80, 0x3c, 0x01, 0x00]); // ASM: cmp byte [rcx+rax],0
    put(bytes, 0x1c86, &[0x74, 0x15]); // ASM: jz 0x1c9d
    put(bytes, 0x1c88, &[0x80, 0x3c, 0x01, 0x20]); // ASM: cmp byte [rcx+rax],0x20
    put(bytes, 0x1c8c, &[0x74, 0x16]); // ASM: jz 0x1ca4
    put(bytes, 0x1c8e, &[0x48, 0xff, 0xc0]); // ASM: inc rax
    put(bytes, 0x1c91, &[0x48, 0x83, 0xf8, 0x08]); // ASM: cmp rax,8
    put(bytes, 0x1c95, &[0x7c, 0xeb]); // ASM: jl 0x1c82
    put(bytes, 0x1c97, &[0x48, 0x83, 0xc8, 0xff]); // ASM: or rax,-1
    put(bytes, 0x1c9b, &[0xeb, 0x0c]); // ASM: jmp 0x1ca9
    put(bytes, 0x1c9d, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x1ca2, &[0xeb, 0x05]); // ASM: jmp 0x1ca9
    put(bytes, 0x1ca4, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x1ca9, &[0xc3]); // ASM: ret
    put(bytes, 0x1cb0, &[0x31, 0xc0]); // ASM: xor eax,eax (LP2)
    put(bytes, 0x1cb2, &[0x4c, 0x8b, 0xc1]); // ASM: mov r8,rcx
    put(bytes, 0x1cb5, &[0x41, 0x80, 0x38, 0x40]); // ASM: cmp byte [r8],0x40
    put(bytes, 0x1cb9, &[0x77, 0x0d]); // ASM: ja 0x1cc8
    put(bytes, 0x1cbb, &[0x41, 0x80, 0x38, 0x00]); // ASM: cmp byte [r8],0
    put(bytes, 0x1cbf, &[0x75, 0x1d]); // ASM: jne 0x1cde
    put(bytes, 0x1cc1, &[0xb8, 0x10, 0x00, 0x00, 0x00]); // ASM: mov eax,16
    put(bytes, 0x1cc6, &[0xeb, 0x11]); // ASM: jmp 0x1cd9
    put(bytes, 0x1cc8, &[0x41, 0x80, 0x38, 0x41]); // ASM: cmp byte [r8],0x41
    put(bytes, 0x1ccc, &[0x74, 0x1b]); // ASM: je 0x1ce9
    put(bytes, 0x1cce, &[0x41, 0x80, 0x38, 0x42]); // ASM: cmp byte [r8],0x42
    put(bytes, 0x1cd2, &[0x74, 0x11]); // ASM: je 0x1ce5
    put(bytes, 0x1cd4, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x1cd9, &[0x4c, 0x03, 0xc0]); // ASM: add r8,rax
    put(bytes, 0x1cdc, &[0xeb, 0xd7]); // ASM: jmp 0x1cb5
    put(bytes, 0x1cde, &[0xb8, 0x03, 0x00, 0x00, 0x00]); // ASM: mov eax,3
    put(bytes, 0x1ce3, &[0xeb, 0x07]); // ASM: jmp 0x1cec
    put(bytes, 0x1ce5, &[0x31, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1ce7, &[0xeb, 0x03]); // ASM: jmp 0x1cec
    put(bytes, 0x1ce9, &[0x49, 0x8b, 0xc0]); // ASM: mov rax,r8
    put(bytes, 0x1cec, &[0xc3]); // ASM: ret
    put(bytes, 0x1cf0, &[0x31, 0xc0]); // ASM: xor eax,eax (LP3)
    put(bytes, 0x1cf2, &[0x85, 0xd2]); // ASM: test edx,edx
    put(bytes, 0x1cf4, &[0x74, 0x25]); // ASM: jz 0x1d1b
    put(bytes, 0x1cf6, &[0x80, 0x3c, 0x01, 0x40]); // ASM: cmp byte [rcx+rax],0x40
    put(bytes, 0x1cfa, &[0x77, 0x0f]); // ASM: ja 0x1d0b
    put(bytes, 0x1cfc, &[0x80, 0x3c, 0x01, 0x00]); // ASM: cmp byte [rcx+rax],0
    put(bytes, 0x1d00, &[0x74, 0x1e]); // ASM: jz 0x1d20
    put(bytes, 0x1d02, &[0xba, 0x01, 0x00, 0x00, 0x00]); // ASM: mov edx,1
    put(bytes, 0x1d07, &[0xeb, 0x0d]); // ASM: jmp 0x1d16
    put(bytes, 0x1d0b, &[0x48, 0x83, 0xf8, 0x08]); // ASM: cmp rax,8
    put(bytes, 0x1d0f, &[0x7d, 0x0a]); // ASM: jge 0x1d1b
    put(bytes, 0x1d11, &[0xba, 0x02, 0x00, 0x00, 0x00]); // ASM: mov edx,2
    put(bytes, 0x1d16, &[0x48, 0x03, 0xc2]); // ASM: add rax,rdx
    put(bytes, 0x1d19, &[0xeb, 0xdb]); // ASM: jmp 0x1cf6
    put(bytes, 0x1d1b, &[0x48, 0x83, 0xc8, 0xff]); // ASM: or rax,-1
    put(bytes, 0x1d1f, &[0xc3]); // ASM: ret
    put(bytes, 0x1d20, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx
    put(bytes, 0x1d23, &[0xeb, 0xfa]); // ASM: jmp 0x1d1f
    put(bytes, 0x1d30, &[0x53, 0x55, 0x56, 0x57]); // ASM: push rbx; push rbp; push rsi; push rdi (TE)
    put(
        bytes,
        0x1d34,
        &[0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57],
    ); // ASM: push r12; push r13; push r14; push r15
    put(bytes, 0x1d3c, &[0x48, 0x83, 0xec, 0x20]); // ASM: sub rsp,0x20
    put(bytes, 0x1d40, &[0x31, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1d42, &[0x85, 0xd2]); // ASM: test edx,edx
    put(bytes, 0x1d44, &[0x74, 0x25]); // ASM: jz 0x1d6b
    put(bytes, 0x1d46, &[0x80, 0x3c, 0x01, 0x40]); // ASM: cmp byte [rcx+rax],0x40
    put(bytes, 0x1d4a, &[0x77, 0x0f]); // ASM: ja 0x1d5b
    put(bytes, 0x1d4c, &[0x80, 0x3c, 0x01, 0x00]); // ASM: cmp byte [rcx+rax],0
    put(bytes, 0x1d50, &[0x74, 0x2e]); // ASM: jz 0x1d80
    put(bytes, 0x1d52, &[0xba, 0x01, 0x00, 0x00, 0x00]); // ASM: mov edx,1
    put(bytes, 0x1d57, &[0xeb, 0x0d]); // ASM: jmp 0x1d66
    put(bytes, 0x1d5b, &[0x48, 0x83, 0xf8, 0x08]); // ASM: cmp rax,8
    put(bytes, 0x1d5f, &[0x7d, 0x0a]); // ASM: jge 0x1d6b
    put(bytes, 0x1d61, &[0xba, 0x02, 0x00, 0x00, 0x00]); // ASM: mov edx,2
    put(bytes, 0x1d66, &[0x48, 0x03, 0xc2]); // ASM: add rax,rdx
    put(bytes, 0x1d69, &[0xeb, 0xdb]); // ASM: jmp 0x1d46
    put(bytes, 0x1d6b, &[0x48, 0x83, 0xc8, 0xff]); // ASM: or rax,-1
    put(bytes, 0x1d6f, &[0x48, 0x83, 0xc4, 0x20]); // ASM: add rsp,0x20
    put(
        bytes,
        0x1d73,
        &[0x41, 0x5f, 0x41, 0x5e, 0x41, 0x5d, 0x41, 0x5c],
    ); // ASM: pop r15; pop r14; pop r13; pop r12
    put(bytes, 0x1d7b, &[0x5f, 0x5e, 0x5d, 0x5b]); // ASM: pop rdi; pop rsi; pop rbp; pop rbx
    put(bytes, 0x1d7f, &[0xc3]); // ASM: ret
    put(bytes, 0x1d80, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx
    put(bytes, 0x1d83, &[0xeb, 0xea]); // ASM: jmp 0x1d6f
    put(bytes, 0x1d90, &[0x31, 0xc0]); // ASM: xor eax,eax (TL)
    put(bytes, 0x1d92, &[0x85, 0xd2]); // ASM: test edx,edx
    put(bytes, 0x1d94, &[0x74, 0x23]); // ASM: jz 0x1db9
    put(bytes, 0x1d96, &[0x80, 0x3c, 0x01, 0x40]); // ASM: cmp byte [rcx+rax],0x40
    put(bytes, 0x1d9a, &[0x77, 0x0d]); // ASM: ja 0x1da9
    put(bytes, 0x1d9c, &[0x80, 0x3c, 0x01, 0x00]); // ASM: cmp byte [rcx+rax],0
    put(bytes, 0x1da0, &[0x74, 0x22]); // ASM: jz 0x1dc4
    put(bytes, 0x1da2, &[0xba, 0x01, 0x00, 0x00, 0x00]); // ASM: mov edx,1
    put(bytes, 0x1da7, &[0xeb, 0x0b]); // ASM: jmp 0x1db4
    put(bytes, 0x1da9, &[0x48, 0x83, 0xf8, 0x08]); // ASM: cmp rax,8
    put(bytes, 0x1dad, &[0x7d, 0x0a]); // ASM: jge 0x1db9
    put(bytes, 0x1daf, &[0xba, 0x02, 0x00, 0x00, 0x00]); // ASM: mov edx,2
    put(bytes, 0x1db4, &[0x48, 0x03, 0xc2]); // ASM: add rax,rdx
    put(bytes, 0x1db7, &[0xeb, 0xdd]); // ASM: jmp 0x1d96
    put(bytes, 0x1db9, &[0xb9, 0x00, 0x00, 0x00, 0x00]); // ASM: mov ecx,0
    put(bytes, 0x1dbe, &[0xe8, 0x1d, 0xf4, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1dc3, &[0xc3]); // ASM: ret
    put(bytes, 0x1dc4, &[0xb9, 0x01, 0x00, 0x00, 0x00]); // ASM: mov ecx,1
    put(bytes, 0x1dc9, &[0xeb, 0xf3]); // ASM: jmp 0x1dbe
    put(bytes, 0x1dd0, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1 (BF0)
    put(bytes, 0x1dd5, &[0xc3]); // ASM: ret
    put(bytes, 0x1de0, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2 (BF1)
    put(bytes, 0x1de5, &[0xc3]); // ASM: ret
    put(bytes, 0x1df0, &[0xb8, 0x03, 0x00, 0x00, 0x00]); // ASM: mov eax,3 (DF1)
    put(bytes, 0x1df5, &[0xc3]); // ASM: ret
    put(bytes, 0x1e00, &[0x48, 0x8d, 0x05, 0x69, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2970 (BC)
    put(bytes, 0x1e07, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x1e0a, &[0xc3]); // ASM: ret
    put(bytes, 0x1e10, &[0x53]); // ASM: push rbx (DC2)
    put(bytes, 0x1e11, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx
    put(bytes, 0x1e14, &[0xe8, 0xe7, 0xff, 0xff, 0xff]); // ASM: call 0x1e00 (BC)
    put(bytes, 0x1e19, &[0x48, 0x8d, 0x05, 0x68, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2988
    put(bytes, 0x1e20, &[0x48, 0x89, 0x03]); // ASM: mov [rbx],rax
    put(bytes, 0x1e23, &[0x5b]); // ASM: pop rbx
    put(bytes, 0x1e24, &[0xc3]); // ASM: ret
    put(bytes, 0x1e30, &[0xe8, 0xab, 0xff, 0xff, 0xff]); // ASM: call 0x1de0 (CB, BF1)
    put(bytes, 0x1e35, &[0x48, 0x89, 0x02]); // ASM: mov [rdx],rax
    put(bytes, 0x1e38, &[0xc3]); // ASM: ret
    put(bytes, 0x1e70, &[0x85, 0xd2]); // ASM: test edx,edx (JT)
    put(bytes, 0x1e72, &[0x75, 0x10]); // ASM: jnz 0x1e84
    put(bytes, 0x1e74, &[0xe8, 0x67, 0xf3, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1e79, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x1e7b, &[0x74, 0x26]); // ASM: jz 0x1ea3
    put(bytes, 0x1e7d, &[0xb9, 0x01, 0x00, 0x00, 0x00]); // ASM: mov ecx,1
    put(bytes, 0x1e82, &[0xeb, 0x13]); // ASM: jmp 0x1e97
    put(bytes, 0x1e84, &[0x83, 0xfa, 0x01]); // ASM: cmp edx,1
    put(bytes, 0x1e87, &[0x75, 0x1a]); // ASM: jnz 0x1ea3
    put(bytes, 0x1e89, &[0xe8, 0x52, 0xf3, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1e8e, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x1e90, &[0x74, 0x11]); // ASM: jz 0x1ea3
    put(bytes, 0x1e92, &[0xb9, 0x02, 0x00, 0x00, 0x00]); // ASM: mov ecx,2
    put(bytes, 0x1e97, &[0xe8, 0x44, 0xf3, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1e9c, &[0x8b, 0xc8]); // ASM: mov ecx,eax
    put(bytes, 0x1e9e, &[0xe8, 0x3d, 0xf3, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1ea3, &[0xc3]); // ASM: ret
    put(bytes, 0x1ee0, &[0x31, 0xc0]); // ASM: xor eax,eax (RL)
    put(bytes, 0x1ee2, &[0xeb, 0x08]); // ASM: jmp 0x1eec
    put(bytes, 0x1ee4, &[0x48, 0xff, 0xc0]); // ASM: inc rax
    put(bytes, 0x1ee7, &[0xe8, 0xf4, 0xf2, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1eec, &[0x48, 0x83, 0xf8, 0x08]); // ASM: cmp rax,8
    put(bytes, 0x1ef0, &[0x7c, 0xf2]); // ASM: jl 0x1ee4
    put(bytes, 0x1ef2, &[0xc3]); // ASM: ret
    put(bytes, 0x1e40, &[0x48, 0x8d, 0x0d, 0xf9, 0x11, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x3040 (DR2)
    put(bytes, 0x1e47, &[0x48, 0x8d, 0x15, 0x62, 0x0b, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> "Ns::T2"
    put(bytes, 0x1e4e, &[0xc3]); // ASM: ret
    put(bytes, 0x1eb0, &[0x48, 0x8d, 0x0d, 0x89, 0x11, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x3040 (DI)
    put(bytes, 0x1eb7, &[0x48, 0x8d, 0x15, 0xf2, 0x0a, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> "Ns::T2"
    put(bytes, 0x1ebe, &[0x48, 0x8d, 0x05, 0x3b, 0x11, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x3000
    put(bytes, 0x1ec5, &[0xe8, 0x76, 0xff, 0xff, 0xff]); // ASM: call 0x1e40 (DR2)
    put(bytes, 0x1eca, &[0xc3]); // ASM: ret
    put(bytes, 0x1e50, &[0x48, 0x8d, 0x05, 0xa9, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2a00 (TT)
    put(bytes, 0x1e57, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x1e5a, &[0x48, 0x8d, 0x05, 0xbf, 0x0b, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2a20
    put(bytes, 0x1e61, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x1e64, &[0xc3]); // ASM: ret
    put(bytes, 0x1290, &[0x48, 0x8d, 0x0d, 0xe9, 0x1d, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x3080 (DI3)
    put(bytes, 0x1297, &[0x48, 0x8d, 0x15, 0xaa, 0x17, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> "Ns::T3"
    put(bytes, 0x129e, &[0x48, 0x8d, 0x05, 0x5b, 0x1d, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x3000
    put(bytes, 0x12a5, &[0xe8, 0x36, 0xff, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x12aa, &[0xc3]); // ASM: ret
    put(bytes, 0x1160, &[0x48, 0x8d, 0x05, 0x99, 0x18, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2a00 (TT2)
    put(bytes, 0x1167, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x116a, &[0x48, 0x8d, 0x05, 0xef, 0x18, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2a60
    put(bytes, 0x1171, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x1174, &[0xc3]); // ASM: ret
    put(bytes, 0x11a0, &[0x48, 0x8d, 0x0d, 0x19, 0x1f, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x30c0 (DI4)
    put(bytes, 0x11a7, &[0x48, 0x8d, 0x15, 0xd2, 0x18, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> "Ns::T4"
    put(bytes, 0x11ae, &[0x48, 0x8d, 0x05, 0x8b, 0x1e, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x3040
    put(bytes, 0x11b5, &[0xe8, 0x26, 0x00, 0x00, 0x00]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x11ba, &[0xc3]); // ASM: ret
    put(bytes, 0x12e0, &[0x48, 0x8d, 0x0d, 0xd9, 0x1d, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x30c0 (DR4)
    put(bytes, 0x12e7, &[0x48, 0x8d, 0x15, 0x92, 0x17, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> "Ns::T4"
    put(bytes, 0x12ee, &[0xc3]); // ASM: ret
    put(bytes, 0x1ed0, &[0x48, 0x8d, 0x05, 0xe9, 0x11, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x30c0 (CR)
    put(bytes, 0x1ed7, &[0xe8, 0x84, 0xf2, 0xff, 0xff]); // ASM: call 0x1160 (TT2)
    put(bytes, 0x1edc, &[0xc3]); // ASM: ret
    put(bytes, 0x1050, &[0x48, 0x8d, 0x05, 0xe9, 0x1f, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x3040 (DC3)
    put(bytes, 0x1057, &[0xe8, 0x54, 0x0b, 0x00, 0x00]); // ASM: call 0x1bb0 (DK)
    put(bytes, 0x105c, &[0xc3]); // ASM: ret
    put(bytes, 0x10e1, &[0x48, 0x8d, 0x05, 0x18, 0x19, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2a00 (TT3)
    put(bytes, 0x10e8, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x10eb, &[0x48, 0x8d, 0x05, 0x2e, 0x19, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2a20
    put(bytes, 0x10f2, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x10f5, &[0x48, 0x8d, 0x05, 0xb4, 0x19, 0x00, 0x00]); // ASM: lea rax,[rip+..] -> 0x2ab0
    put(bytes, 0x10fc, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x10ff, &[0xc3]); // ASM: ret
    put(bytes, 0x1118, &[0x48, 0x8d, 0x15, 0xf1, 0x19, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> "Der::Pass" sig (TP)
    put(bytes, 0x111f, &[0x48, 0x8d, 0x49, 0x28]); // ASM: lea rcx,[rcx+0x28]
    put(bytes, 0x1123, &[0xe8, 0xc8, 0x01, 0x00, 0x00]); // ASM: call 0x12f0 (UP)
    put(bytes, 0x1128, &[0xc3]); // ASM: ret
    put(bytes, 0x12f0, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (UP)
    put(bytes, 0x12f3, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x12f6, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
    put(bytes, 0x12f9, &[0xff, 0x50, 0x08]); // ASM: call [rax+8]
    put(bytes, 0x12fc, &[0xc3]); // ASM: ret
    put(bytes, 0x4000, &[0x85, 0xc9]); // ASM: test ecx,ecx (GJ)
    put(bytes, 0x4002, &[0x74, 0x07]); // ASM: jz 0x400b
    put(bytes, 0x4004, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x4009, &[0xeb, 0x18]); // ASM: jmp 0x4023
    put(bytes, 0x400b, &[0x85, 0xd2]); // ASM: test edx,edx
    put(bytes, 0x400d, &[0x74, 0x12]); // ASM: jz 0x4021
    put(bytes, 0x400f, &[0xe8, 0xcc, 0xd1, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4014, &[0x84, 0xc0]); // ASM: test al,al
    put(bytes, 0x4016, &[0x74, 0x09]); // ASM: je 0x4021
    put(bytes, 0x4018, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x401d, &[0xeb, 0x04]); // ASM: jmp 0x4023
    put(bytes, 0x4021, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4023, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x4028, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x402b, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x402e, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4031, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4034, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4037, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x403a, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x403d, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4040, &[0xc3]); // ASM: ret
    put(bytes, 0x4041, &[0x48, 0x3b, 0x0d, 0xc0, 0xef, 0xff, 0xff]); // ASM: cmp rcx,[rip+..] -> 0x3008 (CK)
    put(bytes, 0x4048, &[0x75, 0x01]); // ASM: jne 0x404b
    put(bytes, 0x404a, &[0xc3]); // ASM: ret
    put(bytes, 0x404b, &[0xe9, 0x90, 0xd1, 0xff, 0xff]); // ASM: jmp 0x11e0 (Q)
    put(bytes, 0x4050, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,7 (CC)
    put(bytes, 0x4055, &[0x48, 0x8b, 0x0d, 0xac, 0xef, 0xff, 0xff]); // ASM: mov rcx,[rip+..] -> 0x3008
    put(bytes, 0x405c, &[0xe8, 0xe0, 0xff, 0xff, 0xff]); // ASM: call 0x4041 (CK)
    put(bytes, 0x4061, &[0xc3]); // ASM: ret
    put(bytes, 0x4090, &[0x83, 0xf9, 0x09]); // ASM: cmp ecx,9 (LD3)
    put(bytes, 0x4093, &[0x74, 0x40]); // ASM: je 0x40d5
    put(bytes, 0x4095, &[0x83, 0xf9, 0x01]); // ASM: cmp ecx,1
    put(bytes, 0x4098, &[0x75, 0x07]); // ASM: jne 0x40a1
    put(bytes, 0x409a, &[0xba, 0x01, 0x00, 0x00, 0x00]); // ASM: mov edx,1
    put(bytes, 0x409f, &[0xeb, 0x16]); // ASM: jmp 0x40b7
    put(bytes, 0x40a1, &[0x83, 0xf9, 0x02]); // ASM: cmp ecx,2
    put(bytes, 0x40a4, &[0x75, 0x07]); // ASM: jne 0x40ad
    put(bytes, 0x40a6, &[0xba, 0x02, 0x00, 0x00, 0x00]); // ASM: mov edx,2
    put(bytes, 0x40ab, &[0xeb, 0x0a]); // ASM: jmp 0x40b7
    put(bytes, 0x40ad, &[0x83, 0xf9, 0x03]); // ASM: cmp ecx,3
    put(bytes, 0x40b0, &[0x75, 0x23]); // ASM: jne 0x40d5
    put(bytes, 0x40b2, &[0xba, 0x03, 0x00, 0x00, 0x00]); // ASM: mov edx,3
    put(bytes, 0x40b7, &[0xe8, 0x24, 0xd1, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x40bc, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40bf, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40c2, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40c5, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40c8, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40cb, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40ce, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40d1, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40d4, &[0xc3]); // ASM: ret
    put(bytes, 0x40d5, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x40da, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40dd, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40e0, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40e3, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40e6, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40e9, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40ec, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40ef, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x40f2, &[0xc3]); // ASM: ret
    put(bytes, 0x40f4, &[0xe8, 0x67, 0xd5, 0xff, 0xff]); // ASM: call 0x1660 (IG, CL2)
    put(bytes, 0x40f9, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x40fb, &[0xc3]); // ASM: ret
    put(bytes, 0x4100, &[0x53]); // ASM: push rbx (BR)
    put(bytes, 0x4101, &[0x8b, 0xd9]); // ASM: mov ebx,ecx
    put(bytes, 0x4103, &[0x48, 0x8d, 0x15, 0x46, 0xea, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> "Ns::Flag" sig
    put(bytes, 0x410a, &[0x33, 0xc9]); // ASM: xor ecx,ecx
    put(bytes, 0x410c, &[0xe8, 0xcf, 0xd0, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4111, &[0x8a, 0xc3]); // ASM: mov al,bl
    put(bytes, 0x4113, &[0x5b]); // ASM: pop rbx
    put(bytes, 0x4114, &[0xc3]); // ASM: ret
    put(bytes, 0x4120, &[0xe8, 0xdb, 0xff, 0xff, 0xff]); // ASM: call 0x4100 (IG2, BR)
    put(bytes, 0x4125, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4127, &[0xc3]); // ASM: ret
    put(bytes, 0x4130, &[0x53]); // ASM: push rbx (BR2)
    put(bytes, 0x4131, &[0x8b, 0xd9]); // ASM: mov ebx,ecx
    put(bytes, 0x4133, &[0x85, 0xc9]); // ASM: test ecx,ecx
    put(bytes, 0x4135, &[0x74, 0x05]); // ASM: jz 0x413c
    put(bytes, 0x4137, &[0xbb, 0x01, 0x00, 0x00, 0x00]); // ASM: mov ebx,1
    put(bytes, 0x413c, &[0x48, 0x8d, 0x15, 0x3d, 0xea, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> "Ns::Flag2" sig
    put(bytes, 0x4143, &[0x33, 0xc9]); // ASM: xor ecx,ecx
    put(bytes, 0x4145, &[0xe8, 0x96, 0xd0, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x414a, &[0x8a, 0xc3]); // ASM: mov al,bl
    put(bytes, 0x414c, &[0x5b]); // ASM: pop rbx
    put(bytes, 0x414d, &[0xc3]); // ASM: ret
    put(bytes, 0x4150, &[0xe8, 0xdb, 0xff, 0xff, 0xff]); // ASM: call 0x4130 (IG3, BR2)
    put(bytes, 0x4155, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4157, &[0xc3]); // ASM: ret
    put(bytes, 0x4160, &[0x48, 0x8d, 0x15, 0x39, 0xea, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> "%d" (SS)
    put(bytes, 0x4167, &[0x33, 0xc9]); // ASM: xor ecx,ecx
    put(bytes, 0x4169, &[0xe8, 0x72, 0xd0, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x416e, &[0xc3]); // ASM: ret
    put(bytes, 0x4170, &[0x48, 0x8d, 0x15, 0xf1, 0xe7, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> L"AES" (WL)
    put(bytes, 0x4177, &[0x33, 0xc9]); // ASM: xor ecx,ecx
    put(bytes, 0x4179, &[0xe8, 0x62, 0xd0, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x417e, &[0xc3]); // ASM: ret
    put(bytes, 0x4180, &[0x85, 0xc9]); // ASM: test ecx,ecx (GC)
    put(bytes, 0x4182, &[0x74, 0x09]); // ASM: jz 0x418d
    put(bytes, 0x4184, &[0xe8, 0x57, 0xd0, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4189, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x418b, &[0x74, 0x1b]); // ASM: jz 0x41a8
    put(bytes, 0x418d, &[0x89, 0x4a, 0x00]); // ASM: mov [rdx+0x0],ecx
    put(bytes, 0x4190, &[0x89, 0x4a, 0x04]); // ASM: mov [rdx+0x4],ecx
    put(bytes, 0x4193, &[0x89, 0x4a, 0x08]); // ASM: mov [rdx+0x8],ecx
    put(bytes, 0x4196, &[0x89, 0x4a, 0x0c]); // ASM: mov [rdx+0xc],ecx
    put(bytes, 0x4199, &[0x89, 0x4a, 0x10]); // ASM: mov [rdx+0x10],ecx
    put(bytes, 0x419c, &[0x89, 0x4a, 0x14]); // ASM: mov [rdx+0x14],ecx
    put(bytes, 0x419f, &[0x89, 0x4a, 0x18]); // ASM: mov [rdx+0x18],ecx
    put(bytes, 0x41a2, &[0x89, 0x4a, 0x1c]); // ASM: mov [rdx+0x1c],ecx
    put(bytes, 0x41a5, &[0x89, 0x4a, 0x20]); // ASM: mov [rdx+0x20],ecx
    put(bytes, 0x41a8, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x41ad, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x41b0, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x41b3, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x41b6, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x41b9, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x41bc, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x41bf, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x41c2, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x41c5, &[0xc3]); // ASM: ret
    put(bytes, 0x41d0, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx (SH)
    put(bytes, 0x41d3, &[0x48, 0x0f, 0xa5, 0xd0]); // ASM: shld rax,rdx,cl
    put(bytes, 0x41d7, &[0xc3]); // ASM: ret
    put(bytes, 0x41e0, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx (SH2)
    put(bytes, 0x41e3, &[0x48, 0x0f, 0xad, 0xd0]); // ASM: shrd rax,rdx,cl
    put(bytes, 0x41e7, &[0xc3]); // ASM: ret
    put(bytes, 0x4200, &[0x8a, 0xc1]); // ASM: mov al,cl (ML8)
    put(bytes, 0x4202, &[0xf6, 0xe2]); // ASM: mul dl
    put(bytes, 0x4204, &[0x0f, 0xb7, 0xc0]); // ASM: movzx eax,ax
    put(bytes, 0x4207, &[0xc3]); // ASM: ret
    put(bytes, 0x4210, &[0x66, 0x8b, 0xc1]); // ASM: mov ax,cx (DV8)
    put(bytes, 0x4213, &[0xf6, 0xf2]); // ASM: div dl
    put(bytes, 0x4215, &[0x0f, 0xb6, 0xc4]); // ASM: movzx eax,ah
    put(bytes, 0x4218, &[0xc3]); // ASM: ret
    put(bytes, 0x4220, &[0x48, 0x8b, 0x05, 0x69, 0xee, 0xff, 0xff]); // ASM: mov rax,[rip+..] -> 0x3090
    put(bytes, 0x4227, &[0x48, 0x85, 0xc0]); // ASM: test rax,rax
    put(bytes, 0x422a, &[0x74, 0x05]); // ASM: jz +5
    put(bytes, 0x422c, &[0xe8, 0xaf, 0xcf, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4231, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4233, &[0xc3]); // ASM: ret
    put(bytes, 0x4240, &[0x48, 0x8b, 0x05, 0x51, 0xee, 0xff, 0xff]); // ASM: mov rax,[rip+..] -> 0x3098
    put(bytes, 0x4247, &[0x48, 0x85, 0xc0]); // ASM: test rax,rax
    put(bytes, 0x424a, &[0x74, 0x05]); // ASM: jz +5
    put(bytes, 0x424c, &[0xe8, 0x8f, 0xcf, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4251, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4253, &[0xc3]); // ASM: ret
    put(bytes, 0x4260, &[0x48, 0x8b, 0x05, 0x39, 0xee, 0xff, 0xff]); // ASM: mov rax,[rip+..] -> 0x30a0
    put(bytes, 0x4267, &[0x48, 0x85, 0xc0]); // ASM: test rax,rax
    put(bytes, 0x426a, &[0x74, 0x05]); // ASM: jz +5
    put(bytes, 0x426c, &[0xe8, 0x6f, 0xcf, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4271, &[0xb0, 0x01]); // ASM: mov eax,1
    put(bytes, 0x4273, &[0xc3]); // ASM: ret
    put(bytes, 0x4300, &[0x80, 0x79, 0x00, 0x00]); // ASM: cmp byte [rcx+0x0],0 (DEEP)
    put(bytes, 0x4304, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4306, &[0xb8, 0x00, 0x00, 0x00, 0x00]); // ASM: mov eax,0x0
    put(bytes, 0x430b, &[0xe9, 0x75, 0x04, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4310, &[0x80, 0x79, 0x01, 0x00]); // ASM: cmp byte [rcx+0x1],0
    put(bytes, 0x4314, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4316, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,0x1
    put(bytes, 0x431b, &[0xe9, 0x65, 0x04, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4320, &[0x80, 0x79, 0x02, 0x00]); // ASM: cmp byte [rcx+0x2],0
    put(bytes, 0x4324, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4326, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,0x2
    put(bytes, 0x432b, &[0xe9, 0x55, 0x04, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4330, &[0x80, 0x79, 0x03, 0x00]); // ASM: cmp byte [rcx+0x3],0
    put(bytes, 0x4334, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4336, &[0xb8, 0x03, 0x00, 0x00, 0x00]); // ASM: mov eax,0x3
    put(bytes, 0x433b, &[0xe9, 0x45, 0x04, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4340, &[0x80, 0x79, 0x04, 0x00]); // ASM: cmp byte [rcx+0x4],0
    put(bytes, 0x4344, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4346, &[0xb8, 0x04, 0x00, 0x00, 0x00]); // ASM: mov eax,0x4
    put(bytes, 0x434b, &[0xe9, 0x35, 0x04, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4350, &[0x80, 0x79, 0x05, 0x00]); // ASM: cmp byte [rcx+0x5],0
    put(bytes, 0x4354, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4356, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,0x5
    put(bytes, 0x435b, &[0xe9, 0x25, 0x04, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4360, &[0x80, 0x79, 0x06, 0x00]); // ASM: cmp byte [rcx+0x6],0
    put(bytes, 0x4364, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4366, &[0xb8, 0x06, 0x00, 0x00, 0x00]); // ASM: mov eax,0x6
    put(bytes, 0x436b, &[0xe9, 0x15, 0x04, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4370, &[0x80, 0x79, 0x07, 0x00]); // ASM: cmp byte [rcx+0x7],0
    put(bytes, 0x4374, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4376, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,0x7
    put(bytes, 0x437b, &[0xe9, 0x05, 0x04, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4380, &[0x80, 0x79, 0x08, 0x00]); // ASM: cmp byte [rcx+0x8],0
    put(bytes, 0x4384, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4386, &[0xb8, 0x08, 0x00, 0x00, 0x00]); // ASM: mov eax,0x8
    put(bytes, 0x438b, &[0xe9, 0xf5, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4390, &[0x80, 0x79, 0x09, 0x00]); // ASM: cmp byte [rcx+0x9],0
    put(bytes, 0x4394, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4396, &[0xb8, 0x09, 0x00, 0x00, 0x00]); // ASM: mov eax,0x9
    put(bytes, 0x439b, &[0xe9, 0xe5, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x43a0, &[0x80, 0x79, 0x0a, 0x00]); // ASM: cmp byte [rcx+0xa],0
    put(bytes, 0x43a4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x43a6, &[0xb8, 0x0a, 0x00, 0x00, 0x00]); // ASM: mov eax,0xa
    put(bytes, 0x43ab, &[0xe9, 0xd5, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x43b0, &[0x80, 0x79, 0x0b, 0x00]); // ASM: cmp byte [rcx+0xb],0
    put(bytes, 0x43b4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x43b6, &[0xb8, 0x0b, 0x00, 0x00, 0x00]); // ASM: mov eax,0xb
    put(bytes, 0x43bb, &[0xe9, 0xc5, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x43c0, &[0x80, 0x79, 0x0c, 0x00]); // ASM: cmp byte [rcx+0xc],0
    put(bytes, 0x43c4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x43c6, &[0xb8, 0x0c, 0x00, 0x00, 0x00]); // ASM: mov eax,0xc
    put(bytes, 0x43cb, &[0xe9, 0xb5, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x43d0, &[0x80, 0x79, 0x0d, 0x00]); // ASM: cmp byte [rcx+0xd],0
    put(bytes, 0x43d4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x43d6, &[0xb8, 0x0d, 0x00, 0x00, 0x00]); // ASM: mov eax,0xd
    put(bytes, 0x43db, &[0xe9, 0xa5, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x43e0, &[0x80, 0x79, 0x0e, 0x00]); // ASM: cmp byte [rcx+0xe],0
    put(bytes, 0x43e4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x43e6, &[0xb8, 0x0e, 0x00, 0x00, 0x00]); // ASM: mov eax,0xe
    put(bytes, 0x43eb, &[0xe9, 0x95, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x43f0, &[0x80, 0x79, 0x0f, 0x00]); // ASM: cmp byte [rcx+0xf],0
    put(bytes, 0x43f4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x43f6, &[0xb8, 0x0f, 0x00, 0x00, 0x00]); // ASM: mov eax,0xf
    put(bytes, 0x43fb, &[0xe9, 0x85, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4400, &[0x80, 0x79, 0x10, 0x00]); // ASM: cmp byte [rcx+0x10],0
    put(bytes, 0x4404, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4406, &[0xb8, 0x10, 0x00, 0x00, 0x00]); // ASM: mov eax,0x10
    put(bytes, 0x440b, &[0xe9, 0x75, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4410, &[0x80, 0x79, 0x11, 0x00]); // ASM: cmp byte [rcx+0x11],0
    put(bytes, 0x4414, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4416, &[0xb8, 0x11, 0x00, 0x00, 0x00]); // ASM: mov eax,0x11
    put(bytes, 0x441b, &[0xe9, 0x65, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4420, &[0x80, 0x79, 0x12, 0x00]); // ASM: cmp byte [rcx+0x12],0
    put(bytes, 0x4424, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4426, &[0xb8, 0x12, 0x00, 0x00, 0x00]); // ASM: mov eax,0x12
    put(bytes, 0x442b, &[0xe9, 0x55, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4430, &[0x80, 0x79, 0x13, 0x00]); // ASM: cmp byte [rcx+0x13],0
    put(bytes, 0x4434, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4436, &[0xb8, 0x13, 0x00, 0x00, 0x00]); // ASM: mov eax,0x13
    put(bytes, 0x443b, &[0xe9, 0x45, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4440, &[0x80, 0x79, 0x14, 0x00]); // ASM: cmp byte [rcx+0x14],0
    put(bytes, 0x4444, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4446, &[0xb8, 0x14, 0x00, 0x00, 0x00]); // ASM: mov eax,0x14
    put(bytes, 0x444b, &[0xe9, 0x35, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4450, &[0x80, 0x79, 0x15, 0x00]); // ASM: cmp byte [rcx+0x15],0
    put(bytes, 0x4454, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4456, &[0xb8, 0x15, 0x00, 0x00, 0x00]); // ASM: mov eax,0x15
    put(bytes, 0x445b, &[0xe9, 0x25, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4460, &[0x80, 0x79, 0x16, 0x00]); // ASM: cmp byte [rcx+0x16],0
    put(bytes, 0x4464, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4466, &[0xb8, 0x16, 0x00, 0x00, 0x00]); // ASM: mov eax,0x16
    put(bytes, 0x446b, &[0xe9, 0x15, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4470, &[0x80, 0x79, 0x17, 0x00]); // ASM: cmp byte [rcx+0x17],0
    put(bytes, 0x4474, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4476, &[0xb8, 0x17, 0x00, 0x00, 0x00]); // ASM: mov eax,0x17
    put(bytes, 0x447b, &[0xe9, 0x05, 0x03, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4480, &[0x80, 0x79, 0x18, 0x00]); // ASM: cmp byte [rcx+0x18],0
    put(bytes, 0x4484, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4486, &[0xb8, 0x18, 0x00, 0x00, 0x00]); // ASM: mov eax,0x18
    put(bytes, 0x448b, &[0xe9, 0xf5, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4490, &[0x80, 0x79, 0x19, 0x00]); // ASM: cmp byte [rcx+0x19],0
    put(bytes, 0x4494, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4496, &[0xb8, 0x19, 0x00, 0x00, 0x00]); // ASM: mov eax,0x19
    put(bytes, 0x449b, &[0xe9, 0xe5, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x44a0, &[0x80, 0x79, 0x1a, 0x00]); // ASM: cmp byte [rcx+0x1a],0
    put(bytes, 0x44a4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x44a6, &[0xb8, 0x1a, 0x00, 0x00, 0x00]); // ASM: mov eax,0x1a
    put(bytes, 0x44ab, &[0xe9, 0xd5, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x44b0, &[0x80, 0x79, 0x1b, 0x00]); // ASM: cmp byte [rcx+0x1b],0
    put(bytes, 0x44b4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x44b6, &[0xb8, 0x1b, 0x00, 0x00, 0x00]); // ASM: mov eax,0x1b
    put(bytes, 0x44bb, &[0xe9, 0xc5, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x44c0, &[0x80, 0x79, 0x1c, 0x00]); // ASM: cmp byte [rcx+0x1c],0
    put(bytes, 0x44c4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x44c6, &[0xb8, 0x1c, 0x00, 0x00, 0x00]); // ASM: mov eax,0x1c
    put(bytes, 0x44cb, &[0xe9, 0xb5, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x44d0, &[0x80, 0x79, 0x1d, 0x00]); // ASM: cmp byte [rcx+0x1d],0
    put(bytes, 0x44d4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x44d6, &[0xb8, 0x1d, 0x00, 0x00, 0x00]); // ASM: mov eax,0x1d
    put(bytes, 0x44db, &[0xe9, 0xa5, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x44e0, &[0x80, 0x79, 0x1e, 0x00]); // ASM: cmp byte [rcx+0x1e],0
    put(bytes, 0x44e4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x44e6, &[0xb8, 0x1e, 0x00, 0x00, 0x00]); // ASM: mov eax,0x1e
    put(bytes, 0x44eb, &[0xe9, 0x95, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x44f0, &[0x80, 0x79, 0x1f, 0x00]); // ASM: cmp byte [rcx+0x1f],0
    put(bytes, 0x44f4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x44f6, &[0xb8, 0x1f, 0x00, 0x00, 0x00]); // ASM: mov eax,0x1f
    put(bytes, 0x44fb, &[0xe9, 0x85, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4500, &[0x80, 0x79, 0x20, 0x00]); // ASM: cmp byte [rcx+0x20],0
    put(bytes, 0x4504, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4506, &[0xb8, 0x20, 0x00, 0x00, 0x00]); // ASM: mov eax,0x20
    put(bytes, 0x450b, &[0xe9, 0x75, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4510, &[0x80, 0x79, 0x21, 0x00]); // ASM: cmp byte [rcx+0x21],0
    put(bytes, 0x4514, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4516, &[0xb8, 0x21, 0x00, 0x00, 0x00]); // ASM: mov eax,0x21
    put(bytes, 0x451b, &[0xe9, 0x65, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4520, &[0x80, 0x79, 0x22, 0x00]); // ASM: cmp byte [rcx+0x22],0
    put(bytes, 0x4524, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4526, &[0xb8, 0x22, 0x00, 0x00, 0x00]); // ASM: mov eax,0x22
    put(bytes, 0x452b, &[0xe9, 0x55, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4530, &[0x80, 0x79, 0x23, 0x00]); // ASM: cmp byte [rcx+0x23],0
    put(bytes, 0x4534, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4536, &[0xb8, 0x23, 0x00, 0x00, 0x00]); // ASM: mov eax,0x23
    put(bytes, 0x453b, &[0xe9, 0x45, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4540, &[0x80, 0x79, 0x24, 0x00]); // ASM: cmp byte [rcx+0x24],0
    put(bytes, 0x4544, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4546, &[0xb8, 0x24, 0x00, 0x00, 0x00]); // ASM: mov eax,0x24
    put(bytes, 0x454b, &[0xe9, 0x35, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4550, &[0x80, 0x79, 0x25, 0x00]); // ASM: cmp byte [rcx+0x25],0
    put(bytes, 0x4554, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4556, &[0xb8, 0x25, 0x00, 0x00, 0x00]); // ASM: mov eax,0x25
    put(bytes, 0x455b, &[0xe9, 0x25, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4560, &[0x80, 0x79, 0x26, 0x00]); // ASM: cmp byte [rcx+0x26],0
    put(bytes, 0x4564, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4566, &[0xb8, 0x26, 0x00, 0x00, 0x00]); // ASM: mov eax,0x26
    put(bytes, 0x456b, &[0xe9, 0x15, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4570, &[0x80, 0x79, 0x27, 0x00]); // ASM: cmp byte [rcx+0x27],0
    put(bytes, 0x4574, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4576, &[0xb8, 0x27, 0x00, 0x00, 0x00]); // ASM: mov eax,0x27
    put(bytes, 0x457b, &[0xe9, 0x05, 0x02, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4580, &[0x80, 0x79, 0x28, 0x00]); // ASM: cmp byte [rcx+0x28],0
    put(bytes, 0x4584, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4586, &[0xb8, 0x28, 0x00, 0x00, 0x00]); // ASM: mov eax,0x28
    put(bytes, 0x458b, &[0xe9, 0xf5, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4590, &[0x80, 0x79, 0x29, 0x00]); // ASM: cmp byte [rcx+0x29],0
    put(bytes, 0x4594, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4596, &[0xb8, 0x29, 0x00, 0x00, 0x00]); // ASM: mov eax,0x29
    put(bytes, 0x459b, &[0xe9, 0xe5, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x45a0, &[0x80, 0x79, 0x2a, 0x00]); // ASM: cmp byte [rcx+0x2a],0
    put(bytes, 0x45a4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x45a6, &[0xb8, 0x2a, 0x00, 0x00, 0x00]); // ASM: mov eax,0x2a
    put(bytes, 0x45ab, &[0xe9, 0xd5, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x45b0, &[0x80, 0x79, 0x2b, 0x00]); // ASM: cmp byte [rcx+0x2b],0
    put(bytes, 0x45b4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x45b6, &[0xb8, 0x2b, 0x00, 0x00, 0x00]); // ASM: mov eax,0x2b
    put(bytes, 0x45bb, &[0xe9, 0xc5, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x45c0, &[0x80, 0x79, 0x2c, 0x00]); // ASM: cmp byte [rcx+0x2c],0
    put(bytes, 0x45c4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x45c6, &[0xb8, 0x2c, 0x00, 0x00, 0x00]); // ASM: mov eax,0x2c
    put(bytes, 0x45cb, &[0xe9, 0xb5, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x45d0, &[0x80, 0x79, 0x2d, 0x00]); // ASM: cmp byte [rcx+0x2d],0
    put(bytes, 0x45d4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x45d6, &[0xb8, 0x2d, 0x00, 0x00, 0x00]); // ASM: mov eax,0x2d
    put(bytes, 0x45db, &[0xe9, 0xa5, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x45e0, &[0x80, 0x79, 0x2e, 0x00]); // ASM: cmp byte [rcx+0x2e],0
    put(bytes, 0x45e4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x45e6, &[0xb8, 0x2e, 0x00, 0x00, 0x00]); // ASM: mov eax,0x2e
    put(bytes, 0x45eb, &[0xe9, 0x95, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x45f0, &[0x80, 0x79, 0x2f, 0x00]); // ASM: cmp byte [rcx+0x2f],0
    put(bytes, 0x45f4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x45f6, &[0xb8, 0x2f, 0x00, 0x00, 0x00]); // ASM: mov eax,0x2f
    put(bytes, 0x45fb, &[0xe9, 0x85, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4600, &[0x80, 0x79, 0x30, 0x00]); // ASM: cmp byte [rcx+0x30],0
    put(bytes, 0x4604, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4606, &[0xb8, 0x30, 0x00, 0x00, 0x00]); // ASM: mov eax,0x30
    put(bytes, 0x460b, &[0xe9, 0x75, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4610, &[0x80, 0x79, 0x31, 0x00]); // ASM: cmp byte [rcx+0x31],0
    put(bytes, 0x4614, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4616, &[0xb8, 0x31, 0x00, 0x00, 0x00]); // ASM: mov eax,0x31
    put(bytes, 0x461b, &[0xe9, 0x65, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4620, &[0x80, 0x79, 0x32, 0x00]); // ASM: cmp byte [rcx+0x32],0
    put(bytes, 0x4624, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4626, &[0xb8, 0x32, 0x00, 0x00, 0x00]); // ASM: mov eax,0x32
    put(bytes, 0x462b, &[0xe9, 0x55, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4630, &[0x80, 0x79, 0x33, 0x00]); // ASM: cmp byte [rcx+0x33],0
    put(bytes, 0x4634, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4636, &[0xb8, 0x33, 0x00, 0x00, 0x00]); // ASM: mov eax,0x33
    put(bytes, 0x463b, &[0xe9, 0x45, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4640, &[0x80, 0x79, 0x34, 0x00]); // ASM: cmp byte [rcx+0x34],0
    put(bytes, 0x4644, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4646, &[0xb8, 0x34, 0x00, 0x00, 0x00]); // ASM: mov eax,0x34
    put(bytes, 0x464b, &[0xe9, 0x35, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4650, &[0x80, 0x79, 0x35, 0x00]); // ASM: cmp byte [rcx+0x35],0
    put(bytes, 0x4654, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4656, &[0xb8, 0x35, 0x00, 0x00, 0x00]); // ASM: mov eax,0x35
    put(bytes, 0x465b, &[0xe9, 0x25, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4660, &[0x80, 0x79, 0x36, 0x00]); // ASM: cmp byte [rcx+0x36],0
    put(bytes, 0x4664, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4666, &[0xb8, 0x36, 0x00, 0x00, 0x00]); // ASM: mov eax,0x36
    put(bytes, 0x466b, &[0xe9, 0x15, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4670, &[0x80, 0x79, 0x37, 0x00]); // ASM: cmp byte [rcx+0x37],0
    put(bytes, 0x4674, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4676, &[0xb8, 0x37, 0x00, 0x00, 0x00]); // ASM: mov eax,0x37
    put(bytes, 0x467b, &[0xe9, 0x05, 0x01, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4680, &[0x80, 0x79, 0x38, 0x00]); // ASM: cmp byte [rcx+0x38],0
    put(bytes, 0x4684, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4686, &[0xb8, 0x38, 0x00, 0x00, 0x00]); // ASM: mov eax,0x38
    put(bytes, 0x468b, &[0xe9, 0xf5, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4690, &[0x80, 0x79, 0x39, 0x00]); // ASM: cmp byte [rcx+0x39],0
    put(bytes, 0x4694, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4696, &[0xb8, 0x39, 0x00, 0x00, 0x00]); // ASM: mov eax,0x39
    put(bytes, 0x469b, &[0xe9, 0xe5, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x46a0, &[0x80, 0x79, 0x3a, 0x00]); // ASM: cmp byte [rcx+0x3a],0
    put(bytes, 0x46a4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x46a6, &[0xb8, 0x3a, 0x00, 0x00, 0x00]); // ASM: mov eax,0x3a
    put(bytes, 0x46ab, &[0xe9, 0xd5, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x46b0, &[0x80, 0x79, 0x3b, 0x00]); // ASM: cmp byte [rcx+0x3b],0
    put(bytes, 0x46b4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x46b6, &[0xb8, 0x3b, 0x00, 0x00, 0x00]); // ASM: mov eax,0x3b
    put(bytes, 0x46bb, &[0xe9, 0xc5, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x46c0, &[0x80, 0x79, 0x3c, 0x00]); // ASM: cmp byte [rcx+0x3c],0
    put(bytes, 0x46c4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x46c6, &[0xb8, 0x3c, 0x00, 0x00, 0x00]); // ASM: mov eax,0x3c
    put(bytes, 0x46cb, &[0xe9, 0xb5, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x46d0, &[0x80, 0x79, 0x3d, 0x00]); // ASM: cmp byte [rcx+0x3d],0
    put(bytes, 0x46d4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x46d6, &[0xb8, 0x3d, 0x00, 0x00, 0x00]); // ASM: mov eax,0x3d
    put(bytes, 0x46db, &[0xe9, 0xa5, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x46e0, &[0x80, 0x79, 0x3e, 0x00]); // ASM: cmp byte [rcx+0x3e],0
    put(bytes, 0x46e4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x46e6, &[0xb8, 0x3e, 0x00, 0x00, 0x00]); // ASM: mov eax,0x3e
    put(bytes, 0x46eb, &[0xe9, 0x95, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x46f0, &[0x80, 0x79, 0x3f, 0x00]); // ASM: cmp byte [rcx+0x3f],0
    put(bytes, 0x46f4, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x46f6, &[0xb8, 0x3f, 0x00, 0x00, 0x00]); // ASM: mov eax,0x3f
    put(bytes, 0x46fb, &[0xe9, 0x85, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4700, &[0x80, 0x79, 0x40, 0x00]); // ASM: cmp byte [rcx+0x40],0
    put(bytes, 0x4704, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4706, &[0xb8, 0x40, 0x00, 0x00, 0x00]); // ASM: mov eax,0x40
    put(bytes, 0x470b, &[0xe9, 0x75, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4710, &[0x80, 0x79, 0x41, 0x00]); // ASM: cmp byte [rcx+0x41],0
    put(bytes, 0x4714, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4716, &[0xb8, 0x41, 0x00, 0x00, 0x00]); // ASM: mov eax,0x41
    put(bytes, 0x471b, &[0xe9, 0x65, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4720, &[0x80, 0x79, 0x42, 0x00]); // ASM: cmp byte [rcx+0x42],0
    put(bytes, 0x4724, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4726, &[0xb8, 0x42, 0x00, 0x00, 0x00]); // ASM: mov eax,0x42
    put(bytes, 0x472b, &[0xe9, 0x55, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4730, &[0x80, 0x79, 0x43, 0x00]); // ASM: cmp byte [rcx+0x43],0
    put(bytes, 0x4734, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4736, &[0xb8, 0x43, 0x00, 0x00, 0x00]); // ASM: mov eax,0x43
    put(bytes, 0x473b, &[0xe9, 0x45, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4740, &[0x80, 0x79, 0x44, 0x00]); // ASM: cmp byte [rcx+0x44],0
    put(bytes, 0x4744, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4746, &[0xb8, 0x44, 0x00, 0x00, 0x00]); // ASM: mov eax,0x44
    put(bytes, 0x474b, &[0xe9, 0x35, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4750, &[0x80, 0x79, 0x45, 0x00]); // ASM: cmp byte [rcx+0x45],0
    put(bytes, 0x4754, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4756, &[0xb8, 0x45, 0x00, 0x00, 0x00]); // ASM: mov eax,0x45
    put(bytes, 0x475b, &[0xe9, 0x25, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4760, &[0x80, 0x79, 0x46, 0x00]); // ASM: cmp byte [rcx+0x46],0
    put(bytes, 0x4764, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4766, &[0xb8, 0x46, 0x00, 0x00, 0x00]); // ASM: mov eax,0x46
    put(bytes, 0x476b, &[0xe9, 0x15, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4770, &[0x80, 0x79, 0x47, 0x00]); // ASM: cmp byte [rcx+0x47],0
    put(bytes, 0x4774, &[0x74, 0x0a]); // ASM: je next level
    put(bytes, 0x4776, &[0xb8, 0x47, 0x00, 0x00, 0x00]); // ASM: mov eax,0x47
    put(bytes, 0x477b, &[0xe9, 0x05, 0x00, 0x00, 0x00]); // ASM: jmp common
    put(bytes, 0x4780, &[0xb8, 0xff, 0x00, 0x00, 0x00]); // ASM: mov eax,0xff
    put(bytes, 0x4785, &[0xc3]); // ASM: ret (common)
    put(bytes, 0x4790, &[0xf0, 0xff, 0x49, 0x08]); // ASM: lock dec dword [rcx+8] (LK)
    put(bytes, 0x4794, &[0x75, 0x06]); // ASM: jne 0x479c
    put(bytes, 0x4796, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x479b, &[0xc3]); // ASM: ret
    put(bytes, 0x479c, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x479e, &[0xc3]); // ASM: ret
    put(bytes, 0x47a0, &[0x80, 0x71, 0x34, 0x01]); // ASM: xor byte [rcx+34h],1 (LP)
    put(bytes, 0x47a4, &[0x48, 0x8b, 0x09]); // ASM: mov rcx,[rcx]
    put(bytes, 0x47a7, &[0x48, 0x85, 0xc9]); // ASM: test rcx,rcx
    put(bytes, 0x47aa, &[0x75, 0xf4]); // ASM: jne 0x47a0
    put(bytes, 0x47ac, &[0xc3]); // ASM: ret
    put(bytes, 0x47b0, &[0x48, 0x89, 0x4c, 0x24, 0x08]); // ASM: mov [rsp+8],rcx (EN)
    put(bytes, 0x47b5, &[0x48, 0x8b, 0x4c, 0x24, 0x08]); // ASM: mov rcx,[rsp+8]
    put(bytes, 0x47ba, &[0x48, 0x8d, 0x15, 0x4f, 0xe4, 0xff, 0xff]); // ASM: lea rdx,[Back]
    put(bytes, 0x47c1, &[0xe8, 0x1a, 0xca, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x47c6, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x47c8, &[0x74, 0x06]); // ASM: jz next
    put(bytes, 0x47ca, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x47cf, &[0xc3]); // ASM: ret
    put(bytes, 0x47d0, &[0x48, 0x8b, 0x4c, 0x24, 0x08]); // ASM: mov rcx,[rsp+8]
    put(bytes, 0x47d5, &[0x48, 0x8d, 0x15, 0x3c, 0xe4, 0xff, 0xff]); // ASM: lea rdx,[Tab]
    put(bytes, 0x47dc, &[0xe8, 0xff, 0xc9, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x47e1, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x47e3, &[0x74, 0x06]); // ASM: jz next
    put(bytes, 0x47e5, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x47ea, &[0xc3]); // ASM: ret
    put(bytes, 0x47eb, &[0x48, 0x8b, 0x4c, 0x24, 0x08]); // ASM: mov rcx,[rsp+8]
    put(bytes, 0x47f0, &[0x48, 0x8d, 0x15, 0x29, 0xe4, 0xff, 0xff]); // ASM: lea rdx,[Clear]
    put(bytes, 0x47f7, &[0xe8, 0xe4, 0xc9, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x47fc, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x47fe, &[0x74, 0x06]); // ASM: jz next
    put(bytes, 0x4800, &[0xb8, 0x03, 0x00, 0x00, 0x00]); // ASM: mov eax,3
    put(bytes, 0x4805, &[0xc3]); // ASM: ret
    put(bytes, 0x4806, &[0x48, 0x8b, 0x4c, 0x24, 0x08]); // ASM: mov rcx,[rsp+8]
    put(bytes, 0x480b, &[0x48, 0x8d, 0x15, 0x16, 0xe4, 0xff, 0xff]); // ASM: lea rdx,[Return]
    put(bytes, 0x4812, &[0xe8, 0xc9, 0xc9, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4817, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x4819, &[0x74, 0x06]); // ASM: jz next
    put(bytes, 0x481b, &[0xb8, 0x04, 0x00, 0x00, 0x00]); // ASM: mov eax,4
    put(bytes, 0x4820, &[0xc3]); // ASM: ret
    put(bytes, 0x4821, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4823, &[0xc3]); // ASM: ret
    put(bytes, 0x4830, &[0x83, 0xf9, 0x00]); // ASM: cmp ecx,0 (EN2)
    put(bytes, 0x4833, &[0x75, 0x08]); // ASM: jne next
    put(bytes, 0x4835, &[0x48, 0x8d, 0x05, 0xf4, 0xe3, 0xff, 0xff]); // ASM: lea rax,[Normal]
    put(bytes, 0x483c, &[0xc3]); // ASM: ret
    put(bytes, 0x483d, &[0x83, 0xf9, 0x01]); // ASM: cmp ecx,1
    put(bytes, 0x4840, &[0x75, 0x08]); // ASM: jne next
    put(bytes, 0x4842, &[0x48, 0x8d, 0x05, 0xef, 0xe3, 0xff, 0xff]); // ASM: lea rax,[Pressed]
    put(bytes, 0x4849, &[0xc3]); // ASM: ret
    put(bytes, 0x484a, &[0x83, 0xf9, 0x02]); // ASM: cmp ecx,2
    put(bytes, 0x484d, &[0x75, 0x08]); // ASM: jne next
    put(bytes, 0x484f, &[0x48, 0x8d, 0x05, 0xea, 0xe3, 0xff, 0xff]); // ASM: lea rax,[Over]
    put(bytes, 0x4856, &[0xc3]); // ASM: ret
    put(bytes, 0x4857, &[0x83, 0xf9, 0x03]); // ASM: cmp ecx,3
    put(bytes, 0x485a, &[0x75, 0x08]); // ASM: jne next
    put(bytes, 0x485c, &[0x48, 0x8d, 0x05, 0xe5, 0xe3, 0xff, 0xff]); // ASM: lea rax,[Down]
    put(bytes, 0x4863, &[0xc3]); // ASM: ret
    put(bytes, 0x4864, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4866, &[0xc3]); // ASM: ret
    put(bytes, 0x4870, &[0x85, 0xc9]); // ASM: test ecx,ecx (ET)
    put(bytes, 0x4872, &[0x74, 0x42]); // ASM: jz 0x48b6
    put(bytes, 0x4874, &[0xe8, 0x67, 0xc9, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4879, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x487b, &[0x74, 0x39]); // ASM: jz 0x48b6
    put(bytes, 0x487d, &[0x89, 0x4a, 0x00]); // ASM: mov [rdx+0x0],ecx
    put(bytes, 0x4880, &[0x89, 0x4a, 0x04]); // ASM: mov [rdx+0x4],ecx
    put(bytes, 0x4883, &[0x89, 0x4a, 0x08]); // ASM: mov [rdx+0x8],ecx
    put(bytes, 0x4886, &[0x89, 0x4a, 0x0c]); // ASM: mov [rdx+0xc],ecx
    put(bytes, 0x4889, &[0x89, 0x4a, 0x10]); // ASM: mov [rdx+0x10],ecx
    put(bytes, 0x488c, &[0x89, 0x4a, 0x14]); // ASM: mov [rdx+0x14],ecx
    put(bytes, 0x488f, &[0x89, 0x4a, 0x18]); // ASM: mov [rdx+0x18],ecx
    put(bytes, 0x4892, &[0x89, 0x4a, 0x1c]); // ASM: mov [rdx+0x1c],ecx
    put(bytes, 0x4895, &[0x89, 0x4a, 0x20]); // ASM: mov [rdx+0x20],ecx
    put(bytes, 0x4898, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x489d, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x48a0, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x48a3, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x48a6, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x48a9, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x48ac, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x48af, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x48b2, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x48b5, &[0xc3]); // ASM: ret
    put(bytes, 0x48b6, &[0xe8, 0x25, 0xc9, 0xff, 0xff]); // ASM: call 0x11e0 (Q) (shared error tail)
    put(bytes, 0x48bb, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,7
    put(bytes, 0x48c0, &[0xc3]); // ASM: ret
    put(bytes, 0x48d0, &[0x83, 0x39, 0x00]); // ASM: cmp dword [rcx],0 (ET2 loop head)
    put(bytes, 0x48d3, &[0x74, 0x0f]); // ASM: je 0x48e4
    put(bytes, 0x48d5, &[0xe8, 0x06, 0xc9, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x48da, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x48dc, &[0x74, 0x09]); // ASM: jz 0x48e7
    put(bytes, 0x48de, &[0x48, 0x83, 0xc1, 0x08]); // ASM: add rcx,8
    put(bytes, 0x48e2, &[0xeb, 0xec]); // ASM: jmp 0x48d0
    put(bytes, 0x48e4, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x48e6, &[0xc3]); // ASM: ret
    put(bytes, 0x48e7, &[0xe8, 0xf4, 0xc8, 0xff, 0xff]); // ASM: call 0x11e0 (Q) (error tail)
    put(bytes, 0x48ec, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,7
    put(bytes, 0x48f1, &[0xc3]); // ASM: ret
    put(bytes, 0x4900, &[0x83, 0x39, 0x00]); // ASM: cmp dword [rcx],0 (ET3 loop head)
    put(bytes, 0x4903, &[0x74, 0x18]); // ASM: je 0x491d
    put(bytes, 0x4905, &[0xe8, 0xd6, 0xc8, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x490a, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x490c, &[0x74, 0x12]); // ASM: jz 0x4920
    put(bytes, 0x490e, &[0xe8, 0xcd, 0xc8, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4913, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x4915, &[0x74, 0x09]); // ASM: jz 0x4920
    put(bytes, 0x4917, &[0x48, 0x83, 0xc1, 0x08]); // ASM: add rcx,8
    put(bytes, 0x491b, &[0xeb, 0xe3]); // ASM: jmp 0x4900
    put(bytes, 0x491d, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x491f, &[0xc3]); // ASM: ret
    put(bytes, 0x4920, &[0xe8, 0xbb, 0xc8, 0xff, 0xff]); // ASM: call 0x11e0 (Q) (error tail)
    put(bytes, 0x4925, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,7
    put(bytes, 0x492a, &[0xc3]); // ASM: ret
    put(bytes, 0x4930, &[0x85, 0xc9]); // ASM: test ecx,ecx (FC)
    put(bytes, 0x4932, &[0x74, 0x17]); // ASM: jz 0x494b
    put(bytes, 0x4934, &[0xe8, 0xa7, 0xc8, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4939, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x493b, &[0x74, 0x02]); // ASM: jz 0x493f
    put(bytes, 0x493d, &[0x89, 0x0a]); // ASM: mov [rdx],ecx
    put(bytes, 0x493f, &[0x89, 0x4a, 0x04]); // ASM: mov [rdx+4],ecx
    put(bytes, 0x4942, &[0xe8, 0x99, 0xc8, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x4947, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x4949, &[0x74, 0x1b]); // ASM: jz 0x4966
    put(bytes, 0x494b, &[0x89, 0x4a, 0x08]); // ASM: mov [rdx+0x8],ecx
    put(bytes, 0x494e, &[0x89, 0x4a, 0x0c]); // ASM: mov [rdx+0xc],ecx
    put(bytes, 0x4951, &[0x89, 0x4a, 0x10]); // ASM: mov [rdx+0x10],ecx
    put(bytes, 0x4954, &[0x89, 0x4a, 0x14]); // ASM: mov [rdx+0x14],ecx
    put(bytes, 0x4957, &[0x89, 0x4a, 0x18]); // ASM: mov [rdx+0x18],ecx
    put(bytes, 0x495a, &[0x89, 0x4a, 0x1c]); // ASM: mov [rdx+0x1c],ecx
    put(bytes, 0x495d, &[0x89, 0x4a, 0x20]); // ASM: mov [rdx+0x20],ecx
    put(bytes, 0x4960, &[0x89, 0x4a, 0x24]); // ASM: mov [rdx+0x24],ecx
    put(bytes, 0x4963, &[0x89, 0x4a, 0x28]); // ASM: mov [rdx+0x28],ecx
    put(bytes, 0x4966, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x496b, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x496e, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4971, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4974, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4977, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x497a, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x497d, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4980, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4983, &[0xc3]); // ASM: ret
    put(bytes, 0x4990, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5 (SP1)
    put(bytes, 0x4995, &[0x83, 0xc0, 0x11]); // ASM: add eax,0x11
    put(bytes, 0x4998, &[0xc3]); // ASM: ret
    put(bytes, 0x49a0, &[0xb8, 0x09, 0x00, 0x00, 0x00]); // ASM: mov eax,9 (SP2)
    put(bytes, 0x49a5, &[0x83, 0xc0, 0x22]); // ASM: add eax,0x22
    put(bytes, 0x49a8, &[0xc3]); // ASM: ret
    put(bytes, 0x49b0, &[0x85, 0xc9]); // ASM: test ecx,ecx (FG)
    put(bytes, 0x49b2, &[0x74, 0x2b]); // ASM: jz 0x49df (END)
    put(bytes, 0x49b4, &[0x89, 0x0a]); // ASM: mov [rdx],ecx (A)
    put(bytes, 0x49b6, &[0xe8, 0x25, 0xc8, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x49bb, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x49bd, &[0x74, 0x17]); // ASM: jz 0x49d6 (D)
    put(bytes, 0x49bf, &[0x89, 0x4a, 0x04]); // ASM: mov [rdx+4],ecx (B)
    put(bytes, 0x49c2, &[0xe8, 0x19, 0xc8, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x49c7, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x49c9, &[0x75, 0x0e]); // ASM: jne 0x49d9 (MID)
    put(bytes, 0x49cb, &[0x89, 0x4a, 0x08]); // ASM: mov [rdx+8],ecx (C)
    put(bytes, 0x49ce, &[0x89, 0x4a, 0x14]); // ASM: mov [rdx+0x14],ecx
    put(bytes, 0x49d1, &[0x89, 0x4a, 0x18]); // ASM: mov [rdx+0x18],ecx
    put(bytes, 0x49d4, &[0x89, 0x0a]); // ASM: mov [rdx],ecx
    put(bytes, 0x49d6, &[0x89, 0x4a, 0x0c]); // ASM: mov [rdx+0xc],ecx (D)
    put(bytes, 0x49d9, &[0x89, 0x4a, 0x10]); // ASM: mov [rdx+0x10],ecx (MID)
    put(bytes, 0x49dc, &[0x89, 0x4a, 0x1c]); // ASM: mov [rdx+0x1c],ecx
    put(bytes, 0x49df, &[0x89, 0x4a, 0x20]); // ASM: mov [rdx+0x20],ecx (END)
    put(bytes, 0x49e2, &[0x89, 0x4a, 0x24]); // ASM: mov [rdx+0x24],ecx
    put(bytes, 0x49e5, &[0x89, 0x4a, 0x28]); // ASM: mov [rdx+0x28],ecx
    put(bytes, 0x49e8, &[0x89, 0x4a, 0x2c]); // ASM: mov [rdx+0x2c],ecx
    put(bytes, 0x49eb, &[0x89, 0x4a, 0x30]); // ASM: mov [rdx+0x30],ecx
    put(bytes, 0x49ee, &[0x89, 0x4a, 0x34]); // ASM: mov [rdx+0x34],ecx
    put(bytes, 0x49f1, &[0x89, 0x4a, 0x38]); // ASM: mov [rdx+0x38],ecx
    put(bytes, 0x49f4, &[0x89, 0x4a, 0x3c]); // ASM: mov [rdx+0x3c],ecx
    put(bytes, 0x49f7, &[0x89, 0x4a, 0x40]); // ASM: mov [rdx+0x40],ecx
    put(bytes, 0x49fa, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x49ff, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4a02, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4a05, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4a08, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4a0b, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4a0e, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4a11, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4a14, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4a17, &[0xc3]); // ASM: ret
    put(bytes, 0x4a20, &[0xe8, 0x8b, 0xfd, 0xff, 0xff]); // ASM: call 0x47b0 (EN) (CE1)
    put(bytes, 0x4a25, &[0x83, 0xf8, 0x03]); // ASM: cmp eax,3
    put(bytes, 0x4a28, &[0x75, 0x06]); // ASM: jne 0x4a30
    put(bytes, 0x4a2a, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x4a2f, &[0xc3]); // ASM: ret
    put(bytes, 0x4a30, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4a32, &[0xc3]); // ASM: ret
    put(bytes, 0x4a40, &[0xb9, 0x02, 0x00, 0x00, 0x00]); // ASM: mov ecx,2 (CE2)
    put(bytes, 0x4a45, &[0xe8, 0xe6, 0xfd, 0xff, 0xff]); // ASM: call 0x4830 (EN2)
    put(bytes, 0x4a4a, &[0xc3]); // ASM: ret
    put(bytes, 0x4a50, &[0x83, 0xf9, 0x00]); // ASM: cmp ecx,0 (EN3)
    put(bytes, 0x4a53, &[0x75, 0x09]); // ASM: jne next level
    put(bytes, 0x4a55, &[0x48, 0x8d, 0x15, 0xd4, 0xe1, 0xff, 0xff]); // ASM: lea rdx,[Normal]
    put(bytes, 0x4a5c, &[0xeb, 0x31]); // ASM: jmp END
    put(bytes, 0x4a5e, &[0x83, 0xf9, 0x01]); // ASM: cmp ecx,1
    put(bytes, 0x4a61, &[0x75, 0x09]); // ASM: jne next level
    put(bytes, 0x4a63, &[0x48, 0x8d, 0x15, 0xce, 0xe1, 0xff, 0xff]); // ASM: lea rdx,[Pressed]
    put(bytes, 0x4a6a, &[0xeb, 0x23]); // ASM: jmp END
    put(bytes, 0x4a6c, &[0x83, 0xf9, 0x02]); // ASM: cmp ecx,2
    put(bytes, 0x4a6f, &[0x75, 0x09]); // ASM: jne next level
    put(bytes, 0x4a71, &[0x48, 0x8d, 0x15, 0xc8, 0xe1, 0xff, 0xff]); // ASM: lea rdx,[Over]
    put(bytes, 0x4a78, &[0xeb, 0x15]); // ASM: jmp END
    put(bytes, 0x4a7a, &[0x83, 0xf9, 0x04]); // ASM: cmp ecx,4
    put(bytes, 0x4a7d, &[0x75, 0x09]); // ASM: jne DEFAULT
    put(bytes, 0x4a7f, &[0x48, 0x8d, 0x15, 0xc2, 0xe1, 0xff, 0xff]); // ASM: lea rdx,[Down]
    put(bytes, 0x4a86, &[0xeb, 0x07]); // ASM: jmp END
    put(bytes, 0x4a88, &[0x48, 0x8d, 0x15, 0xa1, 0xe1, 0xff, 0xff]); // ASM: lea rdx,[Normal] (DEFAULT)
    put(bytes, 0x4a8f, &[0xe8, 0x4c, 0xc7, 0xff, 0xff]); // ASM: call 0x11e0 (Q) (END)
    put(bytes, 0x4a94, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x4aa0,
        &[0x48, 0xb8, 0x67, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66],
    ); // ASM: mov rax,0x6666666666666667 (DV5)
    put(bytes, 0x4aaa, &[0x48, 0xf7, 0xe9]); // ASM: imul rcx
    put(bytes, 0x4aad, &[0x48, 0xd1, 0xfa]); // ASM: sar rdx,1
    put(bytes, 0x4ab0, &[0x48, 0x8b, 0xc2]); // ASM: mov rax,rdx
    put(bytes, 0x4ab3, &[0x48, 0xc1, 0xe8, 0x3f]); // ASM: shr rax,63
    put(bytes, 0x4ab7, &[0x48, 0x03, 0xc2]); // ASM: add rax,rdx
    put(bytes, 0x4aba, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x4ac0,
        &[0x48, 0xb8, 0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc],
    ); // ASM: mov rax,0xcccccccccccccccd (DV10)
    put(bytes, 0x4aca, &[0x48, 0xf7, 0xe1]); // ASM: mul rcx
    put(bytes, 0x4acd, &[0x48, 0xc1, 0xea, 0x03]); // ASM: shr rdx,3
    put(bytes, 0x4ad1, &[0x48, 0x8b, 0xc2]); // ASM: mov rax,rdx
    put(bytes, 0x4ad4, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x4ae0,
        &[0x48, 0xb8, 0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc],
    ); // ASM: mov rax,0xcccccccccccccccd (DM10)
    put(bytes, 0x4aea, &[0x48, 0xf7, 0xe1]); // ASM: mul rcx
    put(bytes, 0x4aed, &[0x48, 0xc1, 0xea, 0x03]); // ASM: shr rdx,3
    put(bytes, 0x4af1, &[0x48, 0x8d, 0x04, 0x92]); // ASM: lea rax,[rdx+rdx*4]
    put(bytes, 0x4af5, &[0x48, 0x03, 0xc0]); // ASM: add rax,rax
    put(bytes, 0x4af8, &[0x48, 0x2b, 0xc8]); // ASM: sub rcx,rax
    put(bytes, 0x4afb, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx
    put(bytes, 0x4afe, &[0xc3]); // ASM: ret
    put(bytes, 0x4b30, &[0x48, 0x83, 0xc8, 0xff]); // ASM: or rax,-1 (OR)
    put(bytes, 0x4b34, &[0xc3]); // ASM: ret
    put(bytes, 0x4b20, &[0x31, 0xc0]); // ASM: xor eax,eax (SE)
    put(bytes, 0x4b22, &[0x48, 0x85, 0xc9]); // ASM: test rcx,rcx
    put(bytes, 0x4b25, &[0x0f, 0x9f, 0xc0]); // ASM: setg al
    put(bytes, 0x4b28, &[0x48, 0xf7, 0xd8]); // ASM: neg rax
    put(bytes, 0x4b2b, &[0x83, 0xe0, 0x22]); // ASM: and eax,0x22
    put(bytes, 0x4b2e, &[0xc3]); // ASM: ret
    put(bytes, 0x4b10, &[0x8b, 0x04, 0x91]); // ASM: mov eax,[rcx+rdx*4] (IX)
    put(bytes, 0x4b13, &[0xc3]); // ASM: ret
    put(bytes, 0x4b00, &[0x48, 0x83, 0xc8, 0xff]); // ASM: or rax,-1 (SL)
    put(bytes, 0x4b04, &[0x48, 0xff, 0xc0]); // ASM: inc rax (L)
    put(bytes, 0x4b07, &[0x80, 0x3c, 0x01, 0x00]); // ASM: cmp byte [rcx+rax],0
    put(bytes, 0x4b0b, &[0x75, 0xf7]); // ASM: jne L
    put(bytes, 0x4b0d, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x4b40,
        &[0x48, 0xb8, 0xc5, 0x4e, 0xec, 0xc4, 0x4e, 0xec, 0xc4, 0x4e],
    ); // ASM: mov rax,0x4ec4ec4ec4ec4ec5 (QS)
    put(bytes, 0x4b4a, &[0x48, 0xf7, 0xe9]); // ASM: imul rcx
    put(bytes, 0x4b4d, &[0x48, 0xc1, 0xfa, 0x06]); // ASM: sar rdx,6
    put(bytes, 0x4b51, &[0x48, 0x8b, 0xc2]); // ASM: mov rax,rdx
    put(bytes, 0x4b54, &[0x48, 0xc1, 0xe8, 0x3f]); // ASM: shr rax,63
    put(bytes, 0x4b58, &[0xc3]); // ASM: ret
    put(bytes, 0x4b60, &[0xb8, 0x10, 0x00, 0x00, 0x00]); // ASM: mov eax,16 (SA)
    put(bytes, 0x4b65, &[0x48, 0xf7, 0xe1]); // ASM: mul rcx
    put(bytes, 0x4b68, &[0x48, 0xc7, 0xc1, 0xff, 0xff, 0xff, 0xff]); // ASM: mov rcx,-1
    put(bytes, 0x4b6f, &[0x48, 0x0f, 0x42, 0xc1]); // ASM: cmovb rax,rcx
    put(bytes, 0x4b73, &[0x48, 0x83, 0xc0, 0x08]); // ASM: add rax,8
    put(bytes, 0x4b77, &[0x48, 0xc7, 0xc1, 0xff, 0xff, 0xff, 0xff]); // ASM: mov rcx,-1
    put(bytes, 0x4b7e, &[0x48, 0x0f, 0x42, 0xc1]); // ASM: cmovb rax,rcx
    put(bytes, 0x4b82, &[0xc3]); // ASM: ret
    put(bytes, 0x4b90, &[0x31, 0xc0]); // ASM: xor eax,eax (TI)
    put(bytes, 0x4b92, &[0x4c, 0x8d, 0x42, 0x01]); // ASM: lea r8,[rdx+1]
    put(bytes, 0x4b96, &[0x48, 0x83, 0xfa, 0x03]); // ASM: cmp rdx,3
    put(bytes, 0x4b9a, &[0x49, 0x0f, 0x45, 0xc0]); // ASM: cmovne rax,r8
    put(bytes, 0x4b9e, &[0x8b, 0x04, 0x81]); // ASM: mov eax,[rcx+rax*4]
    put(bytes, 0x4ba1, &[0xc3]); // ASM: ret
    put(bytes, 0x4bb0, &[0x48, 0x83, 0xe1, 0xf0]); // ASM: and rcx,-16 (AM)
    put(bytes, 0x4bb4, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx
    put(bytes, 0x4bb7, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x4bc0,
        &[0x48, 0xb8, 0x93, 0x24, 0x49, 0x92, 0x24, 0x49, 0x92, 0x24],
    ); // ASM: mov rax,0x2492492492492493 (DV7)
    put(bytes, 0x4bca, &[0x48, 0xf7, 0xe1]); // ASM: mul rcx
    put(bytes, 0x4bcd, &[0x48, 0x2b, 0xca]); // ASM: sub rcx,rdx
    put(bytes, 0x4bd0, &[0x48, 0xd1, 0xe9]); // ASM: shr rcx,1
    put(bytes, 0x4bd3, &[0x48, 0x03, 0xca]); // ASM: add rcx,rdx
    put(bytes, 0x4bd6, &[0x48, 0xc1, 0xe9, 0x02]); // ASM: shr rcx,2
    put(bytes, 0x4bda, &[0x48, 0x8b, 0xc1]); // ASM: mov rax,rcx
    put(bytes, 0x4bdd, &[0xc3]); // ASM: ret
    put(bytes, 0x4be0, &[0x48, 0x63, 0x01]); // ASM: movsxd rax,dword [rcx] (SX)
    put(bytes, 0x4be3, &[0xc3]); // ASM: ret
    put(bytes, 0x4bf0, &[0x48, 0x63, 0x04, 0x91]); // ASM: movsxd rax,dword [rcx+rdx*4] (SX2)
    put(bytes, 0x4bf4, &[0xc3]); // ASM: ret
    put(bytes, 0x4c00, &[0x48, 0x63, 0xc1]); // ASM: movsxd rax,ecx (SC)
    put(bytes, 0x4c03, &[0x48, 0x3b, 0xc2]); // ASM: cmp rax,rdx
    put(bytes, 0x4c06, &[0x0f, 0x9f, 0xc0]); // ASM: setg al
    put(bytes, 0x4c09, &[0x0f, 0xb6, 0xc0]); // ASM: movzx eax,al
    put(bytes, 0x4c0c, &[0x48, 0x03, 0xc1]); // ASM: add rax,rcx
    put(bytes, 0x4c0f, &[0xc3]); // ASM: ret
    put(bytes, 0x4c10, &[0x8b, 0x41, 0x18]); // ASM: mov eax,[rcx+0x18] (LY)
    put(bytes, 0x4c13, &[0x03, 0x41, 0x1c]); // ASM: add eax,[rcx+0x1c]
    put(bytes, 0x4c16, &[0x89, 0x41, 0x20]); // ASM: mov [rcx+0x20],eax
    put(bytes, 0x4c19, &[0xc3]); // ASM: ret
    put(bytes, 0x4c20, &[0x48, 0x63, 0xc1]); // ASM: movsxd rax,ecx (TP)
    put(bytes, 0x4c23, &[0x48, 0x6b, 0xc0, 0x03]); // ASM: imul rax,rax,3
    put(bytes, 0x4c27, &[0xc3]); // ASM: ret
    put(bytes, 0x4c30, &[0x0f, 0xb6, 0xc1]); // ASM: movzx eax,cl (TP2)
    put(bytes, 0x4c33, &[0x83, 0xc0, 0x01]); // ASM: add eax,1
    put(bytes, 0x4c36, &[0xc3]); // ASM: ret
    put(bytes, 0x4c40, &[0x48, 0x8d, 0x44, 0xd1, 0x10]); // ASM: lea rax,[rcx+rdx*8+0x10] (RU)
    put(bytes, 0x4c45, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x4c48, &[0x48, 0x89, 0x41, 0x08]); // ASM: mov [rcx+8],rax
    put(bytes, 0x4c4c, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x4c60,
        &[0x48, 0xb8, 0xc5, 0x4e, 0xec, 0xc4, 0x4e, 0xec, 0xc4, 0x4e],
    ); // ASM: mov rax,0x4ec4ec4ec4ec4ec5 (DV208)
    put(bytes, 0x4c6a, &[0x48, 0x2b, 0xca]); // ASM: sub rcx,rdx
    put(bytes, 0x4c6d, &[0x48, 0xf7, 0xe9]); // ASM: imul rcx
    put(bytes, 0x4c70, &[0x48, 0xc1, 0xfa, 0x06]); // ASM: sar rdx,6
    put(bytes, 0x4c74, &[0x48, 0x8b, 0xc2]); // ASM: mov rax,rdx
    put(bytes, 0x4c77, &[0x48, 0xc1, 0xe8, 0x3f]); // ASM: shr rax,63
    put(bytes, 0x4c7b, &[0x48, 0x03, 0xc2]); // ASM: add rax,rdx
    put(bytes, 0x4c7e, &[0xc3]); // ASM: ret
    put(bytes, 0x4c90, &[0x48, 0x8b, 0x44, 0x24, 0x28]); // ASM: mov rax,[rsp+0x28] (SP5)
    put(bytes, 0x4c95, &[0x48, 0x03, 0x44, 0x24, 0x30]); // ASM: add rax,[rsp+0x30]
    put(bytes, 0x4c9a, &[0xc3]); // ASM: ret
    put(bytes, 0x4cb0, &[0x83, 0xf9, 0x02]); // ASM: cmp ecx,2 (JTG)
    put(bytes, 0x4cb3, &[0x77, 0x1b]); // ASM: ja DEF
    put(bytes, 0x4cb5, &[0x8b, 0xc1]); // ASM: mov eax,ecx
    put(bytes, 0x4cb7, &[0xff, 0x24, 0xc5, 0x00, 0x2e, 0x00, 0x00]); // ASM: jmp qword [rax*8+0x2e00]
    put(bytes, 0x4cbe, &[0xb8, 0x0a, 0x00, 0x00, 0x00]); // ASM: mov eax,10 (CASE0)
    put(bytes, 0x4cc3, &[0xc3]); // ASM: ret
    put(bytes, 0x4cc4, &[0xb8, 0x14, 0x00, 0x00, 0x00]); // ASM: mov eax,20 (CASE1)
    put(bytes, 0x4cc9, &[0xc3]); // ASM: ret
    put(bytes, 0x4cca, &[0xb8, 0x1e, 0x00, 0x00, 0x00]); // ASM: mov eax,30 (CASE2)
    put(bytes, 0x4ccf, &[0xc3]); // ASM: ret
    put(bytes, 0x4cd0, &[0x31, 0xc0]); // ASM: xor eax,eax (DEF)
    put(bytes, 0x4cd2, &[0xc3]); // ASM: ret
    put(bytes, 0x4ce0, &[0x83, 0xf9, 0x02]); // ASM: cmp ecx,2 (JTM)
    put(bytes, 0x4ce3, &[0x77, 0x25]); // ASM: ja DEF
    put(bytes, 0x4ce5, &[0x48, 0x8d, 0x15, 0x14, 0xc3, 0xff, 0xff]); // ASM: lea rdx,[0x1000]
    put(bytes, 0x4cec, &[0x8b, 0x8c, 0x8a, 0x20, 0x1e, 0x00, 0x00]); // ASM: mov ecx,[rdx+rcx*4+0x1e20]
    put(bytes, 0x4cf3, &[0x48, 0x03, 0xca]); // ASM: add rcx,rdx
    put(bytes, 0x4cf6, &[0xff, 0xe1]); // ASM: jmp rcx
    put(bytes, 0x4cf8, &[0xb8, 0x28, 0x00, 0x00, 0x00]); // ASM: mov eax,40 (CASE0)
    put(bytes, 0x4cfd, &[0xc3]); // ASM: ret
    put(bytes, 0x4cfe, &[0xb8, 0x32, 0x00, 0x00, 0x00]); // ASM: mov eax,50 (CASE1)
    put(bytes, 0x4d03, &[0xc3]); // ASM: ret
    put(bytes, 0x4d04, &[0xb8, 0x3c, 0x00, 0x00, 0x00]); // ASM: mov eax,60 (CASE2)
    put(bytes, 0x4d09, &[0xc3]); // ASM: ret
    put(bytes, 0x4d0a, &[0x31, 0xc0]); // ASM: xor eax,eax (DEF)
    put(bytes, 0x4d0c, &[0xc3]); // ASM: ret
    put(bytes, 0x4d20, &[0x48, 0x8d, 0x0d, 0xd9, 0xe1, 0xff, 0xff]); // ASM: lea rcx,[0x2f00] (AQ)
    put(bytes, 0x4d27, &[0x48, 0x8d, 0x15, 0xe2, 0xd6, 0xff, 0xff]); // ASM: lea rdx,[0x2410]
    put(bytes, 0x4d2e, &[0x41, 0xb8, 0x0c, 0x00, 0x00, 0x00]); // ASM: mov r8d,12
    put(bytes, 0x4d34, &[0xff, 0x15, 0x16, 0xd3, 0xff, 0xff]); // ASM: call qword [0x2050] (ReportAssertFailure)
    put(bytes, 0x4d3a, &[0x85, 0xc9]); // ASM: test ecx,ecx
    put(bytes, 0x4d3c, &[0x74, 0x05]); // ASM: jz R
    put(bytes, 0x4d3e, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x4d43, &[0xc3]); // ASM: ret (R)
    put(bytes, 0x4d50, &[0x48, 0x8d, 0x05, 0xc9, 0xe1, 0xff, 0xff]); // ASM: lea rax,[0x2f20] (PF)
    put(bytes, 0x4d57, &[0x48, 0x8b, 0xca]); // ASM: mov rcx,rdx
    put(bytes, 0x4d5a, &[0xe8, 0x11, 0x00, 0x00, 0x00]); // ASM: call 0x4d70 (PG)
    put(bytes, 0x4d5f, &[0xc3]); // ASM: ret
    put(bytes, 0x4d70, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (PG)
    put(bytes, 0x4d73, &[0xc3]); // ASM: ret
    put(bytes, 0x4d80, &[0x48, 0x8d, 0x15, 0xb9, 0xd2, 0xff, 0xff]); // ASM: lea rdx,[0x2040] (TS1)
    put(bytes, 0x4d87, &[0x48, 0x8d, 0x0d, 0x72, 0xe2, 0xff, 0xff]); // ASM: lea rcx,[0x3000]
    put(bytes, 0x4d8e, &[0xc3]); // ASM: ret
    put(bytes, 0x4d90, &[0x48, 0x8d, 0x15, 0xa9, 0xd2, 0xff, 0xff]); // ASM: lea rdx,[0x2040] (TS2)
    put(bytes, 0x4d97, &[0x48, 0x8d, 0x0d, 0x6a, 0xe2, 0xff, 0xff]); // ASM: lea rcx,[0x3008]
    put(bytes, 0x4d9e, &[0xc3]); // ASM: ret
    put(bytes, 0x4da0, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5 (NR)
    put(bytes, 0x4da5, &[0x0f, 0xaf, 0xc1]); // ASM: imul eax,ecx
    put(bytes, 0x4da8, &[0xc3]); // ASM: ret
    put(bytes, 0x4dc0, &[0xe8, 0xdb, 0xff, 0xff, 0xff]); // ASM: call 0x4da0 (NRC)
    put(bytes, 0x4dc5, &[0x31, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x4dc7, &[0xc3]); // ASM: ret
    put(bytes, 0x4de0, &[0x48, 0x8d, 0x05, 0x79, 0xe1, 0xff, 0xff]); // ASM: lea rax,[0x2f60] (ES)
    put(bytes, 0x4de7, &[0xc3]); // ASM: ret
    put(bytes, 0x4e00, &[0x48, 0x8d, 0x05, 0x79, 0xe1, 0xff, 0xff]); // ASM: lea rax,[0x2f80] (TB)
    put(bytes, 0x4e07, &[0xc3]); // ASM: ret
    put(bytes, 0x11e4, &[0xe8, 0xf7, 0xff, 0xff, 0xff]); // ASM: call 0x11e0 (CI, Q)
    put(bytes, 0x11e9, &[0x48, 0x8d, 0x0d, 0xe8, 0x18, 0x00, 0x00]); // ASM: lea rcx,[rip+..] -> 0x2ad8
    put(bytes, 0x11f0, &[0x48, 0x89, 0x08]); // ASM: mov [rax],rcx
    put(bytes, 0x11f3, &[0x48, 0x8d, 0x15, 0x86, 0x1e, 0x00, 0x00]); // ASM: lea rdx,[rip+..] -> 0x3080
    put(bytes, 0x11fa, &[0xc3]); // ASM: ret
    put(bytes, 0x1f00, &[0x85, 0xc9]); // ASM: test ecx,ecx (GX)
    put(bytes, 0x1f02, &[0x74, 0x1a]); // ASM: jz 0x1f1e
    put(bytes, 0x1f04, &[0xe8, 0xd7, 0xf2, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1f09, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x1f0b, &[0x75, 0x11]); // ASM: jnz 0x1f1e
    put(bytes, 0x1f0d, &[0xbf, 0x01, 0x00, 0x00, 0x00]); // ASM: mov edi,1
    put(bytes, 0x1f12, &[0x85, 0xff]); // ASM: test edi,edi
    put(bytes, 0x1f14, &[0x74, 0x05]); // ASM: jz 0x1f1b
    put(bytes, 0x1f16, &[0xe8, 0xc5, 0xf2, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1f1b, &[0x8b, 0xc7]); // ASM: mov eax,edi
    put(bytes, 0x1f1d, &[0xc3]); // ASM: ret
    put(bytes, 0x1f1e, &[0x33, 0xff]); // ASM: xor edi,edi
    put(bytes, 0x1f20, &[0xeb, 0xf0]); // ASM: jmp 0x1f12
    put(bytes, 0x1f30, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1 (BL)
    put(bytes, 0x1f35, &[0xc3]); // ASM: ret
    put(bytes, 0x1f40, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1f30 (CW)
    put(bytes, 0x1f45, &[0x84, 0xc0]); // ASM: test al,al
    put(bytes, 0x1f47, &[0x74, 0x06]); // ASM: jz 0x1f4f
    put(bytes, 0x1f49, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x1f4e, &[0xc3]); // ASM: ret
    put(bytes, 0x1f4f, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1f51, &[0xc3]); // ASM: ret
    put(bytes, 0x1f60, &[0x33, 0xc0]); // ASM: xor eax,eax (BB)
    put(bytes, 0x1f62, &[0x83, 0xf9, 0x01]); // ASM: cmp ecx,1
    put(bytes, 0x1f65, &[0x0f, 0x94, 0xc0]); // ASM: sete al
    put(bytes, 0x1f68, &[0xc3]); // ASM: ret
    put(bytes, 0x1f70, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1f60 (CB2)
    put(bytes, 0x1f75, &[0x8b, 0xc8]); // ASM: mov ecx,eax
    put(bytes, 0x1f77, &[0x84, 0xc9]); // ASM: test cl,cl
    put(bytes, 0x1f79, &[0x74, 0x06]); // ASM: jz 0x1f81
    put(bytes, 0x1f7b, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x1f80, &[0xc3]); // ASM: ret
    put(bytes, 0x1f81, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1f83, &[0xc3]); // ASM: ret
    put(bytes, 0x1f90, &[0x0f, 0xb6, 0x41, 0x10]); // ASM: movzx eax,byte [rcx+0x10] (BZ)
    put(bytes, 0x1f94, &[0xc3]); // ASM: ret
    put(bytes, 0x1fa0, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1f90 (CZ)
    put(bytes, 0x1fa5, &[0x8b, 0xd0]); // ASM: mov edx,eax
    put(bytes, 0x1fa7, &[0x84, 0xd2]); // ASM: test dl,dl
    put(bytes, 0x1fa9, &[0x74, 0x06]); // ASM: jz 0x1fb1
    put(bytes, 0x1fab, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x1fb0, &[0xc3]); // ASM: ret
    put(bytes, 0x1fb1, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1fb3, &[0xc3]); // ASM: ret
    put(bytes, 0x1fc0, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (BN)
    put(bytes, 0x1fc3, &[0x48, 0x85, 0xc0]); // ASM: test rax,rax
    put(bytes, 0x1fc6, &[0x74, 0x05]); // ASM: jz 0x1fcd
    put(bytes, 0x1fc8, &[0x0f, 0xb6, 0x40, 0x08]); // ASM: movzx eax,byte [rax+8]
    put(bytes, 0x1fcc, &[0xc3]); // ASM: ret
    put(bytes, 0x1fcd, &[0xc3]); // ASM: ret
    put(bytes, 0x1fd0, &[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1fc0 (CN)
    put(bytes, 0x1fd5, &[0x8b, 0xd0]); // ASM: mov edx,eax
    put(bytes, 0x1fd7, &[0x84, 0xd2]); // ASM: test dl,dl
    put(bytes, 0x1fd9, &[0x74, 0x06]); // ASM: jz 0x1fe1
    put(bytes, 0x1fdb, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x1fe0, &[0xc3]); // ASM: ret
    put(bytes, 0x1fe1, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1fe3, &[0xc3]); // ASM: ret
    put(bytes, 0x1fe4, &[0x83, 0x39, 0x01]); // ASM: cmp dword [rcx],1 (MB)
    put(bytes, 0x1fe7, &[0x0f, 0x94, 0xc3]); // ASM: sete bl
    put(bytes, 0x1fea, &[0xe8, 0xf1, 0xf1, 0xff, 0xff]); // ASM: call 0x11e0 (Q)
    put(bytes, 0x1fef, &[0x84, 0xdb]); // ASM: test bl,bl
    put(bytes, 0x1ff1, &[0x74, 0x06]); // ASM: jz 0x1ff9
    put(bytes, 0x1ff3, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5
    put(bytes, 0x1ff8, &[0xc3]); // ASM: ret
    put(bytes, 0x1ff9, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x1ffb, &[0xc3]); // ASM: ret
    put(bytes, 0x1660, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (CL2)
    put(bytes, 0x1663, &[0x48, 0x8d, 0x15, 0x96, 0x0a, 0x00, 0x00]); // ASM: lea rdx,[rip+0xa96] -> 0x2100
    put(bytes, 0x166a, &[0xc3]); // ASM: ret

    put(bytes, 0x4e20, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (LKC)
    put(bytes, 0x4e23, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x4e25, &[0x75, 0x21]); // ASM: jnz 0x4e48
    put(bytes, 0x4e27, &[0x48, 0x8d, 0x0d, 0x92, 0xdf, 0xff, 0xff]); // ASM: lea rcx,[rip-0x206e] -> 0x2dc0
    put(bytes, 0x4e2e, &[0x48, 0x8d, 0x15, 0xdb, 0xd5, 0xff, 0xff]); // ASM: lea rdx,[rip-0x2a25] -> 0x2410
    put(bytes, 0x4e35, &[0x41, 0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov r8d,7
    put(bytes, 0x4e3b, &[0x4c, 0x8d, 0x0d, 0x8e, 0xdf, 0xff, 0xff]); // ASM: lea r9,[rip-0x2072] -> 0x2dd0
    put(bytes, 0x4e42, &[0xff, 0x15, 0x08, 0xd2, 0xff, 0xff]); // ASM: call qword [rip-0x2df8] -> 0x2050 (ReportAssertFailure)
    put(bytes, 0x4e48, &[0xc3]); // ASM: ret
    put(bytes, 0x4e50, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (AIA)
    put(bytes, 0x4e53, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x4e55, &[0x75, 0x21]); // ASM: jnz 0x4e78
    put(bytes, 0x4e57, &[0x48, 0x8d, 0x0d, 0xd2, 0xdf, 0xff, 0xff]); // ASM: lea rcx,[rip-0x202e] -> 0x2e30
    put(bytes, 0x4e5e, &[0x48, 0x8d, 0x15, 0xab, 0xd5, 0xff, 0xff]); // ASM: lea rdx,[rip-0x2a55] -> 0x2410
    put(bytes, 0x4e65, &[0x41, 0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov r8d,7
    put(bytes, 0x4e6b, &[0x4c, 0x8d, 0x0d, 0xce, 0xdf, 0xff, 0xff]); // ASM: lea r9,[rip-0x2032] -> 0x2e40
    put(bytes, 0x4e72, &[0xff, 0x15, 0xd8, 0xd1, 0xff, 0xff]); // ASM: call qword [rip-0x2e28] -> 0x2050 (ReportAssertFailure)
    put(bytes, 0x4e78, &[0xc3]); // ASM: ret
    put(bytes, 0x4e80, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (ACA)
    put(bytes, 0x4e83, &[0x48, 0x8d, 0x15, 0xe6, 0xdf, 0xff, 0xff]); // ASM: lea rdx,[rip-0x201a] -> 0x2e70
    put(bytes, 0x4e8a, &[0xc3]); // ASM: ret
    put(bytes, 0x4e90, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (FW1)
    put(bytes, 0x4e94, &[0xb9, 0x77, 0x00, 0x00, 0x00]); // ASM: mov ecx,0x77
    put(bytes, 0x4e99, &[0xe8, 0x12, 0x00, 0x00, 0x00]); // ASM: call 0x4eb0 (FW2)
    put(bytes, 0x4e9e, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x4ea2, &[0xc3]); // ASM: ret
    put(bytes, 0x4eb0, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (FW2)
    put(bytes, 0x4eb4, &[0xe8, 0x07, 0x00, 0x00, 0x00]); // ASM: call 0x4ec0 (FW3)
    put(bytes, 0x4eb9, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x4ebd, &[0xc3]); // ASM: ret
    put(bytes, 0x4ec0, &[0x8b, 0x01]); // ASM: mov eax,[rcx] (FW3)
    put(bytes, 0x4ec2, &[0xc3]); // ASM: ret
    put(bytes, 0x4ed0, &[0x85, 0xc9]); // ASM: test ecx,ecx (CS)
    put(bytes, 0x4ed2, &[0x74, 0x1c]); // ASM: jz 0x4ef0
    put(bytes, 0x4ed4, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x4ed9, &[0xc3]); // ASM: ret
    put(bytes, 0x4ee0, &[0xb8, 0x09, 0x00, 0x00, 0x00]); // ASM: mov eax,9 (TH)
    put(bytes, 0x4ee5, &[0xc3]); // ASM: ret
    put(bytes, 0x4ef0, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x4ef5, &[0xc3]); // ASM: ret
    put(bytes, 0x4f00, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (LT)
    put(bytes, 0x4f04, &[0x48, 0x8d, 0x0d, 0xd5, 0xff, 0xff, 0xff]); // ASM: lea rcx,[rip-0x2b] -> 0x4ee0
    put(bytes, 0x4f0b, &[0xe8, 0xc0, 0xff, 0xff, 0xff]); // ASM: call 0x4ed0 (CS)
    put(bytes, 0x4f10, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x4f14, &[0xc3]); // ASM: ret
    put(bytes, 0x4f20, &[0x83, 0xf9, 0x04]); // ASM: cmp ecx,4 (JTX)
    put(bytes, 0x4f23, &[0x77, 0x27]); // ASM: ja DEF
    put(bytes, 0x4f25, &[0x48, 0x8d, 0x15, 0xd4, 0xc0, 0xff, 0xff]); // ASM: lea rdx,[0x1000]
    put(
        bytes,
        0x4f2c,
        &[0x0f, 0xb6, 0x84, 0x0a, 0xb0, 0x1e, 0x00, 0x00],
    ); // ASM: movzx eax,byte [rdx+rcx+0x1eb0]
    put(bytes, 0x4f34, &[0x8b, 0x8c, 0x82, 0xa0, 0x1e, 0x00, 0x00]); // ASM: mov ecx,[rdx+rax*4+0x1ea0]
    put(bytes, 0x4f3b, &[0x48, 0x03, 0xca]); // ASM: add rcx,rdx
    put(bytes, 0x4f3e, &[0xff, 0xe1]); // ASM: jmp rcx
    put(bytes, 0x4f40, &[0xb8, 0x46, 0x00, 0x00, 0x00]); // ASM: mov eax,70 (CASE0)
    put(bytes, 0x4f45, &[0xc3]); // ASM: ret
    put(bytes, 0x4f46, &[0xb8, 0x50, 0x00, 0x00, 0x00]); // ASM: mov eax,80 (CASE1)
    put(bytes, 0x4f4b, &[0xc3]); // ASM: ret
    put(bytes, 0x4f4c, &[0x31, 0xc0]); // ASM: xor eax,eax (DEF)
    put(bytes, 0x4f4e, &[0xc3]); // ASM: ret
    put(bytes, 0x4f60, &[0xe9, 0x5b, 0xff, 0xff, 0xff]); // ASM: jmp 0x4ec0 (TJ)
    put(bytes, 0x4f70, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (TC)
    put(bytes, 0x4f74, &[0xb9, 0x55, 0x00, 0x00, 0x00]); // ASM: mov ecx,0x55
    put(bytes, 0x4f79, &[0xba, 0x66, 0x00, 0x00, 0x00]); // ASM: mov edx,0x66
    put(bytes, 0x4f7e, &[0xe8, 0xdd, 0xff, 0xff, 0xff]); // ASM: call 0x4f60 (TJ)
    put(bytes, 0x4f83, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x4f87, &[0xc3]); // ASM: ret
    put(bytes, 0x4f90, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (PV)
    put(bytes, 0x4f94, &[0xb9, 0x07, 0x00, 0x00, 0x00]); // ASM: mov ecx,7
    put(bytes, 0x4f99, &[0xe8, 0x32, 0x00, 0x00, 0x00]); // ASM: call 0x4fd0 (PT)
    put(bytes, 0x4f9e, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x4fa2, &[0xc3]); // ASM: ret
    put(bytes, 0x4fb0, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (PW)
    put(bytes, 0x4fb4, &[0xb9, 0x09, 0x00, 0x00, 0x00]); // ASM: mov ecx,9
    put(bytes, 0x4fb9, &[0xe8, 0x12, 0x00, 0x00, 0x00]); // ASM: call 0x4fd0 (PT)
    put(bytes, 0x4fbe, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x4fc2, &[0xc3]); // ASM: ret
    put(bytes, 0x4fd0, &[0x8b, 0xc1]); // ASM: mov eax,ecx (PT)
    put(bytes, 0x4fd2, &[0xc3]); // ASM: ret
    put(bytes, 0x5000, &[0x8b, 0x01]); // ASM: mov eax,[rcx] (GZ)
    put(bytes, 0x5002, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x5004, &[0x75, 0x21]); // ASM: jnz 0x5027
    put(bytes, 0x5006, &[0x48, 0x8d, 0x0d, 0xe3, 0xe7, 0xff, 0xff]); // ASM: lea rcx,[rip-0x181d] -> 0x37f0
    put(bytes, 0x500d, &[0x48, 0x8d, 0x15, 0xfc, 0xd3, 0xff, 0xff]); // ASM: lea rdx,[rip-0x2c04] -> 0x2410
    put(bytes, 0x5014, &[0x41, 0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov r8d,7
    put(bytes, 0x501a, &[0x4c, 0x8d, 0x0d, 0x7f, 0xdf, 0xff, 0xff]); // ASM: lea r9,[rip-0x2081] -> 0x2fa0
    put(bytes, 0x5021, &[0xff, 0x15, 0x29, 0xd0, 0xff, 0xff]); // ASM: call qword [rip-0x2fd7] -> 0x2050 (ReportAssertFailure)
    put(bytes, 0x5027, &[0xc3]); // ASM: ret
    put(bytes, 0x5040, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (GG)
    put(bytes, 0x5043, &[0x85, 0xc0]); // ASM: test eax,eax
    put(bytes, 0x5045, &[0x75, 0x27]); // ASM: jnz 0x506e
    put(bytes, 0x5047, &[0xff, 0x15, 0x03, 0xd0, 0xff, 0xff]); // ASM: call qword [rip-0x2ffd] -> 0x2050 (ReportAssertFailure)
    put(bytes, 0x504d, &[0x48, 0x8d, 0x0d, 0x6c, 0xdf, 0xff, 0xff]); // ASM: lea rcx,[rip-0x2094] -> 0x2fc0
    put(bytes, 0x5054, &[0x48, 0x8d, 0x15, 0xb5, 0xd3, 0xff, 0xff]); // ASM: lea rdx,[rip-0x2c4b] -> 0x2410
    put(bytes, 0x505b, &[0x41, 0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov r8d,7
    put(bytes, 0x5061, &[0x4c, 0x8d, 0x0d, 0x68, 0xdf, 0xff, 0xff]); // ASM: lea r9,[rip-0x2098] -> 0x2fd0
    put(bytes, 0x5068, &[0xff, 0x15, 0xe2, 0xcf, 0xff, 0xff]); // ASM: call qword [rip-0x301e] -> 0x2050 (ReportAssertFailure)
    put(bytes, 0x506e, &[0xc3]); // ASM: ret
    put(bytes, 0x5080, &[0x48, 0x8d, 0x0d, 0x79, 0xe7, 0xff, 0xff]); // ASM: lea rcx,[rip-0x1887] -> 0x3800 (SN)
    put(bytes, 0x5087, &[0xc3]); // ASM: ret
    put(bytes, 0x50a0, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (WS)
    put(bytes, 0x50a3, &[0x48, 0x8d, 0x15, 0x56, 0xe8, 0xff, 0xff]); // ASM: lea rdx,[rip-0x17aa] -> 0x3900
    put(bytes, 0x50aa, &[0xc3]); // ASM: ret
    put(bytes, 0x50b0, &[0x41, 0x8b, 0xc0]); // ASM: mov eax,r8d (WR)
    put(bytes, 0x50b3, &[0xc3]); // ASM: ret
    put(bytes, 0x50c0, &[0x48, 0x83, 0xec, 0x48]); // ASM: sub rsp,0x48 (EC)
    put(bytes, 0x50c4, &[0x48, 0x89, 0x5c, 0x24, 0x38]); // ASM: mov [rsp+0x38],rbx
    put(bytes, 0x50c9, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx
    put(bytes, 0x50cc, &[0x48, 0x89, 0x54, 0x24, 0x30]); // ASM: mov [rsp+0x30],rdx
    put(bytes, 0x50d1, &[0x8b, 0x43, 0x20]); // ASM: mov eax,[rbx+0x20]
    put(bytes, 0x50d4, &[0x89, 0x44, 0x24, 0x20]); // ASM: mov [rsp+0x20],eax
    put(bytes, 0x50d8, &[0x48, 0x8b, 0xca]); // ASM: mov rcx,rdx
    put(bytes, 0x50db, &[0xe8, 0xc0, 0xff, 0xff, 0xff]); // ASM: call 0x50a0 (WS)
    put(bytes, 0x50e0, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x50e3, &[0x48, 0x8d, 0x54, 0x24, 0x20]); // ASM: lea rdx,[rsp+0x20]
    put(bytes, 0x50e8, &[0x41, 0xb8, 0x20, 0x00, 0x00, 0x00]); // ASM: mov r8d,32
    put(bytes, 0x50ee, &[0xe8, 0xbd, 0xff, 0xff, 0xff]); // ASM: call 0x50b0 (WR)
    put(bytes, 0x50f3, &[0x0f, 0xb6, 0x43, 0x24]); // ASM: movzx eax,byte [rbx+0x24]
    put(bytes, 0x50f7, &[0x89, 0x44, 0x24, 0x28]); // ASM: mov [rsp+0x28],eax
    put(bytes, 0x50fb, &[0x48, 0x8b, 0x4c, 0x24, 0x30]); // ASM: mov rcx,[rsp+0x30]
    put(bytes, 0x5100, &[0xe8, 0x9b, 0xff, 0xff, 0xff]); // ASM: call 0x50a0 (WS)
    put(bytes, 0x5105, &[0x48, 0x8b, 0xc8]); // ASM: mov rcx,rax
    put(bytes, 0x5108, &[0x48, 0x8d, 0x54, 0x24, 0x28]); // ASM: lea rdx,[rsp+0x28]
    put(bytes, 0x510d, &[0x41, 0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov r8d,1
    put(bytes, 0x5113, &[0xe8, 0x98, 0xff, 0xff, 0xff]); // ASM: call 0x50b0 (WR)
    put(bytes, 0x5118, &[0x48, 0x8b, 0x5c, 0x24, 0x38]); // ASM: mov rbx,[rsp+0x38]
    put(bytes, 0x511d, &[0x48, 0x83, 0xc4, 0x48]); // ASM: add rsp,0x48
    put(bytes, 0x5121, &[0xc3]); // ASM: ret
    put(bytes, 0x5130, &[0xf3, 0x0f, 0x10, 0x41, 0x10]); // ASM: movss xmm0,[rcx+0x10] (FF)
    put(bytes, 0x5135, &[0xf3, 0x0f, 0x59, 0x41, 0x14]); // ASM: mulss xmm0,[rcx+0x14]
    put(bytes, 0x513a, &[0x48, 0x8d, 0x15, 0x1f, 0xe8, 0xff, 0xff]); // ASM: lea rdx,[rip-0x17e1] -> 0x3960
    put(bytes, 0x5141, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x5150,
        &[0x48, 0xc7, 0x41, 0x10, 0x00, 0x00, 0x00, 0x00],
    ); // ASM: mov qword [rcx+0x10],0 (FZ)
    put(bytes, 0x5158, &[0x48, 0x8d, 0x15, 0x21, 0xe8, 0xff, 0xff]); // ASM: lea rdx,[rip-0x17df] -> 0x3980
    put(bytes, 0x515f, &[0xc3]); // ASM: ret
    put(bytes, 0x5170, &[0xf3, 0x0f, 0x10, 0x41, 0x10]); // ASM: movss xmm0,[rcx+0x10] (FG)
    put(bytes, 0x5175, &[0x48, 0x8d, 0x15, 0x24, 0xe8, 0xff, 0xff]); // ASM: lea rdx,[rip-0x17dc] -> 0x39a0
    put(bytes, 0x517c, &[0xc3]); // ASM: ret
    put(bytes, 0x5190, &[0x48, 0x83, 0xec, 0x28]); // ASM: sub rsp,0x28 (RG)
    put(bytes, 0x5194, &[0x48, 0x8d, 0x15, 0x25, 0xe8, 0xff, 0xff]); // ASM: lea rdx,[rip-0x17db] -> 0x39c0
    put(bytes, 0x519b, &[0x41, 0xb8, 0x44, 0x43, 0x42, 0x41]); // ASM: mov r8d,0x41424344
    put(bytes, 0x51a1, &[0xe8, 0x0a, 0xff, 0xff, 0xff]); // ASM: call 0x50b0 (WR)
    put(bytes, 0x51a6, &[0x48, 0x83, 0xc4, 0x28]); // ASM: add rsp,0x28
    put(bytes, 0x51aa, &[0xc3]); // ASM: ret
    put(bytes, 0x51c0, &[0x85, 0xc9]); // ASM: test ecx,ecx (HG)
    put(bytes, 0x51c2, &[0x74, 0x1c]); // ASM: jz 0x51e0
    put(bytes, 0x51c4, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x51c9, &[0xc3]); // ASM: ret
    put(bytes, 0x51d0, &[0xb8, 0x63, 0x00, 0x00, 0x00]); // ASM: mov eax,99 (HD)
    put(bytes, 0x51d5, &[0xc3]); // ASM: ret
    put(bytes, 0x51e0, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x51e5, &[0xc3]); // ASM: ret
    put(bytes, 0x5200, &[0x8b, 0x41, 0x10]); // ASM: mov eax,[rcx+0x10] (CM)
    put(bytes, 0x5203, &[0x03, 0x41, 0x14]); // ASM: add eax,[rcx+0x14]
    put(bytes, 0x5206, &[0x03, 0x41, 0x18]); // ASM: add eax,[rcx+0x18]
    put(bytes, 0x5209, &[0x03, 0x44, 0xd1, 0x10]); // ASM: add eax,[rcx+rdx*8+0x10]
    put(bytes, 0x520d, &[0xc3]); // ASM: ret
    put(bytes, 0x5240, &[0xff, 0xc1]); // ASM: inc ecx (LB)
    put(bytes, 0x5242, &[0xe9, 0x11, 0x00, 0x00, 0x00]); // ASM: jmp 0x5258
    put(bytes, 0x5247, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x5249, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x524b, &[0x0f, 0x82, 0x0e, 0x00, 0x00, 0x00]); // ASM: jb 0x525f
    put(bytes, 0x5251, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x5253, &[0xe9, 0x2f, 0x00, 0x00, 0x00]); // ASM: jmp 0x5287
    put(bytes, 0x5258, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x525a, &[0xe9, 0x14, 0x00, 0x00, 0x00]); // ASM: jmp 0x5273
    put(bytes, 0x525f, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x5261, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x5263, &[0x0f, 0x82, 0x14, 0x00, 0x00, 0x00]); // ASM: jb 0x527d
    put(bytes, 0x5269, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x526b, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x526d, &[0x0f, 0x82, 0xd4, 0xff, 0xff, 0xff]); // ASM: jb 0x5247
    put(bytes, 0x5273, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x5275, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x5277, &[0x0f, 0x82, 0xe2, 0xff, 0xff, 0xff]); // ASM: jb 0x525f
    put(bytes, 0x527d, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x527f, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x5281, &[0x0f, 0x82, 0xca, 0xff, 0xff, 0xff]); // ASM: jb 0x5251
    put(bytes, 0x5287, &[0xff, 0xc1]); // ASM: inc ecx
    put(bytes, 0x5289, &[0xe9, 0xf9, 0xff, 0xff, 0xff]); // ASM: jmp 0x5287
    put(bytes, 0x52a0, &[0x85, 0xc9]); // ASM: test ecx,ecx (JO)
    put(bytes, 0x52a2, &[0x0f, 0x84, 0x58, 0xdd, 0xff, 0xff]); // ASM: jz 0x3000
    put(bytes, 0x52a8, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x52aa, &[0xc3]); // ASM: ret
    put(bytes, 0x52c0, &[0xe8, 0x3b, 0x00, 0x00, 0x00]); // ASM: call 0x5300 (BC)
    put(bytes, 0x52c5, &[0xe9, 0x0d, 0x00, 0x00, 0x00]); // ASM: jmp 0x52d7
    put(bytes, 0x52ca, &[0xe8, 0x37, 0x00, 0x00, 0x00]); // ASM: call 0x5306
    put(bytes, 0x52cf, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x52d1, &[0x0f, 0x82, 0xe9, 0xff, 0xff, 0xff]); // ASM: jb 0x52c0
    put(bytes, 0x52d7, &[0xe8, 0x30, 0x00, 0x00, 0x00]); // ASM: call 0x530c
    put(bytes, 0x52dc, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x52de, &[0x0f, 0x82, 0xe6, 0xff, 0xff, 0xff]); // ASM: jb 0x52ca
    put(bytes, 0x52e4, &[0xe8, 0x29, 0x00, 0x00, 0x00]); // ASM: call 0x5312
    put(bytes, 0x52e9, &[0xc3]); // ASM: ret
    put(bytes, 0x5300, &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret
    put(bytes, 0x5306, &[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,2; ret
    put(bytes, 0x530c, &[0xb8, 0x03, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,3; ret
    put(bytes, 0x5312, &[0xb8, 0x04, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,4; ret
    put(bytes, 0x5320, &[0xe8, 0x3b, 0x00, 0x00, 0x00]); // ASM: call 0x5360 (NL)
    put(bytes, 0x5325, &[0xe9, 0x00, 0x00, 0x00, 0x00]); // ASM: jmp 0x532a
    put(bytes, 0x532a, &[0xe8, 0x37, 0x00, 0x00, 0x00]); // ASM: call 0x5366
    put(bytes, 0x532f, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x5331, &[0x0f, 0x82, 0xf3, 0xff, 0xff, 0xff]); // ASM: jb 0x532a
    put(bytes, 0x5337, &[0xe8, 0x30, 0x00, 0x00, 0x00]); // ASM: call 0x536c
    put(bytes, 0x533c, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x533e, &[0x0f, 0x82, 0xdc, 0xff, 0xff, 0xff]); // ASM: jb 0x5320
    put(bytes, 0x5344, &[0xe8, 0x29, 0x00, 0x00, 0x00]); // ASM: call 0x5372
    put(bytes, 0x5349, &[0x3b, 0xca]); // ASM: cmp ecx,edx
    put(bytes, 0x534b, &[0x0f, 0x82, 0xd9, 0xff, 0xff, 0xff]); // ASM: jb 0x532a
    put(bytes, 0x5351, &[0xe8, 0x22, 0x00, 0x00, 0x00]); // ASM: call 0x5378
    put(bytes, 0x5356, &[0xe9, 0xf6, 0xff, 0xff, 0xff]); // ASM: jmp 0x5351
    put(bytes, 0x5360, &[0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,5; ret
    put(bytes, 0x5366, &[0xb8, 0x06, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,6; ret
    put(bytes, 0x536c, &[0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,7; ret
    put(bytes, 0x5372, &[0xb8, 0x08, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,8; ret
    put(bytes, 0x5378, &[0xb8, 0x09, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,9; ret
    put(
        bytes,
        0x5390,
        &[
            0xb9, 0x01, 0x00, 0x00, 0x00, 0xe8, 0xab, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0x86, 0x00, 0x00, 0x00,
        ],
    ); // ASM: mov ecx,1; call 0x5445; cmp ecx,edx; jb 0x5428 (NB)
    put(
        bytes,
        0x53a2,
        &[
            0xb9, 0x02, 0x00, 0x00, 0x00, 0xe8, 0x99, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0xdc, 0xff, 0xff, 0xff,
        ],
    ); // ASM: mov ecx,2; call 0x5445; cmp ecx,edx; jb 0x5390
    put(
        bytes,
        0x53b4,
        &[
            0xb9, 0x03, 0x00, 0x00, 0x00, 0xe8, 0x87, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0x74, 0x00, 0x00, 0x00,
        ],
    ); // ASM: mov ecx,3; call 0x5445; cmp ecx,edx; jb 0x543a
    put(
        bytes,
        0x53c6,
        &[
            0xb9, 0x04, 0x00, 0x00, 0x00, 0xe8, 0x75, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0x2f, 0x00, 0x00, 0x00,
        ],
    ); // ASM: mov ecx,4; call 0x5445; cmp ecx,edx; jb 0x5407
    put(
        bytes,
        0x53d8,
        &[
            0xb9, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x63, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0xb8, 0xff, 0xff, 0xff,
        ],
    ); // ASM: mov ecx,5; call 0x5445; cmp ecx,edx; jb 0x53a2
    put(
        bytes,
        0x53ea,
        &[
            0xb9, 0x06, 0x00, 0x00, 0x00, 0xe8, 0x51, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0x94, 0xff, 0xff, 0xff,
        ],
    ); // ASM: mov ecx,6; call 0x5445; cmp ecx,edx; jb 0x5390
    put(
        bytes,
        0x53fc,
        &[
            0xb9, 0x07, 0x00, 0x00, 0x00, 0xe8, 0x3f, 0x00, 0x00, 0x00, 0xc3,
        ],
    ); // ASM: mov ecx,7; call 0x5445; ret
    put(
        bytes,
        0x5407,
        &[
            0xb9, 0x08, 0x00, 0x00, 0x00, 0xe8, 0x34, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0x77, 0xff, 0xff, 0xff,
        ],
    ); // ASM: mov ecx,8; call 0x5445; cmp ecx,edx; jb 0x5390
    put(
        bytes,
        0x5419,
        &[
            0xb9, 0x09, 0x00, 0x00, 0x00, 0xe8, 0x22, 0x00, 0x00, 0x00, 0xe9, 0x00, 0x00, 0x00,
            0x00,
        ],
    ); // ASM: mov ecx,9; call 0x5445; jmp 0x5428
    put(
        bytes,
        0x5428,
        &[
            0xb9, 0x0a, 0x00, 0x00, 0x00, 0xe8, 0x13, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0xee, 0xff, 0xff, 0xff,
        ],
    ); // ASM: mov ecx,10; call 0x5445; cmp ecx,edx; jb 0x5419
    put(
        bytes,
        0x543a,
        &[
            0xb9, 0x0b, 0x00, 0x00, 0x00, 0xe8, 0x01, 0x00, 0x00, 0x00, 0xc3,
        ],
    ); // ASM: mov ecx,11; call 0x5445; ret
    put(bytes, 0x5445, &[0x8b, 0xc1, 0xc3]); // ASM: mov eax,ecx; ret
    put(
        bytes,
        0x5450,
        &[
            0xb9, 0x01, 0x00, 0x00, 0x00, 0xe8, 0x73, 0x00, 0x00, 0x00, 0xe9, 0x30, 0x00, 0x00,
            0x00,
        ],
    ); // ASM: mov ecx,1; call 0x54cd; jmp 0x548f (SL)
    put(
        bytes,
        0x545f,
        &[
            0xb9, 0x02, 0x00, 0x00, 0x00, 0xe8, 0x64, 0x00, 0x00, 0x00, 0xe9, 0x0f, 0x00, 0x00,
            0x00,
        ],
    ); // ASM: mov ecx,2; call 0x54cd; jmp 0x547d
    put(
        bytes,
        0x546e,
        &[
            0xb9, 0x03, 0x00, 0x00, 0x00, 0xe8, 0x55, 0x00, 0x00, 0x00, 0xe9, 0xe2, 0xff, 0xff,
            0xff,
        ],
    ); // ASM: mov ecx,3; call 0x54cd; jmp 0x545f
    put(
        bytes,
        0x547d,
        &[
            0xb9, 0x04, 0x00, 0x00, 0x00, 0xe8, 0x46, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0xd0, 0xff, 0xff, 0xff,
        ],
    ); // ASM: mov ecx,4; call 0x54cd; cmp ecx,edx; jb 0x545f
    put(
        bytes,
        0x548f,
        &[
            0xb9, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x34, 0x00, 0x00, 0x00, 0xe9, 0x12, 0x00, 0x00,
            0x00,
        ],
    ); // ASM: mov ecx,5; call 0x54cd; jmp 0x54b0
    put(
        bytes,
        0x549e,
        &[
            0xb9, 0x06, 0x00, 0x00, 0x00, 0xe8, 0x25, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0xbe, 0xff, 0xff, 0xff,
        ],
    ); // ASM: mov ecx,6; call 0x54cd; cmp ecx,edx; jb 0x546e
    put(
        bytes,
        0x54b0,
        &[
            0xb9, 0x07, 0x00, 0x00, 0x00, 0xe8, 0x13, 0x00, 0x00, 0x00, 0x3b, 0xca, 0x0f, 0x82,
            0xdc, 0xff, 0xff, 0xff,
        ],
    ); // ASM: mov ecx,7; call 0x54cd; cmp ecx,edx; jb 0x549e
    put(
        bytes,
        0x54c2,
        &[
            0xb9, 0x08, 0x00, 0x00, 0x00, 0xe8, 0x01, 0x00, 0x00, 0x00, 0xc3,
        ],
    ); // ASM: mov ecx,8; call 0x54cd; ret
    put(bytes, 0x54cd, &[0x8b, 0xc1, 0xc3]); // ASM: mov eax,ecx; ret
    put(bytes, 0x54e0, &[0x0f, 0x10, 0x41, 0x10]); // ASM: movups xmm0,[rcx+0x10] (MS)
    put(bytes, 0x54e4, &[0xf3, 0x0f, 0x10, 0x4a, 0x20]); // ASM: movss xmm1,[rdx+0x20]
    put(bytes, 0x54e9, &[0xf3, 0x0f, 0x10, 0xc1]); // ASM: movss xmm0,xmm1
    put(bytes, 0x54ed, &[0x0f, 0x11, 0x41, 0x30]); // ASM: movups [rcx+0x30],xmm0
    put(bytes, 0x54f1, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x5500,
        &[
            0xb9, 0x01, 0x00, 0x00, 0x00, 0xe8, 0x35, 0x00, 0x00, 0x00, 0xe9, 0x16, 0x00, 0x00,
            0x00,
        ],
    ); // ASM: mov ecx,1; call 0x553f; jmp 0x5525 (SW)
    put(
        bytes,
        0x550f,
        &[
            0xb9, 0x02, 0x00, 0x00, 0x00, 0xe8, 0x26, 0x00, 0x00, 0x00, 0xc3,
        ],
    ); // ASM: mov ecx,2; call 0x553f; ret
    put(
        bytes,
        0x551a,
        &[
            0xb9, 0x03, 0x00, 0x00, 0x00, 0xe8, 0x1b, 0x00, 0x00, 0x00, 0xc3,
        ],
    ); // ASM: mov ecx,3; call 0x553f; ret
    put(
        bytes,
        0x5525,
        &[
            0xb9, 0x04, 0x00, 0x00, 0x00, 0xe8, 0x10, 0x00, 0x00, 0x00, 0x83, 0xf8, 0x02, 0x0f,
            0x87, 0xc8, 0xff, 0xff, 0xff, 0xff, 0x24, 0xc5, 0xd0, 0x21, 0x00, 0x00,
        ],
    ); // ASM: mov ecx,4; call 0x553f; cmp eax,2; ja 0x5500; jmp qword [rax*8+0x21d0]
    put(bytes, 0x553f, &[0x8b, 0xc1, 0xc3]); // ASM: mov eax,ecx; ret
    put(bytes, 0x5550, &[0xb9, 0x07, 0x00, 0x00, 0x00]); // ASM: mov ecx,7 (TR)
    put(bytes, 0x5555, &[0xe9, 0x06, 0x00, 0x00, 0x00]); // ASM: jmp 0x5560
    put(bytes, 0x5560, &[0x8b, 0xc1, 0xc3]); // ASM: mov eax,ecx; ret (TG)
    put(bytes, 0x5570, &[0xe8, 0xdb, 0xff, 0xff, 0xff]); // ASM: call 0x5550 (TC)
    put(bytes, 0x5575, &[0xe8, 0xe6, 0xff, 0xff, 0xff]); // ASM: call 0x5560
    put(bytes, 0x557a, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x557c, &[0xc3]); // ASM: ret
    put(bytes, 0x5580, &[0xf3, 0x0f, 0x59, 0xc9]); // ASM: mulss xmm1,xmm1 (FP)
    put(bytes, 0x5584, &[0xf3, 0x0f, 0x11, 0x09]); // ASM: movss [rcx],xmm1
    put(bytes, 0x5588, &[0xc3]); // ASM: ret
    put(bytes, 0x5590, &[0x48, 0x8b, 0xca]); // ASM: mov rcx,rdx (FC)
    put(bytes, 0x5593, &[0xf3, 0x0f, 0x10, 0x0a]); // ASM: movss xmm1,[rdx]
    put(bytes, 0x5597, &[0xe8, 0xe4, 0xff, 0xff, 0xff]); // ASM: call 0x5580
    put(bytes, 0x559c, &[0xc3]); // ASM: ret
    // UT 0x55c0: the fields of the object the global at 0x3400 points at.
    put(bytes, 0x55c0, &[0x48, 0x8b, 0x05, 0x39, 0xde, 0xff, 0xff]); // ASM: mov rax,[rip+..] -> 0x3400 (UT)
    put(bytes, 0x55c7, &[0x8b, 0x48, 0x18]); // ASM: mov ecx,[rax+0x18]
    put(bytes, 0x55ca, &[0x03, 0x48, 0x1c]); // ASM: add ecx,[rax+0x1c]
    put(bytes, 0x55cd, &[0x89, 0x48, 0x20]); // ASM: mov [rax+0x20],ecx
    put(bytes, 0x55d0, &[0x8b, 0x40, 0x18]); // ASM: mov eax,[rax+0x18]
    put(bytes, 0x55d3, &[0xc3]); // ASM: ret
    // EN 0x55e0: a function comparing the dword global at 0x3420 against
    // constants, for a user-applied enum to name.
    put(bytes, 0x55e0, &[0x8b, 0x05, 0x3a, 0xde, 0xff, 0xff]); // ASM: mov eax,[rip+..] -> 0x3420 (EN)
    put(bytes, 0x55e6, &[0x83, 0xf8, 0x01]); // ASM: cmp eax,1
    put(bytes, 0x55e9, &[0x74, 0x09]); // ASM: je 0x55f4
    put(bytes, 0x55eb, &[0x83, 0xf8, 0x02]); // ASM: cmp eax,2
    put(bytes, 0x55ee, &[0x74, 0x0a]); // ASM: je 0x55fa
    put(bytes, 0x55f0, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x55f2, &[0xc3]); // ASM: ret
    put(bytes, 0x55f4, &[0xb8, 0x0a, 0x00, 0x00, 0x00]); // ASM: mov eax,10
    put(bytes, 0x55f9, &[0xc3]); // ASM: ret
    put(bytes, 0x55fa, &[0xb8, 0x14, 0x00, 0x00, 0x00]); // ASM: mov eax,20
    put(bytes, 0x55ff, &[0xc3]); // ASM: ret
    // RM 0x5640 stores a table whose slot 1 holds a datum: the reading
    // skips it and keeps F1 at the index its byte offset gives.
    put(
        bytes,
        0x5640,
        &[0x48, 0xb8, 0x30, 0x37, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,0x3730 (RM)
    put(bytes, 0x564a, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x564d, &[0xc3]); // ASM: ret
    put(bytes, 0x5650, &[0xb8, 0x03, 0x00, 0x00, 0x00]); // ASM: mov eax,3 (F0)
    put(bytes, 0x5655, &[0xc3]); // ASM: ret
    put(bytes, 0x5660, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (F1)
    put(bytes, 0x5663, &[0xff, 0x10]); // ASM: call [rax]
    put(bytes, 0x5665, &[0xc3]); // ASM: ret
    // R1 0x5600 and R2 0x5680 store the locator-named tables at 0x3678
    // (`Ns::Rtti`) and 0x3718 (`Ns::Solo`), the second with one slot.
    put(
        bytes,
        0x5600,
        &[0x48, 0xb8, 0x78, 0x36, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,0x3678 (R1)
    put(bytes, 0x560a, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x560d, &[0xc3]); // ASM: ret
    put(bytes, 0x5620, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5 (M0)
    put(bytes, 0x5625, &[0xc3]); // ASM: ret
    put(bytes, 0x5630, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (M1)
    put(bytes, 0x5633, &[0xff, 0x10]); // ASM: call [rax]
    put(bytes, 0x5635, &[0xc3]); // ASM: ret
    put(bytes, 0x5680, &[0x48, 0x89, 0xcb]); // ASM: mov rbx,rcx (R2)
    put(
        bytes,
        0x5683,
        &[0x48, 0xb8, 0x18, 0x37, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,0x3718
    put(bytes, 0x568d, &[0x48, 0x89, 0x03]); // ASM: mov [rbx],rax
    put(bytes, 0x5690, &[0x48, 0x89, 0xd9]); // ASM: mov rcx,rbx
    put(bytes, 0x5693, &[0xe8, 0x18, 0x00, 0x00, 0x00]); // ASM: call 0x56b0 (X)
    put(bytes, 0x5698, &[0xc3]); // ASM: ret
    put(bytes, 0x56a0, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (S0)
    put(bytes, 0x56a3, &[0xc3]); // ASM: ret
    put(bytes, 0x56b0, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx] (X)
    put(bytes, 0x56b3, &[0xff, 0x10]); // ASM: call [rax]
    put(bytes, 0x56b5, &[0xc3]); // ASM: ret
    // EF 0x56c0: a function comparing the dword field at offset 8 of the
    // object the global at 0x3490 points at, for a user-applied struct with
    // an enum-typed field to name.
    put(bytes, 0x56c0, &[0x48, 0x8b, 0x05, 0xc9, 0xdd, 0xff, 0xff]); // ASM: mov rax,[rip+..] -> 0x3490 (EF)
    put(bytes, 0x56c7, &[0x8b, 0x48, 0x08]); // ASM: mov ecx,[rax+8]
    put(bytes, 0x56ca, &[0x83, 0xf9, 0x01]); // ASM: cmp ecx,1
    put(bytes, 0x56cd, &[0x74, 0x09]); // ASM: je 0x56d8
    put(bytes, 0x56cf, &[0x83, 0xf9, 0x02]); // ASM: cmp ecx,2
    put(bytes, 0x56d2, &[0x74, 0x0a]); // ASM: je 0x56de
    put(bytes, 0x56d4, &[0x33, 0xc0]); // ASM: xor eax,eax
    put(bytes, 0x56d6, &[0xc3]); // ASM: ret
    put(bytes, 0x56d8, &[0xb8, 0x0a, 0x00, 0x00, 0x00]); // ASM: mov eax,10
    put(bytes, 0x56dd, &[0xc3]); // ASM: ret
    put(bytes, 0x56de, &[0xb8, 0x14, 0x00, 0x00, 0x00]); // ASM: mov eax,20
    put(bytes, 0x56e3, &[0xc3]); // ASM: ret
    // RW 0x5700 stores `Ns::Wide`'s table at `[this]` and its further
    // base `Ns::Tail`'s at `[this+0x10]`, whose slots (`T0` 0x5740,
    // `T1` 0x5750) are Tail's methods in this image.
    put(
        bytes,
        0x5700,
        &[0x48, 0xb8, 0xb0, 0x32, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,0x32b0 (RW)
    put(bytes, 0x570a, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(
        bytes,
        0x570d,
        &[0x48, 0xb8, 0xf0, 0x32, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,0x32f0
    put(bytes, 0x5717, &[0x48, 0x89, 0x41, 0x10]); // ASM: mov [rcx+0x10],rax
    put(bytes, 0x571b, &[0xc3]); // ASM: ret
    put(bytes, 0x5720, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,7 (W0)
    put(bytes, 0x5725, &[0xc3]); // ASM: ret
    put(bytes, 0x5730, &[0xb8, 0x08, 0x00, 0x00, 0x00]); // ASM: mov eax,8 (W1)
    put(bytes, 0x5735, &[0xc3]); // ASM: ret
    put(bytes, 0x5740, &[0x8b, 0x41, 0x04]); // ASM: mov eax,[rcx+4] (T0)
    put(bytes, 0x5743, &[0xc3]); // ASM: ret
    put(bytes, 0x5750, &[0x8b, 0x41, 0x08]); // ASM: mov eax,[rcx+8] (T1)
    put(bytes, 0x5753, &[0xc3]); // ASM: ret
    checks::code(bytes);
    vcall::code(bytes);
    interlocked::code(bytes);
}

/// Lays down the fixture's `.rdata`: tables, pointers, strings and imports.
///
/// Split out of [`fixture`] for the same reason as [`code_bytes`].
///
/// # Arguments
///
/// * `bytes` - The image being built, `.rdata` at file offset 0x1000.
fn data_bytes(bytes: &mut [u8]) {
    for (i, t) in [0x1090u64, 0x10a0, 0x10b0, 0x10c0].iter().enumerate() {
        put_rdata(bytes, 0x2000 + (i as u64) * 8, &t.to_le_bytes());
    }
    put_rdata(bytes, 0x2030, &0x10e0u64.to_le_bytes());
    put_rdata(bytes, 0x2038, &0x1210u64.to_le_bytes());
    put_rdata(bytes, 0x2040, b"hello, borer world\0");
    put_rdata(bytes, 0x2058, &0x1220u64.to_le_bytes());
    put_rdata(bytes, 0x2060, &0x1230u64.to_le_bytes());
    put_rdata(bytes, 0x2068, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2090, &0x15e0u64.to_le_bytes());
    put_rdata(bytes, 0x2098, &0x1640u64.to_le_bytes());
    put_rdata(bytes, 0x20e0, b"void __cdecl Cls::Set(int)\0");
    put_rdata(bytes, 0x2100, b"bool __cdecl Cls::Has(int) const\0");
    put_rdata(bytes, 0x2130, &0x1660u64.to_le_bytes());
    put_rdata(bytes, 0x2140, b"int __cdecl Other::Get(void) const\0");
    put_rdata(bytes, 0x2170, &0x1670u64.to_le_bytes());
    put_rdata(bytes, 0x2180, b"class Util::String __cdecl Name::Of(int)\0");
    put_rdata(bytes, 0x21b0, &0x1680u64.to_le_bytes());
    put_rdata(bytes, 0x21b8, &0x1690u64.to_le_bytes());
    put_rdata(bytes, 0x21c0, &0x16b0u64.to_le_bytes());
    put_rdata(bytes, 0x21c8, &0x16c0u64.to_le_bytes());
    put_rdata(bytes, 0x2200, &0x16d0u64.to_le_bytes());
    put_rdata(bytes, 0x2208, &0x16f0u64.to_le_bytes());
    put_rdata(bytes, 0x2210, &0x1710u64.to_le_bytes());
    put_rdata(bytes, 0x2218, &0x1730u64.to_le_bytes());
    put_rdata(bytes, 0x2220, b"__cdecl Base::Base(void)\0");
    put_rdata(bytes, 0x2240, b"__cdecl Der::Der(void)\0");
    put_rdata(bytes, 0x2260, b"__cdecl Der::~Der(void)\0");
    put_rdata(bytes, 0x2280, &0x1200u64.to_le_bytes());
    put_rdata(bytes, 0x2288, &0x11e0u64.to_le_bytes());
    put_rdata(bytes, 0x2290, &0u64.to_le_bytes());
    put_rdata(bytes, 0x22a0, &0x1870u64.to_le_bytes());
    put_rdata(bytes, 0x22a8, &0x1200u64.to_le_bytes());
    put_rdata(bytes, 0x22b0, &0u64.to_le_bytes());
    put_rdata(bytes, 0x22c0, &0x1740u64.to_le_bytes());
    put_rdata(bytes, 0x22c8, &0x1200u64.to_le_bytes());
    put_rdata(bytes, 0x22d0, &0u64.to_le_bytes());
    put_rdata(bytes, 0x22d8, b"int __cdecl Der2::Foo(void)\0");
    put_rdata(bytes, 0x2300, &0x1740u64.to_le_bytes());
    put_rdata(bytes, 0x2308, &0x1750u64.to_le_bytes());
    put_rdata(bytes, 0x2310, b"void __cdecl Der::Run(void)\0");
    put_rdata(bytes, 0x2330, &0x1770u64.to_le_bytes());
    put_rdata(bytes, 0x2340, b"class Der *__cdecl Fac::Get(void)\0");
    put_rdata(bytes, 0x2368, &0x1780u64.to_le_bytes());
    put_rdata(bytes, 0x2370, &0x17a0u64.to_le_bytes());
    put_rdata(bytes, 0x2378, &0x17b0u64.to_le_bytes());
    put_rdata(bytes, 0x2388, &0x17d0u64.to_le_bytes());
    put_rdata(
        bytes,
        0x2390,
        b"void __cdecl Der::Use(const class Core::Ptr<class Der> &)\0",
    );
    put_rdata(bytes, 0x23d0, b"int __cdecl Pk::Pick(int)\0");
    put_rdata(bytes, 0x23f0, &0x17f0u64.to_le_bytes());
    put_rdata(bytes, 0x23f8, &0x1800u64.to_le_bytes());
    put_rdata(bytes, 0x2400, b"f.IsValid()\0");
    put_rdata(bytes, 0x2410, b"C:\\ws\\code\\foundation\\util/fourcc.h\0");
    put_rdata(bytes, 0x2440, b"void __cdecl As::Chk(void)\0");
    put_rdata(bytes, 0x2460, &0x1810u64.to_le_bytes());
    put_rdata(bytes, 0x2470, b"void __cdecl Ag::Run(void)\0");
    put_rdata(bytes, 0x2490, &0x1840u64.to_le_bytes());
    put_rdata(bytes, 0x2498, &0x1870u64.to_le_bytes());
    put_rdata(bytes, 0x24a0, &0x1880u64.to_le_bytes());
    put_rdata(bytes, 0x24a8, &0x1890u64.to_le_bytes());
    put_rdata(bytes, 0x24b0, &0x18a0u64.to_le_bytes());
    put_rdata(bytes, 0x24b8, &0x18b0u64.to_le_bytes());
    put_rdata(bytes, 0x24c0, b"void __cdecl Der::Tick(void)\0");
    put_rdata(bytes, 0x24e0, &0x18c0u64.to_le_bytes());
    put_rdata(bytes, 0x24e8, &0x18d0u64.to_le_bytes());
    put_rdata(bytes, 0x2500, b"void __cdecl Der::Poll(void)\0");
    put_rdata(bytes, 0x2520, &0x18e0u64.to_le_bytes());
    put_rdata(bytes, 0x2528, &0x18f0u64.to_le_bytes());
    put_rdata(bytes, 0x2540, b"void __cdecl Der::Wait(void)\0");
    put_rdata(bytes, 0x2560, &0x1920u64.to_le_bytes());
    put_rdata(bytes, 0x2570, b"void __cdecl Der::Peek(void)\0");
    put_rdata(bytes, 0x2590, &0x1950u64.to_le_bytes());
    put_rdata(bytes, 0x2598, &0x1960u64.to_le_bytes());
    put_rdata(bytes, 0x25a0, b"int __cdecl Acc::Get(void) const\0");
    put_rdata(bytes, 0x25c8, &0x1980u64.to_le_bytes());
    put_rdata(bytes, 0x25d0, &0x1990u64.to_le_bytes());
    put_rdata(bytes, 0x25e0, b"this->count\0");
    put_rdata(bytes, 0x2600, b"void __cdecl Der::Chk(void)\0");
    put_rdata(bytes, 0x2620, &0x19a0u64.to_le_bytes());
    put_rdata(bytes, 0x2630, b"void __cdecl Der::Cmp(class Der *)\0");
    put_rdata(bytes, 0x2658, &0x19d0u64.to_le_bytes());
    put_rdata(
        bytes,
        0x2660,
        b"class Core::Ptr<class Der> __cdecl Fac::Make(void)\0",
    );
    put_rdata(bytes, 0x26a0, b"void __cdecl Der::Local(void)\0");
    put_rdata(bytes, 0x26c0, &0x19e0u64.to_le_bytes());
    put_rdata(bytes, 0x26c8, &0x1a00u64.to_le_bytes());
    put_rdata(bytes, 0x26e0, b"void __cdecl Der::Tick2(void)\0");
    put_rdata(bytes, 0x2700, &0x1a30u64.to_le_bytes());
    put_rdata(bytes, 0x2708, &0x1a40u64.to_le_bytes());
    put_rdata(bytes, 0x2710, &0x1a50u64.to_le_bytes());
    put_rdata(bytes, 0x2720, &0u32.to_le_bytes());
    put_rdata(bytes, 0x2740, b"__cdecl Tls::Tls(void)\0");
    put_rdata(bytes, 0x2760, &0x1a60u64.to_le_bytes());
    put_rdata(bytes, 0x2768, &0x1a90u64.to_le_bytes());
    put_rdata(bytes, 0x2780, b"void __cdecl Tls::Use(void)\0");
    put_rdata(bytes, 0x27a0, &0x1ab0u64.to_le_bytes());
    put_rdata(bytes, 0x27a8, &0x1ad0u64.to_le_bytes());
    put_rdata(bytes, 0x27b0, &0x1200u64.to_le_bytes());
    put_rdata(bytes, 0x27b8, &0x13a0u64.to_le_bytes());
    put_rdata(bytes, 0x27c0, &0u64.to_le_bytes());
    put_rdata(bytes, 0x27c8, b"__cdecl Glob::Glob(void)\0");
    put_rdata(bytes, 0x27e8, &0x1ae0u64.to_le_bytes());
    put_rdata(bytes, 0x27f0, &0x1b00u64.to_le_bytes());
    put_rdata(bytes, 0x2800, &0x1b20u64.to_le_bytes());
    put_rdata(bytes, 0x2808, &0x1b30u64.to_le_bytes());
    put_rdata(bytes, 0x2810, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2818, &0x1b10u64.to_le_bytes());
    put_rdata(bytes, 0x2820, b"n == 1\0");
    put_rdata(bytes, 0x2830, b"n must be one\0");
    put_rdata(bytes, 0x2840, b"src/ah.cc\0");
    put_rdata(bytes, 0x2850, &0x1b50u64.to_le_bytes());
    put_rdata(bytes, 0x2858, &0x1b80u64.to_le_bytes());
    put_rdata(
        bytes,
        0x2860,
        b"class Der *__cdecl Core::Ptr<class Der>::operator ->(void) const\0",
    );
    put_rdata(bytes, 0x28a8, &0x1b90u64.to_le_bytes());
    put_rdata(bytes, 0x28b0, &0x1ba0u64.to_le_bytes());
    put_rdata(bytes, 0x28c0, &0x1be0u64.to_le_bytes());
    put_rdata(bytes, 0x28c8, &0x1bf0u64.to_le_bytes());
    put_rdata(bytes, 0x28e0, b"Ns::Thing\0");
    put_rdata(bytes, 0x28f0, &0x1bc0u64.to_le_bytes());
    put_rdata(bytes, 0x28f8, &0x1bd0u64.to_le_bytes());
    put_rdata(bytes, 0x2900, &0x1c00u64.to_le_bytes());
    put_rdata(bytes, 0x2908, &0x1c20u64.to_le_bytes());
    put_rdata(bytes, 0x2910, &0x1be0u64.to_le_bytes());
    put_rdata(bytes, 0x2918, &0x1bf0u64.to_le_bytes());
    put_rdata(bytes, 0x2920, &0x1c50u64.to_le_bytes());
    put_rdata(bytes, 0x2928, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2930, &0x1c30u64.to_le_bytes());
    put_rdata(bytes, 0x2938, &0x1c60u64.to_le_bytes());
    put_rdata(bytes, 0x2940, &0x1c80u64.to_le_bytes());
    put_rdata(bytes, 0x2948, &0x1cb0u64.to_le_bytes());
    put_rdata(bytes, 0x2950, &0x1cf0u64.to_le_bytes());
    put_rdata(bytes, 0x2958, &0x1d30u64.to_le_bytes());
    put_rdata(bytes, 0x2960, &0x1d90u64.to_le_bytes());
    put_rdata(bytes, 0x2968, b"A\0E\0S\0\0\0");
    put_rdata(bytes, 0x2c90, &0x4170u64.to_le_bytes());
    put_rdata(bytes, 0x2970, &0x1dd0u64.to_le_bytes());
    put_rdata(bytes, 0x2978, &0x1de0u64.to_le_bytes());
    put_rdata(bytes, 0x2980, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2988, &0x1dd0u64.to_le_bytes());
    put_rdata(bytes, 0x2990, &0x1df0u64.to_le_bytes());
    put_rdata(bytes, 0x2998, &0u64.to_le_bytes());
    put_rdata(bytes, 0x29a0, &0x1e10u64.to_le_bytes());
    put_rdata(bytes, 0x29a8, &0x1e30u64.to_le_bytes());
    put_rdata(bytes, 0x29b0, b"Ns::T2\0");
    put_rdata(bytes, 0x29b8, &0x1e70u64.to_le_bytes());
    put_rdata(bytes, 0x29c0, &0x1ee0u64.to_le_bytes());
    put_rdata(bytes, 0x29c8, &0x1f00u64.to_le_bytes());
    put_rdata(bytes, 0x29d0, &0x1f40u64.to_le_bytes());
    put_rdata(bytes, 0x29d8, &0x1f70u64.to_le_bytes());
    put_rdata(bytes, 0x29e0, &0x1fa0u64.to_le_bytes());
    put_rdata(bytes, 0x29e8, &0x1fd0u64.to_le_bytes());
    put_rdata(bytes, 0x29f0, &0x1fe4u64.to_le_bytes());
    put_rdata(bytes, 0x29f8, &0x1eb0u64.to_le_bytes());
    put_rdata(bytes, 0x2a00, &0x1dd0u64.to_le_bytes());
    put_rdata(bytes, 0x2a08, &0x1de0u64.to_le_bytes());
    put_rdata(bytes, 0x2a10, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2a20, &0x1dd0u64.to_le_bytes());
    put_rdata(bytes, 0x2a28, &0x1de0u64.to_le_bytes());
    put_rdata(bytes, 0x2a30, &0x1df0u64.to_le_bytes());
    put_rdata(bytes, 0x2a38, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2a40, &0x1e50u64.to_le_bytes());
    put_rdata(bytes, 0x2a48, b"Ns::T3\0");
    put_rdata(bytes, 0x2a50, &0x1290u64.to_le_bytes());
    put_rdata(bytes, 0x2a60, &0x1dd0u64.to_le_bytes());
    put_rdata(bytes, 0x2a68, &0x1de0u64.to_le_bytes());
    put_rdata(bytes, 0x2a70, &0x1df0u64.to_le_bytes());
    put_rdata(bytes, 0x2a78, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2a80, b"Ns::T4\0");
    put_rdata(bytes, 0x2a88, &0x12e0u64.to_le_bytes());
    put_rdata(bytes, 0x2a90, &0x11a0u64.to_le_bytes());
    put_rdata(bytes, 0x2a98, &0x1ed0u64.to_le_bytes());
    put_rdata(bytes, 0x2aa0, &0x1050u64.to_le_bytes());
    put_rdata(bytes, 0x2ab0, &0x1dd0u64.to_le_bytes());
    put_rdata(bytes, 0x2ab8, &0x1de0u64.to_le_bytes());
    put_rdata(bytes, 0x2ac0, &0x1df0u64.to_le_bytes());
    put_rdata(bytes, 0x2ac8, &0x1dd0u64.to_le_bytes());
    put_rdata(bytes, 0x2ad0, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2ad8, &0x1dd0u64.to_le_bytes());
    put_rdata(bytes, 0x2ae0, &0x1de0u64.to_le_bytes());
    put_rdata(bytes, 0x2ae8, &0u64.to_le_bytes());
    put_rdata(bytes, 0x2af0, &0x10e1u64.to_le_bytes());
    put_rdata(bytes, 0x2af8, &0x11e4u64.to_le_bytes());
    put_rdata(bytes, 0x2b00, &0x1118u64.to_le_bytes());
    put_rdata(bytes, 0x2b08, &0x12f0u64.to_le_bytes());
    put_rdata(bytes, 0x2b10, b"void __cdecl Der::Pass(void)\0");
    checks::rdata(bytes);
    put_rdata(bytes, 0x2b30, &0x4000u64.to_le_bytes());
    put_rdata(bytes, 0x2b38, &0x4050u64.to_le_bytes());
    put_rdata(bytes, 0x2b40, &0x4090u64.to_le_bytes());
    put_rdata(bytes, 0x2b48, &0x40f4u64.to_le_bytes());
    put_rdata(bytes, 0x2b50, b"bool __cdecl Ns::Flag(void)\0");
    put_rdata(bytes, 0x2b70, &0x4120u64.to_le_bytes());
    put_rdata(bytes, 0x2b78, &0x4150u64.to_le_bytes());
    put_rdata(bytes, 0x2b80, b"bool __cdecl Ns::Flag2(void)\0");
    put_rdata(bytes, 0x2ba0, b"%d\0");
    put_rdata(bytes, 0x2ba8, &0x4160u64.to_le_bytes());
    put_rdata(bytes, 0x2bb0, &0x4180u64.to_le_bytes());
    put_rdata(bytes, 0x2bb8, &0x41d0u64.to_le_bytes());
    put_rdata(bytes, 0x2bc0, &0x41e0u64.to_le_bytes());
    put_rdata(bytes, 0x2bc8, &0x4200u64.to_le_bytes());
    put_rdata(bytes, 0x2bd0, &0x4210u64.to_le_bytes());
    put_rdata(bytes, 0x2bd8, &0x4220u64.to_le_bytes());
    put_rdata(bytes, 0x2be0, &0x4240u64.to_le_bytes());
    put_rdata(bytes, 0x2be8, &0x4260u64.to_le_bytes());
    put_rdata(bytes, 0x2bf0, &0x4300u64.to_le_bytes());
    put_rdata(bytes, 0x2bf8, &0x4790u64.to_le_bytes());
    put_rdata(bytes, 0x2c00, &0x47a0u64.to_le_bytes());
    put_rdata(bytes, 0x2c08, &0x47b0u64.to_le_bytes());
    put_rdata(bytes, 0x2c50, &0x4830u64.to_le_bytes());
    put_rdata(bytes, 0x2c58, &0x4870u64.to_le_bytes());
    put_rdata(bytes, 0x2c60, &0x48d0u64.to_le_bytes());
    put_rdata(bytes, 0x2c68, &0x4900u64.to_le_bytes());
    put_rdata(bytes, 0x2c70, &0x4930u64.to_le_bytes());
    put_rdata(bytes, 0x2c78, &0x4990u64.to_le_bytes());
    put_rdata(bytes, 0x2c80, &0x49a0u64.to_le_bytes());
    put_rdata(bytes, 0x2c88, &0x49b0u64.to_le_bytes());
    put_rdata(bytes, 0x2c98, &0x4a20u64.to_le_bytes());
    put_rdata(bytes, 0x2ca0, &0x4a40u64.to_le_bytes());
    put_rdata(bytes, 0x2ca8, &0x4a50u64.to_le_bytes());
    put_rdata(bytes, 0x2cb0, &0x4aa0u64.to_le_bytes());
    put_rdata(bytes, 0x2cb8, &0x4ac0u64.to_le_bytes());
    put_rdata(bytes, 0x2cc0, &0x4ae0u64.to_le_bytes());
    put_rdata(bytes, 0x2cc8, &0x4b30u64.to_le_bytes());
    put_rdata(bytes, 0x2cd0, &0x4b20u64.to_le_bytes());
    put_rdata(bytes, 0x2cd8, &0x4b10u64.to_le_bytes());
    put_rdata(bytes, 0x2ce0, &0x4b00u64.to_le_bytes());
    put_rdata(bytes, 0x2ce8, &0x4b40u64.to_le_bytes());
    put_rdata(bytes, 0x2cf0, &0x4b60u64.to_le_bytes());
    put_rdata(bytes, 0x2cf8, &0x4b90u64.to_le_bytes());
    put_rdata(bytes, 0x2d08, &0x4bc0u64.to_le_bytes());
    put_rdata(bytes, 0x2d00, &0x4bb0u64.to_le_bytes());
    put_rdata(bytes, 0x2d10, &0x4be0u64.to_le_bytes());
    put_rdata(bytes, 0x2d18, &0x4bf0u64.to_le_bytes());
    put_rdata(bytes, 0x2d20, &0x4c00u64.to_le_bytes());
    put_rdata(bytes, 0x2d28, &0x4c10u64.to_le_bytes());
    put_rdata(bytes, 0x2d30, &0x4c20u64.to_le_bytes());
    put_rdata(bytes, 0x2d38, &0x4c30u64.to_le_bytes());
    put_rdata(bytes, 0x2d40, &0x4c40u64.to_le_bytes());
    put_rdata(bytes, 0x2d48, &0x4c60u64.to_le_bytes());
    put_rdata(bytes, 0x2d50, &0x4c90u64.to_le_bytes());
    for (i, t) in [0x4cbeu64, 0x4cc4, 0x4cca].iter().enumerate() {
        put_rdata(bytes, 0x2e00 + (i as u64) * 8, &t.to_le_bytes());
    }
    for (i, t) in [0x3cf8u32, 0x3cfe, 0x3d04].iter().enumerate() {
        put_rdata(bytes, 0x2e20 + (i as u64) * 4, &t.to_le_bytes());
    }
    put_rdata(bytes, 0x2d58, &0x4cb0u64.to_le_bytes());
    put_rdata(bytes, 0x2d60, &0x4ce0u64.to_le_bytes());
    put_rdata(bytes, 0x2f00, b"StringAtom(\"x\") != f\0");
    put_rdata(bytes, 0x2d68, &0x4d20u64.to_le_bytes());
    put_rdata(bytes, 0x2f20, b"void __cdecl Pf::Take(class Ns::Thing *)\0");
    put_rdata(bytes, 0x2d70, &0x4d50u64.to_le_bytes());
    put_rdata(bytes, 0x2d78, &0x4d80u64.to_le_bytes());
    put_rdata(bytes, 0x2d80, &0x4d90u64.to_le_bytes());
    put_rdata(bytes, 0x2d88, &0x4dc0u64.to_le_bytes());
    put_rdata(bytes, 0x2f60, b"\0ok\0");
    put_rdata(bytes, 0x2d90, &0x4de0u64.to_le_bytes());
    put_rdata(bytes, 0x2da0, &0x4e20u64.to_le_bytes());
    put_rdata(bytes, 0x2da8, &0x4e50u64.to_le_bytes());
    put_rdata(bytes, 0x2db0, &0x4e80u64.to_le_bytes());
    put_rdata(bytes, 0x2df0, &0x4f00u64.to_le_bytes());
    put_rdata(bytes, 0x2df8, &0x4f20u64.to_le_bytes());
    put_rdata(bytes, 0x2ea0, &0x3f40u32.to_le_bytes());
    put_rdata(bytes, 0x2ea4, &0x3f46u32.to_le_bytes());
    put_rdata(bytes, 0x2eb0, &[0u8, 1, 0, 1, 0]);
    put_rdata(bytes, 0x2ec0, &0x4f70u64.to_le_bytes());
    put_rdata(bytes, 0x2ec8, &0x4f90u64.to_le_bytes());
    put_rdata(bytes, 0x2ed0, &0x4fb0u64.to_le_bytes());
    put_rdata(bytes, 0x2ed8, &0x5000u64.to_le_bytes());
    put_rdata(bytes, 0x2ee0, &0x5040u64.to_le_bytes());
    put_rdata(bytes, 0x2ee8, &0x5080u64.to_le_bytes());
    put_rdata(bytes, 0x2ef0, &0x50c0u64.to_le_bytes());
    put_rdata(bytes, 0x2ef8, &0x5130u64.to_le_bytes());
    put_rdata(bytes, 0x2ff0, &0x5150u64.to_le_bytes());
    put_rdata(bytes, 0x2ff8, &0x5170u64.to_le_bytes());
    put_rdata(bytes, 0x2f18, &0x5190u64.to_le_bytes());
    put_rdata(bytes, 0x2f50, &0x51c0u64.to_le_bytes());
    put_rdata(bytes, 0x2f58, &0x5200u64.to_le_bytes());
    put_rdata(bytes, 0x2f68, &0x5240u64.to_le_bytes());
    put_rdata(bytes, 0x2f70, &0x52a0u64.to_le_bytes());
    put_rdata(bytes, 0x2f78, &0x52c0u64.to_le_bytes());
    put_rdata(bytes, 0x39e0, &0x5900u64.to_le_bytes());
    put_rdata(bytes, 0x39e8, &0x5910u64.to_le_bytes());
    put_rdata(bytes, 0x39f0, &0x5930u64.to_le_bytes());
    put_rdata(bytes, 0x2ea8, &0x5320u64.to_le_bytes());
    put_rdata(bytes, 0x2eb8, &0x5390u64.to_le_bytes());
    put_rdata(bytes, 0x2f90, &0x5450u64.to_le_bytes());
    put_rdata(bytes, 0x2f98, &0x54e0u64.to_le_bytes());
    for (i, t) in [0x550fu64, 0x551a, 0x5525].into_iter().enumerate() {
        put_rdata(bytes, 0x21d0 + (i as u64) * 8, &t.to_le_bytes());
    }
    put_rdata(bytes, 0x2728, &0x5500u64.to_le_bytes());
    put_rdata(bytes, 0x2730, &0x5570u64.to_le_bytes());
    put_rdata(bytes, 0x2738, &0x5590u64.to_le_bytes());
    put_rdata(bytes, 0x39c0, b"Zz::Thing\0");
    put_rdata(bytes, 0x3980, b"void __cdecl Fz::Set(void)\0");
    put_rdata(bytes, 0x39a0, b"float __cdecl Fz::Get(void)\0");
    put_rdata(bytes, 0x3960, b"float __cdecl Fr::Get(void)\0");
    put_rdata(
        bytes,
        0x3900,
        b"class Network::Bs *__cdecl Core::Ptr<class Network::Bs>::operator ->(void) const\0",
    );
    put_rdata(
        bytes,
        0x3800,
        b"C:\\build\\workspace\\a.very.long.machine.path.that.eats.the.window\\code\\module\\probe/needle.h\0",
    );
    put_rdata(bytes, 0x37f0, b"this->head\0");
    put_rdata(bytes, 0x2fa0, b"void __cdecl Gz::Chk(void)\0");
    put_rdata(bytes, 0x2fc0, b"this->tail\0");
    put_rdata(bytes, 0x2fd0, b"void __cdecl Gg::Chk(void)\0");
    put_rdata(bytes, 0x2dc0, b"this->IsSet()\0");
    put_rdata(bytes, 0x2dd0, b"void __cdecl Lk::Chk(void)\0");
    put_rdata(bytes, 0x2e30, b"this->size\0");
    put_rdata(bytes, 0x2e40, b"void __cdecl Arr<int>::Add(void)\0");
    put_rdata(bytes, 0x2e70, b"void __cdecl Arr<char>::Add(void)\0");
    put_rdata(bytes, 0x2f80, b" \t-+0\0");
    put_rdata(bytes, 0x3400, &0x9000u64.to_le_bytes());
    put_rdata(bytes, 0x3410, &0x55c0u64.to_le_bytes());
    put_rdata(bytes, 0x3418, &0x55e0u64.to_le_bytes());
    put_rdata(bytes, 0x3420, &1u32.to_le_bytes());
    put_rdata(bytes, 0x3490, &0x9000u64.to_le_bytes());
    put_rdata(bytes, 0x3498, &0x56c0u64.to_le_bytes());
    put_rdata(bytes, 0x2d98, &0x4e00u64.to_le_bytes());
    put_rdata(bytes, 0x2db8, &0x4e90u64.to_le_bytes());
    put_rdata(bytes, 0x2c10, b"Back\0");
    put_rdata(bytes, 0x2c18, b"Tab\0");
    put_rdata(bytes, 0x2c20, b"Clear\0");
    put_rdata(bytes, 0x2c28, b"Return\0");
    put_rdata(bytes, 0x2c30, b"Normal\0");
    put_rdata(bytes, 0x2c38, b"Pressed\0");
    put_rdata(bytes, 0x2c40, b"Over\0");
    put_rdata(bytes, 0x2c48, b"Down\0");
    put_rdata(bytes, 0x20a0, b"int __cdecl Foo::Bar(void)\0");
    put_rdata(bytes, 0x20c0, b"void __cdecl Foo::Baz(int)\0");
    vcall::data(bytes);
    for i in 0..4u64 {
        put_rdata(bytes, 0x2070 + i * 4, &0x8000_0000u32.to_le_bytes());
        put_rdata(bytes, 0x2080 + i * 4, &0x7fff_ffffu32.to_le_bytes());
    }
    // A vtable with a datum between its methods: the table at 0x3730 holds
    // `F0` at slot 0, the constant `0x9999` (an address of no section) at
    // slot 1 and `F1` at slot 2, and the pointer at 0x3770 seeds its
    // constructor `RM` far enough that the padding after `F1` ends the
    // table before it.
    put_rdata(bytes, 0x3730, &0x5650u64.to_le_bytes());
    put_rdata(bytes, 0x3738, &0x9999u64.to_le_bytes());
    put_rdata(bytes, 0x3740, &0x5660u64.to_le_bytes());
    put_rdata(bytes, 0x3770, &0x5640u64.to_le_bytes());
    put_rdata(bytes, 0x3780, &0x5600u64.to_le_bytes());
    put_rdata(bytes, 0x3790, &0x5680u64.to_le_bytes());
    // MSVC run-time type information for `Ns::Rtti` (vtable 0x3678),
    // `Ns::Solo` (vtable 0x3718, one slot) and `Ns::Wide` (primary vtable
    // 0x32b0, further base `Ns::Tail`'s table 0x32f0 at subobject offset
    // 0x10), as a 64-bit image carries it: image-relative links, and the
    // image base is zero. Each class has a type descriptor, a hierarchy
    // and a complete object locator, whose address is the word before the
    // vtable; `bases` lists the bases past the class itself as
    // `(type descriptor, subobject offset)`.
    let rtti =
        |bytes: &mut [u8], td: u32, name: &[u8], vtable: u32, offset: u32, bases: &[(u32, u32)]| {
            let chd = td + 0x20;
            let array = td + 0x30;
            let bcd = |k: u32| td + 0x38 + 0x10 * k;
            let col = vtable - 0x20;
            let word_at = |bytes: &mut [u8], at: u32, v: u32| {
                put_rdata(bytes, u64::from(at), &v.to_le_bytes());
            };
            put_rdata(bytes, u64::from(td), &[0u8; 16]);
            put_rdata(bytes, u64::from(td + 16), name);
            word_at(
                bytes,
                chd + 8,
                u32::try_from(bases.len() + 1).unwrap_or(u32::MAX),
            );
            word_at(bytes, chd + 12, array);
            for (k, &(base_td, mdisp)) in std::iter::once(&(td, 0)).chain(bases).enumerate() {
                let b = bcd(u32::try_from(k).unwrap_or(u32::MAX));
                word_at(bytes, array + 4 * u32::try_from(k).unwrap_or(u32::MAX), b);
                word_at(bytes, b, base_td);
                word_at(bytes, b + 8, mdisp);
                put_rdata(bytes, u64::from(b + 12), &u32::MAX.to_le_bytes());
            }
            word_at(bytes, col, 1);
            word_at(bytes, col + 4, offset);
            word_at(bytes, col + 8, 0);
            word_at(bytes, col + 12, td);
            word_at(bytes, col + 16, chd);
            word_at(bytes, col + 20, col);
            put_rdata(bytes, u64::from(vtable - 8), &u64::from(col).to_le_bytes());
        };
    rtti(bytes, 0x3600, b".?AVRtti@Ns@@\0", 0x3678, 0, &[]);
    put_rdata(bytes, 0x3678, &0x5620u64.to_le_bytes());
    put_rdata(bytes, 0x3680, &0x5630u64.to_le_bytes());
    rtti(bytes, 0x36a0, b".?AVSolo@Ns@@\0", 0x3718, 0, &[]);
    put_rdata(bytes, 0x3718, &0x56a0u64.to_le_bytes());
    // `Ns::Wide` derives `Ns::Tail` at offset 0x10: its constructor stores
    // its own table at `[this]` and Tail's at `[this+0x10]`, which the
    // scan does not follow, so the subobject's table is found by the
    // immediates that name it.
    put_rdata(bytes, 0x3260, &[0u8; 16]);
    put_rdata(bytes, 0x3270, b".?AVTail@Ns@@\0");
    rtti(
        bytes,
        0x3200,
        b".?AVWide@Ns@@\0",
        0x32b0,
        0,
        &[(0x3260, 0x10)],
    );
    put_rdata(bytes, 0x32b0, &0x5720u64.to_le_bytes());
    put_rdata(bytes, 0x32b8, &0x5730u64.to_le_bytes());
    rtti(
        bytes,
        0x3200,
        b".?AVWide@Ns@@\0",
        0x32f0,
        0x10,
        &[(0x3260, 0x10)],
    );
    put_rdata(bytes, 0x32f0, &0x5740u64.to_le_bytes());
    put_rdata(bytes, 0x32f8, &0x5750u64.to_le_bytes());
    put_rdata(bytes, 0x3320, &0x5700u64.to_le_bytes());
}
