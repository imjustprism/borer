//! What one function's ABI says: where each parameter travels and what
//! class it is, where the result comes back, and whether a hidden pointer
//! carries an indirect result.
//!
//! The layer reads a function's [`Shape`] (the registers and stack words
//! its body reads, cut to what a declaration states) and places each
//! position by the target's convention. The output is explicit, a value of
//! plain data per function ([`FunctionAbi`]), so a later stage can read the
//! prototype of any callee ([`prototype`]) without decompiling it.

use std::sync::Arc;

use super::super::{Shape, lift_a64, shape_built};
use super::conv::{AAPCS64, CDECL_X86, Conv, FASTCALL_X86, GO_X64, MS_X64, SYSV_X64, THISCALL_X86};
use crate::analysis::{Analysis, Function, Overlay};
use crate::isa::{Isa, a64, x86::Register};
use crate::num::from_usize;
use crate::program::Program;

/// The calling convention a function follows, by the target's name for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Target {
    /// System V x86-64: six integer and eight vector argument registers.
    SysvX64,
    /// Microsoft x64: four argument slots, 32 bytes of shadow space.
    Win64,
    /// Go's register ABI on amd64.
    GoX64,
    /// The arm64 procedure call standard: `x0` to `x7`, `v0` to `v7`, an
    /// indirect result's address in `x8`.
    Aapcs64,
    /// 32-bit cdecl: every argument on the stack, the caller pops them.
    X86Cdecl,
    /// 32-bit stdcall: every argument on the stack, the callee pops them.
    X86Stdcall,
    /// 32-bit fastcall: `ecx` and `edx`, then the stack.
    X86Fastcall,
    /// 32-bit thiscall: `this` in `ecx`, the rest on the stack.
    X86Thiscall,
}

impl Target {
    /// Returns the target a convention table and a callee's stack cleanup
    /// name.
    ///
    /// # Arguments
    ///
    /// * `conv` - The convention table the function's shape carries.
    /// * `pops` - Whether the callee pops its stack arguments (`ret N`).
    pub(crate) fn of(conv: &Conv, pops: bool) -> Self {
        if *conv == MS_X64 {
            Self::Win64
        } else if *conv == SYSV_X64 {
            Self::SysvX64
        } else if *conv == GO_X64 {
            Self::GoX64
        } else if *conv == AAPCS64 {
            Self::Aapcs64
        } else if *conv == FASTCALL_X86 {
            Self::X86Fastcall
        } else if *conv == THISCALL_X86 {
            Self::X86Thiscall
        } else if *conv == CDECL_X86 && pops {
            Self::X86Stdcall
        } else {
            Self::X86Cdecl
        }
    }
}

/// How the ABI passes one value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Class {
    /// An integer or a pointer, in general registers or stack words.
    Int,
    /// A floating-point value, in a vector register or on the stack.
    Float,
    /// An aggregate small enough to travel in registers, split into
    /// register-sized pieces.
    #[expect(
        dead_code,
        reason = "the type solve (J8) proposes aggregates; the ABI places them"
    )]
    AggregateInRegisters,
    /// An aggregate the caller copies and passes by its address.
    #[expect(
        dead_code,
        reason = "the type solve (J8) proposes aggregates; the ABI places them"
    )]
    AggregateByReference,
    /// The address an aggregate result is written at: an ABI fact, never a
    /// source parameter (`x8` on arm64, the first argument register on
    /// x86-64).
    IndirectResult,
}

/// Where one piece of a value travels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Loc {
    /// An x86 register.
    X86(Register),
    /// An arm64 register.
    A64(a64::Reg),
    /// A stack word at this offset in bytes from the stack pointer at the
    /// function's entry.
    Stack(u64),
}

/// One parameter or result: its class and the locations its pieces take,
/// in order.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Value {
    /// How the value travels.
    pub(crate) class: Class,
    /// Its pieces' locations, the low piece first.
    pub(crate) locs: Vec<Loc>,
    /// Its width in bits, when the function's code states it.
    pub(crate) bits: Option<u8>,
}

/// What one function's ABI says.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct FunctionAbi {
    /// The convention it follows.
    pub(crate) target: Target,
    /// Its source parameters in order, `this` first when it has one, the
    /// indirect result never among them.
    pub(crate) params: Vec<Value>,
    /// The hidden pointer an aggregate result is written through, when it
    /// returns one that way.
    pub(crate) indirect_result: Option<Value>,
    /// Its result, `None` when it returns nothing in registers.
    pub(crate) ret: Option<Value>,
    /// Whether its first parameter is `this`.
    pub(crate) this: bool,
    /// Whether it takes `...` past its fixed parameters.
    pub(crate) variadic: bool,
}

/// Returns where the source prototype lists an indirect result's pointer:
/// first, after `this` when there is one, whichever register the target
/// passes it in.
///
/// A prototype that lists the pointer where the source does compiles to
/// the same call on any host, which is what makes it a source-level
/// signature: `x8` on arm64 is no argument register at all.
///
/// # Arguments
///
/// * `this` - Whether the function takes `this`.
pub(crate) fn indirect_result_position(this: bool) -> usize {
    usize::from(this)
}

/// Returns a function's [`Shape`], read once per function and overlay
/// through [`Analysis::derived`], by the lifter of its instruction set.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names and prototypes.
/// * `f` - The function.
/// * `bitness` - Decoder bitness, `32` or `64`.
pub(in crate::analysis::decompile) fn shape(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
    bitness: u32,
) -> Arc<Shape> {
    analysis.derived.get_or_build_item(
        "shape",
        overlay.fingerprint(),
        f.entry,
        || match program.arch.isa() {
            Some(Isa::A64) => lift_a64::built_shape(program, analysis, overlay, f),
            Some(Isa::X86 { .. }) | None => shape_built(program, analysis, overlay, f, bitness),
        },
        |shape| shape.params.capacity() * size_of::<Register>(),
    )
}

/// Returns the ABI facts of the function at `entry`: its parameters, its
/// result and its indirect result, each placed by its convention.
///
/// A linkage stub's facts are those of the function it binds
/// ([`super::reached`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names and prototypes.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The facts, or `None` when no function starts at `entry`.
pub(crate) fn of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<FunctionAbi> {
    let entry = super::reached(analysis, entry);
    let f = analysis.function(entry).filter(|f| f.entry == entry)?;
    let bitness = program.arch.bitness().unwrap_or(64);
    let s = shape(program, analysis, overlay, f, bitness);
    Some(placed(&s, f))
}

/// Places a shape's positions by its convention.
///
/// # Arguments
///
/// * `s` - The function's shape.
/// * `f` - The function, for what it hands back.
fn placed(s: &Shape, f: &Function) -> FunctionAbi {
    let conv = s.conv;
    let target = Target::of(conv, f.stack_pop > 0);
    let floats = s.floats();
    let word = conv.word.unsigned_abs();
    let first_stack = word.wrapping_add(conv.shadow.unsigned_abs());
    let regs = s.regs();
    let loc = |i: usize, float: bool| -> Loc {
        let reg = match target {
            Target::Aapcs64 => lift_a64::arg_reg(i, floats).map(Loc::A64),
            Target::SysvX64
            | Target::Win64
            | Target::GoX64
            | Target::X86Cdecl
            | Target::X86Stdcall
            | Target::X86Fastcall
            | Target::X86Thiscall => conv.arg_reg(i, floats).map(Loc::X86),
        };
        reg.filter(|_| float || i < regs || target == Target::Aapcs64)
            .unwrap_or_else(|| {
                let past = from_usize(i.saturating_sub(regs));
                Loc::Stack(first_stack.wrapping_add(past.wrapping_mul(word)))
            })
    };
    let result_at = s.result_param.map(usize::from);
    let mut params = Vec::with_capacity(s.count);
    let mut indirect_result = None;
    let mut seq = 0usize;
    for i in 0..s.count {
        if result_at == Some(i) {
            let at = match target {
                Target::Aapcs64 => Loc::A64(a64::Reg::X(lift_a64::RESULT_REG)),
                Target::SysvX64
                | Target::Win64
                | Target::GoX64
                | Target::X86Cdecl
                | Target::X86Stdcall
                | Target::X86Fastcall
                | Target::X86Thiscall => loc(i, false),
            };
            indirect_result = Some(Value {
                class: Class::IndirectResult,
                locs: vec![at],
                bits: None,
            });
            if target != Target::Aapcs64 {
                seq += 1;
            }
            continue;
        }
        let float = floats & (1u8 << i.min(7)) != 0;
        params.push(Value {
            class: if float { Class::Float } else { Class::Int },
            locs: vec![loc(seq, float)],
            bits: None,
        });
        seq += 1;
    }
    let ret = match (f.returns_value, f.ret_float) {
        (Some(false), None) => None,
        (_, Some(bits)) => Some(Value {
            class: Class::Float,
            bits: Some(bits),
            locs: vec![match target {
                Target::Aapcs64 => Loc::A64(a64::Reg::V(0)),
                Target::SysvX64
                | Target::Win64
                | Target::GoX64
                | Target::X86Cdecl
                | Target::X86Stdcall
                | Target::X86Fastcall
                | Target::X86Thiscall => Loc::X86(Register::XMM0),
            }],
        }),
        (Some(true) | None, None) => Some(Value {
            class: Class::Int,
            bits: f.ret_width,
            locs: vec![match target {
                Target::Aapcs64 => Loc::A64(a64::Reg::X(0)),
                Target::X86Cdecl
                | Target::X86Stdcall
                | Target::X86Fastcall
                | Target::X86Thiscall => Loc::X86(Register::EAX),
                Target::SysvX64 | Target::Win64 | Target::GoX64 => Loc::X86(Register::RAX),
            }],
        }),
    };
    FunctionAbi {
        target,
        params,
        indirect_result,
        ret,
        this: s.this_param,
        variadic: s.variadic,
    }
}

/// A callee's prototype as the ABI types it: each parameter by its class
/// and the target's word, a floating one as `double` unless its width is
/// known, before any type the decompiled body may refine.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Prototype {
    /// The function's name.
    pub(crate) name: String,
    /// The C return type.
    pub(crate) ret: &'static str,
    /// The C parameter types in source order, the indirect result's
    /// pointer first ([`indirect_result_position`]).
    pub(crate) params: Vec<&'static str>,
    /// Whether it takes `...` past its fixed parameters.
    pub(crate) variadic: bool,
}

#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the translation-unit closure (J5) declares callees from it"
    )
)]
impl Prototype {
    /// Returns the declaration, `uint64_t f(uint64_t, double);`.
    pub(crate) fn declaration(&self) -> String {
        let mut params = self.params.clone();
        if self.variadic {
            params.push("...");
        }
        if params.is_empty() {
            params.push("void");
        }
        let sep = if self.ret.ends_with('*') { "" } else { " " };
        format!("{}{sep}{}({});", self.ret, self.name, params.join(", "))
    }
}

/// Returns the prototype of the function at `entry`, typed from its ABI
/// facts alone ([`of`]).
///
/// It is a declaration any caller may print without decompiling the
/// callee, so two functions that call each other declare each other in
/// any order.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names and prototypes.
/// * `entry` - The callee's entry; a linkage stub's prototype is its
///   bound function's under the stub's name.
///
/// # Returns
///
/// The prototype, or `None` when no function starts at `entry`.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the translation-unit closure (J5) declares callees from it"
    )
)]
pub(crate) fn prototype(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<Prototype> {
    let abi = of(program, analysis, overlay, entry)?;
    let wide = program.arch.bitness() != Some(32);
    let word = if wide { "uint64_t" } else { "uint32_t" };
    let ty = |v: &Value| match v.class {
        Class::Float if v.bits == Some(32) => "float",
        Class::Float => "double",
        Class::Int | Class::AggregateInRegisters => word,
        Class::AggregateByReference | Class::IndirectResult => "void *",
    };
    let mut params: Vec<&'static str> = abi.params.iter().map(ty).collect();
    if let Some(r) = &abi.indirect_result {
        params.insert(indirect_result_position(abi.this).min(params.len()), ty(r));
    }
    let ret = match (&abi.ret, &abi.indirect_result) {
        (_, Some(_)) | (None, None) => "void",
        (Some(v), None) => ty(v),
    };
    Some(Prototype {
        name: crate::analysis::decompile::expr::bare(&crate::analysis::name_of(
            analysis, overlay, entry,
        ))
        .to_owned(),
        ret,
        params,
        variadic: abi.variadic,
    })
}

#[cfg(test)]
mod tests {
    use super::{Class, Loc, Target, of, prototype};
    use crate::analysis::{Analysis, Overlay};
    use crate::isa::{a64, x86::Register};
    use crate::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};

    /// Builds a one-section image of `code` at 0x1000, its function named.
    ///
    /// # Arguments
    ///
    /// * `arch` - The instruction set.
    /// * `code` - The bytes.
    fn image(arch: Arch, code: &[u8]) -> Program {
        let mut bytes = vec![0u8; 0x100];
        bytes[..code.len()].copy_from_slice(code);
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let mut p = Program::raw(bytes, arch, 0, Some(0x1000), vec![text]);
        p.symbols = vec![Symbol {
            name: "f".to_owned(),
            addr: 0x1000,
            kind: SymbolKind::Export,
        }];
        p
    }

    /// A Microsoft x64 function adding its two arguments takes them in
    /// `rcx` and `rdx` and hands an integer back in `rax`, and its
    /// prototype declares two words.
    ///
    /// # Panics
    ///
    /// When the arguments sit elsewhere or the prototype differs.
    #[test]
    fn a_win64_function_places_its_arguments_in_rcx_and_rdx() {
        let mut p = image(Arch::X86_64, &[0x48, 0x8d, 0x04, 0x11, 0xc3]);
        p.format = BinaryFormat::Pe;
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let abi = of(&p, &a, &o, 0x1000).unwrap();
        assert_eq!(abi.target, Target::Win64);
        let locs: Vec<Loc> = abi.params.iter().flat_map(|v| v.locs.clone()).collect();
        assert_eq!(locs, [Loc::X86(Register::RCX), Loc::X86(Register::RDX)]);
        assert_eq!(abi.ret.map(|r| r.class), Some(Class::Int));
        assert_eq!(
            prototype(&p, &a, &o, 0x1000).unwrap().declaration(),
            "uint64_t f(uint64_t, uint64_t);"
        );
    }

    /// An arm64 function writing through `x8` returns its aggregate
    /// indirectly: the pointer is the indirect result, in `x8`, not a
    /// parameter, and the prototype lists it first.
    ///
    /// # Panics
    ///
    /// When the pointer is a parameter or the prototype lists it last.
    #[test]
    fn an_arm64_indirect_result_is_no_parameter() {
        let code: Vec<u8> = [
            0xb900_0100u32, // ASM: str w0, [x8]
            0xd65f_03c0,    // ASM: ret
        ]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
        let p = image(Arch::Arm64, &code);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let abi = of(&p, &a, &o, 0x1000).unwrap();
        assert_eq!(abi.target, Target::Aapcs64);
        assert_eq!(abi.params.len(), 1);
        assert_eq!(
            abi.indirect_result.map(|r| (r.class, r.locs)),
            Some((Class::IndirectResult, vec![Loc::A64(a64::Reg::X(8))]))
        );
        assert_eq!(
            prototype(&p, &a, &o, 0x1000).unwrap().declaration(),
            "void f(void *, uint64_t);"
        );
    }
}
