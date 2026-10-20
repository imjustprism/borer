//! Calls into the kernel: `syscall` and `int 0x80`, named by the number
//! the block sets and read with the arguments the entry passes.

use super::*;

impl Exec<'_, '_> {
    /// Lifts a call into the kernel as the call it names.
    ///
    /// On Linux the number in `eax` names the call, by the table of the
    /// entry used ([`crate::emulate::linux_syscall_name`] for `syscall`,
    /// [`crate::analysis::syscalls::i386_syscall_name`] for `int 0x80`),
    /// and the call reads its arguments from the entry's registers: `rdi`,
    /// `rsi`, `rdx`, `r10`, `r8`, `r9` for `syscall`, `ebx`, `ecx`, `edx`,
    /// `esi`, `edi`, `ebp` for `int 0x80`. A named call takes as many as
    /// the C library's function of that name declares, so `mov eax, 1;
    /// syscall` is `rax = write(rdi, rsi, rdx);`. A number no table names,
    /// or one the block does not set, is the C library's `syscall(nr,
    /// ...)` with the registers set since the last call. The result is in
    /// `rax`. The kernel leaves the argument registers as they were, so
    /// they are the call's preserved registers ([`Exec::preserved`]); any
    /// other volatile value is forgotten, as after any call.
    ///
    /// Windows numbers its services anew in every build and borer holds no
    /// table of them, so a Windows `syscall` stays `syscall(nr, ...)`. Its
    /// arguments are in `r10`, `rdx`, `r8` and `r9`; inside a native API's
    /// stub (a function named `NtClose` or `ZwClose`, the service the
    /// number stands for) they are as many as the API takes, the first
    /// four of them.
    ///
    /// # Arguments
    ///
    /// * `gate` - How the kernel is entered.
    pub(super) fn kernel_call(&mut self, gate: KernelGate) {
        const INT80_ARGS: [Register; 6] = [
            Register::EBX,
            Register::ECX,
            Register::EDX,
            Register::ESI,
            Register::EDI,
            Register::EBP,
        ];
        let windows = self.ctx.program.format == BinaryFormat::Pe;
        let regs: &[Register] = match gate {
            KernelGate::Syscall if windows => &NT_ARGS,
            KernelGate::Syscall => &SYSCALL_ARGS,
            KernelGate::Int80 => &INT80_ARGS,
        };
        let raxk = self.canon(self.rax());
        let nr = match self.env.vals.get(&raxk) {
            Some(Expr::Const(n)) => Some(*n),
            _ => None,
        };
        let linux = self.ctx.program.format == BinaryFormat::Elf;
        let name = nr.filter(|_| linux).and_then(|n| match gate {
            KernelGate::Syscall => crate::emulate::linux_syscall_name(n),
            KernelGate::Int80 => crate::analysis::syscalls::i386_syscall_name(n),
        });
        let arity = if windows {
            native_service(&self.ctx.own_name)
        } else {
            name.and_then(|n| crate::analysis::typelib::declared(n, BinaryFormat::Elf))
                .map(|d| d.params.len())
        };
        let n = self.names();
        let mut args = Vec::new();
        let mut values = Vec::new();
        if name.is_none() {
            args.push(self.reg_read(self.rax()).render(&n));
        }
        for (i, r) in regs.iter().enumerate() {
            let k = self.canon(*r);
            let value = match arity {
                Some(a) if i < a => self.reg_read(*r),
                Some(_) => break,
                None if self.env.fresh.contains(&k) => self.reg_read(*r),
                None => break,
            };
            args.push(value.render(&n));
            if self.emit {
                values.push((ArgAt::Reg(*r), value));
            }
        }
        self.preserved = regs.iter().map(|r| self.canon(*r)).collect();
        self.before_call(Some(0), false, 0, &values, &[]);
        self.enter_call(false, &[]);
        self.declare(raxk, self.word_ty());
        let callee = name.unwrap_or("syscall");
        let shown = n.key(raxk);
        emit_line!(self, format!("{shown} = {callee}({});", args.join(", ")));
        self.record(EffectKind::Unmodeled);
        self.after_call(false);
        self.preserved.clear();
        self.env.result_in_rax = true;
    }
}

/// The registers x86-64 Linux `syscall` takes its arguments from, in order.
const SYSCALL_ARGS: [Register; 6] = [
    Register::RDI,
    Register::RSI,
    Register::RDX,
    Register::R10,
    Register::R8,
    Register::R9,
];

/// The registers a Windows `syscall` takes the first four arguments from.
const NT_ARGS: [Register; 4] = [Register::R10, Register::RDX, Register::R8, Register::R9];

/// Returns how many arguments the native API a function's name names
/// takes, when the function is that API's stub.
///
/// `NtClose` and `ZwClose` both name the service `NtClose`, which takes
/// one.
///
/// # Arguments
///
/// * `own` - The function's name.
///
/// # Returns
///
/// The count, or `None` for a name the type library declares no native
/// API by.
fn native_service(own: &str) -> Option<usize> {
    let service = own
        .strip_prefix("Zw")
        .map_or_else(|| own.to_owned(), |rest| format!("Nt{rest}"));
    service
        .starts_with("Nt")
        .then(|| crate::analysis::typelib::declared(&service, BinaryFormat::Pe))
        .flatten()
        .map(|d| d.params.len())
}

/// Returns the argument registers a Linux `syscall` reads.
///
/// They are known when its block sets a number the table names and the C
/// library declares a function of that name: `mov eax, 1; syscall` reads
/// `rdi`, `rsi` and `rdx` for `write`. In a Windows native API's stub
/// they are the registers of as many of the API's arguments as the
/// registers carry ([`native_service`]).
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `instr` - The `syscall`.
///
/// # Returns
///
/// The registers in argument order; none for a number not named, or one
/// its block does not set.
pub(in crate::analysis::decompile) fn kernel_reads(
    ctx: &Ctx<'_>,
    instr: &Instruction,
) -> Vec<Register> {
    if ctx.program.format == BinaryFormat::Pe {
        let arity = native_service(&ctx.own_name).unwrap_or(0);
        return NT_ARGS.iter().copied().take(arity).collect();
    }
    let sites = crate::analysis::syscalls::syscall_sites(ctx.program, ctx.analysis);
    let arity = sites
        .binary_search_by_key(&instr.ip(), |s| s.at)
        .ok()
        .and_then(|k| sites.get(k)?.name)
        .and_then(|n| crate::analysis::typelib::declared(n, BinaryFormat::Elf))
        .map_or(0, |d| d.params.len());
    SYSCALL_ARGS.iter().copied().take(arity).collect()
}

/// How a program enters the kernel, which says where the call's number
/// and arguments are and which table names it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum KernelGate {
    /// x86-64 `syscall`: the number in `rax`, the x86-64 table.
    Syscall,
    /// `int 0x80`: the number in `eax`, the i386 table.
    Int80,
}
