//! The record of one emulated API or syscall call, shared by both emulators.
//!
//! An emulator services an imported call or a syscall by modeling its effect
//! rather than executing it ([`super::Emulator::service_api`],
//! [`super::a64::Machine`]). Recording each one in order, with the arguments
//! read from the machine's memory and decoded by the type library
//! ([`crate::analysis::typelib`]), turns the emulator into a behavior trace:
//! which file it would open, which host it would reach, which key it would
//! set. The record type lives here so both emulators keep the same one, and
//! every string argument it decodes becomes an `emulated` indicator.

use crate::analysis::typelib::{self, Pass};
use crate::program::BinaryFormat;

/// Longest string argument read from memory, in bytes.
pub const TEXT_MAX: usize = 256;

/// Most arguments decoded for one call: past this the type library declares
/// nothing a reader needs, and a variadic tail is unbounded.
const ARGS_MAX: usize = 12;

/// One argument of an emulated call, decoded from the machine at the moment
/// the call was serviced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgValue {
    /// A small integer, shown in decimal when below ten, else in hex.
    Int(u64),
    /// A value the type library names: a flag set, an enumerated value, a
    /// handle, already spelled.
    Named(String),
    /// A string read through a string pointer, with whether it was wide.
    Str {
        /// The text, printable bytes up to [`TEXT_MAX`].
        text: String,
        /// Whether the pointer was to wide (UTF-16) characters.
        wide: bool,
    },
    /// A pointer nothing could be read through, shown as `ptr 0x...`.
    Ptr(u64),
    /// A null pointer.
    Null,
}

impl ArgValue {
    /// Renders the argument as a call site would read it.
    ///
    /// A string is quoted the way the decompiler's call sites quote one, a
    /// wide string with the `L` prefix, its backslashes and quotes escaped;
    /// [`read_text`] keeps only printable bytes, so nothing else needs
    /// escaping.
    #[must_use]
    pub fn shown(&self) -> String {
        match self {
            ArgValue::Int(v) if *v < 10 => v.to_string(),
            ArgValue::Int(v) => format!("{v:#x}"),
            ArgValue::Named(name) => name.clone(),
            ArgValue::Str { text, wide } => {
                let escaped = text.replace('\\', "\\\\").replace('"', "\\\"");
                format!("{}\"{escaped}\"", if *wide { "L" } else { "" })
            }
            ArgValue::Ptr(a) => format!("ptr {a:#x}"),
            ArgValue::Null => "NULL".to_owned(),
        }
    }

    /// The decoded text, when the argument is a string.
    #[must_use]
    pub fn text(&self) -> Option<&str> {
        match self {
            ArgValue::Str { text, .. } => Some(text),
            ArgValue::Int(_) | ArgValue::Named(_) | ArgValue::Ptr(_) | ArgValue::Null => None,
        }
    }
}

/// One imported API or syscall the emulator serviced, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApiCall {
    /// The function's bare name (`CreateFileW`, `write`), or `sys_N` for a
    /// syscall number the table does not list.
    pub api: String,
    /// The Linux syscall number, `None` for an imported call.
    pub syscall: Option<u64>,
    /// The decoded arguments, in order.
    pub args: Vec<ArgValue>,
    /// The value left in the result register, or `None` for a `void`
    /// function.
    pub ret: Option<u64>,
    /// Where the call was made from: the return address of an imported
    /// call, the address of a `syscall`/`svc` instruction.
    pub caller: u64,
}

impl ApiCall {
    /// Renders the call as `api(args) -> ret`, a syscall as
    /// `syscall N name(args) -> ret`, without the return arrow for a `void`
    /// function.
    #[must_use]
    pub fn call_text(&self) -> String {
        let args: Vec<String> = self.args.iter().map(ArgValue::shown).collect();
        let number = self
            .syscall
            .map_or_else(String::new, |nr| format!("syscall {nr} "));
        let head = format!("{number}{}({})", self.api, args.join(", "));
        match self.ret {
            Some(ret) => format!("{head} -> {ret:#x}"),
            None => head,
        }
    }

    /// The decoded string arguments, each the text of a string pointer.
    pub fn strings(&self) -> impl Iterator<Item = &str> {
        self.args.iter().filter_map(ArgValue::text)
    }
}

/// Whether a declared C type is a pointer to narrow or to wide characters.
///
/// A string argument is read as text; any other pointer is left as an
/// address. The spelled type decides: a `wchar_t`, `WCHAR` or a `W`-suffixed
/// string typedef (`LPCWSTR`, `LPWSTR`, `PWSTR`) is wide, a `char` pointer or
/// an `A`-style string typedef (`LPCSTR`, `LPSTR`, `PSTR`) is narrow.
///
/// # Arguments
///
/// * `ty` - The parameter's C type as the library spells it.
/// * `pass` - What the machine passes it as; only a pointer is a string.
///
/// # Returns
///
/// `Some(true)` for a wide string pointer, `Some(false)` for a narrow one,
/// `None` when the type is not a string pointer.
#[must_use]
fn string_kind(ty: &str, pass: Option<Pass>) -> Option<bool> {
    if pass != Some(Pass::Pointer) {
        return None;
    }
    let wide = ty.contains("wchar") || ty.contains("WCHAR") || ty.contains("WSTR");
    if wide {
        return Some(true);
    }
    let narrow =
        ty.contains("char") || ty.contains("CSTR") || ty.contains("LPSTR") || ty.contains("PSTR");
    narrow.then_some(false)
}

/// Decodes the arguments of an imported call by the type library.
///
/// The library's declaration for `api` on the binary's platform names each
/// parameter's type and its constant group. A parameter with a constant
/// group is named by it ([`typelib::render`]); a string pointer is read as
/// text through `text`; any other pointer is `NULL` at zero or `ptr 0x...`;
/// an integer is its value. A call to a function the library does not
/// declare keeps no arguments, since nothing types them.
///
/// # Arguments
///
/// * `api` - The function's bare name.
/// * `format` - The calling binary's format, which picks the platform.
/// * `word` - The machine word in bits (32 or 64).
/// * `arg` - Reads the value of the `n`th argument.
/// * `text` - Reads a string from memory: the address and whether it is
///   wide, returning the text when one is there.
///
/// # Returns
///
/// The decoded arguments, in order, at most [`ARGS_MAX`].
pub(super) fn decode_api_args(
    api: &str,
    format: BinaryFormat,
    word: u8,
    arg: impl Fn(usize) -> u64,
    text: impl Fn(u64, bool) -> Option<String>,
) -> Vec<ArgValue> {
    let Some(decl) = typelib::declared(api, format) else {
        return Vec::new();
    };
    decl.params
        .iter()
        .take(ARGS_MAX)
        .enumerate()
        .map(|(i, param)| {
            let value = arg(i);
            let pass = typelib::pass_of(param.ty, word, format);
            if let Some(group) = param.group.and_then(typelib::group) {
                let bits = pass.map_or(word, |p| p.bits(word)).max(8);
                if let Some(named) = typelib::render(group, value, bits) {
                    return ArgValue::Named(named);
                }
            }
            match string_kind(param.ty, pass) {
                Some(wide) => match text(value, wide) {
                    Some(s) => ArgValue::Str { text: s, wide },
                    None if value == 0 => ArgValue::Null,
                    None => ArgValue::Ptr(value),
                },
                None => match pass {
                    Some(Pass::Pointer) if value == 0 => ArgValue::Null,
                    Some(Pass::Pointer) => ArgValue::Ptr(value),
                    _ => ArgValue::Int(value),
                },
            }
        })
        .collect()
}

/// Whether the type library declares a function to return nothing.
///
/// # Arguments
///
/// * `api` - The function's bare name.
/// * `format` - The calling binary's format.
///
/// # Returns
///
/// `true` when the library declares the function `void`, so a recorded call
/// leaves no result for the caller to read.
#[must_use]
pub(super) fn returns_void(api: &str, format: BinaryFormat) -> bool {
    typelib::declared(api, format).is_some_and(|d| d.ret == "void")
}

/// The argument position of the path a filesystem or process syscall takes,
/// so a run decodes it to a string an indicator can be read from.
///
/// The index counts from zero in the kernel's argument order, the same on
/// every architecture even though the registers differ. Only the primary
/// path of each call is named; a second path (`rename`) and structured
/// arguments (a `sockaddr`) are left as numbers.
///
/// # Arguments
///
/// * `name` - The syscall's name, as the number tables spell it.
///
/// # Returns
///
/// The argument index of the path, or `None` when the call takes none.
#[must_use]
fn syscall_string_arg(name: &str) -> Option<usize> {
    Some(match name {
        "open" | "creat" | "access" | "stat" | "lstat" | "unlink" | "chmod" | "chdir" | "mkdir"
        | "rmdir" | "readlink" | "truncate" | "statfs" | "chown" | "execve" => 0,
        "openat" | "newfstatat" | "execveat" | "unlinkat" | "readlinkat" | "mkdirat"
        | "faccessat" | "fchmodat" => 1,
        _ => return None,
    })
}

/// Decodes the arguments of a Linux syscall by the C library's declaration
/// of the call of the same name.
///
/// The kernel takes a syscall's arguments in the order its C wrapper
/// declares them (`open(path, flags, mode)`, `mmap(addr, len, prot, ...)`),
/// so the POSIX rows of the type library decode them as they decode an
/// imported call: the path as text, `prot` and `flags` by name. A call the
/// library does not declare keeps only its path argument
/// ([`syscall_string_arg`]), and one with none keeps no arguments.
///
/// # Arguments
///
/// * `name` - The syscall's name, as the number tables spell it.
/// * `word` - The machine word in bits.
/// * `arg` - Reads the `n`th syscall argument from its register.
/// * `text` - Reads a string from memory, as for [`decode_api_args`].
///
/// # Returns
///
/// The decoded arguments, in order.
pub(super) fn decode_syscall_args(
    name: &str,
    word: u8,
    arg: impl Fn(usize) -> u64,
    text: impl Fn(u64, bool) -> Option<String>,
) -> Vec<ArgValue> {
    if typelib::declared(name, BinaryFormat::Elf).is_some() {
        return decode_api_args(name, BinaryFormat::Elf, word, arg, text);
    }
    syscall_string_arg(name)
        .and_then(|idx| text(arg(idx), false))
        .map(|text| vec![ArgValue::Str { text, wide: false }])
        .unwrap_or_default()
}

/// Reads a printable string from memory, narrow or wide.
///
/// A narrow string is bytes up to a `NUL`; a wide string is 16-bit units
/// up to a zero unit, each unit's low byte taken when its high byte is zero.
/// Either stops at a byte that is not printable ASCII, so a pointer into
/// binary data yields nothing rather than mojibake, and the read is bounded
/// to `max` bytes.
///
/// # Arguments
///
/// * `addr` - The pointer; a zero address reads nothing.
/// * `wide` - Whether the characters are 16-bit.
/// * `max` - Most bytes to read.
/// * `byte` - Reads one byte of memory as a load does, `None` where nothing
///   is mapped.
///
/// # Returns
///
/// The text, or `None` when the address is zero, nothing is mapped, or no
/// printable character is there.
pub(super) fn read_text(
    addr: u64,
    wide: bool,
    max: usize,
    byte: impl Fn(u64) -> Option<u8>,
) -> Option<String> {
    if addr == 0 {
        return None;
    }
    let step = if wide { 2 } else { 1 };
    let mut out = String::new();
    let mut at = addr;
    for _ in 0..max {
        let low = byte(at)?;
        if low == 0 {
            break;
        }
        if wide && byte(at.wrapping_add(1))? != 0 {
            break;
        }
        if !(0x20..0x7f).contains(&low) {
            break;
        }
        out.push(char::from(low));
        at = at.wrapping_add(step);
    }
    (!out.is_empty()).then_some(out)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::*;

    /// An argument renders the way a call site reads it.
    #[test]
    fn arguments_render_as_a_call_site_would() {
        assert_eq!(ArgValue::Int(4).shown(), "4");
        assert_eq!(ArgValue::Int(0x40).shown(), "0x40");
        assert_eq!(
            ArgValue::Named("GENERIC_READ".to_owned()).shown(),
            "GENERIC_READ"
        );
        assert_eq!(ArgValue::Null.shown(), "NULL");
        assert_eq!(ArgValue::Ptr(0x1234).shown(), "ptr 0x1234");
        assert_eq!(
            ArgValue::Str {
                text: "C:\\x".to_owned(),
                wide: true,
            }
            .shown(),
            "L\"C:\\\\x\""
        );
    }

    /// A call renders as `api(args) -> ret`, the arrow dropped for a void
    /// function, and a syscall leads with its number.
    #[test]
    fn a_call_renders_with_and_without_a_return() {
        let call = ApiCall {
            api: "Sleep".to_owned(),
            syscall: None,
            args: vec![ArgValue::Int(1000)],
            ret: None,
            caller: 0,
        };
        assert_eq!(call.call_text(), "Sleep(0x3e8)");
        let call = ApiCall {
            api: "GetLastError".to_owned(),
            syscall: None,
            args: Vec::new(),
            ret: Some(0),
            caller: 0,
        };
        assert_eq!(call.call_text(), "GetLastError() -> 0x0");
        let call = ApiCall {
            api: "getpid".to_owned(),
            syscall: Some(39),
            args: Vec::new(),
            ret: Some(0),
            caller: 0,
        };
        assert_eq!(call.call_text(), "syscall 39 getpid() -> 0x0");
    }

    /// A syscall the C library declares decodes every argument by that
    /// declaration; one it does not keeps only its path.
    #[test]
    fn syscall_arguments_decode_by_the_c_declaration() {
        let path = |addr: u64, _wide: bool| (addr == 0x1000).then(|| "/etc/hosts".to_owned());
        let regs = [0x1000u64, 0, 0];
        let open = decode_syscall_args("open", 64, |n| regs.get(n).copied().unwrap_or(0), path);
        assert_eq!(open[0].text(), Some("/etc/hosts"));
        assert_eq!(open[1], ArgValue::Named("O_RDONLY".to_owned()));
        let at = [0u64, 0x1000, 0];
        let stat = decode_syscall_args("newfstatat", 64, |n| at.get(n).copied().unwrap_or(0), path);
        assert_eq!(stat.len(), 1);
        assert_eq!(stat[0].text(), Some("/etc/hosts"));
    }

    /// A string type reads as narrow or wide; anything else is no string.
    #[test]
    fn string_kinds_are_read_from_the_type() {
        assert_eq!(string_kind("LPCWSTR", Some(Pass::Pointer)), Some(true));
        assert_eq!(
            string_kind("const char *", Some(Pass::Pointer)),
            Some(false)
        );
        assert_eq!(string_kind("LPSTR", Some(Pass::Pointer)), Some(false));
        assert_eq!(string_kind("LPVOID", Some(Pass::Pointer)), None);
        assert_eq!(
            string_kind(
                "DWORD",
                Some(Pass::Int {
                    bits: 32,
                    signed: false
                })
            ),
            None
        );
    }

    /// A narrow and a wide string are read to a terminator, and binary data
    /// yields nothing.
    #[test]
    fn text_is_read_narrow_and_wide() {
        /// Where the planted bytes are read from; zero is a null pointer.
        const BASE: u64 = 0x1000;
        let read = |mem: &[u8], wide: bool| {
            read_text(BASE, wide, TEXT_MAX, |a| {
                a.checked_sub(BASE)
                    .and_then(|i| usize::try_from(i).ok())
                    .and_then(|i| mem.get(i).copied())
            })
        };
        assert_eq!(read(b"cmd.exe\0rest", false).as_deref(), Some("cmd.exe"));
        let wide: Vec<u8> = "hi"
            .encode_utf16()
            .flat_map(u16::to_le_bytes)
            .chain([0, 0])
            .collect();
        assert_eq!(read(&wide, true).as_deref(), Some("hi"));
        assert_eq!(read(&[0x00, 0xff, 0xfe], false), None);
        assert_eq!(read_text(0, false, TEXT_MAX, |_| Some(b'a')), None);
    }
}
