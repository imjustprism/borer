#!/usr/bin/env python3
"""Generate borer's typed API library: declarations, C type words, constants.

    python scripts/typelib.py          write the three tables
    python scripts/typelib.py --check  exit 1 when a table differs from what this writes

The tables live beside `prototypes.tsv` in crates/borer-engine/src/analysis/:

  typelib.tsv    name, os, return type, the constants the result is compared
                 with, the parameters (`type name`, `|` between them, `...`
                 for a variable list) and each parameter's constant group
  constants.tsv  group, kind (`flags` or `enum`), member name, value
  ctypes.tsv     a C type word and what the machine passes it as

Where the data comes from. Every row is authored here from the public API
documentation: the Win32 reference on learn.microsoft.com (the parameter
names and types each function page lists, and the documented values of the
constants those pages name), the C standard library, and the POSIX
specification and Linux man-pages for the POSIX rows, with the values glibc
uses on Linux x86 and x86-64 (where the kernel and glibc agree; `O_*`,
`MAP_*` and the signal numbers differ on other architectures). No header
text is copied: each declaration is restated as a list of parameter types
and names, and each constant as a name and a number. A function pointer is
spelled `void *` (or the Windows typedef that names it): what the machine
passes, without the signature it points at.

`prototypes.tsv` is a different table: the arity of 8,096 SDK and UCRT
functions, extracted once from the headers, which this script neither reads
nor rewrites. The library here is the smaller, typed layer over it, for the
functions an agent reads most (files, memory, processes, the registry,
sockets, libc), and a function it covers takes its arity from here too.

`os` is `win` for the Windows API, `posix` for POSIX and Linux, and `c` for
the C standard library, which both have: a PE reads the `win` and `c` rows,
an ELF or Mach-O the `posix` and `c` rows, so `socket` can name the address
families each platform numbers its own way.

The output is deterministic: rows are sorted (declarations by name and os,
constants by group, value and name, type words by name), values are written
as lowercase hex, and nothing depends on the clock or the environment, so
running this twice writes the same bytes and `--check` is the test.
"""

from __future__ import annotations

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "crates", "borer-engine", "src", "analysis")

# ---- C type words -------------------------------------------------------
# What the machine passes each word as: an integer of a width and sign, a
# float, a pointer, `long` (32 bits on Windows, the word elsewhere), or a
# word-wide integer (`size_t`). A pointer type is any word with `*` after it;
# these are the names that hide one (`HANDLE`, `LPCWSTR`).

CTYPES: dict[str, str] = {
    "void": "void",
    "char": "char",
    "signed char": "i8",
    "unsigned char": "u8",
    "short": "i16",
    "short int": "i16",
    "unsigned short": "u16",
    "int": "i32",
    "signed": "i32",
    "signed int": "i32",
    "unsigned": "u32",
    "unsigned int": "u32",
    "long": "long",
    "long int": "long",
    "unsigned long": "ulong",
    "long long": "i64",
    "unsigned long long": "u64",
    "__int64": "i64",
    "unsigned __int64": "u64",
    "float": "f32",
    "double": "f64",
    "bool": "u8",
    "_Bool": "u8",
    "wchar_t": "u16",
    "int8_t": "i8",
    "uint8_t": "u8",
    "int16_t": "i16",
    "uint16_t": "u16",
    "int32_t": "i32",
    "uint32_t": "u32",
    "int64_t": "i64",
    "uint64_t": "u64",
    "size_t": "word",
    "ssize_t": "sword",
    "intptr_t": "sword",
    "uintptr_t": "word",
    "ptrdiff_t": "sword",
    "off_t": "i64",
    "pid_t": "i32",
    "uid_t": "u32",
    "gid_t": "u32",
    "mode_t": "u32",
    "socklen_t": "u32",
    "nfds_t": "ulong",
    "useconds_t": "u32",
    "time_t": "i64",
    "pthread_t": "word",
    "sighandler_t": "ptr",
    "FILE": "word",
    "DIR": "word",
    "BOOL": "i32",
    "BOOLEAN": "u8",
    "BYTE": "u8",
    "CHAR": "char",
    "UCHAR": "u8",
    "WCHAR": "u16",
    "SHORT": "i16",
    "USHORT": "u16",
    "WORD": "u16",
    "ATOM": "u16",
    "INT": "i32",
    "UINT": "u32",
    "LONG": "i32",
    "ULONG": "u32",
    "DWORD": "u32",
    "HRESULT": "i32",
    "NTSTATUS": "i32",
    "LSTATUS": "i32",
    "REGSAM": "u32",
    "ACCESS_MASK": "u32",
    "LONGLONG": "i64",
    "ULONGLONG": "u64",
    "DWORD64": "u64",
    "ULONG64": "u64",
    "INT_PTR": "sword",
    "LONG_PTR": "sword",
    "UINT_PTR": "word",
    "ULONG_PTR": "word",
    "DWORD_PTR": "word",
    "SIZE_T": "word",
    "SSIZE_T": "sword",
    "WPARAM": "word",
    "LPARAM": "sword",
    "LRESULT": "sword",
    "SOCKET": "word",
    "HANDLE": "ptr",
    "HGLOBAL": "ptr",
    "HMODULE": "ptr",
    "HINSTANCE": "ptr",
    "HKEY": "ptr",
    "HWND": "ptr",
    "HDC": "ptr",
    "HHOOK": "ptr",
    "HINTERNET": "ptr",
    "HRSRC": "ptr",
    "FARPROC": "ptr",
    "PVOID": "ptr",
    "LPVOID": "ptr",
    "LPCVOID": "ptr",
    "PBYTE": "ptr",
    "LPBYTE": "ptr",
    "PDWORD": "ptr",
    "LPDWORD": "ptr",
    "PHKEY": "ptr",
    "PHANDLE": "ptr",
    "PSIZE_T": "ptr",
    "LPSTR": "ptr",
    "LPCSTR": "ptr",
    "LPWSTR": "ptr",
    "LPCWSTR": "ptr",
    "LPSECURITY_ATTRIBUTES": "ptr",
    "LPOVERLAPPED": "ptr",
    "LPOVERLAPPED_COMPLETION_ROUTINE": "ptr",
    "LPTHREAD_START_ROUTINE": "ptr",
    "LPSTARTUPINFOW": "ptr",
    "LPSTARTUPINFOA": "ptr",
    "LPPROCESS_INFORMATION": "ptr",
    "LPPROCESSENTRY32W": "ptr",
    "LPMODULEENTRY32W": "ptr",
    "LPTHREADENTRY32": "ptr",
    "LPCRITICAL_SECTION": "ptr",
    "LPWIN32_FIND_DATAW": "ptr",
    "LPWIN32_FIND_DATAA": "ptr",
    "HOOKPROC": "ptr",
    "REFCLSID": "ptr",
    "REFIID": "ptr",
    "LPUNKNOWN": "ptr",
    "PLARGE_INTEGER": "ptr",
    "LARGE_INTEGER": "i64",
    "HLOCAL": "ptr",
    "PSID": "ptr",
    "PLUID": "ptr",
    "PTOKEN_PRIVILEGES": "ptr",
    "PSID_NAME_USE": "ptr",
    "PSRWLOCK": "ptr",
    "PCONDITION_VARIABLE": "ptr",
    "PCONTEXT": "ptr",
    "LPFILETIME": "ptr",
    "LPSYSTEMTIME": "ptr",
    "LPSYSTEM_INFO": "ptr",
    "PCCERT_CONTEXT": "ptr",
    "PULONG": "ptr",
    "PUINT": "ptr",
    "PUCHAR": "ptr",
    "LPBOOL": "ptr",
    "LPTOP_LEVEL_EXCEPTION_FILTER": "ptr",
    "PEXCEPTION_POINTERS": "ptr",
    "HCRYPTPROV": "word",
    "LCID": "u32",
    "LANGID": "u16",
    "NET_API_STATUS": "u32",
    "TOKEN_INFORMATION_CLASS": "i32",
    "EXTENDED_NAME_FORMAT": "i32",
    "HEAP_INFORMATION_CLASS": "i32",
    "u_short": "u16",
    "in_addr_t": "ulong",
    "in_addr": "u32",
    "PCSTR": "ptr",
    "PCWSTR": "ptr",
    "PWSTR": "ptr",
    "PUNICODE_STRING": "ptr",
    "PCUNICODE_STRING": "ptr",
    "POBJECT_ATTRIBUTES": "ptr",
    "PCLIENT_ID": "ptr",
    "PROCESSINFOCLASS": "i32",
    "SYSTEM_INFORMATION_CLASS": "i32",
    "PAPCFUNC": "ptr",
    "LPPROC_THREAD_ATTRIBUTE_LIST": "ptr",
    "D3D_DRIVER_TYPE": "u32",
    "D3D_FEATURE_LEVEL": "u32",
    "IDXGIAdapter": "ptr",
    "ID3D11Device": "ptr",
    "ID3D11DeviceContext": "ptr",
    "IDXGISwapChain": "ptr",
    "DXGI_SWAP_CHAIN_DESC": "ptr",
}

# ---- constant groups ----------------------------------------------------
# `flags` groups decompose a value into members, widest first, with any bits
# no member covers left in hex; `enum` groups name a value one member states
# exactly. A member whose value is zero names a zero only. A pointer-wide
# constant is written at 64 bits as the documentation defines it (the
# registry roots are a `LONG` sign-extended into an `HKEY`, the failure
# results all ones); a 32-bit target reads the low half.

STANDARD_RIGHTS = [
    ("DELETE", 0x10000),
    ("READ_CONTROL", 0x20000),
    ("WRITE_DAC", 0x40000),
    ("WRITE_OWNER", 0x80000),
    ("SYNCHRONIZE", 0x100000),
    ("MAXIMUM_ALLOWED", 0x2000000),
]

GROUPS: dict[str, tuple[str, list[tuple[str, int]]]] = {
    # The classic `PROCESSINFOCLASS` values the WDK documents, the ones a
    # query for a PEB, times or image name passes.
    "process_info_class": (
        "enum",
        [
            ("ProcessBasicInformation", 0),
            ("ProcessQuotaLimits", 1),
            ("ProcessIoCounters", 2),
            ("ProcessVmCounters", 3),
            ("ProcessTimes", 4),
            ("ProcessBasePriority", 5),
            ("ProcessRaisePriority", 6),
            ("ProcessDebugPort", 7),
            ("ProcessExceptionPort", 8),
            ("ProcessAccessToken", 9),
            ("ProcessWow64Information", 26),
            ("ProcessImageFileName", 27),
            ("ProcessBreakOnTermination", 29),
        ],
    ),
    # The `SYSTEM_INFORMATION_CLASS` values the classic system queries
    # pass, as the WDK reference numbers them.
    "system_info_class": (
        "enum",
        [
            ("SystemBasicInformation", 0),
            ("SystemProcessorInformation", 1),
            ("SystemPerformanceInformation", 2),
            ("SystemTimeOfDayInformation", 3),
            ("SystemProcessInformation", 5),
            ("SystemProcessorPerformanceInformation", 8),
            ("SystemHandleInformation", 16),
            ("SystemPagefileInformation", 18),
            ("SystemInterruptInformation", 23),
            ("SystemExceptionInformation", 33),
            ("SystemKernelDebuggerInformation", 35),
            ("SystemModuleInformation", 11),
        ],
    ),
    # `D3D_DRIVER_TYPE`, as the D3D11 reference numbers it.
    "d3d_driver_type": (
        "enum",
        [
            ("D3D_DRIVER_TYPE_UNKNOWN", 0),
            ("D3D_DRIVER_TYPE_HARDWARE", 1),
            ("D3D_DRIVER_TYPE_REFERENCE", 2),
            ("D3D_DRIVER_TYPE_NULL", 3),
            ("D3D_DRIVER_TYPE_SOFTWARE", 4),
            ("D3D_DRIVER_TYPE_WARP", 5),
        ],
    ),
    "token_information_class": (
        "enum",
        [
            ("TokenUser", 1),
            ("TokenGroups", 2),
            ("TokenPrivileges", 3),
            ("TokenOwner", 4),
            ("TokenPrimaryGroup", 5),
            ("TokenDefaultDacl", 6),
            ("TokenSource", 7),
            ("TokenType", 8),
            ("TokenImpersonationLevel", 9),
            ("TokenStatistics", 10),
            ("TokenRestrictedSids", 11),
            ("TokenSessionId", 12),
            ("TokenGroupsAndPrivileges", 13),
            ("TokenSessionReference", 14),
            ("TokenSandBoxInert", 15),
            ("TokenAuditPolicy", 16),
            ("TokenOrigin", 17),
            ("TokenElevationType", 18),
            ("TokenLinkedToken", 19),
            ("TokenElevation", 20),
            ("TokenHasRestrictions", 21),
            ("TokenAccessInformation", 22),
            ("TokenVirtualizationAllowed", 23),
            ("TokenVirtualizationEnabled", 24),
            ("TokenIntegrityLevel", 25),
            ("TokenUIAccess", 26),
            ("TokenMandatoryPolicy", 27),
            ("TokenLogonSid", 28),
            ("TokenIsAppContainer", 29),
            ("TokenCapabilities", 30),
            ("TokenAppContainerSid", 31),
            ("TokenAppContainerNumber", 32),
            ("TokenUserClaimAttributes", 33),
            ("TokenDeviceClaimAttributes", 34),
        ],
    ),
    "local_alloc": (
        "flags",
        [("LMEM_FIXED", 0x0), ("LMEM_MOVEABLE", 0x2), ("LMEM_ZEROINIT", 0x40)],
    ),
    "format_message": (
        "flags",
        [
            ("FORMAT_MESSAGE_ALLOCATE_BUFFER", 0x100),
            ("FORMAT_MESSAGE_IGNORE_INSERTS", 0x200),
            ("FORMAT_MESSAGE_FROM_STRING", 0x400),
            ("FORMAT_MESSAGE_FROM_HMODULE", 0x800),
            ("FORMAT_MESSAGE_FROM_SYSTEM", 0x1000),
            ("FORMAT_MESSAGE_ARGUMENT_ARRAY", 0x2000),
        ],
    ),
    "file_type": (
        "enum",
        [
            ("FILE_TYPE_UNKNOWN", 0x0),
            ("FILE_TYPE_DISK", 0x1),
            ("FILE_TYPE_CHAR", 0x2),
            ("FILE_TYPE_PIPE", 0x3),
            ("FILE_TYPE_REMOTE", 0x8000),
        ],
    ),
    "code_page": (
        "enum",
        [
            ("CP_ACP", 0),
            ("CP_OEMCP", 1),
            ("CP_MACCP", 2),
            ("CP_THREAD_ACP", 3),
            ("CP_SYMBOL", 42),
            ("CP_UTF7", 65000),
            ("CP_UTF8", 65001),
        ],
    ),
    "extended_name_format": (
        "enum",
        [
            ("NameUnknown", 0),
            ("NameFullyQualifiedDN", 1),
            ("NameSamCompatible", 2),
            ("NameDisplay", 3),
            ("NameUniqueId", 6),
            ("NameCanonical", 7),
            ("NameUserPrincipal", 8),
            ("NameCanonicalEx", 9),
            ("NameServicePrincipal", 10),
            ("NameDnsDomain", 12),
            ("NameGivenName", 13),
            ("NameSurname", 14),
        ],
    ),
    "bool": ("enum", [("FALSE", 0), ("TRUE", 1)]),
    "file_access": (
        "flags",
        [
            ("FILE_READ_DATA", 0x1),
            ("FILE_WRITE_DATA", 0x2),
            ("FILE_APPEND_DATA", 0x4),
            ("FILE_READ_EA", 0x8),
            ("FILE_WRITE_EA", 0x10),
            ("FILE_EXECUTE", 0x20),
            ("FILE_READ_ATTRIBUTES", 0x80),
            ("FILE_WRITE_ATTRIBUTES", 0x100),
            *STANDARD_RIGHTS,
            ("GENERIC_ALL", 0x10000000),
            ("GENERIC_EXECUTE", 0x20000000),
            ("GENERIC_WRITE", 0x40000000),
            ("GENERIC_READ", 0x80000000),
        ],
    ),
    "file_share": (
        "flags",
        [("FILE_SHARE_READ", 0x1), ("FILE_SHARE_WRITE", 0x2), ("FILE_SHARE_DELETE", 0x4)],
    ),
    "file_disposition": (
        "enum",
        [
            ("CREATE_NEW", 1),
            ("CREATE_ALWAYS", 2),
            ("OPEN_EXISTING", 3),
            ("OPEN_ALWAYS", 4),
            ("TRUNCATE_EXISTING", 5),
        ],
    ),
    "file_flags": (
        "flags",
        [
            ("FILE_ATTRIBUTE_READONLY", 0x1),
            ("FILE_ATTRIBUTE_HIDDEN", 0x2),
            ("FILE_ATTRIBUTE_SYSTEM", 0x4),
            ("FILE_ATTRIBUTE_DIRECTORY", 0x10),
            ("FILE_ATTRIBUTE_ARCHIVE", 0x20),
            ("FILE_ATTRIBUTE_NORMAL", 0x80),
            ("FILE_ATTRIBUTE_TEMPORARY", 0x100),
            ("FILE_ATTRIBUTE_OFFLINE", 0x1000),
            ("FILE_ATTRIBUTE_ENCRYPTED", 0x4000),
            ("FILE_FLAG_OPEN_NO_RECALL", 0x100000),
            ("FILE_FLAG_OPEN_REPARSE_POINT", 0x200000),
            ("FILE_FLAG_POSIX_SEMANTICS", 0x1000000),
            ("FILE_FLAG_BACKUP_SEMANTICS", 0x2000000),
            ("FILE_FLAG_DELETE_ON_CLOSE", 0x4000000),
            ("FILE_FLAG_SEQUENTIAL_SCAN", 0x8000000),
            ("FILE_FLAG_RANDOM_ACCESS", 0x10000000),
            ("FILE_FLAG_NO_BUFFERING", 0x20000000),
            ("FILE_FLAG_OVERLAPPED", 0x40000000),
            ("FILE_FLAG_WRITE_THROUGH", 0x80000000),
        ],
    ),
    "move_method": ("enum", [("FILE_BEGIN", 0), ("FILE_CURRENT", 1), ("FILE_END", 2)]),
    "move_file": (
        "flags",
        [
            ("MOVEFILE_REPLACE_EXISTING", 0x1),
            ("MOVEFILE_COPY_ALLOWED", 0x2),
            ("MOVEFILE_DELAY_UNTIL_REBOOT", 0x4),
            ("MOVEFILE_WRITE_THROUGH", 0x8),
        ],
    ),
    "page_protect": (
        "flags",
        [
            ("PAGE_NOACCESS", 0x1),
            ("PAGE_READONLY", 0x2),
            ("PAGE_READWRITE", 0x4),
            ("PAGE_WRITECOPY", 0x8),
            ("PAGE_EXECUTE", 0x10),
            ("PAGE_EXECUTE_READ", 0x20),
            ("PAGE_EXECUTE_READWRITE", 0x40),
            ("PAGE_EXECUTE_WRITECOPY", 0x80),
            ("PAGE_GUARD", 0x100),
            ("PAGE_NOCACHE", 0x200),
            ("PAGE_WRITECOMBINE", 0x400),
        ],
    ),
    "mem_type": (
        "flags",
        [
            ("MEM_COMMIT", 0x1000),
            ("MEM_RESERVE", 0x2000),
            ("MEM_DECOMMIT", 0x4000),
            ("MEM_RELEASE", 0x8000),
            ("MEM_RESET", 0x80000),
            ("MEM_TOP_DOWN", 0x100000),
            ("MEM_WRITE_WATCH", 0x200000),
            ("MEM_PHYSICAL", 0x400000),
            ("MEM_RESET_UNDO", 0x1000000),
            ("MEM_LARGE_PAGES", 0x20000000),
        ],
    ),
    "heap_flags": (
        "flags",
        [
            ("HEAP_NO_SERIALIZE", 0x1),
            ("HEAP_GENERATE_EXCEPTIONS", 0x4),
            ("HEAP_ZERO_MEMORY", 0x8),
        ],
    ),
    "file_map": (
        "flags",
        [
            ("FILE_MAP_COPY", 0x1),
            ("FILE_MAP_WRITE", 0x2),
            ("FILE_MAP_READ", 0x4),
            ("FILE_MAP_EXECUTE", 0x20),
            ("FILE_MAP_ALL_ACCESS", 0xF001F),
        ],
    ),
    "hkey": (
        "enum",
        [
            ("HKEY_CLASSES_ROOT", 0xFFFFFFFF80000000),
            ("HKEY_CURRENT_USER", 0xFFFFFFFF80000001),
            ("HKEY_LOCAL_MACHINE", 0xFFFFFFFF80000002),
            ("HKEY_USERS", 0xFFFFFFFF80000003),
            ("HKEY_PERFORMANCE_DATA", 0xFFFFFFFF80000004),
            ("HKEY_CURRENT_CONFIG", 0xFFFFFFFF80000005),
            ("HKEY_DYN_DATA", 0xFFFFFFFF80000006),
        ],
    ),
    "reg_sam": (
        "flags",
        [
            ("KEY_QUERY_VALUE", 0x1),
            ("KEY_SET_VALUE", 0x2),
            ("KEY_CREATE_SUB_KEY", 0x4),
            ("KEY_ENUMERATE_SUB_KEYS", 0x8),
            ("KEY_NOTIFY", 0x10),
            ("KEY_CREATE_LINK", 0x20),
            ("KEY_WOW64_64KEY", 0x100),
            ("KEY_WOW64_32KEY", 0x200),
            ("KEY_WRITE", 0x20006),
            ("KEY_READ", 0x20019),
            ("KEY_ALL_ACCESS", 0xF003F),
            *STANDARD_RIGHTS,
        ],
    ),
    "reg_options": (
        "flags",
        [
            ("REG_OPTION_NON_VOLATILE", 0x0),
            ("REG_OPTION_VOLATILE", 0x1),
            ("REG_OPTION_CREATE_LINK", 0x2),
            ("REG_OPTION_BACKUP_RESTORE", 0x4),
            ("REG_OPTION_OPEN_LINK", 0x8),
        ],
    ),
    "reg_type": (
        "enum",
        [
            ("REG_NONE", 0),
            ("REG_SZ", 1),
            ("REG_EXPAND_SZ", 2),
            ("REG_BINARY", 3),
            ("REG_DWORD", 4),
            ("REG_DWORD_BIG_ENDIAN", 5),
            ("REG_LINK", 6),
            ("REG_MULTI_SZ", 7),
            ("REG_QWORD", 11),
        ],
    ),
    "process_access": (
        "flags",
        [
            ("PROCESS_TERMINATE", 0x1),
            ("PROCESS_CREATE_THREAD", 0x2),
            ("PROCESS_SET_SESSIONID", 0x4),
            ("PROCESS_VM_OPERATION", 0x8),
            ("PROCESS_VM_READ", 0x10),
            ("PROCESS_VM_WRITE", 0x20),
            ("PROCESS_DUP_HANDLE", 0x40),
            ("PROCESS_CREATE_PROCESS", 0x80),
            ("PROCESS_SET_QUOTA", 0x100),
            ("PROCESS_SET_INFORMATION", 0x200),
            ("PROCESS_QUERY_INFORMATION", 0x400),
            ("PROCESS_SUSPEND_RESUME", 0x800),
            ("PROCESS_QUERY_LIMITED_INFORMATION", 0x1000),
            ("PROCESS_ALL_ACCESS", 0x1FFFFF),
            *STANDARD_RIGHTS,
        ],
    ),
    "thread_access": (
        "flags",
        [
            ("THREAD_TERMINATE", 0x1),
            ("THREAD_SUSPEND_RESUME", 0x2),
            ("THREAD_GET_CONTEXT", 0x8),
            ("THREAD_SET_CONTEXT", 0x10),
            ("THREAD_SET_INFORMATION", 0x20),
            ("THREAD_QUERY_INFORMATION", 0x40),
            ("THREAD_SET_THREAD_TOKEN", 0x80),
            ("THREAD_IMPERSONATE", 0x100),
            ("THREAD_DIRECT_IMPERSONATION", 0x200),
            ("THREAD_QUERY_LIMITED_INFORMATION", 0x800),
            ("THREAD_ALL_ACCESS", 0x1FFFFF),
            *STANDARD_RIGHTS,
        ],
    ),
    "token_access": (
        "flags",
        [
            ("TOKEN_ASSIGN_PRIMARY", 0x1),
            ("TOKEN_DUPLICATE", 0x2),
            ("TOKEN_IMPERSONATE", 0x4),
            ("TOKEN_QUERY", 0x8),
            ("TOKEN_QUERY_SOURCE", 0x10),
            ("TOKEN_ADJUST_PRIVILEGES", 0x20),
            ("TOKEN_ADJUST_GROUPS", 0x40),
            ("TOKEN_ADJUST_DEFAULT", 0x80),
            ("TOKEN_ADJUST_SESSIONID", 0x100),
            ("TOKEN_ALL_ACCESS", 0xF01FF),
            *STANDARD_RIGHTS,
        ],
    ),
    "process_creation": (
        "flags",
        [
            ("DEBUG_PROCESS", 0x1),
            ("DEBUG_ONLY_THIS_PROCESS", 0x2),
            ("CREATE_SUSPENDED", 0x4),
            ("DETACHED_PROCESS", 0x8),
            ("CREATE_NEW_CONSOLE", 0x10),
            ("NORMAL_PRIORITY_CLASS", 0x20),
            ("IDLE_PRIORITY_CLASS", 0x40),
            ("HIGH_PRIORITY_CLASS", 0x80),
            ("REALTIME_PRIORITY_CLASS", 0x100),
            ("CREATE_NEW_PROCESS_GROUP", 0x200),
            ("CREATE_UNICODE_ENVIRONMENT", 0x400),
            ("CREATE_SEPARATE_WOW_VDM", 0x800),
            ("INHERIT_PARENT_AFFINITY", 0x10000),
            ("CREATE_PROTECTED_PROCESS", 0x40000),
            ("EXTENDED_STARTUPINFO_PRESENT", 0x80000),
            ("CREATE_BREAKAWAY_FROM_JOB", 0x1000000),
            ("CREATE_DEFAULT_ERROR_MODE", 0x4000000),
            ("CREATE_NO_WINDOW", 0x8000000),
        ],
    ),
    "thread_creation": (
        "flags",
        [("CREATE_SUSPENDED", 0x4), ("STACK_SIZE_PARAM_IS_A_RESERVATION", 0x10000)],
    ),
    "duplicate": (
        "flags",
        [("DUPLICATE_CLOSE_SOURCE", 0x1), ("DUPLICATE_SAME_ACCESS", 0x2)],
    ),
    "timeout": ("enum", [("INFINITE", 0xFFFFFFFF)]),
    "wait_result": (
        "enum",
        [
            ("WAIT_OBJECT_0", 0x0),
            ("WAIT_ABANDONED", 0x80),
            ("WAIT_TIMEOUT", 0x102),
            ("WAIT_FAILED", 0xFFFFFFFF),
        ],
    ),
    "handle": ("enum", [("INVALID_HANDLE_VALUE", 0xFFFFFFFFFFFFFFFF)]),
    "std_handle": (
        "enum",
        [
            ("STD_ERROR_HANDLE", 0xFFFFFFF4),
            ("STD_OUTPUT_HANDLE", 0xFFFFFFF5),
            ("STD_INPUT_HANDLE", 0xFFFFFFF6),
        ],
    ),
    "load_library": (
        "flags",
        [
            ("DONT_RESOLVE_DLL_REFERENCES", 0x1),
            ("LOAD_LIBRARY_AS_DATAFILE", 0x2),
            ("LOAD_WITH_ALTERED_SEARCH_PATH", 0x8),
            ("LOAD_IGNORE_CODE_AUTHZ_LEVEL", 0x10),
            ("LOAD_LIBRARY_AS_IMAGE_RESOURCE", 0x20),
            ("LOAD_LIBRARY_AS_DATAFILE_EXCLUSIVE", 0x40),
            ("LOAD_LIBRARY_SEARCH_DLL_LOAD_DIR", 0x100),
            ("LOAD_LIBRARY_SEARCH_APPLICATION_DIR", 0x200),
            ("LOAD_LIBRARY_SEARCH_USER_DIRS", 0x400),
            ("LOAD_LIBRARY_SEARCH_SYSTEM32", 0x800),
            ("LOAD_LIBRARY_SEARCH_DEFAULT_DIRS", 0x1000),
        ],
    ),
    "snapshot": (
        "flags",
        [
            ("TH32CS_SNAPHEAPLIST", 0x1),
            ("TH32CS_SNAPPROCESS", 0x2),
            ("TH32CS_SNAPTHREAD", 0x4),
            ("TH32CS_SNAPMODULE", 0x8),
            ("TH32CS_SNAPALL", 0xF),
            ("TH32CS_SNAPMODULE32", 0x10),
            ("TH32CS_INHERIT", 0x80000000),
        ],
    ),
    "message_box": (
        "flags",
        [
            ("MB_OK", 0x0),
            ("MB_OKCANCEL", 0x1),
            ("MB_ABORTRETRYIGNORE", 0x2),
            ("MB_YESNOCANCEL", 0x3),
            ("MB_YESNO", 0x4),
            ("MB_RETRYCANCEL", 0x5),
            ("MB_ICONERROR", 0x10),
            ("MB_ICONQUESTION", 0x20),
            ("MB_ICONWARNING", 0x30),
            ("MB_ICONINFORMATION", 0x40),
            ("MB_DEFBUTTON2", 0x100),
            ("MB_DEFBUTTON3", 0x200),
            ("MB_SYSTEMMODAL", 0x1000),
            ("MB_TOPMOST", 0x40000),
        ],
    ),
    "dialog_result": (
        "enum",
        [
            ("IDOK", 1),
            ("IDCANCEL", 2),
            ("IDABORT", 3),
            ("IDRETRY", 4),
            ("IDIGNORE", 5),
            ("IDYES", 6),
            ("IDNO", 7),
        ],
    ),
    "show_window": (
        "enum",
        [
            ("SW_HIDE", 0),
            ("SW_SHOWNORMAL", 1),
            ("SW_SHOWMINIMIZED", 2),
            ("SW_SHOWMAXIMIZED", 3),
            ("SW_SHOWNOACTIVATE", 4),
            ("SW_SHOW", 5),
            ("SW_MINIMIZE", 6),
            ("SW_SHOWMINNOACTIVE", 7),
            ("SW_SHOWNA", 8),
            ("SW_RESTORE", 9),
            ("SW_SHOWDEFAULT", 10),
        ],
    ),
    "hook": (
        "enum",
        [
            ("WH_KEYBOARD", 2),
            ("WH_GETMESSAGE", 3),
            ("WH_CALLWNDPROC", 4),
            ("WH_CBT", 5),
            ("WH_MOUSE", 7),
            ("WH_KEYBOARD_LL", 13),
            ("WH_MOUSE_LL", 14),
        ],
    ),
    "clsctx": (
        "flags",
        [
            ("CLSCTX_INPROC_SERVER", 0x1),
            ("CLSCTX_INPROC_HANDLER", 0x2),
            ("CLSCTX_LOCAL_SERVER", 0x4),
            ("CLSCTX_REMOTE_SERVER", 0x10),
        ],
    ),
    "csidl": (
        "enum",
        [
            ("CSIDL_DESKTOP", 0x0),
            ("CSIDL_PERSONAL", 0x5),
            ("CSIDL_STARTUP", 0x7),
            ("CSIDL_APPDATA", 0x1A),
            ("CSIDL_LOCAL_APPDATA", 0x1C),
            ("CSIDL_COMMON_APPDATA", 0x23),
            ("CSIDL_WINDOWS", 0x24),
            ("CSIDL_SYSTEM", 0x25),
            ("CSIDL_PROGRAM_FILES", 0x26),
        ],
    ),
    "internet_open": (
        "enum",
        [
            ("INTERNET_OPEN_TYPE_PRECONFIG", 0),
            ("INTERNET_OPEN_TYPE_DIRECT", 1),
            ("INTERNET_OPEN_TYPE_PROXY", 3),
        ],
    ),
    "internet_flags": (
        "flags",
        [
            ("INTERNET_FLAG_PRAGMA_NOCACHE", 0x100),
            ("INTERNET_FLAG_NO_UI", 0x200),
            ("INTERNET_FLAG_IGNORE_CERT_CN_INVALID", 0x1000),
            ("INTERNET_FLAG_IGNORE_CERT_DATE_INVALID", 0x2000),
            ("INTERNET_FLAG_NO_COOKIES", 0x80000),
            ("INTERNET_FLAG_KEEP_CONNECTION", 0x400000),
            ("INTERNET_FLAG_SECURE", 0x800000),
            ("INTERNET_FLAG_NO_CACHE_WRITE", 0x4000000),
            ("INTERNET_FLAG_RELOAD", 0x80000000),
        ],
    ),
    "af_win": (
        "enum",
        [("AF_UNSPEC", 0), ("AF_UNIX", 1), ("AF_INET", 2), ("AF_INET6", 23)],
    ),
    "af_posix": (
        "enum",
        [
            ("AF_UNSPEC", 0),
            ("AF_UNIX", 1),
            ("AF_INET", 2),
            ("AF_INET6", 10),
            ("AF_NETLINK", 16),
            ("AF_PACKET", 17),
        ],
    ),
    "sock_type_win": (
        "enum",
        [("SOCK_STREAM", 1), ("SOCK_DGRAM", 2), ("SOCK_RAW", 3), ("SOCK_SEQPACKET", 5)],
    ),
    "sock_type_posix": (
        "flags",
        [
            ("SOCK_STREAM", 0x1),
            ("SOCK_DGRAM", 0x2),
            ("SOCK_RAW", 0x3),
            ("SOCK_SEQPACKET", 0x5),
            ("SOCK_NONBLOCK", 0x800),
            ("SOCK_CLOEXEC", 0x80000),
        ],
    ),
    "ipproto": (
        "enum",
        [("IPPROTO_IP", 0), ("IPPROTO_ICMP", 1), ("IPPROTO_TCP", 6), ("IPPROTO_UDP", 17)],
    ),
    # The `send(2)` / `recv(2)` message flags, as glibc numbers them on
    # Linux x86 and x86-64.
    "msg_flags_posix": (
        "flags",
        [
            ("MSG_OOB", 0x1),
            ("MSG_PEEK", 0x2),
            ("MSG_DONTROUTE", 0x4),
            ("MSG_CTRUNC", 0x8),
            ("MSG_TRUNC", 0x20),
            ("MSG_DONTWAIT", 0x40),
            ("MSG_EOR", 0x80),
            ("MSG_WAITALL", 0x100),
            ("MSG_NOSIGNAL", 0x4000),
        ],
    ),
    # Winsock numbers the message flags its own way.
    "msg_flags_win": (
        "flags",
        [
            ("MSG_OOB", 0x1),
            ("MSG_PEEK", 0x2),
            ("MSG_DONTROUTE", 0x4),
            ("MSG_WAITALL", 0x8),
            ("MSG_PARTIAL", 0x8000),
        ],
    ),
    "shutdown_how": ("enum", [("SHUT_RD", 0), ("SHUT_WR", 1), ("SHUT_RDWR", 2)]),
    "open_flags": (
        "flags",
        [
            ("O_RDONLY", 0x0),
            ("O_WRONLY", 0x1),
            ("O_RDWR", 0x2),
            ("O_CREAT", 0x40),
            ("O_EXCL", 0x80),
            ("O_NOCTTY", 0x100),
            ("O_TRUNC", 0x200),
            ("O_APPEND", 0x400),
            ("O_NONBLOCK", 0x800),
            ("O_DSYNC", 0x1000),
            ("O_ASYNC", 0x2000),
            ("O_DIRECT", 0x4000),
            ("O_DIRECTORY", 0x10000),
            ("O_NOFOLLOW", 0x20000),
            ("O_NOATIME", 0x40000),
            ("O_CLOEXEC", 0x80000),
            ("O_SYNC", 0x101000),
            ("O_PATH", 0x200000),
        ],
    ),
    "prot": (
        "flags",
        [("PROT_NONE", 0x0), ("PROT_READ", 0x1), ("PROT_WRITE", 0x2), ("PROT_EXEC", 0x4)],
    ),
    "map_flags": (
        "flags",
        [
            ("MAP_SHARED", 0x1),
            ("MAP_PRIVATE", 0x2),
            ("MAP_FIXED", 0x10),
            ("MAP_ANONYMOUS", 0x20),
            ("MAP_GROWSDOWN", 0x100),
            ("MAP_DENYWRITE", 0x800),
            ("MAP_EXECUTABLE", 0x1000),
            ("MAP_LOCKED", 0x2000),
            ("MAP_NORESERVE", 0x4000),
            ("MAP_POPULATE", 0x8000),
            ("MAP_NONBLOCK", 0x10000),
            ("MAP_STACK", 0x20000),
            ("MAP_HUGETLB", 0x40000),
        ],
    ),
    "map_result": ("enum", [("MAP_FAILED", 0xFFFFFFFFFFFFFFFF)]),
    "seek": ("enum", [("SEEK_SET", 0), ("SEEK_CUR", 1), ("SEEK_END", 2)]),
    "access_mode": (
        "flags",
        [("F_OK", 0x0), ("X_OK", 0x1), ("W_OK", 0x2), ("R_OK", 0x4)],
    ),
    "signal": (
        "enum",
        [
            ("SIGHUP", 1),
            ("SIGINT", 2),
            ("SIGQUIT", 3),
            ("SIGILL", 4),
            ("SIGTRAP", 5),
            ("SIGABRT", 6),
            ("SIGBUS", 7),
            ("SIGFPE", 8),
            ("SIGKILL", 9),
            ("SIGUSR1", 10),
            ("SIGSEGV", 11),
            ("SIGUSR2", 12),
            ("SIGPIPE", 13),
            ("SIGALRM", 14),
            ("SIGTERM", 15),
            ("SIGCHLD", 17),
            ("SIGCONT", 18),
            ("SIGSTOP", 19),
            ("SIGTSTP", 20),
            ("SIGTTIN", 21),
            ("SIGTTOU", 22),
            ("SIGURG", 23),
            ("SIGXCPU", 24),
            ("SIGXFSZ", 25),
            ("SIGPROF", 27),
            ("SIGWINCH", 28),
            ("SIGIO", 29),
            ("SIGSYS", 31),
        ],
    ),
    # How `sigprocmask` changes the blocked set, as POSIX orders it.
    "sigmask": ("enum", [("SIG_BLOCK", 0), ("SIG_UNBLOCK", 1), ("SIG_SETMASK", 2)]),
    "ptrace": (
        "enum",
        [
            ("PTRACE_TRACEME", 0),
            ("PTRACE_PEEKTEXT", 1),
            ("PTRACE_PEEKDATA", 2),
            ("PTRACE_PEEKUSER", 3),
            ("PTRACE_POKETEXT", 4),
            ("PTRACE_POKEDATA", 5),
            ("PTRACE_POKEUSER", 6),
            ("PTRACE_CONT", 7),
            ("PTRACE_KILL", 8),
            ("PTRACE_SINGLESTEP", 9),
            ("PTRACE_GETREGS", 12),
            ("PTRACE_SETREGS", 13),
            ("PTRACE_ATTACH", 16),
            ("PTRACE_DETACH", 17),
            ("PTRACE_SYSCALL", 24),
            ("PTRACE_SETOPTIONS", 0x4200),
            ("PTRACE_SEIZE", 0x4206),
        ],
    ),
    "dlopen": (
        "flags",
        [
            ("RTLD_LOCAL", 0x0),
            ("RTLD_LAZY", 0x1),
            ("RTLD_NOW", 0x2),
            ("RTLD_NOLOAD", 0x4),
            ("RTLD_DEEPBIND", 0x8),
            ("RTLD_GLOBAL", 0x100),
            ("RTLD_NODELETE", 0x1000),
        ],
    ),
    "dl_handle": ("enum", [("RTLD_DEFAULT", 0x0), ("RTLD_NEXT", 0xFFFFFFFFFFFFFFFF)]),
    "fcntl": (
        "enum",
        [
            ("F_DUPFD", 0),
            ("F_GETFD", 1),
            ("F_SETFD", 2),
            ("F_GETFL", 3),
            ("F_SETFL", 4),
            ("F_GETLK", 5),
            ("F_SETLK", 6),
            ("F_SETLKW", 7),
        ],
    ),
    "prctl": (
        "enum",
        [
            ("PR_SET_PDEATHSIG", 1),
            ("PR_GET_DUMPABLE", 3),
            ("PR_SET_DUMPABLE", 4),
            ("PR_SET_NAME", 15),
            ("PR_GET_NAME", 16),
            ("PR_SET_SECCOMP", 22),
            ("PR_SET_NO_NEW_PRIVS", 38),
        ],
    ),
    "wait_options": (
        "flags",
        [("WNOHANG", 0x1), ("WUNTRACED", 0x2), ("WCONTINUED", 0x8)],
    ),
    # The `poll(2)` event and return bits, as Linux numbers them.
    "poll": (
        "flags",
        [
            ("POLLIN", 0x1),
            ("POLLPRI", 0x2),
            ("POLLOUT", 0x4),
            ("POLLERR", 0x8),
            ("POLLHUP", 0x10),
            ("POLLNVAL", 0x20),
            ("POLLRDNORM", 0x40),
            ("POLLRDBAND", 0x80),
            ("POLLWRNORM", 0x100),
            ("POLLWRBAND", 0x200),
            ("POLLRDHUP", 0x2000),
        ],
    ),
}

# ---- declarations -------------------------------------------------------
# One entry per function: (name, os, return type, the result's group, the
# parameters as (type, name, group)). A group of None leaves the parameter's
# constants as numbers; "..." as a parameter is a variable list.

Param = tuple[str, str, str | None]

WIN: list[tuple[str, str, str | None, list[Param]]] = [
    (
        "CreateFileW",
        "HANDLE",
        "handle",
        [
            ("LPCWSTR", "lpFileName", None),
            ("DWORD", "dwDesiredAccess", "file_access"),
            ("DWORD", "dwShareMode", "file_share"),
            ("LPSECURITY_ATTRIBUTES", "lpSecurityAttributes", None),
            ("DWORD", "dwCreationDisposition", "file_disposition"),
            ("DWORD", "dwFlagsAndAttributes", "file_flags"),
            ("HANDLE", "hTemplateFile", None),
        ],
    ),
    (
        "CreateFileA",
        "HANDLE",
        "handle",
        [
            ("LPCSTR", "lpFileName", None),
            ("DWORD", "dwDesiredAccess", "file_access"),
            ("DWORD", "dwShareMode", "file_share"),
            ("LPSECURITY_ATTRIBUTES", "lpSecurityAttributes", None),
            ("DWORD", "dwCreationDisposition", "file_disposition"),
            ("DWORD", "dwFlagsAndAttributes", "file_flags"),
            ("HANDLE", "hTemplateFile", None),
        ],
    ),
    (
        "ReadFile",
        "BOOL",
        None,
        [
            ("HANDLE", "hFile", None),
            ("LPVOID", "lpBuffer", None),
            ("DWORD", "nNumberOfBytesToRead", None),
            ("LPDWORD", "lpNumberOfBytesRead", None),
            ("LPOVERLAPPED", "lpOverlapped", None),
        ],
    ),
    (
        "ReadFileEx",
        "BOOL",
        None,
        [
            ("HANDLE", "hFile", None),
            ("LPVOID", "lpBuffer", None),
            ("DWORD", "nNumberOfBytesToRead", None),
            ("LPOVERLAPPED", "lpOverlapped", None),
            ("LPOVERLAPPED_COMPLETION_ROUTINE", "lpCompletionRoutine", None),
        ],
    ),
    (
        "WriteFile",
        "BOOL",
        None,
        [
            ("HANDLE", "hFile", None),
            ("LPCVOID", "lpBuffer", None),
            ("DWORD", "nNumberOfBytesToWrite", None),
            ("LPDWORD", "lpNumberOfBytesWritten", None),
            ("LPOVERLAPPED", "lpOverlapped", None),
        ],
    ),
    (
        "WriteFileEx",
        "BOOL",
        None,
        [
            ("HANDLE", "hFile", None),
            ("LPCVOID", "lpBuffer", None),
            ("DWORD", "nNumberOfBytesToWrite", None),
            ("LPOVERLAPPED", "lpOverlapped", None),
            ("LPOVERLAPPED_COMPLETION_ROUTINE", "lpCompletionRoutine", None),
        ],
    ),
    ("FlushFileBuffers", "BOOL", None, [("HANDLE", "hFile", None)]),
    ("CloseHandle", "BOOL", None, [("HANDLE", "hObject", None)]),
    ("LocalFree", "HLOCAL", None, [("HLOCAL", "hMem", None)]),
    (
        "LocalAlloc",
        "HLOCAL",
        None,
        [("UINT", "uFlags", "local_alloc"), ("SIZE_T", "uBytes", None)],
    ),
    ("lstrlenW", "int", None, [("LPCWSTR", "lpString", None)]),
    ("lstrlenA", "int", None, [("LPCSTR", "lpString", None)]),
    (
        "GetTokenInformation",
        "BOOL",
        None,
        [
            ("HANDLE", "TokenHandle", None),
            ("TOKEN_INFORMATION_CLASS", "TokenInformationClass", "token_information_class"),
            ("LPVOID", "TokenInformation", None),
            ("DWORD", "TokenInformationLength", None),
            ("PDWORD", "ReturnLength", None),
        ],
    ),
    (
        "LookupAccountSidW",
        "BOOL",
        None,
        [
            ("LPCWSTR", "lpSystemName", None),
            ("PSID", "Sid", None),
            ("LPWSTR", "Name", None),
            ("LPDWORD", "cchName", None),
            ("LPWSTR", "ReferencedDomainName", None),
            ("LPDWORD", "cchReferencedDomainName", None),
            ("PSID_NAME_USE", "peUse", None),
        ],
    ),
    (
        "ConvertSidToStringSidW",
        "BOOL",
        None,
        [("PSID", "Sid", None), ("LPWSTR *", "StringSid", None)],
    ),
    (
        "LookupPrivilegeValueW",
        "BOOL",
        None,
        [("LPCWSTR", "lpSystemName", None), ("LPCWSTR", "lpName", None), ("PLUID", "lpLuid", None)],
    ),
    (
        "AdjustTokenPrivileges",
        "BOOL",
        None,
        [
            ("HANDLE", "TokenHandle", None),
            ("BOOL", "DisableAllPrivileges", "bool"),
            ("PTOKEN_PRIVILEGES", "NewState", None),
            ("DWORD", "BufferLength", None),
            ("PTOKEN_PRIVILEGES", "PreviousState", None),
            ("PDWORD", "ReturnLength", None),
        ],
    ),
    (
        "GetSidSubAuthority",
        "PDWORD",
        None,
        [("PSID", "pSid", None), ("DWORD", "nSubAuthority", None)],
    ),
    ("GetSidSubAuthorityCount", "PUCHAR", None, [("PSID", "pSid", None)]),
    ("GetLengthSid", "DWORD", None, [("PSID", "pSid", None)]),
    ("IsValidSid", "BOOL", None, [("PSID", "pSid", None)]),
    ("EqualSid", "BOOL", None, [("PSID", "pSid1", None), ("PSID", "pSid2", None)]),
    (
        "CopySid",
        "BOOL",
        None,
        [
            ("DWORD", "nDestinationSidLength", None),
            ("PSID", "pDestinationSid", None),
            ("PSID", "pSourceSid", None),
        ],
    ),
    (
        "WideCharToMultiByte",
        "int",
        None,
        [
            ("UINT", "CodePage", "code_page"),
            ("DWORD", "dwFlags", None),
            ("LPCWSTR", "lpWideCharStr", None),
            ("int", "cchWideChar", None),
            ("LPSTR", "lpMultiByteStr", None),
            ("int", "cbMultiByte", None),
            ("LPCSTR", "lpDefaultChar", None),
            ("LPBOOL", "lpUsedDefaultChar", None),
        ],
    ),
    (
        "MultiByteToWideChar",
        "int",
        None,
        [
            ("UINT", "CodePage", "code_page"),
            ("DWORD", "dwFlags", None),
            ("LPCSTR", "lpMultiByteStr", None),
            ("int", "cbMultiByte", None),
            ("LPWSTR", "lpWideCharStr", None),
            ("int", "cchWideChar", None),
        ],
    ),
    (
        "FormatMessageW",
        "DWORD",
        None,
        [
            ("DWORD", "dwFlags", "format_message"),
            ("LPCVOID", "lpSource", None),
            ("DWORD", "dwMessageId", None),
            ("DWORD", "dwLanguageId", None),
            ("LPWSTR", "lpBuffer", None),
            ("DWORD", "nSize", None),
            ("void *", "Arguments", None),
        ],
    ),
    (
        "GetUserNameExW",
        "BOOLEAN",
        None,
        [
            ("EXTENDED_NAME_FORMAT", "NameFormat", "extended_name_format"),
            ("LPWSTR", "lpNameBuffer", None),
            ("PULONG", "nSize", None),
        ],
    ),
    ("GetFileType", "DWORD", "file_type", [("HANDLE", "hFile", None)]),
    (
        "GetConsoleMode",
        "BOOL",
        None,
        [("HANDLE", "hConsoleHandle", None), ("LPDWORD", "lpMode", None)],
    ),
    ("GetConsoleOutputCP", "UINT", None, []),
    (
        "SetConsoleTextAttribute",
        "BOOL",
        None,
        [("HANDLE", "hConsoleOutput", None), ("WORD", "wAttributes", None)],
    ),
    (
        "WriteConsoleW",
        "BOOL",
        None,
        [
            ("HANDLE", "hConsoleOutput", None),
            ("LPCVOID", "lpBuffer", None),
            ("DWORD", "nNumberOfCharsToWrite", None),
            ("LPDWORD", "lpNumberOfCharsWritten", None),
            ("LPVOID", "lpReserved", None),
        ],
    ),
    ("IsDBCSLeadByte", "BOOL", None, [("BYTE", "TestChar", None)]),
    ("AcquireSRWLockExclusive", "void", None, [("PSRWLOCK", "SRWLock", None)]),
    ("ReleaseSRWLockExclusive", "void", None, [("PSRWLOCK", "SRWLock", None)]),
    ("AcquireSRWLockShared", "void", None, [("PSRWLOCK", "SRWLock", None)]),
    ("ReleaseSRWLockShared", "void", None, [("PSRWLOCK", "SRWLock", None)]),
    (
        "WakeAllConditionVariable",
        "void",
        None,
        [("PCONDITION_VARIABLE", "ConditionVariable", None)],
    ),
    (
        "SetUnhandledExceptionFilter",
        "LPTOP_LEVEL_EXCEPTION_FILTER",
        None,
        [("LPTOP_LEVEL_EXCEPTION_FILTER", "lpTopLevelExceptionFilter", None)],
    ),
    ("UnhandledExceptionFilter", "LONG", None, [("PEXCEPTION_POINTERS", "ExceptionInfo", None)]),
    ("RtlCaptureContext", "void", None, [("PCONTEXT", "ContextRecord", None)]),
    ("QueryPerformanceCounter", "BOOL", None, [("PLARGE_INTEGER", "lpPerformanceCount", None)]),
    ("GetSystemTimeAsFileTime", "void", None, [("LPFILETIME", "lpSystemTimeAsFileTime", None)]),
    ("GetSystemInfo", "void", None, [("LPSYSTEM_INFO", "lpSystemInfo", None)]),
    (
        "FileTimeToSystemTime",
        "BOOL",
        None,
        [("LPFILETIME", "lpFileTime", None), ("LPSYSTEMTIME", "lpSystemTime", None)],
    ),
    (
        "HeapSize",
        "SIZE_T",
        None,
        [("HANDLE", "hHeap", None), ("DWORD", "dwFlags", None), ("LPCVOID", "lpMem", None)],
    ),
    (
        "HeapReAlloc",
        "LPVOID",
        None,
        [
            ("HANDLE", "hHeap", None),
            ("DWORD", "dwFlags", None),
            ("LPVOID", "lpMem", None),
            ("SIZE_T", "dwBytes", None),
        ],
    ),
    ("GetThreadLocale", "LCID", None, []),
    ("SetThreadUILanguage", "LANGID", None, [("LANGID", "LangId", None)]),
    ("NetApiBufferFree", "NET_API_STATUS", None, [("LPVOID", "Buffer", None)]),
    ("CertFreeCertificateContext", "BOOL", None, [("PCCERT_CONTEXT", "pCertContext", None)]),
    (
        "CryptReleaseContext",
        "BOOL",
        None,
        [("HCRYPTPROV", "hProv", None), ("DWORD", "dwFlags", None)],
    ),
    (
        "RegOpenKeyW",
        "LSTATUS",
        None,
        [("HKEY", "hKey", "hkey"), ("LPCWSTR", "lpSubKey", None), ("PHKEY", "phkResult", None)],
    ),
    (
        "FindFirstFileA",
        "HANDLE",
        "handle",
        [("LPCSTR", "lpFileName", None), ("LPWIN32_FIND_DATAA", "lpFindFileData", None)],
    ),
    (
        "FindNextFileA",
        "BOOL",
        None,
        [("HANDLE", "hFindFile", None), ("LPWIN32_FIND_DATAA", "lpFindFileData", None)],
    ),
    ("GetFileAttributesA", "DWORD", None, [("LPCSTR", "lpFileName", None)]),
    (
        "GetCurrentDirectoryA",
        "DWORD",
        None,
        [("DWORD", "nBufferLength", None), ("LPSTR", "lpBuffer", None)],
    ),
    ("SetCurrentDirectoryA", "BOOL", None, [("LPCSTR", "lpPathName", None)]),
    ("CharLowerW", "LPWSTR", None, [("LPWSTR", "lpsz", None)]),
    ("CharUpperW", "LPWSTR", None, [("LPWSTR", "lpsz", None)]),
    ("DeleteFileW", "BOOL", None, [("LPCWSTR", "lpFileName", None)]),
    ("DeleteFileA", "BOOL", None, [("LPCSTR", "lpFileName", None)]),
    (
        "CopyFileW",
        "BOOL",
        None,
        [
            ("LPCWSTR", "lpExistingFileName", None),
            ("LPCWSTR", "lpNewFileName", None),
            ("BOOL", "bFailIfExists", "bool"),
        ],
    ),
    (
        "MoveFileExW",
        "BOOL",
        None,
        [
            ("LPCWSTR", "lpExistingFileName", None),
            ("LPCWSTR", "lpNewFileName", None),
            ("DWORD", "dwFlags", "move_file"),
        ],
    ),
    (
        "SetFilePointer",
        "DWORD",
        None,
        [
            ("HANDLE", "hFile", None),
            ("LONG", "lDistanceToMove", None),
            ("PLONG", "lpDistanceToMoveHigh", None),
            ("DWORD", "dwMoveMethod", "move_method"),
        ],
    ),
    (
        "SetFilePointerEx",
        "BOOL",
        None,
        [
            ("HANDLE", "hFile", None),
            ("LARGE_INTEGER", "liDistanceToMove", None),
            ("PLARGE_INTEGER", "lpNewFilePointer", None),
            ("DWORD", "dwMoveMethod", "move_method"),
        ],
    ),
    (
        "GetFileSize",
        "DWORD",
        None,
        [("HANDLE", "hFile", None), ("LPDWORD", "lpFileSizeHigh", None)],
    ),
    ("GetFileAttributesW", "DWORD", None, [("LPCWSTR", "lpFileName", None)]),
    (
        "SetFileAttributesW",
        "BOOL",
        None,
        [("LPCWSTR", "lpFileName", None), ("DWORD", "dwFileAttributes", "file_flags")],
    ),
    (
        "CreateDirectoryW",
        "BOOL",
        None,
        [("LPCWSTR", "lpPathName", None), ("LPSECURITY_ATTRIBUTES", "lpSecurityAttributes", None)],
    ),
    (
        "FindFirstFileW",
        "HANDLE",
        "handle",
        [("LPCWSTR", "lpFileName", None), ("LPWIN32_FIND_DATAW", "lpFindFileData", None)],
    ),
    (
        "FindNextFileW",
        "BOOL",
        None,
        [("HANDLE", "hFindFile", None), ("LPWIN32_FIND_DATAW", "lpFindFileData", None)],
    ),
    ("FindClose", "BOOL", None, [("HANDLE", "hFindFile", None)]),
    (
        "CreateFileMappingW",
        "HANDLE",
        None,
        [
            ("HANDLE", "hFile", None),
            ("LPSECURITY_ATTRIBUTES", "lpFileMappingAttributes", None),
            ("DWORD", "flProtect", "page_protect"),
            ("DWORD", "dwMaximumSizeHigh", None),
            ("DWORD", "dwMaximumSizeLow", None),
            ("LPCWSTR", "lpName", None),
        ],
    ),
    (
        "MapViewOfFile",
        "LPVOID",
        None,
        [
            ("HANDLE", "hFileMappingObject", None),
            ("DWORD", "dwDesiredAccess", "file_map"),
            ("DWORD", "dwFileOffsetHigh", None),
            ("DWORD", "dwFileOffsetLow", None),
            ("SIZE_T", "dwNumberOfBytesToMap", None),
        ],
    ),
    ("UnmapViewOfFile", "BOOL", None, [("LPCVOID", "lpBaseAddress", None)]),
    (
        "VirtualAlloc",
        "LPVOID",
        None,
        [
            ("LPVOID", "lpAddress", None),
            ("SIZE_T", "dwSize", None),
            ("DWORD", "flAllocationType", "mem_type"),
            ("DWORD", "flProtect", "page_protect"),
        ],
    ),
    (
        "VirtualAllocEx",
        "LPVOID",
        None,
        [
            ("HANDLE", "hProcess", None),
            ("LPVOID", "lpAddress", None),
            ("SIZE_T", "dwSize", None),
            ("DWORD", "flAllocationType", "mem_type"),
            ("DWORD", "flProtect", "page_protect"),
        ],
    ),
    (
        "VirtualFree",
        "BOOL",
        None,
        [
            ("LPVOID", "lpAddress", None),
            ("SIZE_T", "dwSize", None),
            ("DWORD", "dwFreeType", "mem_type"),
        ],
    ),
    (
        "VirtualProtect",
        "BOOL",
        None,
        [
            ("LPVOID", "lpAddress", None),
            ("SIZE_T", "dwSize", None),
            ("DWORD", "flNewProtect", "page_protect"),
            ("PDWORD", "lpflOldProtect", None),
        ],
    ),
    (
        "VirtualProtectEx",
        "BOOL",
        None,
        [
            ("HANDLE", "hProcess", None),
            ("LPVOID", "lpAddress", None),
            ("SIZE_T", "dwSize", None),
            ("DWORD", "flNewProtect", "page_protect"),
            ("PDWORD", "lpflOldProtect", None),
        ],
    ),
    (
        "VirtualQuery",
        "SIZE_T",
        None,
        [
            ("LPCVOID", "lpAddress", None),
            ("PMEMORY_BASIC_INFORMATION", "lpBuffer", None),
            ("SIZE_T", "dwLength", None),
        ],
    ),
    ("GetProcessHeap", "HANDLE", None, []),
    (
        "HeapAlloc",
        "LPVOID",
        None,
        [
            ("HANDLE", "hHeap", None),
            ("DWORD", "dwFlags", "heap_flags"),
            ("SIZE_T", "dwBytes", None),
        ],
    ),
    (
        "HeapFree",
        "BOOL",
        None,
        [("HANDLE", "hHeap", None), ("DWORD", "dwFlags", "heap_flags"), ("LPVOID", "lpMem", None)],
    ),
    (
        "WriteProcessMemory",
        "BOOL",
        None,
        [
            ("HANDLE", "hProcess", None),
            ("LPVOID", "lpBaseAddress", None),
            ("LPCVOID", "lpBuffer", None),
            ("SIZE_T", "nSize", None),
            ("SIZE_T *", "lpNumberOfBytesWritten", None),
        ],
    ),
    (
        "ReadProcessMemory",
        "BOOL",
        None,
        [
            ("HANDLE", "hProcess", None),
            ("LPCVOID", "lpBaseAddress", None),
            ("LPVOID", "lpBuffer", None),
            ("SIZE_T", "nSize", None),
            ("SIZE_T *", "lpNumberOfBytesRead", None),
        ],
    ),
    (
        "OpenProcess",
        "HANDLE",
        None,
        [
            ("DWORD", "dwDesiredAccess", "process_access"),
            ("BOOL", "bInheritHandle", "bool"),
            ("DWORD", "dwProcessId", None),
        ],
    ),
    (
        "OpenThread",
        "HANDLE",
        None,
        [
            ("DWORD", "dwDesiredAccess", "thread_access"),
            ("BOOL", "bInheritHandle", "bool"),
            ("DWORD", "dwThreadId", None),
        ],
    ),
    (
        "OpenProcessToken",
        "BOOL",
        None,
        [
            ("HANDLE", "ProcessHandle", None),
            ("DWORD", "DesiredAccess", "token_access"),
            ("PHANDLE", "TokenHandle", None),
        ],
    ),
    (
        "TerminateProcess",
        "BOOL",
        None,
        [("HANDLE", "hProcess", None), ("UINT", "uExitCode", None)],
    ),
    (
        "TerminateThread",
        "BOOL",
        None,
        [("HANDLE", "hThread", None), ("DWORD", "dwExitCode", None)],
    ),
    ("GetCurrentProcess", "HANDLE", None, []),
    ("GetCurrentProcessId", "DWORD", None, []),
    (
        "GetExitCodeProcess",
        "BOOL",
        None,
        [("HANDLE", "hProcess", None), ("LPDWORD", "lpExitCode", None)],
    ),
    ("GetCurrentThreadId", "DWORD", None, []),
    (
        "CreateProcessW",
        "BOOL",
        None,
        [
            ("LPCWSTR", "lpApplicationName", None),
            ("LPWSTR", "lpCommandLine", None),
            ("LPSECURITY_ATTRIBUTES", "lpProcessAttributes", None),
            ("LPSECURITY_ATTRIBUTES", "lpThreadAttributes", None),
            ("BOOL", "bInheritHandles", "bool"),
            ("DWORD", "dwCreationFlags", "process_creation"),
            ("LPVOID", "lpEnvironment", None),
            ("LPCWSTR", "lpCurrentDirectory", None),
            ("LPSTARTUPINFOW", "lpStartupInfo", None),
            ("LPPROCESS_INFORMATION", "lpProcessInformation", None),
        ],
    ),
    (
        "CreateProcessA",
        "BOOL",
        None,
        [
            ("LPCSTR", "lpApplicationName", None),
            ("LPSTR", "lpCommandLine", None),
            ("LPSECURITY_ATTRIBUTES", "lpProcessAttributes", None),
            ("LPSECURITY_ATTRIBUTES", "lpThreadAttributes", None),
            ("BOOL", "bInheritHandles", "bool"),
            ("DWORD", "dwCreationFlags", "process_creation"),
            ("LPVOID", "lpEnvironment", None),
            ("LPCSTR", "lpCurrentDirectory", None),
            ("LPSTARTUPINFOA", "lpStartupInfo", None),
            ("LPPROCESS_INFORMATION", "lpProcessInformation", None),
        ],
    ),
    (
        "CreateProcessAsUserW",
        "BOOL",
        None,
        [
            ("HANDLE", "hToken", None),
            ("LPCWSTR", "lpApplicationName", None),
            ("LPWSTR", "lpCommandLine", None),
            ("LPSECURITY_ATTRIBUTES", "lpProcessAttributes", None),
            ("LPSECURITY_ATTRIBUTES", "lpThreadAttributes", None),
            ("BOOL", "bInheritHandles", "bool"),
            ("DWORD", "dwCreationFlags", "process_creation"),
            ("LPVOID", "lpEnvironment", None),
            ("LPCWSTR", "lpCurrentDirectory", None),
            ("LPSTARTUPINFOW", "lpStartupInfo", None),
            ("LPPROCESS_INFORMATION", "lpProcessInformation", None),
        ],
    ),
    ("WinExec", "UINT", None, [("LPCSTR", "lpCmdLine", None), ("UINT", "uCmdShow", "show_window")]),
    (
        "CreateThread",
        "HANDLE",
        None,
        [
            ("LPSECURITY_ATTRIBUTES", "lpThreadAttributes", None),
            ("SIZE_T", "dwStackSize", None),
            ("LPTHREAD_START_ROUTINE", "lpStartAddress", None),
            ("LPVOID", "lpParameter", None),
            ("DWORD", "dwCreationFlags", "thread_creation"),
            ("LPDWORD", "lpThreadId", None),
        ],
    ),
    (
        "CreateRemoteThread",
        "HANDLE",
        None,
        [
            ("HANDLE", "hProcess", None),
            ("LPSECURITY_ATTRIBUTES", "lpThreadAttributes", None),
            ("SIZE_T", "dwStackSize", None),
            ("LPTHREAD_START_ROUTINE", "lpStartAddress", None),
            ("LPVOID", "lpParameter", None),
            ("DWORD", "dwCreationFlags", "thread_creation"),
            ("LPDWORD", "lpThreadId", None),
        ],
    ),
    ("ResumeThread", "DWORD", None, [("HANDLE", "hThread", None)]),
    ("SuspendThread", "DWORD", None, [("HANDLE", "hThread", None)]),
    (
        "WaitForSingleObject",
        "DWORD",
        "wait_result",
        [("HANDLE", "hHandle", None), ("DWORD", "dwMilliseconds", "timeout")],
    ),
    ("Sleep", "void", None, [("DWORD", "dwMilliseconds", "timeout")]),
    ("ExitProcess", "void", None, [("UINT", "uExitCode", None)]),
    ("ExitThread", "void", None, [("DWORD", "dwExitCode", None)]),
    ("SetLastError", "void", None, [("DWORD", "dwErrCode", None)]),
    ("GetLastError", "DWORD", None, []),
    ("GetTickCount", "DWORD", None, []),
    ("GetTickCount64", "ULONGLONG", None, []),
    ("IsDebuggerPresent", "BOOL", None, []),
    (
        "IsWow64Process",
        "BOOL",
        None,
        [("HANDLE", "hProcess", None), ("PBOOL", "Wow64Process", None)],
    ),
    (
        "CheckRemoteDebuggerPresent",
        "BOOL",
        None,
        [("HANDLE", "hProcess", None), ("PBOOL", "pbDebuggerPresent", None)],
    ),
    ("OutputDebugStringW", "void", None, [("LPCWSTR", "lpOutputString", None)]),
    ("OutputDebugStringA", "void", None, [("LPCSTR", "lpOutputString", None)]),
    (
        "InitializeCriticalSection",
        "void",
        None,
        [("LPCRITICAL_SECTION", "lpCriticalSection", None)],
    ),
    ("EnterCriticalSection", "void", None, [("LPCRITICAL_SECTION", "lpCriticalSection", None)]),
    ("LeaveCriticalSection", "void", None, [("LPCRITICAL_SECTION", "lpCriticalSection", None)]),
    ("DeleteCriticalSection", "void", None, [("LPCRITICAL_SECTION", "lpCriticalSection", None)]),
    (
        "DuplicateHandle",
        "BOOL",
        None,
        [
            ("HANDLE", "hSourceProcessHandle", None),
            ("HANDLE", "hSourceHandle", None),
            ("HANDLE", "hTargetProcessHandle", None),
            ("LPHANDLE", "lpTargetHandle", None),
            ("DWORD", "dwDesiredAccess", None),
            ("BOOL", "bInheritHandle", "bool"),
            ("DWORD", "dwOptions", "duplicate"),
        ],
    ),
    (
        "CreateMutexW",
        "HANDLE",
        None,
        [
            ("LPSECURITY_ATTRIBUTES", "lpMutexAttributes", None),
            ("BOOL", "bInitialOwner", "bool"),
            ("LPCWSTR", "lpName", None),
        ],
    ),
    (
        "CreateEventW",
        "HANDLE",
        None,
        [
            ("LPSECURITY_ATTRIBUTES", "lpEventAttributes", None),
            ("BOOL", "bManualReset", "bool"),
            ("BOOL", "bInitialState", "bool"),
            ("LPCWSTR", "lpName", None),
        ],
    ),
    ("GetStdHandle", "HANDLE", "handle", [("DWORD", "nStdHandle", "std_handle")]),
    ("LoadLibraryW", "HMODULE", None, [("LPCWSTR", "lpLibFileName", None)]),
    ("LoadLibraryA", "HMODULE", None, [("LPCSTR", "lpLibFileName", None)]),
    (
        "LoadLibraryExW",
        "HMODULE",
        None,
        [
            ("LPCWSTR", "lpLibFileName", None),
            ("HANDLE", "hFile", None),
            ("DWORD", "dwFlags", "load_library"),
        ],
    ),
    ("GetModuleHandleW", "HMODULE", None, [("LPCWSTR", "lpModuleName", None)]),
    ("GetModuleHandleA", "HMODULE", None, [("LPCSTR", "lpModuleName", None)]),
    (
        "GetModuleFileNameW",
        "DWORD",
        None,
        [("HMODULE", "hModule", None), ("LPWSTR", "lpFilename", None), ("DWORD", "nSize", None)],
    ),
    (
        "GetModuleFileNameA",
        "DWORD",
        None,
        [("HMODULE", "hModule", None), ("LPSTR", "lpFilename", None), ("DWORD", "nSize", None)],
    ),
    (
        "GetProcAddress",
        "FARPROC",
        None,
        [("HMODULE", "hModule", None), ("LPCSTR", "lpProcName", None)],
    ),
    ("FreeLibrary", "BOOL", None, [("HMODULE", "hLibModule", None)]),
    (
        "FindResourceW",
        "HRSRC",
        None,
        [("HMODULE", "hModule", None), ("LPCWSTR", "lpName", None), ("LPCWSTR", "lpType", None)],
    ),
    ("LoadResource", "HGLOBAL", None, [("HMODULE", "hModule", None), ("HRSRC", "hResInfo", None)]),
    ("LockResource", "LPVOID", None, [("HGLOBAL", "hResData", None)]),
    ("SizeofResource", "DWORD", None, [("HMODULE", "hModule", None), ("HRSRC", "hResInfo", None)]),
    (
        "CreateToolhelp32Snapshot",
        "HANDLE",
        "handle",
        [("DWORD", "dwFlags", "snapshot"), ("DWORD", "th32ProcessID", None)],
    ),
    (
        "Process32FirstW",
        "BOOL",
        None,
        [("HANDLE", "hSnapshot", None), ("LPPROCESSENTRY32W", "lppe", None)],
    ),
    (
        "Process32NextW",
        "BOOL",
        None,
        [("HANDLE", "hSnapshot", None), ("LPPROCESSENTRY32W", "lppe", None)],
    ),
    (
        "Module32FirstW",
        "BOOL",
        None,
        [("HANDLE", "hSnapshot", None), ("LPMODULEENTRY32W", "lpme", None)],
    ),
    (
        "Module32NextW",
        "BOOL",
        None,
        [("HANDLE", "hSnapshot", None), ("LPMODULEENTRY32W", "lpme", None)],
    ),
    (
        "Thread32First",
        "BOOL",
        None,
        [("HANDLE", "hSnapshot", None), ("LPTHREADENTRY32", "lpte", None)],
    ),
    (
        "Thread32Next",
        "BOOL",
        None,
        [("HANDLE", "hSnapshot", None), ("LPTHREADENTRY32", "lpte", None)],
    ),
    (
        "RegOpenKeyExW",
        "LSTATUS",
        None,
        [
            ("HKEY", "hKey", "hkey"),
            ("LPCWSTR", "lpSubKey", None),
            ("DWORD", "ulOptions", "reg_options"),
            ("REGSAM", "samDesired", "reg_sam"),
            ("PHKEY", "phkResult", None),
        ],
    ),
    (
        "RegOpenKeyExA",
        "LSTATUS",
        None,
        [
            ("HKEY", "hKey", "hkey"),
            ("LPCSTR", "lpSubKey", None),
            ("DWORD", "ulOptions", "reg_options"),
            ("REGSAM", "samDesired", "reg_sam"),
            ("PHKEY", "phkResult", None),
        ],
    ),
    (
        "RegCreateKeyExW",
        "LSTATUS",
        None,
        [
            ("HKEY", "hKey", "hkey"),
            ("LPCWSTR", "lpSubKey", None),
            ("DWORD", "Reserved", None),
            ("LPWSTR", "lpClass", None),
            ("DWORD", "dwOptions", "reg_options"),
            ("REGSAM", "samDesired", "reg_sam"),
            ("LPSECURITY_ATTRIBUTES", "lpSecurityAttributes", None),
            ("PHKEY", "phkResult", None),
            ("LPDWORD", "lpdwDisposition", None),
        ],
    ),
    (
        "RegSetValueExW",
        "LSTATUS",
        None,
        [
            ("HKEY", "hKey", "hkey"),
            ("LPCWSTR", "lpValueName", None),
            ("DWORD", "Reserved", None),
            ("DWORD", "dwType", "reg_type"),
            ("const BYTE *", "lpData", None),
            ("DWORD", "cbData", None),
        ],
    ),
    (
        "RegSetValueExA",
        "LSTATUS",
        None,
        [
            ("HKEY", "hKey", "hkey"),
            ("LPCSTR", "lpValueName", None),
            ("DWORD", "Reserved", None),
            ("DWORD", "dwType", "reg_type"),
            ("const BYTE *", "lpData", None),
            ("DWORD", "cbData", None),
        ],
    ),
    (
        "RegQueryValueExW",
        "LSTATUS",
        None,
        [
            ("HKEY", "hKey", "hkey"),
            ("LPCWSTR", "lpValueName", None),
            ("LPDWORD", "lpReserved", None),
            ("LPDWORD", "lpType", None),
            ("LPBYTE", "lpData", None),
            ("LPDWORD", "lpcbData", None),
        ],
    ),
    (
        "RegQueryValueExA",
        "LSTATUS",
        None,
        [
            ("HKEY", "hKey", "hkey"),
            ("LPCSTR", "lpValueName", None),
            ("LPDWORD", "lpReserved", None),
            ("LPDWORD", "lpType", None),
            ("LPBYTE", "lpData", None),
            ("LPDWORD", "lpcbData", None),
        ],
    ),
    (
        "RegEnumValueW",
        "LSTATUS",
        None,
        [
            ("HKEY", "hKey", "hkey"),
            ("DWORD", "dwIndex", None),
            ("LPWSTR", "lpValueName", None),
            ("LPDWORD", "lpcchValueName", None),
            ("LPDWORD", "lpReserved", None),
            ("LPDWORD", "lpType", None),
            ("LPBYTE", "lpData", None),
            ("LPDWORD", "lpcbData", None),
        ],
    ),
    (
        "RegDeleteValueW",
        "LSTATUS",
        None,
        [("HKEY", "hKey", "hkey"), ("LPCWSTR", "lpValueName", None)],
    ),
    ("RegCloseKey", "LSTATUS", None, [("HKEY", "hKey", "hkey")]),
    (
        "GetFileVersionInfoW",
        "BOOL",
        None,
        [
            ("LPCWSTR", "lptstrFilename", None),
            ("DWORD", "dwHandle", None),
            ("DWORD", "dwLen", None),
            ("LPVOID", "lpData", None),
        ],
    ),
    (
        "VerQueryValueW",
        "BOOL",
        None,
        [
            ("LPCVOID", "pBlock", None),
            ("LPCWSTR", "lpSubBlock", None),
            ("LPVOID *", "lplpBuffer", None),
            ("PUINT", "puLen", None),
        ],
    ),
    (
        "MessageBoxW",
        "int",
        "dialog_result",
        [
            ("HWND", "hWnd", None),
            ("LPCWSTR", "lpText", None),
            ("LPCWSTR", "lpCaption", None),
            ("UINT", "uType", "message_box"),
        ],
    ),
    (
        "MessageBoxA",
        "int",
        "dialog_result",
        [
            ("HWND", "hWnd", None),
            ("LPCSTR", "lpText", None),
            ("LPCSTR", "lpCaption", None),
            ("UINT", "uType", "message_box"),
        ],
    ),
    ("ShowWindow", "BOOL", None, [("HWND", "hWnd", None), ("int", "nCmdShow", "show_window")]),
    (
        "SetWindowsHookExW",
        "HHOOK",
        None,
        [
            ("int", "idHook", "hook"),
            ("HOOKPROC", "lpfn", None),
            ("HINSTANCE", "hmod", None),
            ("DWORD", "dwThreadId", None),
        ],
    ),
    ("GetAsyncKeyState", "SHORT", None, [("int", "vKey", None)]),
    (
        "CoCreateInstance",
        "HRESULT",
        None,
        [
            ("REFCLSID", "rclsid", None),
            ("LPUNKNOWN", "pUnkOuter", None),
            ("DWORD", "dwClsContext", "clsctx"),
            ("REFIID", "riid", None),
            ("LPVOID *", "ppv", None),
        ],
    ),
    (
        "SHGetFolderPathW",
        "HRESULT",
        None,
        [
            ("HWND", "hwnd", None),
            ("int", "csidl", "csidl"),
            ("HANDLE", "hToken", None),
            ("DWORD", "dwFlags", None),
            ("LPWSTR", "pszPath", None),
        ],
    ),
    (
        "InternetOpenW",
        "HINTERNET",
        None,
        [
            ("LPCWSTR", "lpszAgent", None),
            ("DWORD", "dwAccessType", "internet_open"),
            ("LPCWSTR", "lpszProxy", None),
            ("LPCWSTR", "lpszProxyBypass", None),
            ("DWORD", "dwFlags", "internet_flags"),
        ],
    ),
    (
        "InternetOpenUrlW",
        "HINTERNET",
        None,
        [
            ("HINTERNET", "hInternet", None),
            ("LPCWSTR", "lpszUrl", None),
            ("LPCWSTR", "lpszHeaders", None),
            ("DWORD", "dwHeadersLength", None),
            ("DWORD", "dwFlags", "internet_flags"),
            ("DWORD_PTR", "dwContext", None),
        ],
    ),
    (
        "InternetReadFile",
        "BOOL",
        None,
        [
            ("HINTERNET", "hFile", None),
            ("LPVOID", "lpBuffer", None),
            ("DWORD", "dwNumberOfBytesToRead", None),
            ("LPDWORD", "lpdwNumberOfBytesRead", None),
        ],
    ),
    ("InternetCloseHandle", "BOOL", None, [("HINTERNET", "hInternet", None)]),
    (
        "socket",
        "SOCKET",
        None,
        [("int", "af", "af_win"), ("int", "type", "sock_type_win"), ("int", "protocol", "ipproto")],
    ),
    ("closesocket", "int", None, [("SOCKET", "s", None)]),
    (
        "WSAStartup",
        "int",
        None,
        [("WORD", "wVersionRequested", None), ("LPWSADATA", "lpWSAData", None)],
    ),
    (
        "connect",
        "int",
        None,
        [
            ("SOCKET", "s", None),
            ("const struct sockaddr *", "name", None),
            ("int", "namelen", None),
        ],
    ),
    (
        "send",
        "int",
        None,
        [
            ("SOCKET", "s", None),
            ("const char *", "buf", None),
            ("int", "len", None),
            ("int", "flags", "msg_flags_win"),
        ],
    ),
    (
        "recv",
        "int",
        None,
        [
            ("SOCKET", "s", None),
            ("char *", "buf", None),
            ("int", "len", None),
            ("int", "flags", "msg_flags_win"),
        ],
    ),
    # winsock helpers the socket code around `socket`/`send` reads.
    ("htons", "u_short", None, [("u_short", "hostshort", None)]),
    ("ntohs", "u_short", None, [("u_short", "netshort", None)]),
    ("htonl", "unsigned long", None, [("unsigned long", "hostlong", None)]),
    ("ntohl", "unsigned long", None, [("unsigned long", "netlong", None)]),
    ("inet_addr", "in_addr_t", None, [("PCSTR", "cp", None)]),
    ("inet_ntoa", "LPSTR", None, [("in_addr", "in", None)]),
    ("WSACleanup", "int", None, []),
    ("WSAGetLastError", "int", None, []),
    # ntdll: the native API malware and loaders call around processes and
    # memory, each typed as the WDK reference states it.
    ("NtClose", "NTSTATUS", None, [("HANDLE", "Handle", None)]),
    (
        "NtOpenProcess",
        "NTSTATUS",
        None,
        [
            ("PHANDLE", "ProcessHandle", None),
            ("ACCESS_MASK", "DesiredAccess", "process_access"),
            ("POBJECT_ATTRIBUTES", "ObjectAttributes", None),
            ("PCLIENT_ID", "ClientId", None),
        ],
    ),
    (
        "NtAllocateVirtualMemory",
        "NTSTATUS",
        None,
        [
            ("HANDLE", "ProcessHandle", None),
            ("PVOID *", "BaseAddress", None),
            ("ULONG_PTR", "ZeroBits", None),
            ("PSIZE_T", "RegionSize", None),
            ("ULONG", "AllocationType", "mem_type"),
            ("ULONG", "Protect", "page_protect"),
        ],
    ),
    (
        "NtProtectVirtualMemory",
        "NTSTATUS",
        None,
        [
            ("HANDLE", "ProcessHandle", None),
            ("PVOID *", "BaseAddress", None),
            ("PSIZE_T", "RegionSize", None),
            ("ULONG", "NewProtect", "page_protect"),
            ("PULONG", "OldProtect", None),
        ],
    ),
    (
        "NtReadVirtualMemory",
        "NTSTATUS",
        None,
        [
            ("HANDLE", "ProcessHandle", None),
            ("PVOID", "BaseAddress", None),
            ("PVOID", "Buffer", None),
            ("SIZE_T", "NumberOfBytesToRead", None),
            ("PSIZE_T", "NumberOfBytesRead", None),
        ],
    ),
    (
        "NtWriteVirtualMemory",
        "NTSTATUS",
        None,
        [
            ("HANDLE", "ProcessHandle", None),
            ("PVOID", "BaseAddress", None),
            ("PVOID", "Buffer", None),
            ("SIZE_T", "NumberOfBytesToWrite", None),
            ("PSIZE_T", "NumberOfBytesWritten", None),
        ],
    ),
    (
        "NtUnmapViewOfSection",
        "NTSTATUS",
        None,
        [("HANDLE", "ProcessHandle", None), ("PVOID", "BaseAddress", None)],
    ),
    (
        "NtQueryInformationProcess",
        "NTSTATUS",
        None,
        [
            ("HANDLE", "ProcessHandle", None),
            ("PROCESSINFOCLASS", "ProcessInformationClass", "process_info_class"),
            ("PVOID", "ProcessInformation", None),
            ("ULONG", "ProcessInformationLength", None),
            ("PULONG", "ReturnLength", None),
        ],
    ),
    (
        "NtQuerySystemInformation",
        "NTSTATUS",
        None,
        [
            ("SYSTEM_INFORMATION_CLASS", "SystemInformationClass", "system_info_class"),
            ("PVOID", "SystemInformation", None),
            ("ULONG", "SystemInformationLength", None),
            ("PULONG", "ReturnLength", None),
        ],
    ),
    (
        "RtlInitUnicodeString",
        "void",
        None,
        [("PUNICODE_STRING", "DestinationString", None), ("PCWSTR", "SourceString", None)],
    ),
    (
        "LdrLoadDll",
        "NTSTATUS",
        None,
        [
            ("PWSTR", "PathToFile", None),
            ("PULONG", "Flags", None),
            ("PUNICODE_STRING", "ModuleFileName", None),
            ("PHANDLE", "ModuleHandle", None),
        ],
    ),
    # injection and debugging around processes.
    (
        "FlushInstructionCache",
        "BOOL",
        None,
        [
            ("HANDLE", "hProcess", None),
            ("LPCVOID", "lpBaseAddress", None),
            ("SIZE_T", "dwSize", None),
        ],
    ),
    (
        "CreateRemoteThreadEx",
        "HANDLE",
        "handle",
        [
            ("HANDLE", "hProcess", None),
            ("LPSECURITY_ATTRIBUTES", "lpThreadAttributes", None),
            ("SIZE_T", "dwStackSize", None),
            ("LPTHREAD_START_ROUTINE", "lpStartAddress", None),
            ("LPVOID", "lpParameter", None),
            ("DWORD", "dwCreationFlags", "thread_creation"),
            ("LPPROC_THREAD_ATTRIBUTE_LIST", "lpAttributeList", None),
            ("LPDWORD", "lpThreadId", None),
        ],
    ),
    (
        "QueueUserAPC",
        "DWORD",
        None,
        [("PAPCFUNC", "pfnAPC", None), ("HANDLE", "hThread", None), ("ULONG_PTR", "dwData", None)],
    ),
    # window and shell surface the droppers and keyloggers read.
    (
        "ShellExecuteW",
        "HINSTANCE",
        None,
        [
            ("HWND", "hwnd", None),
            ("LPCWSTR", "lpOperation", None),
            ("LPCWSTR", "lpFile", None),
            ("LPCWSTR", "lpParameters", None),
            ("LPCWSTR", "lpDirectory", None),
            ("INT", "nShowCmd", None),
        ],
    ),
    (
        "FindWindowW",
        "HWND",
        "handle",
        [("LPCWSTR", "lpClassName", None), ("LPCWSTR", "lpWindowName", None)],
    ),
    (
        "FindWindowA",
        "HWND",
        "handle",
        [("LPCSTR", "lpClassName", None), ("LPCSTR", "lpWindowName", None)],
    ),
    (
        "keybd_event",
        "void",
        None,
        [
            ("BYTE", "bVk", None),
            ("BYTE", "bScan", None),
            ("DWORD", "dwFlags", None),
            ("ULONG_PTR", "dwExtraInfo", None),
        ],
    ),
    (
        "GetWindowThreadProcessId",
        "DWORD",
        None,
        [("HWND", "hWnd", None), ("LPDWORD", "lpdwProcessId", None)],
    ),
    # Direct3D creation, the entry points game cheats and overlays hook.
    (
        "D3D11CreateDevice",
        "HRESULT",
        None,
        [
            ("IDXGIAdapter *", "pAdapter", None),
            ("D3D_DRIVER_TYPE", "DriverType", "d3d_driver_type"),
            ("HMODULE", "Software", None),
            ("UINT", "Flags", None),
            ("const D3D_FEATURE_LEVEL *", "pFeatureLevels", None),
            ("UINT", "FeatureLevels", None),
            ("UINT", "SDKVersion", None),
            ("ID3D11Device **", "ppDevice", None),
            ("D3D_FEATURE_LEVEL *", "pFeatureLevel", None),
            ("ID3D11DeviceContext **", "ppImmediateContext", None),
        ],
    ),
    (
        "D3D11CreateDeviceAndSwapChain",
        "HRESULT",
        None,
        [
            ("IDXGIAdapter *", "pAdapter", None),
            ("D3D_DRIVER_TYPE", "DriverType", "d3d_driver_type"),
            ("HMODULE", "Software", None),
            ("UINT", "Flags", None),
            ("const D3D_FEATURE_LEVEL *", "pFeatureLevels", None),
            ("UINT", "FeatureLevels", None),
            ("UINT", "SDKVersion", None),
            ("DXGI_SWAP_CHAIN_DESC *", "pSwapChainDesc", None),
            ("IDXGISwapChain **", "ppSwapChain", None),
            ("ID3D11Device **", "ppDevice", None),
            ("D3D_FEATURE_LEVEL *", "pFeatureLevel", None),
            ("ID3D11DeviceContext **", "ppImmediateContext", None),
        ],
    ),
    (
        "CreateDXGIFactory",
        "HRESULT",
        None,
        [("REFIID", "riid", None), ("void **", "ppFactory", None)],
    ),
    (
        "CreateDXGIFactory1",
        "HRESULT",
        None,
        [("REFIID", "riid", None), ("void **", "ppFactory", None)],
    ),
]

C: list[tuple[str, str, str | None, list[Param]]] = [
    ("malloc", "void *", None, [("size_t", "size", None)]),
    ("calloc", "void *", None, [("size_t", "nmemb", None), ("size_t", "size", None)]),
    ("realloc", "void *", None, [("void *", "ptr", None), ("size_t", "size", None)]),
    ("free", "void", None, [("void *", "ptr", None)]),
    (
        "memcpy",
        "void *",
        None,
        [("void *", "dest", None), ("const void *", "src", None), ("size_t", "n", None)],
    ),
    (
        "memmove",
        "void *",
        None,
        [("void *", "dest", None), ("const void *", "src", None), ("size_t", "n", None)],
    ),
    ("memset", "void *", None, [("void *", "s", None), ("int", "c", None), ("size_t", "n", None)]),
    (
        "memcmp",
        "int",
        None,
        [("const void *", "s1", None), ("const void *", "s2", None), ("size_t", "n", None)],
    ),
    ("strlen", "size_t", None, [("const char *", "s", None)]),
    ("strcmp", "int", None, [("const char *", "s1", None), ("const char *", "s2", None)]),
    (
        "strncmp",
        "int",
        None,
        [("const char *", "s1", None), ("const char *", "s2", None), ("size_t", "n", None)],
    ),
    ("strcpy", "char *", None, [("char *", "dest", None), ("const char *", "src", None)]),
    (
        "strncpy",
        "char *",
        None,
        [("char *", "dest", None), ("const char *", "src", None), ("size_t", "n", None)],
    ),
    ("strcat", "char *", None, [("char *", "dest", None), ("const char *", "src", None)]),
    ("strchr", "char *", None, [("const char *", "s", None), ("int", "c", None)]),
    (
        "strstr",
        "char *",
        None,
        [("const char *", "haystack", None), ("const char *", "needle", None)],
    ),
    ("wcslen", "size_t", None, [("const wchar_t *", "s", None)]),
    ("printf", "int", None, [("const char *", "format", None), ("...", "", None)]),
    (
        "fprintf",
        "int",
        None,
        [("FILE *", "stream", None), ("const char *", "format", None), ("...", "", None)],
    ),
    (
        "sprintf",
        "int",
        None,
        [("char *", "str", None), ("const char *", "format", None), ("...", "", None)],
    ),
    (
        "snprintf",
        "int",
        None,
        [
            ("char *", "str", None),
            ("size_t", "size", None),
            ("const char *", "format", None),
            ("...", "", None),
        ],
    ),
    ("puts", "int", None, [("const char *", "s", None)]),
    ("putchar", "int", None, [("int", "c", None)]),
    ("fopen", "FILE *", None, [("const char *", "pathname", None), ("const char *", "mode", None)]),
    ("fclose", "int", None, [("FILE *", "stream", None)]),
    (
        "fread",
        "size_t",
        None,
        [
            ("void *", "ptr", None),
            ("size_t", "size", None),
            ("size_t", "nmemb", None),
            ("FILE *", "stream", None),
        ],
    ),
    (
        "fwrite",
        "size_t",
        None,
        [
            ("const void *", "ptr", None),
            ("size_t", "size", None),
            ("size_t", "nmemb", None),
            ("FILE *", "stream", None),
        ],
    ),
    (
        "fseek",
        "int",
        None,
        [("FILE *", "stream", None), ("long", "offset", None), ("int", "whence", "seek")],
    ),
    ("ftell", "long", None, [("FILE *", "stream", None)]),
    ("getenv", "char *", None, [("const char *", "name", None)]),
    ("system", "int", None, [("const char *", "command", None)]),
    ("atoi", "int", None, [("const char *", "nptr", None)]),
    (
        "strtol",
        "long",
        None,
        [("const char *", "nptr", None), ("char **", "endptr", None), ("int", "base", None)],
    ),
    ("exit", "void", None, [("int", "status", None)]),
    ("abort", "void", None, []),
    ("rand", "int", None, []),
    ("srand", "void", None, [("unsigned int", "seed", None)]),
    ("time", "time_t", None, [("time_t *", "tloc", None)]),
]

POSIX: list[tuple[str, str, str | None, list[Param]]] = [
    (
        "open",
        "int",
        None,
        [("const char *", "pathname", None), ("int", "flags", "open_flags"), ("...", "", None)],
    ),
    (
        "openat",
        "int",
        None,
        [
            ("int", "dirfd", None),
            ("const char *", "pathname", None),
            ("int", "flags", "open_flags"),
            ("...", "", None),
        ],
    ),
    (
        "fstatat",
        "int",
        None,
        [
            ("int", "dirfd", None),
            ("const char *", "pathname", None),
            ("struct stat *", "statbuf", None),
            ("int", "flags", None),
        ],
    ),
    ("close", "int", None, [("int", "fd", None)]),
    ("dup2", "int", None, [("int", "oldfd", None), ("int", "newfd", None)]),
    (
        "dup3",
        "int",
        None,
        [("int", "oldfd", None), ("int", "newfd", None), ("int", "flags", "open_flags")],
    ),
    ("pipe2", "int", None, [("int *", "pipefd", None), ("int", "flags", "open_flags")]),
    (
        "read",
        "ssize_t",
        None,
        [("int", "fd", None), ("void *", "buf", None), ("size_t", "count", None)],
    ),
    (
        "write",
        "ssize_t",
        None,
        [("int", "fd", None), ("const void *", "buf", None), ("size_t", "count", None)],
    ),
    (
        "lseek",
        "off_t",
        None,
        [("int", "fd", None), ("off_t", "offset", None), ("int", "whence", "seek")],
    ),
    (
        "truncate",
        "int",
        None,
        [("const char *", "path", None), ("off_t", "length", None)],
    ),
    ("ftruncate", "int", None, [("int", "fd", None), ("off_t", "length", None)]),
    ("fsync", "int", None, [("int", "fd", None)]),
    ("fdatasync", "int", None, [("int", "fd", None)]),
    ("access", "int", None, [("const char *", "pathname", None), ("int", "mode", "access_mode")]),
    ("stat", "int", None, [("const char *", "pathname", None), ("struct stat *", "statbuf", None)]),
    ("fstat", "int", None, [("int", "fd", None), ("struct stat *", "statbuf", None)]),
    (
        "lstat",
        "int",
        None,
        [("const char *", "pathname", None), ("struct stat *", "statbuf", None)],
    ),
    ("unlink", "int", None, [("const char *", "pathname", None)]),
    ("mkdir", "int", None, [("const char *", "pathname", None), ("mode_t", "mode", None)]),
    ("rmdir", "int", None, [("const char *", "pathname", None)]),
    ("opendir", "DIR *", None, [("const char *", "name", None)]),
    ("readdir", "struct dirent *", None, [("DIR *", "dirp", None)]),
    ("closedir", "int", None, [("DIR *", "dirp", None)]),
    ("chmod", "int", None, [("const char *", "pathname", None), ("mode_t", "mode", None)]),
    (
        "mmap",
        "void *",
        "map_result",
        [
            ("void *", "addr", None),
            ("size_t", "length", None),
            ("int", "prot", "prot"),
            ("int", "flags", "map_flags"),
            ("int", "fd", None),
            ("off_t", "offset", None),
        ],
    ),
    ("munmap", "int", None, [("void *", "addr", None), ("size_t", "length", None)]),
    (
        "mprotect",
        "int",
        None,
        [("void *", "addr", None), ("size_t", "len", None), ("int", "prot", "prot")],
    ),
    (
        "socket",
        "int",
        None,
        [
            ("int", "domain", "af_posix"),
            ("int", "type", "sock_type_posix"),
            ("int", "protocol", "ipproto"),
        ],
    ),
    (
        "connect",
        "int",
        None,
        [
            ("int", "sockfd", None),
            ("const struct sockaddr *", "addr", None),
            ("socklen_t", "addrlen", None),
        ],
    ),
    (
        "bind",
        "int",
        None,
        [
            ("int", "sockfd", None),
            ("const struct sockaddr *", "addr", None),
            ("socklen_t", "addrlen", None),
        ],
    ),
    ("listen", "int", None, [("int", "sockfd", None), ("int", "backlog", None)]),
    (
        "accept",
        "int",
        None,
        [
            ("int", "sockfd", None),
            ("struct sockaddr *", "addr", None),
            ("socklen_t *", "addrlen", None),
        ],
    ),
    (
        "send",
        "ssize_t",
        None,
        [
            ("int", "sockfd", None),
            ("const void *", "buf", None),
            ("size_t", "len", None),
            ("int", "flags", "msg_flags_posix"),
        ],
    ),
    (
        "recv",
        "ssize_t",
        None,
        [
            ("int", "sockfd", None),
            ("void *", "buf", None),
            ("size_t", "len", None),
            ("int", "flags", "msg_flags_posix"),
        ],
    ),
    (
        "sendto",
        "ssize_t",
        None,
        [
            ("int", "sockfd", None),
            ("const void *", "buf", None),
            ("size_t", "len", None),
            ("int", "flags", "msg_flags_posix"),
            ("const struct sockaddr *", "dest_addr", None),
            ("socklen_t", "addrlen", None),
        ],
    ),
    (
        "recvfrom",
        "ssize_t",
        None,
        [
            ("int", "sockfd", None),
            ("void *", "buf", None),
            ("size_t", "len", None),
            ("int", "flags", "msg_flags_posix"),
            ("struct sockaddr *", "src_addr", None),
            ("socklen_t *", "addrlen", None),
        ],
    ),
    (
        "sendmsg",
        "ssize_t",
        None,
        [
            ("int", "sockfd", None),
            ("const struct msghdr *", "msg", None),
            ("int", "flags", "msg_flags_posix"),
        ],
    ),
    (
        "recvmsg",
        "ssize_t",
        None,
        [
            ("int", "sockfd", None),
            ("struct msghdr *", "msg", None),
            ("int", "flags", "msg_flags_posix"),
        ],
    ),
    (
        "shutdown",
        "int",
        None,
        [("int", "sockfd", None), ("int", "how", "shutdown_how")],
    ),
    (
        "getsockname",
        "int",
        None,
        [
            ("int", "sockfd", None),
            ("struct sockaddr *", "addr", None),
            ("socklen_t *", "addrlen", None),
        ],
    ),
    (
        "getpeername",
        "int",
        None,
        [
            ("int", "sockfd", None),
            ("struct sockaddr *", "addr", None),
            ("socklen_t *", "addrlen", None),
        ],
    ),
    (
        "setsockopt",
        "int",
        None,
        [
            ("int", "sockfd", None),
            ("int", "level", None),
            ("int", "optname", None),
            ("const void *", "optval", None),
            ("socklen_t", "optlen", None),
        ],
    ),
    (
        "getsockopt",
        "int",
        None,
        [
            ("int", "sockfd", None),
            ("int", "level", None),
            ("int", "optname", None),
            ("void *", "optval", None),
            ("socklen_t *", "optlen", None),
        ],
    ),
    (
        "getaddrinfo",
        "int",
        None,
        [
            ("const char *", "node", None),
            ("const char *", "service", None),
            ("const struct addrinfo *", "hints", None),
            ("struct addrinfo **", "res", None),
        ],
    ),
    ("freeaddrinfo", "void", None, [("struct addrinfo *", "res", None)]),
    ("gethostbyname", "struct hostent *", None, [("const char *", "name", None)]),
    (
        "poll",
        "int",
        None,
        [("struct pollfd *", "fds", None), ("nfds_t", "nfds", None), ("int", "timeout", None)],
    ),
    (
        "ppoll",
        "int",
        None,
        [
            ("struct pollfd *", "fds", None),
            ("nfds_t", "nfds", None),
            ("const struct timespec *", "tmo_p", None),
            ("const sigset_t *", "sigmask", None),
        ],
    ),
    ("fork", "pid_t", None, []),
    ("getpid", "pid_t", None, []),
    ("getppid", "pid_t", None, []),
    ("getuid", "uid_t", None, []),
    ("getcwd", "char *", None, [("char *", "buf", None), ("size_t", "size", None)]),
    (
        "execve",
        "int",
        None,
        [
            ("const char *", "pathname", None),
            ("char *const *", "argv", None),
            ("char *const *", "envp", None),
        ],
    ),
    (
        "waitpid",
        "pid_t",
        None,
        [("pid_t", "pid", None), ("int *", "wstatus", None), ("int", "options", "wait_options")],
    ),
    ("kill", "int", None, [("pid_t", "pid", None), ("int", "sig", "signal")]),
    (
        "signal",
        "sighandler_t",
        None,
        [("int", "signum", "signal"), ("sighandler_t", "handler", None)],
    ),
    ("raise", "int", None, [("int", "sig", "signal")]),
    (
        "sigaction",
        "int",
        None,
        [
            ("int", "signum", "signal"),
            ("const struct sigaction *", "act", None),
            ("struct sigaction *", "oldact", None),
        ],
    ),
    (
        "sigprocmask",
        "int",
        None,
        [
            ("int", "how", "sigmask"),
            ("const sigset_t *", "set", None),
            ("sigset_t *", "oldset", None),
        ],
    ),
    (
        "sigaltstack",
        "int",
        None,
        [("const stack_t *", "ss", None), ("stack_t *", "old_ss", None)],
    ),
    ("_exit", "void", None, [("int", "status", None)]),
    ("sleep", "unsigned int", None, [("unsigned int", "seconds", None)]),
    ("usleep", "int", None, [("useconds_t", "usec", None)]),
    (
        "ptrace",
        "long",
        None,
        [
            ("int", "request", "ptrace"),
            ("pid_t", "pid", None),
            ("void *", "addr", None),
            ("void *", "data", None),
        ],
    ),
    (
        "prctl",
        "int",
        None,
        [("int", "option", "prctl"), ("...", "", None)],
    ),
    (
        "fcntl",
        "int",
        None,
        [("int", "fd", None), ("int", "cmd", "fcntl"), ("...", "", None)],
    ),
    ("dlopen", "void *", None, [("const char *", "filename", None), ("int", "flags", "dlopen")]),
    (
        "dlsym",
        "void *",
        None,
        [("void *", "handle", "dl_handle"), ("const char *", "symbol", None)],
    ),
    ("dlclose", "int", None, [("void *", "handle", None)]),
    ("dlerror", "char *", None, []),
    (
        "pthread_create",
        "int",
        None,
        [
            ("pthread_t *", "thread", None),
            ("const pthread_attr_t *", "attr", None),
            ("void *", "start_routine", None),
            ("void *", "arg", None),
        ],
    ),
    ("pthread_join", "int", None, [("pthread_t", "thread", None), ("void **", "retval", None)]),
    ("pthread_mutex_lock", "int", None, [("pthread_mutex_t *", "mutex", None)]),
    ("pthread_mutex_unlock", "int", None, [("pthread_mutex_t *", "mutex", None)]),
]

# Pointer typedefs the declarations above use that `CTYPES` spells as plain
# words: they pass as pointers.
POINTER_WORDS = {
    "PLONG",
    "PBOOL",
    "LPHANDLE",
    "LPWSADATA",
    "PMEMORY_BASIC_INFORMATION",
}


def declarator(ctype: str, name: str) -> str:
    """A parameter as C spells it: `DWORD dwFlags`, `char *buf`, `...`."""
    if ctype == "...":
        return "..."
    return f"{ctype}{name}" if ctype.endswith("*") else f"{ctype} {name}"


def base_word(ctype: str) -> str:
    """The type's base word, `const`, tags and stars removed."""
    words = [w for w in ctype.replace("*", " ").split() if w not in ("const", "struct")]
    return " ".join(words)


def check() -> list[str]:
    """Names everything the tables would state wrongly."""
    problems: list[str] = []
    for group, (kind, members) in GROUPS.items():
        if kind not in ("flags", "enum"):
            problems.append(f"group {group}: kind {kind}")
        names = [n for n, _ in members]
        if len(set(names)) != len(names):
            problems.append(f"group {group}: a member named twice")
        values = [v for _, v in members]
        if len(set(values)) != len(values):
            problems.append(f"group {group}: a value named twice")
    seen: set[tuple[str, str]] = set()
    for os_name, rows in (("win", WIN), ("c", C), ("posix", POSIX)):
        for name, ret, ret_group, params in rows:
            key = (name, os_name)
            if key in seen:
                problems.append(f"{name}: declared twice for {os_name}")
            seen.add(key)
            if ret_group is not None and ret_group not in GROUPS:
                problems.append(f"{name}: no group {ret_group}")
            for i, (ctype, pname, group) in enumerate(params):
                if ctype == "...":
                    if i != len(params) - 1:
                        problems.append(f"{name}: `...` before the last parameter")
                    continue
                if not pname.isidentifier():
                    problems.append(f"{name}: parameter {i} is named {pname!r}")
                if group is not None and group not in GROUPS:
                    problems.append(f"{name}: no group {group}")
            for ctype in [ret, *(p[0] for p in params if p[0] != "...")]:
                word = base_word(ctype)
                pointer = "*" in ctype or "(" in ctype
                if not pointer and word not in CTYPES and word not in POINTER_WORDS:
                    problems.append(f"{name}: no C type word {word!r}")
    names = {n for n, o in seen}
    for name in names:
        if (name, "c") in seen and ((name, "win") in seen or (name, "posix") in seen):
            problems.append(f"{name}: in the C rows and a platform's")
    return problems


def tables() -> dict[str, str]:
    """The three tables' text, by file name."""
    words = dict(CTYPES)
    for w in POINTER_WORDS:
        words[w] = "ptr"
    ctypes = "".join(f"{name}\t{kind}\n" for name, kind in sorted(words.items()))
    rows: list[tuple[str, str, str]] = []
    for os_name, decls in (("win", WIN), ("c", C), ("posix", POSIX)):
        for name, ret, ret_group, params in decls:
            spelled = "|".join(declarator(t, n) for t, n, _ in params)
            groups = "|".join(g or "-" for _, _, g in params)
            if not any(g for _, _, g in params):
                groups = "-"
            line = "\t".join([name, os_name, ret, ret_group or "-", spelled or "-", groups or "-"])
            rows.append((name, os_name, line))
    typelib = "".join(f"{line}\n" for _, _, line in sorted(rows))
    consts = sorted(
        (group, value, name, kind)
        for group, (kind, members) in GROUPS.items()
        for name, value in members
    )
    constants = "".join(
        f"{group}\t{kind}\t{name}\t{value:#x}\n" for group, value, name, kind in consts
    )
    return {"ctypes.tsv": ctypes, "typelib.tsv": typelib, "constants.tsv": constants}


def main(argv: list[str]) -> int:
    problems = check()
    if problems:
        for p in problems:
            print(f"typelib: {p}", file=sys.stderr)
        return 1
    only_check = "--check" in argv
    stale: list[str] = []
    for name, text in tables().items():
        path = os.path.join(OUT, name)
        try:
            with open(path, encoding="utf-8", newline="") as f:
                current = f.read()
        except FileNotFoundError:
            current = None
        if current == text:
            continue
        if only_check:
            stale.append(name)
            continue
        with open(path, "w", encoding="utf-8", newline="") as f:
            f.write(text)
        print(f"wrote {os.path.relpath(path, ROOT)}")
    if stale:
        print(
            f"typelib: {', '.join(stale)} differ from scripts/typelib.py; run it to regenerate",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
