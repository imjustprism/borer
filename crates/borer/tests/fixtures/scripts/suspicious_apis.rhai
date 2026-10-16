// Groups a program's imports by what they let it do, with the functions
// using each group, for a first look at an unknown binary.
//
//   borer script sample.exe suspicious_apis.rhai
//
// The groups are the usual triage questions: does it write into other
// processes, watch for a debugger, change memory protection, load code at
// run time, talk to the network, touch the registry or services, or read
// the keyboard. A group with no import is left out. Each function that
// uses a group is commented with the group's name.

let groups = #{
    "injection": ["WriteProcessMemory", "CreateRemoteThread", "NtCreateThreadEx",
                  "QueueUserAPC", "SetThreadContext", "NtMapViewOfSection",
                  "VirtualAllocEx", "OpenProcess"],
    "anti-debug": ["IsDebuggerPresent", "CheckRemoteDebuggerPresent",
                   "NtQueryInformationProcess", "OutputDebugString",
                   "NtSetInformationThread", "GetTickCount", "QueryPerformanceCounter"],
    "memory protection": ["VirtualProtect", "VirtualAlloc", "NtProtectVirtualMemory"],
    "run-time loading": ["LoadLibrary", "GetProcAddress", "LdrLoadDll", "LdrGetProcedureAddress"],
    "network": ["WSAStartup", "connect", "InternetOpen", "HttpSendRequest",
                "WinHttpOpen", "URLDownloadToFile", "send", "recv"],
    "registry and services": ["RegSetValue", "RegCreateKey", "CreateService", "OpenSCManager"],
    "input capture": ["SetWindowsHookEx", "GetAsyncKeyState", "GetKeyState", "RegisterRawInputDevices"],
};

for group in groups.keys() {
    let hits = [];
    let users = [];
    for imp in imports() {
        let short = imp.name.split("!");
        let fname = short[short.len - 1];
        for want in groups[group] {
            if fname.starts_with(want) {
                hits.push(fname);
                for x in xrefs(imp.at) {
                    let f = x.function;
                    if f != () && !users.contains(f) { users.push(f); }
                }
            }
        }
    }
    if hits.len == 0 { continue; }
    print(`${group}: ${hits}`);
    for f in users {
        print(`  ${hex(f)} ${name(f)}`);
        comment(f, `uses ${group} APIs`);
    }
}
