// Lists every function that calls an import, and what else it calls.
//
//   borer script app.exe callers_of.rhai VirtualProtect
//
// The argument is part of an import's name (`VirtualProtect` finds
// `KERNEL32.dll!VirtualProtect`), case ignored.

let want = if args().len > 0 { args()[0].to_lower() } else { "" };
if want == "" {
    print("usage: callers_of.rhai <part of an import's name>");
    return;
}
for imp in imports() {
    if !imp.name.to_lower().contains(want) { continue; }
    print(`${imp.name} at ${hex(imp.at)}`);
    let seen = [];
    for x in xrefs(imp.at) {
        let f = x.function;
        if f == () || seen.contains(f) { continue; }
        seen.push(f);
        let also = [];
        for c in callees(f) {
            also.push(name(c));
        }
        print(`  ${hex(f)} ${name(f)} (${x.kind}) also calls: ${also}`);
    }
}
