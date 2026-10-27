//! The resource catalog: every `borer://` resource and template the
//! server lists, and the names they are listed under.

/// The MIME type of every resource: plain text tables, as the tools answer.
pub(crate) const TEXT_PLAIN: &str = "text/plain";

/// The fixed resources: URI and description. Each is listed under the name
/// its URI's path spells ([`resource_name`]).
pub(crate) const RESOURCES: &[(&str, &str)] = &[
    (
        "borer://help",
        "Every resource with what it answers, one line each; a template read without its argument (borer://emulate), or borer://help/<name>, gives its grammar and an example",
    ),
    (
        "borer://info",
        "Summary of the loaded program (binary_info)",
    ),
    (
        "borer://session",
        "Where this session stands: what is loaded, the overlay's counts and whether it is saved, the names, comments, types and loads it applied, and the requests it answered, each marked held (since=<tag> answers what changed), capped or paged",
    ),
    (
        "borer://annotations",
        "Annotation overlay: names and comments",
    ),
    (
        "borer://qt",
        "Qt classes from moc metadata: signals, slots, methods and properties, each mapped to its function",
    ),
    (
        "borer://objc",
        "Objective-C classes and categories from a Mach-O's runtime metadata, a row per method with its implementation (named -[Class sel]), 200 a page; borer://objc/<filter> narrows by class or selector",
    ),
    (
        "borer://capabilities",
        "What the program can do, grouped from its imports: networking, injection, crypto, persistence, anti-analysis and more",
    ),
    (
        "borer://clr",
        "A .NET assembly's metadata: its types, its methods with each body's address (IL is not decompiled; a mixed-mode image's native methods analyze as usual), P/Invokes as dll!export, the external members it uses, referenced assemblies and its user strings, 200 rows a page; borer://clr/<filter> narrows by kind (type, method, pinvoke, memberref, asmref, moduleref, string) or text",
    ),
    (
        "borer://hidden",
        "Strings the program generates at run time by mixing a keystream, recovered by running the generators",
    ),
    (
        "borer://decoded",
        "Strings a decoder function produces, recovered by running it at each of its call sites with that site's arguments (ciphertext pointer, length): a row per recovered string with its decoder and call site; a function that only copies yields nothing; borer://decoded/<filter> narrows by text",
    ),
    (
        "borer://stackstrings",
        "Strings a function builds on its stack a piece at a time, which malware does to keep text out of the data sections",
    ),
    (
        "borer://vm",
        "Dispatch loops: an interpreter's table jump with the handlers that return to it, which is what a virtualized function looks like",
    ),
    (
        "borer://dynimports",
        "The APIs and DLLs the program resolves at runtime via GetProcAddress/LoadLibrary, the imports a thin table hides",
    ),
    (
        "borer://checks",
        "Functions that decide whether a key, serial or license is valid, with the constants they test against",
    ),
    (
        "borer://antianalysis",
        "The anti-debug and anti-VM techniques the binary carries, at the instruction level and in its imports",
    ),
    (
        "borer://flat",
        "Functions whose control flow was flattened into one loop around a switch: every block a case, the block order destroyed, a state variable saying which runs next",
    ),
    (
        "borer://map",
        "The program's namespaces, each with its classes counted by role (from a pack's [roles] lines, else the role words in class names: managers, components, widgets, messages, commands), singletons and methods: a table of contents; borer://map/<namespace> lists one namespace's classes with role, parent, methods and instance",
    ),
    (
        "borer://attrs",
        "Every typed attribute the program registers (entity state: hit points, positions, timers), from the registrar a pack names ([attributes] registrar), with its four-character code, type, access mode, default and the functions using it, 200 rows a page; borer://attrs/<filter> narrows by name or code, and one exact match lists every user with the definition global",
    ),
    (
        "borer://packs",
        "The packs this session knows (named in BORER_PACKS, and every pack in the pack directories) and whether each loads for the loaded program: a pack loads by itself when all its [match] lines hold",
    ),
    (
        "borer://ports",
        "Every message every port (entity property, manager, UI handler) accepts and the function its dispatch calls for it, or inline, from the accept helpers a pack names ([messages] accept); borer://ports/<filter> narrows by component or message",
    ),
    (
        "borer://messages",
        "Every class that registered a four-character wire id, with its named fields and the functions that test for the id (the handlers), 200 rows a page, a function named in several cells numbered once in a # functions: legend; borer://messages/<filter> narrows by class name",
    ),
    (
        "borer://index",
        "Builds the decompilation index of the loaded program (every function's pseudo-C, cached on disk for borer://grep) and reports its size",
    ),
    (
        "borer://triage",
        "What the first ten calls of a triage would tell you, in one: format, protection, anti-analysis, crypto, generated strings, capabilities, and the functions to read first with the evidence for each; for a file with no code (data, an archive, another instruction set), its magic, entropy, high-entropy and encoded regions, and strings",
    ),
    (
        "borer://protection",
        "Whether the image is packed or protected, which protector the section names give away, and the evidence",
    ),
    (
        "borer://iocs",
        "Indicators to block or hunt: URLs, domains, IP and e-mail addresses, registry keys, file paths, pipe, mutex and kernel object names, user agents, each with where it came from (a stored string's address, a stack string, a generated string, decoded base64, an emulated API or syscall argument, an API call's argument), the function using it and a confidence, benign-common marking what every program carries; 200 rows a page, borer://iocs/<filter> narrows by type or text",
    ),
    (
        "borer://fingerprint",
        "The identity of this build's fingerprints: a digest, the counts, and how to write the sidecar a later borer://diff reads. The manifest itself is a file, written by the CLI, because one line per function is megabytes",
    ),
    (
        "borer://hashes",
        "The content hashes a file is correlated by: imphash (Mandiant's dll.function MD5 as pefile and VirusTotal compute it: table order, dll lowercased with .dll/.ocx/.sys stripped, ordinals named as pefile names them), authentihash (SHA-256 with the checksum, security directory and certificate table excluded, so signing does not move it), tlsh (Trend Micro's TLSH, the T1 string public feeds carry; none under 50 bytes or for too little variety) and borer-lsh (borer's own locality-sensitive hash, matching only another borer-lsh)",
    ),
    (
        "borer://encoded",
        "Strings stored encoded: base64 and hex text whose decoded bytes are text or a known file (a URL, a config, an embedded archive), each with its address and the decoded value; borer://encoded/<filter> narrows by decoded text",
    ),
    (
        "borer://children",
        "Programs and containers embedded in the file, each found by its signature and kept only when its headers validate (PE, ELF, Mach-O, zip, gzip, xz, 7z, cab, squashfs, cpio, uImage, cramfs, Android boot image), with offset, size and a one-line identity, plus the high-entropy runs no header explains: packed, compressed or encrypted bytes. load_binary path=<file>@<off> opens a program row as a program of its own; containers are listed, not extracted",
    ),
    (
        "borer://asserts",
        "The fields the binary's assertions name, with the classes that assert them",
    ),
    (
        "borer://sources",
        "The source files the binary's assertions name, by directory: the subsystems it was built from",
    ),
    (
        "borer://classes",
        "Every class that registered a four-character code, the code that identifies it on the wire, with its method count and first method",
    ),
    (
        "borer://singletons",
        "The program's singletons: the classes whose one instance lives at a fixed thread-local or global slot, with the slot and the ::Instance accessor - the engine's global object model",
    ),
    (
        "borer://enums",
        "Every name table the binary encodes (string-to-constant parsers and constant-to-string tables), one line per function",
    ),
    (
        "borer://bench",
        "Wall-clock speed of borer's hot queries on the loaded binary (AOB scan, string walks, indexed grep when the index is cached): one row per op with its answer size, fastest elapsed and throughput; timings differ run to run, the counts never do",
    ),
];

/// The resource templates: URI template, description, and an example.
///
/// The example is read with `{entry}` and `{path}` filled in from the
/// loaded binary ([`resources::example`]). Each is listed under the name
/// its first path segment spells ([`resource_name`]).
pub(crate) const RESOURCE_TEMPLATES: &[(&str, &str, &str)] = &[
    (
        "borer://help/{name}",
        "How to read one resource: its URI, what it answers and, for a template, an example built from the loaded binary",
        "borer://help/emulate",
    ),
    (
        "borer://session/evidence/{id}",
        "The answer its `# evidence:` line names, kept as it was sent; every answer carries one as its last line (a mermaid graph: `%% evidence:`), the id <n>-<8 hex digits>, and this returns the text behind it or says it was let go past the 256 the session keeps",
        "borer://session/evidence/1-00000000",
    ),
    (
        "borer://playbook/{name}",
        "A prompt's text, for an agent whose host offers prompts only to its user: triage, protocol, find_check/<what is validated> or explain_function/<function>",
        "borer://playbook/triage",
    ),
    (
        "borer://stackstrings/{filter}",
        "Stack strings whose text contains the filter",
        "borer://stackstrings/http",
    ),
    (
        "borer://flat/{address}",
        "Cases of one flattening dispatcher, in table order, each with where it ends. The table order is not the order they run",
        "borer://flat/{entry}",
    ),
    (
        "borer://solve/{spec}",
        "Find an argument value that makes a check answer differently: spec is <address>[,aN] (the decompiler's aN, a1 by default). Every constant the function compares against is tried and the answers grouped, so a value standing apart is the one it wants, with the comparison it came from",
        "borer://solve/{entry},a1",
    ),
    (
        "borer://partial/{address}",
        "A counted loop comparing a few bits of a product to a byte table: the iterations, the bit window, the table and the loop-invariant multiplicand. That shape is a hidden-number problem, solved by lattice reduction and not by more samples",
        "borer://partial/{entry}",
    ),
    (
        "borer://sig/{address}",
        "The shortest byte signature that matches the code at a function or address exactly once, the bytes that move between builds (RIP-relative displacements, absolute addresses, branch offsets) wildcarded: the pattern, a C string with its mask, and whether it is unique",
        "borer://sig/{entry}",
    ),
    (
        "borer://yara/{functions}",
        "A YARA rule that finds the functions again: each one's unique byte signature and the strings it references, under the file's magic; functions are names or entries, comma-separated. The rule ends at its closing brace: save it up to there, since borer's own note lines follow, or use the CLI's borer yara, which writes it alone",
        "borer://yara/{entry}",
    ),
    (
        "borer://names/{tool}",
        "borer's names and comments for another tool to apply: tool is ida (an IDAPython script), ghidra (a Ghidra Python script), binja (a Binary Ninja script) or x64dbg (a database to load); a PE's scripts rebase to the tool's image base. An x64dbg database ends at its closing brace: save it up to there, since borer's own note lines follow, or use the CLI's borer names, which writes the file alone",
        "borer://names/ida",
    ),
    (
        "borer://addr/{place}",
        "One place as virtual address, relative address, file offset, section and function: place is a virtual address, rva:<n> or off:<n>",
        "borer://addr/{entry}",
    ),
    (
        "borer://encoded/{filter}",
        "Encoded strings whose decoded value contains {filter}",
        "borer://encoded/http",
    ),
    (
        "borer://why/{address}",
        "What is at an address and how borer knows: where its name came from (the compiler's debug information, a symbol, inferred from code, or nothing), why the function was discovered, what refers to it, and any value recovered by running the code that builds it",
        "borer://why/{entry}",
    ),
    (
        "borer://layout/{spec}",
        "Propose a structure from what a function does through one pointer: spec is <address>[,<register>] (a register, or aN for the argument the decompiler names aN; default the first argument). Each row is a field with the width of the access and what it is passed to. Add ,apply=<Name> at a function's entry to define the fields as struct Name and type that parameter with it, so decompile names them (a dry run; add ,dry_run=false to apply)",
        "borer://layout/{entry},rcx",
    ),
    (
        "borer://taint/{spec}",
        "Follow a value forward through its function: spec is <address>[,<register>] (a register, or aN for the argument the decompiler names aN; default rax, where a call leaves its result). Reports the instructions that carry it, the calls it is passed to and as which argument, the memory it is stored into, and where it still is at the end",
        "borer://taint/{entry},rax",
    ),
    (
        "borer://patch/{spec}",
        "Plan a dry-run patch; borer never writes the file. Replace the whole instructions at an address with new machine code: spec is <at>/<hexbytes>[,detour][,cave=<addr>], at an address or name, hexbytes the replacement as pairs of hex digits (x86/x64 machine code written as if it sits at <at>; borer re-encodes it at its destination through iced, fixing relative branches and RIP-relative operands). Returns the new code and its position-dependent references, the whole original instructions it overwrites with the nop padding named, whether it fits in place or needs a code cave and the usable padding runs (00, cc or 90) in executable sections with their sizes, an emulator check of the planned bytes, and a borer-patch-v1 file (one line per region: file-offset, old-bytes, new-bytes, all hex and equal length, old verified before new is written) a separate tool applies. detour forces a jmp-to-cave trampoline even when the bytes would fit in place; cave=<addr> places the detour at that cave instead of searching",
        "borer://patch/{entry}/9090c3",
    ),
    (
        "borer://emulate/{address}",
        "Run code and read the result. The address carries an experiment: comma-separated reg=val, aN=val (the argument the decompiler names aN; a1 is the first), w<addr>=<hexbytes> (set data or patch code), stop=<addr>, steps=<n> (at most 20000000), trace=<n> (what each of the last n instructions changed; a small steps= watches the start instead), origin=<v> (the instruction that first put the value v in a register or in memory), profile=<n> (the n most-run addresses and most-read pages, where the steps went; at most 64), dump=<addr>:<len> (at most 4096 bytes, ?? where nothing is mapped). Reports final registers, the imported APIs and syscalls it serviced as api(args) -> ret with each argument decoded (a string as text, a flag or handle named, an unknown pointer as ptr 0x...), decoded text and each dump.",
        "borer://emulate/{entry},a1=5,steps=10000",
    ),
    (
        "borer://devirt/{address}",
        "Run a virtualized function and recover the program it executes: handlers summarized once, the trace cleaned of dead stores (writes nothing that runs after them reads) and cut into straight-line runs at every virtual branch, one line per step. The address carries comma-separated settings: budget=<n> raises the step cap (2000000 by default, at most 100000000) for a protector whose dispatch starts after a long bootstrap; strict faults on the first read of an import or of memory the loader would fill, where by default it reads zero and goes on; reg=<value> presets a register, such as the VM's context pointer the entry does not build",
        "borer://devirt/{entry},budget=4000000",
    ),
    (
        "borer://unpack/{address}",
        "Run a packer's bootstrap and report the code it decrypts into memory, with the original entry point. Append ,budget=N to raise the step cap toward a fuller unpack",
        "borer://unpack/{entry}",
    ),
    (
        "borer://calls/{callee}",
        "Every call site of a function or import (direct, through its slot or a thunk) with the arguments the decompiler resolves at each: a constant in hex, a string quoted, a global by name, else the expression, ? where the lifter saw none (an import is padded to its declared parameters). <callee>[,aN=<value>]...: aN=0x40 keeps the calls whose argument aN is that number, aN=text the ones whose argument or string contains it, aN=? the unseen ones; aN!=, aN> and aN< too; offset=<n> for the next page (200 rows a page, 500 callers decompiled at most)",
        "borer://calls/{entry}",
    ),
    (
        "borer://iocs/{filter}",
        "Indicators of one type (url, domain, ip, ipv4, ipv6, email, registry, path, pipe, mutex, object, useragent) or whose value contains the text, comma-separated; offset=<n> for the next page",
        "borer://iocs/url",
    ),
    (
        "borer://hidden/{filter}",
        "Run-time generated strings whose text or generator matches {filter}",
        "borer://hidden/http",
    ),
    (
        "borer://decoded/{filter}",
        "Decoder-recovered strings whose text contains {filter}; offset=<n> for the next page",
        "borer://decoded/http",
    ),
    (
        "borer://oracle/{address}",
        "Run the function at {address} over a probe string in every argument shape and report what it does with it",
        "borer://oracle/{entry}",
    ),
    (
        "borer://run/{spec}",
        "Call a function on inputs typed by its recovered signature and check its decompiled text on them: <function>[,steps=N]/<input>[;<input>...], each input its arguments in order: 5, -1, \"text\", hex:0102 or out:16 (a zeroed buffer). A row per input: the return value, the stop, the steps, the bytes each buffer holds after, and whether the text run as C agrees, differs (at a line) or is unchecked (at most 64 inputs, 1000000 steps each by default, 100000000 in all); then the imported APIs and syscalls the runs serviced as api(args) -> ret with each argument decoded",
        "borer://run/{entry}/5;-1",
    ),
    (
        "borer://diverge/{spec}",
        "Call a function on two inputs and report where the runs part ways: the first step that differs (the comparison that split them), the calls each side then makes, and the writes and serviced calls that differ: <function>[,steps=N]/<input>;<input>",
        "borer://diverge/{entry}/5;-1",
    ),
    (
        "borer://vectors/{spec}",
        "Test vectors for reimplementing a function: <function>[,count=N][,steps=N]. Inputs from the constants it compares and generated from its recovered signature (16 by default, at most 64), each run in the emulator: a row per input with what it returned and left in its buffers, then a C harness asserting the vectors that returned",
        "borer://vectors/{entry}",
    ),
    (
        "borer://diff/{path}",
        "Compare the loaded binary against another version at {path} and report which functions changed, were added or removed",
        "borer://diff/{path}",
    ),
    (
        "borer://difffn/{function}/{path}",
        "Show how one function changed between the loaded binary and another version at {path}, as a diff of the decompilations",
        "borer://difffn/{entry}/{path}",
    ),
    (
        "borer://carry/{path}",
        "Carry this project's names to another build of the same program: each name with its new address and how the function was paired, by identical body or by shape. An update moves every address, and the fingerprints do not move",
        "borer://carry/{path}",
    ),
    (
        "borer://migrate/{function}/{path}",
        "Migrate the field offsets a function reads from the loaded build to the version at {path}: which offsets are unchanged, removed, added, or moved",
        "borer://migrate/{entry}/{path}",
    ),
    (
        "borer://vm/{address}",
        "The handlers of one dispatch loop, each with what it does",
        "borer://vm/{entry}",
    ),
    (
        "borer://asserts/{filter}",
        "Asserted fields whose name or class contains the filter",
        "borer://asserts/count",
    ),
    (
        "borer://sources/{filter}",
        "Source files whose path contains the filter, with their function counts",
        "borer://sources/net",
    ),
    (
        "borer://classes/{filter}",
        "Registered classes whose name or code contains the filter",
        "borer://classes/player",
    ),
    (
        "borer://messages/{filter}",
        "Classes with a registered wire id whose name contains the filter, each with its named fields and the handlers testing for the id (200 a page)",
        "borer://messages/move",
    ),
    (
        "borer://map/{namespace}",
        "One namespace's classes, each with its role, parent, methods and instance (5000 rows at most)",
        "borer://map/net",
    ),
    (
        "borer://ports/{filter}",
        "The messages ports accept and their handlers, for the components or messages whose name contains the filter (5000 rows at most)",
        "borer://ports/move",
    ),
    (
        "borer://attrs/{filter}",
        "Registered attributes whose name or code contains the filter (200 a page); one exact match lists every function reading or writing it with the definition global",
        "borer://attrs/health",
    ),
    (
        "borer://exportpack/{spec}",
        "The session's names as a pack that names the same functions in another build by their first bytes: <name>, or <name>,all to add the names borer recovered",
        "borer://exportpack/mine,all",
    ),
    (
        "borer://scenario/{spec}",
        "A function decompiled under assumptions, <function>/<a2=5,a3=0>: branches and switches on them fold, only the code that can run is written, and the first line counts the blocks cut",
        "borer://scenario/{entry}/a1=5",
    ),
    (
        "borer://scenarios/{spec}",
        "A dispatcher exploded, <function>/<a2=0..32> or <function>/<a2=1|5>: a scenario per value, the values that behave alike grouped, each row with its blocks kept, calls and returns",
        "borer://scenarios/{entry}/a1=0..8",
    ),
    (
        "borer://script/{path}",
        "Runs a Rhai script file against the loaded program in borer's sandbox: what it printed, and the names and comments it proposes (set_name applies one)",
        "borer://script/scan.rhai",
    ),
    (
        "borer://clr/{filter}",
        "A .NET assembly's metadata rows of one kind (type, method, pinvoke, memberref, asmref, moduleref, string) or whose name or detail contains the text, comma-separated; offset=<n> for the next page",
        "borer://clr/pinvoke",
    ),
    (
        "borer://singletons/{filter}",
        "Singletons whose class name contains the filter",
        "borer://singletons/manager",
    ),
    (
        "borer://function/{address}",
        "function_summary at an address or name",
        "borer://function/{entry}",
    ),
    (
        "borer://decompile/{address}",
        "Pseudo-C of the function at an address or name",
        "borer://decompile/{entry}",
    ),
    (
        "borer://disasm/{address}",
        "Disassembly of the function at an address or name",
        "borer://disasm/{entry}",
    ),
    (
        "borer://fields/{address}",
        "Field offsets the function at an address or name dereferences, by (base, offset)",
        "borer://fields/{entry}",
    ),
    (
        "borer://fieldrefs/{offset}",
        "Every instruction program-wide that reads, writes or takes the address of \
                     [reg+offset], with its function; `offset[,name-filter]`, 500 rows at most",
        "borer://fieldrefs/0x10",
    ),
    (
        "borer://vslot/{slot}",
        "Every recovered class whose virtual at a zero-based vtable slot returns a \
                     constant (a wire id, a type tag), by value; `slot[,class-filter]`",
        "borer://vslot/3",
    ),
    (
        "borer://schema/{function}",
        "The record a deserializer reads off its stream (fields, widths, nesting, \
                     repeats), for a function by address or name, or the reading virtual of a class",
        "borer://schema/{entry}",
    ),
    (
        "borer://schemas/{slot}",
        "Every class with a constant at a zero-based vtable slot and the record its \
                     reading virtual decodes, one line each: a protocol as a table; `slot[,class-filter]`",
        "borer://schemas/3",
    ),
    (
        "borer://encode/{function}",
        "What a serializer writes onto its stream (fields in wire order, widths, the \
                     object field each came from, helpers followed into the members they write), \
                     for a function by address or name, or the writing virtual of a class",
        "borer://encode/{entry}",
    ),
    (
        "borer://hooks/{slot}",
        "Every class with a constant at a zero-based vtable slot with the addresses \
                     a binding hooks: its encoder, its decoder, its handler and each call site \
                     the client sends it from; `slot[,class-filter]`",
        "borer://hooks/3",
    ),
    (
        "borer://protocol/{slot}",
        "Every class with a constant at a zero-based vtable slot on one row with \
                     who constructs it, the handler receiving it, what it writes onto the wire \
                     and what it reads back: the whole protocol as one table; `slot[,class-filter]`",
        "borer://protocol/3",
    ),
    (
        "borer://senders/{slot}",
        "Every class with a constant at a zero-based vtable slot and the functions \
                     calling its factory or constructors: who sends each command, as a table; \
                     `slot[,class-filter]`",
        "borer://senders/3",
    ),
    (
        "borer://encodes/{slot}",
        "Every class with a constant at a zero-based vtable slot and what its writing \
                     virtual puts on the wire, one line each: the outbound protocol as a table; \
                     `slot[,class-filter]`",
        "borer://encodes/3",
    ),
    (
        "borer://shape/{function}",
        "Every function running the same code as the one at an address or name over \
                     other operands, with the strings and data addresses that differ: a \
                     registration family as a table",
        "borer://shape/{entry}",
    ),
    (
        "borer://anchors/{path}",
        "Every pinned fact in a manifest file (`field <class> <name> <offset>`, \
                     `vconst <slot> <class> <value>`, `function <name> <rva>`, `encode <class> \
                     <layout>`, `decode <class> <layout>` lines) derived again from the loaded \
                     binary and reported held, moved, changed or gone",
        "borer://anchors/client.anchors",
    ),
    (
        "borer://changes/{path}",
        "What changed since a snapshot file of an earlier build (written by the CLI's \
                     `borer snapshot <binary> <file>`): commands, packet layouts, attributes, \
                     message routes and ids added, removed or changed, by stable name",
        "borer://changes/before.snapshot",
    ),
    (
        "borer://about/{name}",
        "Everything known about one name, from every table at once: the attribute \
                     (with each user reading or writing it), the class (role, parent, instance, \
                     virtuals, the messages it accepts or the components handling it, the wire \
                     for a command), and the function summary; start here with any name",
        "borer://about/{entry}",
    ),
    (
        "borer://grep/{text}",
        "Pseudo-C lines program-wide containing the text (percent-encoded), or \
                     matching it when written re:<expression>, with their function, its \
                     signature and the if/else/loop/switch/case lines enclosing them \
                     (numbered ^N); decompiles \
                     everything once into the index on first use; 200 matching lines at most",
        "borer://grep/memcpy",
    ),
];

/// The `# more:` line of `binary_info`: every resource template by name,
/// from [`RESOURCE_TEMPLATES`] itself.
///
/// The line was written by hand and named 14 of 45 templates, so an agent
/// reading it never learned of the rest.
pub(crate) fn template_names() -> String {
    let names: Vec<&str> = RESOURCE_TEMPLATES
        .iter()
        .map(|&(uri, _, _)| resource_name(uri))
        .collect();
    format!(
        "{} templated resources read by URI through resources/read or the query tool, each described by resources/templates/list or read without its argument: {}",
        names.len(),
        names.join(", ")
    )
}

/// The name a resource is listed under: the first segment of its path,
/// `vslot` for `borer://vslot/{slot}`.
///
/// # Arguments
///
/// * `uri` - The resource URI or URI template.
pub(crate) fn resource_name(uri: &str) -> &str {
    let path = uri.strip_prefix("borer://").unwrap_or(uri);
    path.split_once('/').map_or(path, |(name, _)| name)
}

#[cfg(test)]
mod tests {
    use crate::testing::raw_server;

    /// The resource documentation says what the resources do.
    ///
    /// Every template the dispatcher answers is listed, `binary_info`
    /// names every template, no description carries a run of spaces from a
    /// broken line, and `emulate` and `devirt` describe every setting they
    /// read, `trace=` as the last steps it keeps.
    ///
    /// # Panics
    ///
    /// When a template is unlisted or unnamed, or a description misleads.
    #[test]
    fn the_resource_docs_say_what_the_resources_do() {
        let info = raw_server().binary_info().expect("info");
        let more = info
            .lines()
            .find_map(|l| l.strip_prefix("# more: "))
            .expect("a more line");
        for &(uri, _, _) in super::RESOURCE_TEMPLATES {
            let name = super::resource_name(uri);
            assert!(more.split([' ', ',']).any(|w| w == name), "{name}: {more}");
        }
        for uri in ["borer://map/{namespace}", "borer://ports/{filter}"] {
            assert!(
                super::RESOURCE_TEMPLATES.iter().any(|&(u, _, _)| u == uri),
                "{uri} is answered but not listed"
            );
        }
        let described_all = super::RESOURCES
            .iter()
            .copied()
            .chain(super::RESOURCE_TEMPLATES.iter().map(|&(u, d, _)| (u, d)));
        for (uri, text) in described_all {
            assert!(!text.contains("  "), "{uri}: {text}");
        }
        let described = |uri: &str| {
            super::RESOURCE_TEMPLATES
                .iter()
                .find(|&&(u, _, _)| u == uri)
                .map(|&(_, text, _)| text)
                .expect("listed")
        };
        let emulate = described("borer://emulate/{address}");
        assert!(
            emulate.contains("each of the last n instructions"),
            "{emulate}"
        );
        assert!(
            emulate.contains("origin=") && emulate.contains("profile="),
            "{emulate}"
        );
        let devirt = described("borer://devirt/{address}");
        for setting in ["budget=", "strict", "reg="] {
            assert!(devirt.contains(setting), "{setting}: {devirt}");
        }
    }
}
