use super::{End, Script, Slot, literals};
use crate::analysis::{Analysis, Overlay};
use crate::program::{Arch, Program, Section};

/// An unwritten frame byte reads as the fresh stack's zero, the value
/// the machine reads there.
///
/// A load that spans a written slot and its padding keeps each side's
/// bytes: `*(uint64_t*)&local_30` holds the store to `local_30` in its
/// low byte, `local_2c`'s store in its high half, and zeros between.
///
/// # Panics
///
/// When the load picks a written byte up one lane early, or faults.
#[test]
fn an_unwritten_frame_byte_reads_as_the_fresh_stack() {
    let mut code = vec![0xccu8; 0x40];
    code[..0x11].copy_from_slice(&[
        0x48, 0x83, 0xec, 0x30, // ASM: sub rsp,30h
        0x89, 0x54, 0x24, 0x04, // ASM: mov [rsp+4],edx
        0xc6, 0x04, 0x24, 0x0b, // ASM: mov byte [rsp],0Bh
        0x48, 0x8b, 0x04, 0x24, // ASM: mov rax,[rsp]
        0xc3, // ASM: ret
    ]);
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    let source = "// signature: uint64_t f(uint64_t a1, uint64_t a2)
// layout a1: 0x0 u64
uint8_t local_30;
uint32_t local_2c;

local_30 = 11;
local_2c = a2;
return *(uint64_t*)&local_30;
";
    let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
    let ends_with = |rhs: &str, x: &str| {
        let head = format!(
            "// signature: uint64_t f(uint64_t a1, uint64_t a2)
uint8_t local_30;
uint32_t local_2c;

local_30 = 11;
local_2c = {rhs};
return {x};
"
        );
        Script::read(&p, &a, &Overlay::default(), 0x1000, &head)
            .unwrap()
            .run(&[0x5000, 0x80], &[], 100)
            .unwrap()
            .end
    };
    assert_eq!(
        ends_with("0x80", "*(uint8_t*)((char*)&local_30 + 1)"),
        End::Returned(Some(0)),
        "a constant write stays off the padding byte"
    );
    assert_eq!(
        ends_with("a2", "*(uint8_t*)((char*)&local_30 + 1)"),
        End::Returned(Some(0)),
        "a parameter write stays off the padding byte"
    );
    assert_eq!(
        ends_with("0x80", "*(uint64_t*)&local_30"),
        End::Returned(Some(0x0000_0080_0000_000b)),
        "a constant write four bytes up reads in the high half"
    );
    let bare = "// signature: uint64_t f(uint64_t a1, uint64_t a2)
uint8_t local_30;

local_30 = 11;
return *(uint64_t*)&local_30;
";
    assert_eq!(
        Script::read(&p, &a, &Overlay::default(), 0x1000, bare)
            .unwrap()
            .run(&[0x5000, 0x80], &[], 100)
            .unwrap()
            .end,
        End::Returned(Some(11)),
        "a u64 load over one written byte reads zeros past it"
    );
    let r = s
        .run(&[0x5000, 0x80], &[(0x5000, vec![0; 8])], 100)
        .unwrap();
    assert_eq!(r.end, End::Returned(Some(0x0000_0080_0000_000b)));
}

/// A helper the text writes only in a condition runs.
///
/// The overflow tests and the parity flag are helpers of the closed
/// vocabulary, which the reader evaluates instead of leaving the run
/// unchecked.
///
/// # Panics
///
/// When the run stops unchecked or returns another value.
#[test]
fn a_condition_helper_runs() {
    let p = Program::raw_x64(&[0xc3; 0x10]);
    let a = Analysis::compute(&p);
    let source = "// signature: uint64_t f(uint64_t a1, uint64_t a2)

return saddo16(a1, a2) + parity8(a1) + uaddo64(a1, a2);
";
    let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
    let r = s.run(&[0x7fff, 1], &[], 100).unwrap();
    assert_eq!(r.end, End::Returned(Some(2)));
    let r = s.run(&[u64::MAX, 1], &[], 100).unwrap();
    assert_eq!(r.end, End::Returned(Some(2)));
}

/// On a 32-bit target an address wraps at 32 bits, as the machine's do:
/// `((uint16_t*)a2)[a1]` with `a1` all ones reads the word before `a2`.
///
/// # Panics
///
/// When the read faults past four gigabytes or reads elsewhere.
#[test]
fn a_32_bit_address_wraps_as_the_machine_wraps_it() {
    let mut bytes = vec![0xc3u8; 0x200];
    bytes[0x100] = 0x34;
    bytes[0x101] = 0x12;
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
    let p = Program::raw(bytes, Arch::X86, 0, Some(0x1000), vec![text, data]);
    let a = Analysis::compute(&p);
    let source = "// signature: uint32_t f(uint32_t a1, uint32_t a2)

return ((uint16_t*)a2)[a1];
";
    let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
    let r = s.run(&[0xffff_ffff, 0x2002], &[], 100).unwrap();
    assert_eq!(r.end, End::Returned(Some(0x1234)));
}

/// A name two functions share is the one the function calls: the text
/// spells an overload by its bare name.
///
/// # Panics
///
/// When the run calls the other function.
#[test]
fn a_shared_name_is_the_function_called() {
    let mut code = vec![0xccu8; 0x50];
    code[..11].copy_from_slice(&[
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1020
        0xc3, // ASM: ret
    ]);
    code[0x10..0x16].copy_from_slice(&[0xb8, 1, 0, 0, 0, 0xc3]);
    code[0x20..0x26].copy_from_slice(&[0xb8, 2, 0, 0, 0, 0xc3]);
    code[0x40..0x46].copy_from_slice(&[
        0xe8, 0xcb, 0xff, 0xff, 0xff, // ASM: call 0x1010
        0xc3, // ASM: ret
    ]);
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1010, "f".to_owned());
    o.names.insert(0x1020, "f".to_owned());
    let source = "// signature: uint64_t g(void)

return f();
";
    let s = Script::read(&p, &a, &o, 0x1000, source).unwrap();
    let r = s.run(&[], &[], 1000).unwrap();
    assert_eq!(r.end, End::Returned(Some(2)));
}

/// A callee stopping for a reason of the emulator's leaves a run
/// unchecked.
///
/// A branch on flags the clean state at a call leaves unset, or a jump
/// into the function's own body printed as a call, is no difference of
/// the text. A callee that cannot return (it ends in a trap or a call
/// that never comes back, a panic) is one: the text took a path the
/// binary, which returned, did not.
///
/// # Panics
///
/// When either run ends as anything but unchecked.
#[test]
fn a_callee_stopping_for_the_emulator_is_unchecked() {
    let mut code = vec![0xccu8; 0x20];
    code[..6].copy_from_slice(&[
        0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
        0xc3, // ASM: ret
    ]);
    code[0x10..0x13].copy_from_slice(&[
        0x7e, 0x00, // ASM: jle 0x1012
        0xc3, // ASM: ret
    ]);
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for source in [
        "// signature: uint64_t g(void)

return sub_1010();
",
        "// signature: uint64_t g(void)

return (*0x1005)();
",
    ] {
        let s = Script::read(&p, &a, &o, 0x1000, source).unwrap();
        let r = s.run(&[], &[], 1000).unwrap();
        assert!(matches!(r.end, End::Unchecked(_)), "{source}: {:?}", r.end);
    }
    let mut panics = code.clone();
    panics[0x12..0x14].copy_from_slice(&[0x0f, 0x0b]); // ASM: ud2
    let p = Program::raw_x64(&panics);
    let a = Analysis::compute(&p);
    let source = "// signature: uint64_t g(void)

return sub_1010();
";
    let s = Script::read(&p, &a, &o, 0x1000, source).unwrap();
    let r = s.run(&[], &[], 1000).unwrap();
    assert!(matches!(r.end, End::Callee(..)), "{:?}", r.end);
}

/// A call to code no function starts at is a jump the text prints as a
/// call, whose code expects another frame: unchecked, not a difference.
///
/// # Panics
///
/// When the run ends as anything but unchecked.
#[test]
fn a_call_to_no_function_is_unchecked() {
    let p = Program::raw_x64(&[
        0xff, 0xe0, // ASM: jmp rax
        0x48, 0x8b, 0x44, 0x24, 0x40, // ASM: mov rax,[rsp+0x40]
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    assert!(a.function(0x1002).is_none());
    let source = "// signature: uint64_t g(void)

return (*0x1002)();
";
    let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
    let r = s.run(&[], &[], 1000).unwrap();
    assert!(matches!(r.end, End::Unchecked(_)), "{:?}", r.end);
}

/// A local the text hands an import and then reads is unchecked when
/// nothing set it: the emulator answers an import without filling what
/// it is handed, where the real one would.
///
/// # Panics
///
/// When the read is reported as a fault.
#[test]
fn a_local_an_import_was_handed_is_unchecked() {
    let mut p = Program::raw_x64(&[0xc3]);
    p.symbols.push(crate::program::Symbol {
        name: "kernel32.dll!GetSystemTimeAsFileTime".to_owned(),
        addr: 0x1800,
        kind: crate::program::SymbolKind::Import,
    });
    let a = Analysis::compute(&p);
    let source = "// signature: uint64_t g(void)
uint64_t local_10;

GetSystemTimeAsFileTime(&local_10);
return local_10;
";
    let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
    let r = s.run(&[], &[], 1000).unwrap();
    assert!(matches!(r.end, End::Unchecked(_)), "{:?}", r.end);
}

/// A return names each variable its value reads with the line that set
/// it, and line zero for one no line set that is no parameter.
///
/// # Panics
///
/// When the sources differ.
#[test]
fn a_return_names_where_its_variables_were_set() {
    let p = Program::raw_x64(&[0xc3]);
    let a = Analysis::compute(&p);
    let source = "// signature: uint64_t g(uint64_t a1)
uint64_t rax, rcx;

rcx = a1;
return rax + rcx + a1;
";
    let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
    let r = s.run(&[5], &[], 100).unwrap();
    assert_eq!(r.sources, [("rax".to_owned(), 0), ("rcx".to_owned(), 4)]);
}

/// The image's literals are found by their bytes, narrow and wide, each
/// at its first copy, and a run that is no literal is left out.
///
/// # Panics
///
/// When a literal is missed, found elsewhere, or a non-literal kept.
#[test]
fn literals_are_indexed_where_they_start() {
    let mut data = vec![0u8; 0x100];
    data[0x10..0x14].copy_from_slice(b"abc\0");
    data[0x20..0x24].copy_from_slice(b"abc\0");
    data[0x40..0x46].copy_from_slice(&[b'h', 0, b'i', 0, 0, 0]);
    data[0x60..0x63].copy_from_slice(&[0x01, 0x02, 0]);
    let rdata = Section::mapped(".rdata", 0x2000, 0, 0x100, false, false);
    let p = Program::raw(data, Arch::X86_64, 0, None, vec![rdata]);
    let index = literals(&p);
    assert_eq!(index.get(b"abc\0".as_slice()), Some(&0x2010));
    assert_eq!(
        index.get([b'h', 0, b'i', 0, 0, 0].as_slice()),
        Some(&0x2040)
    );
    assert_eq!(index.get([0x01, 0x02, 0].as_slice()), None);
}

/// Reads a text over a one-`ret` image and runs it.
///
/// # Panics
///
/// When the text does not read or nothing runs.
fn run(text: &str, args: &[u64]) -> (End, usize) {
    let p = Program::raw_x64(&[0xc3]);
    let a = Analysis::compute(&p);
    let s = Script::read(&p, &a, &Overlay::default(), 0x1000, text).unwrap();
    let r = s.run(args, &[], 10_000).unwrap();
    (r.end, r.line)
}

/// A case named in the function's enum header is that constant, and so
/// is the name compared against the same variable.
///
/// # Panics
///
/// When a path returns another value.
#[test]
fn an_enumerator_is_the_constant_its_header_names() {
    let cases = "// signature: uint64_t f(uint64_t a1)\n// enum values of a1: 2 values, Off = 0, On = 1\n\nswitch (a1) {\ncase Off: {\n  return 10;\n}\ncase On: {\n  return 11;\n}\ndefault: {\n  return 12;\n}\n}\n";
    assert_eq!(run(cases, &[0]).0, End::Returned(Some(10)));
    assert_eq!(run(cases, &[1]).0, End::Returned(Some(11)));
    assert_eq!(run(cases, &[2]).0, End::Returned(Some(12)));
    let compared = "// signature: uint64_t f(uint64_t a1)\n// enum values of a1: 2 values, Off = 0, On = 1\n\nif (a1 == On) {\n  return 11;\n}\nreturn 0;\n";
    assert_eq!(run(compared, &[1]).0, End::Returned(Some(11)));
    assert_eq!(run(compared, &[0]).0, End::Returned(Some(0)));
}

/// Loops, switches and gotos run as C runs them, and the return is cut
/// to the declared type.
///
/// # Panics
///
/// When a path returns another value or ends on another line.
#[test]
fn control_flow_runs_as_c_runs_it() {
    let text = "// signature: uint32_t f(uint64_t a1, uint64_t a2)\nuint64_t rax, rcx;\n\nrax = 0;\nfor (rcx = 0; rcx < a1; rcx += 1) {\n  rax += rcx;\n}\nswitch (a2) {\ncase 1: case 2: {\n  rax <<= 32;\n}\ncase 3: {\n  rax += 1;\n  break;\n}\ndefault: {\n  goto L_9;\n}\n}\nreturn rax;\nL_9:\nreturn ~rax;\n";
    assert_eq!(run(text, &[4, 3]).0, End::Returned(Some(7)));
    assert_eq!(run(text, &[4, 1]).0, End::Returned(Some(1)));
    assert_eq!(run(text, &[4, 9]), (End::Returned(Some(0xffff_fff9)), 22));
}

/// C's conversions hold: an `int32_t` compares signed, a narrow value
/// promotes, a `uint8_t *` steps by bytes and a `uint32_t *` by four.
///
/// # Panics
///
/// When a conversion differs from C's.
#[test]
fn conversions_follow_c() {
    let text = "// signature: uint64_t f(uint64_t a1)\nuint64_t rax;\nuint8_t rcx;\n\nrcx = 0xff;\nif ((int32_t)a1 < 0) {\n  return (uint64_t)((uint32_t*)0 + 2) + rcx + 1;\n}\nreturn (int64_t)(int8_t)rcx;\n";
    assert_eq!(run(text, &[0xffff_ffff]).0, End::Returned(Some(8 + 0x100)));
    assert_eq!(run(text, &[1]).0, End::Returned(Some(u64::MAX)));
    let bits = "// signature: int32_t f(int32_t a1)\ndouble d;\n\nd = (double)(((float)a1) & 0xffffffff);\nif (d < 1.0) {\n  return 1;\n}\nreturn 2;\n";
    assert_eq!(run(bits, &[1]).0, End::Returned(Some(1)));
    let pick = "// signature: uint64_t f(uint64_t a1)

if ((a1 == 0 ? 1 : a1) <= -32) {
  return 1;
}
return 0;
";
    assert_eq!(run(pick, &[0]).0, End::Returned(Some(1)));
}

/// What the reader does not model stops the run at its line, unchecked,
/// rather than guessing.
///
/// # Panics
///
/// When the run ends otherwise or elsewhere.
#[test]
fn what_it_cannot_read_stops_at_its_line() {
    let text = "// signature: uint64_t f(uint64_t a1)\nuint64_t rax;\n\nrax = a1;\nrax = frobnicate(rax);\nreturn rax;\n";
    let (end, line) = run(text, &[1]);
    assert_eq!(end, End::Unchecked("frobnicate is not modeled".to_owned()));
    assert_eq!(line, 5);
}

/// A stack slot lives at its frame offset, so its address is a real
/// one and two slots that overlap share bytes.
///
/// # Panics
///
/// When a slot is no memory or the overlap is lost.
#[test]
fn stack_slots_share_their_frame() {
    let p = Program::raw_x64(&[0xc3]);
    let a = Analysis::compute(&p);
    let text = "// signature: uint64_t f(void)\nuint64_t local_10;\nuint32_t local_c;\n\nlocal_10 = 0x1122334455667788;\nlocal_c = 0;\nreturn local_10;\n";
    let s = Script::read(&p, &a, &Overlay::default(), 0x1000, text).unwrap();
    assert!(matches!(
        s.vars.get("local_c").map(|v| v.slot),
        Some(Slot::Mem(_))
    ));
    let r = s.run(&[], &[], 100).unwrap();
    assert_eq!(r.end, End::Returned(Some(0x5566_7788)));
}

/// Runs a text once as ISO C on a function that only returns.
///
/// # Arguments
///
/// * `text` - The text, header first.
/// * `args` - The argument values.
///
/// # Panics
///
/// When the text does not read.
fn run_iso(text: &str, args: &[u64]) -> End {
    let p = Program::raw_x64(&[0xc3]);
    let a = Analysis::compute(&p);
    let s = Script::read_iso(&p, &a, &Overlay::default(), 0x1000, text).unwrap();
    s.run(args, &[], 10_000).unwrap().end
}

/// In ISO mode each local is an object of its own: the overlapping
/// slots that share the frame's bytes in the machine's reading keep
/// their own, and the control flow and conversions are C's as before.
///
/// # Panics
///
/// When a store to one local reaches another, or a run differs.
#[test]
fn iso_locals_are_objects_of_their_own() {
    let text = "// signature: uint64_t f(void)
uint64_t local_10;
uint32_t local_c;

local_10 = 0x1122334455667788;
local_c = 0;
return local_10;
";
    assert_eq!(
        run_iso(text, &[]),
        End::Returned(Some(0x1122_3344_5566_7788))
    );
    let text = "// signature: uint32_t f(uint64_t a1, uint64_t a2)
uint64_t rax, rcx;

rax = 0;
for (rcx = 0; rcx < a1; rcx += 1) {
  rax += rcx;
}
if (a2 == 3) {
  rax += 1;
}
return rax;
";
    assert_eq!(run_iso(text, &[4, 3]), End::Returned(Some(7)));
    assert_eq!(run_iso(text, &[4, 1]), End::Returned(Some(6)));
}

/// In ISO mode a read of what no line set is refused.
///
/// That is a variable, a local's byte past the one written, a register
/// the text never declares and a parameter the signature does not
/// list. The machine's reading answers the first from the entry's
/// register.
///
/// # Panics
///
/// When a read of poison runs on.
#[test]
fn iso_refuses_a_read_of_what_no_line_set() {
    let unset = "// signature: uint64_t f(uint64_t a1)
uint64_t rax;

return rax + a1;
";
    assert!(matches!(run_iso(unset, &[1]), End::Refused(why) if why.contains("`rax`")));
    assert_eq!(run(unset, &[1]).0, End::Returned(Some(1)));
    let past = "// signature: uint64_t f(void)
uint8_t local_30;

local_30 = 11;
return *(uint64_t*)&local_30;
";
    assert!(matches!(run_iso(past, &[]), End::Refused(why) if why.contains("local")));
    let register = "// signature: uint64_t f(uint64_t a1)

return rdx;
";
    assert!(matches!(run_iso(register, &[1]), End::Refused(why) if why.contains("`rdx`")));
    let unlisted = "// signature: uint64_t f(uint64_t a1)

return a2;
";
    assert!(matches!(run_iso(unlisted, &[1]), End::Refused(why) if why.contains("`a2`")));
}

/// A callee finds the text's register variables in the registers no
/// argument travels in, and hands back the width it returns.
///
/// As the machine's callee finds the caller's, one that leaves `rax`
/// as it found it hands back the caller's `rax`. A callee handing back
/// a byte hands back that byte, as C converts a `uint8_t` result, not
/// the caller's bits above it.
///
/// # Panics
///
/// When a run returns otherwise.
#[test]
fn a_callee_finds_the_texts_registers_and_hands_back_its_width() {
    let mut code = vec![
        0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
        0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1020
        0x0f, 0xb6, 0xc0, // ASM: movzx eax,al
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.push(0xc3); // ASM: ret
    code.resize(0x20, 0xcc);
    code.extend([0xb0, 0x07, 0xc3]); // ASM: mov al,7; ret
    let p = Program::raw_x64(&code);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for (body, want) in [
        ("rax = 5;\nrax = sub_1010();\nreturn rax;\n", 5),
        ("rax = 0x100;\nrax = sub_1020();\nreturn rax;\n", 7),
    ] {
        let source = format!("// signature: uint64_t f(void)\nuint64_t rax;\n\n{body}");
        let s = Script::read(&p, &a, &o, 0x1000, &source).unwrap();
        let r = s.run(&[], &[], 1000).unwrap();
        assert_eq!(r.end, End::Returned(Some(want)), "{body}");
    }
}
