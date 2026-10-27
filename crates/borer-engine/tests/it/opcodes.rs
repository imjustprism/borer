//! Opcode protocols, read from hand-assembled 32-bit code.
//!
//! A dispatcher reads an opcode off a stream and switches on it, by a jump
//! table or a compare chain, to handlers that read on from the same
//! stream; a sender writes a constant opcode first and then fields through
//! the same writer. The code is built with iced's assembler, so each
//! instruction reads as written.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::opcodes::{self, Route};
use borer_engine::analysis::schema::Field;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program};
use iced_x86::code_asm::{
    CodeAssembler, CodeLabel, al, byte_ptr, dl, dword_ptr, eax, ecx, edi, edx, esi, esp, word_ptr,
};

use crate::raw;

/// Entry of the start function calling every other.
const START: u64 = 0x401000;
/// `read_u8(stream, out)`: one byte off the cursor into `*out`.
const READ_U8: u64 = 0x401040;
/// `read_u32(stream, out)`: four bytes off the cursor into `*out`.
const READ_U32: u64 = 0x401060;
/// Handler reading a `u32` and a `u8` into its object.
const H_A: u64 = 0x401080;
/// Handler reading one `u32`.
const H_B: u64 = 0x4010c0;
/// Handler reading two bytes and a `u32`.
const H_C: u64 = 0x401100;
/// The dispatcher switching through a jump table.
const TABLE_DISPATCH: u64 = 0x401180;
/// The dispatcher switching through a compare chain.
const CHAIN_DISPATCH: u64 = 0x401280;
/// `write_u8(stream, value)`.
const WRITE_U8: u64 = 0x401380;
/// `write_u32(stream, value)`.
const WRITE_U32: u64 = 0x4013a0;
/// A sender writing opcode `0x21`, then a `u32` and a `u8` of its object.
const SENDER: u64 = 0x4013c0;
/// A serializer writing no constant first: not a sender.
const NOT_SENDER: u64 = 0x401400;
/// A sender of opcode `0x22`, handed as `0x122` to a byte writer, whose
/// first call hands its object a constant.
const SETUP_SENDER: u64 = 0x401440;
/// `read_u16(stream)`: returns the word at the cursor and steps past it.
const READ_RET: u64 = 0x401480;
/// A dispatcher on a returned opcode: one case reads a returned value
/// itself, one hands the stream to a handler in the wrong argument, one
/// to a handler in the right one.
const RETURNED_DISPATCH: u64 = 0x401740;
/// `get_mode(object)`: returns a saved setting and moves nothing.
const GET_MODE: u64 = 0x401540;
/// [`RETURNED_DISPATCH`]'s code switching on [`GET_MODE`]: not a dispatcher.
const MODE_SWITCH: u64 = 0x401800;
/// A serializer handing [`GET_MODE`], which stores nothing, a constant
/// before its writes: not a sender.
const CONFIG_SENDER: u64 = 0x401600;
/// Handler storing a word [`READ_RET`] returns at object offset 0x30.
const H_RET: u64 = 0x401640;
/// Handler `h(object, stream)` reading a `u32` into object offset 0x40.
const H_SWAP: u64 = 0x401680;
/// A sender of opcode `0x23` whose fields [`NOT_SENDER`] writes.
const PAIR_SENDER: u64 = 0x401700;
/// The jump table's address in `.rdata`.
const TABLE: u64 = 0x402000;

/// Assembles one function at `ip` with the labels it asks for resolved.
///
/// # Arguments
///
/// * `ip` - Where the function sits.
/// * `body` - Emits the instructions.
///
/// # Panics
///
/// When the assembler rejects an instruction.
fn asm(ip: u64, body: impl FnOnce(&mut CodeAssembler) -> Vec<CodeLabel>) -> (Vec<u8>, Vec<u64>) {
    let mut a = CodeAssembler::new(32).expect("32-bit assembler");
    let labels = body(&mut a);
    let r = a
        .assemble_options(
            ip,
            iced_x86::BlockEncoderOptions::RETURN_NEW_INSTRUCTION_OFFSETS,
        )
        .expect("assembles");
    let ips = labels
        .iter()
        .map(|l| r.label_ip(l).expect("label placed"))
        .collect();
    (r.inner.code_buffer, ips)
}

/// Emits `push edi; push esi; call target; add esp, 8`: a call handing
/// the stream and the object on.
///
/// # Arguments
///
/// * `a` - The assembler.
/// * `target` - The handler.
fn pass_on(a: &mut CodeAssembler, target: u64) {
    a.push(edi).expect("push");
    a.push(esi).expect("push");
    a.call(target).expect("call");
    a.add(esp, 8).expect("add");
}

/// Emits `read(stream, object + off)` from a handler's own arguments.
///
/// # Arguments
///
/// * `a` - The assembler.
/// * `reader` - The reader.
/// * `off` - The field's offset in the object.
fn read_into(a: &mut CodeAssembler, reader: u64, off: i32) {
    a.mov(eax, dword_ptr(esp + 8)).expect("mov");
    a.add(eax, off).expect("add");
    a.push(eax).expect("push");
    a.push(dword_ptr(esp + 8)).expect("push");
    a.call(reader).expect("call");
    a.add(esp, 8).expect("add");
}

/// Emits a dispatcher's head: saves `esi`/`edi`, takes the stream and the
/// object, reads the opcode into a stack slot and loads it into `eax`.
///
/// # Arguments
///
/// * `a` - The assembler.
fn dispatch_head(a: &mut CodeAssembler) {
    a.push(esi).expect("push");
    a.push(edi).expect("push");
    a.push(ecx).expect("push");
    a.mov(esi, dword_ptr(esp + 0x10)).expect("mov");
    a.mov(edi, dword_ptr(esp + 0x14)).expect("mov");
    a.mov(eax, esp).expect("mov");
    a.push(eax).expect("push");
    a.push(esi).expect("push");
    a.call(READ_U8).expect("call");
    a.add(esp, 8).expect("add");
    a.movzx(eax, byte_ptr(esp)).expect("movzx");
}

/// Assembles a primitive at `at` handed `(stream, value)`: loads the
/// stream's cursor into `eax` and the value into `edx`, runs `body`, and
/// steps the cursor by `step`.
///
/// # Arguments
///
/// * `at` - Where the primitive sits.
/// * `step` - The bytes it moves the cursor.
/// * `body` - Emits the read or the write.
fn primitive(at: u64, step: i32, body: impl FnOnce(&mut CodeAssembler)) -> Vec<u8> {
    asm(at, |a| {
        a.mov(ecx, dword_ptr(esp + 4)).expect("mov");
        a.mov(edx, dword_ptr(esp + 8)).expect("mov");
        a.mov(eax, dword_ptr(ecx)).expect("mov");
        body(a);
        a.add(dword_ptr(ecx), step).expect("add");
        a.ret().expect("ret");
        Vec::new()
    })
    .0
}

/// Emits a dispatcher's tail: restores the registers its head saved and
/// returns.
///
/// # Arguments
///
/// * `a` - The assembler.
fn dispatch_tail(a: &mut CodeAssembler) {
    a.pop(ecx).expect("pop");
    a.pop(edi).expect("pop");
    a.pop(esi).expect("pop");
    a.ret().expect("ret");
}

/// Assembles the dispatcher switching through the jump table at
/// [`TABLE`] over opcodes 0 to 3.
///
/// # Returns
///
/// The code and the case addresses the table holds.
fn table_dispatcher() -> (Vec<u8>, Vec<u64>) {
    asm(TABLE_DISPATCH, |a| {
        let mut cases: Vec<CodeLabel> = (0..4).map(|_| a.create_label()).collect();
        let mut default = a.create_label();
        let mut done = a.create_label();
        dispatch_head(a);
        a.cmp(eax, 3).expect("cmp");
        a.ja(default).expect("ja");
        a.jmp(dword_ptr(eax * 4 + i32::try_from(TABLE).expect("table")))
            .expect("jmp");
        for (label, handler) in cases.iter_mut().zip([H_A, H_B, H_C, H_A]) {
            a.set_label(label).expect("label");
            pass_on(a, handler);
            a.jmp(done).expect("jmp");
        }
        a.set_label(&mut default).expect("label");
        a.xor(eax, eax).expect("xor");
        a.set_label(&mut done).expect("label");
        dispatch_tail(a);
        cases
    })
}

/// Assembles `read_u16(stream)`, which returns the word at the cursor and
/// steps the cursor past it.
fn returning_reader() -> Vec<u8> {
    asm(READ_RET, |a| {
        a.mov(ecx, dword_ptr(esp + 4)).expect("mov");
        a.mov(eax, dword_ptr(ecx)).expect("mov");
        a.movzx(eax, word_ptr(eax)).expect("movzx");
        a.add(dword_ptr(ecx), 2).expect("add");
        a.ret().expect("ret");
        Vec::new()
    })
    .0
}

/// Assembles [`H_RET`]: `object->field_0x30 = read_u16(stream)`.
fn returning_handler() -> Vec<u8> {
    asm(H_RET, |a| {
        a.push(dword_ptr(esp + 4)).expect("push");
        a.call(READ_RET).expect("call");
        a.add(esp, 4).expect("add");
        a.mov(ecx, dword_ptr(esp + 8)).expect("mov");
        a.mov(dword_ptr(ecx + 0x30), eax).expect("mov");
        a.ret().expect("ret");
        Vec::new()
    })
    .0
}

/// Assembles [`H_SWAP`]: `read_u32(stream, object + 0x40)` with the object
/// first and the stream second.
fn swapped_handler() -> Vec<u8> {
    asm(H_SWAP, |a| {
        a.mov(eax, dword_ptr(esp + 4)).expect("mov");
        a.add(eax, 0x40).expect("add");
        a.push(eax).expect("push");
        a.push(dword_ptr(esp + 12)).expect("push");
        a.call(READ_U32).expect("call");
        a.add(esp, 8).expect("add");
        a.ret().expect("ret");
        Vec::new()
    })
    .0
}

/// Assembles [`PAIR_SENDER`]: `write_u8(stream, 0x23)`, then
/// [`NOT_SENDER`] handed the stream and the object.
fn pair_sender() -> Vec<u8> {
    asm(PAIR_SENDER, |a| {
        a.push(esi).expect("push");
        a.push(edi).expect("push");
        a.mov(esi, dword_ptr(esp + 12)).expect("mov");
        a.mov(edi, dword_ptr(esp + 16)).expect("mov");
        a.push(0x23).expect("push");
        a.push(esi).expect("push");
        a.call(WRITE_U8).expect("call");
        a.add(esp, 8).expect("add");
        pass_on(a, NOT_SENDER);
        a.pop(edi).expect("pop");
        a.pop(esi).expect("pop");
        a.ret().expect("ret");
        Vec::new()
    })
    .0
}

/// Assembles [`GET_MODE`]: returns the word at offset 8 of its argument.
fn mode_getter() -> Vec<u8> {
    asm(GET_MODE, |a| {
        a.mov(eax, dword_ptr(esp + 4)).expect("mov");
        a.mov(eax, dword_ptr(eax + 8)).expect("mov");
        a.ret().expect("ret");
        Vec::new()
    })
    .0
}

/// Assembles a dispatcher on the value `reader` returns.
///
/// Case 1 reads a `u32` into object offset 0x20 and stores a second
/// returned value at offset 4, both in its record in order; case 2 calls
/// [`H_A`] with the object where the stream belongs, case 3 calls [`H_B`]
/// as it expects, case 4 calls [`H_RET`], case 5 calls [`H_SWAP`] twice.
///
/// # Arguments
///
/// * `at` - Where it sits.
/// * `reader` - The function returning the switched value.
fn returned_dispatcher(at: u64, reader: u64) -> Vec<u8> {
    asm(at, |a| {
        let mut cases: Vec<CodeLabel> = (0..5).map(|_| a.create_label()).collect();
        let mut done = a.create_label();
        a.push(esi).expect("push");
        a.push(edi).expect("push");
        a.mov(esi, dword_ptr(esp + 12)).expect("mov");
        a.mov(edi, dword_ptr(esp + 16)).expect("mov");
        a.push(esi).expect("push");
        a.call(reader).expect("call");
        a.add(esp, 4).expect("add");
        for (label, op) in cases.iter().zip([1, 2, 3, 4, 5]) {
            a.cmp(eax, op).expect("cmp");
            a.je(*label).expect("je");
        }
        a.jmp(done).expect("jmp");
        a.set_label(&mut cases[0]).expect("label");
        a.lea(eax, dword_ptr(edi + 0x20)).expect("lea");
        a.push(eax).expect("push");
        a.push(esi).expect("push");
        a.call(READ_U32).expect("call");
        a.add(esp, 8).expect("add");
        a.push(esi).expect("push");
        a.call(reader).expect("call");
        a.add(esp, 4).expect("add");
        a.mov(dword_ptr(edi + 4), eax).expect("mov");
        a.jmp(done).expect("jmp");
        a.set_label(&mut cases[1]).expect("label");
        a.push(esi).expect("push");
        a.push(edi).expect("push");
        a.call(H_A).expect("call");
        a.add(esp, 8).expect("add");
        a.jmp(done).expect("jmp");
        a.set_label(&mut cases[2]).expect("label");
        pass_on(a, H_B);
        a.jmp(done).expect("jmp");
        a.set_label(&mut cases[3]).expect("label");
        pass_on(a, H_RET);
        a.jmp(done).expect("jmp");
        a.set_label(&mut cases[4]).expect("label");
        for _ in 0..2 {
            a.push(esi).expect("push");
            a.push(edi).expect("push");
            a.call(H_SWAP).expect("call");
            a.add(esp, 8).expect("add");
        }
        a.set_label(&mut done).expect("label");
        a.pop(edi).expect("pop");
        a.pop(esi).expect("pop");
        a.ret().expect("ret");
        Vec::new()
    })
    .0
}

/// Assembles the dispatcher comparing the opcode with `0x10`, `0x20` and
/// `0x31` in turn.
fn chain_dispatcher() -> Vec<u8> {
    asm(CHAIN_DISPATCH, |a| {
        let mut cases: Vec<CodeLabel> = (0..3).map(|_| a.create_label()).collect();
        let mut done = a.create_label();
        dispatch_head(a);
        for (label, op) in cases.iter().zip([0x10, 0x20, 0x31]) {
            a.cmp(eax, op).expect("cmp");
            a.je(*label).expect("je");
        }
        a.jmp(done).expect("jmp");
        for (label, handler) in cases.iter_mut().zip([H_B, H_C, H_A]) {
            a.set_label(label).expect("label");
            pass_on(a, handler);
            a.jmp(done).expect("jmp");
        }
        a.set_label(&mut done).expect("label");
        dispatch_tail(a);
        Vec::new()
    })
    .0
}

/// Assembles a serializer writing its object's `u32` at 8 and `u8` at
/// 0xc, after `opcode` when one is given, and after a call handing the
/// object a constant when `setup` is set.
///
/// # Arguments
///
/// * `at` - Where it sits.
/// * `opcode` - The constant written first and the function handed it, if
///   any.
/// * `setup` - Whether a call passing the object and 0 comes first.
fn serializer(at: u64, opcode: Option<(i32, u64)>, setup: bool) -> Vec<u8> {
    asm(at, |a| {
        a.push(esi).expect("push");
        a.push(edi).expect("push");
        a.mov(esi, dword_ptr(esp + 12)).expect("mov");
        a.mov(edi, dword_ptr(esp + 16)).expect("mov");
        if setup {
            a.push(0).expect("push");
            a.push(edi).expect("push");
            a.call(H_B).expect("call");
            a.add(esp, 8).expect("add");
        }
        if let Some((op, writer)) = opcode {
            a.push(op).expect("push");
            a.push(esi).expect("push");
            a.call(writer).expect("call");
            a.add(esp, 8).expect("add");
        }
        for (writer, off) in [(WRITE_U32, 8), (WRITE_U8, 0xc)] {
            a.mov(eax, dword_ptr(edi + off)).expect("mov");
            a.push(eax).expect("push");
            a.push(esi).expect("push");
            a.call(writer).expect("call");
            a.add(esp, 8).expect("add");
        }
        a.pop(edi).expect("pop");
        a.pop(esi).expect("pop");
        a.ret().expect("ret");
        Vec::new()
    })
    .0
}

/// Builds the image: readers, writers, three handlers, both dispatchers
/// and two serializers, each at its constant, and the jump table.
fn program() -> Program {
    let mut code = vec![0xccu8; 0x1000];
    let mut put = |at: u64, bytes: &[u8]| {
        let off = usize::try_from(at - START).expect("offset");
        let room = &mut code[off..off + bytes.len()];
        assert!(room.iter().all(|&b| b == 0xcc), "{at:#x} overlaps");
        room.copy_from_slice(bytes);
    };
    let (start, _) = asm(START, |a| {
        for f in [
            TABLE_DISPATCH,
            CHAIN_DISPATCH,
            SENDER,
            NOT_SENDER,
            SETUP_SENDER,
            RETURNED_DISPATCH,
            MODE_SWITCH,
            CONFIG_SENDER,
            PAIR_SENDER,
        ] {
            a.call(f).expect("call");
        }
        a.ret().expect("ret");
        Vec::new()
    });
    put(START, &start);
    put(
        READ_U8,
        &primitive(READ_U8, 1, |a| {
            a.movzx(eax, byte_ptr(eax)).expect("movzx");
            a.mov(byte_ptr(edx), al).expect("mov");
        }),
    );
    put(
        READ_U32,
        &primitive(READ_U32, 4, |a| {
            a.mov(eax, dword_ptr(eax)).expect("mov");
            a.mov(dword_ptr(edx), eax).expect("mov");
        }),
    );
    put(
        WRITE_U8,
        &primitive(WRITE_U8, 1, |a| {
            a.mov(byte_ptr(eax), dl).expect("mov");
        }),
    );
    put(
        WRITE_U32,
        &primitive(WRITE_U32, 4, |a| {
            a.mov(dword_ptr(eax), edx).expect("mov");
        }),
    );
    for (at, reads) in [
        (H_A, vec![(READ_U32, 8), (READ_U8, 0xc)]),
        (H_B, vec![(READ_U32, 0x10)]),
        (
            H_C,
            vec![(READ_U8, 0x14), (READ_U8, 0x15), (READ_U32, 0x18)],
        ),
    ] {
        let (h, _) = asm(at, |a| {
            for (reader, off) in reads {
                read_into(a, reader, off);
            }
            a.ret().expect("ret");
            Vec::new()
        });
        put(at, &h);
    }
    let (td, cases) = table_dispatcher();
    put(TABLE_DISPATCH, &td);
    put(CHAIN_DISPATCH, &chain_dispatcher());
    put(SENDER, &serializer(SENDER, Some((0x21, WRITE_U8)), false));
    put(NOT_SENDER, &serializer(NOT_SENDER, None, false));
    put(
        SETUP_SENDER,
        &serializer(SETUP_SENDER, Some((0x122, WRITE_U8)), true),
    );
    put(READ_RET, &returning_reader());
    put(H_RET, &returning_handler());
    put(H_SWAP, &swapped_handler());
    put(PAIR_SENDER, &pair_sender());
    put(
        RETURNED_DISPATCH,
        &returned_dispatcher(RETURNED_DISPATCH, READ_RET),
    );
    put(GET_MODE, &mode_getter());
    put(MODE_SWITCH, &returned_dispatcher(MODE_SWITCH, GET_MODE));
    put(
        CONFIG_SENDER,
        &serializer(CONFIG_SENDER, Some((7, GET_MODE)), false),
    );
    let table: Vec<u8> = cases
        .iter()
        .flat_map(|&c| u32::try_from(c).expect("32-bit").to_le_bytes())
        .collect();
    raw::image(Arch::X86, &code, &table)
}

/// The kinds of a record's top-level fields, in order.
///
/// # Arguments
///
/// * `fields` - The record.
fn kinds(fields: &[Field]) -> Vec<&str> {
    fields.iter().map(|f| f.kind.as_str()).collect()
}

/// A dispatcher switching through a jump table: the opcode is the byte
/// the reader stores, the table picks the case, and each case's record is
/// the schema of the handler it hands the stream to.
#[test]
fn a_jump_table_dispatcher_maps_each_opcode_to_its_handler_and_record() {
    let p = program();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let d = opcodes::dispatch_of(&p, &a, &o, TABLE_DISPATCH).expect("a dispatcher");
    assert_eq!(d.stream, "a1");
    assert_eq!(d.kind, "u8");
    assert!(!d.returned);
    assert_eq!(d.read_at, Some(TABLE_DISPATCH + 0xf));
    assert!(
        matches!(d.route, Route::Table { entries: 4, .. }),
        "{:?}",
        d.route
    );
    let rows: Vec<(String, Option<u64>, Vec<&str>)> = d
        .cases
        .iter()
        .map(|c| (c.labels.join(","), c.handler, kinds(&c.fields)))
        .collect();
    assert_eq!(
        rows,
        [
            ("0".to_owned(), Some(H_A), vec!["u32", "u8"]),
            ("1".to_owned(), Some(H_B), vec!["u32"]),
            ("2".to_owned(), Some(H_C), vec!["u8", "u8", "u32"]),
            ("3".to_owned(), Some(H_A), vec!["u32", "u8"]),
        ]
    );
    let table = opcodes::dispatch_tsv(&p, &a, &o, TABLE_DISPATCH, "", 2).expect("a table");
    assert!(
        table.contains("4 read on from it, showing 2 of 4"),
        "{table}"
    );
    assert!(table.contains("picked by a jump table"), "{table}");
    assert!(
        table.contains("0x1\tsub_4010c0@0x4010c0\t1\tu32@+0x10"),
        "{table}"
    );
}

/// A dispatcher switching through a chain of compares reads the same, its
/// opcodes the constants compared, and says no table picks the case.
#[test]
fn a_compare_chain_dispatcher_maps_each_opcode_to_its_handler() {
    let p = program();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let d = opcodes::dispatch_of(&p, &a, &o, CHAIN_DISPATCH).expect("a dispatcher");
    assert_eq!(d.route, Route::Compare);
    let rows: Vec<(String, Option<u64>)> = d
        .cases
        .iter()
        .map(|c| (c.labels.join(","), c.handler))
        .collect();
    assert_eq!(
        rows,
        [
            ("16".to_owned(), Some(H_B)),
            ("32".to_owned(), Some(H_C)),
            ("49".to_owned(), Some(H_A)),
        ]
    );
    let table =
        opcodes::dispatch_tsv(&p, &a, &o, CHAIN_DISPATCH, "sub_401100", 10).expect("a table");
    assert!(table.contains("picked by compares"), "{table}");
    assert!(table.contains("showing 1 of 1"), "{table}");
    assert!(table.contains("0x20\tsub_401100@0x401100\t3\t"), "{table}");
    assert!(opcodes::dispatch_of(&p, &a, &o, H_A).is_none());
}

/// A sender hands its writer the opcode as a constant first and fields
/// after it.
///
/// A call handing something else a constant before it does not hide it;
/// a serializer writing no constant first, or handing its first constant
/// to a function that stores nothing, is not one.
#[test]
fn a_sender_writes_its_opcode_first_and_then_its_fields() {
    let p = program();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let s = opcodes::send_of(&p, &a, &o, SENDER).expect("a sender");
    assert_eq!(s.opcode, 0x21);
    assert_eq!(s.writer, "sub_401380");
    assert_eq!(s.write_at, Some(SENDER + 0xd));
    let e = s.encoding;
    let writes: Vec<(&str, &str)> = e
        .fields
        .iter()
        .map(|w| (w.kind.as_str(), w.source.as_str()))
        .collect();
    assert_eq!(writes, [("u8", "33"), ("u32", "a2+0x8"), ("u8", "a2+0xc")]);
    assert!(opcodes::send_of(&p, &a, &o, NOT_SENDER).is_none());
    assert!(opcodes::send_of(&p, &a, &o, CONFIG_SENDER).is_none());
    let pair = opcodes::send_of(&p, &a, &o, PAIR_SENDER).expect("a sender through a helper");
    let helper = pair.encoding.fields.get(1).expect("the helper's write");
    let inner: Vec<&str> = helper.children.iter().map(|w| w.kind.as_str()).collect();
    assert_eq!(inner, ["u32", "u8"], "{pair:?}");
    let setup = opcodes::send_of(&p, &a, &o, SETUP_SENDER).expect("a sender after a setup call");
    assert_eq!(setup.opcode, 0x22);
    assert!(opcodes::send_of(&p, &a, &o, H_A).is_none());
}

/// A returned opcode is read as one, and a switch on a value returned
/// without moving the stream is not.
///
/// A case reading a returned value has that read as its record, and a
/// handler handed the stream where it reads something else has none.
#[test]
fn a_returned_opcode_and_returned_reads_are_read_and_a_misfed_handler_is_not() {
    let p = program();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let d = opcodes::dispatch_of(&p, &a, &o, RETURNED_DISPATCH).expect("a dispatcher");
    assert!(d.returned, "{d:?}");
    assert_eq!(d.kind, "u16", "{d:?}");
    assert_eq!(d.cases[0].fields[1].kind, "u16", "{d:?}");
    assert_eq!(d.reader, "sub_401480");
    let rows: Vec<(String, Option<u64>, Vec<&str>)> = d
        .cases
        .iter()
        .filter(|c| c.labels != ["default"])
        .map(|c| {
            (
                c.labels.join(","),
                c.handler,
                c.fields.iter().map(|f| f.via.as_str()).collect(),
            )
        })
        .collect();
    assert_eq!(
        rows,
        [
            ("1".to_owned(), None, vec!["sub_401060", "sub_401480"]),
            ("2".to_owned(), Some(H_A), vec![]),
            ("3".to_owned(), Some(H_B), vec!["sub_401060"]),
            ("4".to_owned(), Some(H_RET), vec!["sub_401480"]),
            ("5".to_owned(), None, vec!["sub_401060", "sub_401060"]),
        ],
        "{d:?}"
    );
    let table = opcodes::dispatch_tsv(&p, &a, &o, RETURNED_DISPATCH, "", 9).expect("a table");
    assert!(table.contains("# unsure: 0x2 read nothing"), "{table}");
    assert!(opcodes::dispatch_of(&p, &a, &o, MODE_SWITCH).is_none());
}

/// A search finds the three dispatchers and both senders, and says how many
/// functions it read.
#[test]
fn searches_find_the_dispatchers_and_the_senders() {
    let p = program();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let found = opcodes::dispatchers_tsv(&p, &a, &o, "", 10);
    assert!(found.starts_with("# 3 functions switch"), "{found}");
    assert!(
        found.contains("sub_401180\t0x401180\t4\t4\tsub_401040\t"),
        "{found}"
    );
    assert!(found.contains("sub_401280\t0x401280\t3\t3\t"), "{found}");
    let sends = opcodes::sends_tsv(&p, &a, &o, "", 10);
    assert!(sends.starts_with("# 3 functions write"), "{sends}");
    assert!(sends.contains("0x22\tsub_401440\t"), "{sends}");
    assert!(
        sends.contains("0x21\tsub_4013c0\t0x4013c0\tsub_401380\t"),
        "{sends}"
    );
}
