//! The two protocol tables, `encodes` and `schemas`, against the answer
//! each class gives when it is asked for alone.
//!
//! A table lists every class answering one virtual with a constant, with
//! what its writing or reading virtual puts on the wire. Helpers are
//! followed to a depth and no further, so a helper reached at the bottom
//! of one class's chain is read less far than the same helper reached at
//! the top of another's; what a table says of a class must not depend on
//! which classes it listed before it.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::encode::{compact_writes, encoding_for_class, encodings_tsv};
use borer_engine::analysis::schema::{compact_fields, schema_for_class, schemas_tsv};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program};
use iced_x86::code_asm::{CodeAssembler, eax, qword_ptr, rax, rbx, rcx, rdi, rdx, rsp};

use crate::raw;

/// Entry of the start function calling every constructor.
const START: u64 = 0x40_1000;
/// The first constructor; each takes 0x10 bytes.
const CTORS: u64 = 0x40_1020;
/// The first constant virtual; each takes 8 bytes.
const IDS: u64 = 0x40_1050;
/// The stream accessor, `mov rax, rcx; ret`.
const ACCESSOR: u64 = 0x40_1070;
/// The primitive a chain ends in: one eight-byte store.
const PRIMITIVE: u64 = 0x40_1078;
/// The first class's wire virtual; each takes 0x40 bytes.
const WIRES: u64 = 0x40_1080;
/// The first helper of the chain; each takes 0x40 bytes.
const CHAIN: u64 = 0x40_1200;
/// The vtables of the three classes, which name them ([`CLASSES`]).
const TABLES: [u64; 3] = [0x40_2100, 0x40_2200, 0x40_2220];
/// The three classes, in the order a table reads them.
const CLASSES: [&str; 3] = ["class_402100", "class_402200", "class_402220"];
/// The helper each class's wire virtual enters the chain at: the first
/// and the last class at its top, the middle one three helpers down.
const ENTERS: [u64; 3] = [0, 3, 0];
/// A filter holding the last two classes: the one entering the chain low
/// comes first there, where the whole table lists it second.
const LAST_TWO: &str = "4022";

/// Which table an image is built for.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Wire {
    /// Writers: `helper(stream, member + 8)` on the stream an accessor
    /// handed out, down to a primitive storing the member.
    Encode,
    /// Readers: `helper(stream, out + 8)` down to a primitive storing
    /// through `out`.
    Decode,
}

/// Assembles one function at `ip`.
///
/// # Arguments
///
/// * `ip` - Where the function sits.
/// * `body` - Emits the instructions.
fn asm(ip: u64, body: impl FnOnce(&mut CodeAssembler)) -> Vec<u8> {
    let mut a = CodeAssembler::new(64).expect("64-bit assembler");
    body(&mut a);
    a.assemble(ip).expect("assembles")
}

/// Emits a class's wire virtual, `virt(this, stream)`.
///
/// The writer takes the stream from the accessor, hands `helper` the
/// member at `this + 0x10` and the primitive the one at `this + 0x18`; the
/// reader hands `helper` the stream and `this + 0x10`.
///
/// # Arguments
///
/// * `a` - The assembler.
/// * `wire` - Which shape.
/// * `helper` - Where the virtual enters the chain.
fn wire_virtual(a: &mut CodeAssembler, wire: Wire, helper: u64) {
    match wire {
        Wire::Encode => {
            a.push(rbx).expect("push");
            a.push(rdi).expect("push");
            a.sub(rsp, 0x28).expect("sub");
            a.mov(rbx, rcx).expect("mov");
            a.mov(rcx, rdx).expect("mov");
            a.call(ACCESSOR).expect("call");
            a.mov(rdi, rax).expect("mov");
            for (callee, member) in [(helper, 0x10), (PRIMITIVE, 0x18)] {
                a.lea(rdx, qword_ptr(rbx + member)).expect("lea");
                a.mov(rcx, rdi).expect("mov");
                a.call(callee).expect("call");
            }
            a.add(rsp, 0x28).expect("add");
            a.pop(rdi).expect("pop");
            a.pop(rbx).expect("pop");
        }
        Wire::Decode => {
            a.sub(rsp, 0x28).expect("sub");
            a.mov(rax, rcx).expect("mov");
            a.mov(rcx, rdx).expect("mov");
            a.lea(rdx, qword_ptr(rax + 0x10)).expect("lea");
            a.call(helper).expect("call");
            a.add(rsp, 0x28).expect("add");
        }
    }
    a.ret().expect("ret");
}

/// Emits one helper of the chain, `helper(stream, member)`, handing `next`
/// the stream and `member + 8`; the writer takes the stream from the
/// accessor first, as the virtual does.
///
/// # Arguments
///
/// * `a` - The assembler.
/// * `wire` - Which shape.
/// * `next` - The next helper, or the primitive.
fn helper(a: &mut CodeAssembler, wire: Wire, next: u64) {
    match wire {
        Wire::Encode => {
            a.push(rbx).expect("push");
            a.sub(rsp, 0x20).expect("sub");
            a.mov(rbx, rdx).expect("mov");
            a.call(ACCESSOR).expect("call");
            a.lea(rdx, qword_ptr(rbx + 8)).expect("lea");
            a.mov(rcx, rax).expect("mov");
            a.call(next).expect("call");
            a.add(rsp, 0x20).expect("add");
            a.pop(rbx).expect("pop");
        }
        Wire::Decode => {
            a.sub(rsp, 0x28).expect("sub");
            a.add(rdx, 8).expect("add");
            a.call(next).expect("call");
            a.add(rsp, 0x28).expect("add");
        }
    }
    a.ret().expect("ret");
}

/// Builds three classes whose wire virtuals enter one chain of helpers,
/// each helper handing the stream and its member, eight bytes on, to the
/// next and the last to a primitive.
///
/// Every class answers virtual 0 with a constant and has its wire virtual
/// in slot 1.
///
/// # Arguments
///
/// * `wire` - Which shape the virtuals and helpers have.
/// * `helpers` - How long the chain is.
fn program(wire: Wire, helpers: u64) -> Program {
    let mut code = vec![0xccu8; 0x1000];
    let mut put = |at: u64, bytes: &[u8]| {
        let off = usize::try_from(at - START).expect("an address in the page");
        let free = code[off..off + bytes.len()].iter().all(|&b| b == 0xcc);
        assert!(free, "{at:#x} is taken");
        code[off..off + bytes.len()].copy_from_slice(bytes);
    };
    let link = |k: u64| {
        if k < helpers {
            CHAIN + 0x40 * k
        } else {
            PRIMITIVE
        }
    };
    put(
        START,
        &asm(START, |a| {
            for i in 0..3 {
                a.call(CTORS + 0x10 * i).expect("call");
            }
            a.ret().expect("ret");
        }),
    );
    let mut data = vec![0u8; 0x300];
    for (i, (&table, &enters)) in (0u32..).zip(TABLES.iter().zip(&ENTERS)) {
        let n = u64::from(i);
        let (ctor, id, virt) = (CTORS + 0x10 * n, IDS + 8 * n, WIRES + 0x40 * n);
        put(
            ctor,
            &asm(ctor, |a| {
                a.mov(rax, table).expect("mov");
                a.mov(qword_ptr(rcx), rax).expect("mov");
                a.ret().expect("ret");
            }),
        );
        put(
            id,
            &asm(id, |a| {
                a.mov(eax, i + 1).expect("mov");
                a.ret().expect("ret");
            }),
        );
        put(virt, &asm(virt, |a| wire_virtual(a, wire, link(enters))));
        let at = usize::try_from(table - 0x40_2000).expect("offset");
        for (k, slot) in [id, virt].into_iter().enumerate() {
            data[at + 8 * k..at + 8 * k + 8].copy_from_slice(&slot.to_le_bytes());
        }
    }
    for k in 0..helpers {
        put(link(k), &asm(link(k), |a| helper(a, wire, link(k + 1))));
    }
    put(
        ACCESSOR,
        &asm(ACCESSOR, |a| {
            a.mov(rax, rcx).expect("mov");
            a.ret().expect("ret");
        }),
    );
    put(
        PRIMITIVE,
        &asm(PRIMITIVE, |a| {
            match wire {
                Wire::Encode => a.mov(qword_ptr(rcx + 8), rdx).expect("mov"),
                Wire::Decode => a.mov(qword_ptr(rdx), rcx).expect("mov"),
            }
            a.ret().expect("ret");
        }),
    );
    raw::image(Arch::X86_64, &code, &data)
}

/// The row of `class` in a table.
///
/// # Arguments
///
/// * `table` - The table.
/// * `class` - The class.
fn row<'t>(table: &'t str, class: &str) -> &'t str {
    table
        .lines()
        .find(|l| l.split('\t').nth(1) == Some(class))
        .expect("the table lists the class")
}

/// Asserts that every class's row is the one a table of its own gives it.
///
/// Each class must answer `want` when asked alone, and its row, in the
/// whole table and in the one of the last two classes, must be the row of
/// a table listing that class alone and end in that answer.
///
/// # Arguments
///
/// * `want` - What each class answers alone, as a row's last column
///   spells it.
/// * `alone` - Asks one class alone; nothing for a class with no answer.
/// * `table` - Renders the table under a filter.
fn rows_are_the_classes_own(
    want: [&str; 3],
    alone: impl Fn(&str) -> Option<String>,
    table: impl Fn(&str) -> String,
) {
    for filter in ["", LAST_TWO] {
        let listed = table(filter);
        for (class, want) in CLASSES.into_iter().zip(want) {
            if !class.contains(filter) {
                continue;
            }
            assert_eq!(alone(class).as_deref(), Some(want), "{class} alone");
            let got = row(&listed, class);
            assert_eq!(
                got,
                row(&table(class), class),
                "{class} under the filter {filter:?}:\n{listed}"
            );
            assert!(got.ends_with(&format!("\t{want}")), "{class}: {got}");
        }
    }
}

/// A class's row in `encodes` is what the class encodes when asked alone,
/// whichever classes the table lists before it.
///
/// The chain is nine helpers long and an encoder follows six: the classes
/// entering it at its top are cut short of the primitive and their member
/// is of no known kind, while the class entering three helpers down
/// reaches it. One context serving the whole table kept each helper as
/// the first class to reach it left it: listed after a class from the
/// top, the low class lost its `u64`, and listed before one, it lent
/// that class a chain twice as deep as an encoder follows.
#[test]
fn an_encodes_row_is_what_the_class_encodes_alone() {
    let p = program(Wire::Encode, 9);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names
        .insert(ACCESSOR, "Core::Ptr<Net::Stream>::operator ->".to_owned());
    rows_are_the_classes_own(
        [
            "?@+0x10 u64@+0x18",
            "u64@+0x10 u64@+0x18",
            "?@+0x10 u64@+0x18",
        ],
        |class| encoding_for_class(&p, &a, &o, class).map(|(_, e)| compact_writes(&e.fields)),
        |filter| encodings_tsv(&p, &a, &o, 0, filter, 100),
    );
}

/// A class's row in `schemas` is what the class decodes when asked alone,
/// whichever classes the table lists before it.
///
/// The chain is ten readers long and a decoder follows eight: from the
/// top it reads seven members, 56 bytes, and from three readers down it
/// reaches the primitive, 64 bytes. One context serving the whole table
/// answered the low class with the 32 bytes the top class's cut left it,
/// or the top class with 88, past the depth a decoder follows.
#[test]
fn a_schemas_row_is_what_the_class_decodes_alone() {
    let p = program(Wire::Decode, 10);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    rows_are_the_classes_own(
        ["bytes56@+0x10", "bytes64@+0x10", "bytes56@+0x10"],
        |class| schema_for_class(&p, &a, &o, class).map(|(_, s)| compact_fields(&s.fields)),
        |filter| schemas_tsv(&p, &a, &o, 0, filter, 100),
    );
}
