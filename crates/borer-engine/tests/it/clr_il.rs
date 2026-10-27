//! CIL method bodies: tiny and fat headers, exception clauses and
//! instructions, and the reasons a cut body stops.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::clr::il;

/// A tiny body decodes, its branch's target an offset in the code.
#[test]
fn a_tiny_body_decodes_with_its_branch_target() {
    let bytes = [0x16, 0x14, 0x2c, 0x01, 0x00, 0x2a];
    let (b, code) = il::body(&bytes).expect("a tiny body");
    assert_eq!((b.fat, b.max_stack, b.code_len), (false, 8, 5));
    let (instrs, stop) = il::decode(code);
    assert!(stop.is_none());
    let names: Vec<&str> = instrs.iter().map(il::Instr::name).collect();
    assert_eq!(names, ["ldnull", "brfalse.s", "nop", "ret"]);
    assert_eq!(instrs[1].operand, il::Operand::Target(4));
}

/// A fat body reads its flags, locals token and a finally clause.
#[test]
fn a_fat_body_reads_its_clauses() {
    let mut bytes = vec![0x1b, 0x30, 2, 0, 4, 0, 0, 0, 1, 0, 0, 0x11];
    bytes.extend_from_slice(&[0x00, 0xfe, 0x1a, 0x2a]);
    bytes.extend_from_slice(&[1, 16, 0, 0, 2, 0, 0, 0, 1, 2, 0, 1, 0, 0, 0, 0]);
    let (b, code) = il::body(&bytes).expect("a fat body");
    assert!(b.init_locals);
    assert_eq!(b.locals, 0x1100_0001);
    assert_eq!(code.len(), 4);
    assert_eq!(b.clauses.len(), 1);
    assert_eq!(b.clauses[0].kind, il::ClauseKind::Finally);
    assert_eq!((b.clauses[0].try_start, b.clauses[0].try_end), (0, 1));
    let (instrs, _) = il::decode(code);
    assert_eq!(instrs[1].name(), "rethrow");
}

/// A cut operand or a bad header stops with the reason.
#[test]
fn a_cut_operand_stops_decoding_with_the_offset() {
    let (instrs, stop) = il::decode(&[0x00, 0x28, 1, 2]);
    assert_eq!(instrs.len(), 1);
    assert_eq!(
        stop.as_deref(),
        Some("IL_0001: the operand runs past the code")
    );
    let (_, stop) = il::decode(&[0x45, 0xff, 0xff, 0xff, 0xff]);
    assert!(stop.is_some());
    assert!(il::body(&[0x03, 0x30]).is_err());
    assert!(il::body(&[0x01]).is_err());
}
