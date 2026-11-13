//! Frames, SEH helpers, handlers and funclets.

use super::*;

/// A frame aligned with `and esp, -16` keeps its stack pointer: the locals
/// are locals, the argument is read through the entry pointer's copy, and
/// the `pop ecx` after the call is stack cleanup, not asm.
#[test]
fn an_aligned_frame_keeps_its_stack_pointer() {
    let text = dc(&[
        0x53, 0x8b, 0xdc, 0x83, 0xe4, 0xf0, 0x55, 0x8b, 0xec, 0x83, 0xec, 0x10, 0x8b, 0x43, 0x08,
        0x89, 0x45, 0xfc, 0xff, 0x75, 0xfc, 0xe8, 0x08, 0x00, 0x00, 0x00, 0x59, 0x8b, 0xe5, 0x5d,
        0x8b, 0xe3, 0x5b, 0xc3, 0x8b, 0x44, 0x24, 0x04, 0x83, 0xc0, 0x01, 0xc3,
    ]);
    assert!(!text.contains("/* asm"), "{text}");
    assert!(!text.contains("esp"), "{text}");
    assert!(text.contains("(a1)"), "{text}");
}

/// A frame opened with `add esp, -0x2d0` is a frame, not a jump four
/// gigabytes up.
///
/// The 32-bit immediate is signed at its width, so the push after it lands
/// in the frame and the function decompiles at once; the unsigned reading
/// once sent the lifter walking the gap until memory ran out.
#[test]
fn a_negative_add_to_the_stack_pointer_opens_a_frame() {
    let text = dc(&[
        0x55, 0x8b, 0xec, 0x81, 0xc4, 0x30, 0xfd, 0xff, 0xff, 0x53, 0x8d, 0x85, 0x38, 0xfd, 0xff,
        0xff, 0x50, 0xe8, 0x06, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x04, 0x5b, 0xc9, 0xc3, 0xc3,
    ]);
    assert!(text.contains("&local_"), "{text}");
    assert!(!text.contains("arg_ff"), "{text}");
}

/// A small 32-bit frame is a frame: `sub esp, 8` sizes it, so the read
/// above it is the first argument and not the third.
///
/// The frame facts took `sub esp, N` only at the immediate widths the
/// decoder gives 64-bit code; an 8-bit immediate in 32-bit code is another
/// width, so the frame went unrecorded and every `[esp+K]` read was placed
/// as if the frame were empty: `[esp+0xc]` over an 8-byte frame counted as
/// the third argument.
#[test]
fn a_small_32_bit_frame_is_a_frame() {
    let code = [
        0x83, 0xec, 0x08, 0x8b, 0x44, 0x24, 0x0c, 0x83, 0xc4, 0x08, 0xc3,
    ];
    let a = Analysis::compute(&image(&code));
    let f = a.function_at(0x401000).expect("the function is discovered");
    assert_eq!(f.stack_args, 1, "{f:?}");
    let text = dc(&code);
    assert!(text.contains("a1"), "{text}");
    assert!(!text.contains("a3"), "{text}");
}

/// A callee that pops its arguments leaves the caller's stack pointer
/// where it was before the pushes.
///
/// The caller `push 7; call 0x401040; mov eax,[esp-4]; ret` calls
/// `mov eax,[esp+4]; ret 4`. After the call the stack pointer is back at
/// the entry, so `[esp-4]` is the slot four below it, not eight; and the
/// callee's `ret 4` states that it takes one argument.
#[test]
fn a_callee_popping_its_arguments_moves_the_stack_pointer() {
    let mut code = vec![
        0x6a, 0x07, 0xe8, 0x39, 0x00, 0x00, 0x00, 0x8b, 0x44, 0x24, 0xfc, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let callee = a.function(0x401040).expect("callee discovered");
    assert_eq!((callee.stack_pop, callee.stack_args), (4, 1));
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("local_0"), "{text}");
    assert!(!text.contains("local_4"), "{text}");
}

/// A read far above the frame is not the hundred-millionth argument.
///
/// `mov eax, [esp+0x7ffffff0]; ret` reads a slot half a gigabyte above the
/// return address; the stack-argument count the body shows stops at the
/// cap discovery's frame scan applies, so the signature declares a few
/// dozen parameters at most, not one per word up to the read (a mutant
/// read one at six hundred thousand words, and the parameter list alone
/// was gigabytes).
#[test]
fn a_read_far_above_the_frame_is_not_an_argument() {
    let text = dc(&[0x8b, 0x84, 0x24, 0xf0, 0xff, 0xff, 0x7f, 0xc3]);
    let sig = text
        .lines()
        .find(|l| l.starts_with("// signature: "))
        .unwrap_or_default();
    assert!(sig.matches(',').count() < 40, "{sig}");
}

/// A program that talks through Qt's network classes is networking, and one
/// that calls `WinVerifyTrust` checks code integrity, whatever the raw API
/// names look like.
#[test]
fn framework_imports_reach_the_capability_map() {
    use borer_engine::analysis::render::capability_map_tsv;
    let mut p = image(&[0xc3]);
    p.symbols = [
        (0x402000, "Qt5Network.dll!?get@QNetworkAccessManager@@QAEPAVQNetworkReply@@ABVQNetworkRequest@@@Z"),
        (0x402004, "WINTRUST.dll!WinVerifyTrust"),
    ]
    .into_iter()
    .map(|(addr, name)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Import,
    })
    .collect();
    let text = capability_map_tsv(&p, None);
    assert!(text.contains("networking"), "{text}");
    assert!(text.contains("code integrity"), "{text}");
    assert!(text.contains("of 16 capabilities"), "{text}");
}

/// The 32-bit stack probe is known by its body.
///
/// A call to it then neither ends the parameter scan nor clobbers `this`,
/// which is read after it, and the call renders with the frame size it was
/// handed.
///
/// `push ebp; mov ebp,esp; mov eax,0x1000; call 0x401020; mov eax,[ecx];
/// pop ebp; ret` with the probe's opening at 0x401020, `push ecx; lea
/// ecx,[esp+4]; sub ecx,eax; …; ret`.
#[test]
fn a_call_to_the_stack_probe_keeps_this_a_parameter() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0xb8, 0x00, 0x10, 0x00, 0x00, 0xe8, 0x13, 0x00, 0x00, 0x00, 0x8b, 0x01,
        0x5d, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x51, 0x8d, 0x4c, 0x24, 0x04, 0x2b, 0xc8, 0x1b, 0xc0, 0xf7, 0xd0, 0x23, 0xc8, 0x8b, 0xc1,
        0x59, 0x94, 0x8b, 0x00, 0x89, 0x04, 0x24, 0xc3,
    ]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x401020).and_then(|f| f.name.as_deref()),
        Some("__chkstk")
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("(void *this)"), "{text}");
    assert!(text.contains("return *(uint32_t*)this;"), "{text}");
    assert!(text.contains("__chkstk(0x1000);"), "{text}");
}

/// The funclets a function's exception metadata describes belong to it.
///
/// They are named after it, left out of the function listing, and
/// decompiled on its frame, so a read of `[ebp-4]` is the parent's
/// `local_8`. The parent at 0x401000 takes the address of its handler
/// thunk at 0x401030, `mov eax, 0x402000; jmp 0x401040`, where 0x401040
/// jumps through the import slot of `__CxxFrameHandler3`; the `FuncInfo`
/// at 0x402000 has two unwind states, actions at 0x401050 and 0x401060,
/// and one try block with one catch clause at 0x401070.
#[test]
fn an_exception_funclet_belongs_to_its_parent() {
    use borer_engine::analysis::render::{FunctionOrder, functions_tsv};
    use borer_engine::analysis::{Funclet, FuncletRole};
    let mut p = funclet_image(&[0xff, 0x25, 0x00, 0x21, 0x40, 0x00]);
    p.symbols = vec![Symbol {
        name: "MSVCR100.dll!__CxxFrameHandler3".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let funclet = |va: u64| a.function(va).and_then(|f| f.funclet);
    assert_eq!(
        funclet(0x401050),
        Some(Funclet {
            parent: 0x401000,
            role: FuncletRole::Unwind(0)
        })
    );
    assert_eq!(
        funclet(0x401070),
        Some(Funclet {
            parent: 0x401000,
            role: FuncletRole::Catch(0, 0)
        })
    );
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401030).as_deref(), Some("sub_401000::__ehhandler"));
    assert_eq!(name(0x401050).as_deref(), Some("sub_401000::__unwind_0"));
    assert_eq!(name(0x401060).as_deref(), Some("sub_401000::__unwind_1"));
    assert_eq!(name(0x401070).as_deref(), Some("sub_401000::__catch_0_0"));
    let listing = functions_tsv(
        &a,
        &Overlay::default(),
        None,
        FunctionOrder::Address,
        0,
        100,
    )
    .2;
    assert!(
        listing.contains("4 exception funclets left out, filter=funclet lists them"),
        "{listing}"
    );
    assert!(!listing.contains("__unwind_0"), "{listing}");
    let text = decompile(&p, &a, &Overlay::default(), 0x401050).unwrap_or_default();
    assert!(
        text.contains("// note: the unwind action of state 0 of sub_401000;"),
        "{text}"
    );
    assert!(text.contains("return local_4;"), "{text}");
}

/// A function whose frame `__SEH_prolog4` builds still reads its arguments
/// through `ebp` and still saves its registers in its prologue.
///
/// The caller: `mov eax,0; call 0x401040; push ecx; push ebx; push esi;
/// push edi; mov eax,[ebp+8]; add eax,[ebp+0xc]; mov ecx,[ebp-0xc];
/// mov fs:[0],ecx; pop edi; pop esi; pop ebx; leave; ret 8`, with the helper
/// at 0x401040. The helper is named, its call is not rendered, `[ebp+8]` is
/// the first parameter, and the four pushes after it are register saves
/// rather than stores.
#[test]
fn seh_prolog_helper_builds_the_frame() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x51, 0x53, 0x56, 0x57, 0x8b,
        0x45, 0x08, 0x03, 0x45, 0x0c, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00,
        0x5f, 0x5e, 0x5b, 0xc9, 0xc2, 0x08, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let helper = a.function(0x401040).and_then(|f| f.name.as_deref());
    assert_eq!(helper, Some("__SEH_prolog4"));
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("return a1 + a2;"), "{text}");
    assert!(!text.contains("__SEH_prolog4("), "{text}");
    assert!(!text.contains("ebp->"), "{text}");
    assert!(!text.contains("= esi;"), "{text}");
}

/// The block after the frame helper's call starts with the handler
/// registered, so an argument pushed there reaches the call.
///
/// The caller: `mov eax,0; call 0x401040; push ecx; push 0x14; call
/// 0x401060; pop ecx; mov ecx,[ebp-0xc]; mov fs:[0],ecx; leave; ret`,
/// with the helper at 0x401040 and a callee reading one argument at
/// 0x401060. The `push ecx` makes room; the `push 0x14` is the argument.
#[test]
fn a_push_after_the_frame_helper_is_an_argument() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x51, 0x6a, 0x14, 0xe8, 0x4e,
        0x00, 0x00, 0x00, 0x59, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0xc9,
        0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let p = image(&code);
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401060(20)"), "{text}");
}

/// The prologue helper that pushes its handler's address before the head
/// of the handler chain builds the frame too.
///
/// Its caller's `[ebp+8]` is the argument its own callers push, and the
/// stack is known after it.
///
/// The caller at 0x401000: `push 0x14; call 0x401020; pop ecx; ret`; the
/// function at 0x401020: `push 0xc; push 0x402010; call 0x401060; push
/// dword [ebp+8]; call 0x401120; pop ecx; mov ecx,[ebp-0x10]; mov
/// fs:[0],ecx; pop ecx; pop edi; pop esi; pop ebx; leave; ret`, with the
/// helper at 0x401060 and `mov eax,[esp+4]; ret` at 0x401120. An operator
/// `new` wrapper of this shape, unread, took no argument, and each of its
/// callers called it with none; read, the frame the helper sized with
/// `sub esp, eax` lost the stack, and the push after it was no argument.
#[test]
fn a_prolog_helper_pushing_its_handler_builds_the_frame() {
    let mut code = vec![0x6a, 0x14, 0xe8, 0x19, 0x00, 0x00, 0x00, 0x59, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x6a, 0x0c, 0x68, 0x10, 0x20, 0x40, 0x00, 0xe8, 0x34, 0x00, 0x00, 0x00, 0xff, 0x75, 0x08,
        0xe8, 0xec, 0x00, 0x00, 0x00, 0x59, 0x8b, 0x4d, 0xf0, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00,
        0x00, 0x59, 0x5f, 0x5e, 0x5b, 0xc9, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4_HANDLER);
    code.resize(0x120, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let p = image_with_data(&code, &[0; 0x20]);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x401060).and_then(|f| f.name.as_deref()),
        Some("__SEH_prolog4")
    );
    let o = Overlay::default();
    let callee = decompile(&p, &a, &o, 0x401020).unwrap_or_default();
    assert!(callee.contains("sub_401020(uint32_t a1)"), "{callee}");
    assert!(callee.contains("return sub_401120(a1);"), "{callee}");
    assert!(!callee.contains("asm"), "{callee}");
    let caller = decompile(&p, &a, &o, 0x401000).unwrap_or_default();
    assert!(caller.contains("sub_401020(20)"), "{caller}");
}

/// A call to the epilogue helper right before `ret` is the return: the
/// helper is named, the call is not rendered, and `eax` survives it.
///
/// The caller: `mov eax,0; call 0x401040; push ebx; push esi; push edi;
/// mov eax,[ebp+8]; call 0x401060; ret`, with the prologue helper at
/// 0x401040 and the epilogue helper at 0x401060.
#[test]
fn seh_epilog_helper_is_the_return() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x53, 0x56, 0x57, 0x8b, 0x45,
        0x08, 0xe8, 0x4b, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&SEH_EPILOG4);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x401060).and_then(|f| f.name.as_deref()),
        Some("__SEH_epilog4")
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("return a1;"), "{text}");
    assert!(!text.contains("__SEH_epilog4("), "{text}");
}

/// The handler's bookkeeping in a function with a registered handler
/// renders as nothing: the try-level stores at `[ebp-4]` and the unlink of
/// `fs:[0]` before the return.
///
/// The caller of the helper: `mov eax,0; call 0x401040; mov dword
/// [ebp-4],0; mov eax,[ebp+8]; or dword [ebp-4],-1; mov ecx,[ebp-0xc];
/// mov fs:[0],ecx; leave; ret 4`.
#[test]
fn handler_bookkeeping_renders_as_nothing() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0xc7, 0x45, 0xfc, 0x00, 0x00,
        0x00, 0x00, 0x8b, 0x45, 0x08, 0x83, 0x4d, 0xfc, 0xff, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d,
        0x00, 0x00, 0x00, 0x00, 0xc9, 0xc2, 0x04, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    let p = image(&code);
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("return a1;"), "{text}");
    assert!(!text.contains("fs"), "{text}");
    assert!(!text.contains("= -1;"), "{text}");
    assert!(!text.contains("= 0;"), "{text}");
}

/// An inline handler prologue leaves nothing either: the head read from
/// `fs:[0]` and pushed, and the registration of the new record.
///
/// `push ebp; mov ebp,esp; push -1; push 0x401100; mov eax,fs:[0];
/// push eax; mov fs:[0],esp; mov eax,[ebp+8]; mov ecx,[ebp-0x10];
/// mov fs:[0],ecx; leave; ret 4`.
#[test]
fn an_inline_handler_prologue_renders_as_nothing() {
    let text = dc(&[
        0x55, 0x8b, 0xec, 0x6a, 0xff, 0x68, 0x00, 0x11, 0x40, 0x00, 0x64, 0xa1, 0x00, 0x00, 0x00,
        0x00, 0x50, 0x64, 0x89, 0x25, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x45, 0x08, 0x8b, 0x4d, 0xf0,
        0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0xc9, 0xc2, 0x04, 0x00,
    ]);
    assert!(text.contains("return a1;"), "{text}");
    assert!(!text.contains("fs"), "{text}");
}

/// A `__thiscall` callee whose frame a helper builds still takes `this`
/// at its call sites: the scan for the registers it reads goes on past
/// the helper's call.
///
/// The caller at 0x401000: `mov ecx,[esp+4]; call 0x401010; ret`. The
/// callee: `mov eax,0; call 0x401040; mov eax,ecx; mov ecx,[ebp-0xc];
/// mov fs:[0],ecx; leave; ret`, with `__SEH_prolog4` at 0x401040.
#[test]
fn a_helper_framed_callee_still_takes_this_at_its_call_sites() {
    let mut code = vec![0x8b, 0x4c, 0x24, 0x04, 0xe8, 0x07, 0x00, 0x00, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x26, 0x00, 0x00, 0x00, 0x8b, 0xc1, 0x8b, 0x4d, 0xf4,
        0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0xc9, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    let p = image(&code);
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401010(a1)"), "{text}");
}

/// A fragment with no prologue that restores `fs:[0]` before returning
/// is a handler function's tail, and the unlink renders as nothing there
/// too.
///
/// `mov eax,[ebp+8]; mov ecx,[ebp-0xc]; mov fs:[0],ecx; pop edi; leave; ret`.
#[test]
fn a_fragment_that_unlinks_the_handler_renders_no_unlink() {
    let text = dc(&[
        0x8b, 0x45, 0x08, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x5f, 0xc9,
        0xc3,
    ]);
    assert!(!text.contains("fs"), "{text}");
}

/// A jump made after the frame is torn down is a tail call, and its
/// target a function, even when nothing else names that target.
///
/// `push ebp; mov ebp,esp; pop ebp; jmp 0x401010`, with `mov eax,1; ret`
/// at 0x401010 reached by nothing else.
#[test]
fn a_jump_after_the_epilogue_is_a_tail_call() {
    let mut code = vec![0x55, 0x8b, 0xec, 0x5d, 0xe9, 0x07, 0x00, 0x00, 0x00];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401010).is_some(),
        "the jump target is not a function"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("sub_401010("), "{text}");
}

/// An `add esp, N` that cleans up after a call is not an epilogue: the
/// jump after it stays inside the function.
///
/// `push ebp; mov ebp,esp; push 1; call 0x401020; add esp,4; jmp L;
/// L: pop ebp; ret`, with `mov eax,[esp+4]; ret` at 0x401020.
#[test]
fn an_argument_cleanup_before_a_jump_is_not_an_epilogue() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x6a, 0x01, 0xe8, 0x16, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x04, 0xeb, 0x00,
        0x5d, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x40100f).is_none(),
        "the jump target was cut off as a function"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("sub_401020(1)"), "{text}");
}

/// A frame local below the saved frame pointer is a local.
///
/// `push ebp; mov ebp,esp; push ecx; mov dword [ebp-4],5; mov eax,[ebp-4];
/// leave; ret`: the slot is named by its distance below the entry stack
/// pointer, and its displacement reads as minus four, not as `0xfffffffc`.
#[test]
fn frame_locals_are_locals() {
    let text = dc(&[
        0x55, 0x8b, 0xec, 0x51, 0xc7, 0x45, 0xfc, 0x05, 0x00, 0x00, 0x00, 0x8b, 0x45, 0xfc, 0xc9,
        0xc3,
    ]);
    assert!(text.contains("return 5;"), "{text}");
    assert!(!text.contains("0xffff"), "{text}");
    assert!(!text.contains("arg_"), "{text}");
}

/// A `rep movsd` over the frame lands after the stores it overwrites, so
/// a slot read after the copy reads the copied bytes, not the zero stored
/// there first.
///
/// `sub esp,0x20; mov dword [esp+8],0; mov esi,[esp+0x24]; mov edi,esp;
/// mov ecx,8; rep movsd; mov eax,[esp+8]; add esp,0x20; ret`.
#[test]
fn a_rep_movs_over_the_frame_overwrites_pending_slots() {
    let text = dc(&[
        0x83, 0xec, 0x20, 0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x74, 0x24, 0x24,
        0x8b, 0xfc, 0xb9, 0x08, 0x00, 0x00, 0x00, 0xf3, 0xa5, 0x8b, 0x44, 0x24, 0x08, 0x83, 0xc4,
        0x20, 0xc3,
    ]);
    let copy = text.find("memcpy(&local_1c, a1, 32);").unwrap_or(0);
    let zero = text.find("local_14 = 0;").unwrap_or(usize::MAX);
    assert!(zero < copy, "{text}");
    assert!(text.contains("return local_14;"), "{text}");
    assert!(!text.contains("return 0;"), "{text}");
}

/// A write to `esp` in 64-bit code moves the stack pointer.
///
/// It zero-extends into `rsp`, so the tracked frame offset is lost and a
/// later stack read is a raw dereference, not the slot it was before the
/// write. `lea esp,[rcx]; mov rax,[rsp]; ret` in a 64-bit image: comparing
/// only the full register (`rsp`) would miss the `esp` write and read
/// `retaddr` at the stale offset.
#[test]
fn a_write_to_esp_in_64_bit_code_loses_the_frame() {
    let p = raw::image(
        Arch::X86_64,
        &[0x8d, 0x21, 0x48, 0x8b, 0x04, 0x24, 0xc3],
        &[],
    );
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("return *(uint64_t*)rsp;"), "{text}");
    assert!(!text.contains("retaddr"), "{text}");
}

/// The funclets of a frame handler linked into the program belong to it.
///
/// The handler is no import and has no name; the thunk is a handler's all
/// the same, since the record it hands over is a `FuncInfo` by its magic
/// number. The 32-bit client's unwind actions, read as functions of their
/// own, used the parent's `ebp` as a register nothing set.
#[test]
fn an_exception_funclet_of_a_linked_handler_belongs_to_its_parent() {
    use borer_engine::analysis::{Funclet, FuncletRole};
    let p = funclet_image(&[0x55, 0x8b, 0xec, 0x5d, 0xc3]); // ASM: push ebp; mov ebp,esp; pop ebp; ret
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x401050).and_then(|f| f.funclet),
        Some(Funclet {
            parent: 0x401000,
            role: FuncletRole::Unwind(0)
        })
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401050).unwrap_or_default();
    assert!(text.contains("return local_4;"), "{text}");
}

/// An unwinder that only puts the chain's head back registers no handler.
///
/// msvcrt's `_global_unwind2` reads `fs:[0]`, pushes the four arguments of
/// `RtlUnwind` and, after it, stores the head it read back to `fs:[0]`.
/// That store made the function a handler's, whose entry pushes are the
/// registration record and render as nothing: `RtlUnwind()` lost its
/// arguments, and the head was never read into `local_c`.
#[test]
fn an_unwinder_restoring_the_chain_head_registers_no_handler() {
    let code = [
        0x8b, 0xff, // ASM: mov edi, edi
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x51, 0x51, 0x53, 0x56, 0x57, // ASM: push ecx; push ecx; push ebx; push esi; push edi
        0x64, 0x8b, 0x35, 0x00, 0x00, 0x00, 0x00, // ASM: mov esi, fs:[0]
        0x89, 0x75, 0xf8, // ASM: mov [ebp-8], esi
        0xc7, 0x45, 0xfc, 0x2c, 0x10, 0x40, 0x00, // ASM: mov dword [ebp-4], 0x40102c
        0x6a, 0x00, // ASM: push 0
        0xff, 0x75, 0x0c, // ASM: push dword [ebp+0xc]
        0xff, 0x75, 0xfc, // ASM: push dword [ebp-4]
        0xff, 0x75, 0x08, // ASM: push dword [ebp+8]
        0xff, 0x15, 0x00, 0x20, 0x40, 0x00, // ASM: call [0x402000] (RtlUnwind)
        0x8b, 0x45, 0x0c, // ASM: mov eax, [ebp+0xc]
        0x8b, 0x40, 0x04, // ASM: mov eax, [eax+4]
        0x83, 0xe0, 0xfd, // ASM: and eax, -3
        0x8b, 0x4d, 0x0c, // ASM: mov ecx, [ebp+0xc]
        0x89, 0x41, 0x04, // ASM: mov [ecx+4], eax
        0x64, 0x8b, 0x3d, 0x00, 0x00, 0x00, 0x00, // ASM: mov edi, fs:[0]
        0x8b, 0x5d, 0xf8, // ASM: mov ebx, [ebp-8]
        0x89, 0x3b, // ASM: mov [ebx], edi
        0x64, 0x89, 0x1d, 0x00, 0x00, 0x00, 0x00, // ASM: mov fs:[0], ebx
        0x5f, 0x5e, 0x5b, // ASM: pop edi; pop esi; pop ebx
        0xc9, // ASM: leave
        0xc2, 0x08, 0x00, // ASM: ret 8
    ];
    let text = dc_with(&code, &[(0x402000, "RtlUnwind")]);
    assert!(
        text.contains("RtlUnwind(a1, 0x40102c, a2, NULL);"),
        "{text}"
    );
    assert!(
        text.contains("local_8 = NtCurrentTeb()->NtTib.ExceptionList;"),
        "{text}"
    );
}

/// A push, a pop and a `leave` under a 66h prefix move the stack two
/// bytes, in the lifter as in the emulator.
///
/// Two word pushes fill the dword `pop eax` takes, 7 in its upper word, so
/// the function returns 0x70000; `pop dx` takes the low word of a pushed
/// dword, and `leave` pops `bp` alone from its high word, which puts the
/// stack pointer back at the entry for the `ret`. Moving the mode's word
/// each, both sides read 0 for `eax` and agreed on it.
#[test]
fn push_word_agrees_with_the_emulator() {
    let code = [
        0x66, 0x6a, 0x07, // ASM: push word 7
        0x66, 0x6a, 0x00, // ASM: push word 0
        0x58, // ASM: pop eax
        0x6a, 0x05, // ASM: push 5
        0x66, 0x5a, // ASM: pop dx
        0x8b, 0xec, // ASM: mov ebp, esp
        0x66, 0xc9, // ASM: leave (word)
        0xc3, // ASM: ret
    ];
    let text = dc(&code);
    assert!(text.contains("return 0x70000;"), "{text}");
    agrees_with_the_emulator(&code);
}

/// A push, a pop and a `leave` under a 66h prefix move the stack two
/// bytes in 64-bit code too, in the lifter as in the emulator.
///
/// `push ax` and a word push of 7 come back as `pop ax` and `pop cx`, a
/// word each; a word push of 9 is then the `bp` that `leave` pops after
/// setting `rsp` from `rbp` whole, which puts the stack pointer back at
/// the entry for the `ret`. Moving the mode's eight bytes each, the lifter
/// held quadword slots the machine never wrote and `leave` set all of
/// `rbp`.
#[test]
fn push_word_agrees_with_the_emulator_in_64_bit_code() {
    agrees_with_the_emulator_64(&[
        0x66, 0x50, // ASM: push ax
        0x66, 0x6a, 0x07, // ASM: push word 7
        0x66, 0x58, // ASM: pop ax
        0x66, 0x59, // ASM: pop cx
        0x66, 0x6a, 0x09, // ASM: push word 9
        0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        0x66, 0xc9, // ASM: leave (word)
        0xc3, // ASM: ret
    ]);
}

/// Two 16-bit pushes fill one 32-bit calling-convention word, so an unknown
/// indirect callee takes one stack argument rather than reading past the
/// pushed bytes or popping eight bytes from `esp`.
#[test]
fn two_word_pushes_count_as_one_stack_word_for_an_unknown_callee() {
    let text = dc(&[
        0x66, 0x6a, 0x07, // ASM: push word 7
        0x66, 0x6a, 0x03, // ASM: push word 3
        0xff, 0xd2, // ASM: call edx
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp + 4]
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("edx(0x70003);"), "{text}");
    assert!(text.contains("return arg_0;"), "{text}");
}
