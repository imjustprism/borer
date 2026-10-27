//! Calls through COM interfaces decompile as the interface's methods once
//! the code shows which interface an object is, and as vtable slots when
//! nothing does.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::program::{Arch, BinaryFormat, Program, Symbol, SymbolKind};

use crate::decompiled::decompiled;

/// `IID_IDirectInput8A` as a binary holds it, at 0x402100.
const IID_DIRECTINPUT8A: [u8; 16] = [
    0x30, 0x80, 0x79, 0xbf, 0x3a, 0x48, 0xa2, 0x4d, 0xaa, 0x99, 0x5d, 0x64, 0xed, 0x36, 0x97, 0x00,
];

/// A 32-bit PE image of `code` at 0x401000 importing `Direct3DCreate9`
/// at 0x402000 and `DirectInput8Create` at 0x402004, with
/// `IID_IDirectInput8A` at 0x402100.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn image(code: &[u8]) -> Program {
    let mut data = vec![0u8; 0x110];
    data[0x100..].copy_from_slice(&IID_DIRECTINPUT8A);
    let mut p = crate::raw::image(Arch::X86, code, &data);
    p.format = BinaryFormat::Pe;
    p.symbols = [
        ("d3d9.dll!Direct3DCreate9", 0x402000),
        ("DINPUT8.dll!DirectInput8Create", 0x402004),
    ]
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Import,
    })
    .to_vec();
    p
}

/// A D3D9 device's calls read as its methods.
///
/// The object `Direct3DCreate9` returns is an `IDirect3D9`, whose slot 16
/// is `CreateDevice`; the local `CreateDevice` writes through its last
/// parameter is an `IDirect3DDevice9`, whose slot 41 is `BeginScene`.
#[test]
fn a_d3d9_device_calls_its_methods_by_name() {
    let code = [
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp,esp
        0x83, 0xec, 0x08, // ASM: sub esp,8
        0x6a, 0x20, // ASM: push 0x20
        0xff, 0x15, 0x00, 0x20, 0x40, 0x00, // ASM: call [Direct3DCreate9]
        0x89, 0x45, 0xfc, // ASM: mov [ebp-4],eax
        0x8d, 0x4d, 0xf8, // ASM: lea ecx,[ebp-8]
        0x51, // ASM: push ecx
        0x6a, 0x00, // ASM: push 0
        0x6a, 0x20, // ASM: push 0x20
        0x6a, 0x00, // ASM: push 0
        0x6a, 0x01, // ASM: push 1
        0x6a, 0x00, // ASM: push 0
        0x8b, 0x10, // ASM: mov edx,[eax]
        0x50, // ASM: push eax
        0xff, 0x52, 0x40, // ASM: call [edx+0x40]
        0x8b, 0x45, 0xf8, // ASM: mov eax,[ebp-8]
        0x8b, 0x08, // ASM: mov ecx,[eax]
        0x50, // ASM: push eax
        0xff, 0x91, 0xa4, 0x00, 0x00, 0x00, // ASM: call [ecx+0xa4]
        0x8b, 0xe5, // ASM: mov esp,ebp
        0x5d, // ASM: pop ebp
        0xc3, // ASM: ret
    ];
    let text = decompiled(&image(&code), 0x401000);
    assert!(
        text.contains("->CreateDevice(0, 1, 0, 32, 0, &local_c)"),
        "{text}"
    );
    assert!(text.contains("IDirect3DDevice9 *local_c"), "{text}");
    assert!(text.contains("->BeginScene()"), "{text}");
    assert!(!text.contains("vtable["), "{text}");
}

/// Decompiles `DirectInput8Create(0, 0x800, &IID_IDirectInput8A, &p, 0)`,
/// then `between`, then `p->vtable[2]()`.
///
/// # Arguments
///
/// * `between` - Instructions between the creator and the call.
fn dinput(between: &[u8]) -> String {
    let mut code = vec![
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp,esp
        0x51, // ASM: push ecx
        0x6a, 0x00, // ASM: push 0
        0x8d, 0x45, 0xfc, // ASM: lea eax,[ebp-4]
        0x50, // ASM: push eax
        0x68, 0x00, 0x21, 0x40, 0x00, // ASM: push 0x402100
        0x68, 0x00, 0x08, 0x00, 0x00, // ASM: push 0x800
        0x6a, 0x00, // ASM: push 0
        0xff, 0x15, 0x04, 0x20, 0x40, 0x00, // ASM: call [DirectInput8Create]
    ];
    code.extend_from_slice(between);
    code.extend_from_slice(&[
        0x8b, 0x45, 0xfc, // ASM: mov eax,[ebp-4]
        0x8b, 0x08, // ASM: mov ecx,[eax]
        0x50, // ASM: push eax
        0xff, 0x51, 0x08, // ASM: call [ecx+8]
        0x8b, 0xe5, // ASM: mov esp,ebp
        0x5d, // ASM: pop ebp
        0xc3, // ASM: ret
    ]);
    decompiled(&image(&code), 0x401000)
}

/// `DirectInput8Create` hands back the interface its IID argument names:
/// `IID_IDirectInput8A`, whose slot 2 is `Release`.
#[test]
fn an_iid_names_the_interface_a_creator_hands_back() {
    let text = dinput(&[]);
    assert!(text.contains("->Release()"), "{text}");
    assert!(text.contains("IDirectInput8A *local_8"), "{text}");
}

/// A call is named before it retypes its receiver's own local.
///
/// `IDirectInput8A::CreateDevice` in slot 3 hands its device back into
/// the local it was called through, and the next call is
/// `IDirectInputDevice8A::Release`. A local two interfaces share is
/// declared as neither.
#[test]
fn a_call_is_named_before_it_retypes_its_receiver() {
    let text = dinput(&[
        0x6a, 0x00, // ASM: push 0
        0x8d, 0x45, 0xfc, // ASM: lea eax,[ebp-4]
        0x50, // ASM: push eax
        0x68, 0x00, 0x21, 0x40, 0x00, // ASM: push 0x402100
        0x8b, 0x45, 0xfc, // ASM: mov eax,[ebp-4]
        0x8b, 0x08, // ASM: mov ecx,[eax]
        0x50, // ASM: push eax
        0xff, 0x51, 0x0c, // ASM: call [ecx+0xc]
    ]);
    assert!(
        text.contains("->CreateDevice(0x402100, &local_8, 0)"),
        "{text}"
    );
    assert!(text.contains("uint32_t local_8"), "{text}");
    assert!(text.contains("->Release()"), "{text}");
}

/// A local the creator filled may hold anything once the code stores to
/// it, a call takes its address for no out-parameter of an interface, or
/// a string store fills it: its call keeps the vtable slot.
#[test]
fn an_overwritten_local_loses_its_interface() {
    let stored = [
        0x8b, 0x45, 0x08, // ASM: mov eax,[ebp+8]
        0x89, 0x45, 0xfc, // ASM: mov [ebp-4],eax
    ];
    let passed = [
        0x8d, 0x45, 0xfc, // ASM: lea eax,[ebp-4]
        0x50, // ASM: push eax
        0xff, 0x15, 0x00, 0x20, 0x40, 0x00, // ASM: call [Direct3DCreate9]
    ];
    let filled = [
        0x8d, 0x7d, 0xfc, // ASM: lea edi,[ebp-4]
        0x33, 0xc0, // ASM: xor eax,eax
        0xb9, 0x01, 0x00, 0x00, 0x00, // ASM: mov ecx,1
        0xf3, 0xab, // ASM: rep stosd
    ];
    for between in [&stored[..], &passed[..], &filled[..]] {
        let text = dinput(between);
        assert!(text.contains("vtable[2]"), "{text}");
        assert!(
            !text.contains("Release") && !text.contains("IDirectInput8A"),
            "{text}"
        );
    }
}

/// An object nothing shows the interface of keeps its vtable slot.
#[test]
fn an_object_of_no_known_interface_keeps_its_slot() {
    let code = [
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0x8b, 0x08, // ASM: mov ecx,[eax]
        0x50, // ASM: push eax
        0xff, 0x51, 0x08, // ASM: call [ecx+8]
        0xc3, // ASM: ret
    ];
    let text = decompiled(&image(&code), 0x401000);
    assert!(text.contains("vtable[2]"), "{text}");
    assert!(!text.contains("Release"), "{text}");
}

/// On x64 an IID types the local a creator hands its object back through.
///
/// `CreateDXGIFactory` hands back the `IDXGIFactory` its IID names, whose
/// slot 7 is `EnumAdapters`, though the local's address also sits in
/// `r8`, an argument register the callee does not read.
#[test]
fn an_x64_creator_types_its_local_through_the_iid() {
    let code = [
        0x48, 0x83, 0xec, 0x38, // ASM: sub rsp,0x38
        0x4c, 0x8d, 0x44, 0x24, 0x28, // ASM: lea r8,[rsp+0x28]
        0x4c, 0x89, 0xc2, // ASM: mov rdx,r8
        0x48, 0x8d, 0x0d, 0xfd, 0x0f, 0x00, 0x00, // ASM: lea rcx,[IID_IDXGIFactory]
        0xff, 0x15, 0xe7, 0x0f, 0x00, 0x00, // ASM: call [CreateDXGIFactory]
        0x48, 0x8b, 0x4c, 0x24, 0x28, // ASM: mov rcx,[rsp+0x28]
        0x48, 0x8b, 0x01, // ASM: mov rax,[rcx]
        0xff, 0x50, 0x38, // ASM: call [rax+0x38]
        0x48, 0x83, 0xc4, 0x38, // ASM: add rsp,0x38
        0xc3, // ASM: ret
    ];
    let mut data = vec![0u8; 0x10];
    data.extend_from_slice(&[
        0xec, 0x66, 0x71, 0x7b, 0xc7, 0x21, 0xae, 0x44, 0xb2, 0x1a, 0xc9, 0xae, 0x32, 0x1a, 0xe3,
        0x69,
    ]);
    let mut p = crate::decompiled::program64_with_data(&code, &data);
    p.symbols = vec![Symbol {
        name: "dxgi.dll!CreateDXGIFactory".to_owned(),
        addr: 0x1_4000_2000,
        kind: SymbolKind::Import,
    }];
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("->EnumAdapters("), "{text}");
    assert!(text.contains("IDXGIFactory *"), "{text}");
}
