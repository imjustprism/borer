//! Parses arbitrary bytes as a project file and, when its overlay loads,
//! decompiles a small program's function under it, writes the program's
//! ReClass.NET project under it, and reads its first comment as C
//! declarations over its types: the path a project file someone else
//! wrote takes. Any input may be refused; none may panic, hang or exhaust
//! memory.

#![no_main]

use borer_engine::analysis::Analysis;
use borer_engine::analysis::cdecl::{self, Abi};
use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::modsdk::{self, reclass};
use borer_engine::analysis::project::Project;
use borer_engine::program::{Arch, Program, Section};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(project) = serde_json::from_slice::<Project>(data) else {
        return;
    };
    let Ok(overlay) = project.to_overlay() else {
        return;
    };
    let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
    let mut code = vec![0xcc; 0x10];
    // ASM: mov eax, 1; ret
    code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
    let analysis = Analysis::compute(&program);
    _ = decompile(&program, &analysis, &overlay, 0x1000);
    _ = reclass::reclass(&modsdk::build(&program, &analysis, &overlay));
    if let Some(declared) = project.comments.values().next() {
        let abi = Abi {
            word: 8,
            windows: true,
        };
        _ = cdecl::parse(declared, &overlay.types, abi);
    }
});
