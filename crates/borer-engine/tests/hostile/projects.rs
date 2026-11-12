//! Project files built in memory, as a hand-edited one arrives: each is
//! refused, or loads and is read, in bounded time and memory.

use std::collections::BTreeMap;
use std::sync::mpsc;
use std::time::Duration;

use borer_engine::analysis::cdecl::{self, Abi};
use borer_engine::analysis::modsdk::{self, reclass};
use borer_engine::analysis::project::Project;
use borer_engine::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section};

/// Windows x64, the layout a declaration is read by here.
const X64: Abi = Abi {
    word: 8,
    windows: true,
};

/// Runs `work` on a thread of its own, so work that does not end fails the
/// test instead of hanging it.
///
/// # Arguments
///
/// * `work` - The work.
///
/// # Returns
///
/// What the work returned.
///
/// # Panics
///
/// When the work takes over ten seconds.
fn in_time<T: Send + 'static>(work: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || tx.send(work()));
    rx.recv_timeout(Duration::from_secs(10))
        .expect("the work ends within ten seconds")
}

/// Returns typedefs `A0` to `A4094`, each naming the next, the last a
/// `u32`.
fn chain() -> BTreeMap<String, UserType> {
    (0..4095)
        .map(|k| {
            let next = match k {
                4094 => TypeExpr::U32,
                _ => TypeExpr::Named(format!("A{}", k + 1)),
            };
            (format!("A{k}"), UserType::Alias(next))
        })
        .collect()
}

/// Returns a struct of 256 fields of one type, a field every `stride`
/// bytes.
///
/// # Arguments
///
/// * `ty` - The fields' type.
/// * `stride` - Bytes from one field to the next.
fn of_256(ty: &TypeExpr, stride: u64) -> UserType {
    let fields = (0..256u64)
        .map(|k| {
            let name = format!("f{k}");
            (
                k * stride,
                UserField {
                    name,
                    ty: ty.clone(),
                },
            )
        })
        .collect();
    UserType::Struct(UserStruct {
        size: 256 * stride,
        fields,
    })
}

/// A project of a million fields stated of one class, or of 4096 classes
/// of 256 fields, each typed by the first of 4095 typedefs, is refused by
/// its count or its chain before any field is sized.
///
/// Each field was sized down the whole chain before any count was read:
/// hours a load.
#[test]
fn a_project_of_a_million_fields_typed_down_a_chain_is_refused() {
    let _guard = super::serial();
    let typed = |k: u64| (format!("{:#x}", k * 4), format!("m_{k} A0"));
    let class: BTreeMap<String, String> = (0..1_000_000).map(typed).collect();
    let one = Project {
        types: chain(),
        fields: [("C".to_owned(), class)].into(),
        ..Project::default()
    };
    let refused = in_time(move || one.to_overlay()).expect_err("a million fields loaded");
    assert!(
        refused.contains("class C would state 1000000 fields"),
        "{refused}"
    );
    let classes = (0..4096)
        .map(|c| (format!("C{c}"), (0..256).map(typed).collect()))
        .collect();
    let many = Project {
        types: chain(),
        fields: classes,
        ..Project::default()
    };
    let refused = in_time(move || many.to_overlay()).expect_err("4095 typedefs loaded");
    assert!(
        refused.contains("typedef 'A0' starts a chain of 4095 typedefs"),
        "{refused}"
    );
}

/// A project's struct holding itself by value is refused, and a
/// declaration over it, read where no check came first, ends.
///
/// A struct of three fields of its own type was aligned by walking each
/// field to a depth cap: `3^33` steps.
#[test]
fn a_struct_holding_itself_is_refused_and_a_declaration_over_it_ends() {
    let held = UserStruct {
        size: 24,
        fields: (0..3u64)
            .map(|k| {
                let ty = TypeExpr::Named("A".to_owned());
                (
                    k * 8,
                    UserField {
                        name: format!("f{k}"),
                        ty,
                    },
                )
            })
            .collect(),
    };
    let types: BTreeMap<String, UserType> = [("A".to_owned(), UserType::Struct(held))].into();
    let project = Project {
        types: types.clone(),
        ..Project::default()
    };
    let refused = project.to_overlay().expect_err("A holds itself");
    assert!(
        refused.contains("holds itself by value (A -> A)"),
        "{refused}"
    );
    assert!(in_time(move || cdecl::parse(
        "struct B { A x; };",
        &types,
        X64
    )
    .is_ok()));
}

/// A project of seven structs, each holding the next 256 times, loads,
/// and a declaration embedding the first is read in bounded time.
///
/// Its alignment walked every field of every level below it: `256^7`
/// steps.
#[test]
fn a_declaration_over_a_project_of_deep_structs_ends() {
    let types = (0..7u32)
        .map(|k| {
            let ty = match k {
                6 => TypeExpr::U8,
                _ => TypeExpr::Named(format!("S{}", k + 1)),
            };
            (format!("S{k}"), of_256(&ty, 256u64.pow(6 - k)))
        })
        .collect();
    let project = Project {
        types,
        ..Project::default()
    };
    let overlay: Overlay = project.to_overlay().expect("a chain of structs loads");
    let read = in_time(move || {
        cdecl::parse("struct B { S0 x; };", &overlay.types, X64).map(|d| d.types.len())
    });
    assert_eq!(read.ok(), Some(1));
}

/// A project's struct of 256 arrays of 64 KiB loads and writes a small
/// ReClass.NET project, holding little heap while it does.
///
/// Each array was 8192 hex nodes: 128 MiB of XML, and a zip as large again.
#[test]
fn a_project_of_large_arrays_writes_a_small_reclass_project() {
    let _guard = super::serial();
    let big = of_256(&TypeExpr::Array(Box::new(TypeExpr::U8), 0x1_0000), 0x1_0000);
    let project = Project {
        types: [("Big".to_owned(), big)].into(),
        ..Project::default()
    };
    let overlay = project.to_overlay().expect("a struct of arrays loads");
    let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
    let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
    let a = Analysis::compute(&p);
    let (file, peak) = super::measured(|| reclass::reclass(&modsdk::build(&p, &a, &overlay)));
    assert!(file.is_ok_and(|f| f.len() < 1 << 16));
    assert!(peak < 1 << 24, "{peak} bytes at the peak");
}
