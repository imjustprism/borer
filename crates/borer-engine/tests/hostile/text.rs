//! Text passes over hostile decompiled text stay bounded.

use super::serial;

/// Polishes a function's text, requiring it to take under two seconds.
///
/// # Arguments
///
/// * `text` - The function's text.
///
/// # Returns
///
/// The polished text.
///
/// # Panics
///
/// When the polish takes two seconds or more.
fn polished_quickly(text: &str) -> String {
    #[expect(
        clippy::disallowed_methods,
        reason = "the test bounds the time a hostile text takes"
    )]
    let started = std::time::Instant::now();
    let out =
        borer_engine::analysis::decompile::polish(text, 64, &borer_engine::pack::Packs::default());
    let took = started.elapsed();
    assert!(
        took < std::time::Duration::from_secs(2),
        "the polish took {took:?}"
    );
    out
}

/// Returns a guarded loop whose inits after `var1 = a1;` are `chain`,
/// testing `last`.
///
/// # Arguments
///
/// * `chain` - The init lines.
/// * `last` - The variable the loop tests.
fn guarded(chain: &str, last: &str) -> String {
    format!(
        "uint64_t f(uint64_t a1)\n{{\n  uint64_t var1;\n  if (a1 != 0) {{\n    var1 = a1;\n{chain}    do {{\n      sub_1();\n    }} while ({last} != 0);\n  }}\n  return 0;\n}}\n"
    )
}

/// A guarded loop whose inits each square the one before decides nothing
/// in bounded time: the run is past its cap.
#[test]
fn a_chain_of_squared_inits_is_refused_quickly() {
    let _serial = serial();
    let chain: String = (2..=40)
        .map(|n| format!("    var{n} = var{} * var{};\n", n - 1, n - 1))
        .collect();
    assert!(polished_quickly(&guarded(&chain, "var40")).contains("do {"));
}

/// A run just under the cap whose every init reads the one before twice,
/// widened, finishes fast: a widened sum is one atom, not a copy of the
/// form it widens.
#[test]
fn a_chain_of_widened_inits_is_decided_quickly() {
    let _serial = serial();
    let chain: String = (2..=15)
        .map(|n| {
            let w = format!("(uint64_t)(uint32_t)(var{} + 1)", n - 1);
            format!("    var{n} = {w} + {w};\n")
        })
        .collect();
    assert!(polished_quickly(&guarded(&chain, "var15")).contains("do {"));
}
