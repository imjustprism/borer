//! Ground-truth crackme for the decompiler fidelity test.
//!
//! A real compiler-emitted serial check that the test suite locates by its
//! final-comparison constant and verifies structurally after decompilation.

#![expect(
    unsafe_code,
    reason = "`#[unsafe(no_mangle)]` keeps the checked function findable by name"
)]

/// Marker string the check mixes into the accumulator.
const MARKER: &str = "BORER-CRACKME-MARKER";

/// Validates a serial: eight rotate-xor rounds over the key, compared to a constant.
///
/// # Arguments
///
/// * `key` - The serial under test.
///
/// # Returns
///
/// `1` when the key passes, else `0`.
#[unsafe(no_mangle)]
#[expect(
    clippy::cast_possible_truncation,
    reason = "`i` is below eight, so the rotate count and the index both fit; a helper call would change the compiled shape the ground-truth test decompiles"
)]
fn check_serial(key: u64) -> u64 {
    let m = std::hint::black_box(MARKER).as_bytes();
    let mut acc: u64 = 0x9E3779B9_7F4A7C15;
    for i in 0..8u64 {
        acc ^= key.wrapping_add(i).rotate_left((i * 4) as u32) ^ u64::from(m[i as usize]);
    }
    u64::from(acc == 0xDEAD_BEEF)
}

/// Checks the serial given as the first argument (default `0`) and prints the verdict.
fn main() {
    let key = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    println!("check_serial({key:#x}) = {}", check_serial(key));
}
