//! Reads arbitrary bytes as a CIL method body and decodes its code: the
//! header and exception clauses of ECMA-335 II.25.4 and the instructions
//! of Partition III. Any input may be refused; none may panic or hang.

#![no_main]

use borer_engine::clr::il;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok((_, code)) = il::body(data) {
        _ = il::decode(code);
    }
    _ = il::decode(data);
});
