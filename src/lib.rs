pub mod data;
pub mod float;
pub mod heap;
pub mod vm;
use wasm_bindgen::prelude::*;

// This could work with a function or two already designed to interpret things,
// just with a different IO strategy.
// Also, first it needs a class to compile some ASM to bytes.
#[wasm_bindgen]
pub fn web_interpret(s: &str) {
    // take a string
    // compile it to bytes
    // run the bytes on the vm
    // // note that we need to setup an input and output that
    // // can properly be used to give the results and take input
}
