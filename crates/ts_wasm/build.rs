//! Link settings of the wasm module. They are here, not in RUSTFLAGS, so
//! every build of the module gets them (scripts/run-cargo-capped.sh sets
//! RUSTFLAGS, which replaces target rustflags).

fn main() {
    if std::env::var("CARGO_CFG_TARGET_FAMILY").as_deref() == Ok("wasm") {
        // The shadow stack in linear memory: 32 MiB. Native runs the
        // checker on threads with 16 MiB to 1 GiB of stack
        // (gostd/stack.rs); the wasm shadow stack holds only the locals
        // whose address is taken, so it needs less. The stack is first in
        // memory, so an overflow traps and does not corrupt data.
        println!("cargo:rustc-cdylib-link-arg=-zstack-size=33554432");
    }
}
