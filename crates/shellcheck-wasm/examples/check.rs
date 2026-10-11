//! Native counterpart of the WASM ABI for cross-runtime parity tests.
use std::io::{self, Read, Write};

fn main() -> io::Result<()> {
    let mut input = Vec::new();
    io::stdin().read_to_end(&mut input)?;
    io::stdout().write_all(&shellcheck_wasm::check_json(&input))
}
