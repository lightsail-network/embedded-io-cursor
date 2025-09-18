# embedded-io-cursor

[![Crates.io](https://img.shields.io/crates/v/embedded-io-cursor)](https://crates.io/crates/embedded-io-cursor)
[![docs.rs](https://docs.rs/embedded-io-cursor/badge.svg)](https://docs.rs/embedded-io-cursor)
[![CI](https://github.com/lightsail-network/embedded-io-cursor/workflows/CI/badge.svg)](https://github.com/lightsail-network/embedded-io-cursor/actions)

A `no_std`-compatible Cursor implementation designed for use with `embedded-io`.

This crate provides a `Cursor` type that wraps an in-memory buffer and provides `Read`, `Write`, `Seek`, and `BufRead` implementations using the `embedded-io` traits. Unlike the standard library's `Cursor`, this implementation works in `no_std` environments while maintaining API compatibility where possible.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
embedded-io-cursor = "0.1.0"
```

### Basic Usage

```rust
use embedded_io::{Read, Write, Seek, SeekFrom};
use embedded_io_cursor::Cursor;

// Reading from a static buffer
let mut cursor = Cursor::new(&b"hello world"[..]);
let mut buf = [0u8; 5];
cursor.read_exact(&mut buf).unwrap();
assert_eq!(&buf, b"hello");

// Writing to a mutable buffer
let mut buffer = [0u8; 10];
{
    use embedded_io::Write;
    let mut cursor = Cursor::new(&mut buffer[..]);
    let data = b"test";
    let mut written = 0;
    while written < data.len() {
        written += cursor.write(&data[written..]).unwrap();
    }
}
assert_eq!(&buffer[..4], b"test");
```

### With `alloc` feature (requires `alloc` feature to be enabled)

```rust
# #[cfg(feature = "alloc")] {
use embedded_io::Write;
use embedded_io_cursor::Cursor;
extern crate alloc;
use alloc::vec::Vec;

let mut vec = Vec::new();
let mut cursor = Cursor::new(&mut vec);
let data = b"hello world";
let mut written = 0;
while written < data.len() {
    written += cursor.write(&data[written..]).unwrap();
}
assert_eq!(vec, b"hello world");
# }
```

## Features

- `default`: No additional features enabled
- `std`: Enable standard library support (implies `alloc`)
- `alloc`: Enable support for `Vec<u8>` and `Box<[u8]>`
- `defmt`: Enable `defmt` formatting support

## Differences from `std::io::Cursor`

This implementation maintains API compatibility with `std::io::Cursor` where possible, but has some key differences:

1. **Uses `embedded-io` traits**: Instead of `std::io` traits, this uses the `embedded-io` equivalents
2. **Full `BufRead` support**: Implements `embedded-io::BufRead` with `fill_buf()` and `consume()`
3. **Limited buffer types in `no_std`**: Without `alloc`, only basic slice types are supported
4. **Error type**: Uses `embedded_io::ErrorKind` instead of `std::io::Error`

## Testing

Run tests with:

```bash
cargo test                           # All tests (includes doctests)
cargo test --no-default-features     # no_std tests only
cargo test --features alloc          # With alloc support
cargo test --features std            # With std support
cargo test --lib --tests             # Unit and integration tests only
```

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
