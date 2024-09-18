# embedded-io-extras

`embedded-io-extras` is a `no_std` compatible library providing additional utilities, 
including a `Cursor` type. It functions like `std::io::Cursor` but is tailored for environments without 
standard libraries. This crate complements [`embedded-io`](https://crates.io/crates/embedded-io).

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
embedded-io-extras = "0.0.2"
```

and for `no_std` environments:

```toml
[dependencies]
embedded-io-extras = { version = "0.0.2", default-features = false, features = ["alloc"] }
```

- **`std`**: Enable this feature to use `std` with `embedded-io`. Enabled by default.
- **`alloc`**: Enable this feature to support dynamic memory allocation with `embedded-io`. Enabled by default.

## Examples

```rust
use embedded_io_extras::{Cursor, Write};

fn main() {
    let mut cur = Cursor::new(Vec::new());
    assert_eq!(cur.write(&[1, 2, 3]).unwrap(), 3);
    assert_eq!(cur.position(), 3);
    assert_eq!(cur.get_ref(), &vec![1, 2, 3]);
}
```

## License

This project is licensed under the MIT License.
