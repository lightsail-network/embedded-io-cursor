//! Write operation tests
//!
//! Tests for Write trait implementations across different buffer types.

use embedded_io::{Read, Write};
use embedded_io_cursor::Cursor;

// =============================================================================
// Slice Write Tests
// =============================================================================

#[test]
fn test_write_to_slice() {
    let mut buffer = [0u8; 10];
    let mut cursor = Cursor::new(&mut buffer[..]);

    let n = cursor.write(b"hello").unwrap();
    assert_eq!(n, 5);
    assert_eq!(cursor.position(), 5);
    assert_eq!(&buffer[..5], b"hello");
}

#[test]
fn test_write_partial() {
    let mut buffer = [0u8; 3];
    let mut cursor = Cursor::new(&mut buffer[..]);

    let n = cursor.write(b"hello").unwrap();
    assert_eq!(n, 3);
    assert_eq!(cursor.position(), 3);
    assert_eq!(&buffer, b"hel");
}

#[test]
fn test_write_to_full_buffer() {
    let mut buffer = [0u8; 3];
    let mut cursor = Cursor::new(&mut buffer[..]);

    // Fill buffer
    cursor.write(b"abc").unwrap();
    assert_eq!(cursor.position(), 3);

    // Try to write more - should return WriteZero error per embedded-io spec
    let result = cursor.write(b"def");
    assert!(matches!(result, Err(embedded_io::ErrorKind::WriteZero)));
    assert_eq!(cursor.position(), 3);
    assert_eq!(&buffer, b"abc");
}

#[test]
fn test_write_at_exact_end() {
    let mut buffer = [0u8; 5];
    let mut cursor = Cursor::new(&mut buffer[..]);
    cursor.set_position(5);

    let result = cursor.write(b"test");
    assert!(matches!(result, Err(embedded_io::ErrorKind::WriteZero)));
    assert_eq!(cursor.position(), 5);
}

#[test]
fn test_write_beyond_end() {
    let mut buffer = [0u8; 5];
    let mut cursor = Cursor::new(&mut buffer[..]);
    cursor.set_position(10);

    let result = cursor.write(b"test");
    assert!(matches!(result, Err(embedded_io::ErrorKind::WriteZero)));
    assert_eq!(cursor.position(), 10);
}

#[test]
fn test_flush() {
    let mut buffer = [0u8; 5];
    let mut cursor = Cursor::new(&mut buffer[..]);

    cursor.write(b"test").unwrap();
    cursor.flush().unwrap(); // Should not fail
}

// =============================================================================
// Array Write Tests
// =============================================================================

#[test]
fn test_write_to_array() {
    let buffer = [0u8; 10];
    let mut cursor = Cursor::new(buffer);

    let n = cursor.write(b"hello").unwrap();
    assert_eq!(n, 5);
    assert_eq!(cursor.position(), 5);
    assert_eq!(&cursor.into_inner()[..5], b"hello");
}

#[test]
fn test_write_to_array_ref() {
    let mut buffer = [0u8; 10];
    let mut cursor = Cursor::new(&mut buffer);

    let n = cursor.write(b"hello").unwrap();
    assert_eq!(n, 5);
    assert_eq!(cursor.position(), 5);
    assert_eq!(&buffer[..5], b"hello");
}

// =============================================================================
// Vec Write Tests (requires alloc feature)
// =============================================================================

#[cfg(feature = "alloc")]
mod vec_tests {
    extern crate alloc;
    use super::*;
    use alloc::vec::Vec;

    #[test]
    fn test_write_to_vec() {
        let mut vec = Vec::new();
        let mut cursor = Cursor::new(&mut vec);

        let n = cursor.write(b"hello").unwrap();
        assert_eq!(n, 5);
        assert_eq!(cursor.position(), 5);
        assert_eq!(vec, b"hello");
    }

    #[test]
    fn test_write_to_owned_vec() {
        let vec = Vec::new();
        let mut cursor = Cursor::new(vec);

        let n = cursor.write(b"hello").unwrap();
        assert_eq!(n, 5);
        assert_eq!(cursor.position(), 5);
        assert_eq!(cursor.into_inner(), b"hello");
    }

    #[test]
    fn test_vec_expansion() {
        let vec = vec![1, 2, 3];
        let mut cursor = Cursor::new(vec);
        cursor.set_position(5); // Beyond current end

        cursor.write(b"xy").unwrap();
        let result = cursor.into_inner();
        assert_eq!(result, vec![1, 2, 3, 0, 0, b'x', b'y']);
    }
}

// =============================================================================
// Integration Tests
// =============================================================================

#[test]
fn test_write_read_cycle() {
    let mut buffer = [0u8; 10];
    let mut cursor = Cursor::new(&mut buffer[..]);

    // Write data
    cursor.write(b"hello").unwrap();
    assert_eq!(cursor.position(), 5);

    // Reset position and read back
    cursor.set_position(0);
    let mut read_buf = [0u8; 5];
    cursor.read(&mut read_buf).unwrap();
    assert_eq!(&read_buf, b"hello");
}
