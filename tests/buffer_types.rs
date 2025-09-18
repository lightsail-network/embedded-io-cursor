//! Buffer type compatibility tests
//!
//! Tests that verify Cursor works correctly with different buffer types.

use embedded_io::{Read, Write};
use embedded_io_cursor::Cursor;

// =============================================================================
// Array Types
// =============================================================================

#[test]
fn test_array_reference() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data);

    // Should be readable
    let mut buf = [0u8; 3];
    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 3);
    assert_eq!(&buf, &[1, 2, 3]);
}

#[test]
fn test_owned_array() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(data);

    // Should be readable
    let mut buf = [0u8; 3];
    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 3);
    assert_eq!(&buf, &[1, 2, 3]);

    // Should be writable
    cursor.set_position(0);
    let n = cursor.write(&[10, 20]).unwrap();
    assert_eq!(n, 2);

    let inner = cursor.into_inner();
    assert_eq!(&inner[..2], &[10, 20]);
}

#[test]
fn test_mutable_array_reference() {
    let mut data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&mut data);

    // Should be writable
    let n = cursor.write(&[10, 20]).unwrap();
    assert_eq!(n, 2);
    assert_eq!(&data[..2], &[10, 20]);
}

// =============================================================================
// Slice Types
// =============================================================================

#[test]
fn test_read_only_slice() {
    let data = vec![1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data[..]);

    // Should be readable
    let mut buf = [0u8; 3];
    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 3);
    assert_eq!(&buf, &[1, 2, 3]);
}

#[test]
fn test_mutable_slice() {
    let mut data = vec![1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&mut data[..]);

    // Should be readable
    let mut buf = [0u8; 3];
    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 3);
    assert_eq!(&buf, &[1, 2, 3]);

    // Should be writable
    cursor.set_position(0);
    let n = cursor.write(&[10, 20]).unwrap();
    assert_eq!(n, 2);
    assert_eq!(&data[..2], &[10, 20]);
}

// =============================================================================
// Vec Types (requires alloc feature)
// =============================================================================

#[cfg(feature = "alloc")]
mod vec_tests {
    extern crate alloc;
    use super::*;
    use alloc::vec::Vec;

    #[test]
    fn test_vec_reference() {
        let mut vec = vec![1, 2, 3, 4, 5];
        let mut cursor = Cursor::new(&mut vec);

        // Should be readable
        let mut buf = [0u8; 3];
        let n = cursor.read(&mut buf).unwrap();
        assert_eq!(n, 3);
        assert_eq!(&buf, &[1, 2, 3]);

        // Should be writable and expandable
        cursor.set_position(10);
        let n = cursor.write(&[99]).unwrap();
        assert_eq!(n, 1);
        assert_eq!(vec.len(), 11);
        assert_eq!(vec[10], 99);
    }

    #[test]
    fn test_owned_vec() {
        let vec = vec![1, 2, 3, 4, 5];
        let mut cursor = Cursor::new(vec);

        // Should be readable
        let mut buf = [0u8; 3];
        let n = cursor.read(&mut buf).unwrap();
        assert_eq!(n, 3);
        assert_eq!(&buf, &[1, 2, 3]);

        // Should be writable and expandable
        cursor.set_position(10);
        let n = cursor.write(&[99]).unwrap();
        assert_eq!(n, 1);

        let result = cursor.into_inner();
        assert_eq!(result.len(), 11);
        assert_eq!(result[10], 99);
    }

    #[test]
    fn test_vec_gap_filling() {
        let vec = vec![1, 2, 3];
        let mut cursor = Cursor::new(vec);

        // Write with gap
        cursor.set_position(5);
        cursor.write(&[99]).unwrap();

        let result = cursor.into_inner();
        assert_eq!(result, vec![1, 2, 3, 0, 0, 99]);
    }

    #[test]
    fn test_empty_vec() {
        let vec = Vec::new();
        let mut cursor = Cursor::new(vec);

        cursor.write(&[1, 2, 3]).unwrap();

        let result = cursor.into_inner();
        assert_eq!(result, vec![1, 2, 3]);
    }
}

// =============================================================================
// Box Types (requires alloc feature)
// =============================================================================

#[cfg(feature = "alloc")]
mod box_tests {
    extern crate alloc;
    use super::*;
    use alloc::boxed::Box;

    #[test]
    fn test_boxed_slice() {
        let data: Box<[u8]> = vec![1, 2, 3, 4, 5].into_boxed_slice();
        let mut cursor = Cursor::new(data);

        // Should be readable
        let mut buf = [0u8; 3];
        let n = cursor.read(&mut buf).unwrap();
        assert_eq!(n, 3);
        assert_eq!(&buf, &[1, 2, 3]);

        // Should be writable (but not expandable)
        cursor.set_position(0);
        let n = cursor.write(&[10, 20]).unwrap();
        assert_eq!(n, 2);

        let inner = cursor.into_inner();
        assert_eq!(&inner[..2], &[10, 20]);
    }
}
