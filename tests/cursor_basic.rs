//! Basic Cursor functionality tests
//!
//! Tests for cursor construction, position management, and basic methods.

use embedded_io_cursor::Cursor;

#[test]
fn test_new_cursor() {
    let data = [1, 2, 3, 4, 5];
    let cursor = Cursor::new(&data[..]);
    assert_eq!(cursor.position(), 0);
    assert_eq!(cursor.get_ref().len(), 5);
}

#[test]
fn test_position_methods() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data[..]);

    // Initial position
    assert_eq!(cursor.position(), 0);

    // Set position
    cursor.set_position(3);
    assert_eq!(cursor.position(), 3);

    // Set position beyond end
    cursor.set_position(10);
    assert_eq!(cursor.position(), 10);
}

#[test]
fn test_remaining_slice() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data[..]);

    // At start
    assert_eq!(cursor.remaining_slice(), &[1, 2, 3, 4, 5]);

    // In middle
    cursor.set_position(2);
    assert_eq!(cursor.remaining_slice(), &[3, 4, 5]);

    // At end
    cursor.set_position(5);
    assert_eq!(cursor.remaining_slice(), &[]);

    // Beyond end
    cursor.set_position(10);
    assert_eq!(cursor.remaining_slice(), &[]);
}

#[test]
fn test_is_empty() {
    let data = [1, 2, 3];
    let mut cursor = Cursor::new(&data[..]);

    assert!(!cursor.is_empty());

    cursor.set_position(2);
    assert!(!cursor.is_empty());

    cursor.set_position(3);
    assert!(cursor.is_empty());

    cursor.set_position(10);
    assert!(cursor.is_empty());
}

#[test]
fn test_accessors() {
    let mut data = vec![1, 2, 3];
    let mut cursor = Cursor::new(&mut data);

    // get_ref
    assert_eq!(cursor.get_ref().len(), 3);

    // get_mut
    cursor.get_mut().push(4);
    assert_eq!(cursor.get_ref().len(), 4);

    // into_inner
    let inner = cursor.into_inner();
    assert_eq!(inner.len(), 4);
}

#[test]
fn test_clone() {
    let data = vec![1, 2, 3];
    let mut cursor1 = Cursor::new(data);
    cursor1.set_position(2);

    let mut cursor2 = cursor1.clone();

    // Verify independence
    cursor1.set_position(1);
    cursor2.set_position(3);

    assert_eq!(cursor1.position(), 1);
    assert_eq!(cursor2.position(), 3);
}

#[test]
fn test_debug_format() {
    let data = [1, 2, 3];
    let cursor = Cursor::new(&data[..]);
    let debug_str = format!("{:?}", cursor);
    assert!(debug_str.contains("Cursor"));
}
