//! Read operation tests
//!
//! Tests for Read and BufRead trait implementations.

use embedded_io::{BufRead, Read};
use embedded_io_cursor::Cursor;

#[test]
fn test_read_basic() {
    let data = b"hello world";
    let mut cursor = Cursor::new(&data[..]);
    let mut buf = [0u8; 5];

    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 5);
    assert_eq!(&buf, b"hello");
    assert_eq!(cursor.position(), 5);
}

#[test]
fn test_read_partial() {
    let data = b"abc";
    let mut cursor = Cursor::new(&data[..]);
    let mut buf = [0u8; 5];

    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 3);
    assert_eq!(&buf[..3], b"abc");
    assert_eq!(cursor.position(), 3);
}

#[test]
fn test_read_empty() {
    let data = b"";
    let mut cursor = Cursor::new(&data[..]);
    let mut buf = [0u8; 5];

    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 0);
    assert_eq!(cursor.position(), 0);
}

#[test]
fn test_read_exact_success() {
    let data = b"hello world";
    let mut cursor = Cursor::new(&data[..]);
    let mut buf = [0u8; 5];

    cursor.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"hello");
    assert_eq!(cursor.position(), 5);
}

#[test]
fn test_read_exact_eof() {
    let data = b"abc";
    let mut cursor = Cursor::new(&data[..]);
    let mut buf = [0u8; 5];

    let result = cursor.read_exact(&mut buf);
    assert!(result.is_err());
}

#[test]
fn test_buf_read_fill_buf() {
    let data = b"hello world";
    let mut cursor = Cursor::new(&data[..]);

    let buf = cursor.fill_buf().unwrap();
    assert_eq!(buf, b"hello world");

    cursor.set_position(6);
    let buf = cursor.fill_buf().unwrap();
    assert_eq!(buf, b"world");
}

#[test]
fn test_buf_read_consume() {
    let data = b"hello world";
    let mut cursor = Cursor::new(&data[..]);

    let buf = cursor.fill_buf().unwrap();
    assert_eq!(buf.len(), 11);

    cursor.consume(5);
    assert_eq!(cursor.position(), 5);

    let buf = cursor.fill_buf().unwrap();
    assert_eq!(buf, b" world");
}

#[test]
fn test_buf_read_consume_beyond() {
    let data = b"hello";
    let mut cursor = Cursor::new(&data[..]);

    cursor.consume(10); // Beyond buffer
    assert_eq!(cursor.position(), 10);

    let buf = cursor.fill_buf().unwrap();
    assert_eq!(buf, b"");
}

#[test]
fn test_read_at_end() {
    let data = b"hello";
    let mut cursor = Cursor::new(&data[..]);
    cursor.set_position(5);

    let mut buf = [0u8; 5];
    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 0);
}

#[test]
fn test_read_beyond_end() {
    let data = b"hello";
    let mut cursor = Cursor::new(&data[..]);
    cursor.set_position(10);

    let mut buf = [0u8; 5];
    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 0);
}
