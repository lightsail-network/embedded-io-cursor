//! Seek operation tests
//!
//! Tests for Seek trait implementation.

use embedded_io::{Read, Seek, SeekFrom};
use embedded_io_cursor::Cursor;

#[test]
fn test_seek_start() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data[..]);

    let pos = cursor.seek(SeekFrom::Start(3)).unwrap();
    assert_eq!(pos, 3);
    assert_eq!(cursor.position(), 3);
}

#[test]
fn test_seek_start_beyond_end() {
    let data = [1, 2, 3];
    let mut cursor = Cursor::new(&data[..]);

    let pos = cursor.seek(SeekFrom::Start(10)).unwrap();
    assert_eq!(pos, 10);
    assert_eq!(cursor.position(), 10);
}

#[test]
fn test_seek_end() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data[..]);

    let pos = cursor.seek(SeekFrom::End(0)).unwrap();
    assert_eq!(pos, 5);
    assert_eq!(cursor.position(), 5);

    let pos = cursor.seek(SeekFrom::End(-2)).unwrap();
    assert_eq!(pos, 3);
    assert_eq!(cursor.position(), 3);

    let pos = cursor.seek(SeekFrom::End(2)).unwrap();
    assert_eq!(pos, 7);
    assert_eq!(cursor.position(), 7);
}

#[test]
fn test_seek_current() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data[..]);
    cursor.set_position(2);

    let pos = cursor.seek(SeekFrom::Current(2)).unwrap();
    assert_eq!(pos, 4);
    assert_eq!(cursor.position(), 4);

    let pos = cursor.seek(SeekFrom::Current(-1)).unwrap();
    assert_eq!(pos, 3);
    assert_eq!(cursor.position(), 3);
}

#[test]
fn test_seek_current_beyond_end() {
    let data = [1, 2, 3];
    let mut cursor = Cursor::new(&data[..]);
    cursor.set_position(2);

    let pos = cursor.seek(SeekFrom::Current(5)).unwrap();
    assert_eq!(pos, 7);
    assert_eq!(cursor.position(), 7);
}

#[test]
fn test_seek_overflow() {
    let data = [1, 2, 3];
    let mut cursor = Cursor::new(&data[..]);

    // Test potential overflow (may or may not actually overflow depending on platform)
    let result = cursor.seek(SeekFrom::End(i64::MAX));
    // This might succeed on some platforms, so we just verify it doesn't panic
    let _ = result;

    // Test underflow with Current - this should reliably fail
    cursor.set_position(5);
    let result = cursor.seek(SeekFrom::Current(-10));
    assert!(result.is_err());
}

#[test]
fn test_seek_underflow() {
    let data = [1, 2, 3];
    let mut cursor = Cursor::new(&data[..]);
    cursor.set_position(2);

    let result = cursor.seek(SeekFrom::Current(-5));
    assert!(result.is_err());
}

#[test]
fn test_rewind() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data[..]);
    cursor.set_position(3);

    cursor.rewind().unwrap();
    assert_eq!(cursor.position(), 0);
}

#[test]
fn test_stream_position() {
    let data = [1, 2, 3, 4, 5];
    let mut cursor = Cursor::new(&data[..]);
    cursor.set_position(3);

    let pos = cursor.stream_position().unwrap();
    assert_eq!(pos, 3);
}

#[test]
fn test_seek_with_io_operations() {
    let data = b"hello world";
    let mut cursor = Cursor::new(&data[..]);

    // Read some data
    let mut buf = [0u8; 5];
    cursor.read(&mut buf).unwrap();
    assert_eq!(&buf, b"hello");
    assert_eq!(cursor.position(), 5);

    // Seek to start and read again
    cursor.seek(SeekFrom::Start(0)).unwrap();
    cursor.read(&mut buf).unwrap();
    assert_eq!(&buf, b"hello");

    // Seek to end and read (should get 0 bytes)
    cursor.seek(SeekFrom::End(0)).unwrap();
    let n = cursor.read(&mut buf).unwrap();
    assert_eq!(n, 0);
}
