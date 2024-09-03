#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use core::cmp;
pub use embedded_io::*;

/// A `Cursor` wraps an in-memory buffer and provides it with a
/// [`Seek`] implementation.
///
/// This trait is the embedded-io equivalent of std::io::cursor::Cursor.
///
/// `Cursor`s are used with in-memory buffers, anything implementing
/// <code>[AsRef]<\[u8]></code>, to allow them to implement [`Read`] and/or [`Write`],
/// allowing these buffers to be used anywhere you might use a reader or writer
/// that does actual I/O.
///
/// The standard library implements some I/O traits on various types which
/// are commonly used as a buffer, like <code>Cursor<[Vec]\<u8>></code> and
/// <code>Cursor<[&\[u8\]][bytes]></code>.
#[derive(Debug, Default, Eq, PartialEq)]
pub struct Cursor<T> {
    inner: T,
    pos: u64,
}

impl<T> Cursor<T> {
    /// Creates a new cursor wrapping the provided underlying in-memory buffer.
    ///
    /// Cursor initial position is `0` even if underlying buffer (e.g., [`Vec`])
    /// is not empty. So writing to cursor starts with overwriting [`Vec`]
    /// content, not with appending to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_io_extras::Cursor;
    ///
    /// let buff = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buff);
    /// ```
    pub const fn new(inner: T) -> Cursor<T> {
        Cursor { pos: 0, inner }
    }

    /// Consumes this cursor, returning the underlying value.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_io_extras::Cursor;
    ///
    /// let buff = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buff);
    ///
    /// let vec = buff.into_inner();
    /// ```
    pub fn into_inner(self) -> T {
        self.inner
    }

    /// Gets a reference to the underlying value in this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_io_extras::Cursor;
    ///
    /// let buff = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buff);
    ///
    /// let reference = buff.get_ref();
    /// ```
    pub const fn get_ref(&self) -> &T {
        &self.inner
    }

    /// Gets a mutable reference to the underlying value in this cursor.
    ///
    /// Care should be taken to avoid modifying the internal I/O state of the
    /// underlying value as it may corrupt this cursor's position.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_io_extras::Cursor;
    ///
    /// let mut buff = Cursor::new(Vec::new());
    /// # fn force_inference(_: &Cursor<Vec<u8>>) {}
    /// # force_inference(&buff);
    ///
    /// let reference = buff.get_mut();
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.inner
    }

    /// Returns the current position of this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_io_extras::Cursor;
    /// use embedded_io::{Seek, SeekFrom};
    ///
    ///
    /// let mut buff = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(buff.position(), 0);
    ///
    /// buff.seek(SeekFrom::Current(2)).unwrap();
    /// assert_eq!(buff.position(), 2);
    ///
    /// buff.seek(SeekFrom::Current(-1)).unwrap();
    /// assert_eq!(buff.position(), 1);
    /// ```
    pub const fn position(&self) -> u64 {
        self.pos
    }

    /// Sets the position of this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_io_extras::Cursor;
    ///
    /// let mut buff = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(buff.position(), 0);
    ///
    /// buff.set_position(2);
    /// assert_eq!(buff.position(), 2);
    ///
    /// buff.set_position(4);
    /// assert_eq!(buff.position(), 4);
    /// ```
    pub fn set_position(&mut self, pos: u64) {
        self.pos = pos;
    }
}

impl<T> Cursor<T>
where
    T: AsRef<[u8]>,
{
    /// Returns the remaining slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_io_extras::Cursor;
    ///
    /// let mut buff = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(buff.remaining_slice(), &[1, 2, 3, 4, 5]);
    ///
    /// buff.set_position(2);
    /// assert_eq!(buff.remaining_slice(), &[3, 4, 5]);
    ///
    /// buff.set_position(4);
    /// assert_eq!(buff.remaining_slice(), &[5]);
    ///
    /// buff.set_position(6);
    /// assert_eq!(buff.remaining_slice(), &[]);
    /// ```
    pub fn remaining_slice(&self) -> &[u8] {
        let len = self.pos.min(self.inner.as_ref().len() as u64);
        &self.inner.as_ref()[(len as usize)..]
    }

    /// Returns `true` if the remaining slice is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_io_extras::Cursor;
    ///
    /// let mut buff = Cursor::new(vec![1, 2, 3, 4, 5]);
    ///
    /// buff.set_position(2);
    /// assert!(!buff.is_empty());
    ///
    /// buff.set_position(5);
    /// assert!(buff.is_empty());
    ///
    /// buff.set_position(10);
    /// assert!(buff.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.pos >= self.inner.as_ref().len() as u64
    }
}

impl<T> Clone for Cursor<T>
where
    T: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Cursor {
            inner: self.inner.clone(),
            pos: self.pos,
        }
    }

    #[inline]
    fn clone_from(&mut self, other: &Self) {
        self.inner.clone_from(&other.inner);
        self.pos = other.pos;
    }
}

impl<T> ErrorType for Cursor<T>
where
    T: AsRef<[u8]>,
{
    type Error = ErrorKind;
}

impl<T> Seek for Cursor<T>
where
    T: AsRef<[u8]>,
{
    fn seek(&mut self, style: SeekFrom) -> Result<u64, Self::Error> {
        let (base_pos, offset) = match style {
            SeekFrom::Start(n) => {
                self.pos = n;
                return Ok(n);
            }
            SeekFrom::End(n) => (self.inner.as_ref().len() as u64, n),
            SeekFrom::Current(n) => (self.pos, n),
        };
        match base_pos.checked_add_signed(offset) {
            Some(n) => {
                self.pos = n;
                Ok(self.pos)
            }
            None => Err(ErrorKind::InvalidInput),
        }
    }

    fn rewind(&mut self) -> Result<(), Self::Error> {
        self.pos = 0;
        Ok(())
    }

    fn stream_position(&mut self) -> Result<u64, Self::Error> {
        Ok(self.pos)
    }
}

impl<T> Read for Cursor<T>
where
    T: AsRef<[u8]>,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        // Read::read will not return an error in this case,
        // so we can safely unwrap.
        let n = Read::read(&mut self.remaining_slice(), buf).unwrap();
        self.pos += n as u64;
        Ok(n)
    }
}

impl<T> BufRead for Cursor<T>
where
    T: AsRef<[u8]>,
{
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        Ok(self.remaining_slice())
    }

    fn consume(&mut self, amt: usize) {
        self.pos += amt as u64;
    }
}

impl Write for Cursor<&mut [u8]> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        Ok(slice_write(&mut self.pos, &mut self.inner, buf))
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl<const N: usize> Write for Cursor<[u8; N]> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        Ok(slice_write(&mut self.pos, &mut self.inner, buf))
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl Write for Cursor<Vec<u8>> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        Ok(vec_write(&mut self.pos, &mut self.inner, buf))
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl Write for Cursor<&mut Vec<u8>> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        Ok(vec_write(&mut self.pos, self.inner, buf))
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

fn slice_write(pos_mut: &mut u64, slice: &mut [u8], buf: &[u8]) -> usize {
    let pos = cmp::min(*pos_mut, slice.len() as u64) as usize;
    if pos >= slice.len() {
        return 0;
    }
    // Write::write will not return an error in this case,
    // so we can safely unwrap.
    let amt = (&mut slice[pos..]).write(buf).unwrap();
    *pos_mut += amt as u64;
    amt
}

/// Resizing write implementation for [`Cursor`]
///
/// Cursor is allowed to have a pre-allocated and initialised
/// vector body, but with a position of 0. This means the [`Write`]
/// will overwrite the contents of the vec.
///
/// This also allows for the vec body to be empty, but with a position of N.
/// This means that [`Write`] will pad the vec with 0 initially,
/// before writing anything from that point
#[cfg(feature = "alloc")]
fn vec_write(pos_mut: &mut u64, vec: &mut Vec<u8>, buf: &[u8]) -> usize {
    let pos = *pos_mut as usize;

    // Ensure the vector is large enough
    if pos > vec.len() {
        vec.resize(pos, 0);
    }

    // Determine the amount that can be written
    let end_pos = pos + buf.len();
    if end_pos > vec.len() {
        vec.resize(end_pos, 0);
    }

    vec[pos..end_pos].copy_from_slice(buf);

    // Update the position
    *pos_mut += buf.len() as u64;

    buf.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "alloc")]
    use alloc::vec;

    #[test]
    fn test_new() {
        let data = [1, 2, 3];
        let cur = Cursor::new(&data[..]);
        assert_eq!(cur.position(), 0);
        assert_eq!(cur.get_ref(), &data);
    }

    #[test]
    fn test_into_inner() {
        let data = [1, 2, 3];
        let cur = Cursor::new(&data[..]);
        assert_eq!(cur.into_inner(), &data[..]);
    }

    #[test]
    fn test_get_ref() {
        let data = [1, 2, 3];
        let cur = Cursor::new(&data[..]);
        assert_eq!(cur.get_ref(), &data);
    }

    #[test]
    fn test_get_mut() {
        let mut data = [1, 2, 3, 4];
        let mut cur = Cursor::new(&mut data[..]);
        cur.get_mut()[3] = 4;
        assert_eq!(cur.get_ref(), &[1, 2, 3, 4]);
    }
    #[test]
    fn test_position() {
        let data = [1, 2, 3];
        let mut cur = Cursor::new(&data[..]);
        assert_eq!(cur.position(), 0);
        cur.set_position(2);
        assert_eq!(cur.position(), 2);
    }

    #[test]
    fn test_remaining_slice() {
        let data = [1, 2, 3];
        let cur = Cursor::new(&data[..]);
        assert_eq!(cur.remaining_slice(), &[1, 2, 3][..]);
        let mut cur = Cursor::new(&data[..]);
        cur.set_position(2);
        assert_eq!(cur.remaining_slice(), &[3][..]);
    }

    #[test]
    fn test_is_empty() {
        let data = [1, 2, 3];
        let mut cur = Cursor::new(&data[..]);
        assert!(!cur.is_empty());
        cur.set_position(3);
        assert!(cur.is_empty());
    }

    #[test]
    fn test_clone() {
        let data = [1, 2, 3];
        let cur = Cursor::new(&data[..]);
        let cloned = cur.clone();
        assert_eq!(cur.get_ref(), cloned.get_ref());
        assert_eq!(cur.position(), cloned.position());
    }

    #[test]
    fn test_seek() {
        let data = [1, 2, 3];
        let mut cur = Cursor::new(&data[..]);

        // Test SeekFrom::Start
        assert_eq!(cur.seek(SeekFrom::Start(1)).unwrap(), 1);
        assert_eq!(cur.position(), 1);

        // Test SeekFrom::Current
        assert_eq!(cur.seek(SeekFrom::Current(1)).unwrap(), 2);
        assert_eq!(cur.position(), 2);

        // Test SeekFrom::End
        assert_eq!(cur.seek(SeekFrom::End(-1)).unwrap(), 2);
        assert_eq!(cur.position(), 2);

        // Test out-of-bounds SeekFrom::End
        assert!(cur.seek(SeekFrom::End(1)).is_ok());
        assert_eq!(cur.position(), 4);

        // Test out-of-bounds SeekFrom::Current
        cur.set_position(3);
        assert!(cur.seek(SeekFrom::Current(1)).is_ok());
        assert_eq!(cur.position(), 4);
    }

    #[test]
    fn test_rewind() {
        let data = [1, 2, 3];
        let mut cur = Cursor::new(&data[..]);
        cur.set_position(2);
        cur.rewind().unwrap();
        assert_eq!(cur.position(), 0);
    }

    #[test]
    fn test_read() {
        let data = [1, 2, 3];
        let mut cur = Cursor::new(&data[..]);
        let mut buf = [0; 2];
        assert_eq!(cur.read(&mut buf).unwrap(), 2);
        assert_eq!(buf, [1, 2]);
        assert_eq!(cur.position(), 2);
        assert_eq!(cur.read(&mut buf).unwrap(), 1);
        assert_eq!(buf, [3, 2]);
        assert_eq!(cur.position(), 3);
    }

    #[test]
    fn test_buf_read() {
        let data = [1, 2, 3];
        let mut cur = Cursor::new(&data[..]);
        assert_eq!(cur.fill_buf().unwrap(), &[1, 2, 3][..]);
        cur.consume(2);
        assert_eq!(cur.fill_buf().unwrap(), &[3][..]);
    }

    #[test]
    fn test_slice_write() {
        let mut slice = [0; 3];
        let mut cur = Cursor::new(&mut slice[..]);
        assert_eq!(cur.write(&[1, 2, 3]).unwrap(), 3);
        assert_eq!(cur.position(), 3);
        assert_eq!(slice, [1, 2, 3]);

        let mut cur = Cursor::new(&mut slice[..]);
        cur.set_position(1);
        assert_eq!(cur.write(&[4, 5]).unwrap(), 2);
        assert_eq!(slice, [1, 4, 5]);
    }

    #[test]
    fn test_array_write_full() {
        let array = [0u8; 3];
        let mut cur = Cursor::new(array);
        assert_eq!(cur.write(&[1, 2, 3]).unwrap(), 3);
        assert_eq!(cur.get_ref(), &[1, 2, 3]);

        // Attempt to write beyond the array's capacity
        assert_eq!(cur.write(&[4, 5, 6]).unwrap(), 0); // Should not write anything
        assert_eq!(cur.get_ref(), &[1, 2, 3]); // Array remains unchanged
    }

    #[test]
    fn test_array_write() {
        let mut arr = [0; 3];
        let mut cur = Cursor::new(&mut arr[..]);
        assert_eq!(cur.write(&[1, 2, 3]).unwrap(), 3);
        assert_eq!(cur.position(), 3);
        assert_eq!(cur.get_ref(), &[1, 2, 3]);

        let mut arr = [1, 0, 0]; // Reset array for the next test
        let mut cur = Cursor::new(&mut arr[..]);
        cur.set_position(1);
        assert_eq!(cur.write(&[4, 5]).unwrap(), 2);
        assert_eq!(cur.position(), 3);
        assert_eq!(cur.get_ref(), &[1, 4, 5]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_vec_write() {
        let vec = vec![0; 3];
        let mut cur = Cursor::new(vec);
        assert_eq!(cur.write(&[1, 2, 3]).unwrap(), 3);
        assert_eq!(cur.position(), 3);
        assert_eq!(cur.get_ref(), &vec![1, 2, 3]);

        assert_eq!(cur.write(&[4, 5]).unwrap(), 2);
        assert_eq!(cur.position(), 5);
        assert_eq!(cur.get_ref(), &vec![1, 2, 3, 4, 5]);

        let mut vec = Vec::new();
        let mut cur = Cursor::new(&mut vec);
        cur.set_position(2);
        assert_eq!(cur.write(&[1, 2]).unwrap(), 2);
        assert_eq!(vec.as_slice(), &[0, 0, 1, 2]);
    }

    #[test]
    fn test_seek_invalid_input() {
        let data = [1, 2, 3];
        let mut cur = Cursor::new(&data[..]);

        // Attempt to seek to a negative position from the start
        assert_eq!(
            cur.seek(SeekFrom::Current(-5)).unwrap_err(),
            ErrorKind::InvalidInput
        );
    }
    #[test]
    fn test_slice_write_within_bounds() {
        let mut slice = [0u8; 10];
        let buf = [1, 2, 3];
        let mut pos = 0;
        let written = slice_write(&mut pos, &mut slice, &buf);
        assert_eq!(written, 3);
        assert_eq!(&slice[..3], &buf);
        assert_eq!(pos, 3);
    }

    #[test]
    fn test_slice_write_exceeding_bounds() {
        let mut slice = [0u8; 5];
        let buf = [1, 2, 3, 4, 5, 6];
        let mut pos = 0;
        let written = slice_write(&mut pos, &mut slice, &buf);
        assert_eq!(written, 5);
        assert_eq!(&slice, &[1, 2, 3, 4, 5]);
        assert_eq!(pos, 5);
    }

    #[test]
    fn test_slice_write_at_position() {
        let mut slice = [0u8; 10];
        let buf = [4, 5, 6];
        let mut pos = 7;
        let written = slice_write(&mut pos, &mut slice, &buf);
        assert_eq!(written, 3);
        assert_eq!(&slice[7..10], &buf);
        assert_eq!(pos, 10);
    }

    #[test]
    fn test_slice_write_past_end() {
        let mut slice = [0u8; 5];
        let buf = [1, 2, 3];
        let mut pos = 10;
        let written = slice_write(&mut pos, &mut slice, &buf);
        assert_eq!(written, 0);
        assert_eq!(pos, 10);
    }

    #[test]
    fn test_slice_write_empty_buffer() {
        let mut slice = [0u8; 10];
        let buf = [];
        let mut pos = 0;
        let written = slice_write(&mut pos, &mut slice, &buf);
        assert_eq!(written, 0);
        assert_eq!(pos, 0);
    }

    #[test]
    fn test_slice_write_partial_write() {
        let mut slice = [0u8; 5];
        let buf = [1, 2, 3, 4, 5, 6];
        let mut pos = 3;
        let written = slice_write(&mut pos, &mut slice, &buf);
        assert_eq!(written, 2);
        assert_eq!(&slice, &[0, 0, 0, 1, 2]);
        assert_eq!(pos, 5);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_vec_write_within_bounds() {
        let mut vec = vec![0u8; 10];
        let buf = [1, 2, 3];
        let mut pos = 0;
        let written = vec_write(&mut pos, &mut vec, &buf);
        assert_eq!(written, 3);
        assert_eq!(&vec[..3], &buf);
        assert_eq!(pos, 3);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_vec_write_exceeding_bounds() {
        let mut vec = vec![0u8; 5];
        let buf = [1, 2, 3, 4, 5, 6];
        let mut pos = 0;
        let written = vec_write(&mut pos, &mut vec, &buf);
        assert_eq!(written, 6);
        assert_eq!(&vec, &buf);
        assert_eq!(pos, 6);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_vec_write_at_position() {
        let mut vec = vec![0u8; 10];
        let buf = [4, 5, 6];
        let mut pos = 7;
        let written = vec_write(&mut pos, &mut vec, &buf);
        assert_eq!(written, 3);
        assert_eq!(&vec[7..10], &buf);
        assert_eq!(pos, 10);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_vec_write_past_end() {
        let mut vec = vec![0u8; 5];
        let buf = [1, 2, 3];
        let mut pos = 10;
        let written = vec_write(&mut pos, &mut vec, &buf);
        assert_eq!(written, 3);
        assert_eq!(&vec, &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3]);
        assert_eq!(pos, 13);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_vec_write_empty_buffer() {
        let mut vec = vec![0u8; 10];
        let buf = [];
        let mut pos = 0;
        let written = vec_write(&mut pos, &mut vec, &buf);
        assert_eq!(written, 0);
        assert_eq!(pos, 0);
    }
}
