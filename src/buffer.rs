//! Buffers.

mod error;

use core::cmp::Ordering;
use core::fmt;

#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::parser::char::is_utf8_byte_continue;

pub(crate) use self::error::BufferTooSmallError;
pub use self::error::Error;

/// A trait for possibly extensible buffer types.
pub(crate) trait Buffer<'a> {
    /// Error on extending buffer.
    type ExtendError;

    /// Writes the formatted input to the buffer.
    ///
    /// Intended to be used with `std::write!`.
    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> Result<(), Self::ExtendError> {
        let mut buf = FmtWritableBuffer::new(self);
        match fmt::write(&mut buf, args) {
            Ok(_) => Ok(()),
            Err(_) => Err(buf.take_error_unwrap()),
        }
    }

    /// Returns the content in a byte slice.
    #[must_use]
    fn as_bytes(&self) -> &[u8];
    /// Returns the content in a byte slice.
    fn into_bytes(self) -> &'a [u8];
    /// Appends the given string slice.
    fn push_str(&mut self, s: &str) -> Result<(), Self::ExtendError>;
    /// Truncates the content to the specified length.
    ///
    /// # Panics
    ///
    /// Should panic if `new_len` is longer than the current content length
    /// (`self.content_bytes().len()`).
    /// Should panic if `new_len` does not lie on a `char` boundary.
    fn truncate(&mut self, new_len: usize);
    /// Pushes the characters.
    fn extend_chars<I>(&mut self, iter: I) -> Result<(), Self::ExtendError>
    where
        I: IntoIterator<Item = char>;
    /// Writes the optional string with the prefix.
    fn push_optional_with_prefix(
        &mut self,
        prefix: &str,
        body: Option<&str>,
    ) -> Result<(), Self::ExtendError> {
        if let Some(body) = body {
            self.push_str(prefix)?;
            self.push_str(body)?;
        }
        Ok(())
    }
    /// Expands the internal buffer if possible.
    fn try_reserve(&mut self, additional: usize) -> Result<(), Self::ExtendError>;
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<'a> Buffer<'a> for &'a mut String {
    type ExtendError = alloc::collections::TryReserveError;

    #[inline]
    fn as_bytes(&self) -> &[u8] {
        (**self).as_bytes()
    }

    #[inline]
    fn into_bytes(self) -> &'a [u8] {
        (*self).as_bytes()
    }

    fn push_str(&mut self, s: &str) -> Result<(), Self::ExtendError> {
        (**self).try_reserve(s.len())?;
        (**self).push_str(s);

        Ok(())
    }

    fn truncate(&mut self, new_len: usize) {
        if (**self).len() < new_len {
            panic!("[precondition] truncation should make the content shorter")
        }
        (**self).truncate(new_len);
    }

    fn extend_chars<I>(&mut self, iter: I) -> Result<(), Self::ExtendError>
    where
        I: IntoIterator<Item = char>,
    {
        // Cannot use `(**self).extend(iter)`, as it panics on OOM.
        let iter = iter.into_iter();
        (**self).try_reserve(iter.size_hint().0)?;
        let mut buf = [0_u8; 4];
        for c in iter {
            let s = c.encode_utf8(&mut buf);
            (**self).try_reserve(s.len())?;
            (**self).push_str(s);
        }
        Ok(())
    }

    fn push_optional_with_prefix(
        &mut self,
        prefix: &str,
        body: Option<&str>,
    ) -> Result<(), Self::ExtendError> {
        if let Some(body) = body {
            (**self).try_reserve(prefix.len() + body.len())?;
            (**self).push_str(prefix);
            (**self).push_str(body);
        }
        Ok(())
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), Self::ExtendError> {
        (**self).try_reserve(additional)
    }
}

/// Byte slice as a modifiable buffer.
#[derive(Debug)]
pub(super) struct ByteSliceBuf<'a> {
    /// Target slice.
    buf: &'a mut [u8],
    /// Content length, not the buffer size.
    len: usize,
}

impl<'a> ByteSliceBuf<'a> {
    /// Creates a byte slice buffer.
    #[inline]
    #[must_use]
    pub(super) fn new(buf: &'a mut [u8]) -> Self {
        Self { buf, len: 0 }
    }
}

impl<'a> Buffer<'a> for ByteSliceBuf<'a> {
    type ExtendError = BufferTooSmallError;

    #[inline]
    fn as_bytes(&self) -> &[u8] {
        &self.buf[..self.len]
    }

    #[inline]
    fn into_bytes(self) -> &'a [u8] {
        &self.buf[..self.len]
    }

    fn push_str(&mut self, s: &str) -> Result<(), Self::ExtendError> {
        let s_end = self.len + s.len();
        if self.buf.len() < s_end {
            return Err(BufferTooSmallError::new());
        }

        self.buf[self.len..s_end].copy_from_slice(s.as_bytes());
        self.len = s_end;

        Ok(())
    }

    fn truncate(&mut self, new_len: usize) {
        let last_byte = match new_len.cmp(&self.len) {
            Ordering::Greater => {
                panic!("[precondition] truncation should make the content shorter")
            }
            Ordering::Equal => return,
            Ordering::Less => self.buf[new_len],
        };
        // `0x80..=0xbf` (i.e. `0b_1000_0000..=0b_1011_1111`) is not the first byte,
        // and `0xc0..=0xc1` (i.e. `0b_1100_0000..=0b_1100_0001` shouldn't appear
        // anywhere in UTF-8 byte sequence.
        // `0x80 as i8` is -128, and `0xc0 as i8` is -96.
        //
        // The first byte of the UTF-8 character is not `0b10xx_xxxx`, and
        // the continue bytes is `0b10xx_xxxx`.
        // `0b1011_1111 as i8` is -65, and `0b1000_0000 as i8` is -128.
        let is_byte_continue = is_utf8_byte_continue(last_byte);
        if is_byte_continue {
            panic!("[precondition] `new_len` should lie on a `char` boundary");
        }

        self.len = new_len;
    }

    fn extend_chars<I>(&mut self, iter: I) -> Result<(), Self::ExtendError>
    where
        I: IntoIterator<Item = char>,
    {
        let mut buf = [0_u8; 4];
        for c in iter {
            self.push_str(c.encode_utf8(&mut buf))?;
        }
        Ok(())
    }

    fn push_optional_with_prefix(
        &mut self,
        prefix: &str,
        body: Option<&str>,
    ) -> Result<(), Self::ExtendError> {
        if let Some(body) = body {
            let prefix_end = self.len + prefix.len();
            let body_end = prefix_end + body.len();
            if self.buf.len() < body_end {
                return Err(BufferTooSmallError::new());
            }
            self.buf[self.len..prefix_end].copy_from_slice(prefix.as_bytes());
            self.buf[prefix_end..body_end].copy_from_slice(body.as_bytes());
            self.len = body_end;
        }
        Ok(())
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), Self::ExtendError> {
        let rest_len = self.buf.len() - self.len;
        if additional > rest_len {
            Err(BufferTooSmallError::new())
        } else {
            Ok(())
        }
    }
}

/// A wrapper type to make the buffer type writable by `core::fmt::Write`.
pub(crate) struct FmtWritableBuffer<'a, 'b, T: ?Sized + Buffer<'b>> {
    /// Buffer.
    buffer: &'a mut T,
    /// Error.
    error: Option<T::ExtendError>,
}

impl<'a, 'b, T: ?Sized + Buffer<'b>> FmtWritableBuffer<'a, 'b, T> {
    /// Creates a new wrapper object.
    #[inline]
    #[must_use]
    pub(crate) fn new(buffer: &'a mut T) -> Self {
        Self {
            buffer,
            error: None,
        }
    }

    /// Takes the error object out of `self` and returns it.
    ///
    /// # Panics
    ///
    /// Panics if the error is not set or already cleared.
    #[inline]
    #[must_use]
    pub(crate) fn take_error_unwrap(&mut self) -> T::ExtendError {
        self.error
            .take()
            .expect("[precondition] buffer error should be set")
    }
}

impl<'a, 'b, T: ?Sized + Buffer<'b>> fmt::Write for FmtWritableBuffer<'a, 'b, T> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if let Err(e) = self.buffer.push_str(s) {
            self.error = Some(e);
            return Err(fmt::Error);
        }
        Ok(())
    }
}
