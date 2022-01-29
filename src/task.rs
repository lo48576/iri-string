//! API for tasks.

use core::fmt;

#[cfg(feature = "alloc")]
use alloc::collections::TryReserveError;

#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::buffer::{BufferTooSmallError, Error as BufferError};

/// Processes the data and write it somewhere.
pub trait ProcessAndWrite: Sized {
    /// Borrowed output types.
    type OutputBorrowed: ?Sized;
    /// Owned output types.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    type OutputOwned;
    /// Data processing error.
    type ProcessError: fmt::Display;

    /// Processes the data, and writes it to the newly allocated buffer.
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * failed to allocate memory, or
    /// * failed to process data.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    fn allocate_and_write(self) -> Result<Self::OutputOwned, Error<Self::ProcessError>>;

    /// Processes the data, and writes it to the given byte slice.
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * buffer is not large enough, or
    /// * failed to process data.
    fn write_to_byte_slice(
        self,
        buf: &mut [u8],
    ) -> Result<&Self::OutputBorrowed, Error<Self::ProcessError>>;

    /// Processes the data, and appends it to the buffer inside the provided [`String`].
    ///
    /// # Failures
    ///
    /// This fails if failed to process data.
    ///
    /// # Panics
    ///
    /// This panics if failed to allocate memory.
    /// To avoid panic on allocation failure, use [`try_append_to_std_string`].
    ///
    /// [`try_append_to_std_string`]: `Self::try_append_to_std_string`
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    fn append_to_std_string(
        self,
        buf: &mut String,
    ) -> Result<&Self::OutputBorrowed, Self::ProcessError> {
        match self.try_append_to_std_string(buf) {
            Ok(v) => Ok(v),
            Err(Error::Buffer(e)) => panic!("buffer error: {}", e),
            Err(Error::Process(e)) => Err(e),
        }
    }

    /// Processes the data, and appends it to the buffer inside the provided [`String`].
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * failed to allocate memory, or
    /// * failed to process data.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    fn try_append_to_std_string(
        self,
        buf: &mut String,
    ) -> Result<&Self::OutputBorrowed, Error<Self::ProcessError>>;
}

/// Write task error.
#[derive(Debug, Clone)]
pub enum Error<T> {
    /// Buffer error.
    Buffer(BufferError),
    /// Data processing failure.
    Process(T),
}

impl<T> fmt::Display for Error<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Buffer(_) => f.write_str("buffer error"),
            Error::Process(_) => f.write_str("data processing failed"),
        }
    }
}

impl<T> From<BufferTooSmallError> for Error<T> {
    #[inline]
    fn from(e: BufferTooSmallError) -> Self {
        Self::Buffer(e.into())
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<T> From<TryReserveError> for Error<T> {
    #[inline]
    fn from(e: TryReserveError) -> Self {
        Self::Buffer(e.into())
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<T> std::error::Error for Error<T>
where
    T: std::error::Error + 'static,
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Buffer(e) => Some(e),
            Error::Process(e) => Some(e),
        }
    }
}
