//! API for tasks.

use core::fmt;

#[cfg(feature = "alloc")]
use alloc::collections::TryReserveError;

use crate::buffer::{BufferTooSmallError, Error as BufferError};

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
