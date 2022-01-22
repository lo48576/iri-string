//! Buffer error.

use core::fmt;

#[cfg(feature = "alloc")]
use alloc::collections::TryReserveError;

/// A buffer error.
///
/// For detail about resolution failure, see [the module documentation][`crate::resolve`].
#[derive(Debug, Clone)]
pub struct Error {
    /// Inner error representation.
    // Use indirect private type to make `BufferTooSmallError` private.
    // Note, however, the value of `BufferTooSmallError` can be exposed as
    // `&std::error::Error` through `std::error::Error::source()`.
    repr: ErrorRepr,
}

impl fmt::Display for Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.repr {
            #[cfg(feature = "alloc")]
            ErrorRepr::Allocate(_) => f.write_str("memory allocation failed"),
            ErrorRepr::BufferFull(_) => f.write_str("buffer full"),
        }
    }
}

impl From<BufferTooSmallError> for Error {
    #[inline]
    fn from(e: BufferTooSmallError) -> Self {
        Self {
            repr: ErrorRepr::BufferFull(e),
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl From<TryReserveError> for Error {
    #[inline]
    fn from(e: TryReserveError) -> Self {
        Self {
            repr: ErrorRepr::Allocate(e),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.repr {
            #[cfg(feature = "alloc")]
            ErrorRepr::Allocate(e) => Some(e),
            ErrorRepr::BufferFull(e) => Some(e),
        }
    }
}

/// Internal representation of `Error`.
#[derive(Debug, Clone)]
pub(crate) enum ErrorRepr {
    /// Memory allocation error for `alloc` stuff.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    Allocate(TryReserveError),
    /// Memory allocation error for fixed-size buffer.
    BufferFull(BufferTooSmallError),
}

/// An error indicating that the buffer is too small.
#[derive(Debug, Clone, Copy)]
pub(crate) struct BufferTooSmallError(());

impl BufferTooSmallError {
    /// Creates a new error.
    #[inline]
    #[must_use]
    pub(super) fn new() -> Self {
        Self(())
    }
}

impl fmt::Display for BufferTooSmallError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("destination buffer does not have enough capacity")
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for BufferTooSmallError {}
