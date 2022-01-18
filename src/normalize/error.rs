//! Normalization and resolution error.

use core::fmt;

#[cfg(feature = "alloc")]
use alloc::collections::TryReserveError;

use crate::buffer::BufferTooSmallError;

/// IRI normalization and resolution error.
///
/// For detail about resolution failure, see [the module documentation][`crate::resolve`].
#[derive(Debug, Clone)]
pub struct Error {
    /// Inner error representation.
    repr: ErrorRepr,
}

impl Error {
    /// Returns the error kind.
    #[must_use]
    pub fn kind(&self) -> ErrorKind {
        match &self.repr {
            #[cfg(feature = "alloc")]
            ErrorRepr::Alloc(_) => ErrorKind::OutOfMemory,
            ErrorRepr::BufferFull(_) => ErrorKind::OutOfMemory,
            ErrorRepr::Unresolvable => ErrorKind::Unresolvable,
        }
    }
}

impl fmt::Display for Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.repr {
            #[cfg(feature = "alloc")]
            ErrorRepr::Alloc(_) => f.write_str("IRI resolution failed: allocation failed"),
            ErrorRepr::BufferFull(_) => f.write_str("IRI resolution failed: buffer full"),
            ErrorRepr::Unresolvable => {
                f.write_str("IRI resolution failed: unresolvable base and IRI pair")
            }
        }
    }
}

impl From<ErrorRepr> for Error {
    #[inline]
    fn from(repr: ErrorRepr) -> Self {
        Self { repr }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.repr {
            #[cfg(feature = "alloc")]
            ErrorRepr::Alloc(e) => Some(e),
            ErrorRepr::BufferFull(e) => Some(e),
            _ => None,
        }
    }
}

/// Internal representation of `ResolutionError`.
#[derive(Debug, Clone)]
pub(crate) enum ErrorRepr {
    /// Memory allocation error for `alloc` stuff.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    Alloc(TryReserveError),
    /// Memory allocation error for fixed-size buffer.
    BufferFull(BufferTooSmallError),
    /// Unresolvable base and reference.
    Unresolvable,
}

impl From<BufferTooSmallError> for ErrorRepr {
    #[inline]
    fn from(e: BufferTooSmallError) -> Self {
        Self::BufferFull(e)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl From<TryReserveError> for ErrorRepr {
    #[inline]
    fn from(e: TryReserveError) -> Self {
        Self::Alloc(e)
    }
}

/// Resolution error kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// Unresolvable base and reference.
    Unresolvable,
    /// Out of memory.
    OutOfMemory,
}
