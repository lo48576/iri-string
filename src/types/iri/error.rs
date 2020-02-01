//! Error.

use core::fmt;

#[cfg(feature = "std")]
use std::error;

use crate::validate::iri::Error;

/// Error on conversion into an IRI type.
///
/// Enabled by `alloc` or `std` feature.
// This type itself does not require `alloc` or `std, but the type is used only when `alloc`
// feature is enabled. To avoid exporting unused type, the type (and the `types::iri::error`
// module) is available only when `alloc` feature is enabled.
#[derive(Debug, Clone)]
pub struct IriCreationError<T> {
    /// Soruce data.
    source: T,
    /// Validation error.
    error: Error,
}

impl<T> IriCreationError<T> {
    /// Returns the source data.
    pub fn into_source(self) -> T {
        self.source
    }

    /// Returns validation error.
    pub fn validation_error(&self) -> Error {
        self.error
    }

    /// Creates a new `Error`.
    pub(crate) fn new(error: Error, source: T) -> Self {
        Self { source, error }
    }
}

impl<T> fmt::Display for IriCreationError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error.fmt(f)
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug> error::Error for IriCreationError<T> {}
