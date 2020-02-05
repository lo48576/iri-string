//! Resource identifier creation error.

use core::{fmt, marker::PhantomData};

#[cfg(feature = "std")]
use std::error;

use crate::{spec::Spec, validate::Error};

/// Error on conversion into an IRI type.
///
/// Enabled by `alloc` or `std` feature.
// This type itself does not require `alloc` or `std, but the type is used only when `alloc`
// feature is enabled. To avoid exporting unused stuff, the type (and the `types::generic::error`
// module) is available only when necessary.
//
// Note that all types which implement `Spec` also implement `SpecInternal`.
pub struct CreationError<S, T> {
    /// Soruce data.
    source: T,
    /// Validation error.
    error: Error,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<S: Spec, T> CreationError<S, T> {
    /// Returns the source data.
    pub fn into_source(self) -> T {
        self.source
    }

    /// Returns the validation error.
    pub fn validation_error(&self) -> Error {
        self.error
    }

    /// Creates a new `CreationError`.
    pub(crate) fn new(error: Error, source: T) -> Self {
        Self {
            source,
            error,
            _spec: PhantomData,
        }
    }
}

impl<S: Spec, T: fmt::Debug> fmt::Debug for CreationError<S, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CreationError")
            .field("source", &self.source)
            .field("error", &self.error)
            .finish()
    }
}

impl<S: Spec, T: Clone> Clone for CreationError<S, T> {
    fn clone(&self) -> Self {
        Self {
            source: self.source.clone(),
            error: self.error,
            _spec: PhantomData,
        }
    }
}

impl<S: Spec, T> fmt::Display for CreationError<S, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error.fmt(f)
    }
}

#[cfg(feature = "std")]
impl<S: Spec, T: fmt::Debug> error::Error for CreationError<S, T> {}
