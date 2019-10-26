//! Error.

use std::{error, fmt};

use crate::validate::iri::Error;

/// Error on converting from `String`.
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.error.fmt(f)
    }
}

impl<T: fmt::Debug> error::Error for IriCreationError<T> {}
