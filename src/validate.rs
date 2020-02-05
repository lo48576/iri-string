//! Validators.

use core::{fmt, marker::PhantomData};

#[cfg(feature = "std")]
use std::error;

use nom::combinator::all_consuming;

use crate::{parser, spec::Spec};

/// Resource identifier validation error.
// Implement traits manually to accept all `S: Spec` (without other trait bounds).
pub struct Error<S>(PhantomData<fn() -> S>);

impl<S: Spec> Error<S> {
    /// Creates a new `Error`.
    ///
    /// For internal use.
    #[inline]
    pub(crate) fn new() -> Self {
        Error(PhantomData)
    }
}

// Implement manually to accept all `S: Spec` (without `fmt::Debug` bound).
impl<S: Spec> fmt::Debug for Error<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Error")
    }
}

impl<S: Spec> Clone for Error<S> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

// Note that this type should implement `Copy` trait.
// To return additional non-`Copy` data as an error, use wrapper type
// (as `std::string::FromUtf8Error` contains `std::str::Utf8Error`).
impl<S: Spec> Copy for Error<S> {}

impl<S: Spec> PartialEq for Error<S> {
    #[inline]
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl<S: Spec> Eq for Error<S> {}

impl<S: Spec> fmt::Display for Error<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Invalid IRI")
    }
}

#[cfg(feature = "std")]
impl<S: Spec> error::Error for Error<S> {}

/// Converts the given result into a validation result.
fn conv_err<T, E, S: Spec>(res: Result<T, E>) -> Result<(), Error<S>> {
    match res {
        Ok(_) => Ok(()),
        Err(_) => Err(Error::new()),
    }
}

/// Validates [IRI][uri].
///
/// [uri]: https://tools.ietf.org/html/rfc3986#section-3
pub fn iri<S: Spec>(s: &str) -> Result<(), Error<S>> {
    conv_err(all_consuming(parser::uri::<(), S>)(s))
}

/// Validates [IRI reference][uri-reference].
///
/// [uri-reference]: https://tools.ietf.org/html/rfc3986#section-4.1
pub fn iri_reference<S: Spec>(s: &str) -> Result<(), Error<S>> {
    conv_err(all_consuming(parser::uri_reference::<(), S>)(s))
}

/// Validates [absolute IRI][absolute-uri].
///
/// [absolute-uri]: https://tools.ietf.org/html/rfc3986#section-4.3
pub fn absolute_iri<S: Spec>(s: &str) -> Result<(), Error<S>> {
    conv_err(all_consuming(parser::absolute_uri::<(), S>)(s))
}

/// Validates [relative reference][relative-ref].
///
/// [relative-ref]: https://tools.ietf.org/html/rfc3986#section-4.2
pub fn relative_ref<S: Spec>(s: &str) -> Result<(), Error<S>> {
    conv_err(all_consuming(parser::relative_ref::<(), S>)(s))
}

/// Validates [IRI path][path].
///
/// [path]: https://tools.ietf.org/html/rfc3986#section-3.3
pub fn path<S: Spec>(s: &str) -> Result<(), Error<S>> {
    conv_err(all_consuming(parser::path::<(), S>)(s))
}

/// Validates [IRI fragment][fragment].
///
/// [fragment]: https://tools.ietf.org/html/rfc3986#section-3.5
pub fn fragment<S: Spec>(s: &str) -> Result<(), Error<S>> {
    conv_err(all_consuming(parser::fragment::<(), S>)(s))
}
