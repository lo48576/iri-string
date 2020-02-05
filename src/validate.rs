//! Validators.

use core::fmt;

#[cfg(feature = "std")]
use std::error;

use nom::combinator::all_consuming;

use crate::{parser, spec::Spec};

/// Resource identifier validation error.
// Note that this type should implement `Copy` trait.
// To return additional non-`Copy` data as an error, use wrapper type
// (as `std::string::FromUtf8Error` contains `std::str::Utf8Error`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Error(());

impl Error {
    /// Creates a new `Error`.
    ///
    /// For internal use.
    #[inline]
    pub(crate) fn new() -> Self {
        Error(())
    }
}

impl fmt::Display for Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Invalid IRI")
    }
}

#[cfg(feature = "std")]
impl error::Error for Error {}

/// Converts the given result into a validation result.
fn conv_err<T, E>(res: Result<T, E>) -> Result<(), Error> {
    match res {
        Ok(_) => Ok(()),
        Err(_) => Err(Error::new()),
    }
}

/// Validates [IRI][uri].
///
/// This validator corresponds to [`RiStr`] and [`RiString`] types.
///
/// [uri]: https://tools.ietf.org/html/rfc3986#section-3
/// [`RiStr`]: ../types/struct.RiStr.html
/// [`RiString`]: ../types/struct.RiString.html
pub fn iri<S: Spec>(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri::<(), S>)(s))
}

/// Validates [IRI reference][uri-reference].
///
/// This validator corresponds to [`RiReferenceStr`] and [`RiReferenceString`] types.
///
/// [uri-reference]: https://tools.ietf.org/html/rfc3986#section-4.1
/// [`RiReferenceStr`]: ../types/struct.RiReferenceStr.html
/// [`RiReferenceString`]: ../types/struct.RiReferenceString.html
pub fn iri_reference<S: Spec>(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri_reference::<(), S>)(s))
}

/// Validates [absolute IRI][absolute-uri].
///
/// This validator corresponds to [`RiAbsoluteStr`] and [`RiAbsoluteString`] types.
///
/// [absolute-uri]: https://tools.ietf.org/html/rfc3986#section-4.3
/// [`RiAbsoluteStr`]: ../types/struct.RiAbsoluteStr.html
/// [`RiAbsoluteString`]: ../types/struct.RiAbsoluteString.html
pub fn absolute_iri<S: Spec>(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::absolute_uri::<(), S>)(s))
}

/// Validates [relative reference][relative-ref].
///
/// This validator corresponds to [`RiRelativeStr`] and [`RiRelativeString`] types.
///
/// [relative-ref]: https://tools.ietf.org/html/rfc3986#section-4.2
/// [`RiRelativeStr`]: ../types/struct.RiRelativeStr.html
/// [`RiRelativeString`]: ../types/struct.RiRelativeString.html
pub fn relative_ref<S: Spec>(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::relative_ref::<(), S>)(s))
}

/// Validates [IRI path][path].
///
/// [path]: https://tools.ietf.org/html/rfc3986#section-3.3
pub fn path<S: Spec>(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::path::<(), S>)(s))
}

/// Validates [IRI fragment][fragment].
///
/// This validator corresponds to [`RiFragmentStr`] and [`RiFragmentString`] types.
///
/// Note that the first `#` character in an IRI is not a part of a fragment.
/// For example, `https://example.com/#foo` has a fragment `foo`, **not** `#foo`.
///
/// [fragment]: https://tools.ietf.org/html/rfc3986#section-3.5
/// [`RiFragmentStr`]: ../types/struct.RiFragmentStr.html
/// [`RiFragmentString`]: ../types/struct.RiFragmentString.html
pub fn fragment<S: Spec>(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::fragment::<(), S>)(s))
}
