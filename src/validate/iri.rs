//! IRI validator.
//!
//! About IRI, see [RFC 3987 Internationalized Resource Identifiers (IRIs)][RFC 3987].
//!
//! [RFC 3987]: https://tools.ietf.org/html/rfc3987

use std::{error, fmt};

use nom::combinator::all_consuming;

use crate::parser::{self, IriRule};

/// [RFC 3987] IRI validation error.
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Error(());

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Invalid IRI")
    }
}

impl error::Error for Error {}

/// Converts the given result into a validation result.
fn conv_err<T, E>(res: Result<T, E>) -> Result<(), Error> {
    match res {
        Ok(_) => Ok(()),
        Err(_) => Err(Error(())),
    }
}

/// Validates [RFC 3987] [IRI][uri].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [uri]: https://tools.ietf.org/html/rfc3986#section-3
pub fn iri(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri::<(), IriRule>)(s))
}

/// Validates [RFC 3987] [IRI reference][uri-reference].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [uri-reference]: https://tools.ietf.org/html/rfc3986#section-4.1
pub fn iri_reference(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri_reference::<(), IriRule>)(s))
}

/// Validates [RFC 3987] [absolute IRI][absolute-uri].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [absolute-uri]: https://tools.ietf.org/html/rfc3986#section-4.3
pub fn absolute_iri(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::absolute_uri::<(), IriRule>)(s))
}

/// Validates [RFC 3987] [relative reference][relative-ref].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [relative-ref]: https://tools.ietf.org/html/rfc3986#section-4.2
pub fn relative_ref(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::relative_ref::<(), IriRule>)(s))
}

/// Validates [RFC 3987] [IRI path][path].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [path]: https://tools.ietf.org/html/rfc3986#section-3.3
pub fn path(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::path::<(), IriRule>)(s))
}

/// Validates [RFC 3987] [IRI fragment][fragment].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [fragment]: https://tools.ietf.org/html/rfc3986#section-3.5
pub fn fragment(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::fragment::<(), IriRule>)(s))
}
