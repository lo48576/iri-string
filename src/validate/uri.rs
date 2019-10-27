//! URI validator.
//!
//! About URI, see [RFC 3986 Uniform Resource Identifiers (URI): Generic Syntax][RFC 3986].
//!
//! [RFC 3986]: https://tools.ietf.org/html/rfc3986

use std::{error, fmt};

use nom::combinator::all_consuming;

use crate::parser::{self, UriRule};

/// [RFC 3986] URI validation error.
///
/// [RFC 3986]: https://tools.ietf.org/html/rfc3986
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Error(());

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Invalid URI")
    }
}

impl error::Error for Error {}

/// Converts the given result into a validation result.
///
/// [RFC 3986]: https://tools.ietf.org/html/rfc3986
fn conv_err<T, E>(res: Result<T, E>) -> Result<(), Error> {
    match res {
        Ok(_) => Ok(()),
        Err(_) => Err(Error(())),
    }
}

/// Validates [RFC 3986] [URI][uri].
///
/// [RFC 3986]: https://tools.ietf.org/html/rfc3986
/// [uri]: https://tools.ietf.org/html/rfc3986#section-3
pub fn uri(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri::<(), UriRule>)(s))
}

/// Validates [RFC 3986] [URI reference][uri-reference].
///
/// [RFC 3986]: https://tools.ietf.org/html/rfc3986
/// [uri-reference]: https://tools.ietf.org/html/rfc3986#section-4.1
pub fn uri_reference(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri_reference::<(), UriRule>)(s))
}

/// Validates [RFC 3986] [absolute URI][absolute-uri].
///
/// [RFC 3986]: https://tools.ietf.org/html/rfc3986
/// [absolute-uri]: https://tools.ietf.org/html/rfc3986#section-4.3
pub fn absolute_uri(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::absolute_uri::<(), UriRule>)(s))
}

/// Validates [RFC 3986] [relative reference][relative-ref].
///
/// [RFC 3986]: https://tools.ietf.org/html/rfc3986
/// [relative-ref]: https://tools.ietf.org/html/rfc3986#section-4.2
pub fn relative_ref(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::relative_ref::<(), UriRule>)(s))
}

/// Validates [RFC 3986] [URI path][path].
///
/// [RFC 3986]: https://tools.ietf.org/html/rfc3986
/// [path]: https://tools.ietf.org/html/rfc3986#section-3.3
pub fn path(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::path::<(), UriRule>)(s))
}
