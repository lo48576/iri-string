//! URI validator.

use std::{error, fmt};

use nom::combinator::all_consuming;

use crate::parser::{self, UriRule};

/// URI validation error.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Error(());

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Invalid URI")
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

/// Validates RFC 3986 URI.
pub fn uri(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri::<(), UriRule>)(s))
}

/// Validates RFC 3986 URI reference.
pub fn uri_reference(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri_reference::<(), UriRule>)(s))
}

/// Validates RFC 3986 absolute URI.
pub fn absolute_uri(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::absolute_uri::<(), UriRule>)(s))
}

/// Validates RFC 3986 relative reference.
pub fn relative_ref(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::relative_ref::<(), UriRule>)(s))
}

/// Validates RFC 3986 URI path.
pub fn path(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::path::<(), UriRule>)(s))
}
