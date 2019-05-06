//! IRI validator.

use std::{error, fmt};

use nom::combinator::all_consuming;

use crate::parser::{self, IriRule};

/// IRI validation error.
#[derive(Debug, PartialEq, Eq, Hash)]
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

/// Validates RFC 3987 IRI.
pub fn iri(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri::<(), IriRule>)(s))
}

/// Validates RFC 3987 IRI reference.
pub fn iri_reference(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::uri_reference::<(), IriRule>)(s))
}

/// Validates RFC 3987 absolute IRI.
pub fn absolute_iri(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::absolute_uri::<(), IriRule>)(s))
}

/// Validates RFC 3987 relative reference.
pub fn relative_ref(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::relative_ref::<(), IriRule>)(s))
}

/// Validates RFC 3987 IRI path.
pub fn path(s: &str) -> Result<(), Error> {
    conv_err(all_consuming(parser::path::<(), IriRule>)(s))
}
