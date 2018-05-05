//! String types for IRI.
//!
//! See [RFC 3987](https://tools.ietf.org/html/rfc3987) about IRI.
#![warn(missing_docs)]

#[cfg(feature = "serde")]
#[macro_use]
extern crate serde;
extern crate opaque_typedef;
#[macro_use]
extern crate opaque_typedef_macros;
extern crate url;

pub use url::ParseError as UrlParseError;
pub use url::Url;

pub use absolute::{AbsoluteIri, AbsoluteIriStr, AbsoluteIriString};
pub use relative::{RelativeIriParseError, RelativeIriStr, RelativeIriString};

pub mod absolute;
pub mod relative;


/// Checks if the string has colon before slash.
///
/// Precisely, this returns `true` iff:
///
/// * the string has colon character, and
/// * the string has no slash characters before the first colon.
fn has_colon_before_slash(s: &str) -> bool {
    s.find(|c| c == ':' || c == '/')
        .map_or(false, |pos| s.as_bytes()[pos] == b':')
}
