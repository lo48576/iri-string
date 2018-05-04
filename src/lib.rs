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

pub mod absolute;
