//! String types for [RFC 3987 IRI][RFC 3987].
//!
//! Note that this crate does not have any extra knowledge about protocols.
//! Comparisons between IRI strings by `PartialEq` and `Eq` is implemented as [simple string
//! comparison](https://tools.ietf.org/html/rfc3986#section-6.2.1).
//! You should implement by yourself or use another crate to use such extra knowledge to compare
//! IRIs.
//!
//! [RFC 3987]: https://tools.ietf.org/html/rfc3987
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

pub(crate) mod parser;
pub mod resolve;
pub mod types;
pub mod validate;
