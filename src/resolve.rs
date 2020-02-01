//! URI and IRI resolvers.
//!
//! Enabled by `alloc` or `std` feature.

pub use self::iri::resolve as resolve_iri;

mod iri;
