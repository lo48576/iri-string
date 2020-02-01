//! URI and IRI types.
//!
//! # IRI types
//!
//! Defined in [RFC 3987](https://tools.ietf.org/html/rfc3987).
//!
//! a URI (defined in [RFC 3986](https://tools.ietf.org/html/rfc3986)) is also
//! an IRI.
//!
//! ```text
//! IRI           = scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]
//! IRI-reference = IRI / irelative-ref
//! absolute-IRI  = scheme ":" ihier-part [ "?" iquery ]
//! irelative-ref = irelative-part [ "?" iquery ] [ "#" ifragment ]
//!     (`irelative-part` is roughly same as `ihier-part`.)
//! ```
//!
//! Hierarchy:
//!
//! ```text
//! IriReferenceStr
//! |-- IriStr
//! |   `-- AbsoluteIriStr
//! `-- RelativeIriStr
//! ```
//!
//! Therefore, the conversions below are safe and cheap:
//!
//! * `IriStr -> IriReferenceStr`
//! * `AbsoluteIriStr -> IriStr`
//! * `AbsoluteIriStr -> IriReferenceStr`
//! * `RelativeIriStr -> IriReferenceStr`
//!
//! For safely convertible types (consider `FooStr -> BarStr` is safe), traits
//! below are implemented:
//!
//! * `AsRef<BarStr> for FooStr`
//! * `AsRef<BarStr> for FooString`
//! * `From<FooString> for BarString`
//! * `PartialEq<FooStr> for BarStr` and lots of impls like that
//!     + `PartialEq` and `ParitalOrd`.
//!     + Slice, owned, `Cow`, reference, etc...
//!
//! # URI types
//!
//! Currently not implemented :-P.

pub use self::iri::{AbsoluteIriStr, IriFragmentStr, IriReferenceStr, IriStr, RelativeIriStr};
#[cfg(feature = "alloc")]
pub use self::iri::{
    AbsoluteIriString, IriCreationError, IriFragmentString, IriReferenceString, IriString,
    RelativeIriString,
};

#[macro_use]
mod macros;

mod iri;
