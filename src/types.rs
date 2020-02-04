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

use crate::spec::IriSpec;

#[cfg(feature = "alloc")]
pub use self::generic::{
    CreationError, RiAbsoluteString, RiFragmentString, RiReferenceString, RiRelativeString,
    RiString,
};
pub use self::generic::{RiAbsoluteStr, RiFragmentStr, RiReferenceStr, RiRelativeStr, RiStr};

#[allow(missing_docs, clippy::missing_docs_in_private_items)]
pub type AbsoluteIriStr = RiAbsoluteStr<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
#[cfg(feature = "alloc")]
pub type AbsoluteIriString = RiAbsoluteString<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
pub type IriFragmentStr = RiFragmentStr<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
#[cfg(feature = "alloc")]
pub type IriFragmentString = RiFragmentString<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
pub type IriStr = RiStr<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
#[cfg(feature = "alloc")]
pub type IriString = RiString<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
pub type IriReferenceStr = RiReferenceStr<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
#[cfg(feature = "alloc")]
pub type IriReferenceString = RiReferenceString<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
pub type RelativeIriStr = RiRelativeStr<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
#[cfg(feature = "alloc")]
pub type RelativeIriString = RiRelativeString<IriSpec>;
#[allow(missing_docs, clippy::missing_docs_in_private_items)]
#[cfg(feature = "alloc")]
pub type IriCreationError<T> = CreationError<IriSpec, T>;

pub(crate) mod generic;
