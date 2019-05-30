//! IRI types.
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

pub use self::{
    absolute::{AbsoluteIriStr, AbsoluteIriString},
    error::CreationError,
    fragment::{IriFragmentStr, IriFragmentString},
    normal::{IriStr, IriString},
    reference::{IriReferenceStr, IriReferenceString},
    relative::{RelativeIriStr, RelativeIriString},
};

mod absolute;
mod error;
mod fragment;
mod normal;
mod reference;
mod relative;
