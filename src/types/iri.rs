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
    error::IriCreationError,
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

/// Sets the fragment part to the given string.
///
/// Removes fragment part (and following `#` character) if `None` is given.
fn set_fragment(s: &mut String, fragment: Option<&str>) {
    remove_fragment(s);
    if let Some(fragment) = fragment {
        s.reserve(fragment.len() + 1);
        s.push('#');
        s.push_str(fragment);
    }
}

/// Removes the prefix.
fn remove_fragment(s: &mut String) {
    if let Some(colon_pos) = s.find('#') {
        s.truncate(colon_pos);
    }
}
