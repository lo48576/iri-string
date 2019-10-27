//! Fragment string.

use std::convert::TryFrom;

#[cfg(feature = "serde")]
use serde::Serialize;
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    types::IriCreationError,
    validate::iri::{fragment, Error},
};

/// A borrowed slice of an IRI.
///
/// This corresponds to `ifragment` rule in [RFC 3987].
/// This is `*( ipchar / "/" / "?" )`.
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[allow(clippy::derive_hash_xor_eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriFragmentStr(str);

impl IriFragmentStr {
    /// Creates a new `&IriFragmentStr`.
    ///
    /// ```
    /// # use iri_string::types::IriFragmentStr;
    /// assert!(IriFragmentStr::new("foo").is_ok());
    /// assert!(IriFragmentStr::new("foo/bar").is_ok());
    /// assert!(IriFragmentStr::new("/foo/bar").is_ok());
    /// assert!(IriFragmentStr::new("//foo/bar").is_ok());
    /// assert!(IriFragmentStr::new("https://user:pass@example.com:8080").is_ok());
    /// assert!(IriFragmentStr::new("https://example.com/").is_ok());
    ///
    /// // `<` and `>` cannot directly appear in an IRI.
    /// assert!(IriFragmentStr::new("<not allowed>").is_err());
    /// ```
    pub fn new(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `IriFragmentStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(StrSpec::validate(s), Ok(()));
        StrSpec::from_inner_unchecked(s)
    }

    /// Returns `&str`.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// An owned string of an IRI fragment.
///
/// This corresponds to `ifragment` rule in [RFC 3987].
/// This is `*( ipchar / "/" / "?" )`.
///
/// See documentation for [`IriFragmentStr`].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [`IriFragmentStr`]: struct.IriFragmentStr.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriFragmentString(String);

impl IriFragmentString {
    /// Creates a new `IriFragmentString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(StrSpec::validate(&s), Ok(()));
        StringSpec::from_inner_unchecked(s)
    }

    /// Shrinks the capacity of the inner buffer to match its length.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl_basics! {
    Slice {
        spec: StrSpec,
        custom: IriFragmentStr,
        validator: fragment,
        error: Error,
    },
    Owned {
        spec: StringSpec,
        custom: IriFragmentString,
        error: IriCreationError<String>,
    },
}

impl_serde! {
    expecting: "an IRI fragment",
    slice: IriFragmentStr,
    owned: IriFragmentString,
}
