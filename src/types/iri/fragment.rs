//! Fragment string.

use core::convert::TryFrom;

#[cfg(feature = "serde")]
use serde::Serialize;
#[cfg(feature = "std")]
use validated_slice::OwnedSliceSpec;
use validated_slice::SliceSpec;

#[cfg(feature = "std")]
use crate::types::IriCreationError;
use crate::validate::iri::{fragment, Error};

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
    /// # Examples
    ///
    /// ```
    /// # use iri_string::types::IriFragmentStr;
    /// assert!(IriFragmentStr::new("").is_ok());
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

    /// Creates a new `&IriFragmentStr` from the fragment part prefixed by `#`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::types::IriFragmentStr;
    /// assert!(IriFragmentStr::from_prefixed("#").is_ok());
    /// assert!(IriFragmentStr::from_prefixed("#foo").is_ok());
    /// assert!(IriFragmentStr::from_prefixed("#foo/bar").is_ok());
    /// assert!(IriFragmentStr::from_prefixed("#/foo/bar").is_ok());
    /// assert!(IriFragmentStr::from_prefixed("#//foo/bar").is_ok());
    /// assert!(IriFragmentStr::from_prefixed("#https://user:pass@example.com:8080").is_ok());
    /// assert!(IriFragmentStr::from_prefixed("#https://example.com/").is_ok());
    ///
    /// // `<` and `>` cannot directly appear in an IRI.
    /// assert!(IriFragmentStr::from_prefixed("#<not allowed>").is_err());
    /// // `#` prefix is expected.
    /// assert!(IriFragmentStr::from_prefixed("").is_err());
    /// assert!(IriFragmentStr::from_prefixed("foo").is_err());
    /// ```
    pub fn from_prefixed(s: &str) -> Result<&Self, Error> {
        if s.as_bytes().get(0) != Some(&b'#') {
            return Err(Error::new());
        }
        TryFrom::try_from(&s[1..])
    }

    /// Creates a new `IriFragmentStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(StrSpec::validate(s), Ok(()));
        StrSpec::from_inner_unchecked(s)
    }

    /// Returns `&str`.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }

    /// Returns the string length.
    #[inline]
    pub fn len(&self) -> usize {
        self.as_str().len()
    }

    /// Returns whether the string is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
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
#[cfg(feature = "std")]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriFragmentString(String);

#[cfg(feature = "std")]
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
