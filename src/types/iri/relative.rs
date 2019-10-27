//! Relative IRI.

use std::convert::TryFrom;

#[cfg(feature = "serde")]
use serde::Serialize;
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    types::{
        iri::set_fragment, IriCreationError, IriFragmentStr, IriReferenceStr, IriReferenceString,
    },
    validate::iri::{relative_ref, Error},
};

/// A borrowed slice of a relative IRI.
///
/// This corresponds to `irelative-ref` rule in [RFC 3987].
/// This is `irelative-part [ "?" iquery ] [ "#" fragment ]`.
/// In other words, this is roughly `IriStr` without scheme part.
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[allow(clippy::derive_hash_xor_eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct RelativeIriStr(str);

impl RelativeIriStr {
    /// Creates a new `&RelativeIriStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::types::RelativeIriStr;
    /// assert!(RelativeIriStr::new("foo").is_ok());
    /// assert!(RelativeIriStr::new("foo/bar").is_ok());
    /// assert!(RelativeIriStr::new("/foo").is_ok());
    /// assert!(RelativeIriStr::new("//foo/bar").is_ok());
    /// assert!(RelativeIriStr::new("?foo").is_ok());
    /// assert!(RelativeIriStr::new("#foo").is_ok());
    /// assert!(RelativeIriStr::new("foo/bar?baz#qux").is_ok());
    ///
    /// // Absolute IRI is not allowed.
    /// assert!(RelativeIriStr::new("https://example.com/").is_err());
    /// assert!(RelativeIriStr::new("foo:bar").is_err());
    /// // `<` and `>` cannot directly appear in an IRI.
    /// assert!(RelativeIriStr::new("<not allowed>").is_err());
    /// ```
    pub fn new(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&RelativeIriStr` maybe without validation.
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

/// An owned string of a relative IRI.
///
/// This corresponds to `irelative-ref` rule in [RFC 3987].
/// This is `irelative-part [ "?" iquery ] [ "#" fragment ]`.
/// In other words, this is roughly `IriString` without scheme part.
///
/// See documentation for [`RelativeIriStr`].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [`RelativeIriStr`]: struct.RelativeIriStr.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct RelativeIriString(String);

impl RelativeIriString {
    /// Creates a new `RelativeIriString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(StrSpec::validate(&s), Ok(()));
        StringSpec::from_inner_unchecked(s)
    }

    /// Sets the fragment part to the given string.
    ///
    /// Removes fragment part (and following `#` character) if `None` is given.
    pub fn set_fragment(&mut self, fragment: Option<&IriFragmentStr>) {
        set_fragment(&mut self.0, fragment.map(AsRef::as_ref));
        debug_assert!(relative_ref(&self.0).is_ok());
    }

    /// Shrinks the capacity of the inner buffer to match its length.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl_basics! {
    Slice {
        spec: StrSpec,
        custom: RelativeIriStr,
        validator: relative_ref,
        error: Error,
    },
    Owned {
        spec: StringSpec,
        custom: RelativeIriString,
        error: IriCreationError<String>,
    },
}

impl std::ops::Deref for RelativeIriStr {
    type Target = IriReferenceStr;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl_conv_and_cmp! {
    source: {
        owned: RelativeIriString,
        slice: RelativeIriStr,
        creation_error: IriCreationError,
        validation_error: Error,
    },
    target: [
        {
            owned: IriReferenceString,
            slice: IriReferenceStr,
        },
    ],
}

impl_serde! {
    expecting: "a relative IRI",
    slice: RelativeIriStr,
    owned: RelativeIriString,
}
