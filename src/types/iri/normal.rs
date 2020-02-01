//! Usual absolute IRI (fragment part being allowed).

#[cfg(feature = "alloc")]
use alloc::string::String;

use core::convert::TryFrom;

#[cfg(feature = "serde")]
use serde::Serialize;
#[cfg(feature = "alloc")]
use validated_slice::OwnedSliceSpec;
use validated_slice::SliceSpec;

use crate::{
    manipulation::CustomIriSliceExt,
    types::{AbsoluteIriStr, IriFragmentStr, IriReferenceStr},
    validate::iri::{iri, Error},
};
#[cfg(feature = "alloc")]
use crate::{
    manipulation::{raw::set_fragment, CustomIriOwnedExt},
    types::{AbsoluteIriString, IriCreationError, IriFragmentString, IriReferenceString},
};

/// A borrowed string of an absolute IRI possibly with fragment part.
///
/// This corresponds to `IRI` rule in [RFC 3987].
/// This is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
/// In other words, this is `AbsoluteIriStr` with fragment part allowed.
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[allow(clippy::derive_hash_xor_eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriStr(str);

impl IriStr {
    /// Creates a new `&IriStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::types::IriStr;
    /// assert!(IriStr::new("https://user:pass@example.com:8080").is_ok());
    /// assert!(IriStr::new("https://example.com/").is_ok());
    /// assert!(IriStr::new("https://example.com/foo?bar=baz").is_ok());
    /// assert!(IriStr::new("https://example.com/foo?bar=baz#qux").is_ok());
    /// assert!(IriStr::new("foo:bar").is_ok());
    /// assert!(IriStr::new("foo:").is_ok());
    /// // `foo://.../` below are all allowed. See the crate documentation for detail.
    /// assert!(IriStr::new("foo:/").is_ok());
    /// assert!(IriStr::new("foo://").is_ok());
    /// assert!(IriStr::new("foo:///").is_ok());
    /// assert!(IriStr::new("foo:////").is_ok());
    /// assert!(IriStr::new("foo://///").is_ok());
    ///
    /// // Relative IRI is not allowed.
    /// assert!(IriStr::new("foo/bar").is_err());
    /// assert!(IriStr::new("/foo/bar").is_err());
    /// assert!(IriStr::new("//foo/bar").is_err());
    /// assert!(IriStr::new("#foo").is_err());
    /// // Empty string is not a valid IRI.
    /// assert!(IriStr::new("").is_err());
    /// ```
    pub fn new(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `IriStr` maybe without validation.
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
    ///
    /// Note that the length is always larger than 0, because all valid
    /// (non-relative) IRIs are not empty.
    #[inline]
    pub fn len(&self) -> usize {
        self.as_str().len()
    }

    /// Returns whether the string is empty, i.e. always returns `false`.
    ///
    /// Note that all valid (non-relative) IRIs are not empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Splits the IRI into absolute IRI part and fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, IriStr}, validate::iri::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#corge")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// let fragment_expected = IriFragmentStr::new("corge")?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, IriStr}, validate::iri::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// let fragment_expected = IriFragmentStr::new("")?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn to_absolute_and_fragment(&self) -> (&AbsoluteIriStr, Option<&IriFragmentStr>) {
        self.split_fragment()
    }

    /// Strips the fragment part if exists, and returns `&AbsoluteIriStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#corge")?;
    /// assert_eq!(iri.to_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.to_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    pub fn to_absolute(&self) -> &AbsoluteIriStr {
        self.without_fragment()
    }

    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, IriStr}, validate::iri::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#corge")?;
    /// let fragment = IriFragmentStr::new("corge")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, IriStr}, validate::iri::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#")?;
    /// let fragment = IriFragmentStr::new("")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn fragment(&self) -> Option<&IriFragmentStr> {
        CustomIriSliceExt::fragment(self)
    }
}

/// An owned string of an absolute IRI possibly with fragment part.
///
/// This corresponds to `IRI` rule in [RFC 3987].
/// This is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
/// In other words, this is `AbsoluteIriString` with fragment part allowed.
///
/// See documentation for [`IriStr`].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [`IriStr`]: struct.IriStr.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriString(String);

#[cfg(feature = "alloc")]
impl IriString {
    /// Creates a new `IriString` without validation.
    ///
    /// This does not validate the given string at any time.
    ///
    /// Intended for internal use.
    ///
    /// # Safety
    ///
    /// The given string must be a valid IRI string.
    pub(crate) unsafe fn new_always_unchecked(s: String) -> Self {
        StringSpec::from_inner_unchecked(s)
    }

    /// Creates a new `IriString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(StrSpec::validate(&s), Ok(()));
        StringSpec::from_inner_unchecked(s)
    }

    /// Splits the IRI into absolute IRI part and fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::types::{IriFragmentString, IriString};
    /// let iri = "foo://bar/baz?qux=quux#corge".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// let fragment_expected = IriFragmentString::try_from("corge".to_owned())
    ///     .map_err(|e| e.validation_error())?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, iri_string::validate::iri::Error>(())
    ///
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::types::{IriFragmentString, IriString};
    /// let iri = "foo://bar/baz?qux=quux#".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// let fragment_expected = IriFragmentString::try_from("".to_owned())
    ///     .map_err(|e| e.validation_error())?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, iri_string::validate::iri::Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::types::IriString;
    /// let iri = "foo://bar/baz?qux=quux".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, None);
    /// # Ok::<_, iri_string::validate::iri::Error>(())
    /// ```
    pub fn into_absolute_and_fragment(self) -> (AbsoluteIriString, Option<IriFragmentString>) {
        self.split_fragment()
    }

    /// Strips the fragment part if exists, and returns `AbsoluteIriString`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{types::IriString, validate::iri::Error};
    /// let iri = "foo://bar/baz?qux=quux#corge".parse::<IriString>()?;
    /// assert_eq!(iri.into_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::IriString, validate::iri::Error};
    /// let iri = "foo://bar/baz?qux=quux".parse::<IriString>()?;
    /// assert_eq!(iri.into_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    pub fn into_absolute(self) -> AbsoluteIriString {
        self.without_fragment()
    }

    /// Sets the fragment part to the given string.
    ///
    /// Removes fragment part (and following `#` character) if `None` is given.
    pub fn set_fragment(&mut self, fragment: Option<&IriFragmentStr>) {
        set_fragment(&mut self.0, fragment.map(AsRef::as_ref));
        debug_assert!(iri(&self.0).is_ok());
    }

    /// Shrinks the capacity of the inner buffer to match its length.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl_basics! {
    Slice {
        spec: StrSpec,
        custom: IriStr,
        validator: iri,
        error: Error,
    },
    Owned {
        spec: StringSpec,
        custom: IriString,
        error: IriCreationError<String>,
    },
}

impl_conv_and_cmp! {
    source: {
        owned: IriString,
        slice: IriStr,
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
    expecting: "an IRI",
    slice: IriStr,
    owned: IriString,
}
