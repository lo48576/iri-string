//! Relative IRI.

use core::convert::TryFrom;

#[cfg(feature = "serde")]
use serde::Serialize;
#[cfg(feature = "std")]
use validated_slice::OwnedSliceSpec;
use validated_slice::SliceSpec;

#[cfg(feature = "std")]
use crate::{
    manipulation::raw::set_fragment,
    resolve::resolve_iri,
    types::{AbsoluteIriStr, IriCreationError, IriReferenceString, IriString},
};
use crate::{
    manipulation::CustomIriSliceExt,
    types::{IriFragmentStr, IriReferenceStr},
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
    /// // The first path component can have colon if the path is absolute.
    /// assert!(RelativeIriStr::new("/foo:bar/").is_ok());
    /// // Second or following path components can have colon.
    /// assert!(RelativeIriStr::new("foo/bar://baz/").is_ok());
    ///
    /// // Absolute IRI is not allowed.
    /// assert!(RelativeIriStr::new("https://example.com/").is_err());
    /// assert!(RelativeIriStr::new("foo:bar").is_err());
    /// // `<` and `>` cannot directly appear in an IRI.
    /// assert!(RelativeIriStr::new("<not allowed>").is_err());
    /// // The first path component cannot have colon, if the path is not absolute.
    /// assert!(RelativeIriStr::new("foo:").is_err());
    /// assert!(RelativeIriStr::new("foo:/").is_err());
    /// assert!(RelativeIriStr::new("foo://").is_err());
    /// assert!(RelativeIriStr::new("foo:///").is_err());
    /// assert!(RelativeIriStr::new("foo:////").is_err());
    /// assert!(RelativeIriStr::new("foo://///").is_err());
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

    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, RelativeIriStr}, validate::iri::Error};
    /// let iri = RelativeIriStr::new("?foo#bar")?;
    /// let fragment = IriFragmentStr::new("bar")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, RelativeIriStr}, validate::iri::Error};
    /// let iri = RelativeIriStr::new("#foo")?;
    /// let fragment = IriFragmentStr::new("foo")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::RelativeIriStr, validate::iri::Error};
    /// let iri = RelativeIriStr::new("")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn fragment(&self) -> Option<&IriFragmentStr> {
        CustomIriSliceExt::fragment(self)
    }

    /// Returns resolved IRI against the given base IRI, using strict resolver.
    ///
    /// About reference resolution output example, see [RFC 3986 section
    /// 5.4](https://tools.ietf.org/html/rfc3986#section-5.4).
    ///
    /// About resolver strictness, see [RFC 3986 section
    /// 5.4.2](https://tools.ietf.org/html/rfc3986#section-5.4.2):
    ///
    /// > Some parsers allow the scheme name to be present in a relative
    /// > reference if it is the same as the base URI scheme. This is considered
    /// > to be a loophole in prior specifications of partial URI
    /// > [RFC1630](https://tools.ietf.org/html/rfc1630). Its use should be
    /// avoided but is allowed for backward compatibility.
    /// >
    /// > --- <https://tools.ietf.org/html/rfc3986#section-5.4.2>
    ///
    /// Usual users will want to use strict resolver.
    #[cfg(feature = "std")]
    pub fn resolve_against(&self, base: &AbsoluteIriStr) -> IriString {
        resolve_iri(self, base, true)
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
#[cfg(feature = "std")]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct RelativeIriString(String);

#[cfg(feature = "std")]
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
