//! IRI reference.

#[cfg(feature = "alloc")]
use alloc::string::String;

use core::convert::TryFrom;

#[cfg(feature = "alloc")]
use alloc::borrow::Cow;

#[cfg(feature = "serde")]
use serde::Serialize;
#[cfg(feature = "alloc")]
use validated_slice::OwnedSliceSpec;
use validated_slice::SliceSpec;

#[cfg(feature = "alloc")]
use crate::{
    manipulation::raw::set_fragment,
    resolve::resolve_iri,
    spec::IriSpec,
    types::{AbsoluteIriStr, IriCreationError, IriString, RelativeIriString},
    validate::iri as validate_iri,
};
use crate::{
    manipulation::CustomIriSliceExt,
    types::{IriFragmentStr, IriStr, RelativeIriStr},
    validate::{iri::Error, iri_reference},
};

/// A borrowed slice of an IRI reference.
///
/// This corresponds to `IRI-reference` rule in [RFC 3987].
/// This is `IRI / irelative-ref`
/// In other words, this is union of `IriStr` and `RelativeIriStr.
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[allow(clippy::derive_hash_xor_eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriReferenceStr(str);

impl IriReferenceStr {
    /// Creates a new `&IriReferenceStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::types::IriReferenceStr;
    /// assert!(IriReferenceStr::new("https://user:pass@example.com:8080").is_ok());
    /// assert!(IriReferenceStr::new("https://example.com/").is_ok());
    /// assert!(IriReferenceStr::new("https://example.com/foo?bar=baz").is_ok());
    /// assert!(IriReferenceStr::new("https://example.com/foo?bar=baz#qux").is_ok());
    /// assert!(IriReferenceStr::new("foo:bar").is_ok());
    /// assert!(IriReferenceStr::new("foo:").is_ok());
    /// // `foo://.../` below are all allowed. See the crate documentation for detail.
    /// assert!(IriReferenceStr::new("foo:/").is_ok());
    /// assert!(IriReferenceStr::new("foo://").is_ok());
    /// assert!(IriReferenceStr::new("foo:///").is_ok());
    /// assert!(IriReferenceStr::new("foo:////").is_ok());
    /// assert!(IriReferenceStr::new("foo://///").is_ok());
    /// assert!(IriReferenceStr::new("foo/bar").is_ok());
    /// assert!(IriReferenceStr::new("/foo/bar").is_ok());
    /// assert!(IriReferenceStr::new("//foo/bar").is_ok());
    /// assert!(IriReferenceStr::new("#foo").is_ok());
    ///
    /// // `<` and `>` cannot directly appear in an IRI.
    /// assert!(IriReferenceStr::new("<not allowed>").is_err());
    /// ```
    pub fn new(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&IriReferenceStr` maybe without validation.
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

    /// Returns the string as `&IriStr`, if it is valid as an IRI.
    ///
    /// If it is not an IRI, then `&RelativeIriStr` is returned as `Err(_)`.
    pub fn to_iri(&self) -> Result<&IriStr, &RelativeIriStr> {
        // Check with `IRI` rule first, because of the syntax.
        //
        // > Some productions are ambiguous. The "first-match-wins" (a.k.a.
        // > "greedy") algorithm applies. For details, see [RFC3986].
        // >
        // > --- <https://tools.ietf.org/html/rfc3987#section-2.2>.
        <&IriStr>::try_from(self.as_str()).map_err(|_| unsafe {
            // This is safe because of the syntax rule
            // `IRI-reference = IRI / irelative-ref`.
            // It says that if an IRI reference is not an IRI, then it is
            // a relative IRI.
            RelativeIriStr::new_unchecked(self.as_str())
        })
    }

    /// Returns the string as `&RelativeIriStr`, if it is valid as an IRI.
    ///
    /// If it is not an IRI, then `&IriStr` is returned as `Err(_)`.
    pub fn to_relative_iri(&self) -> Result<&RelativeIriStr, &IriStr> {
        match self.to_iri() {
            Ok(iri) => Err(iri),
            Err(relative) => Ok(relative),
        }
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
    ///
    /// Enabled by `alloc` or `std` feature.
    #[cfg(feature = "alloc")]
    pub fn resolve_against(&self, base: &AbsoluteIriStr) -> Cow<'_, IriStr> {
        match self.to_iri() {
            Ok(iri) => Cow::Borrowed(iri),
            Err(relative) => Cow::Owned(resolve_iri(relative, base, true)),
        }
    }

    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, IriReferenceStr}, validate::iri::Error};
    /// let iri = IriReferenceStr::new("foo://bar/baz?qux=quux#corge")?;
    /// let fragment = IriFragmentStr::new("corge")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, IriReferenceStr}, validate::iri::Error};
    /// let iri = IriReferenceStr::new("foo://bar/baz?qux=quux#")?;
    /// let fragment = IriFragmentStr::new("")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::IriReferenceStr, validate::iri::Error};
    /// let iri = IriReferenceStr::new("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::{IriFragmentStr, IriReferenceStr}, validate::iri::Error};
    /// let iri = IriReferenceStr::new("#foo")?;
    /// let fragment = IriFragmentStr::new("foo")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::IriReferenceStr, validate::iri::Error};
    /// let iri = IriReferenceStr::new("")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn fragment(&self) -> Option<&IriFragmentStr> {
        CustomIriSliceExt::fragment(self)
    }
}

/// An owned string of an IRI reference.
///
/// This corresponds to `IRI-reference` rule in [RFC 3987].
/// This is `IRI / irelative-ref`
/// In other words, this is union of `IriString` and `RelativeIriString.
///
/// See documentation for [`IriReferenceStr`].
///
/// Enabled by `alloc` or `std` feature.
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [`IriReferenceStr`]: struct.IriReferenceStr.html
#[cfg(feature = "alloc")]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriReferenceString(String);

#[cfg(feature = "alloc")]
impl IriReferenceString {
    /// Creates a new `IriReferenceString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(StrSpec::validate(&s), Ok(()));
        StringSpec::from_inner_unchecked(s)
    }

    /// Returns the string as `IriString`, if it is valid as an IRI.
    ///
    /// If it is not an IRI, then `RelativeIriString` is returned as `Err(_)`.
    pub fn into_iri(self) -> Result<IriString, RelativeIriString> {
        let s: String = self.into();
        // Check with `IRI` rule first, because of the syntax.
        //
        // > Some productions are ambiguous. The "first-match-wins" (a.k.a.
        // > "greedy") algorithm applies. For details, see [RFC3986].
        // >
        // > --- <https://tools.ietf.org/html/rfc3987#section-2.2>.
        if validate_iri::<IriSpec>(&s).is_ok() {
            Ok(unsafe {
                // This is safe because `s` is already validated by condition
                // of `if`.
                IriString::new_always_unchecked(s)
            })
        } else {
            Err(unsafe {
                // This is safe because of the syntax rule
                // `IRI-reference = IRI / irelative-ref`.
                // It says that if an IRI reference is not an IRI, then it is
                // a relative IRI.
                RelativeIriString::new_unchecked(s)
            })
        }
    }

    /// Returns the string as `RelativeIriString`, if it is valid as an IRI.
    ///
    /// If it is not an IRI, then `IriString` is returned as `Err(_)`.
    pub fn into_relative_iri(self) -> Result<RelativeIriString, IriString> {
        match self.into_iri() {
            Ok(iri) => Err(iri),
            Err(relative) => Ok(relative),
        }
    }

    /// Sets the fragment part to the given string.
    ///
    /// Removes fragment part (and following `#` character) if `None` is given.
    pub fn set_fragment(&mut self, fragment: Option<&IriFragmentStr>) {
        set_fragment(&mut self.0, fragment.map(AsRef::as_ref));
        debug_assert!(iri_reference::<IriSpec>(&self.0).is_ok());
    }

    /// Shrinks the capacity of the inner buffer to match its length.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl_basics! {
    Slice {
        spec: StrSpec,
        custom: IriReferenceStr,
        validator: iri_reference::<IriSpec>,
        error: Error,
    },
    Owned {
        spec: StringSpec,
        custom: IriReferenceString,
        error: IriCreationError<String>,
    },
}

validated_slice::impl_std_traits_for_slice! {
    Spec {
        spec: StrSpec,
        custom: IriReferenceStr,
        inner: str,
        error: Error,
    };
}

impl_serde! {
    expecting: "an IRI reference",
    slice: IriReferenceStr,
    owned: IriReferenceString,
}
