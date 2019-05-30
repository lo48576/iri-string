//! IRI reference.

use std::{convert::TryFrom, fmt};

#[cfg(feature = "serde")]
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize,
};

use crate::{
    resolve::resolve_iri,
    types::{
        AbsoluteIriStr, CreationError, IriFragmentStr, IriStr, IriString, RelativeIriStr,
        RelativeIriString,
    },
    validate::iri::{iri as validate_iri, iri_reference, Error},
};

custom_slice_macros::define_slice_types_pair! {
    /// An owned string of an IRI reference.
    ///
    /// This corresponds to `IRI-reference` rule in RFC 3987.
    /// This is `IRI / irelative-ref`
    /// In other words, this is union of `IriString` and `RelativeIriString.
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[cfg_attr(feature = "serde", derive(Serialize))]
    #[cfg_attr(feature = "serde", serde(transparent))]
    #[custom_slice(owned)]
    #[custom_slice(derive(
        AsRefSlice,
        AsRefSliceInner,
        Deref,
        IntoInner,
        PartialEqBulk,
        PartialEqInnerBulk,
        PartialOrdBulk,
        PartialOrdInnerBulk,
        TryFromInner,
    ))]
    #[custom_slice(error(type = "CreationError<String>", map = "{|e, v| CreationError::new(e, v)}"))]
    #[custom_slice(new_unchecked = "
            /// Creates a new `IriReferenceString` without validation.
            pub(crate) unsafe fn new_always_unchecked
        ")]
    pub struct IriReferenceString(String);

    /// A borrowed slice of an IRI reference.
    ///
    /// This corresponds to `IRI-reference` rule in RFC 3987.
    /// This is `IRI / irelative-ref`
    /// In other words, this is union of `IriStr` and `RelativeIriStr.
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    #[allow(clippy::derive_hash_xor_eq)]
    #[cfg_attr(feature = "serde", derive(Serialize))]
    #[cfg_attr(feature = "serde", serde(transparent))]
    #[custom_slice(slice)]
    #[custom_slice(derive(
        AsRefSlice,
        AsRefSliceInner,
        DefaultRef,
        Deref,
        PartialEqBulk,
        PartialEqInnerBulk,
        PartialOrdBulk,
        PartialOrdInnerBulk,
        IntoArc,
        IntoBox,
        IntoRc,
        TryFromInner,
    ))]
    #[custom_slice(error(type = "Error"))]
    #[custom_slice(new_unchecked = "
            /// Creates a new `&IriReferenceStr` without validation.
            pub(crate) unsafe fn new_always_unchecked
        ")]
    pub struct IriReferenceStr(str);

    /// Validates the given string as an IRI reference.
    #[custom_slice(validator)]
    fn validate(s: &str) -> Result<(), Error> {
        iri_reference(s)
    }
}

impl IriReferenceString {
    /// Creates a new `IriReferenceString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(validate(&s), Ok(()));
        Self::new_always_unchecked(s)
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
        if validate_iri(&s).is_ok() {
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

    /// Shrinks the capacity of the inner buffer to match its length.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl IriReferenceStr {
    /// Creates a new `&IriReferenceStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(validate(s), Ok(()));
        Self::new_always_unchecked(s)
    }

    /// Returns the string as `&IriStr`, if it is valid as an IRI.
    ///
    /// If it is not an IRI, then `&RelativeIriStr` is returned as `Err(_)`.
    pub fn to_iri(&self) -> Result<&IriStr, &RelativeIriStr> {
        let s: &str = self.as_ref();
        // Check with `IRI` rule first, because of the syntax.
        //
        // > Some productions are ambiguous. The "first-match-wins" (a.k.a.
        // > "greedy") algorithm applies. For details, see [RFC3986].
        // >
        // > --- <https://tools.ietf.org/html/rfc3987#section-2.2>.
        <&IriStr>::try_from(s).map_err(|_| unsafe {
            // This is safe because of the syntax rule
            // `IRI-reference = IRI / irelative-ref`.
            // It says that if an IRI reference is not an IRI, then it is
            // a relative IRI.
            RelativeIriStr::new_unchecked(s)
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

    /// Returns resolved IRI using strict resolver.
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
    pub fn resolve(&self, base: &AbsoluteIriStr) -> IriString {
        resolve_iri(self, base, true)
    }

    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::{IriFragmentStr, IriReferenceStr}, validate::iri::Error};
    /// let iri = <&IriReferenceStr>::try_from("foo://bar/baz?qux=quux#corge")?;
    /// let fragment = <&IriFragmentStr>::try_from("corge")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::{IriFragmentStr, IriReferenceStr}, validate::iri::Error};
    /// let iri = <&IriReferenceStr>::try_from("foo://bar/baz?qux=quux#")?;
    /// let fragment = <&IriFragmentStr>::try_from("")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriReferenceStr, validate::iri::Error};
    /// let iri = <&IriReferenceStr>::try_from("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::{IriFragmentStr, IriReferenceStr}, validate::iri::Error};
    /// let iri = <&IriReferenceStr>::try_from("#foo")?;
    /// let fragment = <&IriFragmentStr>::try_from("foo")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriReferenceStr, validate::iri::Error};
    /// let iri = <&IriReferenceStr>::try_from("")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn fragment(&self) -> Option<&IriFragmentStr> {
        let s: &str = self.as_ref();
        s.find('#').map(|colon_pos| unsafe {
            // This is safe because the fragment part of the valid
            // `IriReferenceStr` is guaranteed to be a valid fragment.
            IriFragmentStr::new_unchecked(&s[(colon_pos + 1)..])
        })
    }
}

impl fmt::Display for IriReferenceString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<IriReferenceStr>::as_ref(self).fmt(f)
    }
}

impl fmt::Display for &IriReferenceStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<str>::as_ref(self).fmt(f)
    }
}

impl std::str::FromStr for IriReferenceString {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        <&IriReferenceStr>::try_from(s).map(ToOwned::to_owned)
    }
}

/// `IriReferenceString` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct IriReferenceStringVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for IriReferenceStringVisitor {
    type Value = IriReferenceString;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an IRI reference")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&IriReferenceStr>::try_from(v)
            .map(ToOwned::to_owned)
            .map_err(E::custom)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        IriReferenceString::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for IriReferenceString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(IriReferenceStringVisitor)
    }
}

/// `IriReferenceStr` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct IriReferenceStrVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for IriReferenceStrVisitor {
    type Value = &'de IriReferenceStr;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an IRI reference")
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&'de IriReferenceStr>::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de: 'a, 'a> Deserialize<'de> for &'a IriReferenceStr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_string(IriReferenceStrVisitor)
    }
}
