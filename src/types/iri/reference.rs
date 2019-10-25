//! IRI reference.

use std::{convert::TryFrom, fmt};

#[cfg(feature = "serde")]
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize,
};
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    resolve::resolve_iri,
    types::{
        iri::set_fragment, AbsoluteIriStr, CreationError, IriFragmentStr, IriStr, IriString,
        RelativeIriStr, RelativeIriString,
    },
    validate::iri::{iri as validate_iri, iri_reference, Error},
};

/// Spec of `IriReferenceStr`.
enum StrSpec {}

impl SliceSpec for StrSpec {
    type Custom = IriReferenceStr;
    type Inner = str;
    type Error = Error;

    #[inline]
    fn validate(s: &Self::Inner) -> Result<(), Self::Error> {
        iri_reference(s)
    }

    validated_slice::impl_slice_spec_methods! {
        field=0;
        methods=[
            as_inner,
            as_inner_mut,
            from_inner_unchecked,
            from_inner_unchecked_mut,
        ];
    }
}

validated_slice::impl_std_traits_for_slice! {
    Spec {
        spec: StrSpec,
        custom: IriReferenceStr,
        inner: str,
        error: Error,
    };
    { AsRef<str> };
    { AsRef<{Custom}> };
    { From<&{Custom}> for Arc<{Custom}> };
    { From<&{Custom}> for Box<{Custom}> };
    { From<&{Custom}> for Rc<{Custom}> };
    { TryFrom<&{Inner}> for &{Custom} };
    { Default for &{Custom} };
    { Display };
    { Deref<Target = {Inner}> };
}

validated_slice::impl_cmp_for_slice! {
    Spec {
        spec: StrSpec,
        custom: IriReferenceStr,
        inner: str,
        base: Inner,
    };
    Cmp { PartialEq, PartialOrd };
    { ({Custom}), (&{Custom}), rev };
    { ({Custom}), (Cow<{Custom}>), rev };

    { ({Custom}), ({Inner}), rev };
    { ({Custom}), (&{Inner}), rev };
    { (&{Custom}), ({Inner}), rev };
    { ({Custom}), (Cow<{Inner}>), rev };
    { (&{Custom}), (Cow<{Inner}>), rev };
}

/// Spec of `IriReferenceString`.
enum StringSpec {}

impl OwnedSliceSpec for StringSpec {
    type Custom = IriReferenceString;
    type Inner = String;
    type Error = CreationError<Self::Inner>;
    type SliceSpec = StrSpec;
    type SliceCustom = IriReferenceStr;
    type SliceInner = str;
    type SliceError = Error;

    #[inline]
    fn convert_validation_error(e: Self::SliceError, v: Self::Inner) -> Self::Error {
        CreationError::new(e, v)
    }

    #[inline]
    fn as_slice_inner(s: &Self::Custom) -> &Self::SliceInner {
        &s.0
    }

    #[inline]
    fn as_slice_inner_mut(s: &mut Self::Custom) -> &mut Self::SliceInner {
        &mut s.0
    }

    #[inline]
    fn inner_as_slice_inner(s: &Self::Inner) -> &Self::SliceInner {
        s
    }

    #[inline]
    unsafe fn from_inner_unchecked(s: Self::Inner) -> Self::Custom {
        IriReferenceString(s)
    }

    #[inline]
    fn into_inner(s: Self::Custom) -> Self::Inner {
        s.0
    }
}

validated_slice::impl_std_traits_for_owned_slice! {
    Spec {
        spec: StringSpec,
        custom: IriReferenceString,
        inner: String,
        error: CreationError<String>,
        slice_custom: IriReferenceStr,
        slice_inner: str,
        slice_error: Error,
    };
    { Borrow<str> };
    { Borrow<{SliceCustom}> };
    { ToOwned<Owned = {Custom}> for {SliceCustom} };
    { AsRef<str> };
    { AsRef<{SliceCustom}> };
    { From<{Custom}> for {Inner} };
    { TryFrom<{Inner}> };
    { Display };
    { Deref<Target = {SliceCustom}> };
    { FromStr };
}

validated_slice::impl_cmp_for_owned_slice! {
    Spec {
        spec: StringSpec,
        custom: IriReferenceString,
        inner: String,
        slice_custom: IriReferenceStr,
        slice_inner: str,
        base: Inner,
    };
    Cmp { PartialEq, PartialOrd };
    { ({Custom}), ({SliceCustom}), rev };
    { ({Custom}), (&{SliceCustom}), rev };
    { ({Custom}), (Cow<{SliceCustom}>), rev };
    { ({Custom}), ({SliceInner}), rev };
    { ({Custom}), (&{SliceInner}), rev };
    { ({Custom}), (Cow<{SliceInner}>), rev };
}

/// An owned string of an IRI reference.
///
/// This corresponds to `IRI-reference` rule in RFC 3987.
/// This is `IRI / irelative-ref`
/// In other words, this is union of `IriString` and `RelativeIriString.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
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
pub struct IriReferenceStr(str);

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

    /// Sets the fragment part to the given string.
    ///
    /// Removes fragment part (and following `#` character) if `None` is given.
    pub fn set_fragment(&mut self, fragment: Option<&IriFragmentStr>) {
        set_fragment(&mut self.0, fragment.map(AsRef::as_ref));
        debug_assert!(iri_reference(&self.0).is_ok());
    }

    /// Shrinks the capacity of the inner buffer to match its length.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl IriReferenceStr {
    /// Creates a new `&IriReferenceStr`.
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
            RelativeIriStr::new_unchecked(self)
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

    /// Returns `&str`.
    pub fn as_str(&self) -> &str {
        self.as_ref()
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
