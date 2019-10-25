//! Fragment string.

use std::{convert::TryFrom, fmt};

#[cfg(feature = "serde")]
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize,
};
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    types::CreationError,
    validate::iri::{fragment, Error},
};

/// Spec of `IriFragmentStr`.
enum StrSpec {}

impl SliceSpec for StrSpec {
    type Custom = IriFragmentStr;
    type Inner = str;
    type Error = Error;

    #[inline]
    fn validate(s: &Self::Inner) -> Result<(), Self::Error> {
        fragment(s)
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
        custom: IriFragmentStr,
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
}

validated_slice::impl_cmp_for_slice! {
    Spec {
        spec: StrSpec,
        custom: IriFragmentStr,
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

/// Spec of `IriFragmentString`.
enum StringSpec {}

impl OwnedSliceSpec for StringSpec {
    type Custom = IriFragmentString;
    type Inner = String;
    type Error = CreationError<Self::Inner>;
    type SliceSpec = StrSpec;
    type SliceCustom = IriFragmentStr;
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
        IriFragmentString(s)
    }

    #[inline]
    fn into_inner(s: Self::Custom) -> Self::Inner {
        s.0
    }
}

validated_slice::impl_std_traits_for_owned_slice! {
    Spec {
        spec: StringSpec,
        custom: IriFragmentString,
        inner: String,
        error: CreationError<String>,
        slice_custom: IriFragmentStr,
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
        custom: IriFragmentString,
        inner: String,
        slice_custom: IriFragmentStr,
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

/// An owned string of an IRI fragment.
///
/// This corresponds to `ifragment` rule in RFC 3987.
/// This is `*( ipchar / "/" / "?" )`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriFragmentString(String);

/// A borrowed slice of an IRI.
///
/// This corresponds to `ifragment` rule in RFC 3987.
/// This is `*( ipchar / "/" / "?" )`.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[allow(clippy::derive_hash_xor_eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriFragmentStr(str);

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

impl IriFragmentStr {
    /// Creates a new `&IriFragmentStr`.
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

impl_std_traits! {
    source: {
        owned: IriFragmentString,
        slice: IriFragmentStr,
        creation_error: CreationError,
        validation_error: Error,
    },
    target: [],
}

/// `IriFragmentString` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct IriFragmentStringVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for IriFragmentStringVisitor {
    type Value = IriFragmentString;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an IRI fragment")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&IriFragmentStr>::try_from(v)
            .map(ToOwned::to_owned)
            .map_err(E::custom)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        IriFragmentString::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for IriFragmentString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(IriFragmentStringVisitor)
    }
}

/// `IriStr` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct IriFragmentStrVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for IriFragmentStrVisitor {
    type Value = &'de IriFragmentStr;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an IRI fragment")
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&'de IriFragmentStr>::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de: 'a, 'a> Deserialize<'de> for &'a IriFragmentStr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_string(IriFragmentStrVisitor)
    }
}
