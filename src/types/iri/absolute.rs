//! Absolute IRI.

use std::{convert::TryFrom, fmt};

#[cfg(feature = "serde")]
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize,
};

use crate::{
    types::{CreationError, IriReferenceStr, IriReferenceString, IriStr, IriString},
    validate::iri::{absolute_iri, Error},
};

custom_slice_macros::define_slice_types_pair! {
    /// An owned string of an absolute IRI.
    ///
    /// This corresponds to `absolute-IRI` rule in RFC 3987.
    /// This is `scheme ":" ihier-part [ "?" iquery ]`.
    /// In other words, this is `IriString` without fragment part.
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
            /// Creates a new `AbsoluteIriString` without validation.
            unsafe fn new_always_unchecked
        ")]
    pub struct AbsoluteIriString(String);

    /// A borrowed slice of an absolute IRI.
    ///
    /// This corresponds to `absolute-IRI` rule in RFC 3987.
    /// This is `scheme ":" ihier-part [ "?" iquery ]`.
    /// In other words, this is `IriStr` without fragment part.
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
            /// Creates a new `&AbsoluteIriStr` without validation.
            unsafe fn new_always_unchecked
        ")]
    pub struct AbsoluteIriStr(str);

    /// Validates the given string as an absolute IRI.
    #[custom_slice(validator)]
    fn validate(s: &str) -> Result<(), Error> {
        absolute_iri(s)
    }
}

impl AbsoluteIriString {
    /// Creates a new `AbsoluteIriString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(validate(&s), Ok(()));
        Self::new_always_unchecked(s)
    }

    /// Shrinks the capacity of the inner buffer to match its length.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl AbsoluteIriStr {
    /// Creates a new `&AbsoluteIriStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(validate(s), Ok(()));
        Self::new_always_unchecked(s)
    }

    /// Returns `&str`.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

impl std::ops::Deref for AbsoluteIriStr {
    type Target = IriStr;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl fmt::Display for AbsoluteIriString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<AbsoluteIriStr>::as_ref(self).fmt(f)
    }
}

impl fmt::Display for &AbsoluteIriStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl std::str::FromStr for AbsoluteIriString {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        <&AbsoluteIriStr>::try_from(s).map(ToOwned::to_owned)
    }
}

impl_std_traits! {
    source: {
        owned: AbsoluteIriString,
        slice: AbsoluteIriStr,
        creation_error: CreationError,
        validation_error: Error,
    },
    target: [
        {
            owned: IriString,
            slice: IriStr,
        },
        {
            owned: IriReferenceString,
            slice: IriReferenceStr,
        },
    ],
}

/// `AbsoluteIriString` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct AbsoluteIriStringVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for AbsoluteIriStringVisitor {
    type Value = AbsoluteIriString;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an absolute IRI")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&AbsoluteIriStr>::try_from(v)
            .map(ToOwned::to_owned)
            .map_err(E::custom)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        AbsoluteIriString::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for AbsoluteIriString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(AbsoluteIriStringVisitor)
    }
}

/// `AbsoluteIriStr` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct AbsoluteIriStrVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for AbsoluteIriStrVisitor {
    type Value = &'de AbsoluteIriStr;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an absolute IRI")
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&'de AbsoluteIriStr>::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de: 'a, 'a> Deserialize<'de> for &'a AbsoluteIriStr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_string(AbsoluteIriStrVisitor)
    }
}
