//! Absolute IRI.

use std::convert::TryFrom;
#[cfg(feature = "serde")]
use std::fmt;

#[cfg(feature = "serde")]
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize,
};
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    types::{CreationError, IriReferenceStr, IriReferenceString, IriStr, IriString},
    validate::iri::{absolute_iri, Error},
};

impl_basics! {
    Slice {
        spec: StrSpec,
        custom: AbsoluteIriStr,
        validator: absolute_iri,
        error: Error,
    },
    Owned {
        spec: StringSpec,
        custom: AbsoluteIriString,
        error: CreationError<String>,
    },
}

/// An owned string of an absolute IRI.
///
/// This corresponds to `absolute-IRI` rule in RFC 3987.
/// This is `scheme ":" ihier-part [ "?" iquery ]`.
/// In other words, this is `IriString` without fragment part.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
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
pub struct AbsoluteIriStr(str);

impl AbsoluteIriString {
    /// Creates a new `AbsoluteIriString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(StrSpec::validate(&s), Ok(()));
        StringSpec::from_inner_unchecked(s)
    }

    /// Shrinks the capacity of the inner buffer to match its length.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl AbsoluteIriStr {
    /// Creates a new `&AbsoluteIriStr`.
    pub fn new(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `&AbsoluteIriStr` maybe without validation.
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

impl std::ops::Deref for AbsoluteIriStr {
    type Target = IriStr;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl_conv_and_cmp! {
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
