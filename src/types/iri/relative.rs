//! Relative IRI.

use std::{convert::TryFrom, fmt};

#[cfg(feature = "serde")]
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize,
};
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    types::{
        iri::set_fragment, CreationError, IriFragmentStr, IriReferenceStr, IriReferenceString,
    },
    validate::iri::{relative_ref, Error},
};

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
        error: CreationError<String>,
    },
}

/// An owned string of a relative IRI.
///
/// This corresponds to `irelative-ref` rule in RFC 3987.
/// This is `irelative-part [ "?" iquery ] [ "#" fragment ]`.
/// In other words, this is roughly `IriString` without scheme part.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct RelativeIriString(String);

/// A borrowed slice of a relative IRI.
///
/// This corresponds to `irelative-ref` rule in RFC 3987.
/// This is `irelative-part [ "?" iquery ] [ "#" fragment ]`.
/// In other words, this is roughly `IriStr` without scheme part.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[allow(clippy::derive_hash_xor_eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct RelativeIriStr(str);

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

impl RelativeIriStr {
    /// Creates a new `&RelativeIriStr`.
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
        creation_error: CreationError,
        validation_error: Error,
    },
    target: [
        {
            owned: IriReferenceString,
            slice: IriReferenceStr,
        },
    ],
}

/// `RelativeIriString` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct RelativeIriStringVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for RelativeIriStringVisitor {
    type Value = RelativeIriString;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a relative IRI")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&RelativeIriStr>::try_from(v)
            .map(ToOwned::to_owned)
            .map_err(E::custom)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        RelativeIriString::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for RelativeIriString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(RelativeIriStringVisitor)
    }
}

/// `RelativeIriStr` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct RelativeIriStrVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for RelativeIriStrVisitor {
    type Value = &'de RelativeIriStr;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a relative IRI")
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&'de RelativeIriStr>::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de: 'a, 'a> Deserialize<'de> for &'a RelativeIriStr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_string(RelativeIriStrVisitor)
    }
}
