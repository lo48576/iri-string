//! Fragment string.

use std::{convert::TryFrom, fmt};

#[cfg(feature = "serde")]
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize,
};

use crate::{
    types::CreationError,
    validate::iri::{fragment, Error},
};

custom_slice_macros::define_slice_types_pair! {
    /// An owned string of an IRI fragment.
    ///
    /// This corresponds to `ifragment` rule in RFC 3987.
    /// This is `*( ipchar / "/" / "?" )`.
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
            /// Creates a new `IriFragmentString` without validation.
            pub(crate) unsafe fn new_always_unchecked
        ")]
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
            /// Creates a new `&IriFragmentStr` without validation.
            pub(crate) unsafe fn new_always_unchecked
        ")]
    pub struct IriFragmentStr(str);

    /// Validates the given string as an IRI.
    #[custom_slice(validator)]
    fn validate(s: &str) -> Result<(), Error> {
        fragment(s)
    }
}

impl IriFragmentString {
    /// Creates a new `IriFragmentString` maybe without validation.
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

impl IriFragmentStr {
    /// Creates a new `IriFragmentStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(validate(&s), Ok(()));
        Self::new_always_unchecked(s)
    }
}

impl fmt::Display for IriFragmentString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<IriFragmentStr>::as_ref(self).fmt(f)
    }
}

impl fmt::Display for &IriFragmentStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<str>::as_ref(self).fmt(f)
    }
}

impl std::str::FromStr for IriFragmentString {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        <&IriFragmentStr>::try_from(s).map(ToOwned::to_owned)
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
