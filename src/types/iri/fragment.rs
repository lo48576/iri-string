//! Fragment string.

use std::convert::TryFrom;

#[cfg(feature = "serde")]
use serde::Serialize;
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    types::CreationError,
    validate::iri::{fragment, Error},
};

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

/// An owned string of an IRI fragment.
///
/// This corresponds to `ifragment` rule in RFC 3987.
/// This is `*( ipchar / "/" / "?" )`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriFragmentString(String);

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

impl_basics! {
    Slice {
        spec: StrSpec,
        custom: IriFragmentStr,
        validator: fragment,
        error: Error,
    },
    Owned {
        spec: StringSpec,
        custom: IriFragmentString,
        error: CreationError<String>,
    },
}

impl_serde! {
    expecting: "an IRI fragment",
    slice: IriFragmentStr,
    owned: IriFragmentString,
}
