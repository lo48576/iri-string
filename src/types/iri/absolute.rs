//! Absolute IRI (without fragment part).

use std::convert::TryFrom;

#[cfg(feature = "serde")]
use serde::Serialize;
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    types::{CreationError, IriReferenceStr, IriReferenceString, IriStr, IriString},
    validate::iri::{absolute_iri, Error},
};

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

/// An owned string of an absolute IRI.
///
/// This corresponds to `absolute-IRI` rule in RFC 3987.
/// This is `scheme ":" ihier-part [ "?" iquery ]`.
/// In other words, this is `IriString` without fragment part.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct AbsoluteIriString(String);

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

impl_serde! {
    expecting: "an absolute IRI",
    slice: AbsoluteIriStr,
    owned: AbsoluteIriString,
}
