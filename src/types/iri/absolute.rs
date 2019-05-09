//! Absolute IRI.

use std::{convert::TryFrom, fmt};

use crate::{
    types::{IriReferenceStr, IriReferenceString, IriStr, IriString},
    validate::iri::{absolute_iri, Error},
};

custom_slice_macros::define_slice_types_pair! {
    /// An owned string of an absolute IRI.
    ///
    /// This corresponds to `absolute-IRI` rule in RFC 3987.
    /// This is `scheme ":" ihier-part [ "?" iquery ]`.
    /// In other words, this is `IriString` without fragment part.
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[custom_slice(owned)]
    #[custom_slice(derive(
        AsRefSlice, AsRefSliceInner, Deref, IntoInner,
        PartialEqBulk, PartialEqInnerBulk, PartialOrdBulk, PartialOrdInnerBulk,
        TryFromInner,
    ))]
    #[custom_slice(error(type = "Error"))]
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
    #[custom_slice(slice)]
    #[custom_slice(derive(
        AsRefSlice, AsRefSliceInner,
        DefaultRef, Deref, PartialEqBulk, PartialEqInnerBulk,
        PartialOrdBulk, PartialOrdInnerBulk, IntoArc, IntoBox, IntoRc,
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
}

impl AbsoluteIriStr {
    /// Creates a new `&AbsoluteIriStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(validate(s), Ok(()));
        Self::new_always_unchecked(s)
    }
}

impl fmt::Display for AbsoluteIriString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<AbsoluteIriStr>::as_ref(self).fmt(f)
    }
}

impl fmt::Display for &AbsoluteIriStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<str>::as_ref(self).fmt(f)
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
        error: Error,
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
