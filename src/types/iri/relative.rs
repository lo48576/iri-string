//! Relative IRI.

use std::{convert::TryFrom, fmt};

use crate::{
    types::{IriReferenceStr, IriReferenceString},
    validate::iri::{relative_ref, Error},
};

custom_slice_macros::define_slice_types_pair! {
    /// An owned string of a relative IRI.
    ///
    /// This corresponds to `irelative-ref` rule in RFC 3987.
    /// This is `irelative-part [ "?" iquery ] [ "#" fragment ]`.
    /// In other words, this is roughly `IriString` without scheme part.
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[custom_slice(owned)]
    #[custom_slice(derive(
        AsRefSlice, AsRefSliceInner, Deref, IntoInner,
        PartialEqBulk, PartialEqInnerBulk, PartialOrdBulk, PartialOrdInnerBulk,
        TryFromInner,
    ))]
    #[custom_slice(error(type = "Error"))]
    #[custom_slice(new_unchecked = "
        /// Creates a new `RelativeIriString` without validation.
        pub(crate) unsafe fn new_always_unchecked
    ")]
    pub struct RelativeIriString(String);

    /// A borrowed slice of a relative IRI.
    ///
    /// This corresponds to `irelative-ref` rule in RFC 3987.
    /// This is `irelative-part [ "?" iquery ] [ "#" fragment ]`.
    /// In other words, this is roughly `IriStr` without scheme part.
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
        /// Creates a new `&RelativeIriStr` without validation.
        pub(crate) unsafe fn new_always_unchecked
    ")]
    pub struct RelativeIriStr(str);

    /// Validates the given string as a relative IRI.
    #[custom_slice(validator)]
    fn validate(s: &str) -> Result<(), Error> {
        relative_ref(s)
    }
}

impl RelativeIriString {
    /// Creates a new `RelativeIriString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(validate(&s), Ok(()));
        Self::new_always_unchecked(s)
    }
}

impl RelativeIriStr {
    /// Creates a new `&RelativeIriStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(validate(s), Ok(()));
        Self::new_always_unchecked(s)
    }
}

impl fmt::Display for RelativeIriString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<RelativeIriStr>::as_ref(self).fmt(f)
    }
}

impl fmt::Display for &RelativeIriStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<str>::as_ref(self).fmt(f)
    }
}

impl std::str::FromStr for RelativeIriString {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        <&RelativeIriStr>::try_from(s).map(ToOwned::to_owned)
    }
}

impl_std_traits! {
    source: {
        owned: RelativeIriString,
        slice: RelativeIriStr,
        error: Error,
    },
    target: [
        {
            owned: IriReferenceString,
            slice: IriReferenceStr,
        },
    ],
}
