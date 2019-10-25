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

/// Spec of `RelativeIriStr`.
enum StrSpec {}

impl SliceSpec for StrSpec {
    type Custom = RelativeIriStr;
    type Inner = str;
    type Error = Error;

    #[inline]
    fn validate(s: &Self::Inner) -> Result<(), Self::Error> {
        relative_ref(s)
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
        custom: RelativeIriStr,
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
        custom: RelativeIriStr,
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

/// Spec of `RelativeIriString`.
enum StringSpec {}

impl OwnedSliceSpec for StringSpec {
    type Custom = RelativeIriString;
    type Inner = String;
    type Error = CreationError<Self::Inner>;
    type SliceSpec = StrSpec;
    type SliceCustom = RelativeIriStr;
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
        RelativeIriString(s)
    }

    #[inline]
    fn into_inner(s: Self::Custom) -> Self::Inner {
        s.0
    }
}

validated_slice::impl_std_traits_for_owned_slice! {
    Spec {
        spec: StringSpec,
        custom: RelativeIriString,
        inner: String,
        error: CreationError<String>,
        slice_custom: RelativeIriStr,
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
        custom: RelativeIriString,
        inner: String,
        slice_custom: RelativeIriStr,
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

impl_std_traits! {
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
