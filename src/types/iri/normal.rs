//! Absolute IRI.

use std::{convert::TryFrom, fmt};

use nom::combinator::complete;
#[cfg(feature = "serde")]
use serde::{
    de::{self, Visitor},
    Deserialize, Deserializer, Serialize,
};
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    parser::{self, IriRule},
    types::{
        iri::set_fragment, AbsoluteIriStr, AbsoluteIriString, CreationError, IriFragmentStr,
        IriFragmentString, IriReferenceStr, IriReferenceString,
    },
    validate::iri::{iri, Error},
};

/// Spec of `IriStr`.
enum StrSpec {}

impl SliceSpec for StrSpec {
    type Custom = IriStr;
    type Inner = str;
    type Error = Error;

    #[inline]
    fn validate(s: &Self::Inner) -> Result<(), Self::Error> {
        iri(s)
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
        custom: IriStr,
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
        custom: IriStr,
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

/// Spec of `IriString`.
enum StringSpec {}

impl OwnedSliceSpec for StringSpec {
    type Custom = IriString;
    type Inner = String;
    type Error = CreationError<Self::Inner>;
    type SliceSpec = StrSpec;
    type SliceCustom = IriStr;
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
        IriString(s)
    }

    #[inline]
    fn into_inner(s: Self::Custom) -> Self::Inner {
        s.0
    }
}

validated_slice::impl_std_traits_for_owned_slice! {
    Spec {
        spec: StringSpec,
        custom: IriString,
        inner: String,
        error: CreationError<String>,
        slice_custom: IriStr,
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
        custom: IriString,
        inner: String,
        slice_custom: IriStr,
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

/// An owned string of an IRI.
///
/// This corresponds to `IRI` rule in RFC 3987.
/// This is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
/// In other words, this is `AbsoluteIriString` with fragment part allowed.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriString(String);

/// A borrowed slice of an IRI.
///
/// This corresponds to `IRI` rule in RFC 3987.
/// This is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
/// In other words, this is `AbsoluteIriStr` with fragment part allowed.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[allow(clippy::derive_hash_xor_eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriStr(str);

impl IriString {
    /// Creates a new `IriString` without validation.
    ///
    /// This does not validate the given string at any time.
    ///
    /// Intended for internal use.
    ///
    /// # Safety
    ///
    /// The given string must be a valid IRI string.
    pub(crate) unsafe fn new_always_unchecked(s: String) -> Self {
        StringSpec::from_inner_unchecked(s)
    }

    /// Creates a new `IriString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(StrSpec::validate(&s), Ok(()));
        StringSpec::from_inner_unchecked(s)
    }

    /// Splits the IRI into absolute IRI part and fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::types::{IriFragmentString, IriString};
    /// let iri = "foo://bar/baz?qux=quux#corge".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// let fragment_expected = IriFragmentString::try_from("corge".to_owned())?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Box<std::error::Error>>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::types::{IriFragmentString, IriString};
    /// let iri = "foo://bar/baz?qux=quux#".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// let fragment_expected = IriFragmentString::try_from("".to_owned())?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Box<std::error::Error>>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::types::IriString;
    /// let iri = "foo://bar/baz?qux=quux".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, None);
    /// # Ok::<_, Box<std::error::Error>>(())
    /// ```
    pub fn into_absolute_and_fragment(self) -> (AbsoluteIriString, Option<IriFragmentString>) {
        let (abs_iri, fragment) = self.split_fragment();
        if fragment.is_none() {
            let abs_iri = unsafe {
                // This is safe because the `abs_uri` is parsable with
                // `absolute_uri`.
                // This is ensured by `split_fragment()`.
                AbsoluteIriString::new_unchecked(self.into())
            };
            return (abs_iri, None);
        }
        let abs_len = abs_iri.len();

        let mut s: String = self.into();
        let fragment = s.split_off(abs_len + 1);
        // Current `s` contains a trailing `#` character, which should be
        // removed.
        {
            // Remove a trailing `#`.
            let hash = s.pop();
            assert_eq!(hash, Some('#'));
        }
        assert_eq!(s.len(), abs_len);
        let abs_iri = unsafe {
            // This is safe because `absolute_part_len()` guarantees that
            // `&s[..abs_len]` is parsable with `absolute_uri`.
            AbsoluteIriString::new_unchecked(s)
        };
        let fragment = unsafe {
            // This is safe because the fragment part of the valid `IriString`
            // is guaranteed to be a valid fragment.
            IriFragmentString::new_unchecked(fragment)
        };
        (abs_iri, Some(fragment))
    }

    /// Strips the fragment part if exists, and returns `AbsoluteIriString`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{types::IriString, validate::iri::Error};
    /// let iri = "foo://bar/baz?qux=quux#corge".parse::<IriString>()?;
    /// assert_eq!(iri.into_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{types::IriString, validate::iri::Error};
    /// let iri = "foo://bar/baz?qux=quux".parse::<IriString>()?;
    /// assert_eq!(iri.into_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    pub fn into_absolute(self) -> AbsoluteIriString {
        let (abs_iri, _fragment) = self.split_fragment();
        let abs_len = abs_iri.len();
        let mut s: String = self.into();
        s.truncate(abs_len);
        unsafe {
            // This is safe because `absolute_part_len()` guarantees that
            // `&s[..abs_len]` is parsable with `absolute_uri`.
            AbsoluteIriString::new_unchecked(s)
        }
    }

    /// Sets the fragment part to the given string.
    ///
    /// Removes fragment part (and following `#` character) if `None` is given.
    pub fn set_fragment(&mut self, fragment: Option<&IriFragmentStr>) {
        set_fragment(&mut self.0, fragment.map(AsRef::as_ref));
        debug_assert!(iri(&self.0).is_ok());
    }

    /// Shrinks the capacity of the inner buffer to match its length.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

impl IriStr {
    /// Creates a new `&IriStr`.
    pub fn new(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new `IriStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(StrSpec::validate(s), Ok(()));
        StrSpec::from_inner_unchecked(s)
    }

    /// Returns the absolute IRI part and fragment part in raw string slices.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    fn split_fragment(&self) -> (&str, Option<&str>) {
        match complete(parser::absolute_uri::<(), IriRule>)(&self.0) {
            Ok(("", abs_iri)) => (abs_iri, None),
            Ok((hash_frag, abs_iri)) => {
                assert_eq!(hash_frag.as_bytes()[0], b'#');
                (abs_iri, Some(&hash_frag[1..]))
            }
            Err(_) => unreachable!(
                "Should never reach here: IRI should contain absolute IRI as its prefix"
            ),
        }
    }

    /// Splits the IRI into absolute IRI part and fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::{IriFragmentStr, IriStr}, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux#corge")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// let fragment_expected = <&IriFragmentStr>::try_from("corge")?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::{IriFragmentStr, IriStr}, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux#")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// let fragment_expected = <&IriFragmentStr>::try_from("")?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn to_absolute_and_fragment(&self) -> (&AbsoluteIriStr, Option<&IriFragmentStr>) {
        let (abs_iri, fragment) = self.split_fragment();
        let abs_iri = unsafe {
            // This is safe because the `abs_uri` is parsable with
            // `absolute_uri`.
            // This is ensured by `split_fragment()`.
            AbsoluteIriStr::new_unchecked(abs_iri)
        };
        let fragment = fragment.map(|fragment| unsafe {
            // This is safe because the fragment part of the valid `IriString`
            // is guaranteed to be a valid fragment.
            IriFragmentStr::new_unchecked(fragment)
        });
        (abs_iri, fragment)
    }

    /// Strips the fragment part if exists, and returns `&AbsoluteIriStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux#corge")?;
    /// assert_eq!(iri.to_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.to_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    pub fn to_absolute(&self) -> &AbsoluteIriStr {
        self.to_absolute_and_fragment().0
    }

    /// Returns `&str`.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

impl std::ops::Deref for IriStr {
    type Target = IriReferenceStr;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl_std_traits! {
    source: {
        owned: IriString,
        slice: IriStr,
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

/// `IriString` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct IriStringVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for IriStringVisitor {
    type Value = IriString;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an IRI")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&IriStr>::try_from(v)
            .map(ToOwned::to_owned)
            .map_err(E::custom)
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        IriString::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for IriString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(IriStringVisitor)
    }
}

/// `IriStr` visitor.
#[cfg(feature = "serde")]
#[derive(Debug, Clone, Copy)]
struct IriStrVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for IriStrVisitor {
    type Value = &'de IriStr;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an absolute IRI")
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        <&'de IriStr>::try_from(v).map_err(E::custom)
    }
}

#[cfg(feature = "serde")]
impl<'de: 'a, 'a> Deserialize<'de> for &'a IriStr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_string(IriStrVisitor)
    }
}
