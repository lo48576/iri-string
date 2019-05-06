//! Absolute IRI.

use std::{convert::TryFrom, fmt};

use nom::combinator::complete;

use crate::{
    parser::{self, IriRule},
    types::{AbsoluteIriStr, AbsoluteIriString},
    validate::iri::{iri, Error},
};

custom_slice_macros::define_slice_types_pair! {
    /// An owned string of an IRI.
    ///
    /// This corresponds to `IRI` rule in RFC 3987.
    /// This is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
    /// In other words, this is `AbsoluteIriString` with fragment part allowed.
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[custom_slice(owned)]
    #[custom_slice(derive(
        AsRefSlice, AsRefSliceInner, Deref, IntoInner,
        PartialEqBulk, PartialEqInnerBulk, PartialOrdBulk, PartialOrdInnerBulk,
        TryFromInner,
    ))]
    #[custom_slice(error(type = "Error"))]
    #[custom_slice(new_unchecked = "
        /// Creates a new `IriString` without validation.
        pub(crate) unsafe fn new_always_unchecked
    ")]
    pub struct IriString(String);

    /// A borrowed slice of an IRI.
    ///
    /// This corresponds to `IRI` rule in RFC 3987.
    /// This is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
    /// In other words, this is `AbsoluteIriStr` with fragment part allowed.
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
        /// Creates a new `&IriStr` without validation.
        pub(crate) unsafe fn new_always_unchecked
    ")]
    pub struct IriStr(str);

    /// Validates the given string as an IRI.
    #[custom_slice(validator)]
    fn validate(s: &str) -> Result<(), Error> {
        iri(s)
    }
}

impl IriString {
    /// Creates a new `IriString` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: String) -> Self {
        debug_assert_eq!(validate(&s), Ok(()));
        Self::new_always_unchecked(s)
    }

    /// Splits the IRI into absolute IRI part and fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriString, validate::iri::Error};
    /// let iri = "foo://bar/baz?qux=quux#corge".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some("corge".to_owned()));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriString, validate::iri::Error};
    /// let iri = "foo://bar/baz?qux=quux#".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some("".to_owned()));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriString, validate::iri::Error};
    /// let iri = "foo://bar/baz?qux=quux".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn into_absolute_and_fragment(self) -> (AbsoluteIriString, Option<String>) {
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
}

impl IriStr {
    /// Creates a new `IriStr` maybe without validation.
    ///
    /// This does validation on debug build.
    pub(crate) unsafe fn new_unchecked(s: &str) -> &Self {
        debug_assert_eq!(validate(&s), Ok(()));
        Self::new_always_unchecked(s)
    }

    /// Returns the absolute IRI part and fragment part in raw string slices.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    fn split_fragment(&self) -> (&str, Option<&str>) {
        match complete(parser::absolute_uri::<(), IriRule>)(self) {
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
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux#corge")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some("corge"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux#")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(""));
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
    pub fn to_absolute_and_fragment(&self) -> (&AbsoluteIriStr, Option<&str>) {
        let (abs_iri, fragment) = self.split_fragment();
        let abs_iri = unsafe {
            // This is safe because the `abs_uri` is parsable with
            // `absolute_uri`.
            // This is ensured by `split_fragment()`.
            AbsoluteIriStr::new_unchecked(abs_iri)
        };
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

    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux#corge")?;
    /// assert_eq!(iri.fragment(), Some("corge"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux#")?;
    /// assert_eq!(iri.fragment(), Some(""));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{types::IriStr, validate::iri::Error};
    /// let iri = <&IriStr>::try_from("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn fragment(&self) -> Option<&str> {
        self.split_fragment().1
    }
}

impl fmt::Display for IriString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<IriStr>::as_ref(self).fmt(f)
    }
}

impl fmt::Display for &IriStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        AsRef::<str>::as_ref(self).fmt(f)
    }
}

impl std::str::FromStr for IriString {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        <&IriStr>::try_from(s).map(ToOwned::to_owned)
    }
}

impl From<AbsoluteIriString> for IriString {
    fn from(s: AbsoluteIriString) -> Self {
        debug_assert_eq!(validate(s.as_ref()), Ok(()));
        unsafe {
            // This is safe because an absolute IRI is also an IRI.
            // See syntax rule.
            IriString::new_unchecked(s.into())
        }
    }
}

impl AsRef<IriStr> for AbsoluteIriString {
    fn as_ref(&self) -> &IriStr {
        debug_assert_eq!(validate(self.as_ref()), Ok(()));
        unsafe {
            // This is safe because an absolute IRI is also an IRI.
            // See syntax rule.
            IriStr::new_unchecked(self.as_ref())
        }
    }
}

impl AsRef<IriStr> for AbsoluteIriStr {
    fn as_ref(&self) -> &IriStr {
        debug_assert_eq!(validate(self.as_ref()), Ok(()));
        unsafe {
            // This is safe because an absolute IRI is also an IRI.
            // See syntax rule.
            IriStr::new_unchecked(self.as_ref())
        }
    }
}
