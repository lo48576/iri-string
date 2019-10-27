//! Usual absolute IRI (fragment part being allowed).

use std::convert::TryFrom;

use nom::combinator::complete;
#[cfg(feature = "serde")]
use serde::Serialize;
use validated_slice::{OwnedSliceSpec, SliceSpec};

use crate::{
    parser::{self, IriRule},
    types::{
        iri::set_fragment, AbsoluteIriStr, AbsoluteIriString, IriCreationError, IriFragmentStr,
        IriFragmentString, IriReferenceStr, IriReferenceString,
    },
    validate::iri::{iri, Error},
};

/// A borrowed string of an absolute IRI possibly with fragment part.
///
/// This corresponds to `IRI` rule in [RFC 3987].
/// This is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
/// In other words, this is `AbsoluteIriStr` with fragment part allowed.
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[allow(clippy::derive_hash_xor_eq)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriStr(str);

impl IriStr {
    /// Creates a new `&IriStr`.
    ///
    /// ```
    /// # use iri_string::types::IriStr;
    /// assert!(IriStr::new("https://user:pass@example.com:8080").is_ok());
    /// assert!(IriStr::new("https://example.com/").is_ok());
    /// assert!(IriStr::new("https://example.com/foo?bar=baz").is_ok());
    /// assert!(IriStr::new("https://example.com/foo?bar=baz#qux").is_ok());
    /// assert!(IriStr::new("foo:bar").is_ok());
    ///
    /// // Relative IRI is not allowed.
    /// assert!(IriStr::new("foo/bar").is_err());
    /// assert!(IriStr::new("/foo/bar").is_err());
    /// assert!(IriStr::new("//foo/bar").is_err());
    /// assert!(IriStr::new("#foo").is_err());
    /// // > When authority is not present, the path cannot begin with two slash characters ("//").
    /// // >
    /// // > --- [RFC 3986 section 3](https://tools.ietf.org/html/rfc3986#section-3)
    /// assert!(IriStr::new("foo:////").is_err());
    /// ```
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

/// An owned string of an absolute IRI possibly with fragment part.
///
/// This corresponds to `IRI` rule in [RFC 3987].
/// This is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
/// In other words, this is `AbsoluteIriString` with fragment part allowed.
///
/// See documentation for [`IriStr`].
///
/// [RFC 3987]: https://tools.ietf.org/html/rfc3987
/// [`IriStr`]: struct.IriStr.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IriString(String);

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

impl_basics! {
    Slice {
        spec: StrSpec,
        custom: IriStr,
        validator: iri,
        error: Error,
    },
    Owned {
        spec: StringSpec,
        custom: IriString,
        error: IriCreationError<String>,
    },
}

impl std::ops::Deref for IriStr {
    type Target = IriReferenceStr;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl_conv_and_cmp! {
    source: {
        owned: IriString,
        slice: IriStr,
        creation_error: IriCreationError,
        validation_error: Error,
    },
    target: [
        {
            owned: IriReferenceString,
            slice: IriReferenceStr,
        },
    ],
}
impl_serde! {
    expecting: "an IRI",
    slice: IriStr,
    owned: IriString,
}
