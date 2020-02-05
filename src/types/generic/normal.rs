//! Usual absolute IRI (fragment part being allowed).

#[cfg(feature = "alloc")]
use alloc::string::String;

#[cfg(feature = "alloc")]
use crate::types::{RiAbsoluteString, RiFragmentString, RiReferenceString};
use crate::{
    raw,
    spec::Spec,
    types::{RiAbsoluteStr, RiFragmentStr, RiReferenceStr},
    validate::iri,
};

define_custom_string_slice! {
    /// A borrowed string of an absolute IRI possibly with fragment part.
    ///
    /// This corresponds to [`IRI` rule] in [RFC 3987] (and [`URI` rule] in [RFC 3986]).
    /// The rule for `IRI` is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
    /// In other words, this is [`RiAbsoluteStr`] with fragment part allowed.
    ///
    /// # Valid values
    ///
    /// This type can have an IRI (which is absolute, and may have fragment part).
    ///
    /// ```
    /// # use iri_string::types::IriStr;
    /// assert!(IriStr::new("https://user:pass@example.com:8080").is_ok());
    /// assert!(IriStr::new("https://example.com/").is_ok());
    /// assert!(IriStr::new("https://example.com/foo?bar=baz").is_ok());
    /// assert!(IriStr::new("https://example.com/foo?bar=baz#qux").is_ok());
    /// assert!(IriStr::new("foo:bar").is_ok());
    /// assert!(IriStr::new("foo:").is_ok());
    /// // `foo://.../` below are all allowed. See the crate documentation for detail.
    /// assert!(IriStr::new("foo:/").is_ok());
    /// assert!(IriStr::new("foo://").is_ok());
    /// assert!(IriStr::new("foo:///").is_ok());
    /// assert!(IriStr::new("foo:////").is_ok());
    /// assert!(IriStr::new("foo://///").is_ok());
    /// ```
    ///
    /// Relative IRI reference is not allowed.
    ///
    /// ```
    /// # use iri_string::types::IriStr;
    /// // This is relative path.
    /// assert!(IriStr::new("foo/bar").is_err());
    /// // `/foo/bar` is an absolute path, but it is authority-relative.
    /// assert!(IriStr::new("/foo/bar").is_err());
    /// // `//foo/bar` is termed "network-path reference",
    /// // or usually called "protocol-relative reference".
    /// assert!(IriStr::new("//foo/bar").is_err());
    /// // Same-document reference is relative.
    /// assert!(IriStr::new("#foo").is_err());
    /// // Empty string is not a valid absolute IRI.
    /// assert!(IriStr::new("").is_err());
    /// ```
    ///
    /// Some characters and sequences cannot used in an IRI.
    ///
    /// ```
    /// # use iri_string::types::IriStr;
    /// // `<` and `>` cannot directly appear in an IRI.
    /// assert!(IriStr::new("<not allowed>").is_err());
    /// // Broken percent encoding cannot appear in an IRI.
    /// assert!(IriStr::new("%").is_err());
    /// assert!(IriStr::new("%GG").is_err());
    /// ```
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC 3987]: https://tools.ietf.org/html/rfc3987
    /// [`IRI` rule]: https://tools.ietf.org/html/rfc3987#section-2.2
    /// [`URI` rule]: https://tools.ietf.org/html/rfc3986#section-3
    /// [`RiAbsoluteStr`]: struct.RiAbsoluteStr.html
    struct RiStr {
        validator = iri,
        expecting_msg = "IRI string",
    }
}

#[cfg(feature = "alloc")]
define_custom_string_owned! {
    /// An owned string of an absolute IRI possibly with fragment part.
    ///
    /// This corresponds to [`IRI` rule] in [RFC 3987] (and [`URI` rule] in [RFC 3986]).
    /// The rule for `IRI` is `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`.
    /// In other words, this is [`RiAbsoluteString`] with fragment part allowed.
    ///
    /// For details, see the document for [`RiStr`].
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC 3987]: https://tools.ietf.org/html/rfc3987
    /// [`IRI` rule]: https://tools.ietf.org/html/rfc3987#section-2.2
    /// [`URI` rule]: https://tools.ietf.org/html/rfc3986#section-3
    /// [`RiAbsoluteString`]: struct.RiAbsoluteString.html
    struct RiString {
        validator = iri,
        slice = RiStr,
        expecting_msg = "IRI string",
    }
}

impl<S: Spec> RiStr<S> {
    /// Splits the IRI into an absolute IRI part and a fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// If the IRI has a fragment part, `Some(_)` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriStr}, validate::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#corge")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// let fragment_expected = IriFragmentStr::new("corge")?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// When the fragment part exists but is empty string, `Some(_)` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriStr}, validate::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// let fragment_expected = IriFragmentStr::new("")?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// If the IRI has no fragment, `None` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriStr, validate::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux")?;
    /// let (absolute, fragment) = iri.to_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn to_absolute_and_fragment(&self) -> (&RiAbsoluteStr<S>, Option<&RiFragmentStr<S>>) {
        let (prefix, fragment) = raw::split_fragment(self.as_str());
        let prefix = unsafe {
            // This is safe because the an IRI without fragment part is also an absolute IRI.
            RiAbsoluteStr::new_maybe_unchecked(prefix)
        };
        let fragment = fragment.map(|fragment| unsafe {
            // This is safe because the returned string is fragment part, and is also substring of
            // the source IRI.
            RiFragmentStr::new_maybe_unchecked(fragment)
        });

        (prefix, fragment)
    }

    /// Strips the fragment part if exists, and returns [`&RiAbsoluteStr`][`RiAbsoluteStr`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriStr, validate::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#corge")?;
    /// assert_eq!(iri.to_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriStr, validate::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.to_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`RiAbsoluteStr`]: struct.RiAbsoluteStr.html
    pub fn to_absolute(&self) -> &RiAbsoluteStr<S> {
        let prefix_len = raw::split_fragment(self.as_str()).0.len();
        unsafe {
            // This is safe because an IRI without the fragment part (and a leading `#` character)
            // is also an absolute IRI.
            RiAbsoluteStr::new_maybe_unchecked(&self.as_str()[..prefix_len])
        }
    }

    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriStr}, validate::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#corge")?;
    /// let fragment = IriFragmentStr::new("corge")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriStr}, validate::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux#")?;
    /// let fragment = IriFragmentStr::new("")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriStr, validate::Error};
    /// let iri = IriStr::new("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn fragment(&self) -> Option<&RiFragmentStr<S>> {
        AsRef::<RiReferenceStr<S>>::as_ref(self).fragment()
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> RiString<S> {
    /// Splits the IRI into an absolute IRI part and a fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentString, IriString}, validate::Error};
    /// let iri = "foo://bar/baz?qux=quux#corge".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// let fragment_expected = IriFragmentString::try_from("corge".to_owned())
    ///     .map_err(|e| e.validation_error())?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Error>(())
    ///
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentString, IriString}, validate::Error};
    /// let iri = "foo://bar/baz?qux=quux#".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// let fragment_expected = IriFragmentString::try_from("".to_owned())
    ///     .map_err(|e| e.validation_error())?;
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, Some(fragment_expected));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use iri_string::{spec::IriSpec, types::IriString, validate::Error};
    /// let iri = "foo://bar/baz?qux=quux".parse::<IriString>()?;
    /// let (absolute, fragment) = iri.into_absolute_and_fragment();
    /// assert_eq!(absolute, "foo://bar/baz?qux=quux");
    /// assert_eq!(fragment, None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn into_absolute_and_fragment(self) -> (RiAbsoluteString<S>, Option<RiFragmentString<S>>) {
        let (prefix, fragment) = raw::split_fragment_owned(self.into());
        let prefix = unsafe {
            // This is safe because the an IRI without fragment part is also an absolute IRI.
            RiAbsoluteString::new_maybe_unchecked(prefix)
        };
        let fragment = fragment.map(|fragment| unsafe {
            // This is safe because the returned string is fragment part, and is also substring of
            // the source IRI.
            RiFragmentString::new_maybe_unchecked(fragment)
        });

        (prefix, fragment)
    }

    /// Strips the fragment part if exists, and returns an [`RiAbsoluteString`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriString, validate::Error};
    /// let iri = "foo://bar/baz?qux=quux#corge".parse::<IriString>()?;
    /// assert_eq!(iri.into_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriString, validate::Error};
    /// let iri = "foo://bar/baz?qux=quux".parse::<IriString>()?;
    /// assert_eq!(iri.into_absolute(), "foo://bar/baz?qux=quux");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`RiAbsoluteString`]: struct.RiAbsoluteString.html
    pub fn into_absolute(self) -> RiAbsoluteString<S> {
        let mut s: String = self.into();
        raw::remove_fragment(&mut s);
        unsafe {
            // This is safe because the an IRI without fragment part is also an absolute IRI.
            RiAbsoluteString::new_maybe_unchecked(s)
        }
    }

    /// Sets the fragment part to the given string.
    ///
    /// Removes fragment part (and following `#` character) if `None` is given.
    pub fn set_fragment(&mut self, fragment: Option<&RiFragmentStr<S>>) {
        raw::set_fragment(&mut self.inner, fragment.map(AsRef::as_ref));
        debug_assert!(iri::<S>(&self.inner).is_ok());
    }
}

impl_infallible_conv_between_iri! {
    from_slice: RiStr,
    from_owned: RiString,
    to_slice: RiReferenceStr,
    to_owned: RiReferenceString,
}
