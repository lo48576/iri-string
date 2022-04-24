//! Usual absolute IRI (fragment part being allowed).

#[cfg(feature = "alloc")]
use core::convert::Infallible;

#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::components::AuthorityComponents;
#[cfg(feature = "alloc")]
use crate::normalize::{Error, NormalizationTask};
use crate::parser::trusted as trusted_parser;
#[cfg(feature = "alloc")]
use crate::raw;
use crate::spec::Spec;
#[cfg(feature = "alloc")]
use crate::task::{Error as TaskError, ProcessAndWrite};
use crate::types::{RiAbsoluteStr, RiFragmentStr, RiReferenceStr};
#[cfg(feature = "alloc")]
use crate::types::{RiAbsoluteString, RiFragmentString, RiReferenceString};
use crate::validate::iri;

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
    #[must_use]
    pub fn to_absolute_and_fragment(&self) -> (&RiAbsoluteStr<S>, Option<&RiFragmentStr<S>>) {
        let (prefix, fragment) = trusted_parser::split_fragment(self.as_str());
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
    #[must_use]
    pub fn to_absolute(&self) -> &RiAbsoluteStr<S> {
        let prefix_len = trusted_parser::split_fragment(self.as_str()).0.len();
        unsafe {
            // This is safe because an IRI without the fragment part (and a leading `#` character)
            // is also an absolute IRI.
            RiAbsoluteStr::new_maybe_unchecked(&self.as_str()[..prefix_len])
        }
    }

    /// Returns `true` if the IRI is already normalized.
    ///
    /// This returns the same result as
    /// `self.normalize.map_or(false, |normalized| normalized == self))`, but
    /// does this more efficiently without heap allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://example.COM/foo/./bar/%2e%2e/../baz?query#fragment")?;
    /// assert!(!iri.is_normalized());
    ///
    /// let normalized = iri.normalize()?;
    /// assert_eq!(normalized, "http://example.com/baz?query#fragment");
    /// assert!(normalized.is_normalized());
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[must_use]
    #[inline]
    pub fn is_normalized(&self) -> bool {
        trusted_parser::is_normalized::<S>(self.as_str(), false)
    }

    /// Returns the normalized IRI.
    ///
    /// If you want to avoid serialization errors (except for memory allocation
    /// failure), use [`normalize_whatwg`][`Self::normalize_whatwg`] method.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://example.COM/foo/./bar/%2e%2e/../baz?query#fragment")?;
    ///
    /// let normalized = iri.normalize()?;
    /// assert_eq!(normalized, "http://example.com/baz?query#fragment");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[inline]
    pub fn normalize(&self) -> Result<RiString<S>, TaskError<Error>> {
        NormalizationTask::from(self).allocate_and_write()
    }

    /// Returns `true` if the IRI is already normalized in the sense of WHATWG spec.
    ///
    /// This returns the same result as
    /// `self.normalize_whatwg.map_or(false, |normalized| normalized == self))`,
    /// but does this more efficiently without heap allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("scheme:a/..//not-a-host")?;
    /// assert!(!iri.is_normalized_whatwg());
    ///
    /// let normalized = iri.normalize_whatwg()?;
    /// assert_eq!(normalized, "scheme:/.//not-a-host");
    /// assert!(normalized.is_normalized_whatwg());
    /// assert!(!normalized.is_normalized(), "not normalized in the sense of RFC 3987");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[must_use]
    #[inline]
    pub fn is_normalized_whatwg(&self) -> bool {
        trusted_parser::is_normalized::<S>(self.as_str(), true)
    }

    /// Returns the normalized IRI serialized using WHATWG URL Standard.
    ///
    /// # WHATWG Serialization
    ///
    /// Consider combining scheme `a`, no host, and path `//p`. Naive
    /// implementation will generate result string `a://p`, but it is not
    /// intended result since it is an IRI that consists of scheme `a`, host
    /// `p`, and path `` (empty). In such case RFC 3986/3987 don't define the
    /// correct result, so `normalize` method fails with
    /// [`normalize::Error`][`crate::normalize::Error`] (wrapped by
    /// [`task::Error::Process`][`TaskError::Process`]).
    ///
    /// To prevent such errors but still to keep normalization
    /// idempotent, [WHATWG URL Standard][WHATWG-URL] spec requires the
    /// normalization result for such cases to be `a:/.//p`.
    ///
    /// See <https://url.spec.whatwg.org/#url-serializing> (or archive
    /// <https://web.archive.org/web/20220204115552/https://url.spec.whatwg.org/#url-serializing>).
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::types::IriStr;
    ///
    /// let iri1 = IriStr::new("scheme:/..//bar")?;
    /// assert!(iri1.normalize().is_err(), "`scheme://bar` is not intended result");
    /// assert_eq!(iri1.normalize_whatwg()?, "scheme:/.//bar");
    ///
    /// let iri2 = IriStr::new("scheme:..///bar")?;
    /// assert!(iri2.normalize().is_err(), "`scheme://bar` is not intended result");
    /// assert_eq!(iri2.normalize_whatwg()?, "scheme:/.//bar");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [WHATWG-URL]: https://url.spec.whatwg.org/
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[inline]
    pub fn normalize_whatwg(&self) -> Result<RiString<S>, TaskError<Infallible>> {
        let mut task = NormalizationTask::from(self);
        task.enable_whatwg_serialization();
        task.allocate_and_write().map_err(|e| match e {
            TaskError::Buffer(e) => TaskError::Buffer(e),
            TaskError::Process(_) => {
                panic!("WHATWG normalization algorithm should not fail")
            }
        })
    }
}

/// Components getters.
impl<S: Spec> RiStr<S> {
    /// Returns the scheme.
    ///
    /// The following colon is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("http://example.com/pathpath?queryquery#fragfrag")?;
    /// assert_eq!(iri.scheme_str(), "http");
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn scheme_str(&self) -> &str {
        trusted_parser::extract_scheme_absolute(self.as_str())
    }

    /// Returns the authority.
    ///
    /// The leading `//` is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("http://example.com/pathpath?queryquery#fragfrag")?;
    /// assert_eq!(iri.authority_str(), Some("example.com"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
    /// assert_eq!(iri.authority_str(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn authority_str(&self) -> Option<&str> {
        trusted_parser::extract_authority_absolute(self.as_str())
    }

    /// Returns the path.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("http://example.com/pathpath?queryquery#fragfrag")?;
    /// assert_eq!(iri.path_str(), "/pathpath");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
    /// assert_eq!(iri.path_str(), "uuid:10db315b-fcd1-4428-aca8-15babc9a2da2");
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn path_str(&self) -> &str {
        trusted_parser::extract_path_absolute(self.as_str())
    }

    /// Returns the query.
    ///
    /// The leading question mark (`?`) is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("http://example.com/pathpath?queryquery#fragfrag")?;
    /// assert_eq!(iri.query_str(), Some("queryquery"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
    /// assert_eq!(iri.query_str(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn query_str(&self) -> Option<&str> {
        trusted_parser::extract_query(self.as_str())
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
    #[must_use]
    pub fn fragment(&self) -> Option<&RiFragmentStr<S>> {
        AsRef::<RiReferenceStr<S>>::as_ref(self).fragment()
    }

    /// Returns the authority components.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("http://user:pass@example.com:8080/pathpath?queryquery")?;
    /// let authority = iri.authority_components()
    ///     .expect("authority is available");
    /// assert_eq!(authority.userinfo(), Some("user:pass"));
    /// assert_eq!(authority.host(), "example.com");
    /// assert_eq!(authority.port(), Some("8080"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
    /// assert_eq!(iri.authority_str(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn authority_components(&self) -> Option<AuthorityComponents<'_>> {
        AuthorityComponents::from_iri(self.as_ref())
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
    #[must_use]
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
    #[must_use]
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

impl_trivial_conv_between_iri! {
    from_slice: RiStr,
    from_owned: RiString,
    to_slice: RiReferenceStr,
    to_owned: RiReferenceString,
}
