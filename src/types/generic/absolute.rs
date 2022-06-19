//! Absolute IRI (without fragment part).

use crate::components::AuthorityComponents;
#[cfg(feature = "alloc")]
use crate::normalize::NormalizationTask;
use crate::normalize::{Error, NormalizationInput};
use crate::parser::trusted as trusted_parser;
use crate::spec::Spec;
#[cfg(feature = "alloc")]
use crate::task::{Error as TaskError, ProcessAndWrite};
use crate::types::{RiQueryStr, RiReferenceStr, RiStr};
#[cfg(feature = "alloc")]
use crate::types::{RiReferenceString, RiString};
use crate::validate::absolute_iri;

define_custom_string_slice! {
    /// A borrowed slice of an absolute IRI without fragment part.
    ///
    /// This corresponds to [`absolute-IRI` rule] in [RFC 3987]
    /// (and [`absolute-URI` rule] in [RFC 3986]).
    /// In other words, this is [`RiStr`] without fragment part.
    ///
    /// If you want to accept fragment part, use [`RiStr`].
    ///
    /// # Valid values
    ///
    /// This type can have an absolute IRI without fragment part.
    ///
    /// ```
    /// # use iri_string::types::IriAbsoluteStr;
    /// assert!(IriAbsoluteStr::new("https://example.com/foo?bar=baz").is_ok());
    /// assert!(IriAbsoluteStr::new("foo:bar").is_ok());
    /// // Scheme `foo` and empty path.
    /// assert!(IriAbsoluteStr::new("foo:").is_ok());
    /// // `foo://.../` below are all allowed. See the crate documentation for detail.
    /// assert!(IriAbsoluteStr::new("foo:/").is_ok());
    /// assert!(IriAbsoluteStr::new("foo://").is_ok());
    /// assert!(IriAbsoluteStr::new("foo:///").is_ok());
    /// assert!(IriAbsoluteStr::new("foo:////").is_ok());
    /// assert!(IriAbsoluteStr::new("foo://///").is_ok());
    ///
    /// ```
    ///
    /// Relative IRI is not allowed.
    ///
    /// ```
    /// # use iri_string::types::IriAbsoluteStr;
    /// // This is relative path.
    /// assert!(IriAbsoluteStr::new("foo/bar").is_err());
    /// // `/foo/bar` is an absolute path, but it is authority-relative.
    /// assert!(IriAbsoluteStr::new("/foo/bar").is_err());
    /// // `//foo/bar` is termed "network-path reference",
    /// // or usually called "protocol-relative reference".
    /// assert!(IriAbsoluteStr::new("//foo/bar").is_err());
    /// // Empty string is not a valid absolute IRI.
    /// assert!(IriAbsoluteStr::new("").is_err());
    /// ```
    ///
    /// Fragment part (such as trailing `#foo`) is not allowed.
    ///
    /// ```
    /// # use iri_string::types::IriAbsoluteStr;
    /// // Fragment part is not allowed.
    /// assert!(IriAbsoluteStr::new("https://example.com/foo?bar=baz#qux").is_err());
    /// ```
    ///
    /// Some characters and sequences cannot used in an absolute IRI.
    ///
    /// ```
    /// # use iri_string::types::IriAbsoluteStr;
    /// // `<` and `>` cannot directly appear in an absolute IRI.
    /// assert!(IriAbsoluteStr::new("<not allowed>").is_err());
    /// // Broken percent encoding cannot appear in an absolute IRI.
    /// assert!(IriAbsoluteStr::new("%").is_err());
    /// assert!(IriAbsoluteStr::new("%GG").is_err());
    /// ```
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC 3987]: https://tools.ietf.org/html/rfc3987
    /// [`absolute-IRI` rule]: https://tools.ietf.org/html/rfc3987#section-2.2
    /// [`absolute-URI` rule]: https://tools.ietf.org/html/rfc3986#section-4.3
    /// [`RiStr`]: struct.RiStr.html
    struct RiAbsoluteStr {
        validator = absolute_iri,
        expecting_msg = "Absolute IRI string",
    }
}

#[cfg(feature = "alloc")]
define_custom_string_owned! {
    /// An owned string of an absolute IRI without fragment part.
    ///
    /// This corresponds to [`absolute-IRI` rule] in [RFC 3987]
    /// (and [`absolute-URI` rule] in [RFC 3986]).
    /// The rule for `absolute-IRI` is `scheme ":" ihier-part [ "?" iquery ]`.
    /// In other words, this is [`RiString`] without fragment part.
    ///
    /// If you want to accept fragment part, use [`RiString`].
    ///
    /// For details, see the document for [`RiAbsoluteStr`].
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC 3987]: https://tools.ietf.org/html/rfc3987
    /// [`absolute-IRI` rule]: https://tools.ietf.org/html/rfc3987#section-2.2
    /// [`absolute-URI` rule]: https://tools.ietf.org/html/rfc3986#section-4.3
    /// [`RiAbsoluteStr`]: struct.RiAbsoluteStr.html
    /// [`RiString`]: struct.RiString.html
    struct RiAbsoluteString {
        validator = absolute_iri,
        slice = RiAbsoluteStr,
        expecting_msg = "Absolute IRI string",
    }
}

impl<S: Spec> RiAbsoluteStr<S> {
    /// Returns Ok`(())` if the IRI is normalizable by the RFC 3986 algorithm.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("HTTP://example.COM/foo/%2e/bar/..")?;
    /// assert!(iri.ensure_rfc3986_normalizable().is_ok());
    ///
    /// let iri2 = IriAbsoluteStr::new("scheme:/..//bar")?;
    /// // The normalization result would be `scheme://bar` according to RFC
    /// // 3986, but it is unintended and should be treated as a failure.
    /// // WHATWG URL Stardard handles this case.
    /// assert!(!iri.ensure_rfc3986_normalizable().is_err());
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn ensure_rfc3986_normalizable(&self) -> Result<(), Error> {
        NormalizationInput::from(self).ensure_rfc3986_normalizable()
    }

    /// Returns `true` if the IRI is already normalized.
    ///
    /// This returns the same result as
    /// `self.try_normalize.map_or(false, |normalized| normalized == self))`, but
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
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("HTTP://example.COM/foo/./bar/%2e%2e/../baz?query")?;
    /// assert!(!iri.is_normalized());
    ///
    /// let normalized = iri.try_normalize()?;
    /// assert_eq!(normalized, "http://example.com/baz?query");
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
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("HTTP://example.COM/foo/./bar/%2e%2e/../baz?query")?;
    ///
    /// let normalized = iri.try_normalize()?;
    /// assert_eq!(normalized, "http://example.com/baz?query");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[inline]
    pub fn try_normalize(&self) -> Result<RiAbsoluteString<S>, TaskError<Error>> {
        NormalizationTask::from(self).allocate_and_write()
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
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("HTTP://example.COM/foo/./bar/%2e%2e/../baz?query")?;
    ///
    /// let normalized = iri.try_normalize()?;
    /// assert_eq!(normalized, "http://example.com/baz?query");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[deprecated(
        since = "0.5.5",
        note = "Use `try_normalize()` for non-panicking normalization"
    )]
    #[inline]
    pub fn normalize(&self) -> Result<RiAbsoluteString<S>, TaskError<Error>> {
        self.try_normalize()
    }

    /// Returns `true` if the IRI is already normalized in the sense of WHATWG spec.
    ///
    /// This returns the same result as
    /// `self.try_normalize_whatwg.map_or(false, |normalized| normalized == self))`,
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
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("scheme:a/..//not-a-host")?;
    /// assert!(!iri.is_normalized_whatwg());
    ///
    /// let normalized = iri.try_normalize_whatwg()?;
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
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri1 = IriAbsoluteStr::new("scheme:/..//bar")?;
    /// assert!(iri1.try_normalize().is_err(), "`scheme://bar` is not intended result");
    /// assert_eq!(iri1.try_normalize_whatwg()?, "scheme:/.//bar");
    ///
    /// let iri2 = IriAbsoluteStr::new("scheme:..///bar")?;
    /// assert!(iri2.try_normalize().is_err(), "`scheme://bar` is not intended result");
    /// assert_eq!(iri2.try_normalize_whatwg()?, "scheme:/.//bar");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[inline]
    pub fn try_normalize_whatwg(&self) -> Result<RiAbsoluteString<S>, TaskError<Error>> {
        let mut task = NormalizationTask::from(self);
        task.enable_whatwg_serialization();
        task.allocate_and_write()
    }

    /// Returns the normalized IRI serialized using WHATWG URL Standard.
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
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri1 = IriAbsoluteStr::new("scheme:/..//bar")?;
    /// assert!(iri1.try_normalize().is_err(), "`scheme://bar` is not intended result");
    /// assert_eq!(iri1.try_normalize_whatwg()?, "scheme:/.//bar");
    ///
    /// let iri2 = IriAbsoluteStr::new("scheme:..///bar")?;
    /// assert!(iri2.try_normalize().is_err(), "`scheme://bar` is not intended result");
    /// assert_eq!(iri2.try_normalize_whatwg()?, "scheme:/.//bar");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[deprecated(
        since = "0.5.5",
        note = "Use `try_normalize_whatwg()` for non-panicking normalization"
    )]
    #[inline]
    pub fn normalize_whatwg(&self) -> Result<RiAbsoluteString<S>, TaskError<Error>> {
        self.try_normalize_whatwg()
    }
}

/// Components getters.
impl<S: Spec> RiAbsoluteStr<S> {
    /// Returns the scheme.
    ///
    /// The following colon is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("http://example.com/pathpath?queryquery")?;
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
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("http://example.com/pathpath?queryquery")?;
    /// assert_eq!(iri.authority_str(), Some("example.com"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
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
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("http://example.com/pathpath?queryquery")?;
    /// assert_eq!(iri.path_str(), "/pathpath");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
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
    /// use iri_string::types::{IriAbsoluteStr, IriQueryStr};
    ///
    /// let iri = IriAbsoluteStr::new("http://example.com/pathpath?queryquery")?;
    /// let query = IriQueryStr::new("queryquery")?;
    /// assert_eq!(iri.query(), Some(query));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
    /// assert_eq!(iri.query(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn query(&self) -> Option<&RiQueryStr<S>> {
        trusted_parser::extract_query_absolute_iri(self.as_str()).map(|query| unsafe {
            // This is safe because `extract_query` returns the query part of an IRI, and the
            // returned string is substring of the source IRI.
            RiQueryStr::new_maybe_unchecked(query)
        })
    }

    /// Returns the query in a raw string slice.
    ///
    /// The leading question mark (`?`) is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("http://example.com/pathpath?queryquery")?;
    /// assert_eq!(iri.query_str(), Some("queryquery"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
    /// assert_eq!(iri.query_str(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn query_str(&self) -> Option<&str> {
        trusted_parser::extract_query_absolute_iri(self.as_str())
    }

    /// Returns the authority components.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("http://user:pass@example.com:8080/pathpath?queryquery")?;
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
    /// use iri_string::types::IriAbsoluteStr;
    ///
    /// let iri = IriAbsoluteStr::new("urn:uuid:10db315b-fcd1-4428-aca8-15babc9a2da2")?;
    /// assert_eq!(iri.authority_str(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn authority_components(&self) -> Option<AuthorityComponents<'_>> {
        AuthorityComponents::from_iri(self.as_ref())
    }
}

impl_trivial_conv_between_iri! {
    from_slice: RiAbsoluteStr,
    from_owned: RiAbsoluteString,
    to_slice: RiStr,
    to_owned: RiString,
}

impl_trivial_conv_between_iri! {
    from_slice: RiAbsoluteStr,
    from_owned: RiAbsoluteString,
    to_slice: RiReferenceStr,
    to_owned: RiReferenceString,
}
