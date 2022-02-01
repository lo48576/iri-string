//! Absolute IRI (without fragment part).

use crate::components::AuthorityComponents;
#[cfg(feature = "alloc")]
use crate::normalize::{Error, NormalizationTask};
use crate::parser::trusted as trusted_parser;
use crate::spec::Spec;
#[cfg(feature = "alloc")]
use crate::task::{Error as TaskError, ProcessAndWrite};
use crate::types::{RiReferenceStr, RiStr};
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
    /// Returns the normalized IRI.
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
    /// let normalized = iri.normalize()?;
    /// assert_eq!(normalized, "http://example.com/baz?query");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn normalize(&self) -> Result<RiAbsoluteString<S>, TaskError<Error>> {
        NormalizationTask::from(self).allocate_and_write()
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
