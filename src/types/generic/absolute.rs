//! Absolute IRI (without fragment part).

#[cfg(feature = "alloc")]
use crate::types::{RiReferenceString, RiString};
use crate::{
    types::{RiReferenceStr, RiStr},
    validate::absolute_iri,
};

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
    /// # use iri_string::types::AbsoluteIriStr;
    /// assert!(AbsoluteIriStr::new("https://example.com/foo?bar=baz").is_ok());
    /// assert!(AbsoluteIriStr::new("foo:bar").is_ok());
    /// // Scheme `foo` and empty path.
    /// assert!(AbsoluteIriStr::new("foo:").is_ok());
    /// // `foo://.../` below are all allowed. See the crate documentation for detail.
    /// assert!(AbsoluteIriStr::new("foo:/").is_ok());
    /// assert!(AbsoluteIriStr::new("foo://").is_ok());
    /// assert!(AbsoluteIriStr::new("foo:///").is_ok());
    /// assert!(AbsoluteIriStr::new("foo:////").is_ok());
    /// assert!(AbsoluteIriStr::new("foo://///").is_ok());
    ///
    /// ```
    ///
    /// Relative IRI is not allowed.
    ///
    /// ```
    /// # use iri_string::types::AbsoluteIriStr;
    /// // This is relative path.
    /// assert!(AbsoluteIriStr::new("foo/bar").is_err());
    /// // `/foo/bar` is an absolute path, but it is authority-relative.
    /// assert!(AbsoluteIriStr::new("/foo/bar").is_err());
    /// // `//foo/bar` is termed "network-path reference",
    /// // or usually called "protocol-relative reference".
    /// assert!(AbsoluteIriStr::new("//foo/bar").is_err());
    /// // Empty string is not a valid absolute IRI.
    /// assert!(AbsoluteIriStr::new("").is_err());
    /// ```
    ///
    /// Fragment part (such as trailing `#foo`) is not allowed.
    ///
    /// ```
    /// # use iri_string::types::AbsoluteIriStr;
    /// // Fragment part is not allowed.
    /// assert!(AbsoluteIriStr::new("https://example.com/foo?bar=baz#qux").is_err());
    /// ```
    ///
    /// Some characters and sequences cannot used in an absolute IRI.
    ///
    /// ```
    /// # use iri_string::types::AbsoluteIriStr;
    /// // `<` and `>` cannot directly appear in an absolute IRI.
    /// assert!(AbsoluteIriStr::new("<not allowed>").is_err());
    /// // Broken percent encoding cannot appear in an absolute IRI.
    /// assert!(AbsoluteIriStr::new("%").is_err());
    /// assert!(AbsoluteIriStr::new("%GG").is_err());
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

impl_infallible_conv_between_iri! {
    from_slice: RiAbsoluteStr,
    from_owned: RiAbsoluteString,
    to_slice: RiStr,
    to_owned: RiString,
}

impl_infallible_conv_between_iri! {
    from_slice: RiAbsoluteStr,
    from_owned: RiAbsoluteString,
    to_slice: RiReferenceStr,
    to_owned: RiReferenceString,
}
