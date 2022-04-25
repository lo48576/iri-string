//! IRI-specific implementations.

#[cfg(feature = "alloc")]
use alloc::string::String;

#[cfg(feature = "alloc")]
use crate::convert::{try_percent_encode_iri_inline, MappedToUri};
use crate::spec::IriSpec;
#[cfg(feature = "alloc")]
use crate::task::ProcessAndWrite;
use crate::types::{RiAbsoluteStr, RiFragmentStr, RiReferenceStr, RiRelativeStr, RiStr};
#[cfg(feature = "alloc")]
use crate::types::{
    RiAbsoluteString, RiFragmentString, RiReferenceString, RiRelativeString, RiString,
};
use crate::types::{UriAbsoluteStr, UriFragmentStr, UriReferenceStr, UriRelativeStr, UriStr};
#[cfg(feature = "alloc")]
use crate::types::{
    UriAbsoluteString, UriFragmentString, UriReferenceString, UriRelativeString, UriString,
};

/// A type alias for [`RiAbsoluteStr`]`<`[`IriSpec`]`>`.
pub type IriAbsoluteStr = RiAbsoluteStr<IriSpec>;

/// A type alias for [`RiAbsoluteString`]`<`[`IriSpec`]`>`.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriAbsoluteString = RiAbsoluteString<IriSpec>;

/// A type alias for [`RiFragmentStr`]`<`[`IriSpec`]`>`.
pub type IriFragmentStr = RiFragmentStr<IriSpec>;

/// A type alias for [`RiFragmentString`]`<`[`IriSpec`]`>`.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriFragmentString = RiFragmentString<IriSpec>;

/// A type alias for [`RiStr`]`<`[`IriSpec`]`>`.
pub type IriStr = RiStr<IriSpec>;

/// A type alias for [`RiString`]`<`[`IriSpec`]`>`.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriString = RiString<IriSpec>;

/// A type alias for [`RiReferenceStr`]`<`[`IriSpec`]`>`.
pub type IriReferenceStr = RiReferenceStr<IriSpec>;

/// A type alias for [`RiReferenceString`]`<`[`IriSpec`]`>`.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriReferenceString = RiReferenceString<IriSpec>;

/// A type alias for [`RiRelativeStr`]`<`[`IriSpec`]`>`.
pub type IriRelativeStr = RiRelativeStr<IriSpec>;

/// A type alias for [`RiRelativeString`]`<`[`IriSpec`]`>`.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriRelativeString = RiRelativeString<IriSpec>;

/// Implements the conversion from an IRI into a URI.
macro_rules! impl_conversion_between_uri {
    (
        $ty_owned_iri:ident,
        $ty_owned_uri:ident,
        $ty_borrowed_iri:ident,
        $ty_borrowed_uri:ident,
        $example_iri:expr,
        $example_uri:expr
    ) => {
        /// Conversion from an IRI into a URI.
        impl $ty_borrowed_iri {
            /// Percent-encodes the IRI into a valid URI that identifies the equivalent resource.
            ///
            /// If you need more precise control over memory allocation and buffer
            /// handling, use [`MappedToUri`][`crate::convert::MappedToUri`] type.
            ///
            /// # Examples
            ///
            /// ```
            /// # use iri_string::validate::Error;
            /// # #[cfg(feature = "alloc")] {
            #[doc = concat!("use iri_string::types::{", stringify!($ty_borrowed_iri), ", ", stringify!($ty_owned_uri), "};")]
            ///
            #[doc = concat!("let iri = ", stringify!($ty_borrowed_iri), "::new(", stringify!($example_iri), ")?;")]
            /// // Type annotation here is not necessary.
            #[doc = concat!("let uri: ", stringify!($ty_owned_uri), " = iri.encode_to_uri();")]
            #[doc = concat!("assert_eq!(uri, ", stringify!($example_uri), ");")]
            /// # }
            /// # Ok::<_, Error>(())
            /// ```
            #[cfg(feature = "alloc")]
            #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
            pub fn encode_to_uri(&self) -> $ty_owned_uri {
                MappedToUri::from(self).allocate_and_write().expect("failed to allocate memory")
            }

            /// Converts an IRI into a URI without modification, if possible.
            ///
            /// This is semantically equivalent to
            #[doc = concat!("`", stringify!($ty_borrowed_uri), "::new(self.as_str()).ok()`.")]
            ///
            /// # Examples
            ///
            /// ```
            /// # use iri_string::validate::Error;
            #[doc = concat!("use iri_string::types::{", stringify!($ty_borrowed_iri), ", ", stringify!($ty_borrowed_uri), "};")]
            ///
            #[doc = concat!("let ascii_iri = ", stringify!($ty_borrowed_iri), "::new(", stringify!($example_uri), ")?;")]
            /// assert_eq!(
            ///     ascii_iri.as_uri().map(AsRef::as_ref),
            #[doc = concat!("    Some(", stringify!($example_uri), ")")]
            /// );
            ///
            #[doc = concat!("let nonascii_iri = ", stringify!($ty_borrowed_iri), "::new(", stringify!($example_iri), ")?;")]
            /// assert_eq!(nonascii_iri.as_uri(), None);
            /// # Ok::<_, Error>(())
            /// ```
            pub fn as_uri(&self) -> Option<&$ty_borrowed_uri> {
                if !self.as_str().is_ascii() {
                    return None;
                }
                debug_assert!(
                    <$ty_borrowed_uri>::new(self.as_str()).is_ok(),
                    "[consistency] the ASCII-only IRI must also be a valid URI"
                );
                let uri = unsafe {
                    // SAFETY: An ASCII-only IRI is a URI.
                    // URI (by `UriSpec`) is a subset of IRI (by `IriSpec`),
                    // and the difference is that URIs can only have ASCII characters.
                    <$ty_borrowed_uri>::new_maybe_unchecked(self.as_str())
                };
                Some(uri)
            }
        }

        /// Conversion from an IRI into a URI.
        #[cfg(feature = "alloc")]
        #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
        impl $ty_owned_iri {
            /// Percent-encodes the IRI into a valid URI that identifies the equivalent resource.
            ///
            /// After the encode, the IRI is also a valid URI.
            ///
            /// If you want a new URI string rather than modifying the IRI string,
            /// use [`encode_into_uri`][`Self::encode_into_uri`] method.
            ///
            /// If you need more precise control over memory allocation and buffer
            /// handling, use [`MappedToUri`][`crate::convert::MappedToUri`] type.
            ///
            /// # Examples
            ///
            /// ```
            /// # use iri_string::validate::Error;
            /// #[cfg(feature = "alloc")] {
            #[doc = concat!("use iri_string::types::", stringify!($ty_owned_iri), ";")]
            ///
            #[doc = concat!("let mut iri = ", stringify!($ty_owned_iri), "::try_from(", stringify!($example_iri), ")?;")]
            /// iri.encode_to_uri();
            #[doc = concat!("assert_eq!(iri, ", stringify!($example_uri), ");")]
            /// # }
            /// # Ok::<_, Error>(())
            /// ```
            pub fn encode_to_uri(&mut self) {
                try_percent_encode_iri_inline(self.as_inner_mut())
                    .expect("failed to allocate memory");
                debug_assert!(
                    <$ty_borrowed_iri>::new(self.as_str()).is_ok(),
                    "[consistency] the content must be valid at any time"
                );
            }

            /// Percent-encodes the IRI into a valid URI that identifies the equivalent resource.
            ///
            /// If you want to modify the value rather than creating a new
            /// URI string, use [`encode_to_uri`][`Self::encode_to_uri`] method.
            ///
            /// If you need more precise control over memory allocation and buffer
            /// handling, use [`MappedToUri`][`crate::convert::MappedToUri`] type.
            ///
            /// # Examples
            ///
            /// ```
            /// # use iri_string::validate::Error;
            /// #[cfg(feature = "alloc")] {
            #[doc = concat!("use iri_string::types::{", stringify!($ty_owned_iri), ", ", stringify!($ty_owned_uri), "};")]
            ///
            #[doc = concat!("let iri = ", stringify!($ty_owned_iri), "::try_from(", stringify!($example_iri), ")?;")]
            /// // Type annotation here is not necessary.
            #[doc = concat!("let uri: ", stringify!($ty_owned_uri), " = iri.encode_into_uri();")]
            #[doc = concat!("assert_eq!(uri, ", stringify!($example_uri), ");")]
            /// # }
            /// # Ok::<_, Error>(())
            /// ```
            pub fn encode_into_uri(self) -> $ty_owned_uri {
                MappedToUri::from(self.as_slice()).allocate_and_write().expect("failed to allocate memory")
            }

            /// Converts an IRI into a URI without modification, if possible.
            ///
            /// # Examples
            ///
            /// ```
            /// # use iri_string::validate::Error;
            #[doc = concat!("use iri_string::types::{", stringify!($ty_owned_iri), ", ", stringify!($ty_owned_uri), "};")]
            ///
            #[doc = concat!("let ascii_iri = ", stringify!($ty_owned_iri), "::try_from(", stringify!($example_uri), ")?;")]
            /// assert_eq!(
            ///     ascii_iri.try_into_uri().map(|uri| uri.to_string()),
            #[doc = concat!("    Ok(", stringify!($example_uri), ".to_string())")]
            /// );
            ///
            #[doc = concat!("let nonascii_iri = ", stringify!($ty_owned_iri), "::try_from(", stringify!($example_iri), ")?;")]
            /// assert_eq!(
            ///     nonascii_iri.try_into_uri().map_err(|iri| iri.to_string()),
            #[doc = concat!("    Err(", stringify!($example_iri), ".to_string())")]
            /// );
            /// # Ok::<_, Error>(())
            /// ```
            pub fn try_into_uri(self) -> Result<$ty_owned_uri, $ty_owned_iri> {
                if !self.as_str().is_ascii() {
                    return Err(self);
                }
                let s: String = self.into();
                debug_assert!(
                    <$ty_borrowed_uri>::new(s.as_str()).is_ok(),
                    "[consistency] the ASCII-only IRI must also be a valid URI"
                );
                let uri = unsafe {
                    // SAFETY: An ASCII-only IRI is a URI.
                    // URI (by `UriSpec`) is a subset of IRI (by `IriSpec`),
                    // and the difference is that URIs can only have ASCII characters.
                    <$ty_owned_uri>::new_maybe_unchecked(s)
                };
                Ok(uri)
            }
        }
    };
}

impl_conversion_between_uri!(
    IriAbsoluteString,
    UriAbsoluteString,
    IriAbsoluteStr,
    UriAbsoluteStr,
    "http://example.com/?alpha=\u{03B1}",
    "http://example.com/?alpha=%CE%B1"
);
impl_conversion_between_uri!(
    IriReferenceString,
    UriReferenceString,
    IriReferenceStr,
    UriReferenceStr,
    "http://example.com/?alpha=\u{03B1}",
    "http://example.com/?alpha=%CE%B1"
);
impl_conversion_between_uri!(
    IriRelativeString,
    UriRelativeString,
    IriRelativeStr,
    UriRelativeStr,
    "../?alpha=\u{03B1}",
    "../?alpha=%CE%B1"
);
impl_conversion_between_uri!(
    IriString,
    UriString,
    IriStr,
    UriStr,
    "http://example.com/?alpha=\u{03B1}",
    "http://example.com/?alpha=%CE%B1"
);
impl_conversion_between_uri!(
    IriFragmentString,
    UriFragmentString,
    IriFragmentStr,
    UriFragmentStr,
    "alpha-is-\u{03B1}",
    "alpha-is-%CE%B1"
);

#[cfg(test)]
#[cfg(feature = "alloc")]
mod tests {
    use crate::types::{IriReferenceString, UriReferenceStr};

    const CASES: &[(&str, &str)] = &[
        ("?alpha=\u{03B1}", "?alpha=%CE%B1"),
        (
            "?katakana-letter-i=\u{30A4}",
            "?katakana-letter-i=%E3%82%A4",
        ),
        ("?sushi=\u{1f363}", "?sushi=%F0%9F%8D%A3"),
    ];

    #[test]
    fn iri_to_uri() {
        for (iri, expected_uri) in CASES {
            let expected_uri =
                UriReferenceStr::new(*expected_uri).expect("test cases must be valid");

            let mut iri = IriReferenceString::try_from(*iri).expect("test cases must be valid");
            iri.encode_to_uri();
            assert_eq!(iri, expected_uri);
            iri.encode_to_uri();
            assert_eq!(iri, expected_uri, "`encode_to_uri` must be idempotent");
        }
    }
}
