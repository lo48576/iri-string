//! IRI-specific implementations.

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
#[cfg(feature = "alloc")]
use crate::types::{
    UriAbsoluteString, UriFragmentString, UriReferenceString, UriRelativeString, UriString,
};

/// A borrowed string type for an absolute IRI.
pub type IriAbsoluteStr = RiAbsoluteStr<IriSpec>;

/// An owned string type for an absolute IRI.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriAbsoluteString = RiAbsoluteString<IriSpec>;

/// A borrowed string type for a fragment part of an IRI.
pub type IriFragmentStr = RiFragmentStr<IriSpec>;

/// An owned string type for a fragment part of an IRI.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriFragmentString = RiFragmentString<IriSpec>;

/// A borrowed string type for an IRI.
pub type IriStr = RiStr<IriSpec>;

/// An owned string type for an IRI.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriString = RiString<IriSpec>;

/// A borrowed string type for an IRI reference.
pub type IriReferenceStr = RiReferenceStr<IriSpec>;

/// An owned string type for an IRI reference.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriReferenceString = RiReferenceString<IriSpec>;

/// A borrowed string type for a relative IRI reference.
pub type IriRelativeStr = RiRelativeStr<IriSpec>;

/// An owned string type for a relative IRI reference.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type IriRelativeString = RiRelativeString<IriSpec>;

/// Implements the conversion from an IRI into a URI.
macro_rules! impl_encode_to_uri {
    (
        $ty_owned_iri:ident,
        $ty_owned_uri:ident,
        $ty_borrowed_iri:ident,
        $ty_borrowed_uri:ident,
        $example_iri:expr,
        $example_uri:expr
    ) => {
        /// Conversion from an IRI into a URI.
        #[cfg(feature = "alloc")]
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
            pub fn encode_to_uri(&self) -> $ty_owned_uri {
                MappedToUri::from(self).allocate_and_write().expect("failed to allocate memory")
            }
        }

        /// Conversion from an IRI into a URI.
        #[cfg(feature = "alloc")]
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
        }
    };
}

impl_encode_to_uri!(
    IriAbsoluteString,
    UriAbsoluteString,
    IriAbsoluteStr,
    UriAbsoluteStr,
    "http://example.com/?alpha=\u{03B1}",
    "http://example.com/?alpha=%CE%B1"
);
impl_encode_to_uri!(
    IriReferenceString,
    UriReferenceString,
    IriReferenceStr,
    UriReferenceStr,
    "http://example.com/?alpha=\u{03B1}",
    "http://example.com/?alpha=%CE%B1"
);
impl_encode_to_uri!(
    IriRelativeString,
    UriRelativeString,
    IriRelativeStr,
    UriRelativeStr,
    "../?alpha=\u{03B1}",
    "../?alpha=%CE%B1"
);
impl_encode_to_uri!(
    IriString,
    UriString,
    IriStr,
    UriStr,
    "http://example.com/?alpha=\u{03B1}",
    "http://example.com/?alpha=%CE%B1"
);
impl_encode_to_uri!(
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
