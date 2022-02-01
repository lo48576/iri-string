//! URI-specific implementations.

use crate::spec::UriSpec;
use crate::types::{
    IriAbsoluteStr, IriFragmentStr, IriReferenceStr, IriRelativeStr, IriStr, RiAbsoluteStr,
    RiFragmentStr, RiReferenceStr, RiRelativeStr, RiStr,
};
#[cfg(feature = "alloc")]
use crate::types::{
    IriAbsoluteString, IriFragmentString, IriReferenceString, IriRelativeString, IriString,
    RiAbsoluteString, RiFragmentString, RiReferenceString, RiRelativeString, RiString,
};

/// A borrowed string type for an absolute URI.
pub type UriAbsoluteStr = RiAbsoluteStr<UriSpec>;

/// An owned string type for an absolute URI.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type UriAbsoluteString = RiAbsoluteString<UriSpec>;

/// A borrowed string type for a fragment part of an URI.
pub type UriFragmentStr = RiFragmentStr<UriSpec>;

/// An owned string type for a fragment part of an URI.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type UriFragmentString = RiFragmentString<UriSpec>;

/// A borrowed string type for an URI.
pub type UriStr = RiStr<UriSpec>;

/// An owned string type for an URI.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type UriString = RiString<UriSpec>;

/// A borrowed string type for an URI reference.
pub type UriReferenceStr = RiReferenceStr<UriSpec>;

/// An owned string type for an URI reference.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type UriReferenceString = RiReferenceString<UriSpec>;

/// A borrowed string type for a relative URI reference.
pub type UriRelativeStr = RiRelativeStr<UriSpec>;

/// An owned string type for a relative URI reference.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub type UriRelativeString = RiRelativeString<UriSpec>;

/// Implements the trivial conversions between a URI and an IRI.
macro_rules! impl_conversions_between_iri {
    (
        $borrowed_uri:ident,
        $owned_uri:ident,
        $borrowed_iri:ident,
        $owned_iri:ident,
    ) => {
        impl AsRef<$borrowed_iri> for $borrowed_uri {
            fn as_ref(&self) -> &$borrowed_iri {
                unsafe {
                    // SAFETY: A valid URI is also a valid IRI.
                    <$borrowed_iri>::new_maybe_unchecked(self.as_str())
                }
            }
        }

        #[cfg(feature = "alloc")]
        impl From<$owned_uri> for $owned_iri {
            #[inline]
            fn from(uri: $owned_uri) -> Self {
                unsafe {
                    // SAFETY: A valid URI is also a valid IRI.
                    Self::new_maybe_unchecked(uri.into())
                }
            }
        }

        #[cfg(feature = "alloc")]
        impl AsRef<$borrowed_iri> for $owned_uri {
            fn as_ref(&self) -> &$borrowed_iri {
                AsRef::<$borrowed_uri>::as_ref(self).as_ref()
            }
        }
    };
}

impl_conversions_between_iri!(
    UriAbsoluteStr,
    UriAbsoluteString,
    IriAbsoluteStr,
    IriAbsoluteString,
);
impl_conversions_between_iri!(
    UriReferenceStr,
    UriReferenceString,
    IriReferenceStr,
    IriReferenceString,
);
impl_conversions_between_iri!(
    UriRelativeStr,
    UriRelativeString,
    IriRelativeStr,
    IriRelativeString,
);
impl_conversions_between_iri!(UriStr, UriString, IriStr, IriString,);
impl_conversions_between_iri!(
    UriFragmentStr,
    UriFragmentString,
    IriFragmentStr,
    IriFragmentString,
);
