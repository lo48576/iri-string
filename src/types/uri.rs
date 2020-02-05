//! URI-specific implementations.

#[cfg(feature = "alloc")]
use crate::types::{
    RiAbsoluteString, RiFragmentString, RiReferenceString, RiRelativeString, RiString,
};
use crate::{
    spec::UriSpec,
    types::{RiAbsoluteStr, RiFragmentStr, RiReferenceStr, RiRelativeStr, RiStr},
};

/// A borrowed string type for an absolute URI.
pub type UriAbsoluteStr = RiAbsoluteStr<UriSpec>;

/// An owned string type for an absolute URI.
#[cfg(feature = "alloc")]
pub type UriAbsoluteString = RiAbsoluteString<UriSpec>;

/// A borrowed string type for a fragment part of an URI.
pub type UriFragmentStr = RiFragmentStr<UriSpec>;

/// An owned string type for a fragment part of an URI.
#[cfg(feature = "alloc")]
pub type UriFragmentString = RiFragmentString<UriSpec>;

/// A borrowed string type for an URI.
pub type UriStr = RiStr<UriSpec>;

/// An owned string type for an URI.
#[cfg(feature = "alloc")]
pub type UriString = RiString<UriSpec>;

/// A borrowed string type for an URI reference.
pub type UriReferenceStr = RiReferenceStr<UriSpec>;

/// An owned string type for an URI reference.
#[cfg(feature = "alloc")]
pub type UriReferenceString = RiReferenceString<UriSpec>;

/// A borrowed string type for a relative URI reference.
pub type UriRelativeStr = RiRelativeStr<UriSpec>;

/// An owned string type for a relative URI reference.
#[cfg(feature = "alloc")]
pub type UriRelativeString = RiRelativeString<UriSpec>;
