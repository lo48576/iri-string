//! IRI-specific implementations.

#[cfg(feature = "alloc")]
use crate::types::{
    RiAbsoluteString, RiFragmentString, RiReferenceString, RiRelativeString, RiString,
};
use crate::{
    spec::IriSpec,
    types::{RiAbsoluteStr, RiFragmentStr, RiReferenceStr, RiRelativeStr, RiStr},
};

/// A borrowed string type for an absolute IRI.
pub type IriAbsoluteStr = RiAbsoluteStr<IriSpec>;

/// An owned string type for an absolute IRI.
#[cfg(feature = "alloc")]
pub type IriAbsoluteString = RiAbsoluteString<IriSpec>;

/// A borrowed string type for a fragment part of an IRI.
pub type IriFragmentStr = RiFragmentStr<IriSpec>;

/// An owned string type for a fragment part of an IRI.
#[cfg(feature = "alloc")]
pub type IriFragmentString = RiFragmentString<IriSpec>;

/// A borrowed string type for an IRI.
pub type IriStr = RiStr<IriSpec>;

/// An owned string type for an IRI.
#[cfg(feature = "alloc")]
pub type IriString = RiString<IriSpec>;

/// A borrowed string type for an IRI reference.
pub type IriReferenceStr = RiReferenceStr<IriSpec>;

/// An owned string type for an IRI reference.
#[cfg(feature = "alloc")]
pub type IriReferenceString = RiReferenceString<IriSpec>;

/// A borrowed string type for a relative IRI reference.
pub type IriRelativeStr = RiRelativeStr<IriSpec>;

/// An owned string type for a relative IRI reference.
#[cfg(feature = "alloc")]
pub type IriRelativeString = RiRelativeString<IriSpec>;
