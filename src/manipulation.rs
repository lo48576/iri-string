//! IRI strings manipulation.

#[cfg(feature = "alloc")]
use alloc::string::String;

#[cfg(feature = "alloc")]
pub(crate) use self::owned::CustomIriOwnedExt;
pub(crate) use self::slice::CustomIriSliceExt;

#[cfg(feature = "alloc")]
mod owned;
pub(crate) mod raw;
mod slice;

/// A type that indicate the value does not exist.
pub(crate) enum Void {}

impl AsRef<str> for Void {
    fn as_ref(&self) -> &str {
        unreachable!("Reference to `Void` value should never exist")
    }
}

#[cfg(feature = "alloc")]
impl Into<String> for Void {
    fn into(self) -> String {
        unreachable!("`Void` value should never exist")
    }
}
