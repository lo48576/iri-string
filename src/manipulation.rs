//! IRI strings manipulation.

#[cfg(feature = "std")]
mod owned;
pub(crate) mod raw;
mod slice;

#[cfg(feature = "std")]
pub(crate) use self::owned::CustomIriOwnedExt;
pub(crate) use self::slice::CustomIriSliceExt;

/// A type that indicate the value does not exist.
pub(crate) enum Void {}

impl AsRef<str> for Void {
    fn as_ref(&self) -> &str {
        unreachable!("Reference to `Void` value should never exist")
    }
}

#[cfg(feature = "std")]
impl Into<String> for Void {
    fn into(self) -> String {
        unreachable!("`Void` value should never exist")
    }
}
