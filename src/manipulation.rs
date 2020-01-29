//! IRI strings manipulation.

mod owned;
pub(crate) mod raw;
mod slice;

pub(crate) use self::{owned::CustomIriOwnedExt, slice::CustomIriSliceExt};

/// A type that indicate the value does not exist.
pub(crate) enum Void {}

impl AsRef<str> for Void {
    fn as_ref(&self) -> &str {
        unreachable!("Reference to `Void` value should never exist")
    }
}

impl Into<String> for Void {
    fn into(self) -> String {
        unreachable!("`Void` value should never exist")
    }
}
