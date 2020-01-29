//! Extension traits implementation for custom string slice types.

use crate::{
    manipulation::{raw, Void},
    types,
};

/// A trait for custom string types.
pub(crate) trait CustomSlice: AsRef<str> {
    /// Creates a new IRI without validation.
    ///
    /// This may do validation on debug build.
    ///
    /// # Safety
    ///
    /// The given string must be valid as the type `Self`.
    // Note that IRI string types internally does validation in debug build, even in
    // `new_unchecked()`.
    unsafe fn new_unchecked(s: &str) -> &Self;

    /// Returns `&str`.
    #[inline]
    fn as_str(&self) -> &str {
        self.as_ref()
    }
}

impl CustomSlice for Void {
    #[inline]
    unsafe fn new_unchecked(_: &str) -> &Self {
        // If this happen, it is a bug of this crate.
        panic!("Program should never attempt to create `Void` value or a reference to `Void`")
    }
}

impl CustomSlice for types::AbsoluteIriStr {
    #[inline]
    unsafe fn new_unchecked(s: &str) -> &Self {
        Self::new_unchecked(s)
    }
}

impl CustomSlice for types::IriFragmentStr {
    #[inline]
    unsafe fn new_unchecked(s: &str) -> &Self {
        Self::new_unchecked(s)
    }
}

impl CustomSlice for types::IriReferenceStr {
    #[inline]
    unsafe fn new_unchecked(s: &str) -> &Self {
        Self::new_unchecked(s)
    }
}

impl CustomSlice for types::IriStr {
    #[inline]
    unsafe fn new_unchecked(s: &str) -> &Self {
        Self::new_unchecked(s)
    }
}

impl CustomSlice for types::RelativeIriStr {
    #[inline]
    unsafe fn new_unchecked(s: &str) -> &Self {
        Self::new_unchecked(s)
    }
}

/// A trait for custom URI / IRI string types.
pub(crate) trait CustomIriSliceExt: CustomSlice {
    /// A type for a string without fragment part.
    type WithoutFragmentSlice: ?Sized + CustomSlice;
    /// A type for a fragment part.
    type FragmentSlice: ?Sized + CustomSlice;

    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    fn fragment(&self) -> Option<&Self::FragmentSlice> {
        raw::split_fragment(self.as_ref()).1.map(|fragment| unsafe {
            // This should be safe because the fragment part of the valid
            // IRI is guaranteed to be a valid fragment.
            <Self::FragmentSlice>::new_unchecked(fragment)
        })
    }

    /// Splits the string into the prefix and the fragment part, and only returns the prefix part.
    ///
    /// Returns the same value as `.split_fragment().0`, but `.without_fragment()` is more
    /// efficient.
    fn without_fragment(&self) -> &Self::WithoutFragmentSlice {
        let prefix_len = raw::split_fragment(self.as_ref()).0.len();
        unsafe {
            // This is safe because the kind of an IRI does not change if
            // the fragment part is removed.
            <Self::WithoutFragmentSlice>::new_unchecked(&self.as_str()[..prefix_len])
        }
    }

    /// Splits the string into the prefix and the fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    fn split_fragment(&self) -> (&Self::WithoutFragmentSlice, Option<&Self::FragmentSlice>) {
        let (prefix, fragment) = raw::split_fragment(self.as_ref());
        let prefix = unsafe {
            // This is safe because the kind of an IRI does not change if
            // the fragment part is removed.
            <Self::WithoutFragmentSlice>::new_unchecked(prefix)
        };
        let fragment = fragment.map(|fragment| unsafe {
            // This is safe because the fragment part of the valid
            // `IriReferenceStr` is guaranteed to be a valid fragment.
            <Self::FragmentSlice>::new_unchecked(fragment)
        });

        (prefix, fragment)
    }
}

impl CustomIriSliceExt for types::AbsoluteIriStr {
    type WithoutFragmentSlice = Self;
    type FragmentSlice = Void;

    #[inline]
    fn split_fragment(&self) -> (&Self::WithoutFragmentSlice, Option<&Self::FragmentSlice>) {
        (self, None)
    }
}

impl CustomIriSliceExt for types::IriReferenceStr {
    type WithoutFragmentSlice = Self;
    type FragmentSlice = types::IriFragmentStr;
}

impl CustomIriSliceExt for types::IriStr {
    type WithoutFragmentSlice = types::AbsoluteIriStr;
    type FragmentSlice = types::IriFragmentStr;
}

impl CustomIriSliceExt for types::RelativeIriStr {
    type WithoutFragmentSlice = Self;
    type FragmentSlice = types::IriFragmentStr;
}
