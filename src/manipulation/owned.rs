//! Extension traits implementation for custom owned string types.

use crate::{
    manipulation::{raw, Void},
    types,
};

/// A trait for custom string types.
pub(crate) trait CustomOwned: Sized + AsRef<str> + Into<String> {
    /// Creates a new IRI without validation.
    ///
    /// This may do validation on debug build.
    ///
    /// # Safety
    ///
    /// The given string must be valid as the type `Self`.
    // Note that IRI string types internally does validation in debug build, even in
    // `new_unchecked()`.
    unsafe fn new_unchecked(s: String) -> Self;
}

impl CustomOwned for Void {
    #[inline]
    unsafe fn new_unchecked(_: String) -> Self {
        // If this happen, it is a bug of this crate.
        panic!("Program should never attempt to create `Void` value")
    }
}

impl CustomOwned for types::AbsoluteIriString {
    #[inline]
    unsafe fn new_unchecked(s: String) -> Self {
        Self::new_unchecked(s)
    }
}

impl CustomOwned for types::IriFragmentString {
    #[inline]
    unsafe fn new_unchecked(s: String) -> Self {
        Self::new_unchecked(s)
    }
}

impl CustomOwned for types::IriReferenceString {
    #[inline]
    unsafe fn new_unchecked(s: String) -> Self {
        Self::new_unchecked(s)
    }
}

impl CustomOwned for types::IriString {
    #[inline]
    unsafe fn new_unchecked(s: String) -> Self {
        Self::new_unchecked(s)
    }
}

impl CustomOwned for types::RelativeIriString {
    #[inline]
    unsafe fn new_unchecked(s: String) -> Self {
        Self::new_unchecked(s)
    }
}

/// A trait for custom URI / IRI string types.
pub(crate) trait CustomIriOwnedExt: CustomOwned {
    /// A type for a string without fragment part.
    type WithoutFragmentOwned: ?Sized + CustomOwned;
    /// A type for a fragment part.
    type FragmentOwned: ?Sized + CustomOwned;

    /// Returns a new string with fragment part removed.
    ///
    /// Returns the same value as `.split_fragment().0`, but `.without_fragment()` is more
    /// efficient.
    fn without_fragment(self) -> Self::WithoutFragmentOwned {
        let mut s: String = self.into();
        raw::remove_fragment(&mut s);
        unsafe {
            // This should be safe because `self` with the fragment part should be valid as
            // `WithoutFragmentOwned`.
            <Self::WithoutFragmentOwned>::new_unchecked(s)
        }
    }

    /// Splits the string into the prefix and the fragment part.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    fn split_fragment(self) -> (Self::WithoutFragmentOwned, Option<Self::FragmentOwned>) {
        let (prefix, fragment) = raw::split_fragment(self.as_ref());
        if fragment.is_none() {
            let abs_iri = unsafe {
                // This should be safe because `self` with the fragment part should be valid as
                // `WithoutFragmentOwned`.
                <Self::WithoutFragmentOwned>::new_unchecked(self.into())
            };
            return (abs_iri, None);
        }
        let prefix_len = prefix.len();

        let mut s: String = self.into();
        // `+ 1` is for leading `#` character.
        let fragment = s.split_off(prefix_len + 1);
        // Current `s` contains a trailing `#` character, which should be removed.
        {
            // Remove a trailing `#`.
            let hash = s.pop();
            assert_eq!(hash, Some('#'));
        }
        assert_eq!(s.len(), prefix_len);
        let prefix = unsafe {
            // This should be safe because `self` with the fragment part should be valid as
            // `WithoutFragmentOwned`.
            <Self::WithoutFragmentOwned>::new_unchecked(s)
        };
        let fragment = unsafe {
            // This should be safe because the fragment part of `self` should be valid as
            // `FragmentOwned`.
            <Self::FragmentOwned>::new_unchecked(fragment)
        };
        (prefix, Some(fragment))
    }
}

impl CustomIriOwnedExt for types::AbsoluteIriString {
    type WithoutFragmentOwned = Self;
    type FragmentOwned = Void;

    #[inline]
    fn split_fragment(self) -> (Self::WithoutFragmentOwned, Option<Self::FragmentOwned>) {
        (self, None)
    }
}

impl CustomIriOwnedExt for types::IriReferenceString {
    type WithoutFragmentOwned = Self;
    type FragmentOwned = types::IriFragmentString;
}

impl CustomIriOwnedExt for types::IriString {
    type WithoutFragmentOwned = types::AbsoluteIriString;
    type FragmentOwned = types::IriFragmentString;
}

impl CustomIriOwnedExt for types::RelativeIriString {
    type WithoutFragmentOwned = Self;
    type FragmentOwned = types::IriFragmentString;
}
