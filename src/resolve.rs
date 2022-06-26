//! URI and IRI resolvers.
//!
//! # IRI resolution can fail without WHATWG URL Standard serialization
//!
//! ## Pure RFC 3986 algorithm
//!
//! Though this is not explicitly stated in RFC 3986, IRI resolution can fail.
//! Below are examples:
//!
//! * base=`scheme:`, ref=`.///bar`.
//!     + Resulting IRI should have scheme `scheme` and path `//bar`, but does not have authority.
//! * base=`scheme:foo`, ref=`.///bar`.
//!     + Resulting IRI should have scheme `scheme` and path `//bar`, but does not have authority.
//! * base=`scheme:`, ref=`/..//baz`.
//!     + Resulting IRI should have scheme `scheme` and path `//bar`, but does not have authority.
//! * base=`scheme:foo/bar`, ref=`..//baz`.
//!     + Resulting IRI should have scheme `scheme` and path `//bar`, but does not have authority.
//!
//! IRI without authority (note that this is different from "with empty authority")
//! cannot have a path starting with `//`, since it is ambiguous and can be
//! interpreted as an IRI with authority. For the above examples, `scheme://bar`
//! is not valid output, as `bar` in `scheme://bar` will be interpreted as an
//! authority, not a path.
//!
//! Thus, IRI resolution by pure RFC 3986 algorithm can fail for some abnormal
//! cases.
//!
//! Note that this kind of failure can happen only when the base IRI has no
//! authority and empty path. This would be rare in the wild, since many people
//! would use an IRI with authority part, such as `http://`.
//!
//! If you are handling `scheme://`-style URIs and IRIs, don't worry about the
//! failure. Currently no cases are known to fail when at least one of the base
//! IRI or the relative IRI contains authorities.
//!
//! If you want this kind of abnormal IRI resolution to succeed and to be
//! idempotent, use WHATWG variation of resolution and normalization.
//!
//! ## WHATWG serialization
//!
//! To handle IRI resolution failure, WHATWG URL Standard defines serialization
//! algorithm for this kind of result, and it makes IRI resolution (and even
//! normalization) infallible and idempotent.
//!
//! IRI resolution and normalization provided by this crate automatically
//! applies this special rule if necessary, so they are infallible. If you want
//! to detect resolution/normalization failure, use
//! [`Normalized::ensure_rfc3986_normalizable`] method.
//!
//! ## Examples
//!
//! ```
//! # #[cfg(feature = "alloc")] {
//! use iri_string::format::ToDedicatedString;
//! use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
//!
//! let base = IriAbsoluteStr::new("scheme:")?;
//! {
//!     let reference = IriReferenceStr::new(".///not-a-host")?;
//!     let result = reference.resolve_against(base);
//!     assert!(result.ensure_rfc3986_normalizable().is_err());
//!     assert_eq!(result.to_dedicated_string(), "scheme:/.//not-a-host");
//! }
//!
//! {
//!     let reference2 = IriReferenceStr::new("/..//not-a-host")?;
//!     // Resulting string will be `scheme://not-a-host`, but `not-a-host`
//!     // should be a path segment, not a host. So, the semantically correct
//!     // target IRI cannot be represented by RFC 3986 IRI resolution.
//!     let result2 = reference2.resolve_against(base);
//!     assert!(result2.ensure_rfc3986_normalizable().is_err());
//!
//!     // Algorithm defined in WHATWG URL Standard addresses this case.
//!     assert_eq!(result2.to_dedicated_string(), "scheme:/.//not-a-host");
//! }
//! # }
//! # Ok::<_, iri_string::validate::Error>(())
//! ```

#[cfg(test)]
mod tests;

use crate::components::RiReferenceComponents;
use crate::normalize::{NormalizationInput, Normalized};
use crate::spec::Spec;
use crate::types::{RiAbsoluteStr, RiReferenceStr, RiStr};

/// A resolver against the fixed base.
#[derive(Debug, Clone, Copy)]
pub struct FixedBaseResolver<'a, S: Spec> {
    /// Components of the base IRI.
    base_components: RiReferenceComponents<'a, S>,
}

impl<'a, S: Spec> FixedBaseResolver<'a, S> {
    /// Creates a new resolver with the given base.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// # // `ToDedicatedString` is available only when
    /// # // `alloc` feature is enabled.
    /// #[cfg(feature = "alloc")] {
    /// use iri_string::format::ToDedicatedString;
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// let base = IriAbsoluteStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let resolved = resolver.resolve(reference);
    ///
    /// assert_eq!(resolved.to_dedicated_string(), "http://example.com/there");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[must_use]
    pub fn new(base: &'a RiAbsoluteStr<S>) -> Self {
        Self {
            base_components: RiReferenceComponents::from(base.as_ref()),
        }
    }

    /// Returns the base.
    ///
    /// # Examples
    ///
    /// ```
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// let base = IriAbsoluteStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// assert_eq!(resolver.base(), base);
    /// # Ok::<_, iri_string::validate::Error>(())
    /// ```
    #[must_use]
    pub fn base(&self) -> &'a RiAbsoluteStr<S> {
        unsafe {
            // SAFETY: `base_components` can only be created from `&RiAbsoluteStr<S>`.
            RiAbsoluteStr::new_maybe_unchecked(self.base_components.iri().as_str())
        }
    }
}

impl<'a, S: Spec> FixedBaseResolver<'a, S> {
    /// Resolves the given reference against the fixed base.
    ///
    /// The task returned by this method does **not** normalize the resolution
    /// result. However, `..` and `.` are recognized even when they are
    /// percent-encoded.
    ///
    /// # Failures
    ///
    /// This function itself does not fail, but resolution algorithm defined by
    /// RFC 3986 can fail. In that case, serialization algorithm defined by
    /// WHATWG URL Standard would be automatically applied.
    ///
    /// See the documentation of [`Normalized`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// # // `ToDedicatedString` is available only when
    /// # // `alloc` feature is enabled.
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::format::ToDedicatedString;
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// let base = IriAbsoluteStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let resolved = resolver.resolve(reference);
    ///
    /// assert_eq!(resolved.to_dedicated_string(), "http://example.com/there");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// Note that `..` and `.` path segments are recognized even when they are
    /// percent-encoded.
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// # // `ToDedicatedString` is available only when
    /// # // `alloc` feature is enabled.
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::format::ToDedicatedString;
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// let base = IriAbsoluteStr::new("HTTP://example.COM/base/base2/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// // `%2e%2e` is recognized as `..`.
    /// // However, `dot%2edot` is NOT normalized into `dot.dot`.
    /// let reference = IriReferenceStr::new("%2e%2e/../dot%2edot")?;
    /// let resolved = resolver.resolve(reference);
    ///
    /// // Resolved but not normalized.
    /// assert_eq!(resolved.to_dedicated_string(), "HTTP://example.COM/dot%2edot");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn resolve(&self, reference: &'a RiReferenceStr<S>) -> Normalized<'a, RiStr<S>> {
        let input = NormalizationInput::with_resolution_params(&self.base_components, reference);
        Normalized::from_input(input)
    }
}
