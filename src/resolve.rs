//! URI and IRI resolvers.
//!
//! # IRI resolution can fail
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
//! Thus, IRI resolution can fail for some abnormal cases.
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
//! ## Examples
//!
//! ```
//! # #[cfg(feature = "alloc")] {
//! use iri_string::task::Error as TaskError;
//! use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
//!
//! let base = IriAbsoluteStr::new("scheme:")?;
//! {
//!     let reference = IriReferenceStr::new(".///not-a-host")?;
//!     let err = reference.try_resolve_against(base)
//!         .expect_err("this resolution should fail");
//!     assert!(matches!(err, TaskError::Process(_)), "normalization error");
//!
//!     // WHATWG version.
//!     let resolved_whatwg = reference.try_resolve_whatwg_against(base)
//!         .expect("memory allocation failed");
//!     assert_eq!(*resolved_whatwg, "scheme:/.//not-a-host");
//! }
//!
//! {
//!     let reference2 = IriReferenceStr::new("/..//not-a-host")?;
//!     // Resulting string will be `scheme://not-a-host`, but `not-a-host`
//!     // should be a path segment, not a host. So, the semantically correct
//!     // target IRI cannot be represented by RFC 3986 IRI resolution.
//!     let err2 = reference2.try_resolve_against(base)
//!         .expect_err("this resolution should fail");
//!     assert!(matches!(err2, TaskError::Process(_)), "normalization error");
//!
//!     // Algorithm defined in WHATWG URL Standard addresses this case.
//!     let resolved_whatwg2 = reference2.try_resolve_whatwg_against(base)
//!         .expect("memory allocation failed");
//!     assert_eq!(*resolved_whatwg2, "scheme:/.//not-a-host");
//! }
//! # }
//! # Ok::<_, iri_string::validate::Error>(())
//! ```

#[cfg(test)]
mod tests;

#[cfg(feature = "alloc")]
use core::convert::Infallible;

use crate::components::RiReferenceComponents;
#[cfg(feature = "alloc")]
use crate::normalize::Error;
use crate::normalize::{NormalizationOp, NormalizationTask, Path, PathToNormalize};
use crate::spec::Spec;
#[cfg(feature = "alloc")]
use crate::task::{Error as TaskError, ProcessAndWrite};
#[cfg(feature = "alloc")]
use crate::types::RiString;
use crate::types::{RiAbsoluteStr, RiReferenceStr, RiStr};

/// Resolves the IRI reference.
///
/// It is recommended to use methods such as [`RiReferenceStr::try_resolve_against()`] and
/// [`RiRelativeStr::try_resolve_against()`], rather than this freestanding function.
///
/// If you are going to resolve multiple references against the common base,
/// consider using [`FixedBaseResolver`].
///
/// Enabled by `alloc` or `std` feature.
///
/// # Failures
///
/// This fails if
///
/// * memory allocation failed, or
/// * the IRI referernce is unresolvable against the base.
///
/// To see examples of unresolvable IRIs, visit the documentation
/// for [`normalize::Error`][`crate::normalize::Error`].
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] struct Error;
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
/// # impl<T> From<iri_string::task::Error<T>> for Error {
/// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
/// use iri_string::resolve::{try_resolve, FixedBaseResolver};
/// use iri_string::task::ProcessAndWrite;
/// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
///
/// let base = IriAbsoluteStr::new("http://example.com/base/")?;
/// let reference = IriReferenceStr::new("../there")?;
///
/// // Resolve `reference` against `base`.
/// let resolved = try_resolve(reference, base)?;
/// assert_eq!(resolved, "http://example.com/there");
///
/// // These two produces the same result with the same type.
/// assert_eq!(
///     FixedBaseResolver::new(base).try_resolve(reference)?,
///     "http://example.com/there"
/// );
/// assert_eq!(
///     FixedBaseResolver::new(base).create_task(reference).allocate_and_write()?,
///     "http://example.com/there"
/// );
/// # Ok::<_, Error>(())
/// ```
///
/// [`RiReferenceStr::try_resolve_against()`]: `RiReferenceStr::try_resolve_against`
/// [`RiRelativeStr::try_resolve_against()`]: `crate::types::RiRelativeStr::try_resolve_against`
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub fn try_resolve<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
) -> Result<RiString<S>, TaskError<Error>> {
    FixedBaseResolver::new(base.as_ref()).try_resolve(reference.as_ref())
}

/// Resolves the IRI reference.
///
/// It is recommended to use methods such as [`RiReferenceStr::try_resolve_against()`] and
/// [`RiRelativeStr::try_resolve_against()`], rather than this freestanding function.
///
/// If you are going to resolve multiple references against the common base,
/// consider using [`FixedBaseResolver`].
///
/// Enabled by `alloc` or `std` feature.
///
/// # Failures
///
/// This fails if
///
/// * memory allocation failed, or
/// * the IRI referernce is unresolvable against the base.
///
/// To see examples of unresolvable IRIs, visit the documentation
/// for [`normalize::Error`][`crate::normalize::Error`].
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] struct Error;
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
/// # impl<T> From<iri_string::task::Error<T>> for Error {
/// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
/// use iri_string::resolve::{try_resolve, FixedBaseResolver};
/// use iri_string::task::ProcessAndWrite;
/// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
///
/// let base = IriAbsoluteStr::new("http://example.com/base/")?;
/// let reference = IriReferenceStr::new("../there")?;
///
/// // Resolve `reference` against `base`.
/// let resolved = try_resolve(reference, base)?;
/// assert_eq!(resolved, "http://example.com/there");
///
/// // These two produces the same result with the same type.
/// assert_eq!(
///     FixedBaseResolver::new(base).try_resolve(reference)?,
///     "http://example.com/there"
/// );
/// assert_eq!(
///     FixedBaseResolver::new(base).create_task(reference).allocate_and_write()?,
///     "http://example.com/there"
/// );
/// # Ok::<_, Error>(())
/// ```
///
/// [`RiReferenceStr::try_resolve_against()`]: `RiReferenceStr::try_resolve_against`
/// [`RiRelativeStr::try_resolve_against()`]: `crate::types::RiRelativeStr::try_resolve_against`
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[deprecated(
    since = "0.5.5",
    note = "Use `try_resolve()` for non-panicking normalization"
)]
#[inline]
pub fn resolve<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
) -> Result<RiString<S>, TaskError<Error>> {
    try_resolve(reference.as_ref(), base.as_ref())
}

/// Resolves the IRI reference.
///
/// It is recommended to use methods such as [`RiReferenceStr::try_resolve_whatwg_against()`]
/// and [`RiRelativeStr::try_resolve_whatwg_against()`], rather than this freestanding function.
///
/// If you are going to resolve multiple references against the common base,
/// consider using [`FixedBaseResolver`].
///
/// Enabled by `alloc` or `std` feature.
///
/// # Failures
///
/// This fails if memory allocation failed.
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] struct Error;
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
/// # impl<T> From<iri_string::task::Error<T>> for Error {
/// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
/// use iri_string::resolve::{try_resolve_whatwg, FixedBaseResolver};
/// use iri_string::task::ProcessAndWrite;
/// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
///
/// let base = IriAbsoluteStr::new("scheme:/path")?;
/// let reference = IriReferenceStr::new("..//not-a-host")?;
///
/// // Resolve `reference` against `base`.
/// let resolved = try_resolve_whatwg(reference, base)?;
/// // Note that the result is not `scheme://not-a-host`.
/// assert_eq!(resolved, "scheme:/.//not-a-host");
/// # Ok::<_, Error>(())
/// ```
///
/// [`RiReferenceStr::try_resolve_whatwg_against()`]: `RiReferenceStr::try_resolve_whatwg_against`
/// [`RiRelativeStr::try_resolve_whatwg_against()`]:
///     `crate::types::RiRelativeStr::try_resolve_whatwg_against`
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub fn try_resolve_whatwg<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
) -> Result<RiString<S>, TaskError<Infallible>> {
    let mut task = FixedBaseResolver::new(base.as_ref()).create_task(reference.as_ref());
    task.enable_whatwg_serialization();
    task.allocate_and_write().map_err(|e| match e {
        TaskError::Buffer(e) => TaskError::Buffer(e),
        TaskError::Process(_) => unreachable!("WHATWG normaliation algorithm should not fail"),
    })
}

/// Resolves the IRI reference.
///
/// It is recommended to use methods such as [`RiReferenceStr::try_resolve_whatwg_against()`]
/// and [`RiRelativeStr::try_resolve_whatwg_against()`], rather than this freestanding function.
///
/// If you are going to resolve multiple references against the common base,
/// consider using [`FixedBaseResolver`].
///
/// Enabled by `alloc` or `std` feature.
///
/// # Failures
///
/// This fails if memory allocation failed.
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] struct Error;
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
/// # impl<T> From<iri_string::task::Error<T>> for Error {
/// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
/// use iri_string::resolve::{try_resolve_whatwg, FixedBaseResolver};
/// use iri_string::task::ProcessAndWrite;
/// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
///
/// let base = IriAbsoluteStr::new("scheme:/path")?;
/// let reference = IriReferenceStr::new("..//not-a-host")?;
///
/// // Resolve `reference` against `base`.
/// let resolved = try_resolve_whatwg(reference, base)?;
/// // Note that the result is not `scheme://not-a-host`.
/// assert_eq!(resolved, "scheme:/.//not-a-host");
/// # Ok::<_, Error>(())
/// ```
///
/// [`RiReferenceStr::try_resolve_whatwg_against()`]: `RiReferenceStr::try_resolve_whatwg_against`
/// [`RiRelativeStr::try_resolve_whatwg_against()`]:
///     `crate::types::RiRelativeStr::try_resolve_whatwg_against`
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[deprecated(
    since = "0.5.5",
    note = "Use `try_resolve_whatwg()` for non-panicking normalization"
)]
#[inline]
pub fn resolve_whatwg<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
) -> Result<RiString<S>, TaskError<Infallible>> {
    try_resolve_whatwg(reference.as_ref(), base.as_ref())
}

/// Resolves and normalizes the IRI reference.
///
/// It is recommended to use methods such as [`RiReferenceStr::try_resolve_normalize_against()`]
/// and [`RiRelativeStr::try_resolve_normalize_against()`], rather than this
/// freestanding function.
///
/// If you are going to resolve multiple references against the common base,
/// consider using [`FixedBaseResolver`].
///
/// Enabled by `alloc` or `std` feature.
///
/// # Failures
///
/// This fails if
///
/// * memory allocation failed, or
/// * the IRI referernce is unresolvable against the base.
///
/// To see examples of unresolvable IRIs, visit the
/// [module documentation][`self`].
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] struct Error;
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
/// # impl<T> From<iri_string::task::Error<T>> for Error {
/// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
/// use iri_string::resolve::{try_resolve_normalize, FixedBaseResolver};
/// use iri_string::task::ProcessAndWrite;
/// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
///
/// let base = IriAbsoluteStr::new("http://example.com/base/")?;
/// let reference = IriReferenceStr::new("../there")?;
///
/// // Resolve and normalize `reference` against `base`.
/// let resolved = try_resolve_normalize(reference, base)?;
/// assert_eq!(resolved, "http://example.com/there");
///
/// // These two produces the same result with the same type.
/// assert_eq!(
///     FixedBaseResolver::new(base).try_resolve(reference)?,
///     "http://example.com/there"
/// );
/// assert_eq!(
///     FixedBaseResolver::new(base)
///         .create_normalizing_task(reference)
///         .allocate_and_write()?,
///     "http://example.com/there"
/// );
///
/// # Ok::<_, Error>(())
/// ```
///
/// [RFC 3986 section 5.2]: https://tools.ietf.org/html/rfc3986#section-5.2
/// [`RiReferenceStr::try_resolve_normalize_against()`]: `RiReferenceStr::try_resolve_normalize_against`
/// [`RiRelativeStr::try_resolve_normalize_against()`]:
///     `crate::types::RiRelativeStr::try_resolve_normalize_against`
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub fn try_resolve_normalize<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
) -> Result<RiString<S>, TaskError<Error>> {
    FixedBaseResolver::new(base.as_ref()).try_resolve_normalize(reference.as_ref())
}

/// Resolves and normalizes the IRI reference.
///
/// It is recommended to use methods such as [`RiReferenceStr::try_resolve_normalize_against()`]
/// and [`RiRelativeStr::try_resolve_normalize_against()`], rather than this
/// freestanding function.
///
/// If you are going to resolve multiple references against the common base,
/// consider using [`FixedBaseResolver`].
///
/// Enabled by `alloc` or `std` feature.
///
/// # Failures
///
/// This fails if
///
/// * memory allocation failed, or
/// * the IRI referernce is unresolvable against the base.
///
/// To see examples of unresolvable IRIs, visit the
/// [module documentation][`self`].
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] struct Error;
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
/// # impl<T> From<iri_string::task::Error<T>> for Error {
/// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
/// use iri_string::resolve::{try_resolve_normalize, FixedBaseResolver};
/// use iri_string::task::ProcessAndWrite;
/// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
///
/// let base = IriAbsoluteStr::new("http://example.com/base/")?;
/// let reference = IriReferenceStr::new("../there")?;
///
/// // Resolve and normalize `reference` against `base`.
/// let resolved = try_resolve_normalize(reference, base)?;
/// assert_eq!(resolved, "http://example.com/there");
///
/// // These two produces the same result with the same type.
/// assert_eq!(
///     FixedBaseResolver::new(base).try_resolve(reference)?,
///     "http://example.com/there"
/// );
/// assert_eq!(
///     FixedBaseResolver::new(base)
///         .create_normalizing_task(reference)
///         .allocate_and_write()?,
///     "http://example.com/there"
/// );
///
/// # Ok::<_, Error>(())
/// ```
///
/// [RFC 3986 section 5.2]: https://tools.ietf.org/html/rfc3986#section-5.2
/// [`RiReferenceStr::try_resolve_normalize_against()`]: `RiReferenceStr::try_resolve_normalize_against`
/// [`RiRelativeStr::try_resolve_normalize_against()`]:
///     `crate::types::RiRelativeStr::try_resolve_normalize_against`
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[deprecated(
    since = "0.5.5",
    note = "Use `try_resolve_normalize()` for non-panicking normalization"
)]
#[inline]
pub fn resolve_normalize<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
) -> Result<RiString<S>, TaskError<Error>> {
    try_resolve_normalize(reference.as_ref(), base.as_ref())
}

/// Resolves and normalizes the IRI reference.
///
/// It is recommended to use methods such as
/// [`RiReferenceStr::try_resolve_normalize_whatwg_against()`] and
/// [`RiRelativeStr::try_resolve_normalize_whatwg_against()`], rather than this
/// freestanding function.
///
/// If you are going to resolve multiple references against the common base,
/// consider using [`FixedBaseResolver`].
///
/// Enabled by `alloc` or `std` feature.
///
/// # Failures
///
/// This fails if memory allocation failed.
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] struct Error;
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
/// # impl<T> From<iri_string::task::Error<T>> for Error {
/// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
/// use iri_string::resolve::{try_resolve_normalize_whatwg, FixedBaseResolver};
/// use iri_string::task::ProcessAndWrite;
/// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
///
/// let base = IriAbsoluteStr::new("scheme:/path")?;
/// let reference = IriReferenceStr::new("..//not-a-host")?;
///
/// // Resolve and normalize `reference` against `base`.
/// let resolved = try_resolve_normalize_whatwg(reference, base)?;
/// assert_eq!(resolved, "scheme:/.//not-a-host");
/// # Ok::<_, Error>(())
/// ```
///
/// [RFC 3986 section 5.2]: https://tools.ietf.org/html/rfc3986#section-5.2
/// [`RiReferenceStr::try_resolve_normalize_whatwg_against()`]:
///     `RiReferenceStr::try_resolve_normalize_whatwg_against`
/// [`RiRelativeStr::try_resolve_normalize_whatwg_against()`]:
///     `crate::types::RiRelativeStr::try_resolve_normalize_whatwg_against`
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub fn try_resolve_normalize_whatwg<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
) -> Result<RiString<S>, TaskError<Infallible>> {
    let mut task =
        FixedBaseResolver::new(base.as_ref()).create_normalizing_task(reference.as_ref());
    task.enable_whatwg_serialization();
    task.allocate_and_write().map_err(|e| match e {
        TaskError::Buffer(e) => TaskError::Buffer(e),
        TaskError::Process(_) => unreachable!("WHATWG normaliation algorithm should not fail"),
    })
}

/// Resolves and normalizes the IRI reference.
///
/// It is recommended to use methods such as
/// [`RiReferenceStr::try_resolve_normalize_whatwg_against()`] and
/// [`RiRelativeStr::try_resolve_normalize_whatwg_against()`], rather than this
/// freestanding function.
///
/// If you are going to resolve multiple references against the common base,
/// consider using [`FixedBaseResolver`].
///
/// Enabled by `alloc` or `std` feature.
///
/// # Failures
///
/// This fails if memory allocation failed.
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] struct Error;
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
/// # impl<T> From<iri_string::task::Error<T>> for Error {
/// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
/// use iri_string::resolve::{try_resolve_normalize_whatwg, FixedBaseResolver};
/// use iri_string::task::ProcessAndWrite;
/// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
///
/// let base = IriAbsoluteStr::new("scheme:/path")?;
/// let reference = IriReferenceStr::new("..//not-a-host")?;
///
/// // Resolve and normalize `reference` against `base`.
/// let resolved = try_resolve_normalize_whatwg(reference, base)?;
/// assert_eq!(resolved, "scheme:/.//not-a-host");
/// # Ok::<_, Error>(())
/// ```
///
/// [RFC 3986 section 5.2]: https://tools.ietf.org/html/rfc3986#section-5.2
/// [`RiReferenceStr::try_resolve_normalize_whatwg_against()`]:
///     `RiReferenceStr::try_resolve_normalize_whatwg_against`
/// [`RiRelativeStr::try_resolve_normalize_whatwg_against()`]:
///     `crate::types::RiRelativeStr::try_resolve_normalize_whatwg_against`
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[deprecated(
    since = "0.5.5",
    note = "Use `try_resolve_normalize_whatwg()` for non-panicking normalization"
)]
#[inline]
pub fn resolve_normalize_whatwg<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
) -> Result<RiString<S>, TaskError<Infallible>> {
    try_resolve_normalize_whatwg(reference.as_ref(), base.as_ref())
}

/// A resolver against the fixed base.
///
/// If you want more control over how to resolve the buffer, create
/// [`NormalizationTask`] by [`create_task`] or [`create_normalizing_task`] method.
///
/// [`create_normalizing_task`]: `Self::create_normalizing_task`
/// [`create_task`]: `Self::create_task`
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
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `FixedBaseResolver::try_resolve()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriAbsoluteStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let resolved = resolver.try_resolve(reference)?;
    ///
    /// assert_eq!(resolved, "http://example.com/there");
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
    /// Enabled by `alloc` or `std` feature.
    ///
    /// The task returned by this method does **not** normalize the resolution
    /// result. However, `..` and `.` are recognized even when they are
    /// percent-encoded.
    ///
    /// # Failures
    ///
    /// This fails if
    ///
    /// * memory allocation failed, or
    /// * the IRI referernce is unresolvable against the base.
    ///
    /// To see examples of unresolvable IRIs, visit the
    /// [module documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// let base = IriAbsoluteStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let resolved = resolver.try_resolve(reference)?;
    ///
    /// assert_eq!(resolved, "http://example.com/there");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// Note that `..` and `.` path segments are recognized even when they are
    /// percent-encoded.
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `ResolutionTask::allocate_and_write()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriAbsoluteStr::new("HTTP://example.COM/base/base2/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// // `%2e%2e` is recognized as `..`.
    /// // However, `dot%2edot` is NOT normalized into `dot.dot`.
    /// let reference = IriReferenceStr::new("%2e%2e/../dot%2edot")?;
    /// let task = resolver.create_task(reference);
    ///
    /// let resolved = task.allocate_and_write()?;
    /// // Resolved but not normalized.
    /// assert_eq!(resolved, "HTTP://example.COM/dot%2edot");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`create_normalizing_task`]: `Self::create_normalizing_task`
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn try_resolve(
        &self,
        reference: &RiReferenceStr<S>,
    ) -> Result<RiString<S>, TaskError<Error>> {
        self.create_task(reference).allocate_and_write()
    }
    /// Resolves the given reference against the fixed base.
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// The task returned by this method does **not** normalize the resolution
    /// result. However, `..` and `.` are recognized even when they are
    /// percent-encoded.
    ///
    /// # Failures
    ///
    /// This fails if
    ///
    /// * memory allocation failed, or
    /// * the IRI referernce is unresolvable against the base.
    ///
    /// To see examples of unresolvable IRIs, visit the
    /// [module documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// let base = IriAbsoluteStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let resolved = resolver.try_resolve(reference)?;
    ///
    /// assert_eq!(resolved, "http://example.com/there");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// Note that `..` and `.` path segments are recognized even when they are
    /// percent-encoded.
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `ResolutionTask::allocate_and_write()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriAbsoluteStr::new("HTTP://example.COM/base/base2/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// // `%2e%2e` is recognized as `..`.
    /// // However, `dot%2edot` is NOT normalized into `dot.dot`.
    /// let reference = IriReferenceStr::new("%2e%2e/../dot%2edot")?;
    /// let task = resolver.create_task(reference);
    ///
    /// let resolved = task.allocate_and_write()?;
    /// // Resolved but not normalized.
    /// assert_eq!(resolved, "HTTP://example.COM/dot%2edot");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`create_normalizing_task`]: `Self::create_normalizing_task`
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[deprecated(
        since = "0.5.5",
        note = "Use `try_resolve()` for non-panicking normalization"
    )]
    pub fn resolve(&self, reference: &RiReferenceStr<S>) -> Result<RiString<S>, TaskError<Error>> {
        self.try_resolve(reference)
    }

    /// Resolves the given reference against the fixed base, and normalizes the result.
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// The task returned by this method is normalized.
    ///
    /// If you don't want the result to be normalized, use [`create_task`] method.
    ///
    /// # Failures
    ///
    /// This fails if
    ///
    /// * memory allocation failed, or
    /// * the IRI referernce is unresolvable against the base.
    ///
    /// To see examples of unresolvable IRIs, visit the
    /// [module documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `ResolutionTask::allocate_and_write()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriAbsoluteStr::new("HTTP://example.COM/base/base2/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// // `%2e%2e` is recognized as `..`.
    /// let reference = IriReferenceStr::new("%2e%2e/../dot%2edot")?;
    /// let task = resolver.create_normalizing_task(reference);
    ///
    /// let resolved = task.allocate_and_write()?;
    /// // Not only resolved, but also normalized.
    /// assert_eq!(resolved, "http://example.com/dot.dot");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`create_task`]: `Self::create_task`
    /// [`unreserved` characters]: https://datatracker.ietf.org/doc/html/rfc3986#section-2.3
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn try_resolve_normalize(
        &self,
        reference: &RiReferenceStr<S>,
    ) -> Result<RiString<S>, TaskError<Error>> {
        self.create_normalizing_task(reference).allocate_and_write()
    }

    /// Resolves the given reference against the fixed base, and normalizes the result.
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// The task returned by this method is normalized.
    ///
    /// If you don't want the result to be normalized, use [`create_task`] method.
    ///
    /// # Failures
    ///
    /// This fails if
    ///
    /// * memory allocation failed, or
    /// * the IRI referernce is unresolvable against the base.
    ///
    /// To see examples of unresolvable IRIs, visit the
    /// [module documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `ResolutionTask::allocate_and_write()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriAbsoluteStr::new("HTTP://example.COM/base/base2/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// // `%2e%2e` is recognized as `..`.
    /// let reference = IriReferenceStr::new("%2e%2e/../dot%2edot")?;
    /// let task = resolver.create_normalizing_task(reference);
    ///
    /// let resolved = task.allocate_and_write()?;
    /// // Not only resolved, but also normalized.
    /// assert_eq!(resolved, "http://example.com/dot.dot");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`create_task`]: `Self::create_task`
    /// [`unreserved` characters]: https://datatracker.ietf.org/doc/html/rfc3986#section-2.3
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn resolve_normalize(
        &self,
        reference: &RiReferenceStr<S>,
    ) -> Result<RiString<S>, TaskError<Error>> {
        self.try_resolve_normalize(reference)
    }

    /// Creates a resolution task.
    ///
    /// The returned [`NormalizationTask`] allows you to resolve the IRI without
    /// memory allocation, resolve to existing buffers, estimate required
    /// memory size, etc. If you need more control than
    /// [`resolve`][`Self::resolve`] method, use this.
    ///
    /// The task returned by this method does not normalize the resolution
    /// result. However, note that `..` and `.` is recognized even when they
    /// are percent-encoded.
    ///
    /// If you want to normalize the result, use
    /// [`create_normalizing_task`][`Self::create_normalizing_task`]
    /// method instead, or call [`NormalizationTask::enable_normalization`] for
    /// the returned task.
    ///
    /// If you want to avoid resolution failure by using resolution described in
    /// WHATWG URL Standard, call
    /// [`NormalizationTask::enable_whatwg_serialization`] for the returned task.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `ResolutionTask::allocate_and_write()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriAbsoluteStr::new("HTTP://example.COM/base/base2/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// // `%2e%2e` is recognized as `..`.
    /// // However, `dot%2edot` is NOT normalized into `dot.dot`.
    /// let reference = IriReferenceStr::new("%2e%2e/../dot%2edot")?;
    /// let task = resolver.create_task(reference);
    ///
    /// let resolved = task.allocate_and_write()?;
    /// // Resolved but not normalized.
    /// assert_eq!(resolved, "HTTP://example.COM/dot%2edot");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`create_task`]: `Self::create_task`
    #[must_use]
    pub fn create_task(&self, reference: &'a RiReferenceStr<S>) -> NormalizationTask<'a, RiStr<S>> {
        let b = self.base_components;
        let r = RiReferenceComponents::from(reference);

        let (r_scheme, r_authority, r_path, r_query, r_fragment) = r.to_major();
        let (b_scheme, b_authority, b_path, b_query, _) = b.to_major();
        let b_scheme = b_scheme.expect("[validity] non-relative IRI must have a scheme");

        /// The toplevel component the reference has.
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        enum RefToplevel {
            /// Scheme.
            Scheme,
            /// Authority.
            Authority,
            /// Path.
            Path,
            /// Query.
            Query,
            /// Reference is empty or has only fragment.
            None,
        }

        impl RefToplevel {
            /// Choose a component from either of the reference or the base,
            /// based on the toplevel component of the reference.
            fn choose<T>(self, component: RefToplevel, reference: T, base: T) -> T {
                if self <= component {
                    reference
                } else {
                    base
                }
            }
        }

        let ref_toplevel = if r_scheme.is_some() {
            RefToplevel::Scheme
        } else if r_authority.is_some() {
            RefToplevel::Authority
        } else if !r_path.is_empty() {
            RefToplevel::Path
        } else if r_query.is_some() {
            RefToplevel::Query
        } else {
            RefToplevel::None
        };

        let path = match ref_toplevel {
            RefToplevel::Scheme | RefToplevel::Authority => {
                Path::NeedsProcessing(PathToNormalize::from_single_path(r_path))
            }
            RefToplevel::Path => {
                if r_path.starts_with('/') {
                    Path::NeedsProcessing(PathToNormalize::from_single_path(r_path))
                } else {
                    // About this branch, see
                    // <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.3>.
                    //
                    // > o  If the base URI has a defined authority component and an empty
                    // >    path, then return a string consisting of "/" concatenated with the
                    // >    reference's path; otherwise,
                    let b_path = if b_authority.is_some() && b_path.is_empty() {
                        "/"
                    } else {
                        b_path
                    };
                    Path::NeedsProcessing(PathToNormalize::from_paths_to_be_resolved(
                        b_path, r_path,
                    ))
                }
            }
            RefToplevel::Query | RefToplevel::None => Path::Done(b_path),
        };

        NormalizationTask::new(
            r_scheme.unwrap_or(b_scheme),
            ref_toplevel.choose(RefToplevel::Authority, r_authority, b_authority),
            path,
            ref_toplevel.choose(RefToplevel::Query, r_query, b_query),
            r_fragment,
            NormalizationOp {
                case_pct_normalization: false,
            },
            false,
        )
    }

    /// Creates a resolution task.
    ///
    /// The returned [`NormalizationTask`] allows you to resolve the IRI without
    /// memory allocation, resolve to existing buffers, estimate required
    /// memory size, etc. If you need more control than
    /// [`try_resolve_normalize`][`Self::try_resolve_normalize`] method, use this.
    ///
    /// The task returned by this method normalizes the resolution result.
    /// If you don't want to normalize the result, use
    /// [`create_task`][`Self::create_task`] instead.
    ///
    /// If you want to avoid resolution and normalization failure by using
    /// resolution described in WHATWG URL Standard, call
    /// [`NormalizationTask::enable_whatwg_serialization`] for the returned task.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `ResolutionTask::allocate_and_write()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriAbsoluteStr::new("HTTP://example.COM/base/base2/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("%2e%2e/../dot%2edot")?;
    /// let task = resolver.create_normalizing_task(reference);
    ///
    /// let resolved = task.allocate_and_write()?;
    /// // Not only resolved, but also normalized.
    /// assert_eq!(resolved, "http://example.com/dot.dot");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[must_use]
    pub fn create_normalizing_task(
        &self,
        reference: &'a RiReferenceStr<S>,
    ) -> NormalizationTask<'a, RiStr<S>> {
        let mut task = self.create_task(reference);
        task.enable_normalization();
        task
    }
}
