//! Normalization.
//!
//! # IRI normalization (and resolution) can fail
//!
//! Though this is not explicitly stated in RFC 3986, IRI normalization can fail.
//! For example, `foo:.///bar`, `foo:./..//bar`, and `foo:/..//bar` are all
//! normalized to `foo://bar` as a string. However, IRI without authority (note
//! that this is different from "with empty authority") cannot have a path
//! starting with `//`, since it is ambiguous and can be interpreted as an IRI
//! with authority. So, `foo://bar` is decomposed as scheme `foo`, authority
//! `bar`, and empty path. The expected result is the combination of scheme
//! `foo`, no authority, and path `//bar` (though this is not possible to
//! serialize), so the algorithm fails as it cannot return the intended result.
//!
//! IRI resolution can also fail since it (conditionally) invokes normalization
//! during the resolution process. For example, resolving a reference `.///bar`
//! or `/..//bar` against the base `foo:` fail.
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
//! ## Examples
//!
//! ### Normalization failure
//!
//! ```
//! # #[cfg(feature = "alloc")] {
//! use iri_string::normalize::Error;
//! use iri_string::task::Error as TaskError;
//! use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
//!
//! let base = IriAbsoluteStr::new("foo:.///bar")?;
//! assert!(base.normalize().is_err(), "this normalization should fail");
//! # }
//! # Ok::<_, iri_string::validate::Error>(())
//! ```
//!
//! ### Resolution failure
//!
//! ```
//! # #[cfg(feature = "alloc")] {
//! use iri_string::task::Error as TaskError;
//! use iri_string::types::{IriAbsoluteStr, IriReferenceStr};
//!
//! let base = IriAbsoluteStr::new("scheme:")?;
//! {
//!     let reference = IriReferenceStr::new(".///bar")?;
//!     let err = reference.resolve_against(base)
//!         .expect_err("this resolution should fail");
//!     assert!(matches!(err, TaskError::Process(_)));
//! }
//!
//! {
//!     let reference2 = IriReferenceStr::new("/..//bar")?;
//!     // Resulting string will be `scheme://bar`, but `bar` should be a path
//!     // segment, not a host. So, the semantically correct target IRI cannot
//!     // be represented.
//!     let err2 = reference2.resolve_against(base)
//!         .expect_err("this resolution should fail");
//!     assert!(matches!(err2, TaskError::Process(_)));
//! }
//! # }
//! # Ok::<_, iri_string::validate::Error>(())
//! ```

mod error;
mod path;
mod percent_encoding;

use core::cmp::Ordering;
use core::marker::PhantomData;

#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::buffer::{Buffer, ByteSliceBuf};
use crate::components::RiReferenceComponents;
use crate::parser::str::rfind_split_hole;
use crate::spec::Spec;
use crate::task::{Error as TaskError, ProcessAndWrite};
use crate::types::{RiAbsoluteStr, RiStr};
#[cfg(feature = "alloc")]
use crate::types::{RiAbsoluteString, RiString};

pub use self::error::Error;
pub(crate) use self::path::{Path, PathToNormalize};

/// Normalization type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NormalizationType {
    /// Full generic syntax-based normalization.
    Full,
    /// Only `remove_dot_segments` algorithm.
    RemoveDotSegments,
}

/// IRI normalization/resolution task.
///
/// Most of the main functionalities are provided from [`ProcessAndWrite`] trait,
/// so you may need to write `use iri_string::task::ProcessAndWrite` where you
/// use this task type.
#[derive(Debug, Clone, Copy)]
pub struct NormalizationTask<'a, T: ?Sized> {
    /// Common data.
    common: NormalizationTaskCommon<'a>,
    /// Spec.
    _spec: PhantomData<fn() -> T>,
}

impl<'a, S: Spec> From<&'a RiStr<S>> for NormalizationTask<'a, RiStr<S>> {
    fn from(iri: &'a RiStr<S>) -> Self {
        let components = RiReferenceComponents::<S>::from(iri.as_ref());
        let (scheme, authority, path, query, fragment) = components.to_major();
        let scheme = scheme.expect("[validity] `absolute IRI must have `scheme`");
        let path = Path::NeedsProcessing(PathToNormalize::from_single_path(path));

        let common = NormalizationTaskCommon {
            scheme,
            authority,
            path,
            query,
            fragment,
            op: NormalizationType::Full,
        };
        common.into()
    }
}

#[cfg(feature = "alloc")]
impl<'a, S: Spec> From<&'a RiString<S>> for NormalizationTask<'a, RiStr<S>> {
    #[inline]
    fn from(iri: &'a RiString<S>) -> Self {
        NormalizationTask::from(iri.as_slice())
    }
}

impl<'a, S: Spec> From<&'a RiAbsoluteStr<S>> for NormalizationTask<'a, RiAbsoluteStr<S>> {
    fn from(iri: &'a RiAbsoluteStr<S>) -> Self {
        let components = RiReferenceComponents::<S>::from(iri.as_ref());
        let (scheme, authority, path, query, fragment) = components.to_major();
        let scheme = scheme.expect("[validity] `absolute IRI must have `scheme`");
        let path = Path::NeedsProcessing(PathToNormalize::from_single_path(path));

        let common = NormalizationTaskCommon {
            scheme,
            authority,
            path,
            query,
            fragment,
            op: NormalizationType::Full,
        };
        common.into()
    }
}

#[cfg(feature = "alloc")]
impl<'a, S: Spec> From<&'a RiAbsoluteString<S>> for NormalizationTask<'a, RiAbsoluteStr<S>> {
    #[inline]
    fn from(iri: &'a RiAbsoluteString<S>) -> Self {
        NormalizationTask::from(iri.as_slice())
    }
}

impl<'a, T: ?Sized + AsRef<str>> NormalizationTask<'a, T> {
    /// Enables normalization for the task.
    pub(crate) fn enable_normalization(&mut self) {
        debug_assert!(
            matches!(
                self.common.op,
                NormalizationType::Full | NormalizationType::RemoveDotSegments
            ),
            "No cases should be overlooked"
        );
        self.common.op = NormalizationType::Full;
    }

    /// Resolves the IRI, and writes it to the buffer.
    fn write_to_buf<'b, B: Buffer<'b>, S: Spec>(&self, buf: B) -> Result<&'b [u8], TaskError<Error>>
    where
        TaskError<Error>: From<B::ExtendError>,
    {
        self.common.write_to_buf::<B, S>(buf).map_err(Into::into)
    }

    /// Returns the estimated maximum size required for IRI normalization/resolution.
    ///
    /// With a buffer of the returned size, IRI normalization/resolution would
    /// succeed without OOM error. The operation may succeed with smaller
    /// buffer than this function estimates, but it is not guaranteed.
    ///
    /// Note that this is `O(N)` operation (where N is input length).
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1%ff")?;
    /// let task = NormalizationTask::from(iri);
    ///
    /// let max_size = task.estimate_max_buf_size_for_resolution();
    /// let mut buf = vec![0_u8; max_size];
    /// let resolved = task.write_to_byte_slice(&mut buf[..])?;
    ///
    /// assert_eq!(resolved, "http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF");
    /// # Ok::<_, Error>(())
    /// ```
    #[must_use]
    pub fn estimate_max_buf_size_for_resolution(&self) -> usize {
        let known_exact = self.common.scheme.len()
            + self.common.authority.map_or(0, |s| s.len() + 2)
            + self.common.query.map_or(0, |s| s.len() + 1)
            + self.common.fragment.map_or(0, |s| s.len() + 1);
        let path_max = self.common.path.estimate_max_buf_size_for_resolution();

        known_exact + path_max
    }
}

impl<'a, T: ?Sized> From<NormalizationTaskCommon<'a>> for NormalizationTask<'a, T> {
    #[inline]
    fn from(common: NormalizationTaskCommon<'a>) -> Self {
        Self {
            common,
            _spec: PhantomData,
        }
    }
}

impl<S: Spec> ProcessAndWrite for &NormalizationTask<'_, RiStr<S>> {
    type OutputBorrowed = RiStr<S>;
    #[cfg(feature = "alloc")]
    type OutputOwned = RiString<S>;
    type ProcessError = Error;

    /// Processes the data, and writes it to the newly allocated buffer.
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * failed to allocate memory, or
    /// * failed to process data.
    ///
    /// To see examples of unresolvable IRIs, visit the [module
    /// documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1%ff")?;
    /// let task = NormalizationTask::from(iri);
    ///
    /// assert_eq!(
    ///     task.allocate_and_write()?,
    ///     "http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF"
    /// );
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    fn allocate_and_write(self) -> Result<Self::OutputOwned, TaskError<Self::ProcessError>> {
        let mut s = String::new();
        self.write_to_buf::<_, S>(&mut s)?;
        Ok(RiString::try_from(s).expect("[consistency] the resolved IRI must be valid"))
    }

    /// Processes the data, and writes it to the given byte slice.
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * buffer is not large enough, or
    /// * failed to process data.
    ///
    /// To see examples of unresolvable IRIs, visit the [module
    /// documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1%ff")?;
    /// let task = NormalizationTask::from(iri);
    ///
    /// // Long enough!
    /// let mut buf = [0_u8; 128];
    /// let normalized = task.write_to_byte_slice(&mut buf[..])?;
    ///
    /// assert_eq!(normalized, "http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// This returns error when the buffer is not long enough for processing.
    ///
    /// Note that it would be still not enough even if the buffer is long enough
    /// to store the result. During processing, the resolver might use more
    /// memory than the result. You can get maximum required buffer size by
    /// [`estimate_max_buf_size_for_resolution`] method.
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl From<iri_string::normalize::Error> for Error {
    /// #     fn from(e: iri_string::normalize::Error) -> Self { Self } }
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::{Error as TaskError, ProcessAndWrite};
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("http://example.com/a/b/c/d/e/../../../../../f")?;
    /// const EXPECTED: &str = "http://example.com/f";
    /// let task = NormalizationTask::from(iri);
    ///
    /// // Buffer is too short for processing, even though it is long enough
    /// // to store the result.
    /// let mut buf = [0_u8; EXPECTED.len()];
    /// let resolved = task.write_to_byte_slice(&mut buf[..]);
    /// assert!(
    ///     matches!(resolved, Err(TaskError::Buffer(_))),
    ///     "failed due to not enough buffer size"
    /// );
    /// // You can retry writing if you have larger buffer,
    /// // since `task` was not consumed.
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`estimate_max_buf_size_for_resolution`]: `NormalizationTask::estimate_max_buf_size_for_resolution`
    fn write_to_byte_slice(
        self,
        buf: &mut [u8],
    ) -> Result<&Self::OutputBorrowed, TaskError<Self::ProcessError>> {
        let buf = ByteSliceBuf::new(buf);
        let s = self.write_to_buf::<_, S>(buf)?;
        // Convert the type.
        // This should never fail (unless the crate has bugs), but do the
        // validation here for extra safety.
        let s = <&RiStr<S>>::try_from(s).expect("[consistency] the resolved IRI must be valid");
        Ok(s)
    }

    /// Processes the data, and appends it to the buffer inside the provided [`String`].
    ///
    /// # Failures
    ///
    /// This fails if failed to process data.
    ///
    /// # Panics
    ///
    /// This panics if failed to allocate memory.
    /// To avoid panic on allocation failure, use [`try_append_to_std_string`].
    ///
    /// [`try_append_to_std_string`]: `ProcessAndWrite::try_append_to_std_string`
    #[cfg(feature = "alloc")]
    fn append_to_std_string(
        self,
        buf: &mut String,
    ) -> Result<&Self::OutputBorrowed, Self::ProcessError> {
        match self.try_append_to_std_string(buf) {
            Ok(v) => Ok(v),
            Err(TaskError::Buffer(e)) => panic!("buffer error: {}", e),
            Err(TaskError::Process(e)) => Err(e),
        }
    }

    /// Processes the data, and appends it to the buffer inside the provided [`String`].
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * failed to allocate memory, or
    /// * failed to process data.
    ///
    /// To see examples of unresolvable IRIs, visit the [module
    /// documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1%ff")?;
    /// let task = NormalizationTask::from(iri);
    ///
    /// let mut buf = String::from("Result: ");
    ///
    /// let result: Result<&IriStr, _> = task.try_append_to_std_string(&mut buf);
    /// if let Ok(s) = result {
    ///     assert_eq!(s, "http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF");
    ///     assert_eq!(buf, "Result: http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF");
    /// }
    /// # }
    /// # Ok::<_, iri_string::validate::Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    fn try_append_to_std_string(
        self,
        buf: &mut String,
    ) -> Result<&Self::OutputBorrowed, TaskError<Self::ProcessError>> {
        let s = self.write_to_buf::<_, S>(buf)?;
        // Convert the type.
        // This should never fail (unless the crate has bugs), but do the
        // validation here for extra safety.
        let s = <&RiStr<S>>::try_from(s).expect("[consistency] the resolved IRI must be valid");
        Ok(s)
    }
}

impl<S: Spec> ProcessAndWrite for &NormalizationTask<'_, RiAbsoluteStr<S>> {
    type OutputBorrowed = RiAbsoluteStr<S>;
    #[cfg(feature = "alloc")]
    type OutputOwned = RiAbsoluteString<S>;
    type ProcessError = Error;

    /// Processes the data, and writes it to the newly allocated buffer.
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * failed to allocate memory, or
    /// * failed to process data.
    ///
    /// To see examples of unresolvable IRIs, visit the [module
    /// documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1%ff")?;
    /// let task = NormalizationTask::from(iri);
    ///
    /// assert_eq!(
    ///     task.allocate_and_write()?,
    ///     "http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF"
    /// );
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    fn allocate_and_write(self) -> Result<Self::OutputOwned, TaskError<Self::ProcessError>> {
        let mut s = String::new();
        self.write_to_buf::<_, S>(&mut s)?;
        Ok(RiAbsoluteString::try_from(s).expect("[consistency] the resolved IRI must be valid"))
    }

    /// Processes the data, and writes it to the given byte slice.
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * buffer is not large enough, or
    /// * failed to process data.
    ///
    /// To see examples of unresolvable IRIs, visit the [module
    /// documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl<T> From<iri_string::task::Error<T>> for Error {
    /// #     fn from(e: iri_string::task::Error<T>) -> Self { Self } }
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1%ff")?;
    /// let task = NormalizationTask::from(iri);
    ///
    /// // Long enough!
    /// let mut buf = [0_u8; 128];
    /// let normalized = task.write_to_byte_slice(&mut buf[..])?;
    ///
    /// assert_eq!(normalized, "http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// This returns error when the buffer is not long enough for processing.
    ///
    /// Note that it would be still not enough even if the buffer is long enough
    /// to store the result. During processing, the resolver might use more
    /// memory than the result. You can get maximum required buffer size by
    /// [`estimate_max_buf_size_for_resolution`] method.
    ///
    /// ```
    /// # #[derive(Debug)] struct Error;
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self } }
    /// # impl From<iri_string::normalize::Error> for Error {
    /// #     fn from(e: iri_string::normalize::Error) -> Self { Self } }
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::{Error as TaskError, ProcessAndWrite};
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("http://example.com/a/b/c/d/e/../../../../../f")?;
    /// const EXPECTED: &str = "http://example.com/f";
    /// let task = NormalizationTask::from(iri);
    ///
    /// // Buffer is too short for processing, even though it is long enough
    /// // to store the result.
    /// let mut buf = [0_u8; EXPECTED.len()];
    /// let resolved = task.write_to_byte_slice(&mut buf[..]);
    /// assert!(
    ///     matches!(resolved, Err(TaskError::Buffer(_))),
    ///     "failed due to not enough buffer size"
    /// );
    /// // You can retry writing if you have larger buffer,
    /// // since `task` was not consumed.
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`estimate_max_buf_size_for_resolution`]: `NormalizationTask::estimate_max_buf_size_for_resolution`
    fn write_to_byte_slice(
        self,
        buf: &mut [u8],
    ) -> Result<&Self::OutputBorrowed, TaskError<Self::ProcessError>> {
        let buf = ByteSliceBuf::new(buf);
        let s = self.write_to_buf::<_, S>(buf)?;
        // Convert the type.
        // This should never fail (unless the crate has bugs), but do the
        // validation here for extra safety.
        let s =
            <&RiAbsoluteStr<S>>::try_from(s).expect("[consistency] the resolved IRI must be valid");
        Ok(s)
    }

    /// Processes the data, and appends it to the buffer inside the provided [`String`].
    ///
    /// # Failures
    ///
    /// This fails if failed to process data.
    ///
    /// # Panics
    ///
    /// This panics if failed to allocate memory.
    /// To avoid panic on allocation failure, use [`try_append_to_std_string`].
    ///
    /// [`try_append_to_std_string`]: `ProcessAndWrite::try_append_to_std_string`
    #[cfg(feature = "alloc")]
    fn append_to_std_string(
        self,
        buf: &mut String,
    ) -> Result<&Self::OutputBorrowed, Self::ProcessError> {
        match self.try_append_to_std_string(buf) {
            Ok(v) => Ok(v),
            Err(TaskError::Buffer(e)) => panic!("buffer error: {}", e),
            Err(TaskError::Process(e)) => Err(e),
        }
    }

    /// Processes the data, and appends it to the buffer inside the provided [`String`].
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * failed to allocate memory, or
    /// * failed to process data.
    ///
    /// To see examples of unresolvable IRIs, visit the [module
    /// documentation][`self`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::normalize::NormalizationTask;
    /// use iri_string::task::ProcessAndWrite;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1%ff")?;
    /// let task = NormalizationTask::from(iri);
    ///
    /// let mut buf = String::from("Result: ");
    ///
    /// let result: Result<&IriStr, _> = task.try_append_to_std_string(&mut buf);
    /// if let Ok(s) = result {
    ///     assert_eq!(s, "http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF");
    ///     assert_eq!(buf, "Result: http://example.com/slash%2Fslash/\u{03B1}\u{03B1}%FF");
    /// }
    /// # }
    /// # Ok::<_, iri_string::validate::Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    fn try_append_to_std_string(
        self,
        buf: &mut String,
    ) -> Result<&Self::OutputBorrowed, TaskError<Self::ProcessError>> {
        let s = self.write_to_buf::<_, S>(buf)?;
        // Convert the type.
        // This should never fail (unless the crate has bugs), but do the
        // validation here for extra safety.
        let s =
            <&RiAbsoluteStr<S>>::try_from(s).expect("[consistency] the resolved IRI must be valid");
        Ok(s)
    }
}

/// Spec-agnostic IRI normalization/resolution task.
#[derive(Debug, Clone, Copy)]
pub(crate) struct NormalizationTaskCommon<'a> {
    /// Target scheme.
    pub(crate) scheme: &'a str,
    /// Target authority.
    pub(crate) authority: Option<&'a str>,
    /// Target path without dot-removal.
    pub(crate) path: Path<'a>,
    /// Target query.
    pub(crate) query: Option<&'a str>,
    /// Target fragment.
    pub(crate) fragment: Option<&'a str>,
    /// Normalization type.
    pub(crate) op: NormalizationType,
}

impl<'a> NormalizationTaskCommon<'a> {
    /// Runs the resolution task and write the result to the buffer.
    // For the internal algorithm, see [RFC 3986 section 5.3],
    // [RFC 3986 section 6.2.2], and [RFC 3987 section 5.3.2].
    //
    // [RFC 3986 section 5.3]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.3
    // [RFC 3986 section 6.2]: https://datatracker.ietf.org/doc/html/rfc3986#section-6.2.2
    // [RFC 3987 section 5.3.2]: https://datatracker.ietf.org/doc/html/rfc3987#section-5.3.2
    fn write_to_buf<'b, B: Buffer<'b>, S: Spec>(
        &self,
        mut buf: B,
    ) -> Result<&'b [u8], TaskError<Error>>
    where
        TaskError<Error>: From<B::ExtendError>,
    {
        let buf_offset = buf.as_bytes().len();
        // Write the scheme.
        match self.op {
            NormalizationType::Full => {
                // Apply case normalization.
                //
                // > namely, that the scheme and US-ASCII only host are case
                // > insensitive and therefore should be normalized to lowercase.
                // >
                // > --- <https://datatracker.ietf.org/doc/html/rfc3987#section-5.3.2.1>.
                buf.extend_chars(self.scheme.chars().map(|c| c.to_ascii_lowercase()))?;
            }
            NormalizationType::RemoveDotSegments => {
                buf.push_str(self.scheme)?;
            }
        }
        buf.push_str(":")?;

        // Write the authority if available.
        if let Some(authority) = self.authority {
            buf.push_str("//")?;
            match self.op {
                NormalizationType::Full => {
                    let host_port = match rfind_split_hole(authority, b'@') {
                        Some((userinfo, host_port)) => {
                            // Don't lowercase `userinfo` even if it is ASCII only.
                            buf.extend_chars(normalize_case_and_pct_encodings::<S>(userinfo))?;
                            buf.push_str("@")?;
                            host_port
                        }
                        None => authority,
                    };
                    // Apply case normalization and percent-encoding normalization to `host`.
                    // Optional `":" port` part only consists of an ASCII colon
                    // and ASCII digit, so this won't affect to the test result.
                    if is_ascii_only_host(host_port) {
                        // Lowercase ASCII alphabets.
                        buf.extend_chars(
                            normalize_case_and_pct_encodings::<S>(host_port)
                                .map(|c| c.to_ascii_lowercase()),
                        )?;
                    } else {
                        buf.extend_chars(normalize_case_and_pct_encodings::<S>(host_port))?;
                    }
                }
                NormalizationType::RemoveDotSegments => {
                    buf.push_str(authority)?;
                }
            }
        }

        // Process and write the path.
        let path_start_pos = buf.as_bytes().len();
        match self.path {
            Path::Done(s) => {
                // Not applying `remove_dot_segments`.
                buf.push_str(s)?;
            }
            Path::NeedsProcessing(path) => {
                path.normalize::<_, S>(&mut buf, self.op)?;
            }
        }

        // If authority is absent, the path should never start with `//`.
        if self.authority.is_none() && buf.as_bytes()[path_start_pos..].starts_with(b"//") {
            return Err(TaskError::Process(Error::new()));
        }

        // Write the query if available.
        if let Some(query) = self.query {
            buf.push_str("?")?;
            match self.op {
                NormalizationType::Full => {
                    // Apply percent-encoding normalization.
                    buf.extend_chars(normalize_case_and_pct_encodings::<S>(query))?;
                }
                NormalizationType::RemoveDotSegments => {
                    buf.push_str(query)?;
                }
            }
        }

        // Write the fragment if available.
        if let Some(fragment) = self.fragment {
            buf.push_str("#")?;
            match self.op {
                NormalizationType::Full => {
                    // Apply percent-encoding normalization.
                    buf.extend_chars(normalize_case_and_pct_encodings::<S>(fragment))?;
                }
                NormalizationType::RemoveDotSegments => {
                    buf.push_str(fragment)?;
                }
            }
        }

        Ok(&buf.into_bytes()[buf_offset..])
    }
}

/// Returns an iterator to apply percent encodings normalization and case normalization.
///
/// # Precondition
///
/// The given string should be a valid IRI reference with the spec `S`.
fn normalize_case_and_pct_encodings<S: Spec>(
    i: &str,
) -> core::iter::Flatten<percent_encoding::PctNormalizedFragments<'_, S>> {
    percent_encoding::PctNormalizedFragments::new(i).flatten()
}

/// Decodes two hexdigits into a byte.
///
/// # Preconditions
///
/// The parameters `upper` and `lower` should be an ASCII hexadecimal digit.
#[must_use]
fn hexdigits_to_byte([upper, lower]: [u8; 2]) -> u8 {
    let i_upper = match (upper & 0xf0).cmp(&0x40) {
        Ordering::Less => upper - b'0',
        Ordering::Equal => upper - (b'A' - 10),
        Ordering::Greater => upper - (b'a' - 10),
    };
    let i_lower = match (lower & 0xf0).cmp(&0x40) {
        Ordering::Less => lower - b'0',
        Ordering::Equal => lower - (b'A' - 10),
        Ordering::Greater => lower - (b'a' - 10),
    };
    (i_upper << 4) + i_lower
}

/// Converts the first two hexdigit bytes in the buffer into a byte.
///
/// # Panics
///
/// Panics if the string does not start with two hexdigits.
#[must_use]
fn take_xdigits2(s: &str) -> (u8, &str) {
    let mut bytes = s.bytes();
    let upper_xdigit = bytes
        .next()
        .expect("[validity] at least two bytes should follow the `%` in a valid IRI reference");
    let lower_xdigit = bytes
        .next()
        .expect("[validity] at least two bytes should follow the `%` in a valid IRI reference");
    let v = hexdigits_to_byte([upper_xdigit, lower_xdigit]);
    (v, &s[2..])
}

/// Returns true if the given `host`/`ihost` string consists of only US-ASCII characters.
///
/// # Precondition
///
/// The given string should be valid `host` or `host ":" port` string.
fn is_ascii_only_host(mut host: &str) -> bool {
    while let Some((i, c)) = host
        .char_indices()
        .find(|(_i, c)| !c.is_ascii() || *c == '%')
    {
        if c != '%' {
            // Non-ASCII character found.
            debug_assert!(!c.is_ascii());
            return false;
        }
        // Percent-encoded character found.
        let after_pct = &host[(i + 1)..];
        let (byte, rest) = take_xdigits2(after_pct);
        if !byte.is_ascii() {
            return false;
        }
        host = rest;
    }

    // Neither non-ASCII characters nor percent-encoded characters found.
    true
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use crate::types::{IriAbsoluteStr, IriReferenceStr, IriStr, UriStr};

    #[cfg(feature = "alloc")]
    // `&[(expected, &[source_for_expected], &[different_iri])]`
    const CASES: &[(&str, &[&str], &[&str])] = &[
        (
            "https://example.com/pa/th?query#frag",
            &["https://example.com/pa/th?query#frag"],
            &[],
        ),
        (
            "https://example.com/pA/Th?Query#Frag",
            &["HTTPs://EXaMPLE.COM/pA/Th?Query#Frag"],
            &[
                "https://example.com/pa/th?Query#Frag",
                "https://example.com/pA/Th?query#Frag",
                "https://example.com/pA/Th?Query#frag",
            ],
        ),
        (
            "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
            &[
                "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
                "URN:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
            ],
            &[
                "urn:UUID:7f1450df-6678-465b-a881-188f9b6ec822",
                "urn:uuid:7F1450DF-6678-465B-A881-188F9B6EC822",
            ],
        ),
        (
            "http://example.com/a/b/d/e",
            &[
                "http://example.com/a/b/c/%2e%2e/d/e",
                "http://example.com/a/b/c/%2E%2E/d/e",
                "http://example.com/a/b/c/../d/e",
                "http://example.com/a/b/c/%2E%2e/d/e",
                "http://example.com/a/b/c/.%2e/d/e",
                "http://example.com/a/./././././b/c/.%2e/d/e",
            ],
            &[],
        ),
        (
            "http://example.com/~Ascii%21",
            &["http://example.com/%7E%41%73%63%69%69%21"],
            &[],
        ),
    ];

    #[test]
    #[cfg(feature = "alloc")]
    fn normalize() {
        for (expected, sources, different_iris) in CASES {
            let expected = IriStr::new(*expected).expect("must be a valid IRI");

            assert_eq!(
                expected
                    .normalize()
                    .expect("normalized IRI must be normalizable"),
                expected,
                "IRI normalization must be idempotent"
            );

            for src in *sources {
                let src = IriStr::new(*src).expect("must be a valid IRI");
                let normalized = src.normalize().expect("should be normalizable");
                assert_eq!(normalized, expected);
            }

            for different in *different_iris {
                let different = IriStr::new(*different).expect("must be a valid IRI");
                let normalized = different.normalize().expect("should be normalizable");
                assert_ne!(
                    normalized, expected,
                    "{:?} should not be normalized to {:?}",
                    different, expected
                );
            }
        }
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn normalize_percent_encoded_non_ascii_in_uri() {
        let uri = UriStr::new("http://example.com/?a=%CE%B1&b=%CE%CE%B1%B1")
            .expect("must be a valid URI");
        let normalized = uri.normalize().expect("should be normalizable");
        assert_eq!(normalized, "http://example.com/?a=%CE%B1&b=%CE%CE%B1%B1");
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn normalize_percent_encoded_non_ascii_in_iri() {
        let iri = IriStr::new("http://example.com/?a=%CE%B1&b=%CE%CE%B1%B1")
            .expect("must be a valid IRI");
        let normalized = iri.normalize().expect("should be normalizable");
        assert_eq!(
            normalized, "http://example.com/?a=\u{03B1}&b=%CE\u{03B1}%B1",
            "U+03B1 is an unreserved character"
        );
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn resolution_without_normalization() {
        let iri_base =
            IriAbsoluteStr::new("HTTP://%55%73%65%72:%50%61%73%73@EXAMPLE.COM/path/PATH/%ce%b1%ff")
                .expect("must be a valid IRI");
        let iri: &IriReferenceStr = iri_base.as_ref();
        let normalized = iri
            .resolve_against(iri_base)
            .expect("should produce valid result");
        assert_eq!(
            &*normalized,
            "HTTP://%55%73%65%72:%50%61%73%73@EXAMPLE.COM/path/PATH/%ce%b1%ff"
        );
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn resolution_with_normalization() {
        let iri_base =
            IriAbsoluteStr::new("HTTP://%55%73%65%72:%50%61%73%73@EXAMPLE.COM/path/PATH/%ce%b1%ff")
                .expect("must be a valid IRI");
        let iri: &IriReferenceStr = iri_base.as_ref();
        let normalized = iri
            .resolve_normalize_against(iri_base)
            .expect("should produce valid result");
        assert_eq!(
            &*normalized,
            "http://User:Pass@example.com/path/PATH/\u{03B1}%FF"
        );
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn normalize_non_ascii_only_host() {
        let uri = UriStr::new("SCHEME://Alpha%ce%b1/").expect("must be a valid URI");
        let normalized = uri.normalize().expect("should be normalizable");
        assert_eq!(normalized, "scheme://Alpha%CE%B1/");
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn normalize_host_with_sub_delims() {
        let uri = UriStr::new("SCHEME://PLUS%2bPLUS/").expect("must be a valid URI");
        let normalized = uri.normalize().expect("should be normalizable");
        assert_eq!(
            normalized, "scheme://plus%2Bplus/",
            "hexdigits in percent-encoding triplets should be normalized to uppercase"
        );
    }
}
