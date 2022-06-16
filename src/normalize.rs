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
//! assert!(base.try_normalize().is_err(), "this normalization should fail");
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
mod pct_case;

use core::fmt;
use core::marker::PhantomData;

use crate::buffer::{Buffer, ByteSliceBuf, FmtWritableBuffer};
use crate::components::RiReferenceComponents;
use crate::parser::str::rfind_split_hole;
use crate::parser::trusted::is_ascii_only_host;
use crate::spec::Spec;
use crate::task::{Error as TaskError, ProcessAndWrite};
use crate::types::{RiAbsoluteStr, RiStr};
#[cfg(feature = "alloc")]
use crate::types::{RiAbsoluteString, RiString};

pub use self::error::Error;
pub(crate) use self::path::{Path, PathToNormalize};
pub(crate) use self::pct_case::{
    is_pct_case_normalized, DisplayNormalizedAsciiOnlyHost, DisplayPctCaseNormalize,
};

/// Error on normalization by `core::fmt::Display`.
#[derive(Debug, Clone)]
enum DisplayNormalizeError {
    /// Formatting error.
    Format(fmt::Error),
    /// Normalization error.
    Normalization(Error),
}

impl From<fmt::Error> for DisplayNormalizeError {
    #[inline]
    fn from(e: fmt::Error) -> Self {
        Self::Format(e)
    }
}

impl From<Error> for DisplayNormalizeError {
    #[inline]
    fn from(e: Error) -> Self {
        Self::Normalization(e)
    }
}

/// Normalization operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct NormalizationOp {
    /// Whether to apply case normalization and percent-encoding normalization.
    ///
    /// Note that even when this option is `true`, plain US-ASCII characters
    /// won't be automatically lowered. Users should apply case normalization
    /// for US-ASCII only `host` component by themselves.
    pub(crate) case_pct_normalization: bool,
    /// Whether to apply serialization described in WHATWG URL Standard when necessary.
    ///
    /// If this option is enabled, serialization of WHATWG URL Standard will be
    /// used instead of pure RFC 3986 algorithm in some situation.
    ///
    /// Consider an IRI that would have `foo` as a scheme, no authority, and
    /// `//bar` as a path, after normalization. According to RFC 3986 algorithm,
    /// the resulting string would be `foo://bar`, but this is obviously invalid
    /// since `bar` here would be interpreted as an authority, rather than the
    /// part of the path.
    ///
    /// To prevent such erroneous / fallible normalization and resolution,
    /// WHATWG URL Standard have an additional rule to modify the path.
    /// That rule is, prepending `/.` to the path to prevent starting from `//`
    /// when no authority is present.
    /// By this rule, the result of the example case above will be
    /// `foo:/.//bar`. This can be unambiguously interpreted as the combination
    /// of the scheme `foo`, no authority, and the path `/.//bar`, which is
    /// semantically equal to the path `//bar`.
    pub(crate) whatwg_serialization: bool,
}

/// Spec-agnostic IRI normalization/resolution input.
#[derive(Debug, Clone, Copy)]
struct NormalizationInput<'a> {
    /// Target scheme.
    scheme: &'a str,
    /// Target authority.
    authority: Option<&'a str>,
    /// Target path without dot-removal.
    path: Path<'a>,
    /// Target query.
    query: Option<&'a str>,
    /// Target fragment.
    fragment: Option<&'a str>,
    /// Normalization type.
    op: NormalizationOp,
}

/// Writable as a normalized IRI.
///
/// Note that this implicitly apply serialization rule defined by WHATWG URL
/// Standard (to handle normalization impossible by RFC 3986) because `Display`
/// should not fail by reasons other than backend I/O failure. If you make the
/// normalization fail in such cases, check if the path starts with `/./`.
/// When the normalization succeeds by RFC 3986 algorithm, the path never starts
/// with `/./`.
struct DisplayNormalize<'a, S> {
    /// Spec-agnostic normalization input.
    input: NormalizationInput<'a>,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<S: Spec> fmt::Debug for DisplayNormalize<'_, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DisplayNormalize")
            .field("input", &self.input)
            .finish()
    }
}

impl<'a, S: Spec> DisplayNormalize<'a, S> {
    /// Creates a new `DisplayNormalize` object from the given input.
    #[inline]
    #[must_use]
    fn from_input(input: NormalizationInput<'a>) -> Self {
        Self {
            input,
            _spec: PhantomData,
        }
    }
}

impl<S: Spec> fmt::Display for DisplayNormalize<'_, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_write(f).map_err(|_| fmt::Error)
    }
}

impl<S: Spec> DisplayNormalize<'_, S> {
    /// Writes the normalized IRI string.
    fn fmt_write<W: fmt::Write>(&self, f: &mut W) -> Result<(), DisplayNormalizeError> {
        // Write the scheme.
        if self.input.op.case_pct_normalization {
            // Apply case normalization.
            //
            // > namely, that the scheme and US-ASCII only host are case
            // > insensitive and therefore should be normalized to lowercase.
            // >
            // > --- <https://datatracker.ietf.org/doc/html/rfc3987#section-5.3.2.1>.
            //
            // Note that `scheme` consists of only ASCII characters and contains
            // no percent-encoded characters.
            self.input
                .scheme
                .chars()
                .map(|c| c.to_ascii_lowercase())
                .try_for_each(|c| f.write_char(c))?;
        } else {
            f.write_str(self.input.scheme)?;
        }
        f.write_str(":")?;

        // Write the authority if available.
        if let Some(authority) = self.input.authority {
            f.write_str("//")?;
            if self.input.op.case_pct_normalization {
                normalize_authority::<S, _>(f, authority)?;
            } else {
                // No case/pct normalization.
                f.write_str(authority)?;
            }
        }

        // Process and write the path.
        match self.input.path {
            Path::Done(s) => f.write_str(s)?,
            Path::NeedsProcessing(path) => {
                path.fmt_write_normalize::<S, _>(f, self.input.op, self.input.authority.is_some())?
            }
        }

        // Write the query if available.
        if let Some(query) = self.input.query {
            f.write_char('?')?;
            if self.input.op.case_pct_normalization {
                // Apply percent-encoding normalization.
                write!(f, "{}", DisplayPctCaseNormalize::<S>::new(query))?;
            } else {
                f.write_str(query)?;
            }
        }

        // Write the fragment if available.
        if let Some(fragment) = self.input.fragment {
            f.write_char('#')?;
            if self.input.op.case_pct_normalization {
                // Apply percent-encoding normalization.
                write!(f, "{}", DisplayPctCaseNormalize::<S>::new(fragment))?;
            } else {
                f.write_str(fragment)?;
            }
        }

        Ok(())
    }
}

/// Writes the normalized authority.
fn normalize_authority<S: Spec, W: fmt::Write>(f: &mut W, authority: &str) -> fmt::Result {
    let host_port = match rfind_split_hole(authority, b'@') {
        Some((userinfo, host_port)) => {
            // Don't lowercase `userinfo` even if it is ASCII only. `userinfo`
            // is not a part of `host`.
            write!(f, "{}", DisplayPctCaseNormalize::<S>::new(userinfo))?;
            f.write_char('@')?;
            host_port
        }
        None => authority,
    };
    normalize_host_port::<S, _>(f, host_port)
}

/// Writes the normalized host and port.
fn normalize_host_port<S: Spec, W: fmt::Write>(f: &mut W, host_port: &str) -> fmt::Result {
    // If the suffix is a colon, it is a delimiter between the host and empty
    // port. An empty port should be removed during normalization (see RFC 3986
    // section 3.2.3), so strip it.
    //
    // > URI producers and normalizers should omit the port component and its
    // > ":" delimiter if port is empty or if its value would be the same as
    // > that of the scheme's default.
    // >
    // > --- [RFC 3986 section 3.2.3. Port](https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2.3)
    let host_port = host_port.strip_suffix(':').unwrap_or(host_port);

    // Apply case normalization and percent-encoding normalization to `host`.
    // Optional `":" port` part only consists of an ASCII colon and ASCII
    // digits, so this won't affect to the test result.
    if is_ascii_only_host(host_port) {
        // If the host is ASCII characters only, make plain alphabets lower case.
        write!(f, "{}", DisplayNormalizedAsciiOnlyHost::new(host_port))
    } else {
        write!(f, "{}", DisplayPctCaseNormalize::<S>::new(host_port))
    }
}

/// IRI normalization/resolution task.
///
/// Most of the main functionalities are provided from [`ProcessAndWrite`] trait,
/// so you may need to write `use iri_string::task::ProcessAndWrite` where you
/// use this task type.
#[derive(Debug, Clone, Copy)]
pub struct NormalizationTask<'a, T: ?Sized> {
    /// Normalization input.
    input: NormalizationInput<'a>,
    /// Spec-aware IRI string type.
    _ty_str: PhantomData<fn() -> T>,
}

impl<'a, T: ?Sized> NormalizationTask<'a, T> {
    /// Creates a new normalization task.
    #[inline]
    #[must_use]
    pub(crate) fn new(
        scheme: &'a str,
        authority: Option<&'a str>,
        path: Path<'a>,
        query: Option<&'a str>,
        fragment: Option<&'a str>,
        op: NormalizationOp,
    ) -> Self {
        Self {
            input: NormalizationInput {
                scheme,
                authority,
                path,
                query,
                fragment,
                op,
            },
            _ty_str: PhantomData,
        }
    }
}

impl<'a, S: Spec> From<&'a RiStr<S>> for NormalizationTask<'a, RiStr<S>> {
    fn from(iri: &'a RiStr<S>) -> Self {
        let components = RiReferenceComponents::<S>::from(iri.as_ref());
        let (scheme, authority, path, query, fragment) = components.to_major();
        let scheme = scheme.expect("[validity] `absolute IRI must have `scheme`");
        let path = Path::NeedsProcessing(PathToNormalize::from_single_path(path));

        Self {
            input: NormalizationInput {
                scheme,
                authority,
                path,
                query,
                fragment,
                op: NormalizationOp {
                    case_pct_normalization: true,
                    whatwg_serialization: false,
                },
            },
            _ty_str: PhantomData,
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a, S: Spec> From<&'a RiString<S>> for NormalizationTask<'a, RiStr<S>> {
    #[inline]
    fn from(iri: &'a RiString<S>) -> Self {
        Self::from(iri.as_slice())
    }
}

impl<'a, S: Spec> From<&'a RiAbsoluteStr<S>> for NormalizationTask<'a, RiAbsoluteStr<S>> {
    fn from(iri: &'a RiAbsoluteStr<S>) -> Self {
        let components = RiReferenceComponents::<S>::from(iri.as_ref());
        let (scheme, authority, path, query, fragment) = components.to_major();
        let scheme = scheme.expect("[validity] `absolute IRI must have `scheme`");
        let path = Path::NeedsProcessing(PathToNormalize::from_single_path(path));

        Self {
            input: NormalizationInput {
                scheme,
                authority,
                path,
                query,
                fragment,
                op: NormalizationOp {
                    case_pct_normalization: true,
                    whatwg_serialization: false,
                },
            },
            _ty_str: PhantomData,
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a, S: Spec> From<&'a RiAbsoluteString<S>> for NormalizationTask<'a, RiAbsoluteStr<S>> {
    #[inline]
    fn from(iri: &'a RiAbsoluteString<S>) -> Self {
        Self::from(iri.as_slice())
    }
}

impl<'a, T: ?Sized + AsRef<str>> NormalizationTask<'a, T> {
    /// Enables normalization for the task.
    #[inline]
    pub fn enable_normalization(&mut self) {
        self.input.op.case_pct_normalization = true;
    }

    /// Enables WHATWG URL Standard serialization for the task.
    #[inline]
    pub fn enable_whatwg_serialization(&mut self) {
        self.input.op.whatwg_serialization = true;
    }

    /// Resolves the IRI, and writes it to the buffer.
    fn write_to_buf<'b, B: Buffer<'b>, S: Spec>(
        &self,
        mut buf: B,
    ) -> Result<&'b [u8], TaskError<Error>>
    where
        TaskError<Error>: From<B::ExtendError>,
    {
        let buf_offset = buf.as_bytes().len();
        let mut writer = FmtWritableBuffer::new(&mut buf);
        match DisplayNormalize::<S>::from_input(self.input).fmt_write(&mut writer) {
            Ok(_) => Ok(&buf.into_bytes()[buf_offset..]),
            Err(DisplayNormalizeError::Format(_)) => Err(writer.take_error_unwrap().into()),
            Err(DisplayNormalizeError::Normalization(e)) => Err(TaskError::Process(e)),
        }
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
        let known_exact = self.input.scheme.len()
            + self.input.authority.map_or(0, |s| s.len() + 2)
            + self.input.query.map_or(0, |s| s.len() + 1)
            + self.input.fragment.map_or(0, |s| s.len() + 1);
        let path_max = match &self.input.path {
            Path::Done(s) => s.len(),
            Path::NeedsProcessing(path) => path.len(),
        };

        known_exact + path_max
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
    /// You can get maximum required buffer size by
    /// [`estimate_max_buf_size_for_resolution`] method.
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
    /// You can get maximum required buffer size by
    /// [`estimate_max_buf_size_for_resolution`] method.
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

#[cfg(test)]
#[cfg(feature = "alloc")]
mod tests_display {
    use super::*;

    use crate::spec::{IriSpec, UriSpec};

    #[test]
    fn normalize_iri_1() {
        let disp = DisplayNormalize::<IriSpec> {
            input: NormalizationInput {
                scheme: "http",
                authority: Some("user:pass@example.com:80"),
                path: Path::NeedsProcessing(PathToNormalize::from_paths_to_be_resolved(
                    "/1/2/3/4/.././5/../6/",
                    "a/b/c/d/e/f/g/h/i/../../../j/k/l/../../../../m/n/./o",
                )),
                query: Some("query"),
                fragment: Some("fragment"),
                op: NormalizationOp {
                    case_pct_normalization: true,
                    whatwg_serialization: true,
                },
            },
            _spec: PhantomData,
        };
        assert_eq!(
            disp.to_string(),
            "http://user:pass@example.com:80/1/2/3/6/a/b/c/d/e/m/n/o?query#fragment"
        );
    }

    #[test]
    fn normalize_iri_2() {
        let disp = DisplayNormalize::<IriSpec> {
            input: NormalizationInput {
                scheme: "http",
                authority: Some("user:pass@example.com:80"),
                path: Path::NeedsProcessing(PathToNormalize::from_paths_to_be_resolved(
                    "/%7e/2/beta=%CE%B2/4/.././5/../6/",
                    "a/b/alpha=%CE%B1/d/e/f/g/h/i/../../../j/k/l/../../../../%3c/%7e/./%3e",
                )),
                query: Some("query"),
                fragment: Some("fragment"),
                op: NormalizationOp {
                    case_pct_normalization: true,
                    whatwg_serialization: true,
                },
            },
            _spec: PhantomData,
        };
        assert_eq!(
            disp.to_string(),
            "http://user:pass@example.com:80/~/2/beta=\u{03B2}/6/a/b/alpha=\u{03B1}/d/e/%3C/~/%3E?query#fragment"
        );
    }

    #[test]
    fn normalize_uri_1() {
        let disp = DisplayNormalize::<UriSpec> {
            input: NormalizationInput {
                scheme: "http",
                authority: Some("user:pass@example.com:80"),
                path: Path::NeedsProcessing(PathToNormalize::from_paths_to_be_resolved(
                    "/%7e/2/beta=%ce%b2/4/.././5/../6/",
                    "a/b/alpha=%CE%B1/d/e/f/g/h/i/../../../j/k/l/../../../../%3c/%7e/./%3e",
                )),
                query: Some("query"),
                fragment: Some("fragment"),
                op: NormalizationOp {
                    case_pct_normalization: true,
                    whatwg_serialization: true,
                },
            },
            _spec: PhantomData,
        };
        assert_eq!(
            disp.to_string(),
            "http://user:pass@example.com:80/~/2/beta=%CE%B2/6/a/b/alpha=%CE%B1/d/e/%3C/~/%3E?query#fragment"
        );
    }

    #[test]
    fn trailing_slash_should_remain() {
        let disp = DisplayNormalize::<UriSpec> {
            input: NormalizationInput {
                scheme: "http",
                authority: Some("example.com"),
                path: Path::NeedsProcessing(PathToNormalize::from_single_path("/../../")),
                query: None,
                fragment: None,
                op: NormalizationOp {
                    case_pct_normalization: true,
                    whatwg_serialization: true,
                },
            },
            _spec: PhantomData,
        };
        assert_eq!(disp.to_string(), "http://example.com/");
    }

    #[test]
    fn leading_double_slash_without_authority_whatwg() {
        let disp = DisplayNormalize::<UriSpec> {
            input: NormalizationInput {
                scheme: "scheme",
                authority: None,
                path: Path::NeedsProcessing(PathToNormalize::from_paths_to_be_resolved(
                    "/a/b/", "../..//c",
                )),
                query: None,
                fragment: None,
                op: NormalizationOp {
                    case_pct_normalization: true,
                    whatwg_serialization: true,
                },
            },
            _spec: PhantomData,
        };
        assert_eq!(disp.to_string(), "scheme:/.//c");
    }

    #[test]
    fn leading_double_slash_without_authority_non_whatwg() {
        let disp = DisplayNormalize::<UriSpec> {
            input: NormalizationInput {
                scheme: "scheme",
                authority: None,
                path: Path::NeedsProcessing(PathToNormalize::from_paths_to_be_resolved(
                    "/a/b/", "../..//c",
                )),
                query: None,
                fragment: None,
                op: NormalizationOp {
                    case_pct_normalization: true,
                    whatwg_serialization: false,
                },
            },
            _spec: PhantomData,
        };
        struct DummyWriter;
        impl fmt::Write for DummyWriter {
            fn write_str(&mut self, _: &str) -> fmt::Result {
                Ok(())
            }
        }
        assert!(disp.fmt_write(&mut DummyWriter).is_err());
    }
}

#[cfg(test)]
#[cfg(feature = "alloc")]
mod tests {
    use crate::types::{IriAbsoluteStr, IriReferenceStr, IriStr, UriStr};

    // `&[(expected, &[source_for_expected], &[iri_with_different_normalization_result])]`
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
        (
            // See <https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2.3>:
            //
            // > URI producers and normalizers should omit the port component
            // > and its ":" delimiter if port is empty or if its value would
            // > be the same as that of the scheme's default.
            "https://example.com/",
            &["https://example.com:/"],
            &[],
        ),
    ];

    #[test]
    fn normalize() {
        for (expected, sources, different_iris) in CASES {
            let expected = IriStr::new(*expected).expect("must be a valid IRI");

            assert_eq!(
                expected
                    .try_normalize()
                    .expect("normalized IRI must be normalizable"),
                expected,
                "IRI normalization must be idempotent"
            );

            for src in *sources {
                let src = IriStr::new(*src).expect("must be a valid IRI");
                let normalized = src.try_normalize().expect("should be normalizable");
                assert_eq!(normalized, expected);
            }

            for different in *different_iris {
                let different = IriStr::new(*different).expect("must be a valid IRI");
                let normalized = different.try_normalize().expect("should be normalizable");
                assert_ne!(
                    normalized, expected,
                    "{:?} should not be normalized to {:?}",
                    different, expected
                );
            }
        }
    }

    #[test]
    fn normalize_percent_encoded_non_ascii_in_uri() {
        let uri = UriStr::new("http://example.com/?a=%CE%B1&b=%CE%CE%B1%B1")
            .expect("must be a valid URI");
        let normalized = uri.try_normalize().expect("should be normalizable");
        assert_eq!(normalized, "http://example.com/?a=%CE%B1&b=%CE%CE%B1%B1");
    }

    #[test]
    fn normalize_percent_encoded_non_ascii_in_iri() {
        let iri = IriStr::new("http://example.com/?a=%CE%B1&b=%CE%CE%B1%B1")
            .expect("must be a valid IRI");
        let normalized = iri.try_normalize().expect("should be normalizable");
        assert_eq!(
            normalized, "http://example.com/?a=\u{03B1}&b=%CE\u{03B1}%B1",
            "U+03B1 is an unreserved character"
        );
    }

    #[test]
    fn resolution_without_normalization() {
        let iri_base =
            IriAbsoluteStr::new("HTTP://%55%73%65%72:%50%61%73%73@EXAMPLE.COM/path/PATH/%ce%b1%ff")
                .expect("must be a valid IRI");
        let iri: &IriReferenceStr = iri_base.as_ref();
        let normalized = iri
            .try_resolve_against(iri_base)
            .expect("should produce valid result");
        assert_eq!(
            &*normalized,
            "HTTP://%55%73%65%72:%50%61%73%73@EXAMPLE.COM/path/PATH/%ce%b1%ff"
        );
    }

    #[test]
    fn resolution_with_normalization() {
        let iri_base =
            IriAbsoluteStr::new("HTTP://%55%73%65%72:%50%61%73%73@EXAMPLE.COM/path/PATH/%ce%b1%ff")
                .expect("must be a valid IRI");
        let iri: &IriReferenceStr = iri_base.as_ref();
        let normalized = iri
            .try_resolve_normalize_against(iri_base)
            .expect("should produce valid result");
        assert_eq!(
            &*normalized,
            "http://User:Pass@example.com/path/PATH/\u{03B1}%FF"
        );
    }

    #[test]
    fn normalize_non_ascii_only_host() {
        let uri = UriStr::new("SCHEME://Alpha%ce%b1/").expect("must be a valid URI");
        let normalized = uri.try_normalize().expect("should be normalizable");
        assert_eq!(normalized, "scheme://Alpha%CE%B1/");
    }

    #[test]
    fn normalize_host_with_sub_delims() {
        let uri = UriStr::new("SCHEME://PLUS%2bPLUS/").expect("must be a valid URI");
        let normalized = uri.try_normalize().expect("should be normalizable");
        assert_eq!(
            normalized, "scheme://plus%2Bplus/",
            "hexdigits in percent-encoding triplets should be normalized to uppercase"
        );
    }

    #[test]
    fn whatwg_normalization() {
        let uri = UriStr::new("scheme:..///not-a-host").expect("must be a valid URI");
        assert!(!uri.is_normalized_whatwg());

        let normalized = uri.try_normalize_whatwg().expect("cannot allocate memory");
        assert_eq!(normalized, "scheme:/.//not-a-host");
        assert!(normalized.is_normalized_whatwg());

        let normalized_again = uri.try_normalize_whatwg().expect("cannot allocate memory");
        assert_eq!(normalized_again, normalized);
        assert!(normalized_again.is_normalized_whatwg());
    }
}
