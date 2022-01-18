//! Normalization.

mod error;
mod path;

use core::marker::PhantomData;

#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::buffer::{Buffer, ByteSliceBuf};
use crate::components::RiReferenceComponents;
use crate::parser::char;
use crate::spec::Spec;
use crate::types::RiStr;
#[cfg(feature = "alloc")]
use crate::types::RiString;

use self::error::ErrorRepr;
pub use self::error::{Error, ErrorKind};
pub(crate) use self::path::{Path, PathToNormalize};

/// Creates a normalization task.
///
/// # Examples
///
/// ```
/// # #[derive(Debug)] enum Error {
/// #     Validate(iri_string::validate::Error),
/// #     Normalize(iri_string::normalize::Error) }
/// # impl From<iri_string::validate::Error> for Error {
/// #     fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
/// # impl From<iri_string::normalize::Error> for Error {
/// #     fn from(e: iri_string::normalize::Error) -> Self { Self::Normalize(e) } }
/// # #[cfg(feature = "alloc")] {
/// use iri_string::normalize::create_task;
/// use iri_string::types::IriStr;
///
/// let iri = IriStr::new("HTTP://example.COM/foo/./bar/%2e%2e/../baz")?;
///
/// let normalized = create_task(iri).allocate_and_write()?;
/// assert_eq!(normalized, "http://example.com/baz");
/// # }
/// # Ok::<_, Error>(())
/// ```
#[must_use]
pub fn create_task<S: Spec>(iri: &RiStr<S>) -> NormalizationTask<'_, S> {
    NormalizationTask::new(iri)
}

/// Normalization type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NormalizationType {
    /// Full generic syntax-based normalization.
    Full,
    /// Only `remove_dot_segments` algorithm.
    RemoveDotSegments,
}

/// IRI normalization/resolution task.
#[derive(Debug, Clone, Copy)]
pub struct NormalizationTask<'a, S> {
    /// Common data.
    common: NormalizationTaskCommon<'a>,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<'a, S: Spec> NormalizationTask<'a, S> {
    /// Creates a new normalization task.
    fn new(iri: &'a RiStr<S>) -> Self {
        let components = RiReferenceComponents::from(iri.as_ref());
        let (scheme, authority, path, query, fragment) = components.to_major();
        let scheme = scheme.expect("[validity] `absolute IRI must have `scheme`");
        let path = Path::NeedsProcessing(PathToNormalize::from_single_path(path));

        Self {
            common: NormalizationTaskCommon {
                scheme,
                authority,
                path,
                query,
                fragment,
                op: NormalizationType::Full,
            },
            _spec: PhantomData,
        }
    }

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
    fn write_to_buf<'b, B: Buffer<'b>>(&self, buf: B) -> Result<&'b [u8], Error>
    where
        ErrorRepr: From<B::ExtendError>,
    {
        self.common.write_to_buf(buf).map_err(Into::into)
    }

    /// Normalizes the IRI, and writes it to the newly allocated buffer.
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * buffer was not long enough, or
    /// * the resulting IRI referernce is unresolvable.
    ///
    /// To see examples of unresolvable IRIs, visit the module documentation
    /// for [`resolve`][`crate::resolve`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] enum Error {
    /// #     Validate(iri_string::validate::Error),
    /// #     Normalize(iri_string::normalize::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::normalize::Error> for Error {
    /// #     fn from(e: iri_string::normalize::Error) -> Self { Self::Normalize(e) } }
    /// use iri_string::normalize::create_task;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1")?;
    /// let task = create_task(iri.as_ref());
    ///
    /// assert_eq!(
    ///     task.allocate_and_write()?,
    ///     "http://example.com/slash%2Fslash/\u{03B1}%CE%B1"
    /// );
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn allocate_and_write(&self) -> Result<RiString<S>, Error> {
        let mut s = String::new();
        self.write_to_buf(&mut s)?;
        Ok(RiString::try_from(s).expect("[consistency] the resolved IRI must be valid"))
    }

    /// Normalizes the IRI, and writes it to the given byte slice.
    ///
    /// To estimate how much memory is required (at most), use
    /// [`estimate_max_buf_size_for_resolution`].
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * buffer was not long enough, or
    /// * the resulting IRI referernce is unresolvable.
    ///
    /// To see examples of unresolvable IRIs, visit the module documentation
    /// for [`resolve`][`crate::resolve`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] enum Error {
    /// #     Validate(iri_string::validate::Error),
    /// #     Normalize(iri_string::normalize::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::normalize::Error> for Error {
    /// #     fn from(e: iri_string::normalize::Error) -> Self { Self::Normalize(e) } }
    /// use iri_string::normalize::create_task;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1")?;
    /// let task = create_task(iri);
    ///
    /// // Long enough!
    /// let mut buf = [0_u8; 128];
    /// let normalized = task.write_to_byte_slice(&mut buf[..])?;
    ///
    /// assert_eq!(normalized, "http://example.com/slash%2Fslash/\u{03B1}%CE%B1");
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
    /// # #[derive(Debug)] enum Error {
    /// #     Validate(iri_string::validate::Error),
    /// #     Normalize(iri_string::normalize::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::normalize::Error> for Error {
    /// #     fn from(e: iri_string::normalize::Error) -> Self { Self::Normalize(e) } }
    /// use iri_string::normalize::{ErrorKind, NormalizationTask, create_task};
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("http://example.com/a/b/c/d/e/../../../../../f")?;
    /// const EXPECTED: &str = "http://example.com/f";
    /// let task = create_task(iri);
    ///
    /// // Buffer is too short for processing, even though it is long enough
    /// // to store the result.
    /// let mut buf = [0_u8; EXPECTED.len()];
    /// let resolved = task.write_to_byte_slice(&mut buf[..]);
    /// assert_eq!(
    ///     resolved.map_err(|e| e.kind()),
    ///     Err(ErrorKind::OutOfMemory),
    ///     "failed due to not enough buffer size"
    /// );
    /// // You can retry writing if you have larger buffer,
    /// // since `task` was not consumed.
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// [`estimate_max_buf_size_for_resolution`]: `Self::estimate_max_buf_size_for_resolution`
    pub fn write_to_byte_slice<'b>(&self, buf: &'b mut [u8]) -> Result<&'b RiStr<S>, Error> {
        let buf = ByteSliceBuf::new(buf);
        let s = self.write_to_buf(buf)?;
        // Convert the type.
        // This should never fail (unless the crate has bugs), but do the
        // validation here for extra safety.
        let s = <&RiStr<S>>::try_from(s).expect("[consistency] the resolved IRI must be valid");
        Ok(s)
    }

    /// Resolves the IRI, and writes it to the buffer inside the provided [`RiString`].
    ///
    /// This temporarily takes the ownership of the destination string buffer,
    /// since `RiSting<S>` always allocates (i.e. does not accept empty string
    /// as a default value) and the buffer cannot be replaced temporarily with
    /// the non-allocating default values. In order to make the function
    /// exception-safe, this cannot write to the `&mut RiString<S>` directly.
    ///
    /// # Failures
    ///
    /// This fails if:
    ///
    /// * buffer was not long enough, or
    /// * the resulting IRI referernce is unresolvable.
    ///
    /// To see examples of unresolvable IRIs, visit the module documentation
    /// for [`resolve`][`crate::resolve`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)] enum Error {
    /// #     Validate(iri_string::validate::Error),
    /// #     Normalize(iri_string::normalize::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::normalize::Error> for Error {
    /// #     fn from(e: iri_string::normalize::Error) -> Self { Self::Normalize(e) } }
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::normalize::create_task;
    /// use iri_string::types::{IriStr, IriString};
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/../../there")?;
    /// let task = create_task(iri);
    ///
    /// // Long buffer is reused.
    /// {
    ///     let buf_long = IriString::try_from("https://example.com/loooooooooooooooooooong-enough/sooooooooooooooo-long")?;
    ///     let buf_long_capacity = buf_long.capacity();
    ///
    ///     let normalized_long = task.write_to_iri_string(buf_long)?;
    ///     assert_eq!(normalized_long, "http://example.com/there");
    ///     assert_eq!(
    ///         normalized_long.capacity(),
    ///         buf_long_capacity,
    ///         "the internal buffer was reused"
    ///     );
    /// }
    ///
    /// // Short buffer will be extended or reallocated.
    /// {
    ///     let buf_short = IriString::try_from("foo:bar")?;
    ///     let buf_short_capacity = buf_short.capacity();
    ///
    ///     let normalized_short = task.write_to_iri_string(buf_short)?;
    ///     assert_eq!(normalized_short, "http://example.com/there");
    ///     assert!(
    ///         normalized_short.capacity() >= buf_short_capacity,
    ///         "the internal buffer would have been expanded"
    ///     );
    /// }
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn write_to_iri_string(&self, dest: RiString<S>) -> Result<RiString<S>, Error> {
        let mut buf: String = dest.into();
        buf.clear();
        self.write_to_buf(&mut buf)?;
        Ok(RiString::<S>::try_from(buf).expect("[consistency] the resolved IRI must be valid"))
    }

    /// Resolves the IRI, and appends it to the buffer inside the provided [`String`].
    ///
    /// # Failures
    ///
    /// This fails if
    ///
    /// * memory allocation failed, or
    /// * the IRI referernce is unresolvable against the base.
    ///
    /// To see examples of unresolvable IRIs, visit the documentation
    /// for [`resolve::Error`][`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::normalize::create_task;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1")?;
    /// let task = create_task(iri);
    ///
    /// let mut buf = String::from("Result: ");
    ///
    /// let result: Result<&IriStr, _> = task.try_append_to_std_string(&mut buf);
    /// if let Ok(s) = result {
    ///     assert_eq!(s, "http://example.com/slash%2Fslash/\u{03B1}%CE%B1");
    ///     assert_eq!(buf, "Result: http://example.com/slash%2Fslash/\u{03B1}%CE%B1");
    /// }
    /// # }
    /// # Ok::<_, iri_string::validate::Error>(())
    /// ```
    ///
    /// The buffer will be automatically expanded or reallocated when it was
    /// not long enough.
    ///
    /// ```
    /// # #[derive(Debug)] enum Error {
    /// #     Validate(iri_string::validate::Error),
    /// #     Normalize(iri_string::normalize::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::normalize::Error> for Error {
    /// #     fn from(e: iri_string::normalize::Error) -> Self { Self::Normalize(e) } }
    /// use iri_string::normalize::create_task;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1")?;
    /// let task = create_task(iri);
    ///
    /// // Long buffer is reused.
    /// {
    ///     let mut buf_long = String::with_capacity(128);
    ///     let buf_long_capacity = buf_long.capacity();
    ///
    ///     let resolved_long = task.append_to_std_string(&mut buf_long)?;
    ///     assert_eq!(buf_long, "http://example.com/slash%2Fslash/\u{03B1}%CE%B1");
    ///     assert_eq!(
    ///         buf_long.capacity(),
    ///         buf_long_capacity,
    ///         "the internal buffer was reused"
    ///     );
    /// }
    ///
    /// // Short buffer will be extended or reallocated.
    /// {
    ///     let mut buf_short = String::new();
    ///     let buf_short_capacity = buf_short.capacity();
    ///     assert_eq!(buf_short_capacity, 0, "String::new() does not heap-allocate");
    ///
    ///     let resolved_short = task.append_to_std_string(&mut buf_short)?;
    ///     assert_eq!(resolved_short, "http://example.com/slash%2Fslash/\u{03B1}%CE%B1");
    ///     assert!(
    ///         buf_short.capacity() >= buf_short_capacity,
    ///         "the internal buffer would have been expanded"
    ///     );
    /// }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn append_to_std_string<'b>(&self, buf: &'b mut String) -> Result<&'b RiStr<S>, Error> {
        self.try_append_to_std_string(buf)
    }

    /// Resolves the IRI, and appends it to the buffer inside the provided [`String`].
    ///
    /// # Failures
    ///
    /// This fails if
    ///
    /// * memory allocation failed, or
    /// * the IRI referernce is unresolvable against the base.
    ///
    /// To see examples of unresolvable IRIs, visit the documentation
    /// for [`resolve::Error`][`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::normalize::create_task;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1")?;
    /// let task = create_task(iri);
    ///
    /// let mut buf = String::from("Result: ");
    ///
    /// let result: Result<&IriStr, _> = task.try_append_to_std_string(&mut buf);
    /// if let Ok(s) = result {
    ///     assert_eq!(s, "http://example.com/slash%2Fslash/\u{03B1}%CE%B1");
    ///     assert_eq!(buf, "Result: http://example.com/slash%2Fslash/\u{03B1}%CE%B1");
    /// }
    /// # }
    /// # Ok::<_, iri_string::validate::Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn try_append_to_std_string<'b>(&self, buf: &'b mut String) -> Result<&'b RiStr<S>, Error> {
        let s = self.write_to_buf(buf)?;
        // Convert the type.
        // This should never fail (unless the crate has bugs), but do the
        // validation here for extra safety.
        let s = <&RiStr<S>>::try_from(s).expect("[consistency] the resolved IRI must be valid");
        Ok(s)
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
    /// # #[derive(Debug)] enum Error {
    /// #     Validate(iri_string::validate::Error),
    /// #     Normalize(iri_string::normalize::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #     fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::normalize::Error> for Error {
    /// #     fn from(e: iri_string::normalize::Error) -> Self { Self::Normalize(e) } }
    /// use iri_string::normalize::create_task;
    /// use iri_string::types::IriStr;
    ///
    /// let iri = IriStr::new("HTTP://e%78ample%2ecom/a/../slash%2fslash/\u{03B1}%ce%b1")?;
    /// let task = create_task(iri);
    ///
    /// let max_size = task.estimate_max_buf_size_for_resolution();
    /// let mut buf = vec![0_u8; max_size];
    /// let resolved = task.write_to_byte_slice(&mut buf[..])?;
    ///
    /// assert_eq!(resolved, "http://example.com/slash%2Fslash/\u{03B1}%CE%B1");
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

impl<'a, S: Spec> From<NormalizationTaskCommon<'a>> for NormalizationTask<'a, S> {
    #[inline]
    fn from(common: NormalizationTaskCommon<'a>) -> Self {
        Self {
            common,
            _spec: PhantomData,
        }
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

impl NormalizationTaskCommon<'_> {
    /// Runs the resolution task and write the result to the buffer.
    // For the internal algorithm, see [RFC 3986 section 5.3],
    // [RFC 3986 section 6.2.2], and [RFC 3987 section 5.3.2].
    //
    // [RFC 3986 section 5.3]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.3
    // [RFC 3986 section 6.2]: https://datatracker.ietf.org/doc/html/rfc3986#section-6.2.2
    // [RFC 3987 section 5.3.2]: https://datatracker.ietf.org/doc/html/rfc3987#section-5.3.2
    fn write_to_buf<'b, B: Buffer<'b>>(&self, mut buf: B) -> Result<&'b [u8], ErrorRepr>
    where
        ErrorRepr: From<B::ExtendError>,
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
                    // Apply case normalization and percent-encoding normalization.
                    buf.extend_chars(normalize_case_and_pct_encodings(authority))?;
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
                path.normalize(&mut buf, self.op)?;
            }
        }

        // If authority is absent, the path should never start with `//`.
        if self.authority.is_none() && buf.as_bytes()[path_start_pos..].starts_with(b"//") {
            return Err(ErrorRepr::Unresolvable);
        }

        // Write the query if available.
        if let Some(query) = self.query {
            buf.push_str("?")?;
            match self.op {
                NormalizationType::Full => {
                    // Apply percent-encoding normalization.
                    buf.extend_chars(normalize_pct_encodings(query))?;
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
                    buf.extend_chars(normalize_pct_encodings(fragment))?;
                }
                NormalizationType::RemoveDotSegments => {
                    buf.push_str(fragment)?;
                }
            }
        }

        Ok(&buf.into_bytes()[buf_offset..])
    }
}

/// A state for case normalization and percent-encoding normalization.
#[derive(Debug, Clone)]
struct NormalizeCaseAndPercentEncodings<'a> {
    /// The rest of the input.
    rest: &'a str,
    /// Number of characters that consists of a percent encoding.
    rest_pct_encoded: u8,
    /// Whether to normalize the case.
    normalize_case: bool,
}

impl NormalizeCaseAndPercentEncodings<'_> {
    /// Removes the first character in the buffer.
    fn consume_char(&mut self) -> Option<char> {
        let mut iter = self.rest.chars();
        let next = iter.next()?;
        let advanced = self.rest.len() - iter.as_str().len();
        self.rest = &self.rest[advanced..];
        Some(next)
    }
}

impl Iterator for NormalizeCaseAndPercentEncodings<'_> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        let first_char = self.consume_char()?;

        if let Some(new_rest_pct) = self.rest_pct_encoded.checked_sub(1) {
            self.rest_pct_encoded = new_rest_pct;
            return Some(first_char.to_ascii_uppercase());
        }

        if first_char != '%' {
            if self.normalize_case && first_char.is_ascii_uppercase() {
                return Some(first_char.to_ascii_lowercase());
            }
            return Some(first_char);
        }

        let decoded = {
            let bytes = self.rest.as_bytes();
            let upper_hex = match bytes[0] {
                c @ b'0'..=b'9' => c - b'0',
                c @ b'a'..=b'f' => c - b'a' + 10,
                c @ b'A'..=b'F' => c - b'A' + 10,
                _ => {
                    unreachable!("valid IRIs must not have incomplete or invalid percent encodings")
                }
            };
            let lower_hex = match bytes[1] {
                c @ b'0'..=b'9' => c - b'0',
                c @ b'a'..=b'f' => c - b'a' + 10,
                c @ b'A'..=b'F' => c - b'A' + 10,
                _ => {
                    unreachable!("valid IRIs must not have incomplete or invalid percent encodings")
                }
            };
            let code = (upper_hex << 4) | lower_hex;
            if self.normalize_case && code.is_ascii_uppercase() {
                code.to_ascii_lowercase()
            } else {
                code
            }
        };
        if decoded.is_ascii() && char::is_ascii_unreserved(decoded) {
            self.consume_char();
            self.consume_char();
            return Some(decoded as char);
        }

        self.rest_pct_encoded = 2;
        Some(first_char)
    }
}

/// Returns an iterator to apply case normalization and percent encodings normalization.
fn normalize_case_and_pct_encodings(i: &str) -> NormalizeCaseAndPercentEncodings<'_> {
    NormalizeCaseAndPercentEncodings {
        rest: i,
        rest_pct_encoded: 0,
        normalize_case: true,
    }
}

/// Returns an iterator to apply only percent encodings normalization.
fn normalize_pct_encodings(i: &str) -> NormalizeCaseAndPercentEncodings<'_> {
    NormalizeCaseAndPercentEncodings {
        rest: i,
        rest_pct_encoded: 0,
        normalize_case: false,
    }
}
