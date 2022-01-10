//! URI and IRI resolvers.

use core::fmt;
use core::marker::PhantomData;

#[cfg(feature = "alloc")]
use alloc::collections::TryReserveError;
#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::buffer::{Buffer, BufferTooSmallError, ByteSliceBuf};
use crate::components::RiReferenceComponents;
use crate::normalize::RemoveDotSegPath;
use crate::spec::Spec;
#[cfg(feature = "alloc")]
use crate::types::RiString;
use crate::types::{RiReferenceStr, RiStr};

/// IRI resolution error.
///
/// Though this is not explicitly stated in RFC 3986, IRI resolution can fail.
/// Below are examples:
///
/// * base=`scheme:foo`, ref=`.///bar`.
///   Resulting IRI should have scheme `scheme` and path `//bar`, but does not
///   have authority.
/// * base=`scheme:foo/bar`, ref=`..//baz`.
///   Resulting IRI should have scheme `scheme` and path `//bar`, but does not
///   have authority.
///
/// IRI without authority (note that this is different from "with empty authority")
/// cannot have a path starting with `//`, since it is ambiguous and can be
/// interpreted as an IRI with authority. For the above example, `scheme://bar`
/// is not valid output, as `bar` in `scheme://bar` should be interpreted as an
/// authority, not a path.
///
/// Thus, IRI resolution can fail for some abnormal cases.
#[derive(Debug, Clone)]
pub struct Error {
    /// Inner error representation.
    repr: ErrorRepr,
}

impl Error {
    /// Returns the error kind.
    #[must_use]
    pub fn kind(&self) -> ErrorKind {
        match &self.repr {
            #[cfg(feature = "alloc")]
            ErrorRepr::Alloc(_) => ErrorKind::OutOfMemory,
            ErrorRepr::BufferFull(_) => ErrorKind::OutOfMemory,
            ErrorRepr::Unresolvable => ErrorKind::Unresolvable,
        }
    }
}

impl fmt::Display for Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.repr {
            #[cfg(feature = "alloc")]
            ErrorRepr::Alloc(_) => f.write_str("IRI resolution failed: allocation failed"),
            ErrorRepr::BufferFull(_) => f.write_str("IRI resolution failed: buffer full"),
            ErrorRepr::Unresolvable => {
                f.write_str("IRI resolution failed: unresolvable base and IRI pair")
            }
        }
    }
}

impl From<ErrorRepr> for Error {
    #[inline]
    fn from(repr: ErrorRepr) -> Self {
        Self { repr }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.repr {
            #[cfg(feature = "alloc")]
            ErrorRepr::Alloc(e) => Some(e),
            ErrorRepr::BufferFull(e) => Some(e),
            _ => None,
        }
    }
}

/// Internal representation of `ResolutionError`.
#[derive(Debug, Clone)]
pub(crate) enum ErrorRepr {
    /// Memory allocation error for `alloc` stuff.
    #[cfg(feature = "alloc")]
    Alloc(TryReserveError),
    /// Memory allocation error for fixed-size buffer.
    BufferFull(BufferTooSmallError),
    /// Unresolvable base and reference.
    Unresolvable,
}

impl From<BufferTooSmallError> for ErrorRepr {
    #[inline]
    fn from(e: BufferTooSmallError) -> Self {
        Self::BufferFull(e)
    }
}

#[cfg(feature = "alloc")]
impl From<TryReserveError> for ErrorRepr {
    #[inline]
    fn from(e: TryReserveError) -> Self {
        Self::Alloc(e)
    }
}

/// Resolution error kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// Unresolvable base and reference.
    Unresolvable,
    /// Out of memory.
    OutOfMemory,
}

/// Resolves the IRI reference.
///
/// It is recommended to use methods such as [`RiReferenceStr::resolve_against()`] and
/// [`RiRelativeStr::resolve_against()`], rather than this freestanding function.
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
/// for [`resolve::Error`][`Error`].
///
/// # Examples
///
/// ```
/// # #[derive(Debug)]
/// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
/// # impl From<iri_string::validate::Error> for Error {
/// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
/// # impl From<iri_string::resolve::Error> for Error {
/// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
/// use iri_string::resolve::{resolve, FixedBaseResolver};
/// use iri_string::types::{IriReferenceStr, IriStr};
///
/// let base = IriStr::new("http://example.com/base/")?;
/// let reference = IriReferenceStr::new("../there")?;
///
/// // Resolve `reference` against `base`.
/// let resolved = resolve(reference, base)?;
/// assert_eq!(resolved, "http://example.com/there");
///
/// // These two produces the same result with the same type.
/// assert_eq!(
///     FixedBaseResolver::new(base).resolve(reference)?,
///     "http://example.com/there"
/// );
/// assert_eq!(
///     FixedBaseResolver::new(base).create_task(reference).allocate_and_write()?,
///     "http://example.com/there"
/// );
///
/// # Ok::<_, Error>(())
/// ```
///
/// [RFC 3986 section 5.2]: https://tools.ietf.org/html/rfc3986#section-5.2
/// [`RiReferenceStr::resolve_against()`]: `RiReferenceStr::resolve_against`
/// [`RiRelativeStr::resolve_against()`]: `crate::types::RiRelativeStr::resolve_against`
#[cfg(feature = "alloc")]
pub fn resolve<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiStr<S>>,
) -> Result<RiString<S>, Error> {
    FixedBaseResolver::new(base.as_ref()).resolve(reference.as_ref())
}

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
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `FixedBaseResolver::resolve()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let resolved = resolver.resolve(reference)?;
    ///
    /// assert_eq!(resolved, "http://example.com/there");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[must_use]
    pub fn new(base: &'a RiStr<S>) -> Self {
        Self {
            base_components: RiReferenceComponents::from(base.as_ref()),
        }
    }
}

impl<'a, S: Spec> FixedBaseResolver<'a, S> {
    /// Resolves the given reference against the fixed base.
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
    /// for [`resolve::Error`][`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// let base = IriStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let resolved = resolver.resolve(reference)?;
    ///
    /// assert_eq!(resolved, "http://example.com/there");
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    pub fn resolve(&self, reference: &RiReferenceStr<S>) -> Result<RiString<S>, Error> {
        let mut buf = String::new();
        self.create_task(reference).write_to_buf(&mut buf)?;
        // Convert the type.
        // This should never fail (unless the crate has bugs), but do the
        // validation here for extra safety.
        Ok(RiString::try_from(buf).expect("the resolved IRI must be valid"))
    }

    /// Creates a resolution task.
    ///
    /// The returned [`ResolutionTask`] allows you to resolve the IRI without
    /// memory allocation, resolve to existing buffers, estimate required
    /// memory size, etc. If you need more control than
    /// [`resolve`][`Self::resolve`] method, use this.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// # #[cfg(feature = "alloc")] {
    /// # // `ResolutionTask::allocate_and_write()` is available only when
    /// # // `alloc` feature is enabled.
    /// let base = IriStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let task = resolver.create_task(reference);
    ///
    /// let resolved = task.allocate_and_write()?;
    /// assert_eq!(resolved, "http://example.com/there");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[must_use]
    pub fn create_task(&self, reference: &'a RiReferenceStr<S>) -> ResolutionTask<'a, S> {
        let b = self.base_components;
        let b_scheme = b
            .scheme
            .expect("[validity] non-relative IRI must have a scheme");
        let r = RiReferenceComponents::from(reference);

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

        let ref_toplevel = if r.scheme.is_some() {
            RefToplevel::Scheme
        } else if r.authority.is_some() {
            RefToplevel::Authority
        } else if !r.path.is_empty() {
            RefToplevel::Path
        } else if r.query.is_some() {
            RefToplevel::Query
        } else {
            RefToplevel::None
        };

        let path = match ref_toplevel {
            RefToplevel::Scheme | RefToplevel::Authority => {
                Path::NeedsDotSegRemoval(RemoveDotSegPath::from_single_path(r.path))
            }
            RefToplevel::Path => {
                if r.path.starts_with('/') {
                    Path::NeedsDotSegRemoval(RemoveDotSegPath::from_single_path(r.path))
                } else {
                    // About this branch, see
                    // <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.3>.
                    //
                    // > o  If the base URI has a defined authority component and an empty
                    // >    path, then return a string consisting of "/" concatenated with the
                    // >    reference's path; otherwise,
                    let b_path = if b.authority.is_some() && b.path.is_empty() {
                        "/"
                    } else {
                        b.path
                    };
                    Path::NeedsDotSegRemoval(RemoveDotSegPath::from_paths_to_be_resolved(
                        b_path, r.path,
                    ))
                }
            }
            RefToplevel::Query | RefToplevel::None => Path::Done(b.path),
        };

        ResolutionTask {
            common: ResolutionTaskCommon {
                scheme: r.scheme.unwrap_or(b_scheme),
                authority: ref_toplevel.choose(RefToplevel::Authority, r.authority, b.authority),
                path,
                query: ref_toplevel.choose(RefToplevel::Query, r.query, b.query),
                fragment: r.fragment,
            },
            _spec: PhantomData,
        }
    }
}

/// A task for delayed IRI resolution.
///
/// This doesn't heap-allocate until executed, and can estimate how much buffer
/// is required to execute the resolution.
pub struct ResolutionTask<'a, S> {
    /// Common data.
    common: ResolutionTaskCommon<'a>,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<S: Spec> ResolutionTask<'_, S> {
    /// Resolves the IRI, and writes it to the buffer.
    fn write_to_buf<'b, B: Buffer<'b>>(&self, buf: B) -> Result<&'b [u8], Error>
    where
        ErrorRepr: From<B::ExtendError>,
    {
        self.common.write_to_buf(buf).map_err(Into::into)
    }

    /// Resolves the IRI, and writes it to the newly allocated buffer.
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
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// let base = IriStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let task = resolver.create_task(reference);
    ///
    /// assert_eq!(task.allocate_and_write()?, "http://example.com/there");
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    pub fn allocate_and_write(&self) -> Result<RiString<S>, Error> {
        let mut s = String::new();
        self.write_to_buf(&mut s)?;
        Ok(RiString::try_from(s).expect("[consistency] the resolved IRI must be valid"))
    }

    /// Resolves the IRI, and writes it to the given byte slice.
    ///
    /// To estimate how much memory is required (at most), use
    /// [`estimate_max_buf_size_for_resolution`].
    ///
    /// # Failures
    ///
    /// This fails if
    ///
    /// * buffer was not long enough, or
    /// * the IRI referernce is unresolvable against the base.
    ///
    /// To see examples of unresolvable IRIs, visit the documentation
    /// for [`resolve::Error`][`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// let base = IriStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let task = resolver.create_task(reference);
    ///
    /// // Long enough!
    /// let mut buf = [0_u8; 128];
    /// let resolved = task.write_to_byte_slice(&mut buf[..])?;
    ///
    /// assert_eq!(resolved, "http://example.com/there");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// This returns error when the buffer is not long enough for processing.
    ///
    /// Note that it would be still not enough even if the buffer is long enough
    /// to store the result. During processing, the resolver might use more
    /// memory than the result.
    ///
    /// ```
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::{ErrorKind, FixedBaseResolver};
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// let base = IriStr::new("http://example.com/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("a/b/c/d/e/../../../../../f")?;
    /// const EXPECTED: &str = "http://example.com/f";
    /// let task = resolver.create_task(reference);
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
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriReferenceStr, IriStr, IriString};
    ///
    /// let base = IriStr::new("http://example.com/base-dir/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let task = resolver.create_task(reference);
    ///
    /// // Long buffer is reused.
    /// {
    ///     let buf_long = IriString::try_from("https://example.com/loooooooooooooooooooong-enough")?;
    ///     let buf_long_capacity = buf_long.capacity();
    ///
    ///     let resolved_long = task.write_to_iri_string(buf_long)?;
    ///     assert_eq!(resolved_long, "http://example.com/there");
    ///     assert_eq!(
    ///         resolved_long.capacity(),
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
    ///     let resolved_short = task.write_to_iri_string(buf_short)?;
    ///     assert_eq!(resolved_short, "http://example.com/there");
    ///     assert!(
    ///         resolved_short.capacity() >= buf_short_capacity,
    ///         "the internal buffer would have been expanded"
    ///     );
    /// }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
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
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// let base = IriStr::new("http://example.com/base-dir/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let task = resolver.create_task(reference);
    ///
    /// // Long buffer is reused.
    /// {
    ///     let mut buf_long = String::with_capacity(128);
    ///     let buf_long_capacity = buf_long.capacity();
    ///
    ///     let resolved_long = task.append_to_std_string(&mut buf_long)?;
    ///     assert_eq!(buf_long, "http://example.com/there");
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
    ///     assert_eq!(resolved_short, "http://example.com/there");
    ///     assert!(
    ///         buf_short.capacity() >= buf_short_capacity,
    ///         "the internal buffer would have been expanded"
    ///     );
    /// }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "alloc")]
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
    /// use iri_string::resolve::{Error, FixedBaseResolver};
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// let base = IriStr::new("http://example.com/base-dir/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let task = resolver.create_task(reference);
    ///
    /// let mut buf = String::new();
    ///
    /// let resolved_short: Result<_, Error> = task.try_append_to_std_string(&mut buf);
    /// if let Ok(s) = resolved_short {
    ///     assert_eq!(s, "http://example.com/there");
    /// }
    /// # Ok::<_, iri_string::validate::Error>(())
    /// ```
    #[cfg(feature = "alloc")]
    pub fn try_append_to_std_string<'b>(&self, buf: &'b mut String) -> Result<&'b RiStr<S>, Error> {
        let s = self.write_to_buf(buf)?;
        // Convert the type.
        // This should never fail (unless the crate has bugs), but do the
        // validation here for extra safety.
        let s = <&RiStr<S>>::try_from(s).expect("[consistency] the resolved IRI must be valid");
        Ok(s)
    }

    /// Returns the estimated maximum size required for IRI resolution.
    ///
    /// With a buffer of the returned size, IRI resolution (and merge) would
    /// succeed without OOM error. The resolution may succeed with smaller
    /// buffer than this function estimates, but it is not guaranteed.
    ///
    /// Note that this is `O(N)` operation (where N is input length).
    ///
    /// # Examples
    ///
    /// ```
    /// # #[derive(Debug)]
    /// # enum Error { Validate(iri_string::validate::Error), Resolve(iri_string::resolve::Error) }
    /// # impl From<iri_string::validate::Error> for Error {
    /// #   fn from(e: iri_string::validate::Error) -> Self { Self::Validate(e) } }
    /// # impl From<iri_string::resolve::Error> for Error {
    /// #   fn from(e: iri_string::resolve::Error) -> Self { Self::Resolve(e) } }
    /// use iri_string::resolve::FixedBaseResolver;
    /// use iri_string::types::{IriReferenceStr, IriStr};
    ///
    /// let base = IriStr::new("http://example.com/base/")?;
    /// let resolver = FixedBaseResolver::new(base);
    ///
    /// let reference = IriReferenceStr::new("../there")?;
    /// let task = resolver.create_task(reference);
    ///
    /// let max_size = task.estimate_max_buf_size_for_resolution();
    /// let mut buf = vec![0_u8; max_size];
    /// let resolved = task.write_to_byte_slice(&mut buf[..])?;
    ///
    /// assert_eq!(resolved, "http://example.com/there");
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

/// Spec-agnostic IRI resolution task.
///
/// This doesn't heap-allocate until executed, and can estimate how much buffer
/// is required to execute the resolution.
struct ResolutionTaskCommon<'a> {
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
}

impl ResolutionTaskCommon<'_> {
    /// Runs the resolution task and write the result to the buffer.
    // For the internal algorithm, see [RFC 3986 section 5.3].
    //
    // [RFC 3986 section 5.3]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.3
    fn write_to_buf<'b, B: Buffer<'b>>(&self, mut buf: B) -> Result<&'b [u8], ErrorRepr>
    where
        ErrorRepr: From<B::ExtendError>,
    {
        // Write the scheme.
        buf.push_str(self.scheme)?;
        buf.push_str(":")?;

        // Write the authority if available.
        buf.push_optional_with_prefix("//", self.authority)?;

        // Process and write the path.
        let path_start_pos = buf.as_bytes().len();
        match self.path {
            Path::Done(s) => {
                // Not applying `remove_dot_segments`.
                buf.push_str(s)?;
            }
            Path::NeedsDotSegRemoval(path) => {
                path.merge_and_remove_dot_segments(&mut buf)?;
            }
        }

        // If authority is absent, the path should never start with `//`.
        if self.authority.is_none() && buf.as_bytes()[path_start_pos..].starts_with(b"//") {
            return Err(ErrorRepr::Unresolvable);
        }

        // Write the query if available.
        buf.push_optional_with_prefix("?", self.query)?;

        // Write the fragment if available.
        buf.push_optional_with_prefix("#", self.fragment)?;

        Ok(buf.into_bytes())
    }
}

/// Path that is (possibly) not yet processed or being processed.
#[derive(Clone, Copy)]
enum Path<'a> {
    /// The result. No more processing is needed.
    Done(&'a str),
    /// Not yet completely processed path.
    NeedsDotSegRemoval(RemoveDotSegPath<'a>),
}

impl Path<'_> {
    /// Returns the estimated maximum size required for IRI resolution.
    ///
    /// With a buffer of the returned size, IRI resolution (and merge) would
    /// succeed without OOM error. The resolution may succeed with smaller
    /// buffer than this function estimates, but it is not guaranteed.
    ///
    /// Note that this is `O(N)` operation (where N is input length).
    #[must_use]
    fn estimate_max_buf_size_for_resolution(&self) -> usize {
        match self {
            Self::Done(s) => s.len(),
            Self::NeedsDotSegRemoval(path) => path.estimate_max_buf_size_for_resolution(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::types::{IriReferenceStr, IriStr};

    #[cfg(feature = "alloc")]
    use self::refimpl::resolve as resolve_refimpl;

    /// Test cases for strict resolvers.
    // [(base, [(input, output)])]
    const TEST_CASES: &[(&str, &[(&str, &str)])] = &[
        // RFC 3986, section 5.2.4.
        ("scheme:///a/b/c/./../../", &[("g", "scheme:///a/g")]),
        ("scheme:///a/b/c/./../", &[("../g", "scheme:///a/g")]),
        ("scheme:///a/b/c/./", &[("../../g", "scheme:///a/g")]),
        ("scheme:///a/b/c/", &[("./../../g", "scheme:///a/g")]),
        ("scheme:///a/b/", &[("c/./../../g", "scheme:///a/g")]),
        ("scheme:///a/", &[("b/c/./../../g", "scheme:///a/g")]),
        ("scheme:///", &[("a/b/c/./../../g", "scheme:///a/g")]),
        ("scheme:mid/content=5/../", &[("6", "scheme:mid/6")]),
        ("scheme:mid/content=5/", &[("../6", "scheme:mid/6")]),
        ("scheme:mid/", &[("content=5/../6", "scheme:mid/6")]),
        ("scheme:", &[("mid/content=5/../6", "scheme:mid/6")]),
        // RFC 3986, section 5.4.1.
        (
            "http://a/b/c/d;p?q",
            &[
                ("g:h", "g:h"),
                ("g", "http://a/b/c/g"),
                ("./g", "http://a/b/c/g"),
                ("g/", "http://a/b/c/g/"),
                ("/g", "http://a/g"),
                ("//g", "http://g"),
                ("?y", "http://a/b/c/d;p?y"),
                ("g?y", "http://a/b/c/g?y"),
                ("#s", "http://a/b/c/d;p?q#s"),
                ("g#s", "http://a/b/c/g#s"),
                ("g?y#s", "http://a/b/c/g?y#s"),
                (";x", "http://a/b/c/;x"),
                ("g;x", "http://a/b/c/g;x"),
                ("g;x?y#s", "http://a/b/c/g;x?y#s"),
                ("", "http://a/b/c/d;p?q"),
                (".", "http://a/b/c/"),
                ("./", "http://a/b/c/"),
                ("..", "http://a/b/"),
                ("../", "http://a/b/"),
                ("../g", "http://a/b/g"),
                ("../..", "http://a/"),
                ("../../", "http://a/"),
                ("../../g", "http://a/g"),
            ],
        ),
        // RFC 3986, section 5.4.2.
        (
            "http://a/b/c/d;p?q",
            &[
                ("../../../g", "http://a/g"),
                ("../../../../g", "http://a/g"),
                ("/./g", "http://a/g"),
                ("/../g", "http://a/g"),
                ("g.", "http://a/b/c/g."),
                (".g", "http://a/b/c/.g"),
                ("g..", "http://a/b/c/g.."),
                ("..g", "http://a/b/c/..g"),
                ("./../g", "http://a/b/g"),
                ("./g/.", "http://a/b/c/g/"),
                ("g/./h", "http://a/b/c/g/h"),
                ("g/../h", "http://a/b/c/h"),
                ("g;x=1/./y", "http://a/b/c/g;x=1/y"),
                ("g;x=1/../y", "http://a/b/c/y"),
                ("g?y/./x", "http://a/b/c/g?y/./x"),
                ("g?y/../x", "http://a/b/c/g?y/../x"),
                ("g#s/./x", "http://a/b/c/g#s/./x"),
                ("g#s/../x", "http://a/b/c/g#s/../x"),
                ("http:g", "http:g"),
            ],
        ),
        // Custom cases.
        (
            "http://a/b/c/d/e/../..",
            &[
                // `/a/b/c/d/e/../..` but without dot segments removal.
                ("", "http://a/b/c/d/e/../.."),
                // `/a/b/c/d/e/../..`
                ("..", "http://a/b/c/"),
                // `/a/b/c/d/e/../../`
                ("../", "http://a/b/c/"),
                // `/a/b/c/d/e/../.`
                (".", "http://a/b/c/d/"),
                // `/a/b/c/d/e/.././`
                ("./", "http://a/b/c/d/"),
                // `/a/b/c/d/e/../..?query` but without dot segments removal.
                ("?query", "http://a/b/c/d/e/../..?query"),
                // `/a/b/c/d/e/../..#frag` but without dot segments removal.
                ("#frag", "http://a/b/c/d/e/../..#frag"),
                // If the authority is specified, paths won't be merged.
                ("http://example.com", "http://example.com"),
                ("http://example.com/", "http://example.com/"),
                // If the path of the reference is not empty, remove_dot_segments is applied.
                ("http://example.com/..", "http://example.com/"),
                // If the scheme is specified, paths won't be merged.
                ("scheme:", "scheme:"),
                ("scheme:foo#frag", "scheme:foo#frag"),
            ],
        ),
        // Custom cases.
        (
            "https://a/b/c",
            &[
                ("", "https://a/b/c"),
                ("x/", "https://a/b/x/"),
                ("x//", "https://a/b/x//"),
                ("x///", "https://a/b/x///"),
                ("x//y", "https://a/b/x//y"),
                ("x//y/", "https://a/b/x//y/"),
                ("x//y//", "https://a/b/x//y//"),
                // `/b/x//..//y//`.
                // STEP     OUTPUT BUFFER   INPUT BUFFER
                //  1 :                     /b/x//..//y//
                //  2E:     /b              /x//..//y//
                //  2E:     /b/x            //..//y//
                //  2E:     /b/x/           /..//y//
                //  2C:     /b/x            //y//
                //  2E:     /b/x/           /y//
                //  2E:     /b/x//y         //
                //  2E:     /b/x//y/        /
                //  2E:     /b/x//y//
                ("x//..//y//", "https://a/b/x//y//"),
            ],
        ),
        // Custom cases.
        (
            "scheme:a/b/c",
            &[
                ("", "scheme:a/b/c"),
                ("x/", "scheme:a/b/x/"),
                ("x//", "scheme:a/b/x//"),
                ("x///", "scheme:a/b/x///"),
                ("x//y", "scheme:a/b/x//y"),
                ("x//y/", "scheme:a/b/x//y/"),
                // `a/b/x//..//y//`.
                // STEP     OUTPUT BUFFER   INPUT BUFFER
                //  1 :                     a/b/x//..//y//
                //  2E:     a               /b/x//..//y//
                //  2E:     a/b             /x//..//y//
                //  2E:     a/b/x           //..//y//
                //  2E:     a/b/x/          /..//y//
                //  2C:     a/b/x           //y//
                //  2E:     a/b/x/          /y//
                //  2E:     a/b/x//y        //
                //  2E:     a/b/x//y/       /
                //  2E:     a/b/x//y//
                ("x//..//y//", "scheme:a/b/x//y//"),
            ],
        ),
        // Custom cases.
        (
            "scheme:a",
            &[
                // `x/../..`.
                // STEP     OUTPUT BUFFER   INPUT BUFFER
                //  1 :                     x/../..
                //  2E:     x               /../..
                //  2C:                     /..
                //  2C:                     /
                //  2E:     /
                ("x/../..", "scheme:/"),
                // `x/../../y`.
                // STEP     OUTPUT BUFFER   INPUT BUFFER
                //  1 :                     x/../../y
                //  2E:     x               /../../y
                //  2C:                     /../y
                //  2C:                     /y
                //  2E:     /y
                ("x/../../y", "scheme:/y"),
            ],
        ),
        // Custom cases.
        // Empty base path should be considered as `/` when the base authority is present.
        (
            "scheme://host",
            &[
                ("", "scheme://host"),
                (".", "scheme://host/"),
                ("..", "scheme://host/"),
                ("foo", "scheme://host/foo"),
            ],
        ),
    ];

    #[test]
    #[cfg(feature = "alloc")]
    fn test_resolve_standalone() {
        for (base, pairs) in TEST_CASES {
            let base = <&IriStr>::try_from(*base)
                .expect("Invalid testcase: base IRI should be absolute IRI");
            for (input, expected) in *pairs {
                let input = <&IriReferenceStr>::try_from(*input)
                    .expect("Invalid testcase: `input` should be IRI reference");
                let got = resolve(input, base).expect("Invalid testcase: result should be valid");
                assert_eq!(
                    AsRef::<str>::as_ref(&got),
                    *expected,
                    "base = {:?}, input = {:?}",
                    base,
                    input
                );
            }
        }
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_resolve_standalone_same_result_as_reference_impl() {
        for (base, pairs) in TEST_CASES {
            let base = <&IriStr>::try_from(*base)
                .expect("Invalid testcase: base IRI should be absolute IRI");
            for (input, expected) in *pairs {
                let input = <&IriReferenceStr>::try_from(*input)
                    .expect("Invalid testcase: `input` should be IRI reference");
                let got = resolve(input, base).expect("Invalid testcase: result should be valid");
                assert_eq!(
                    AsRef::<str>::as_ref(&got),
                    *expected,
                    "base = {:?}, input = {:?}",
                    base,
                    input
                );

                let referernce_result = resolve_refimpl(input, base);
                assert_eq!(got, referernce_result);
            }
        }
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_fixed_base_resolver() {
        for (base, pairs) in TEST_CASES {
            let base = <&IriStr>::try_from(*base)
                .expect("Invalid testcase: base IRI should be absolute IRI");
            let resolver = FixedBaseResolver::new(base);
            for (input, expected) in *pairs {
                let input = <&IriReferenceStr>::try_from(*input)
                    .expect("Invalid testcase: `input` should be IRI reference");
                let got = resolver
                    .resolve(input)
                    .expect("Invalid testcase: result should be valid");
                assert_eq!(
                    AsRef::<str>::as_ref(&got),
                    *expected,
                    "base = {:?}, input = {:?}",
                    base,
                    input
                );
            }
        }
    }

    #[test]
    fn test_fixed_base_resolver_to_byte_slice() {
        let mut buf = [0_u8; 128];
        for (base, pairs) in TEST_CASES {
            let base = <&IriStr>::try_from(*base)
                .expect("Invalid testcase: base IRI should be absolute IRI");
            let resolver = FixedBaseResolver::new(base);
            for (input, expected) in *pairs {
                let input = <&IriReferenceStr>::try_from(*input)
                    .expect("Invalid testcase: `input` should be IRI reference");
                let task = resolver.create_task(input);
                let got = task
                    .write_to_byte_slice(&mut buf)
                    .expect("should not fail by OOM");
                assert_eq!(
                    AsRef::<str>::as_ref(&got),
                    *expected,
                    "base = {:?}, input = {:?}",
                    base,
                    input
                );
            }
        }
    }

    #[test]
    fn test_fixed_base_resolver_to_byte_slice_should_never_panic() {
        let mut buf_small = [0_u8; 2];
        let mut buf_empty = [];

        for (base, pairs) in TEST_CASES {
            let base = <&IriStr>::try_from(*base)
                .expect("Invalid testcase: base IRI should be absolute IRI");
            let resolver = FixedBaseResolver::new(base);
            for (input, _) in *pairs {
                let input = <&IriReferenceStr>::try_from(*input)
                    .expect("Invalid testcase: `input` should be IRI reference");
                let task = resolver.create_task(input);
                let result_small = task.write_to_byte_slice(&mut buf_small);
                assert!(
                    result_small.is_err(),
                    "expected to fail due to too small destination buffer"
                );
                let result_empty = task.write_to_byte_slice(&mut buf_empty);
                assert!(
                    result_empty.is_err(),
                    "expected to fail due to too small destination buffer"
                );
            }
        }
    }

    #[test]
    fn test_task_live_longer_than_fixed_base_resolver() {
        let mut buf = [0_u8; 128];

        let base = <&IriStr>::try_from("http://example.com/")
            .expect("Invalid testcase: base IRI should be a valid IRI");
        let reference = <&IriReferenceStr>::try_from("foo/bar")
            .expect("Invalid testcase: reference IRI should be a valid IRI-reference");

        let task = {
            let resolver = FixedBaseResolver::new(base);
            resolver.create_task(reference)
        };
        let result = task
            .write_to_byte_slice(&mut buf)
            .expect("`buf` should be long enough");
        assert_eq!(result, "http://example.com/foo/bar");
    }

    /// Reference implementation based on RFC 3986 section 5.
    #[cfg(feature = "alloc")]
    mod refimpl {
        use alloc::format;
        use alloc::string::String;

        use crate::components::RiReferenceComponents;
        use crate::spec::Spec;
        use crate::types::{RiReferenceStr, RiStr, RiString};

        /// Resolves the relative IRI.
        ///
        /// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.2>.
        pub(super) fn resolve<S: Spec>(
            reference: &RiReferenceStr<S>,
            base: &RiStr<S>,
        ) -> RiString<S> {
            let r = RiReferenceComponents::from(reference);
            let b = RiReferenceComponents::from(base.as_ref());

            let t_scheme: &str;
            let t_authority: Option<&str>;
            let t_path: String;
            let t_query: Option<&str>;

            if let Some(r_scheme) = r.scheme {
                t_scheme = r_scheme;
                t_authority = r.authority;
                t_path = remove_dot_segments(r.path.into());
                t_query = r.query;
            } else {
                if r.authority.is_some() {
                    t_authority = r.authority;
                    t_path = remove_dot_segments(r.path.into());
                    t_query = r.query;
                } else {
                    if r.path.is_empty() {
                        t_path = b.path.into();
                        if r.query.is_some() {
                            t_query = r.query;
                        } else {
                            t_query = b.query;
                        }
                    } else {
                        if r.path.starts_with('/') {
                            t_path = remove_dot_segments(r.path.into());
                        } else {
                            t_path =
                                remove_dot_segments(merge(b.path, r.path, b.authority.is_some()));
                        }
                        t_query = r.query;
                    }
                    t_authority = b.authority;
                }
                t_scheme = b.scheme.expect("non-relative IRI must have a scheme");
            }
            let t_fragment: Option<&str> = r.fragment;

            let s = recompose(t_scheme, t_authority, &t_path, t_query, t_fragment);
            RiString::<S>::try_from(s).expect("resolution result must be a valid IRI")
        }

        /// Merges the two paths.
        ///
        /// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.3>.
        fn merge(base_path: &str, ref_path: &str, base_authority_defined: bool) -> String {
            if base_authority_defined && base_path.is_empty() {
                format!("/{}", ref_path)
            } else {
                let base_path_end = base_path.rfind('/').map_or(0, |s| s + 1);
                format!("{}{}", &base_path[..base_path_end], ref_path)
            }
        }

        /// Removes dot segments from the path.
        ///
        /// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4>.
        fn remove_dot_segments(mut input: String) -> String {
            let mut output = String::new();
            while !input.is_empty() {
                if input.starts_with("../") {
                    // 2A.
                    input.drain(..3);
                } else if input.starts_with("./") {
                    // 2A.
                    input.drain(..2);
                } else if input.starts_with("/./") {
                    // 2B.
                    input.replace_range(..3, "/");
                } else if input == "/." {
                    // 2B.
                    input.replace_range(..2, "/");
                } else if input.starts_with("/../") {
                    // 2C.
                    input.replace_range(..4, "/");
                    remove_last_segment_and_preceding_slash(&mut output);
                } else if input == "/.." {
                    // 2C.
                    input.replace_range(..3, "/");
                    remove_last_segment_and_preceding_slash(&mut output);
                } else if input == "." {
                    // 2D.
                    input.drain(..1);
                } else if input == ".." {
                    // 2D.
                    input.drain(..2);
                } else {
                    // 2E.
                    let first_seg_end = if let Some(after_slash) = input.strip_prefix('/') {
                        // `+1` is the length of the initial slash.
                        after_slash
                            .find('/')
                            .map_or_else(|| input.len(), |pos| pos + 1)
                    } else {
                        input.find('/').unwrap_or_else(|| input.len())
                    };
                    output.extend(input.drain(..first_seg_end));
                }
            }

            output
        }

        /// Removes the last path segment and the preceding slash if any.
        ///
        /// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4>,
        /// step 2C.
        fn remove_last_segment_and_preceding_slash(output: &mut String) {
            match output.rfind('/') {
                Some(slash_pos) => {
                    output.drain(slash_pos..);
                }
                None => output.clear(),
            }
        }

        /// Recomposes the components.
        ///
        /// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.3>.
        fn recompose(
            scheme: &str,
            authority: Option<&str>,
            path: &str,
            query: Option<&str>,
            fragment: Option<&str>,
        ) -> String {
            let mut result = String::new();

            result.push_str(scheme);
            result.push(':');
            if let Some(authority) = authority {
                result.push_str("//");
                result.push_str(authority);
            }
            result.push_str(path);
            if let Some(query) = query {
                result.push('?');
                result.push_str(query);
            }
            if let Some(fragment) = fragment {
                result.push('#');
                result.push_str(fragment);
            }

            result
        }
    }
}
