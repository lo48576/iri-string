//! Conversion between URI/IRI types.

use core::fmt;

#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::buffer::{Buffer, BufferTooSmallError, ByteSliceBuf};
use crate::spec::{IriSpec, UriSpec};
use crate::task::{Error, ProcessAndWrite};
use crate::types::{RiAbsoluteStr, RiReferenceStr, RiRelativeStr, RiStr};
#[cfg(feature = "alloc")]
use crate::types::{RiAbsoluteString, RiReferenceString, RiRelativeString, RiString};

/// A resource identifier mapped to a URI of some kind.
///
/// Note that some methods are not directly implemented but provided from
/// [`ProcessAndWrite`] trait.
///
/// Supported `Src` type are:
///
/// * IRIs:
///     + [`IriAbsoluteStr`] (alias of `RiAbsoluteStr<IriSpec>`)
///     + [`IriReferenceStr`] (alias of `RiReferenceStr<IriSpec>`)
///     + [`IriRelativeStr`] (alias of `RiRelativeStr<IriSpec>`)
///     + [`IriStr`] (alias of `RiStr<IriSpec>`)
/// * URIs:
///     + [`UriAbsoluteStr`] (alias of `RiAbsoluteStr<UriSpec>`)
///     + [`UriReferenceStr`] (alias of `RiReferenceStr<UriSpec>`)
///     + [`UriRelativeStr`] (alias of `RiRelativeStr<UriSpec>`)
///     + [`UriStr`] (alias of `RiStr<UriSpec>`)
///
/// # Examples
///
/// ```
/// use iri_string::convert::MappedToUri;
/// use iri_string::types::{IriStr, UriStr};
///
/// let src = IriStr::new("http://example.com/?alpha=\u{03B1}")?;
/// // The type is `MappedToUri<IriStr>`, but you usually don't need to specify.
/// let mapped = MappedToUri::from(src).to_string();
/// assert_eq!(mapped, "http://example.com/?alpha=%CE%B1");
/// # Ok::<_, iri_string::validate::Error>(())
/// ```
///
/// [`IriAbsoluteStr`]: crate::types::IriAbsoluteStr
/// [`IriReferenceStr`]: crate::types::IriReferenceStr
/// [`IriRelativeStr`]: crate::types::IriRelativeStr
/// [`IriStr`]: crate::types::IriStr
/// [`UriAbsoluteStr`]: crate::types::UriAbsoluteStr
/// [`UriReferenceStr`]: crate::types::UriReferenceStr
/// [`UriRelativeStr`]: crate::types::UriRelativeStr
/// [`UriStr`]: crate::types::UriStr
#[derive(Debug, Clone, Copy)]
pub struct MappedToUri<'a, Src: ?Sized>(&'a Src);

/// Implement conversions for an IRI string type.
macro_rules! impl_for_iri {
    ($base_borrowed:ident, $base_owned:ident) => {
        // For IRIs.
        impl<'a> ProcessAndWrite for MappedToUri<'a, $base_borrowed<IriSpec>> {
            type OutputBorrowed = $base_borrowed<UriSpec>;
            #[cfg(feature = "alloc")]
            type OutputOwned = $base_owned<UriSpec>;
            type ProcessError = core::convert::Infallible;

            #[cfg(feature = "alloc")]
            fn allocate_and_write(self) -> Result<Self::OutputOwned, Error<Self::ProcessError>> {
                // The length of the result will be the equal to or longer than the source IRI.
                let mut s = String::new();
                s.try_reserve(self.0.len())?;
                self.try_append_to_std_string(&mut s)?;
                // Convert the type.
                // This should never fail (unless the crate has bugs), but do the
                // validation here for extra safety.
                Ok(Self::OutputOwned::try_from(s)
                    .expect("[consistency] the resolved URI must be valid"))
            }

            fn write_to_byte_slice(
                self,
                buf: &mut [u8],
            ) -> Result<&Self::OutputBorrowed, Error<Self::ProcessError>> {
                let mut buf = ByteSliceBuf::new(buf);
                write_percent_encoded(self.0.as_str(), |s| buf.push_str(s))?;
                // Convert the type.
                // This should never fail (unless the crate has bugs), but do the
                // validation here for extra safety.
                let s = <&Self::OutputBorrowed>::try_from(buf.into_bytes())
                    .expect("[consistency] an IRI must be convertible into a valid URI");
                Ok(s)
            }

            #[cfg(feature = "alloc")]
            fn try_append_to_std_string(
                self,
                buf: &mut String,
            ) -> Result<&Self::OutputBorrowed, Error<Self::ProcessError>> {
                let start = buf.len();
                write_percent_encoded(
                    self.0.as_str(),
                    |s| -> Result<(), alloc::collections::TryReserveError> {
                        buf.try_reserve(s.len())?;
                        buf.push_str(s);
                        Ok(())
                    },
                )?;
                let end = buf.len();
                let written = &buf[start..end];
                let iri = unsafe {
                    // SAFETY: When non-ASCII characters in an IRI are percent-encoded,
                    // it is still valid IRI, and is now also valid URI (since it
                    // contains only ASCII characters).
                    Self::OutputBorrowed::new_maybe_unchecked(written)
                };
                Ok(iri)
            }
        }

        impl<'a> fmt::Display for MappedToUri<'a, $base_borrowed<IriSpec>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write_percent_encoded(self.0.as_str(), |s| f.write_str(s))
            }
        }

        impl<'a> From<&'a $base_borrowed<IriSpec>> for MappedToUri<'a, $base_borrowed<IriSpec>> {
            #[inline]
            fn from(iri: &'a $base_borrowed<IriSpec>) -> Self {
                Self(iri)
            }
        }

        #[cfg(feature = "alloc")]
        impl<'a> From<&'a $base_owned<IriSpec>> for MappedToUri<'a, $base_borrowed<IriSpec>> {
            #[inline]
            fn from(iri: &'a $base_owned<IriSpec>) -> Self {
                Self(iri.as_slice())
            }
        }

        // For URIs.
        impl<'a> ProcessAndWrite for MappedToUri<'a, $base_borrowed<UriSpec>> {
            type OutputBorrowed = $base_borrowed<UriSpec>;
            #[cfg(feature = "alloc")]
            type OutputOwned = $base_owned<UriSpec>;
            type ProcessError = core::convert::Infallible;

            #[cfg(feature = "alloc")]
            fn allocate_and_write(self) -> Result<Self::OutputOwned, Error<Self::ProcessError>> {
                let mut s = String::new();
                s.try_reserve(self.0.len())?;
                s.push_str(self.0.as_str());
                let iri = unsafe {
                    // SAFETY: The content of `s` is equivalent to `self.0`, which is a valid IRI.
                    Self::OutputOwned::new_maybe_unchecked(s)
                };
                Ok(iri)
            }

            fn write_to_byte_slice(
                self,
                buf: &mut [u8],
            ) -> Result<&Self::OutputBorrowed, Error<Self::ProcessError>> {
                if buf.len() < self.0.len() {
                    return Err(BufferTooSmallError::new().into());
                }
                let dest = buf
                    .get_mut(..self.0.len())
                    .ok_or(Error::Buffer(BufferTooSmallError::new().into()))?;
                dest.copy_from_slice(self.0.as_str().as_bytes());
                let s = unsafe {
                    // SAFETY: `dest` is completely same as `self.0`, which is valid UTF-8 string.
                    core::str::from_utf8_unchecked(dest)
                };
                let iri = unsafe {
                    // SAFETY: `dest` is completely same as `self.0`, which is
                    // valid `Self::OutputBorrowed` IRI.
                    Self::OutputBorrowed::new_maybe_unchecked(s)
                };
                Ok(iri)
            }

            #[cfg(feature = "alloc")]
            fn try_append_to_std_string(
                self,
                buf: &mut String,
            ) -> Result<&Self::OutputBorrowed, Error<Self::ProcessError>> {
                buf.try_reserve(self.0.len())?;
                let start = buf.len();
                buf.push_str(self.0.as_str());
                let end = buf.len();
                let written = &buf[start..end];
                let iri = unsafe {
                    // SAFETY: When non-ASCII characters in an IRI are percent-encoded,
                    // it is still valid IRI, and is now also valid URI (since it
                    // contains only ASCII characters).
                    Self::OutputBorrowed::new_maybe_unchecked(written)
                };
                Ok(iri)
            }
        }

        impl<'a> fmt::Display for MappedToUri<'a, $base_borrowed<UriSpec>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write_percent_encoded(self.0.as_str(), |s| f.write_str(s))
            }
        }

        impl<'a> From<&'a $base_borrowed<UriSpec>> for MappedToUri<'a, $base_borrowed<UriSpec>> {
            #[inline]
            fn from(iri: &'a $base_borrowed<UriSpec>) -> Self {
                Self(iri)
            }
        }

        #[cfg(feature = "alloc")]
        impl<'a> From<&'a $base_owned<UriSpec>> for MappedToUri<'a, $base_borrowed<UriSpec>> {
            #[inline]
            fn from(iri: &'a $base_owned<UriSpec>) -> Self {
                Self(iri.as_slice())
            }
        }
    };
}

impl_for_iri!(RiAbsoluteStr, RiAbsoluteString);
impl_for_iri!(RiReferenceStr, RiReferenceString);
impl_for_iri!(RiRelativeStr, RiRelativeString);
impl_for_iri!(RiStr, RiString);

/// Percent-encodes and writes the IRI string using the given buffer.
fn write_percent_encoded<F, E>(mut s: &str, mut f: F) -> Result<(), E>
where
    F: FnMut(&str) -> Result<(), E>,
{
    while !s.is_empty() {
        // Skip ASCII characters.
        let non_ascii_pos = s
            .bytes()
            .position(|b| !b.is_ascii())
            .unwrap_or_else(|| s.len());
        let (ascii, rest) = s.split_at(non_ascii_pos);
        if !ascii.is_empty() {
            f(ascii)?;
            s = rest;
        }

        if s.is_empty() {
            return Ok(());
        }

        // Search for the next ASCII character.
        let nonascii_end = s
            .bytes()
            .position(|b| b.is_ascii())
            .unwrap_or_else(|| s.len());
        let (nonasciis, rest) = s.split_at(nonascii_end);
        debug_assert!(
            !nonasciis.is_empty(),
            "string without non-ASCII characters should have caused early return"
        );
        s = rest;

        // Escape non-ASCII characters as percent-encoded bytes.
        //
        // RFC 3987 (section 3.1 step 2) says "for each character in
        // 'ucschar' or 'iprivate'", but this simply means "for each
        // non-ASCII characters" since any non-ASCII characters that can
        // appear in an IRI match `ucschar` or `iprivate`.
        /// Number of source bytes to encode at once.
        const NUM_BYTES_AT_ONCE: usize = 21;
        percent_encode_bytes(nonasciis, &mut [0_u8; NUM_BYTES_AT_ONCE * 3], &mut f)?;
    }

    Ok(())
}

/// Percent-encode the string and pass the encoded chunks to the given function.
///
/// `buf` is used as a temporary working buffer. It is initialized by this
/// function, so users can pass any mutable byte slice with enough size.
///
/// # Precondition
///
/// The length of `buf` must be 3 bytes or more.
fn percent_encode_bytes<F, E>(s: &str, buf: &mut [u8], mut f: F) -> Result<(), E>
where
    for<'a> F: FnMut(&'a str) -> Result<(), E>,
{
    /// Fill the buffer by percent-encoded bytes.
    ///
    /// Note that this function applies percent-encoding to every characters,
    /// even if it is ASCII alphabet.
    ///
    /// # Precondition
    ///
    /// * The length of `buf` must be 3 bytes or more.
    /// * All of the `buf[i * 3]` elements should already be set to `b'%'`.
    // This function have many preconditions and I don't want checks for them
    // to be mandatory, so make this nested inner function.
    fn fill_by_percent_encoded<'a>(buf: &'a mut [u8], bytes: &mut core::str::Bytes<'_>) -> &'a str {
        /// Hexadecimal digits for a nibble.
        const HEXDIGITS: [u8; 16] = [
            b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'A', b'B', b'C', b'D',
            b'E', b'F',
        ];

        let src_len = bytes.len();
        // `<[u8; N]>::array_chunks_mut` is unstable as of Rust 1.58.1.
        for (dest, byte) in buf.chunks_exact_mut(3).zip(bytes.by_ref()) {
            debug_assert_eq!(
                dest.len(),
                3,
                "[validity] `chunks_exact()` must return a slice with the exact length"
            );
            debug_assert_eq!(
                dest[0], b'%',
                "[precondition] the buffer must be properly initialized"
            );

            let upper = byte >> 4;
            let lower = byte & 0b1111;
            dest[1] = HEXDIGITS[usize::from(upper)];
            dest[2] = HEXDIGITS[usize::from(lower)];
        }
        let num_dest_written = (src_len - bytes.len()) * 3;
        let buf_filled = &buf[..num_dest_written];
        unsafe {
            // SAFETY: `b'%'` and `HEXDIGITS[_]` are all ASCII characters,
            // so the string is valid UTF-8 bytes.
            debug_assert!(core::str::from_utf8(buf_filled).is_ok());
            core::str::from_utf8_unchecked(buf_filled)
        }
    }

    assert!(
        buf.len() >= 3,
        "[precondition] length of `buf` must be 3 bytes or more"
    );

    // Drop the elements that will never be used.
    // The length to be used is always a multiple of three.
    let buf_len = buf.len() / 3 * 3;
    let buf = &mut buf[..buf_len];

    // Fill some bytes with `%`.
    // This will be vectorized by optimization (especially for long buffers),
    // so no need to selectively set `buf[i * 3]`.
    buf.fill(b'%');

    let mut bytes = s.bytes();
    // `<core::str::Bytes as ExactSizeIterator>::is_empty` is unstable as of Rust 1.58.1.
    while bytes.len() != 0 {
        let encoded = fill_by_percent_encoded(buf, &mut bytes);
        f(encoded)?;
    }

    Ok(())
}
