//! Conversion between URI/IRI types.

use core::fmt;

#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::buffer::{Buffer, BufferTooSmallError, ByteSliceBuf};
use crate::task::{Error, ProcessAndWrite};
use crate::types::{
    IriAbsoluteStr, IriFragmentStr, IriQueryStr, IriReferenceStr, IriRelativeStr, IriStr,
};
#[cfg(feature = "alloc")]
use crate::types::{
    IriAbsoluteString, IriFragmentString, IriQueryString, IriReferenceString, IriRelativeString,
    IriString,
};
use crate::types::{
    UriAbsoluteStr, UriFragmentStr, UriQueryStr, UriReferenceStr, UriRelativeStr, UriStr,
};
#[cfg(feature = "alloc")]
use crate::types::{
    UriAbsoluteString, UriFragmentString, UriQueryString, UriReferenceString, UriRelativeString,
    UriString,
};

/// Hexadecimal digits for a nibble.
const HEXDIGITS: [u8; 16] = [
    b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'A', b'B', b'C', b'D', b'E', b'F',
];

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
    ($borrowed_uri:ident, $owned_uri:ident, $borrowed_iri:ident, $owned_iri:ident) => {
        // For IRIs.
        impl<'a> ProcessAndWrite for MappedToUri<'a, $borrowed_iri> {
            type OutputBorrowed = $borrowed_uri;
            #[cfg(feature = "alloc")]
            type OutputOwned = $owned_uri;
            type ProcessError = core::convert::Infallible;

            #[cfg(feature = "alloc")]
            fn allocate_and_write(self) -> Result<Self::OutputOwned, Error<Self::ProcessError>> {
                let mut s = String::new();
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
                let num_nonascii = count_nonascii(self.0.as_str());
                if num_nonascii == 0 {
                    // No need to escape.
                    buf.push_str(self.0.as_str())?;
                } else {
                    let additional = num_nonascii * 3;
                    // Fail fast if the buffer is too short.
                    buf.try_reserve(additional)?;
                    write_percent_encoded(self.0.as_str(), |s| buf.push_str(s))?;
                }
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
                let num_nonascii = count_nonascii(self.0.as_str());
                if num_nonascii == 0 {
                    // No need to escape.
                    buf.push_str(self.0.as_str());
                } else {
                    // Extend the buffer at once.
                    let additional = self.0.len() + num_nonascii * 2;
                    buf.try_reserve(additional)?;
                    // `let Ok(_) = ...` is not yet stable as of Rust 1.58.1.
                    let _always_success = write_percent_encoded(self.0.as_str(), |s| {
                        debug_assert!(
                            (buf.capacity() - buf.len()) >= s.len(),
                            "[consistency] buffer should have been \
                             extended to the necessary size"
                        );
                        buf.push_str(s);
                        Ok::<_, core::convert::Infallible>(())
                    });
                    debug_assert!(
                        _always_success.is_ok(),
                        "[validity] the operation is infallible"
                    );
                }
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

        impl<'a> fmt::Display for MappedToUri<'a, $borrowed_iri> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write_percent_encoded(self.0.as_str(), |s| f.write_str(s))
            }
        }

        impl<'a> From<&'a $borrowed_iri> for MappedToUri<'a, $borrowed_iri> {
            #[inline]
            fn from(iri: &'a $borrowed_iri) -> Self {
                Self(iri)
            }
        }

        #[cfg(feature = "alloc")]
        impl<'a> From<&'a $owned_iri> for MappedToUri<'a, $borrowed_iri> {
            #[inline]
            fn from(iri: &'a $owned_iri) -> Self {
                Self(iri.as_slice())
            }
        }

        // For URIs.
        impl<'a> ProcessAndWrite for MappedToUri<'a, $borrowed_uri> {
            type OutputBorrowed = $borrowed_uri;
            #[cfg(feature = "alloc")]
            type OutputOwned = $owned_uri;
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

        impl<'a> fmt::Display for MappedToUri<'a, $borrowed_uri> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write_percent_encoded(self.0.as_str(), |s| f.write_str(s))
            }
        }

        impl<'a> From<&'a $borrowed_uri> for MappedToUri<'a, $borrowed_uri> {
            #[inline]
            fn from(iri: &'a $borrowed_uri) -> Self {
                Self(iri)
            }
        }

        #[cfg(feature = "alloc")]
        impl<'a> From<&'a $owned_uri> for MappedToUri<'a, $borrowed_uri> {
            #[inline]
            fn from(iri: &'a $owned_uri) -> Self {
                Self(iri.as_slice())
            }
        }
    };
}

impl_for_iri!(
    UriAbsoluteStr,
    UriAbsoluteString,
    IriAbsoluteStr,
    IriAbsoluteString
);
impl_for_iri!(
    UriReferenceStr,
    UriReferenceString,
    IriReferenceStr,
    IriReferenceString
);
impl_for_iri!(
    UriRelativeStr,
    UriRelativeString,
    IriRelativeStr,
    IriRelativeString
);
impl_for_iri!(UriStr, UriString, IriStr, IriString);
impl_for_iri!(UriQueryStr, UriQueryString, IriQueryStr, IriQueryString);
impl_for_iri!(
    UriFragmentStr,
    UriFragmentString,
    IriFragmentStr,
    IriFragmentString
);

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

/// Percent-encodes the given IRI using the given buffer.
#[cfg(feature = "alloc")]
pub(crate) fn try_percent_encode_iri_inline(
    iri: &mut String,
) -> Result<(), alloc::collections::TryReserveError> {
    // Calculate the result length and extend the buffer.
    let num_nonascii = count_nonascii(iri);
    if num_nonascii == 0 {
        // No need to escape.
        return Ok(());
    }
    let additional = num_nonascii * 2;
    iri.try_reserve(additional)?;
    let src_len = iri.len();

    // Temporarily take the ownership of the internal buffer.
    let mut buf = core::mem::take(iri).into_bytes();
    // `b'\0'` cannot appear in a valid IRI, so this default value would be
    // useful in case of debugging.
    buf.extend(core::iter::repeat(b'\0').take(additional));

    // Fill the buffer from the tail to the head.
    let mut dest_end = buf.len();
    let mut src_end = src_len;
    let mut rest_nonascii = num_nonascii;
    while rest_nonascii > 0 {
        debug_assert!(
            src_end > 0,
            "[validity] the source position should not overrun"
        );
        debug_assert!(
            dest_end > 0,
            "[validity] the destination position should not overrun"
        );
        src_end -= 1;
        dest_end -= 1;
        let byte = buf[src_end];
        if byte.is_ascii() {
            buf[dest_end] = byte;
            // Use the ASCII character directly.
        } else {
            // Percent-encode the byte.
            dest_end -= 2;
            buf[dest_end] = b'%';
            let upper = byte >> 4;
            let lower = byte & 0b1111;
            buf[dest_end + 1] = HEXDIGITS[usize::from(upper)];
            buf[dest_end + 2] = HEXDIGITS[usize::from(lower)];
            rest_nonascii -= 1;
        }
    }

    // Move the result from the temporary buffer to the destination.
    let s = String::from_utf8(buf).expect("[consistency] the encoding result is an ASCII string");
    *iri = s;
    Ok(())
}

/// Returns the number of non-ASCII characters.
#[inline]
#[must_use]
fn count_nonascii(s: &str) -> usize {
    s.bytes().filter(|b| !b.is_ascii()).count()
}
