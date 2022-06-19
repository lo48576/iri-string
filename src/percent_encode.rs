//! Percent encoding.

use core::fmt::{self, Write as _};
use core::marker::PhantomData;

#[cfg(feature = "alloc")]
use alloc::collections::TryReserveError;
#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::buffer::Buffer as _;
use crate::buffer::ByteSliceBuf;
use crate::parser::char;
use crate::spec::{IriSpec, Spec, UriSpec};
use crate::task::{Error as TaskError, ProcessAndWrite};

/// A proxy to percent-encode a string as a part of URI.
pub type PercentEncodedForUri<T> = PercentEncoded<T, UriSpec>;

/// A proxy to percent-encode a string as a part of IRI.
pub type PercentEncodedForIri<T> = PercentEncoded<T, IriSpec>;

/// Context for percent encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
enum Context {
    /// Encode the string as a reg-name (usually called as "hostname").
    RegName,
    /// Encode the string as a path segment.
    ///
    /// A slash (`/`) will be encoded to `%2F`.
    PathSegment,
    /// Encode the string as path segments joined with `/`.
    ///
    /// A slash (`/`) will be used as is.
    Path,
    /// Encode the string as a query string (without the `?` prefix).
    Query,
    /// Encode the string as a fragment string (without the `#` prefix).
    Fragment,
}

/// A proxy to percent-encode a string.
///
/// Type aliases [`PercentEncodedForUri`] and [`PercentEncodedForUri`] are provided.
/// You can use them to make the expression simpler, for example write
/// `PercentEncodedForUri::from_path(foo)` instead of
/// `PercentEncoded::<_, UriSpec>::from_path(foo)`.
#[derive(Debug, Clone, Copy)]
pub struct PercentEncoded<T, S> {
    /// Source string context.
    context: Context,
    /// Raw string before being encoded.
    raw: T,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<T: fmt::Display, S: Spec> PercentEncoded<T, S> {
    /// Creates an encoded string from a raw reg-name (i.e. hostname or domain).
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::percent_encode::PercentEncoded;
    /// use iri_string::spec::UriSpec;
    ///
    /// let raw = "alpha.\u{03B1}.example.com";
    /// let encoded = "alpha.%CE%B1.example.com";
    /// assert_eq!(
    ///     PercentEncoded::<_, UriSpec>::from_reg_name(raw).to_string(),
    ///     encoded
    /// );
    /// # }
    /// ```
    pub fn from_reg_name(raw: T) -> Self {
        Self {
            context: Context::RegName,
            raw,
            _spec: PhantomData,
        }
    }

    /// Creates an encoded string from a raw path segment.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::percent_encode::PercentEncoded;
    /// use iri_string::spec::UriSpec;
    ///
    /// let raw = "alpha/\u{03B1}?#";
    /// // Note that `/` is encoded to `%2F`.
    /// let encoded = "alpha%2F%CE%B1%3F%23";
    /// assert_eq!(
    ///     PercentEncoded::<_, UriSpec>::from_path_segment(raw).to_string(),
    ///     encoded
    /// );
    /// # }
    /// ```
    pub fn from_path_segment(raw: T) -> Self {
        Self {
            context: Context::PathSegment,
            raw,
            _spec: PhantomData,
        }
    }

    /// Creates an encoded string from a raw path.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::percent_encode::PercentEncoded;
    /// use iri_string::spec::UriSpec;
    ///
    /// let raw = "alpha/\u{03B1}?#";
    /// // Note that `/` is NOT percent encoded.
    /// let encoded = "alpha/%CE%B1%3F%23";
    /// assert_eq!(
    ///     PercentEncoded::<_, UriSpec>::from_path(raw).to_string(),
    ///     encoded
    /// );
    /// # }
    /// ```
    pub fn from_path(raw: T) -> Self {
        Self {
            context: Context::Path,
            raw,
            _spec: PhantomData,
        }
    }

    /// Creates an encoded string from a raw query.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::percent_encode::PercentEncoded;
    /// use iri_string::spec::UriSpec;
    ///
    /// let raw = "alpha/\u{03B1}?#";
    /// let encoded = "alpha/%CE%B1?%23";
    /// assert_eq!(
    ///     PercentEncoded::<_, UriSpec>::from_query(raw).to_string(),
    ///     encoded
    /// );
    /// # }
    /// ```
    pub fn from_query(raw: T) -> Self {
        Self {
            context: Context::Query,
            raw,
            _spec: PhantomData,
        }
    }

    /// Creates an encoded string from a raw fragment.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use iri_string::percent_encode::PercentEncoded;
    /// use iri_string::spec::UriSpec;
    ///
    /// let raw = "alpha/\u{03B1}?#";
    /// let encoded = "alpha/%CE%B1?%23";
    /// assert_eq!(
    ///     PercentEncoded::<_, UriSpec>::from_fragment(raw).to_string(),
    ///     encoded
    /// );
    /// # }
    /// ```
    pub fn from_fragment(raw: T) -> Self {
        Self {
            context: Context::Fragment,
            raw,
            _spec: PhantomData,
        }
    }
}

impl<T: fmt::Display, S: Spec> fmt::Display for PercentEncoded<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// Filter that encodes a character before written if necessary.
        struct Filter<'a, 'b, S> {
            /// Encoding context.
            context: Context,
            /// Writer.
            writer: &'a mut fmt::Formatter<'b>,
            /// Spec.
            _spec: PhantomData<fn() -> S>,
        }
        impl<S: Spec> fmt::Write for Filter<'_, '_, S> {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                s.chars().try_for_each(|c| self.write_char(c))
            }
            fn write_char(&mut self, c: char) -> fmt::Result {
                let is_valid_char = match (self.context, c.is_ascii()) {
                    (Context::RegName, true) => char::is_ascii_regname(c as u8),
                    (Context::RegName, false) => char::is_nonascii_regname::<S>(c),
                    (Context::PathSegment, true) => char::is_ascii_pchar(c as u8),
                    (Context::PathSegment, false) => S::is_nonascii_char_unreserved(c),
                    (Context::Path, true) => c == '/' || char::is_ascii_pchar(c as u8),
                    (Context::Path, false) => S::is_nonascii_char_unreserved(c),
                    (Context::Query, true) => c == '/' || char::is_ascii_frag_query(c as u8),
                    (Context::Query, false) => char::is_nonascii_query::<S>(c),
                    (Context::Fragment, true) => c == '/' || char::is_ascii_frag_query(c as u8),
                    (Context::Fragment, false) => char::is_nonascii_fragment::<S>(c),
                };
                if is_valid_char {
                    self.writer.write_char(c)
                } else {
                    write_pct_encoded_char(&mut self.writer, c)
                }
            }
        }
        let mut filter = Filter {
            context: self.context,
            writer: f,
            _spec: PhantomData::<fn() -> S>,
        };
        write!(filter, "{}", self.raw)
    }
}

/// Percent-encodes the given character and writes it.
#[inline]
fn write_pct_encoded_char<W: fmt::Write>(writer: &mut W, c: char) -> fmt::Result {
    let mut buf = [0_u8; 4];
    let buf = c.encode_utf8(&mut buf);
    buf.bytes().try_for_each(|b| write!(writer, "%{:02X}", b))
}

impl<T: fmt::Display, S: Spec> ProcessAndWrite for &'_ PercentEncoded<T, S> {
    type OutputBorrowed = str;
    #[cfg(feature = "alloc")]
    type OutputOwned = String;
    type ProcessError = core::convert::Infallible;

    #[cfg(feature = "alloc")]
    #[inline]
    fn allocate_and_write(self) -> Result<Self::OutputOwned, TaskError<Self::ProcessError>> {
        let mut s = String::new();
        self.try_append_to_std_string(&mut s)?;
        Ok(s)
    }

    fn write_to_byte_slice(
        self,
        buf: &mut [u8],
    ) -> Result<&Self::OutputBorrowed, TaskError<Self::ProcessError>> {
        /// A wrapper to implement `fmt::Write` for `ByteSliceBuf`.
        struct FmtWritableByteSlice<'a> {
            /// Backend buffer.
            buf: ByteSliceBuf<'a>,
        }
        impl fmt::Write for FmtWritableByteSlice<'_> {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                self.buf.push_str(s).map_err(|_| fmt::Error)
            }
        }

        let mut writer = FmtWritableByteSlice {
            buf: ByteSliceBuf::new(buf),
        };
        write!(writer, "{}", self).expect("[validity] percent encoding should never fail");
        let s = core::str::from_utf8(writer.buf.into_bytes())
            .expect("[validity] percent-encoded characters must always be valid Ascii string.");
        Ok(s)
    }

    #[cfg(feature = "alloc")]
    fn try_append_to_std_string(
        self,
        buf: &mut String,
    ) -> Result<&Self::OutputBorrowed, TaskError<Self::ProcessError>> {
        /// `fmt::Write for String` panics on allocation falilure, so use custom wrapper.
        struct FmtWritableString<'a> {
            /// Backend buffer.
            buf: &'a mut String,
            /// Memory allocation error.
            error: Option<TryReserveError>,
        }
        impl fmt::Write for FmtWritableString<'_> {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                if let Err(e) = self.buf.try_reserve(s.len()) {
                    self.error = Some(e);
                    return Err(fmt::Error);
                }
                self.buf.push_str(s);
                Ok(())
            }
        }

        let mut writer = FmtWritableString { buf, error: None };
        let _result = write!(writer, "{}", self);
        if let Some(e) = writer.error {
            assert!(
                _result.is_err(),
                "[consistency] error should be set iff the memory allocation failed"
            );
            return Err(TaskError::Buffer(e.into()));
        }
        Ok(buf.as_str())
    }
}

#[cfg(feature = "alloc")]
#[cfg(test)]
mod tests {
    use super::*;

    use alloc::string::ToString;

    #[test]
    fn regname() {
        assert_eq!(
            PercentEncoded::<_, UriSpec>::from_reg_name("alpha.\u{03B1}.reg.name").to_string(),
            "alpha.%CE%B1.reg.name"
        );
        assert_eq!(
            PercentEncoded::<_, IriSpec>::from_reg_name("alpha.\u{03B1}.reg.name").to_string(),
            "alpha.\u{03B1}.reg.name"
        );
    }

    #[test]
    fn path_segment() {
        assert_eq!(
            PercentEncoded::<_, UriSpec>::from_path_segment("\u{03B1}/<alpha>?#").to_string(),
            "%CE%B1%2F%3Calpha%3E%3F%23"
        );
        assert_eq!(
            PercentEncoded::<_, IriSpec>::from_path_segment("\u{03B1}/<alpha>?#").to_string(),
            "\u{03B1}%2F%3Calpha%3E%3F%23"
        );
    }

    #[test]
    fn path() {
        assert_eq!(
            PercentEncoded::<_, UriSpec>::from_path("\u{03B1}/<alpha>?#").to_string(),
            "%CE%B1/%3Calpha%3E%3F%23"
        );
        assert_eq!(
            PercentEncoded::<_, IriSpec>::from_path("\u{03B1}/<alpha>?#").to_string(),
            "\u{03B1}/%3Calpha%3E%3F%23"
        );
    }

    #[test]
    fn query() {
        assert_eq!(
            PercentEncoded::<_, UriSpec>::from_query("\u{03B1}/<alpha>?#").to_string(),
            "%CE%B1/%3Calpha%3E?%23"
        );
        assert_eq!(
            PercentEncoded::<_, IriSpec>::from_query("\u{03B1}/<alpha>?#").to_string(),
            "\u{03B1}/%3Calpha%3E?%23"
        );
    }

    #[test]
    fn fragment() {
        assert_eq!(
            PercentEncoded::<_, UriSpec>::from_fragment("\u{03B1}/<alpha>?#").to_string(),
            "%CE%B1/%3Calpha%3E?%23"
        );
        assert_eq!(
            PercentEncoded::<_, IriSpec>::from_fragment("\u{03B1}/<alpha>?#").to_string(),
            "\u{03B1}/%3Calpha%3E?%23"
        );
    }
}
