//! Percent encoding normalizer.

use core::cmp::Ordering;
use core::marker::PhantomData;

use crate::parser::char::{is_ascii_unreserved, is_unreserved, is_utf8_byte_continue};
use crate::spec::Spec;

use super::take_xdigits2;

/// Percent-encoding normalized and case normalized string fragment.
///
/// Note that this does not lowercase any ASCII alphabets.
/// If users would like to case normalize ASCII-only `host` component, they are
/// responsible to do check and conversion manually (on the fragments).
#[derive(Debug, Clone)]
pub(crate) enum PctNormalizedFragment<'a> {
    /// Nothing to output.
    None,
    /// Raw character output.
    Char(char),
    /// Percent-encoding triplets.
    PercentEncodingTriplets(&'a str),
}

impl<'a> PctNormalizedFragment<'a> {
    /// Creates a fragment for the given percent-encoding triplets.
    #[inline]
    #[must_use]
    fn pct_enc_triplets(s: &'a str) -> Self {
        Self::PercentEncodingTriplets(s)
    }
}

impl<'a> Iterator for PctNormalizedFragment<'a> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::None => None,
            Self::Char(c) => {
                let c = *c;
                *self = Self::None;
                Some(c)
            }
            Self::PercentEncodingTriplets(s) => {
                if let Some((c, rest)) = take_first_char(s) {
                    *s = rest;
                    // Uppercase hexdigits in percent-encoding triplets.
                    Some(c.to_ascii_uppercase())
                } else {
                    *self = Self::None;
                    None
                }
            }
        }
    }
}

impl core::iter::FusedIterator for PctNormalizedFragment<'_> {}

/// Percent encoding normalizer.
#[derive(Debug, Clone)]
pub(crate) struct PctNormalizedFragments<'a, S> {
    /// The rest of the input.
    rest: &'a str,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<'a, S: Spec> PctNormalizedFragments<'a, S> {
    /// Creates a new normalizing iterator.
    #[inline]
    #[must_use]
    pub(crate) fn new(s: &'a str) -> Self {
        Self {
            rest: s,
            _spec: PhantomData,
        }
    }
}

impl<'a, S: Spec> Iterator for PctNormalizedFragments<'a, S> {
    type Item = PctNormalizedFragment<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let (first_char, rest) = take_first_char(self.rest)?;

        if first_char != '%' {
            self.rest = rest;
            return Some(PctNormalizedFragment::Char(first_char));
        }

        debug_assert_eq!(first_char, '%');
        // Process percent-encoded triplets.
        let (first_decoded_byte, rest) = take_xdigits2(rest);
        if first_decoded_byte.is_ascii() {
            let triplet = &self.rest[..3];
            self.rest = rest;
            if is_ascii_unreserved(first_decoded_byte) {
                // Return the decoded ASCII character.
                return Some(PctNormalizedFragment::Char(char::from(first_decoded_byte)));
            } else {
                // Return the percent-encoded triplet.
                return Some(PctNormalizedFragment::pct_enc_triplets(triplet));
            }
        }

        // Get the expected length of decoded char.
        let expected_char_len = match (first_decoded_byte & 0xf0).cmp(&0b1110_0000) {
            Ordering::Less => 2,
            Ordering::Equal => 3,
            Ordering::Greater => 4,
        };

        // Get continue bytes.
        let c_buf = &mut [first_decoded_byte, 0, 0, 0][..expected_char_len];
        let mut suffix_of_the_decoded = rest;
        for buf_dest in &mut c_buf[1..] {
            let (byte, after_triplet) = match take_first_char(suffix_of_the_decoded) {
                Some(('%', after_percent)) => take_xdigits2(after_percent),
                _ => {
                    // Decoded bytes won't be valid UTF-8 byte sequence.
                    // Return the read percent-encoding triplets without decoding.
                    // Note that all characters in `&c_buf[2..]` (if available)
                    // will be decoded to "continue byte" of UTF-8, so they
                    // cannot be the start of a valid UTF-8 byte sequence.
                    let skip_triplets_len = self.rest.len() - suffix_of_the_decoded.len();
                    let triplets = &self.rest[..skip_triplets_len];
                    self.rest = suffix_of_the_decoded;
                    return Some(PctNormalizedFragment::pct_enc_triplets(triplets));
                }
            };
            if !is_utf8_byte_continue(byte) {
                // The read triplets so far cannot be decoded into a valid UTF-8
                // bytes sequence. However, the current byte can start a valid
                // UTF-8 byte sequence. So, do not take the current triplet away.
                let skip_triplets_len = self.rest.len() - suffix_of_the_decoded.len();
                let triplets = &self.rest[..skip_triplets_len];
                self.rest = suffix_of_the_decoded;
                return Some(PctNormalizedFragment::pct_enc_triplets(triplets));
            }
            *buf_dest = byte;
            suffix_of_the_decoded = after_triplet;
        }

        // All bytes are read. Process the decoded character.
        let triplets = {
            let skip_triplets_len = self.rest.len() - suffix_of_the_decoded.len();
            &self.rest[..skip_triplets_len]
        };
        self.rest = suffix_of_the_decoded;
        let decoded_s = match core::str::from_utf8(c_buf) {
            Ok(s) => s,
            Err(_) => {
                // The read triplets so far cannot be decoded into a valid UTF-8
                // bytes sequence.
                return Some(PctNormalizedFragment::pct_enc_triplets(triplets));
            }
        };
        let decoded_c = decoded_s
            .chars()
            .next()
            .expect("[consistency] the buffer is non-empty");

        if is_unreserved::<S>(decoded_c) {
            // Return the decoded unreserved character.
            Some(PctNormalizedFragment::Char(decoded_c))
        } else {
            // Return the triplets.
            Some(PctNormalizedFragment::pct_enc_triplets(triplets))
        }
    }
}

impl<S: Spec> core::iter::FusedIterator for PctNormalizedFragments<'_, S> {}

/// Splits the given string into the first character and the rest.
///
/// Returns `(first_char, first_char_len, rest_str)`.
#[must_use]
fn take_first_char(s: &str) -> Option<(char, &str)> {
    let mut chars = s.chars();
    let c = chars.next()?;
    let rest = chars.as_str();
    Some((c, rest))
}
