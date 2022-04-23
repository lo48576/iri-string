//! Fast parsers for trusted (already validated) input.
//!
//! Using this in wrong way will lead to unexpected wrong result.

pub(crate) mod authority;

use core::cmp::Ordering;
use core::marker::PhantomData;
use core::num::NonZeroUsize;

use crate::components::RiReferenceComponents;
use crate::normalize::normalize_case_and_pct_encodings;
use crate::parser::str::{find_split2, find_split3, find_split4_hole, find_split_hole};
use crate::spec::Spec;
use crate::types::RiReferenceStr;

/// Eats a `scheme` and a following colon, and returns the rest and the scheme.
///
/// Returns `(rest, scheme)`.
///
/// This should be called at the head of an absolute IRIs/URIs.
#[must_use]
fn scheme_colon(i: &str) -> (&str, &str) {
    let (scheme, rest) =
        find_split_hole(i, b':').expect("[precondition] absolute IRIs must have `scheme` part");
    (rest, scheme)
}

/// Eats a `scheme` and a following colon if available, and returns the rest and the scheme.
///
/// This should be called at the head of an `IRI-reference` or similar.
#[must_use]
fn scheme_colon_opt(i: &str) -> (&str, Option<&str>) {
    match find_split4_hole(i, b':', b'/', b'?', b'#') {
        Some((scheme, b':', rest)) => (rest, Some(scheme)),
        _ => (i, None),
    }
}

/// Eats double slash and the following authority if available, and returns the authority.
///
/// This should be called at the head of an `IRI-reference`, or at the result of `scheme_colon`.
#[must_use]
fn slash_slash_authority_opt(i: &str) -> (&str, Option<&str>) {
    let s = match i.strip_prefix("//") {
        Some(rest) => rest,
        None => return (i, None),
    };
    // `i` might match `path-abempty` (which can start with `//`), but it is not
    // allowed as `relative-part`, so no need to care `path-abempty` rule here.
    // A slash, question mark, and hash character won't appear in `authority`.
    match find_split3(s, b'/', b'?', b'#') {
        Some((authority, rest)) => (rest, Some(authority)),
        None => ("", Some(s)),
    }
}

/// Eats a string until the query, and returns that part (excluding `?` for the query).
#[must_use]
fn until_query(i: &str) -> (&str, &str) {
    // `?` won't appear before the query part.
    match find_split2(i, b'?', b'#') {
        Some((before_query, rest)) => (rest, before_query),
        None => ("", i),
    }
}

/// Decomposes query and fragment, if available.
///
/// The string must starts with `?`, or `#`, or be empty.
#[must_use]
fn decompose_query_and_fragment(i: &str) -> (Option<&str>, Option<&str>) {
    match i.as_bytes().get(0).copied() {
        None => (None, None),
        Some(b'?') => {
            let rest = &i[1..];
            match find_split_hole(rest, b'#') {
                Some((query, fragment)) => (Some(query), Some(fragment)),
                None => (Some(rest), None),
            }
        }
        Some(c) => {
            debug_assert_eq!(c, b'#');
            (None, Some(&i[1..]))
        }
    }
}

/// Decomposes the given valid `IRI-reference`.
#[must_use]
pub(crate) fn decompose_iri_reference<S: Spec>(
    i: &RiReferenceStr<S>,
) -> RiReferenceComponents<'_, S> {
    ///// Inner function to avoid unnecessary monomorphizations on `S`.
    //fn decompose(i: &str) -> (Option<&str>, Option<&str>, &str, Option<&str>, Option<&str>) {
    //    let (i, scheme) = scheme_colon_opt(i);
    //    let (i, authority) = slash_slash_authority_opt(i);
    //    let (i, path) = until_query(i);
    //    let (query, fragment) = decompose_query_and_fragment(i);
    //    (scheme, authority, path, query, fragment)
    //}

    /// Inner function to avoid unnecessary monomorphizations on `S`.
    fn decompose(
        i: &str,
    ) -> (
        Option<NonZeroUsize>,
        Option<NonZeroUsize>,
        Option<NonZeroUsize>,
        Option<NonZeroUsize>,
    ) {
        let len = i.len();
        let (i, scheme) = scheme_colon_opt(i);
        let scheme_end = scheme.and_then(|s| NonZeroUsize::new(s.len()));
        let authority_start = len - i.len() + 2;
        let (i, authority) = slash_slash_authority_opt(i);
        let authority_end = authority.and_then(|s| NonZeroUsize::new(authority_start + s.len()));
        let (i, _path) = until_query(i);
        let next_of_path = len - i.len() + 1;
        let (query, fragment) = decompose_query_and_fragment(i);
        let (query_start, fragment_start) = match (query, fragment) {
            (Some(query), Some(_fragment)) => (
                NonZeroUsize::new(next_of_path),
                NonZeroUsize::new(next_of_path + query.len() + 1),
            ),
            (Some(_query), None) => (NonZeroUsize::new(next_of_path), None),
            (None, Some(_fragment)) => (None, NonZeroUsize::new(next_of_path)),
            (None, None) => (None, None),
        };
        (scheme_end, authority_end, query_start, fragment_start)
    }

    let (scheme_end, authority_end, query_start, fragment_start) = decompose(i.as_str());
    RiReferenceComponents {
        iri: i,
        scheme_end,
        authority_end,
        query_start,
        fragment_start,
        _spec: PhantomData,
    }
}

/// Extracts `scheme` part from an IRI reference.
///
/// # Precondition
///
/// The given string must be a valid IRI reference.
#[inline]
#[must_use]
pub(crate) fn extract_scheme(i: &str) -> Option<&str> {
    scheme_colon_opt(i).1
}

/// Extracts `scheme` part from an absolute IRI.
///
/// # Precondition
///
/// The given string must be a valid absolute IRI.
#[inline]
#[must_use]
pub(crate) fn extract_scheme_absolute(i: &str) -> &str {
    scheme_colon(i).1
}

/// Extracts `authority` part from an IRI reference.
///
/// # Precondition
///
/// The given string must be a valid IRI reference.
#[inline]
#[must_use]
pub(crate) fn extract_authority(i: &str) -> Option<&str> {
    let (i, _scheme) = scheme_colon_opt(i);
    slash_slash_authority_opt(i).1
}

/// Extracts `authority` part from an absolute IRI.
///
/// # Precondition
///
/// The given string must be a valid absolute IRI.
#[inline]
#[must_use]
pub(crate) fn extract_authority_absolute(i: &str) -> Option<&str> {
    let (i, _scheme) = scheme_colon(i);
    slash_slash_authority_opt(i).1
}

/// Extracts `authority` part from a relative IRI.
///
/// # Precondition
///
/// The given string must be a valid relative IRI.
#[inline]
#[must_use]
pub(crate) fn extract_authority_relative(i: &str) -> Option<&str> {
    slash_slash_authority_opt(i).1
}

/// Extracts `path` part from an IRI reference.
///
/// # Precondition
///
/// The given string must be a valid IRI reference.
#[inline]
#[must_use]
pub(crate) fn extract_path(i: &str) -> &str {
    let (i, _scheme) = scheme_colon_opt(i);
    let (i, _authority) = slash_slash_authority_opt(i);
    until_query(i).1
}

/// Extracts `path` part from an absolute IRI.
///
/// # Precondition
///
/// The given string must be a valid absolute IRI.
#[inline]
#[must_use]
pub(crate) fn extract_path_absolute(i: &str) -> &str {
    let (i, _scheme) = scheme_colon(i);
    let (i, _authority) = slash_slash_authority_opt(i);
    until_query(i).1
}

/// Extracts `path` part from a relative IRI.
///
/// # Precondition
///
/// The given string must be a valid relative IRI.
#[inline]
#[must_use]
pub(crate) fn extract_path_relative(i: &str) -> &str {
    let (i, _authority) = slash_slash_authority_opt(i);
    until_query(i).1
}

/// Extracts `query` part from an IRI reference.
///
/// # Precondition
///
/// The given string must be a valid IRI reference.
#[inline]
#[must_use]
pub(crate) fn extract_query(i: &str) -> Option<&str> {
    let (i, _before_query) = until_query(i);
    decompose_query_and_fragment(i).0
}

/// Extracts `query` part from an `absolute-IRI` string.
///
/// # Precondition
///
/// The given string must be a valid `absolute-IRI` string.
#[must_use]
pub(crate) fn extract_query_absolute_iri(i: &str) -> Option<&str> {
    let (i, _before_query) = until_query(i);
    if i.is_empty() {
        None
    } else {
        debug_assert_eq!(
            i.as_bytes().get(0),
            Some(&b'?'),
            "`absolute-IRI` string must not have `fragment part"
        );
        Some(&i[1..])
    }
}

/// Splits an IRI string into the prefix and the fragment part.
///
/// A leading `#` character is truncated if the fragment part exists.
///
/// # Precondition
///
/// The given string must be a valid IRI reference.
#[inline]
#[must_use]
pub(crate) fn split_fragment(iri: &str) -> (&str, Option<&str>) {
    // It is completely OK to find the first `#` character from valid IRI to get fragment part,
    // because the spec says that there are no `#` characters before the fragment part.
    //
    // > ```
    // > scheme      = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )
    // > ```
    // >
    // > --- [RFC 3986, section 3.1. Scheme](https://tools.ietf.org/html/rfc3986#section-3.1)
    //
    // > The authority component is preceded by a double slash ("//") and is terminated by the
    // > next slash ("/"), question mark ("?"), or number sign ("#") character, or by the end
    // > of the URI.
    // >
    // > --- [RFC 3986, section 3.2. Authority](https://tools.ietf.org/html/rfc3986#section-3.2)
    //
    // > The path is terminated by the first question mark ("?") or number sign ("#")
    // > character, or by the end of the URI.
    // >
    // > --- [RFC 3986, section 3.3. Path](https://tools.ietf.org/html/rfc3986#section-3.3)
    //
    // > The query component is indicated by the first question mark ("?") character and
    // > terminated by a number sign ("#") character or by the end of the URI.
    // >
    // > --- [RFC 3986, section 3.4. Query](https://tools.ietf.org/html/rfc3986#section-3.4)
    match find_split_hole(iri, b'#') {
        Some((prefix, fragment)) => (prefix, Some(fragment)),
        None => (iri, None),
    }
}

/// Returns the fragment part of the given IRI.
///
/// A leading `#` character of the fragment is truncated.
#[inline]
#[must_use]
pub(crate) fn extract_fragment(iri: &str) -> Option<&str> {
    split_fragment(iri).1
}

/// Returns `Ok(_)` if the string is normalized.
///
/// If this function returns `true`, normalization input and output will be identical.
///
/// In this function, "normalized" means that any of the normalization below
/// won't change the input on normalization:
///
/// * syntax-based normalization,
/// * case normalization,
/// * percent-encoding normalization, and
/// * path segment normalizaiton.
///
/// Note that scheme-based normalization is not considered.
#[must_use]
pub(crate) fn is_normalized<S: Spec>(i: &str) -> bool {
    let (i, scheme) = scheme_colon(i);
    let (after_authority, authority) = slash_slash_authority_opt(i);
    let (_after_path, path) = until_query(after_authority);

    // Syntax-based normalization: uppercase chars in `scheme` should be
    // converted to lowercase.
    if scheme.bytes().any(|b| b.is_ascii_uppercase()) {
        return false;
    }

    // Case normalization: ASCII alphabets in US-ASCII only `host` should be
    // normalized to lowercase.
    // Case normalization: ASCII alphabets in percent-encoding triplet should be
    // normalized to uppercase.
    // Percent-encoding normalization: unresreved characters should be decoded
    // in `userinfo`, `host`, `path`, `query`, and `fragments`.
    // Path segment normalization: the path should not have dot segments (`.`
    // and/or `..`).
    //
    // Note that `authority` can have percent-encoded `userinfo`.
    if let Some(authority) = authority {
        let authority_components = authority::decompose_authority(authority);

        // Check `host`.
        let host = authority_components.host();
        let host_is_normalized = if is_ascii_only_host(host) {
            // Note that percent-encoding triplets in US-ASCII only
            // host should be uppercase. For example, `plus%2bplus`
            // is wrong and `plus%2Bplus` is correct.
            let normalized_host_chars =
                normalize_case_and_pct_encodings::<S>(host).scan(3, |after_percent, c| {
                    // after_percent: 0 is `%`, 1 is upper hexdigit, 2 is lower
                    // hexdigit, and 3 is plain character.
                    Some(if c == '%' {
                        *after_percent = 0;
                        c
                    } else if *after_percent < 2 {
                        *after_percent += 1;
                        c
                    } else {
                        *after_percent = 3;
                        c.to_ascii_lowercase()
                    })
                });
            normalized_host_chars.eq(host.chars())
        } else {
            // If the host is not ASCII-only, conversion to lowercase is not performed.
            normalize_case_and_pct_encodings::<S>(host).eq(host.chars())
        };
        if !host_is_normalized {
            return false;
        }

        // Check pencent encodings in `userinfo`.
        if let Some(userinfo) = authority_components.userinfo() {
            if !userinfo
                .chars()
                .eq(normalize_case_and_pct_encodings::<S>(userinfo))
            {
                return false;
            }
        }
    }

    // Check `path`.
    // Syntax normalization:
    // Percent-encoding normalization: unresreved characters should be decoded
    // in `path`, `query`, and `fragments`.

    // Syntax-based normalization: Dot segments should be removed.
    // Note that we don't have to care `%2e` and `%2E` since `.` is unreserved
    // and they will be decoded if not normalized.
    if path.split('/').any(|segment| matches!(segment, "." | "..")) {
        return false;
    }
    normalize_case_and_pct_encodings::<S>(after_authority).eq(after_authority.chars())
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
pub(crate) fn take_xdigits2(s: &str) -> (u8, &str) {
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
#[must_use]
pub(crate) fn is_ascii_only_host(mut host: &str) -> bool {
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
