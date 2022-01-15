//! Fast parsers for trusted (already validated) input.
//!
//! Using this in wrong way will lead to unexpected wrong result.

use core::marker::PhantomData;
use core::num::NonZeroUsize;

use crate::components::RiReferenceComponents;
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
