//! Raw IRI strings manipulation.
//!
//! Note that functions in this module may operates on raw `&str` types.
//! It is caller's responsilibility to guarantee that the given string satisfies the precondition.

#[cfg(feature = "alloc")]
use alloc::string::String;

/// Splits the string into the prefix and the fragment part.
///
/// A leading `#` character is truncated if the fragment part exists.
#[inline]
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
    match iri.find('#') {
        Some(colon_pos) => (&iri[..colon_pos], Some(&iri[(colon_pos + 1)..])),
        None => (iri, None),
    }
}

/// Returns the fragment part of the given IRI.
///
/// A leading `#` character of the fragment is truncated.
#[inline]
pub(crate) fn extract_fragment(iri: &str) -> Option<&str> {
    split_fragment(iri).1
}

/// Sets the fragment part to the given string.
///
/// Removes fragment part (and following `#` character) if `None` is given.
#[cfg(feature = "alloc")]
pub(crate) fn set_fragment(s: &mut String, fragment: Option<&str>) {
    remove_fragment(s);
    if let Some(fragment) = fragment {
        s.reserve(fragment.len() + 1);
        s.push('#');
        s.push_str(fragment);
    }
}

/// Removes the fragment part from the string.
#[cfg(feature = "alloc")]
#[inline]
pub(crate) fn remove_fragment(s: &mut String) {
    if let Some(colon_pos) = s.find('#') {
        s.truncate(colon_pos);
    }
}

/// Splits the string into the prefix and the fragment part.
///
/// A leading `#` character is truncated if the fragment part exists.
#[cfg(feature = "alloc")]
pub(crate) fn split_fragment_owned(mut s: String) -> (String, Option<String>) {
    let (prefix, fragment) = split_fragment(&s);
    if fragment.is_none() {
        // The string has no fragment part.
        return (s, None);
    }
    let prefix_len = prefix.len();

    // `+ 1` is for leading `#` character.
    let fragment = s.split_off(prefix_len + 1);
    // Current `s` contains a trailing `#` character, which should be removed.
    {
        // Remove a trailing `#`.
        let hash = s.pop();
        assert_eq!(hash, Some('#'));
    }
    assert_eq!(s.len(), prefix_len);

    (s, Some(fragment))
}
