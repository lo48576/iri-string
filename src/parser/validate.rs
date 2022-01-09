//! Validating parsers for non-trusted (possibly invalid) input.

mod authority;
mod path;

use crate::parser::char;
use crate::parser::str::{
    find_split, find_split2_hole, find_split_hole, satisfy_chars_with_pct_encoded,
};
use crate::spec::Spec;
use crate::validate::Error;

use self::authority::validate_authority;
pub(crate) use self::path::validate_path;
use self::path::{
    validate_path_abempty, validate_path_absolute_authority_absent,
    validate_path_relative_authority_absent,
};

/// Returns `Ok(_)` if the string matches `scheme`.
fn validate_scheme(i: &str) -> Result<(), Error> {
    debug_assert!(!i.is_empty());
    let bytes = i.as_bytes();
    if bytes[0].is_ascii_alphabetic()
        && bytes[1..]
            .iter()
            .all(|&b| b.is_ascii() && char::is_ascii_scheme_continue(b))
    {
        Ok(())
    } else {
        Err(Error::new())
    }
}

/// Returns `Ok(_)` if the string matches `query` or `iquery`.
fn validate_query<S: Spec>(i: &str) -> Result<(), Error> {
    let is_valid =
        satisfy_chars_with_pct_encoded(i, char::is_ascii_frag_query, char::is_nonascii_query::<S>);
    if is_valid {
        Ok(())
    } else {
        Err(Error::new())
    }
}

/// Returns `Ok(_)` if the string matches `authority path-abempty` rule sequence.
fn validate_authority_path_abempty<S: Spec>(i: &str) -> Result<(), Error> {
    let (maybe_authority, maybe_path) = match find_split(i, b'/') {
        Some(v) => v,
        None => (i, ""),
    };
    validate_authority::<S>(maybe_authority)?;
    validate_path_abempty::<S>(maybe_path)
}

/// Returns `Ok(_)` if the string matches `URI`/`IRI` rules.
#[inline]
pub(crate) fn validate_uri<S: Spec>(i: &str) -> Result<(), Error> {
    validate_uri_reference_common::<S>(i, UriReferenceRule::Absolute)
}

/// Returns `Ok(_)` if the string matches `URI-reference`/`IRI-reference` rules.
#[inline]
pub(crate) fn validate_uri_reference<S: Spec>(i: &str) -> Result<(), Error> {
    validate_uri_reference_common::<S>(i, UriReferenceRule::Any)
}

/// Returns `Ok(_)` if the string matches `absolute-URI`/`absolute-IRI` rules.
#[inline]
pub(crate) fn validate_absolute_uri<S: Spec>(i: &str) -> Result<(), Error> {
    validate_uri_reference_common::<S>(i, UriReferenceRule::AbsoluteWithoutFragment)
}

/// Syntax rule for URI/IRI references.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum UriReferenceRule {
    /// `URI` and `IRI`.
    ///
    /// This can have a fragment.
    Absolute,
    /// `absolute-URI` and `absolute-IRI`.
    ///
    /// This cannot have a fragment.
    AbsoluteWithoutFragment,
    /// `URI-reference` and `IRI-reference`.
    ///
    /// This can be relative.
    Any,
}

impl UriReferenceRule {
    /// Returns `true` is the relative reference is allowed.
    #[inline]
    #[must_use]
    fn is_relative_allowed(self) -> bool {
        self == Self::Any
    }

    /// Returns `true` is the fragment part is allowed.
    #[inline]
    #[must_use]
    fn is_fragment_allowed(self) -> bool {
        matches!(self, Self::Absolute | Self::Any)
    }
}

/// Returns `Ok(_)` if the string matches `URI-reference`/`IRI-reference` rules.
fn validate_uri_reference_common<S: Spec>(
    i: &str,
    ref_rule: UriReferenceRule,
) -> Result<(), Error> {
    // Validate `scheme ":"`.
    let (i, _scheme) = match find_split_hole(i, b':') {
        None => {
            if ref_rule.is_relative_allowed() {
                return validate_relative_ref::<S>(i);
            } else {
                return Err(Error::new());
            }
        }
        Some(("", _)) => return Err(Error::new()),
        Some((maybe_scheme, rest)) => {
            validate_scheme(maybe_scheme)?;
            (rest, maybe_scheme)
        }
    };

    // Validate `hier-part`.
    let after_path = match i.strip_prefix("//") {
        Some(i) => {
            let (maybe_authority_path, after_path) = match find_split2_hole(i, b'?', b'#') {
                Some((maybe_authority_path, c, rest)) => (maybe_authority_path, Some((c, rest))),
                None => (i, None),
            };
            validate_authority_path_abempty::<S>(maybe_authority_path)?;
            after_path
        }
        None => {
            let (maybe_path, after_path) = match find_split2_hole(i, b'?', b'#') {
                Some((maybe_path, c, rest)) => (maybe_path, Some((c, rest))),
                None => (i, None),
            };
            // Authority is absent.
            validate_path_absolute_authority_absent::<S>(maybe_path)?;
            after_path
        }
    };

    // Validate `[ "?" query ] [ "#" fragment ]`.
    if let Some((first, rest)) = after_path {
        validate_after_path::<S>(first, rest, ref_rule.is_fragment_allowed())?;
    }
    Ok(())
}

/// Returns `Ok(_)` if the string matches `relative-ref`/`irelative-ref` rules.
pub(crate) fn validate_relative_ref<S: Spec>(i: &str) -> Result<(), Error> {
    // Validate `relative-part`.
    let after_path = match i.strip_prefix("//") {
        Some(i) => {
            let (maybe_authority_path, after_path) = match find_split2_hole(i, b'?', b'#') {
                Some((maybe_authority_path, c, rest)) => (maybe_authority_path, Some((c, rest))),
                None => (i, None),
            };
            validate_authority_path_abempty::<S>(maybe_authority_path)?;
            after_path
        }
        None => {
            let (maybe_path, after_path) = match find_split2_hole(i, b'?', b'#') {
                Some((maybe_path, c, rest)) => (maybe_path, Some((c, rest))),
                None => (i, None),
            };
            // Authority is absent.
            validate_path_relative_authority_absent::<S>(maybe_path)?;
            after_path
        }
    };

    // Validate `[ "?" query ] [ "#" fragment ]`.
    if let Some((first, rest)) = after_path {
        validate_after_path::<S>(first, rest, true)?;
    }
    Ok(())
}

/// Returns `Ok(_)` if the string matches `[ "?" query ] [ "#" fragment ]` (or IRI version).
fn validate_after_path<S: Spec>(first: u8, rest: &str, accept_fragment: bool) -> Result<(), Error> {
    let (maybe_query, maybe_fragment) = if first == b'?' {
        match find_split_hole(rest, b'#') {
            Some(v) => v,
            None => (rest, ""),
        }
    } else {
        debug_assert_eq!(first, b'#');
        ("", rest)
    };
    validate_query::<S>(maybe_query)?;
    if !accept_fragment && !maybe_fragment.is_empty() {
        return Err(Error::new());
    }
    validate_fragment::<S>(maybe_fragment)
}

/// Returns `Ok(_)` if the string matches `fragment`/`ifragment` rules.
pub(crate) fn validate_fragment<S: Spec>(i: &str) -> Result<(), Error> {
    let is_valid = satisfy_chars_with_pct_encoded(
        i,
        char::is_ascii_frag_query,
        char::is_nonascii_fragment::<S>,
    );
    if is_valid {
        Ok(())
    } else {
        Err(Error::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::spec::{IriSpec, UriSpec};

    macro_rules! assert_invalid {
        ($parser:expr, $input:expr $(,)?) => {{
            let input = $input;
            let input: &str = input.as_ref();
            assert!(
                $parser(input).is_err(),
                "parser={:?}, input={:?}",
                stringify!($parser),
                input
            );
        }};
    }

    macro_rules! assert_validate {
        ($parser:expr, $($input:expr),* $(,)?) => {{
            $({
                let input = $input;
                let input: &str = input.as_ref();
                assert!(
                    $parser(input).is_ok(),
                    "parser={:?}, input={:?}",
                    stringify!($parser),
                    input
                );
            })*
        }};
    }

    macro_rules! assert_validate_list {
        ($parser:expr, $($list:expr),* $(,)?) => {{
            $({
                for input in $list {
                    assert_validate!($parser, input);
                }
            })*
        }};
    }

    const OK_URI_LIST: &[&str] = &[
        // RFC 3986 itself.
        "https://tools.ietf.org/html/rfc3986",
        // RFC 3986 section 1.1.2.
        "ftp://ftp.is.co.za/rfc/rfc1808.txt",
        "http://www.ietf.org/rfc/rfc2396.txt",
        "ldap://[2001:db8::7]/c=GB?objectClass?one",
        "mailto:John.Doe@example.com",
        "news:comp.infosystems.www.servers.unix",
        "tel:+1-816-555-1212",
        "telnet://192.0.2.16:80/",
        "urn:oasis:names:specification:docbook:dtd:xml:4.1.2",
        // RFC 3986 section 3.
        "foo://example.com:8042/over/there?name=ferret#nose",
        "urn:example:animal:ferret:nose",
        // RFC 3986 section 3.3.
        "mailto:fred@example.com",
        "foo://info.example.com?fred",
        // RFC 3986 section 5.4.
        "http://a/b/c/d;p?q",
        // RFC 3986 section 5.4.1.
        "g:h",
        "http://a/b/c/g",
        "http://a/b/c/g/",
        "http://a/g",
        "http://g",
        "http://a/b/c/d;p?y",
        "http://a/b/c/g?y",
        "http://a/b/c/d;p?q#s",
        "http://a/b/c/g#s",
        "http://a/b/c/g?y#s",
        "http://a/b/c/;x",
        "http://a/b/c/g;x",
        "http://a/b/c/g;x?y#s",
        "http://a/b/c/d;p?q",
        "http://a/b/c/",
        "http://a/b/",
        "http://a/b/g",
        "http://a/",
        // RFC 3986 section 5.4.2.
        "http://a/b/c/g.",
        "http://a/b/c/.g",
        "http://a/b/c/g..",
        "http://a/b/c/..g",
        "http://a/b/c/g/h",
        "http://a/b/c/h",
        "http://a/b/c/g;x=1/y",
        "http://a/b/c/y",
        "http://a/b/c/g?y/./x",
        "http://a/b/c/g?y/../x",
        "http://a/b/c/g#s/./x",
        "http://a/b/c/g#s/../x",
        // RFC 3986 section 6.2.2.
        "example://a/b/c/%7Bfoo%7D",
        "eXAMPLE://a/./b/../b/%63/%7bfoo%7d",
        // RFC 3986 section 6.2.2.1.
        "HTTP://www.EXAMPLE.com/",
        "http://www.example.com/",
        // RFC 3986 section 6.2.3.
        "http://example.com",
        "http://example.com/",
        "http://example.com:/",
        "http://example.com:80/",
        "http://example.com/?",
        "mailto:Joe@Example.COM",
        "mailto:Joe@example.com",
        // RFC 3986 section 6.2.4.
        "http://example.com/data",
        "http://example.com/data/",
        "ftp://cnn.example.com&story=breaking_news@10.0.0.1/top_story.htm",
        // RFC 3986 section Appendix B.
        "http://www.ics.uci.edu/pub/ietf/uri/#Related",
        // RFC 3986 section Appendix C.
        "http://www.w3.org/Addressing/",
        "ftp://foo.example.com/rfc/",
        "http://www.ics.uci.edu/pub/ietf/uri/historical.html#WARNING",
    ];

    const OK_IRI_LIST: &[&str] = &[
        // RFC 3987 itself.
        "https://tools.ietf.org/html/rfc3987",
        // RFC 3987 section 3.1.
        "http://r\u{E9}sum\u{E9}.example.org",
        "http://xn--rsum-bpad.example.org",
        "http://r%C3%A9sum%C3%A9.example.org",
        "http://www.example.org/red%09ros\u{E9}#red",
        "http://www.example.org/red%09ros%C3%A9#red",
        // RFC 3987 section 3.2.
        "http://example.com/\u{10300}\u{10301}\u{10302}",
        "http://example.com/%F0%90%8C%80%F0%90%8C%81%F0%90%8C%82",
        // RFC 3987 section 3.2.1.
        "http://www.example.org/r%C3%A9sum%C3%A9.html",
        "http://www.example.org/r%E9sum%E9.html",
        "http://www.example.org/D%C3%BCrst",
        "http://www.example.org/D%FCrst",
        "http://www.example.org/D\u{FC}rst",
        "http://xn--99zt52a.example.org/%e2%80%ae",
        "http://xn--99zt52a.example.org/%E2%80%AE",
        "http://\u{7D0D}\u{8C46}.example.org/%E2%80%AE",
        // RFC 3987 section 4.4.
        "http://ab.CDEFGH.ij/kl/mn/op.html",
        "http://ab.CDE.FGH/ij/kl/mn/op.html",
        "http://AB.CD.EF/GH/IJ/KL?MN=OP;QR=ST#UV",
        "http://AB.CD.ef/gh/IJ/KL.html",
        "http://ab.cd.EF/GH/ij/kl.html",
        "http://ab.CD.EF/GH/IJ/kl.html",
        "http://ab.CDE123FGH.ij/kl/mn/op.html",
        "http://ab.cd.ef/GH1/2IJ/KL.html",
        "http://ab.cd.ef/GH%31/%32IJ/KL.html",
        "http://ab.CDEFGH.123/kl/mn/op.html",
        // RFC 3987 section 5.2.
        "http://example.org/ros\u{E9}",
        // RFC 3987 section 5.3.2.
        "example://a/b/c/%7Bfoo%7D/ros\u{E9}",
        "eXAMPLE://a/./b/../b/%63/%7bfoo%7d/ros%C3%A9",
        // RFC 3987 section 5.3.2.1.
        "HTTP://www.EXAMPLE.com/",
        "http://www.example.com/",
        // RFC 3987 section 5.3.2.2.
        "http://www.example.org/r\u{E9}sum\u{E9}.html",
        "http://www.example.org/re\u{301}sume\u{301}.html",
        // RFC 3987 section 5.3.2.3.
        "http://example.org/~user",
        "http://example.org/%7euser",
        "http://example.org/%7Euser",
        // RFC 3987 section 5.3.3.
        "http://example.com",
        "http://example.com/",
        "http://example.com:/",
        "http://example.com:80/",
        //"http://r\u{E9}sum\u{E9}.example.org",  // duplicate
        //"http://xn--rsum-bpad.example.org",  // duplicate
        // RFC 3987 section 5.3.4.
        "http://example.com/data",
        "http://example.com/data/",
        // RFC 3987 section 6.4.
        //"http://www.example.org/r%C3%A9sum%C3%A9.html",  // duplicate
        //"http://www.example.org/r\u{E9}sum\u{E9}.html",  // duplicate
        //"http://www.example.org/r%E9sum%E9.html",  // duplicate
        "http://www.example.org/r%E9sum%E9.xml#r\u{E9}sum\u{E9}",
    ];

    #[test]
    fn test_uri() {
        assert_validate_list!(validate_uri::<UriSpec>, OK_URI_LIST);
    }

    #[test]
    fn test_iri() {
        assert_validate_list!(validate_uri::<IriSpec>, OK_URI_LIST, OK_IRI_LIST);
    }

    #[test]
    fn test_invalid_chars() {
        // Not allowed characters `<` and `>`.
        assert_invalid!(validate_uri::<UriSpec>, "foo://bar/<foo>");
        assert_invalid!(validate_uri::<IriSpec>, "foo://bar/<foo>");
        // U+FFFD Replacement character: Invalid as URI, also invalid as IRI.
        assert_invalid!(validate_uri::<UriSpec>, "foo://bar/\u{FFFD}");
        assert_invalid!(validate_uri::<IriSpec>, "foo://bar/\u{FFFD}");
        // U+3044: Hiragana letter I: Invalid as URI, valid as IRI.
        assert_invalid!(validate_uri::<UriSpec>, "foo://bar/\u{3044}");
        assert_validate!(validate_uri::<IriSpec>, "foo://bar/\u{3044}");
    }

    #[test]
    fn test_invalid_pct_encoded() {
        // Invalid percent encoding.
        assert_invalid!(validate_uri::<UriSpec>, "%zz");
        assert_invalid!(validate_uri::<UriSpec>, "%gg");
        assert_invalid!(validate_uri::<UriSpec>, "%%30%30");
        assert_invalid!(validate_uri::<UriSpec>, "%%300");
        assert_invalid!(validate_uri::<UriSpec>, "%3%30");
        assert_invalid!(validate_uri::<UriSpec>, "%0");
        assert_invalid!(validate_uri::<UriSpec>, "foo://bar/%0");
        assert_invalid!(validate_uri::<UriSpec>, "foo://bar/%0/");
    }
}
