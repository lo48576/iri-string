//! Tests for validators.

#[cfg(not(test))]
compile_error!("`tests` module should be enable only when `cfg(tests)`");

use core::fmt::Write;

#[cfg(feature = "alloc")]
use alloc::string::ToString;

use crate::spec::{IriSpec, Spec, UriSpec};
use crate::tests::{Components, WritableByteBuffer};
use crate::types::{
    IriAbsoluteStr, IriReferenceStr, IriRelativeStr, IriStr, RiReferenceStr, UriAbsoluteStr,
    UriReferenceStr, UriRelativeStr, UriStr,
};

macro_rules! components {
    ($(($serialized:expr, $scheme:expr, $authority:expr, $path:expr, $query:expr, $fragment:expr)),* $(,)?) => {
        &[
            $(
                (
                    $serialized,
                    Components::new(
                        {$scheme}.into(),
                        {$authority}.into(),
                        {$path}.into(),
                        {$query}.into(),
                        {$fragment}.into(),
                    ),
                )
            ),*
        ]
    }
}

fn compose_roundtrip<S: Spec>(components_list: &[(&str, Components)]) {
    #[cfg(feature = "alloc")]
    {
        for (expected_str, components) in components_list {
            let serialized = components.to_string();
            assert_eq!(serialized, *expected_str);
            let parsed =
                RiReferenceStr::<S>::new(&serialized).expect("the test case should be valid");
            let decomposed = Components::from(parsed);

            assert_eq!(
                components, decomposed,
                "serialized={:?}, parsed={:?}",
                serialized, parsed
            );
        }
    }

    {
        let buf = &mut [0_u8; 256];
        let mut buf = WritableByteBuffer::new(buf);
        for (expected_str, components) in components_list {
            buf.clear();
            write!(&mut buf, "{}", components).expect("failed to serialize");
            let serialized = buf.as_str();
            assert_eq!(serialized, *expected_str);
            let parsed =
                RiReferenceStr::<S>::new(serialized).expect("the test case should be valid");
            let decomposed = Components::from(parsed);

            assert_eq!(
                components, decomposed,
                "serialized={:?}, parsed={:?}",
                serialized, parsed
            );
        }
    }
}

fn assert_convertible<T: ?Sized>(source: &str)
where
    T: PartialEq<str> + core::fmt::Debug,
    for<'a> &'a T: TryFrom<&'a str>,
    for<'a> <&'a T as TryFrom<&'a str>>::Error: core::fmt::Debug,
{
    match <&T>::try_from(source) {
        Ok(parsed) => assert_eq!(parsed, source),
        Err(e) => panic!("should be convertible: source={:?}: {:?}", source, e),
    }
}

fn assert_non_convertible<T: ?Sized>(source: &str)
where
    T: PartialEq<str> + core::fmt::Debug,
    for<'a> &'a T: TryFrom<&'a str>,
    for<'a> <&'a T as TryFrom<&'a str>>::Error: core::fmt::Debug,
{
    if let Ok(parsed) = <&T>::try_from(source) {
        panic!(
            "should not be convertible: source={:?}, parsed={:?}",
            source, parsed
        );
    }
}

mod decompose {
    use super::*;

    #[test]
    fn test_combinations() {
        let components = components!(
            ("", None, None, "", None, None),
            ("#fragment", None, None, "", None, "fragment"),
            ("?query", None, None, "", "query", None),
            ("?query#fragment", None, None, "", "query", "fragment"),
            ("path", None, None, "path", None, None),
            ("path#fragment", None, None, "path", None, "fragment"),
            ("path?query", None, None, "path", "query", None),
            (
                "path?query#fragment",
                None,
                None,
                "path",
                "query",
                "fragment"
            ),
            ("/path", None, None, "/path", None, None),
            ("/path#fragment", None, None, "/path", None, "fragment"),
            ("/path?query", None, None, "/path", "query", None),
            (
                "/path?query#fragment",
                None,
                None,
                "/path",
                "query",
                "fragment"
            ),
            ("//authority", None, "authority", "", None, None),
            (
                "//authority#fragment",
                None,
                "authority",
                "",
                None,
                "fragment"
            ),
            ("//authority?query", None, "authority", "", "query", None),
            (
                "//authority?query#fragment",
                None,
                "authority",
                "",
                "query",
                "fragment"
            ),
            ("//authority/path", None, "authority", "/path", None, None),
            (
                "//authority/path#fragment",
                None,
                "authority",
                "/path",
                None,
                "fragment"
            ),
            (
                "//authority/path?query",
                None,
                "authority",
                "/path",
                "query",
                None
            ),
            (
                "//authority/path?query#fragment",
                None,
                "authority",
                "/path",
                "query",
                "fragment"
            ),
            ("scheme:", "scheme", None, "", None, None),
            ("scheme:#fragment", "scheme", None, "", None, "fragment"),
            ("scheme:?query", "scheme", None, "", "query", None),
            (
                "scheme:?query#fragment",
                "scheme",
                None,
                "",
                "query",
                "fragment"
            ),
            ("scheme:path", "scheme", None, "path", None, None),
            (
                "scheme:path#fragment",
                "scheme",
                None,
                "path",
                None,
                "fragment"
            ),
            ("scheme:path?query", "scheme", None, "path", "query", None),
            (
                "scheme:path?query#fragment",
                "scheme",
                None,
                "path",
                "query",
                "fragment"
            ),
            ("scheme:/path", "scheme", None, "/path", None, None),
            (
                "scheme:/path#fragment",
                "scheme",
                None,
                "/path",
                None,
                "fragment"
            ),
            ("scheme:/path?query", "scheme", None, "/path", "query", None),
            (
                "scheme:/path?query#fragment",
                "scheme",
                None,
                "/path",
                "query",
                "fragment"
            ),
            ("scheme://authority", "scheme", "authority", "", None, None),
            (
                "scheme://authority#fragment",
                "scheme",
                "authority",
                "",
                None,
                "fragment"
            ),
            (
                "scheme://authority?query",
                "scheme",
                "authority",
                "",
                "query",
                None
            ),
            (
                "scheme://authority?query#fragment",
                "scheme",
                "authority",
                "",
                "query",
                "fragment"
            ),
            (
                "scheme://authority/path",
                "scheme",
                "authority",
                "/path",
                None,
                None
            ),
            (
                "scheme://authority/path#fragment",
                "scheme",
                "authority",
                "/path",
                None,
                "fragment"
            ),
            (
                "scheme://authority/path?query",
                "scheme",
                "authority",
                "/path",
                "query",
                None
            ),
            (
                "scheme://authority/path?query#fragment",
                "scheme",
                "authority",
                "/path",
                "query",
                "fragment"
            ),
        );
        compose_roundtrip::<UriSpec>(components);
        compose_roundtrip::<IriSpec>(components);
    }

    #[test]
    fn test_absolute_paths_slash_only() {
        let components = components!(
            ("scheme:", "scheme", None, "", None, None),
            ("scheme:/", "scheme", None, "/", None, None),
            ("scheme://", "scheme", "", "", None, None),
            ("scheme:///", "scheme", "", "/", None, None),
            ("scheme:////", "scheme", "", "//", None, None),
            ("scheme://///", "scheme", "", "///", None, None),
        );
        compose_roundtrip::<UriSpec>(components);
        compose_roundtrip::<IriSpec>(components);
    }

    #[test]
    fn test_relative_paths_slash_only() {
        let components = components!(
            ("", None, None, "", None, None),
            ("/", None, None, "/", None, None),
            ("//", None, "", "", None, None),
            ("///", None, "", "/", None, None),
            ("////", None, "", "//", None, None),
            ("/////", None, "", "///", None, None),
        );
        compose_roundtrip::<UriSpec>(components);
        compose_roundtrip::<IriSpec>(components);
    }

    #[test]
    fn test_hosts() {
        let components = components!(
            // IPv4.
            ("//192.0.2.0", None, "192.0.2.0", "", None, None),
            ("//192.0.2.0:80", None, "192.0.2.0:80", "", None, None),
            ("//198.51.100.99", None, "198.51.100.99", "", None, None),
            (
                "//198.51.100.99:80",
                None,
                "198.51.100.99:80",
                "",
                None,
                None
            ),
            ("//203.0.113.255", None, "203.0.113.255", "", None, None),
            (
                "//203.0.113.255:80",
                None,
                "203.0.113.255:80",
                "",
                None,
                None
            ),
            // IPv6.
            ("//[2001:db8::]", None, "[2001:db8::]", "", None, None),
            ("//[2001:db8::]:80", None, "[2001:db8::]:80", "", None, None),
            ("//[2001:0db8::]", None, "[2001:0db8::]", "", None, None),
            (
                "//[2001:0db8::]:80",
                None,
                "[2001:0db8::]:80",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0:0:0:0:0:ffff]",
                None,
                "[2001:0db8:0:0:0:0:0:ffff]",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0:0:0:0:0:ffff]:80",
                None,
                "[2001:0db8:0:0:0:0:0:ffff]:80",
                "",
                None,
                None
            ),
            (
                "//[2001:0DB8:0:0:0:A:BCDE:FFFF]",
                None,
                "[2001:0DB8:0:0:0:A:BCDE:FFFF]",
                "",
                None,
                None
            ),
            (
                "//[2001:0DB8:0:0:0:A:BCDE:FFFF]:80",
                None,
                "[2001:0DB8:0:0:0:A:BCDE:FFFF]:80",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8::89ab:cdef:89AB:CDEF]:80",
                None,
                "[2001:0db8::89ab:cdef:89AB:CDEF]:80",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0:0:0:0::1]",
                None,
                "[2001:0db8:0:0:0:0::1]",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0:0:0:0::1]:80",
                None,
                "[2001:0db8:0:0:0:0::1]:80",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0:0:0::1]",
                None,
                "[2001:0db8:0:0:0::1]",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0:0:0::1]:80",
                None,
                "[2001:0db8:0:0:0::1]:80",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0:0::1]",
                None,
                "[2001:0db8:0:0::1]",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0:0::1]:80",
                None,
                "[2001:0db8:0:0::1]:80",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0::1]",
                None,
                "[2001:0db8:0::1]",
                "",
                None,
                None
            ),
            (
                "//[2001:0db8:0::1]:80",
                None,
                "[2001:0db8:0::1]:80",
                "",
                None,
                None
            ),
            ("//[2001:0db8::1]", None, "[2001:0db8::1]", "", None, None),
            (
                "//[2001:0db8::1]:80",
                None,
                "[2001:0db8::1]:80",
                "",
                None,
                None
            ),
            // IPvFuture.
            (
                "//[v9999.this-is-future-version-of-ip-address:::::::::]",
                None,
                "[v9999.this-is-future-version-of-ip-address:::::::::]",
                "",
                None,
                None
            ),
            (
                "//[v9999.this-is-future-version-of-ip-address:::::::::]:80",
                None,
                "[v9999.this-is-future-version-of-ip-address:::::::::]:80",
                "",
                None,
                None
            ),
        );
        compose_roundtrip::<UriSpec>(components);
        compose_roundtrip::<IriSpec>(components);
    }

    #[test]
    fn test_abnormal_port() {
        // `port` is defined as `*DIGIT` in RFC 3986.
        // (See <https://datatracker.ietf.org/doc/html/rfc3986#section-3.2.3>.)
        // This means that the port can be empty or quite large.
        let components = components!(
            // No port.
            ("//localhost", None, "localhost", "", None, None),
            // Empty port.
            ("//localhost:", None, "localhost:", "", None, None),
            // Too large port.
            (
                "//localhost:999999999",
                None,
                "localhost:999999999",
                "",
                None,
                None
            ),
        );
        compose_roundtrip::<UriSpec>(components);
        compose_roundtrip::<IriSpec>(components);
    }
}

mod validate {
    use super::*;

    #[test]
    fn rfc3986_uris_absolute_without_fragment() {
        const URIS: &[&str] = &[
            // RFC 3986 itself.
            "https://tools.ietf.org/html/rfc3986",
            "https://datatracker.ietf.org/doc/html/rfc3986",
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
            "http://a/b/c/;x",
            "http://a/b/c/g;x",
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
            // RFC 3986 section Appendix C.
            "http://www.w3.org/Addressing/",
            "ftp://foo.example.com/rfc/",
            // RFC 3987 itself.
            "https://tools.ietf.org/html/rfc3987",
            "https://datatracker.ietf.org/doc/html/rfc3987",
            // RFC 3987 section 3.1.
            "http://xn--rsum-bpad.example.org",
            "http://r%C3%A9sum%C3%A9.example.org",
            // RFC 3987 section 3.2.
            "http://example.com/%F0%90%8C%80%F0%90%8C%81%F0%90%8C%82",
            // RFC 3987 section 3.2.1.
            "http://www.example.org/r%C3%A9sum%C3%A9.html",
            "http://www.example.org/r%E9sum%E9.html",
            "http://www.example.org/D%C3%BCrst",
            "http://www.example.org/D%FCrst",
            "http://xn--99zt52a.example.org/%e2%80%ae",
            "http://xn--99zt52a.example.org/%E2%80%AE",
            // RFC 3987 section 4.4.
            "http://ab.CDEFGH.ij/kl/mn/op.html",
            "http://ab.CDE.FGH/ij/kl/mn/op.html",
            "http://AB.CD.ef/gh/IJ/KL.html",
            "http://ab.cd.EF/GH/ij/kl.html",
            "http://ab.CD.EF/GH/IJ/kl.html",
            "http://ab.CDE123FGH.ij/kl/mn/op.html",
            "http://ab.cd.ef/GH1/2IJ/KL.html",
            "http://ab.cd.ef/GH%31/%32IJ/KL.html",
            "http://ab.CDEFGH.123/kl/mn/op.html",
            // RFC 3987 section 5.3.2.
            "eXAMPLE://a/./b/../b/%63/%7bfoo%7d/ros%C3%A9",
            // RFC 3987 section 5.3.2.1.
            "HTTP://www.EXAMPLE.com/",
            "http://www.example.com/",
            // RFC 3987 section 5.3.2.3.
            "http://example.org/~user",
            "http://example.org/%7euser",
            "http://example.org/%7Euser",
            // RFC 3987 section 5.3.3.
            "http://example.com",
            "http://example.com/",
            "http://example.com:/",
            "http://example.com:80/",
            //"http://xn--rsum-bpad.example.org",  // duplicate
            // RFC 3987 section 5.3.4.
            "http://example.com/data",
            "http://example.com/data/",
            // RFC 3987 section 6.4.
            //"http://www.example.org/r%C3%A9sum%C3%A9.html",  // duplicate
            //"http://www.example.org/r%E9sum%E9.html",  // duplicate
        ];
        for uri in URIS {
            assert_convertible::<IriReferenceStr>(uri);
            assert_convertible::<UriReferenceStr>(uri);
            assert_convertible::<IriStr>(uri);
            assert_convertible::<UriStr>(uri);
            assert_convertible::<IriAbsoluteStr>(uri);
            assert_convertible::<UriAbsoluteStr>(uri);
            assert_non_convertible::<IriRelativeStr>(uri);
            assert_non_convertible::<UriRelativeStr>(uri);
        }
    }

    #[test]
    fn rfc3986_uris_absolute_with_fragment() {
        const URIS: &[&str] = &[
            // RFC 3986 section 3.
            "foo://example.com:8042/over/there?name=ferret#nose",
            // RFC 3986 section 5.4.1.
            "http://a/b/c/d;p?q#s",
            "http://a/b/c/g#s",
            "http://a/b/c/g?y#s",
            "http://a/b/c/g;x?y#s",
            // RFC 3986 section 5.4.2.
            "http://a/b/c/g#s/./x",
            "http://a/b/c/g#s/../x",
            // RFC 3986 section Appendix B.
            "http://www.ics.uci.edu/pub/ietf/uri/#Related",
            // RFC 3986 section Appendix C.
            "http://www.ics.uci.edu/pub/ietf/uri/historical.html#WARNING",
            // RFC 3987 section 3.1.
            "http://www.example.org/red%09ros%C3%A9#red",
            // RFC 3987 section 4.4.
            "http://AB.CD.EF/GH/IJ/KL?MN=OP;QR=ST#UV",
        ];
        for uri in URIS {
            assert_convertible::<IriReferenceStr>(uri);
            assert_convertible::<UriReferenceStr>(uri);
            assert_convertible::<IriStr>(uri);
            assert_convertible::<UriStr>(uri);
            assert_non_convertible::<IriAbsoluteStr>(uri);
            assert_non_convertible::<UriAbsoluteStr>(uri);
            assert_non_convertible::<IriRelativeStr>(uri);
            assert_non_convertible::<UriRelativeStr>(uri);
        }
    }

    #[test]
    fn rfc3986_uris_relative() {
        const URIS: &[&str] = &[
            // RFC 3986 section 5.4.1.
            "g",
            "./g",
            "g/",
            "/g",
            "//g",
            "?y",
            "g?y",
            "#s",
            "g#s",
            "g?y#s",
            ";x",
            "g;x",
            "g;x?y#s",
            "",
            ".",
            "./",
            "..",
            "../",
            "../g",
            "../..",
            "../../",
            "../../g",
            // RFC 3986 section 5.4.2.
            "/./g",
            "/../g",
            "g.",
            ".g",
            "g..",
            "..g",
            "./../g",
            "./g/.",
            "g/./h",
            "g/../h",
            "g;x=1/./y",
            "g;x=1/../y",
            "g?y/./x",
            "g?y/../x",
            "g#s/./x",
            "g#s/../x",
        ];
        for uri in URIS {
            assert_convertible::<IriReferenceStr>(uri);
            assert_convertible::<UriReferenceStr>(uri);
            assert_non_convertible::<IriStr>(uri);
            assert_non_convertible::<UriStr>(uri);
            assert_non_convertible::<IriAbsoluteStr>(uri);
            assert_non_convertible::<UriAbsoluteStr>(uri);
            assert_convertible::<IriRelativeStr>(uri);
            assert_convertible::<UriRelativeStr>(uri);
        }
    }

    #[test]
    fn rfc3987_iris_absolute_without_fragment() {
        const URIS: &[&str] = &[
            // RFC 3987 section 3.1.
            "http://r\u{E9}sum\u{E9}.example.org",
            // RFC 3987 section 3.2.
            "http://example.com/\u{10300}\u{10301}\u{10302}",
            "http://www.example.org/D\u{FC}rst",
            "http://\u{7D0D}\u{8C46}.example.org/%E2%80%AE",
            // RFC 3987 section 5.2.
            "http://example.org/ros\u{E9}",
            // RFC 3987 section 5.3.2.
            "example://a/b/c/%7Bfoo%7D/ros\u{E9}",
            // RFC 3987 section 5.3.2.2.
            "http://www.example.org/r\u{E9}sum\u{E9}.html",
            "http://www.example.org/re\u{301}sume\u{301}.html",
            // RFC 3987 section 5.3.3.
            //"http://r\u{E9}sum\u{E9}.example.org",  // duplicate
            // RFC 3987 section 6.4.
            //"http://www.example.org/r\u{E9}sum\u{E9}.html",  // duplicate
        ];
        for uri in URIS {
            assert_convertible::<IriReferenceStr>(uri);
            assert_non_convertible::<UriReferenceStr>(uri);
            assert_convertible::<IriStr>(uri);
            assert_non_convertible::<UriStr>(uri);
            assert_convertible::<IriAbsoluteStr>(uri);
            assert_non_convertible::<UriAbsoluteStr>(uri);
            assert_non_convertible::<IriRelativeStr>(uri);
            assert_non_convertible::<UriRelativeStr>(uri);
        }
    }

    #[test]
    fn rfc3987_iris_absolute_with_fragment() {
        const URIS: &[&str] = &[
            // RFC 3987 section 6.4.
            "http://www.example.org/r%E9sum%E9.xml#r\u{E9}sum\u{E9}",
        ];
        for uri in URIS {
            assert_convertible::<IriReferenceStr>(uri);
            assert_non_convertible::<UriReferenceStr>(uri);
            assert_convertible::<IriStr>(uri);
            assert_non_convertible::<UriStr>(uri);
            assert_non_convertible::<IriAbsoluteStr>(uri);
            assert_non_convertible::<UriAbsoluteStr>(uri);
            assert_non_convertible::<IriRelativeStr>(uri);
            assert_non_convertible::<UriRelativeStr>(uri);
        }
    }

    #[test]
    fn test_invalid_char() {
        const URIS: &[&str] = &[
            "##", // Fragment cannot have `#`.
            "<",  // `<` cannot appear in an IRI reference.
            ">",  // `>` cannot appear in an IRI reference.
        ];
        for uri in URIS {
            assert_non_convertible::<IriReferenceStr>(uri);
            assert_non_convertible::<UriReferenceStr>(uri);
            assert_non_convertible::<IriStr>(uri);
            assert_non_convertible::<UriStr>(uri);
            assert_non_convertible::<IriAbsoluteStr>(uri);
            assert_non_convertible::<UriAbsoluteStr>(uri);
            assert_non_convertible::<IriRelativeStr>(uri);
            assert_non_convertible::<UriRelativeStr>(uri);
        }
    }

    #[test]
    fn invalid_percent_encoding() {
        const URIS: &[&str] = &["%", "%0", "%0g", "%f", "%fg", "%g", "%g0", "%gf", "%gg"];
        for uri in URIS {
            assert_non_convertible::<IriReferenceStr>(uri);
            assert_non_convertible::<UriReferenceStr>(uri);
            assert_non_convertible::<IriStr>(uri);
            assert_non_convertible::<UriStr>(uri);
            assert_non_convertible::<IriAbsoluteStr>(uri);
            assert_non_convertible::<UriAbsoluteStr>(uri);
            assert_non_convertible::<IriRelativeStr>(uri);
            assert_non_convertible::<UriRelativeStr>(uri);
        }
    }
}
