//! Tests for IRI resolution.

#[macro_use]
mod utils;
#[cfg(feature = "alloc")]
mod resolve_refimpl;

use iri_string::format::write_to_slice;
#[cfg(feature = "alloc")]
use iri_string::format::ToDedicatedString;
use iri_string::resolve::FixedBaseResolver;
use iri_string::types::*;

#[cfg(feature = "alloc")]
use self::resolve_refimpl::resolve as resolve_refimpl;

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
fn resolve() {
    for (base, pairs) in TEST_CASES {
        let base = IriAbsoluteStr::new(base).expect("should be valid base IRI");

        for (target, expected) in *pairs {
            let target = IriReferenceStr::new(target).expect("should be valid IRI reference");
            let resolved = target.resolve_against(base);
            assert_eq_display!(resolved, expected, "base={base:?}, target={target:?}");

            #[cfg(feature = "alloc")]
            assert_eq!(
                resolved.to_dedicated_string().as_str(),
                *expected,
                "base={base:?}, target={target:?}"
            );
        }
    }
}

#[test]
#[cfg(feature = "alloc")]
fn fixed_base_resolver() {
    for (base, pairs) in TEST_CASES {
        let base = IriAbsoluteStr::new(base).expect("should be valid base IRI");
        let resolver = FixedBaseResolver::new(base);

        for (target, expected) in *pairs {
            let target = IriReferenceStr::new(target).expect("should be valid IRI reference");
            let resolved = resolver.resolve(target);

            assert_eq_display!(resolved, expected, "base={base:?}, target={target:?}");
            #[cfg(feature = "alloc")]
            assert_eq!(
                resolved.to_dedicated_string().as_str(),
                *expected,
                "base={base:?}, target={target:?}"
            );
        }
    }
}

#[cfg(feature = "alloc")]
#[test]
fn same_result_as_reference_impl() {
    for (base, pairs) in TEST_CASES {
        let base = IriAbsoluteStr::new(base).expect("should be valid base IRI");

        for (target, expected) in *pairs {
            let target = IriReferenceStr::new(target).expect("should be valid IRI reference");
            let resolved = target.resolve_against(base).to_dedicated_string();

            let expected_refimpl = resolve_refimpl(target, base);
            assert_eq!(
                *expected, expected_refimpl,
                "base={base:?}, target={target:?}"
            );
            assert_eq!(
                resolved, expected_refimpl,
                "base={base:?}, target={target:?}"
            );
        }
    }
}

#[test]
fn percent_encoded_dots() {
    // [(base, ref, result)]
    const TEST_CASES: &[(&str, &str, &str)] = &[
        ("scheme:", ".", "scheme:"),
        ("scheme:", "%2e", "scheme:"),
        ("scheme:", "%2E", "scheme:"),
        ("scheme://a", ".", "scheme://a/"),
        ("scheme://a", "%2e", "scheme://a/"),
        ("scheme://a", "%2E", "scheme://a/"),
        ("scheme://a/b/c", ".", "scheme://a/b/"),
        ("scheme://a/b/c", "%2e", "scheme://a/b/"),
        ("scheme://a/b/c", "%2E", "scheme://a/b/"),
        ("scheme://a/b/c", "./g", "scheme://a/b/g"),
        ("scheme://a/b/c", "%2e/g", "scheme://a/b/g"),
        ("scheme://a/b/c", "%2E/g", "scheme://a/b/g"),
        ("scheme://a/b/c/d/e/f", "../../../g", "scheme://a/b/g"),
        (
            "scheme://a/b/c/d/e/f",
            "%2E%2E/%2E%2e/%2E./g",
            "scheme://a/b/g",
        ),
        (
            "scheme://a/b/c/d/e/f",
            "%2e%2E/%2e%2e/%2e./g",
            "scheme://a/b/g",
        ),
        ("scheme://a/b/c/d/e/f", ".%2E/.%2e/../g", "scheme://a/b/g"),
    ];

    for (base, reference, expected) in TEST_CASES {
        let base = IriAbsoluteStr::new(base).expect("should be valid base IRI");
        let reference = IriReferenceStr::new(reference).expect("should be valid IRI reference");

        let resolved = reference.resolve_against(base);
        assert_eq_display!(resolved, *expected);
        #[cfg(feature = "alloc")]
        assert_eq!(resolved.to_dedicated_string(), *expected);
    }
}

#[test]
fn write_to_slice_dont_require_extra_capacity() {
    let mut buf = [0_u8; 128];

    for (base, pairs) in TEST_CASES {
        let base = IriAbsoluteStr::new(base).expect("should be valid base IRI");
        let resolver = FixedBaseResolver::new(base);

        for (target, expected) in *pairs {
            if expected.is_empty() {
                continue;
            }

            let target = IriReferenceStr::new(target).expect("should be valid IRI reference");
            let resolved = resolver.resolve(target);

            let result_small = write_to_slice(&mut buf[..expected.len() - 1], &resolved);
            assert!(result_small.is_err(), "should fail due to too small buffer");

            let result_enough = write_to_slice(&mut buf[..expected.len()], &resolved);
            assert!(result_enough.is_ok(), "buffer should have enough size");
            assert_eq!(
                result_enough.unwrap(),
                *expected,
                "correct result should be written"
            );
        }
    }
}

#[test]
fn resolution_result_live_longer_than_fixed_base_resolver() {
    let mut buf = [0_u8; 128];

    let base = IriAbsoluteStr::new("http://example.com/").expect("should be valid base IRI");
    let reference = IriReferenceStr::new("foo/bar").expect("should be valid IRI reference");

    let resolved = {
        let resolver = FixedBaseResolver::new(base);
        resolver.resolve(reference)
    };
    // Note that `the result of `resolver.resolve()` is still alive here.
    let result = write_to_slice(&mut buf, &resolved).expect("`buf` should have enough capacity");
    assert_eq!(result, "http://example.com/foo/bar");
}
