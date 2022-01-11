//! Tests for resolvers.

#[cfg(not(test))]
compile_error!("`tests` module should be enable only when `cfg(tests)`");

#[cfg(feature = "alloc")]
mod refimpl;

use super::*;

use crate::types::{IriAbsoluteStr, IriReferenceStr};

#[cfg(feature = "alloc")]
use self::refimpl::resolve as resolve_refimpl;

#[cfg(feature = "alloc")]
fn abs_iri(s: &str) -> &IriAbsoluteStr {
    IriAbsoluteStr::new(s).expect("test case should be valid")
}

#[cfg(feature = "alloc")]
fn iri_ref(s: &str) -> &IriReferenceStr {
    IriReferenceStr::new(s).expect("test case should be valid")
}

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
#[cfg(feature = "alloc")]
fn test_resolve_standalone() {
    for (base, pairs) in TEST_CASES {
        let base = <&IriAbsoluteStr>::try_from(*base)
            .expect("Invalid testcase: base IRI should be absolute IRI");
        for (input, expected) in *pairs {
            let input = <&IriReferenceStr>::try_from(*input)
                .expect("Invalid testcase: `input` should be IRI reference");
            let got = resolve(input, base).expect("Invalid testcase: result should be valid");
            assert_eq!(
                AsRef::<str>::as_ref(&got),
                *expected,
                "base = {:?}, input = {:?}",
                base,
                input
            );
        }
    }
}

#[test]
#[cfg(feature = "alloc")]
fn test_resolve_standalone_same_result_as_reference_impl() {
    for (base, pairs) in TEST_CASES {
        let base = <&IriAbsoluteStr>::try_from(*base)
            .expect("Invalid testcase: base IRI should be absolute IRI");
        for (input, expected) in *pairs {
            let input = <&IriReferenceStr>::try_from(*input)
                .expect("Invalid testcase: `input` should be IRI reference");
            let got = resolve(input, base).expect("Invalid testcase: result should be valid");
            assert_eq!(
                AsRef::<str>::as_ref(&got),
                *expected,
                "base = {:?}, input = {:?}",
                base,
                input
            );

            let referernce_result = resolve_refimpl(input, base);
            assert_eq!(got, referernce_result);
        }
    }
}

#[test]
#[cfg(feature = "alloc")]
fn test_resolve_percent_encoded_dots() {
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
        let base = abs_iri(base);
        let reference = iri_ref(reference);
        let got = resolve(reference, base).expect("resolution should success in this test");
        assert_eq!(got, *expected);
    }
}

#[test]
#[cfg(feature = "alloc")]
fn test_fixed_base_resolver() {
    for (base, pairs) in TEST_CASES {
        let base = <&IriAbsoluteStr>::try_from(*base)
            .expect("Invalid testcase: base IRI should be absolute IRI");
        let resolver = FixedBaseResolver::new(base);
        for (input, expected) in *pairs {
            let input = <&IriReferenceStr>::try_from(*input)
                .expect("Invalid testcase: `input` should be IRI reference");
            let got = resolver
                .resolve(input)
                .expect("Invalid testcase: result should be valid");
            assert_eq!(
                AsRef::<str>::as_ref(&got),
                *expected,
                "base = {:?}, input = {:?}",
                base,
                input
            );
        }
    }
}

#[test]
fn test_fixed_base_resolver_to_byte_slice() {
    let mut buf = [0_u8; 128];
    for (base, pairs) in TEST_CASES {
        let base = <&IriAbsoluteStr>::try_from(*base)
            .expect("Invalid testcase: base IRI should be absolute IRI");
        let resolver = FixedBaseResolver::new(base);
        for (input, expected) in *pairs {
            let input = <&IriReferenceStr>::try_from(*input)
                .expect("Invalid testcase: `input` should be IRI reference");
            let task = resolver.create_task(input);
            let got = task
                .write_to_byte_slice(&mut buf)
                .expect("should not fail by OOM");
            assert_eq!(
                AsRef::<str>::as_ref(&got),
                *expected,
                "base = {:?}, input = {:?}",
                base,
                input
            );
        }
    }
}

#[test]
fn test_fixed_base_resolver_to_byte_slice_should_never_panic() {
    let mut buf_small = [0_u8; 2];
    let mut buf_empty = [];

    for (base, pairs) in TEST_CASES {
        let base = <&IriAbsoluteStr>::try_from(*base)
            .expect("Invalid testcase: base IRI should be absolute IRI");
        let resolver = FixedBaseResolver::new(base);
        for (input, _) in *pairs {
            let input = <&IriReferenceStr>::try_from(*input)
                .expect("Invalid testcase: `input` should be IRI reference");
            let task = resolver.create_task(input);
            let result_small = task.write_to_byte_slice(&mut buf_small);
            assert!(
                result_small.is_err(),
                "expected to fail due to too small destination buffer"
            );
            let result_empty = task.write_to_byte_slice(&mut buf_empty);
            assert!(
                result_empty.is_err(),
                "expected to fail due to too small destination buffer"
            );
        }
    }
}

#[test]
fn test_task_live_longer_than_fixed_base_resolver() {
    let mut buf = [0_u8; 128];

    let base = <&IriAbsoluteStr>::try_from("http://example.com/")
        .expect("Invalid testcase: base IRI should be a valid IRI");
    let reference = <&IriReferenceStr>::try_from("foo/bar")
        .expect("Invalid testcase: reference IRI should be a valid IRI-reference");

    let task = {
        let resolver = FixedBaseResolver::new(base);
        resolver.create_task(reference)
    };
    let result = task
        .write_to_byte_slice(&mut buf)
        .expect("`buf` should be long enough");
    assert_eq!(result, "http://example.com/foo/bar");
}
