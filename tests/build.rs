//! Tests for builder.

mod components;
#[macro_use]
mod utils;

use iri_string::build::Builder;
use iri_string::types::*;

use self::components::{TestCase, TEST_CASES};

fn assert_builds_for_case(case: &TestCase<'_>, builder: &Builder<'_>) {
    if case.is_iri_class() {
        {
            let built = builder
                .clone()
                .build::<IriReferenceStr>()
                .expect("should be valid IRI reference");
            assert_eq_display!(built, case.composed);
        }
        {
            let built = builder.clone().build::<IriStr>();
            if case.is_absolute() {
                let built = built.expect("should be valid IRI");
                assert_eq_display!(built, case.composed);
            } else {
                assert!(built.is_err(), "should be invalid as IRI");
            }
        }
        {
            let built = builder.clone().build::<IriAbsoluteStr>();
            if case.is_absolute_without_fragment() {
                let built = built.expect("should be valid absolute IRI");
                assert_eq_display!(built, case.composed);
            } else {
                assert!(built.is_err(), "should be invalid as absolute IRI");
            }
        }
        {
            let built = builder.clone().build::<IriRelativeStr>();
            if case.is_relative() {
                let built = built.expect("should be valid relative IRI reference");
                assert_eq_display!(built, case.composed);
            } else {
                assert!(
                    built.is_err(),
                    "should be invalid as relative IRI reference"
                );
            }
        }
    }
    if case.is_uri_class() {
        {
            let built = builder
                .clone()
                .build::<UriReferenceStr>()
                .expect("should be valid URI reference");
            assert_eq_display!(built, case.composed);
        }
        {
            let built = builder.clone().build::<UriStr>();
            if case.is_absolute() {
                let built = built.expect("should be valid URI");
                assert_eq_display!(built, case.composed);
            } else {
                assert!(built.is_err(), "should be invalid as URI");
            }
        }
        {
            let built = builder.clone().build::<UriAbsoluteStr>();
            if case.is_absolute_without_fragment() {
                let built = built.expect("should be valid absolute URI");
                assert_eq_display!(built, case.composed);
            } else {
                assert!(built.is_err(), "should be invalid as absolute URI");
            }
        }
        {
            let built = builder.clone().build::<UriRelativeStr>();
            if case.is_relative() {
                let built = built.expect("should be valid relative URI reference");
                assert_eq_display!(built, case.composed);
            } else {
                assert!(
                    built.is_err(),
                    "should be invalid as relative URI reference"
                );
            }
        }
    }
}

/// Build should succeed or fail, depending on the target syntax and the source string.
#[test]
fn build_simple() {
    for case in TEST_CASES.iter() {
        let mut builder = Builder::new();
        case.components.feed_builder(&mut builder, false);

        assert_builds_for_case(case, &builder);
    }
}

/// Fields of a builder can be unset.
#[test]
fn reuse_dirty_builder() {
    let dirty = {
        let mut b = Builder::new();
        b.scheme("scheme");
        b.userinfo(("user", "password"));
        b.host("host");
        b.port("90127");
        b.path("/path/path-again");
        b.query("query");
        b.fragment("fragment");
        b
    };
    for case in TEST_CASES.iter() {
        let mut builder = dirty.clone();
        case.components.feed_builder(&mut builder, true);

        assert_builds_for_case(case, &builder);
    }
}

/// Builder can normalize absolute IRIs.
#[test]
fn build_normalized_absolute() {
    for case in TEST_CASES.iter().filter(|case| case.is_absolute()) {
        assert!(
            !case.is_relative(),
            "every IRI is absolute or relative, but not both"
        );

        let mut builder = Builder::new();
        case.components.feed_builder(&mut builder, false);
        builder.normalize();

        let built_iri = builder
            .clone()
            .build::<IriStr>()
            .expect("should be valid IRI reference");
        assert_eq_display!(built_iri, case.normalized_iri, "case={case:#?}");

        if case.is_uri_class() {
            let built_uri = builder
                .build::<UriStr>()
                .expect("should be valid URI reference");
            assert_eq_display!(built_uri, case.normalized_uri, "case={case:#?}");
        }
    }
}

/// Builder can normalize relative IRIs.
#[test]
fn build_normalized_relative() {
    for case in TEST_CASES.iter().filter(|case| case.is_relative()) {
        assert!(
            !case.is_absolute(),
            "every IRI is absolute or relative, but not both"
        );

        let mut builder = Builder::new();
        case.components.feed_builder(&mut builder, false);
        builder.normalize();

        let built = builder
            .clone()
            .build::<IriRelativeStr>()
            .expect("should be valid relative IRI reference");
        assert_eq_display!(built, case.normalized_iri);

        if case.is_uri_class() {
            let built_uri = builder
                .build::<UriReferenceStr>()
                .expect("should be valid relative URI reference");
            assert_eq_display!(built_uri, case.normalized_uri);
        }
    }
}

/// Build result can judge RFC3986-normalizedness correctly.
#[test]
fn build_normalizedness() {
    for case in TEST_CASES.iter().filter(|case| case.is_absolute()) {
        let mut builder = Builder::new();
        case.components.feed_builder(&mut builder, false);
        builder.normalize();

        let built = builder
            .clone()
            .build::<IriStr>()
            .expect("should be valid IRI reference");
        let built_judge = built.ensure_rfc3986_normalizable().is_ok();
        assert_eq!(
            built_judge,
            case.is_rfc3986_normalizable(),
            "RFC3986-normalizedness should be correctly judged: case={case:#?}"
        );

        let mut buf = [0_u8; 512];
        let s = iri_string::format::write_to_slice(&mut buf, &built).expect("not enough buffer");
        let built_slice = IriStr::new(s).expect("should be valid IRI reference");
        assert!(built_slice.is_normalized_whatwg(), "should be normalized");
        let slice_judge = built_slice.is_normalized_rfc3986();

        assert_eq!(
            slice_judge, built_judge,
            "RFC3986-normalizedness should be consistently judged: case={case:#?}"
        );
    }
}
