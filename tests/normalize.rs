//! Tests for normalization.

mod components;
#[macro_use]
mod utils;

#[cfg(feature = "alloc")]
use iri_string::format::ToDedicatedString;
use iri_string::types::*;

use self::components::TEST_CASES;

/// Semantically different IRIs should not be normalized into the same IRI.
#[test]
fn different_iris() {
    for case in TEST_CASES
        .iter()
        .filter(|case| !case.different_iris.is_empty())
    {
        let normalized = IriStr::new(case.normalized_iri).expect("should be valid IRI reference");
        for other in case.different_iris.iter().copied() {
            let other = IriStr::new(other).expect("should be valid IRI reference");
            assert_ne!(
                normalized, other,
                "<{}> should not be normalized to <{other}>, case={case:#?}",
                case.composed
            );
        }
    }
}

/// Normalization should work for IRI.
#[test]
fn normalize_uri() {
    for case in TEST_CASES
        .iter()
        .filter(|case| case.is_uri_class() && case.is_absolute())
    {
        let source = UriStr::new(case.composed).expect("should be valid URI");
        let normalized = source.normalize();
        let expected = UriStr::new(case.normalized_uri).expect("should be valid URI");

        assert_eq_display!(normalized, expected, "case={case:#?}");
        #[cfg(feature = "alloc")]
        assert_eq!(normalized.to_string(), expected.as_str(), "case={case:#?}");
        #[cfg(feature = "alloc")]
        assert_eq!(normalized.to_dedicated_string(), expected, "case={case:#?}");

        assert_eq!(
            case.is_rfc3986_normalizable(),
            normalized.ensure_rfc3986_normalizable().is_ok(),
            "case={case:#?}"
        );
    }
}

/// Normalization should work for IRI.
#[test]
fn normalize_iri() {
    for case in TEST_CASES
        .iter()
        .filter(|case| case.is_iri_class() && case.is_absolute())
    {
        let source = IriStr::new(case.composed).expect("should be valid IRI");
        let normalized = source.normalize();
        let expected = IriStr::new(case.normalized_iri).expect("should be valid IRI");

        assert_eq_display!(normalized, expected, "case={case:#?}");
        #[cfg(feature = "alloc")]
        assert_eq!(normalized.to_string(), expected.as_str(), "case={case:#?}");
        #[cfg(feature = "alloc")]
        assert_eq!(normalized.to_dedicated_string(), expected, "case={case:#?}");

        assert_eq!(
            case.is_rfc3986_normalizable(),
            normalized.ensure_rfc3986_normalizable().is_ok(),
            "case={case:#?}"
        );
    }
}

/// Normalization should be idempotent.
#[test]
fn normalize_idempotent() {
    let mut buf = [0_u8; 512];

    for case in TEST_CASES
        .iter()
        .filter(|case| case.is_iri_class() && case.is_absolute())
    {
        let source = IriStr::new(case.composed).expect("should be valid IRI");
        let normalized = source.normalize();
        let expected = IriStr::new(case.normalized_iri).expect("should be valid IRI");

        let normalized_s =
            iri_string::format::write_to_slice(&mut buf, &normalized).expect("not enough buffer");
        let normalized_s = IriStr::new(normalized_s).expect("should be valid IRI reference");

        // Normalize again.
        let normalized_again = normalized_s.normalize();
        assert_eq_display!(normalized_again, expected, "case={case:#?}");
    }
}
