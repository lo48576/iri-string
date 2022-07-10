//! Tests for percent encoding.

#[cfg(feature = "alloc")]
extern crate alloc;

#[macro_use]
mod utils;

#[cfg(feature = "alloc")]
use alloc::string::ToString;

use iri_string::percent_encode::{PercentEncodedForIri, PercentEncodedForUri};

#[test]
fn regname_uri() {
    let encoded = PercentEncodedForUri::from_reg_name("alpha.\u{03B1}.reg.name");
    let expected = "alpha.%CE%B1.reg.name";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn regname_iri() {
    let encoded = PercentEncodedForIri::from_reg_name("alpha.\u{03B1}.reg.name");
    let expected = "alpha.\u{03B1}.reg.name";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn path_segment_uri() {
    let encoded = PercentEncodedForUri::from_path_segment("\u{03B1}/<alpha>?#");
    let expected = "%CE%B1%2F%3Calpha%3E%3F%23";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn path_segment_iri() {
    let encoded = PercentEncodedForIri::from_path_segment("\u{03B1}/<alpha>?#");
    let expected = "\u{03B1}%2F%3Calpha%3E%3F%23";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn path_uri() {
    let encoded = PercentEncodedForUri::from_path("\u{03B1}/<alpha>?#");
    let expected = "%CE%B1/%3Calpha%3E%3F%23";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn path_iri() {
    let encoded = PercentEncodedForIri::from_path("\u{03B1}/<alpha>?#");
    let expected = "\u{03B1}/%3Calpha%3E%3F%23";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn query_uri() {
    let encoded = PercentEncodedForUri::from_query("\u{03B1}/<alpha>?#");
    let expected = "%CE%B1/%3Calpha%3E?%23";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn query_iri() {
    let encoded = PercentEncodedForIri::from_query("\u{03B1}/<alpha>?#");
    let expected = "\u{03B1}/%3Calpha%3E?%23";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn fragment_uri() {
    let encoded = PercentEncodedForUri::from_fragment("\u{03B1}/<alpha>?#");
    let expected = "%CE%B1/%3Calpha%3E?%23";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}

#[test]
fn fragment_iri() {
    let encoded = PercentEncodedForIri::from_fragment("\u{03B1}/<alpha>?#");
    let expected = "\u{03B1}/%3Calpha%3E?%23";
    assert_eq_display!(encoded, expected);
    #[cfg(feature = "alloc")]
    assert_eq!(encoded.to_string(), expected);
}
