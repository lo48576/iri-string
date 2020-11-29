//! URI and IRI resolvers.
//!
//! Enabled by `alloc` or `std` feature.

use core::convert::TryFrom;

use alloc::{format, string::String};

use crate::{
    parser::RiReferenceComponents,
    spec::Spec,
    types::{RiAbsoluteStr, RiReferenceStr, RiString},
};

/// Resolves the IRI reference.
///
/// It is recommended to use methods such as [`RiReferenceStr::resolve_against()`] and
/// [`RiRelativeStr::resolve_against()`], rather than this freestanding function.
///
/// It is strongly recommended to pass `true` for `is_strict` parameter.
/// If `is_strict` is false, the resolution is done in backward compat mode.
/// However, its use should be avoided.
///
/// > Some parsers allow the scheme name to be present in a relative reference
/// > if it is the same as the base URI scheme. This is considered to be a
/// > loophole in prior specifications of partial URI
/// > [RFC1630](https://tools.ietf.org/html/rfc1630). Its use should be avoided
/// > but is allowed for backward compatibility.
/// >
/// > --- [RFC 3986 section 5.2]
///
/// See [RFC 3986 section 5.2] for detail.
///
/// Enabled by `alloc` or `std` feature.
///
/// [RFC 3986 section 5.2]: https://tools.ietf.org/html/rfc3986#section-5.2
/// [`RiReferenceStr::resolve_against()`]: ../types/struct.RiReferenceStr.html#method.resolve_against
/// [`RiRelativeStr::resolve_against()`]: ../types/struct.RiRelativeStr.html#method.resolve_against
pub fn resolve<S: Spec>(
    reference: impl AsRef<RiReferenceStr<S>>,
    base: impl AsRef<RiAbsoluteStr<S>>,
    is_strict: bool,
) -> RiString<S> {
    resolve_impl(reference.as_ref(), base.as_ref(), is_strict)
}

/// Internal implementation of `resolve`.
///
/// It is strongly recommended to pass `true` for `is_strict` parameter.
/// If `is_strict` is false, the resolution is done in backward compat mode.
/// However, its use should be avoided.
///
/// > Some parsers allow the scheme name to be present in a relative reference
/// > if it is the same as the base URI scheme. This is considered to be a
/// > loophole in prior specifications of partial URI
/// > [RFC1630](https://tools.ietf.org/html/rfc1630). Its use should be avoided
/// > but is allowed for backward compatibility.
/// >
/// > --- [RFC 3986 section 5.2]
///
/// See [RFC 3986 section 5.2] for detail.
///
/// [RFC 3986 section 5.2]: https://tools.ietf.org/html/rfc3986#section-5.2
// > This section defines the process of resolving a URI reference within a
// > context that allows relative references so that the result is a string
// > matching the <URI> syntax rule of Section 3.
// >
// > --- <https://tools.ietf.org/html/rfc3986#section-5>
//
// > A base URI must conform to the <absolute-URI> syntax rule (Section 4.3).
// >
// > --- <https://tools.ietf.org/html/rfc3986#section-5.1>
fn resolve_impl<S: Spec>(
    reference: &RiReferenceStr<S>,
    base: &RiAbsoluteStr<S>,
    is_strict: bool,
) -> RiString<S> {
    let r = RiReferenceComponents::<S>::from(reference);
    let b = RiReferenceComponents::<S>::from(base.as_ref());
    let b_scheme = b
        .scheme
        .expect("Should never fail: `RiAbsoluteStr` should have `scheme` part");

    if let Some(r_scheme) = r.scheme {
        if is_strict || r_scheme != b_scheme {
            let path_new = remove_dot_segments(r.path);
            return recompose_components(r_scheme, r.authority, &path_new, r.query, r.fragment);
        }
    }
    if let Some(r_authority) = r.authority {
        let path_new = remove_dot_segments(r.path);
        return recompose_components(b_scheme, Some(r_authority), &path_new, r.query, r.fragment);
    }
    if r.path.is_empty() {
        return recompose_components(
            b_scheme,
            b.authority,
            b.path,
            r.query.or(b.query),
            r.fragment,
        );
    }
    let path_new = if r.path.starts_with('/') {
        remove_dot_segments(r.path)
    } else {
        remove_dot_segments(&merge(b.path, r.path, b.authority.is_some()))
    };
    recompose_components(b_scheme, b.authority, &path_new, r.query, r.fragment)
}

/// See <https://tools.ietf.org/html/rfc3986#section-5.3>.
fn recompose_components<S: Spec>(
    scheme: &str,
    authority: Option<&str>,
    path: &str,
    query: Option<&str>,
    fragment: Option<&str>,
) -> RiString<S> {
    let mut s = String::from(scheme);
    s.push(':');
    if let Some(authority) = authority {
        s.push_str("//");
        s.push_str(authority);
    }
    s.push_str(path);
    if let Some(query) = query {
        s.push('?');
        s.push_str(query);
    }
    if let Some(fragment) = fragment {
        s.push('#');
        s.push_str(fragment);
    }
    // This should be safe, because RFC 3986 says the algorithm emits URI.
    // However, I'm unsure about correctness of the implementation in this
    // crate, so always validate here.
    RiString::<S>::try_from(s).unwrap_or_else(|e| {
        panic!(
            "Should never happen: if panicked, `resolve()` has a bug: {}",
            e
        )
    })
}

/// See <https://tools.ietf.org/html/rfc3986#section-5.2.4>.
fn remove_dot_segments(mut input: &str) -> String {
    // 1.
    let mut output = String::new();
    // 2.
    while !input.is_empty() {
        input = remove_dot_segments_step(input, &mut output);
        assert!(input.is_empty() || input.as_bytes()[0] == b'/');
    }
    // 3.
    output
}

/// A step in `remove_dot_segments`.
fn remove_dot_segments_step<'a>(input: &'a str, output: &'_ mut String) -> &'a str {
    if let Some(rest) = input.strip_prefix("../") {
        // 2.A.
        rest
    } else if input.starts_with("./") || input.starts_with("/./") {
        // 2.A, 2.B.
        &input[2..]
    } else if input == "/." {
        // 2.B.
        &input[0..1]
    } else if input.starts_with("/../") {
        // 2.C.
        match output.rfind('/') {
            Some(slash_pos) => output.truncate(slash_pos),
            None => output.clear(),
        }
        assert!(!output.ends_with('/'));
        &input[3..]
    } else if input == "/.." {
        // 2.C.
        match output.rfind('/') {
            Some(slash_pos) => output.truncate(slash_pos),
            None => output.clear(),
        }
        assert!(!output.ends_with('/'));
        "/"
    } else if input == "." || input == ".." {
        // 2.D.
        ""
    } else {
        // 2.E.
        let (first_seg, rest) = match input.find('/').and_then(|i| {
            if i == 0 {
                input[1..].find('/').map(|i| i + 1)
            } else {
                Some(i)
            }
        }) {
            Some(i) => (&input[..i], &input[i..]),
            None => (input, ""),
        };
        output.push_str(first_seg);
        rest
    }
}

/// See <https://tools.ietf.org/html/rfc3986#section-5.2.3>.
fn merge(base_path: &str, ref_path: &str, base_authority_defined: bool) -> String {
    if base_authority_defined && base_path.is_empty() {
        format!("/{}", ref_path)
    } else {
        let base_dir = &base_path[..base_path.rfind('/').map(|i| i + 1).unwrap_or(0)];
        format!("{}{}", base_dir, ref_path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::types::{IriAbsoluteStr, IriReferenceStr};

    #[test]
    fn test_remove_dot_segments() {
        // [[(output, input)]]
        const TEST_CASES: &[&[(&str, &str)]] = &[
            // RFC 3986, section 5.2.4.
            &[
                ("", "/a/b/c/./../../g"),
                ("/a", "/b/c/./../../g"),
                ("/a/b", "/c/./../../g"),
                ("/a/b/c", "/./../../g"),
                ("/a/b/c", "/../../g"),
                ("/a/b", "/../g"),
                ("/a", "/g"),
                ("/a/g", ""),
            ],
            &[
                ("", "mid/content=5/../6"),
                ("mid", "/content=5/../6"),
                ("mid/content=5", "/../6"),
                ("mid", "/6"),
                ("mid/6", ""),
            ],
        ];

        for steps in TEST_CASES {
            for steps in steps.windows(2) {
                let (out_prev, in_prev) = steps[0];
                let (out_expected, in_expected) = steps[1];
                let mut out_got = String::from(out_prev);
                let in_got = remove_dot_segments_step(in_prev, &mut out_got);
                assert_eq!(
                    (out_got.as_ref(), in_got),
                    (out_expected, in_expected),
                    "out_prev = {:?}, in_prev = {:?}",
                    out_prev,
                    in_prev
                );
            }
            assert_eq!(remove_dot_segments(steps[0].1), steps[steps.len() - 1].0);
        }
    }

    #[test]
    fn test_reference_resolution() {
        // [(base, [(input, output)])]
        const STRICT_TEST_CASES: &[(&str, &[(&str, &str)])] = &[
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
        ];

        // Test for strict resolver.
        for (base, pairs) in STRICT_TEST_CASES {
            let base = <&IriAbsoluteStr>::try_from(*base)
                .expect("Invalid testcase: base IRI should be absolute IRI");
            for (input, expected) in *pairs {
                let input = <&IriReferenceStr>::try_from(*input)
                    .expect("Invalid testcase: `input` should be IRI reference");
                let got = resolve(input, base, true);
                assert_eq!(
                    AsRef::<str>::as_ref(&got),
                    *expected,
                    "base = {:?}, input = {:?}",
                    base,
                    input
                );
            }
        }

        // Test for loose resolver.
        {
            // RFC 3986, section 5.4.2.
            let base = <&IriAbsoluteStr>::try_from("http://a/b/c/d;p?q")
                .expect("Invalid testcase: base IRI should be absolute IRI");
            let input = <&IriReferenceStr>::try_from("http:g")
                .expect("Invalid testcase: `input` should be IRI reference");
            let got = resolve(input, base, false);
            assert_eq!(AsRef::<str>::as_ref(&got), "http://a/b/c/g");
        }
    }
}
