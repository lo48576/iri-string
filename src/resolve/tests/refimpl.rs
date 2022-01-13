/// Reference implementation based on RFC 3986 section 5.
use alloc::format;
use alloc::string::String;

use crate::components::RiReferenceComponents;
use crate::spec::Spec;
use crate::types::{RiAbsoluteStr, RiReferenceStr, RiString};

/// Resolves the relative IRI.
///
/// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.2>.
pub(super) fn resolve<S: Spec>(
    reference: &RiReferenceStr<S>,
    base: &RiAbsoluteStr<S>,
) -> RiString<S> {
    let r = RiReferenceComponents::from(reference);
    let b = RiReferenceComponents::from(base.as_ref());

    let t_scheme: &str;
    let t_authority: Option<&str>;
    let t_path: String;
    let t_query: Option<&str>;

    if let Some(r_scheme) = r.scheme {
        t_scheme = r_scheme;
        t_authority = r.authority;
        t_path = remove_dot_segments(r.path.into());
        t_query = r.query;
    } else {
        if r.authority.is_some() {
            t_authority = r.authority;
            t_path = remove_dot_segments(r.path.into());
            t_query = r.query;
        } else {
            if r.path.is_empty() {
                t_path = b.path.into();
                if r.query.is_some() {
                    t_query = r.query;
                } else {
                    t_query = b.query;
                }
            } else {
                if r.path.starts_with('/') {
                    t_path = remove_dot_segments(r.path.into());
                } else {
                    t_path = remove_dot_segments(merge(b.path, r.path, b.authority.is_some()));
                }
                t_query = r.query;
            }
            t_authority = b.authority;
        }
        t_scheme = b.scheme.expect("non-relative IRI must have a scheme");
    }
    let t_fragment: Option<&str> = r.fragment;

    let s = recompose(t_scheme, t_authority, &t_path, t_query, t_fragment);
    RiString::<S>::try_from(s).expect("resolution result must be a valid IRI")
}

/// Merges the two paths.
///
/// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.3>.
fn merge(base_path: &str, ref_path: &str, base_authority_defined: bool) -> String {
    if base_authority_defined && base_path.is_empty() {
        format!("/{}", ref_path)
    } else {
        let base_path_end = base_path.rfind('/').map_or(0, |s| s + 1);
        format!("{}{}", &base_path[..base_path_end], ref_path)
    }
}

/// Removes dot segments from the path.
///
/// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4>.
fn remove_dot_segments(mut input: String) -> String {
    let mut output = String::new();
    while !input.is_empty() {
        if input.starts_with("../") {
            // 2A.
            input.drain(..3);
        } else if input.starts_with("./") {
            // 2A.
            input.drain(..2);
        } else if input.starts_with("/./") {
            // 2B.
            input.replace_range(..3, "/");
        } else if input == "/." {
            // 2B.
            input.replace_range(..2, "/");
        } else if input.starts_with("/../") {
            // 2C.
            input.replace_range(..4, "/");
            remove_last_segment_and_preceding_slash(&mut output);
        } else if input == "/.." {
            // 2C.
            input.replace_range(..3, "/");
            remove_last_segment_and_preceding_slash(&mut output);
        } else if input == "." {
            // 2D.
            input.drain(..1);
        } else if input == ".." {
            // 2D.
            input.drain(..2);
        } else {
            // 2E.
            let first_seg_end = if let Some(after_slash) = input.strip_prefix('/') {
                // `+1` is the length of the initial slash.
                after_slash
                    .find('/')
                    .map_or_else(|| input.len(), |pos| pos + 1)
            } else {
                input.find('/').unwrap_or_else(|| input.len())
            };
            output.extend(input.drain(..first_seg_end));
        }
    }

    output
}

/// Removes the last path segment and the preceding slash if any.
///
/// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4>,
/// step 2C.
fn remove_last_segment_and_preceding_slash(output: &mut String) {
    match output.rfind('/') {
        Some(slash_pos) => {
            output.drain(slash_pos..);
        }
        None => output.clear(),
    }
}

/// Recomposes the components.
///
/// See <https://datatracker.ietf.org/doc/html/rfc3986#section-5.3>.
fn recompose(
    scheme: &str,
    authority: Option<&str>,
    path: &str,
    query: Option<&str>,
    fragment: Option<&str>,
) -> String {
    let mut result = String::new();

    result.push_str(scheme);
    result.push(':');
    if let Some(authority) = authority {
        result.push_str("//");
        result.push_str(authority);
    }
    result.push_str(path);
    if let Some(query) = query {
        result.push('?');
        result.push_str(query);
    }
    if let Some(fragment) = fragment {
        result.push('#');
        result.push_str(fragment);
    }

    result
}
