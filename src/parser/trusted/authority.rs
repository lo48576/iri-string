//! Parsers for trusted `authority` string.

use crate::components::AuthorityComponents;
use crate::parser::str::{find_split_hole, rfind_split};

/// Decomposes the authority into `(userinfo, host, port)`.
///
/// The leading `:` is truncated.
///
/// # Precondition
///
/// The given string must be a valid IRI reference.
#[inline]
#[must_use]
pub(crate) fn decompose_authority(authority: &str) -> AuthorityComponents<'_> {
    let i = authority;
    let (i, host_start) = match find_split_hole(i, b'@') {
        Some((userinfo, rest)) => (rest, userinfo.len() + 1),
        None => (authority, 0),
    };
    let (_i, host_end) = match rfind_split(i, b':') {
        Some((colon_port, rest)) => (rest, host_start + colon_port.len()),
        None => (i, authority.len()),
    };

    AuthorityComponents {
        authority,
        host_start,
        host_end,
    }
}
