//! Generic resource identifier types.
//!
//! ```text
//! IRI           = scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]
//! IRI-reference = IRI / irelative-ref
//! absolute-IRI  = scheme ":" ihier-part [ "?" iquery ]
//! irelative-ref = irelative-part [ "?" iquery ] [ "#" ifragment ]
//!     (`irelative-part` is roughly same as `ihier-part`.)
//! ```
//!
//! Hierarchy:
//!
//! ```text
//! RiReferenceStr
//! |-- RiStr
//! |   `-- RiAbsoluteStr
//! `-- RiRelativeStr
//! ```
//!
//! Therefore, the conversions below are safe and cheap:
//!
//! * `RiStr -> RiReferenceStr`
//! * `RiAbsoluteStr -> RiStr`
//! * `RiAbsoluteStr -> RiReferenceStr`
//! * `RiRelativeStr -> RiReferenceStr`
//!
//! For safely convertible types (consider `FooStr -> BarStr` is safe), traits
//! below are implemented:
//!
//! * `AsRef<BarStr> for FooStr`
//! * `AsRef<BarStr> for FooString`
//! * `From<FooString> for BarString`
//! * `PartialEq<FooStr> for BarStr` and lots of impls like that
//!     + `PartialEq` and `ParitalOrd`.
//!     + Slice, owned, `Cow`, reference, etc...

pub use self::{
    absolute::RiAbsoluteStr, fragment::RiFragmentStr, normal::RiStr, query::RiQueryStr,
    reference::RiReferenceStr, relative::RiRelativeStr,
};
#[cfg(feature = "alloc")]
pub use self::{
    absolute::RiAbsoluteString, error::CreationError, fragment::RiFragmentString, normal::RiString,
    query::RiQueryString, reference::RiReferenceString, relative::RiRelativeString,
};

#[macro_use]
mod macros;

mod absolute;
#[cfg(feature = "alloc")]
mod error;
mod fragment;
mod normal;
mod query;
mod reference;
mod relative;

/// Replaces the host in-place and returns the range of the new host, if authority is not empty.
///
/// If the IRI has no authority, returns `None` without doing nothing. Note
/// that an empty host is distinguished from the absence of an authority.
///
/// If the new host is invalid (i.e., [`validate::validate_host`][`crate::validate::host`]
/// returns `Err(_)`), also returns `None` without doing anything.
#[cfg(feature = "alloc")]
fn replace_domain_impl<S: crate::spec::Spec>(
    iri_ref: &mut alloc::string::String,
    new_host: &str,
    replace_only_reg_name: bool,
) -> Result<Option<core::ops::Range<usize>>, alloc::collections::TryReserveError> {
    use crate::components::AuthorityComponents;
    use crate::parser::trusted as trusted_parser;
    use crate::parser::validate::validate_host;

    // Validation of `new_host` needs some parsing, so do this authority
    // presence first to avoid that cost when possible. Extracting authority
    // should be faster because it essentially checks the length of the
    // scheme (which is known to be valid if available) and the presence of
    // the fixed string `://`.
    let (old_host, host_start) = match AuthorityComponents::from_iri_get_offset(iri_ref) {
        Some((authority, offset)) => (authority.host(), offset + authority.host_start),
        None => return Ok(None),
    };
    let old_host_end = host_start + old_host.len();

    if validate_host::<S>(new_host).is_err() {
        return Ok(None);
    }

    if replace_only_reg_name && !trusted_parser::authority::is_host_reg_name(old_host) {
        // Host in the IRI is not a reg-name. Avoid replacing.
        return Ok(None);
    }

    if let Some(additional) = new_host.len().checked_sub(old_host.len()) {
        iri_ref.try_reserve(additional)?;
    }
    iri_ref.replace_range(host_start..old_host_end, new_host);

    let new_host_end = host_start + new_host.len();
    Ok(Some(host_start..new_host_end))
}
