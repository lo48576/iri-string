//! Parser.

use nom::combinator::all_consuming;

use self::details::decompose_uri_reference;
pub(crate) use self::details::{
    absolute_uri, path, relative_ref, uri, uri_reference, IriRule, UriRule,
};
pub use crate::types::IriReferenceStr;

mod details;

/// Components of an IRI reference.
///
/// See <https://tools.ietf.org/html/rfc3986#section-5.2.2>.
#[derive(Debug, Clone)]
pub(crate) struct IriReferenceComponents<'a> {
    /// Scheme.
    pub(crate) scheme: Option<&'a str>,
    /// Authority.
    pub(crate) authority: Option<&'a str>,
    /// Path.
    pub(crate) path: &'a str,
    /// Query.
    pub(crate) query: Option<&'a str>,
    /// Fragment.
    pub(crate) fragment: Option<&'a str>,
}

impl<'a> From<&'a IriReferenceStr> for IriReferenceComponents<'a> {
    fn from(s: &'a IriReferenceStr) -> Self {
        all_consuming(decompose_uri_reference::<(), IriRule>)(s)
            .map(|(_rest, components)| components)
            .expect("Should never fail: `IriReferenceStr` should be already validated")
    }
}
