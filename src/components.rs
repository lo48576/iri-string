//! Components of IRIs.

use core::marker::PhantomData;

use crate::spec::Spec;
use crate::types::RiReferenceStr;

use crate::parser::trusted as trusted_parser;

/// Components of an IRI reference.
///
/// See <https://tools.ietf.org/html/rfc3986#section-5.2.2>.
#[derive(Debug, Clone, Copy)]
pub(crate) struct RiReferenceComponents<'a, S> {
    /// Scheme.
    pub(crate) scheme: Option<&'a str>,
    /// Authority.
    ///
    /// Note that this can be `Some("")`.
    pub(crate) authority: Option<&'a str>,
    /// Path.
    pub(crate) path: &'a str,
    /// Query.
    pub(crate) query: Option<&'a str>,
    /// Fragment.
    pub(crate) fragment: Option<&'a str>,
    /// Spec.
    pub(crate) _spec: PhantomData<fn() -> S>,
}

impl<'a, S: Spec> From<&'a RiReferenceStr<S>> for RiReferenceComponents<'a, S> {
    #[inline]
    fn from(s: &'a RiReferenceStr<S>) -> Self {
        trusted_parser::decompose_iri_reference(s)
    }
}
