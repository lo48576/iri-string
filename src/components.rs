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
    scheme: Option<&'a str>,
    /// Authority.
    ///
    /// Note that this can be `Some("")`.
    authority: Option<&'a str>,
    /// Path.
    path: &'a str,
    /// Query.
    query: Option<&'a str>,
    /// Fragment.
    fragment: Option<&'a str>,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<'a, S: Spec> RiReferenceComponents<'a, S> {
    /// Returns a scheme.
    #[must_use]
    pub(crate) fn scheme(&self) -> Option<&'a str> {
        self.scheme
    }

    /// Returns a authority.
    #[must_use]
    pub(crate) fn authority(&self) -> Option<&'a str> {
        self.authority
    }

    /// Returns a path.
    #[must_use]
    pub(crate) fn path(&self) -> &'a str {
        self.path
    }

    /// Returns a query.
    #[must_use]
    pub(crate) fn query(&self) -> Option<&'a str> {
        self.query
    }

    /// Returns a fragment.
    #[must_use]
    pub(crate) fn fragment(&self) -> Option<&'a str> {
        self.fragment
    }

    /// Returns a major components.
    #[must_use]
    pub(crate) fn to_major(
        self,
    ) -> (
        Option<&'a str>,
        Option<&'a str>,
        &'a str,
        Option<&'a str>,
        Option<&'a str>,
    ) {
        (
            self.scheme(),
            self.authority(),
            self.path(),
            self.query(),
            self.fragment(),
        )
    }

    /// Creates an object from the given major components.
    #[must_use]
    pub(crate) fn from_major(
        scheme: Option<&'a str>,
        authority: Option<&'a str>,
        path: &'a str,
        query: Option<&'a str>,
        fragment: Option<&'a str>,
    ) -> Self {
        Self {
            scheme,
            authority,
            path,
            query,
            fragment,
            _spec: PhantomData,
        }
    }
}

impl<'a, S: Spec> From<&'a RiReferenceStr<S>> for RiReferenceComponents<'a, S> {
    #[inline]
    fn from(s: &'a RiReferenceStr<S>) -> Self {
        trusted_parser::decompose_iri_reference(s)
    }
}
