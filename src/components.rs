//! Components of IRIs.

use core::marker::PhantomData;
use core::num::NonZeroUsize;

use crate::spec::Spec;
use crate::types::RiReferenceStr;

use crate::parser::trusted as trusted_parser;

/// Components of an IRI reference.
///
/// See <https://tools.ietf.org/html/rfc3986#section-5.2.2>.
#[derive(Debug, Clone, Copy)]
pub(crate) struct RiReferenceComponents<'a, S: Spec> {
    /// Original complete string.
    pub(crate) iri: &'a RiReferenceStr<S>,
    /// Scheme end.
    pub(crate) scheme_end: Option<NonZeroUsize>,
    /// Authority end.
    ///
    /// Note that absence of the authority and the empty authority is
    /// distinguished.
    pub(crate) authority_end: Option<NonZeroUsize>,
    /// Query start (after the leading `?`).
    pub(crate) query_start: Option<NonZeroUsize>,
    /// Fragment start (after the leading `#`).
    pub(crate) fragment_start: Option<NonZeroUsize>,
    /// Spec.
    pub(crate) _spec: PhantomData<fn() -> S>,
}

impl<'a, S: Spec> RiReferenceComponents<'a, S> {
    /// Returns five major components: scheme, authority, path, query, and fragment.
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
        let s = self.iri.as_str();
        let (scheme, next_of_scheme) = match self.scheme_end {
            Some(end) => (Some(&s[..end.get()]), end.get() + 1),
            None => (None, 0),
        };
        let (authority, next_of_authority) = match self.authority_end {
            Some(end) => (Some(&s[(next_of_scheme + 2)..end.get()]), end.get()),
            None => (None, next_of_scheme),
        };
        let (fragment, end_of_prev_of_fragment) = match self.fragment_start {
            Some(start) => (Some(&s[start.get()..]), start.get() - 1),
            None => (None, s.len()),
        };
        let (query, end_of_path) = match self.query_start {
            Some(start) => (
                Some(&s[start.get()..end_of_prev_of_fragment]),
                start.get() - 1,
            ),
            None => (None, end_of_prev_of_fragment),
        };
        let path = &s[next_of_authority..end_of_path];
        (scheme, authority, path, query, fragment)
    }
}

impl<'a, S: Spec> From<&'a RiReferenceStr<S>> for RiReferenceComponents<'a, S> {
    #[inline]
    fn from(s: &'a RiReferenceStr<S>) -> Self {
        trusted_parser::decompose_iri_reference(s)
    }
}
