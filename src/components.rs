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

#[cfg(test)]
mod tests {
    use super::*;

    use crate::types::IriReferenceStr;

    /// Creates an `IriReferenceStr`.
    fn iri_ref(s: &str) -> &IriReferenceStr {
        IriReferenceStr::new(s).expect("should be valid")
    }

    #[test]
    fn absolute_slashes() {
        let c0 = RiReferenceComponents::from(iri_ref("scheme:"));
        assert_eq!(c0.authority, None);
        assert_eq!(c0.path, "");

        let c1 = RiReferenceComponents::from(iri_ref("scheme:/"));
        assert_eq!(c1.authority, None);
        assert_eq!(c1.path, "/");

        let c2 = RiReferenceComponents::from(iri_ref("scheme://"));
        assert_eq!(c2.authority, Some(""));
        assert_eq!(c2.path, "");

        let c3 = RiReferenceComponents::from(iri_ref("scheme:///"));
        assert_eq!(c3.authority, Some(""));
        assert_eq!(c3.path, "/");

        let c4 = RiReferenceComponents::from(iri_ref("scheme:////"));
        assert_eq!(c4.authority, Some(""));
        assert_eq!(c4.path, "//");

        let c5 = RiReferenceComponents::from(iri_ref("scheme://///"));
        assert_eq!(c5.authority, Some(""));
        assert_eq!(c5.path, "///");
    }

    #[test]
    fn relative_slashes() {
        let c0 = RiReferenceComponents::from(iri_ref(""));
        assert_eq!(c0.authority, None);
        assert_eq!(c0.path, "");

        let c1 = RiReferenceComponents::from(iri_ref("/"));
        assert_eq!(c1.authority, None);
        assert_eq!(c1.path, "/");

        let c2 = RiReferenceComponents::from(iri_ref("//"));
        assert_eq!(c2.authority, Some(""));
        assert_eq!(c2.path, "");

        let c3 = RiReferenceComponents::from(iri_ref("///"));
        assert_eq!(c3.authority, Some(""));
        assert_eq!(c3.path, "/");

        let c4 = RiReferenceComponents::from(iri_ref("////"));
        assert_eq!(c4.authority, Some(""));
        assert_eq!(c4.path, "//");

        let c5 = RiReferenceComponents::from(iri_ref("/////"));
        assert_eq!(c5.authority, Some(""));
        assert_eq!(c5.path, "///");
    }
}
