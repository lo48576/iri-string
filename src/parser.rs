//! Parser.

use core::marker::PhantomData;

use nom::combinator::all_consuming;

use crate::{spec::Spec, types::RiReferenceStr};

use self::details::decompose_uri_reference;
pub(crate) use self::details::{absolute_uri, fragment, path, relative_ref, uri, uri_reference};

pub(crate) mod char;
mod details;

/// Components of an IRI reference.
///
/// See <https://tools.ietf.org/html/rfc3986#section-5.2.2>.
#[derive(Debug, Clone)]
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
    fn from(s: &'a RiReferenceStr<S>) -> Self {
        all_consuming(decompose_uri_reference::<(), S>)(s.as_str())
            .map(|(_rest, components)| components)
            .expect("Should never fail: `RiReferenceStr` should be already validated")
    }
}
