//! IRI reference.

use core::convert::TryFrom;

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, string::String};

use crate::{
    raw,
    spec::Spec,
    types::{RiFragmentStr, RiRelativeStr, RiStr},
    validate::iri_reference,
};
#[cfg(feature = "alloc")]
use crate::{
    resolve::resolve,
    types::{RiAbsoluteStr, RiRelativeString, RiString},
    validate::iri,
};

define_custom_string_slice! {
    /// A borrowed string of an absolute IRI possibly with fragment part.
    ///
    /// This corresponds to [`IRI-reference` rule] in [RFC 3987]
    /// (and [`URI-reference` rule] in [RFC 3986]).
    /// The rule for `IRI-reference` is `IRI / irelative-ref`.
    /// In other words, this is union of [`RiStr`] and [`RiRelativeStr`].
    ///
    /// # Valid values
    ///
    /// This type can have an IRI reference (which can be absolute or relative).
    ///
    /// ```
    /// # use iri_string::types::IriReferenceStr;
    /// assert!(IriReferenceStr::new("https://user:pass@example.com:8080").is_ok());
    /// assert!(IriReferenceStr::new("https://example.com/").is_ok());
    /// assert!(IriReferenceStr::new("https://example.com/foo?bar=baz").is_ok());
    /// assert!(IriReferenceStr::new("https://example.com/foo?bar=baz#qux").is_ok());
    /// assert!(IriReferenceStr::new("foo:bar").is_ok());
    /// assert!(IriReferenceStr::new("foo:").is_ok());
    /// // `foo://.../` below are all allowed. See the crate documentation for detail.
    /// assert!(IriReferenceStr::new("foo:/").is_ok());
    /// assert!(IriReferenceStr::new("foo://").is_ok());
    /// assert!(IriReferenceStr::new("foo:///").is_ok());
    /// assert!(IriReferenceStr::new("foo:////").is_ok());
    /// assert!(IriReferenceStr::new("foo://///").is_ok());
    /// assert!(IriReferenceStr::new("foo/bar").is_ok());
    /// assert!(IriReferenceStr::new("/foo/bar").is_ok());
    /// assert!(IriReferenceStr::new("//foo/bar").is_ok());
    /// assert!(IriReferenceStr::new("#foo").is_ok());
    /// ```
    ///
    /// Some characters and sequences cannot used in an IRI reference.
    ///
    /// ```
    /// # use iri_string::types::IriReferenceStr;
    /// // `<` and `>` cannot directly appear in an IRI reference.
    /// assert!(IriReferenceStr::new("<not allowed>").is_err());
    /// // Broken percent encoding cannot appear in an IRI reference.
    /// assert!(IriReferenceStr::new("%").is_err());
    /// assert!(IriReferenceStr::new("%GG").is_err());
    /// ```
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC 3987]: https://tools.ietf.org/html/rfc3987
    /// [`IRI-reference` rule]: https://tools.ietf.org/html/rfc3987#section-2.2
    /// [`URI-reference` rule]: https://tools.ietf.org/html/rfc3986#section-4.1
    /// [`RiRelativeStr`]: struct.RiRelativeStr.html
    /// [`RiStr`]: struct.RiStr.html
    struct RiReferenceStr {
        validator = iri_reference,
        expecting_msg = "IRI reference string",
    }
}

#[cfg(feature = "alloc")]
define_custom_string_owned! {
    /// An owned string of an absolute IRI possibly with fragment part.
    ///
    /// This corresponds to [`IRI-reference` rule] in [RFC 3987]
    /// (and [`URI-reference` rule] in [RFC 3986]).
    /// The rule for `IRI-reference` is `IRI / irelative-ref`.
    /// In other words, this is union of [`RiString`] and [`RiRelativeString`].
    ///
    /// For details, see the document for [`RiReferenceStr`].
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC 3987]: https://tools.ietf.org/html/rfc3987
    /// [`IRI-reference` rule]: https://tools.ietf.org/html/rfc3987#section-2.2
    /// [`URI-reference` rule]: https://tools.ietf.org/html/rfc3986#section-4.1
    /// [`RiReferenceStr`]: struct.RiReferenceString.html
    /// [`RiRelativeString`]: struct.RiRelativeString.html
    /// [`RiString`]: struct.RiString.html
    struct RiReferenceString {
        validator = iri_reference,
        slice = RiReferenceStr,
        expecting_msg = "IRI reference string",
    }
}

impl<S: Spec> RiReferenceStr<S> {
    /// Returns the string as [`&RiStr`][`RiStr`], if it is valid as an IRI.
    ///
    /// If it is not an IRI, then [`&RiRelativeStr`][`RiRelativeStr`] is returned as `Err(_)`.
    ///
    /// [`RiRelativeStr`]: struct.RiRelativeStr.html
    /// [`RiStr`]: struct.RiStr.html
    pub fn to_iri(&self) -> Result<&RiStr<S>, &RiRelativeStr<S>> {
        // Check with `IRI` rule first, because the syntax rule for `IRI-reference` is
        // `IRI / irelative-ref`.
        //
        // > Some productions are ambiguous. The "first-match-wins" (a.k.a.
        // > "greedy") algorithm applies. For details, see [RFC3986].
        // >
        // > --- <https://tools.ietf.org/html/rfc3987#section-2.2>.
        <&RiStr<S>>::try_from(self.as_str()).map_err(|_| unsafe {
            // This is safe because of the syntax rule `IRI-reference = IRI / irelative-ref`.
            // It says that if an IRI reference is not an IRI, then it is a relative IRI.
            RiRelativeStr::new_maybe_unchecked(self.as_str())
        })
    }

    /// Returns the string as [`&RiRelativeStr`][`RiRelativeStr`], if it is valid as an IRI.
    ///
    /// If it is not an IRI, then [`&RiStr`][`RiStr`] is returned as `Err(_)`.
    ///
    /// [`RiRelativeStr`]: struct.RiRelativeStr.html
    /// [`RiStr`]: struct.RiStr.html
    pub fn to_relative_iri(&self) -> Result<&RiRelativeStr<S>, &RiStr<S>> {
        match self.to_iri() {
            Ok(iri) => Err(iri),
            Err(relative) => Ok(relative),
        }
    }

    /// Returns resolved IRI against the given base IRI, using strict resolver.
    ///
    /// About reference resolution output example, see [RFC 3986 section 5.4].
    ///
    /// About resolver strictness, see [RFC 3986 section 5.4.2]:
    ///
    /// > Some parsers allow the scheme name to be present in a relative
    /// > reference if it is the same as the base URI scheme. This is considered
    /// > to be a loophole in prior specifications of partial URI
    /// > [RFC1630](https://tools.ietf.org/html/rfc1630). Its use should be
    /// > avoided but is allowed for backward compatibility.
    /// >
    /// > --- <https://tools.ietf.org/html/rfc3986#section-5.4.2>
    ///
    /// Usual users will want to use strict resolver.
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// [RFC 3986 section 5.4]: https://tools.ietf.org/html/rfc3986#section-5.4
    /// [RFC 3986 section 5.4.2]: https://tools.ietf.org/html/rfc3986#section-5.4.2
    #[cfg(feature = "alloc")]
    pub fn resolve_against<'a>(&'a self, base: &'_ RiAbsoluteStr<S>) -> Cow<'a, RiStr<S>> {
        match self.to_iri() {
            Ok(iri) => Cow::Borrowed(iri),
            Err(relative) => Cow::Owned(resolve(relative, base, true)),
        }
    }

    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// If the IRI has a fragment part, `Some(_)` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriReferenceStr}, validate::Error};
    /// let iri = IriReferenceStr::new("foo://bar/baz?qux=quux#corge")?;
    /// let fragment = IriFragmentStr::new("corge")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriReferenceStr}, validate::Error};
    /// let iri = IriReferenceStr::new("#foo")?;
    /// let fragment = IriFragmentStr::new("foo")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// When the fragment part exists but is empty string, `Some(_)` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriReferenceStr}, validate::Error};
    /// let iri = IriReferenceStr::new("foo://bar/baz?qux=quux#")?;
    /// let fragment = IriFragmentStr::new("")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriReferenceStr}, validate::Error};
    /// let iri = IriReferenceStr::new("#")?;
    /// let fragment = IriFragmentStr::new("")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// If the IRI has no fragment, `None` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriReferenceStr, validate::Error};
    /// let iri = IriReferenceStr::new("foo://bar/baz?qux=quux")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriReferenceStr, validate::Error};
    /// let iri = IriReferenceStr::new("")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn fragment(&self) -> Option<&RiFragmentStr<S>> {
        raw::extract_fragment(self.as_str()).map(|fragment| unsafe {
            // This is safe because `extract_fragment` returns the fragment part of an IRI, and the
            // returned string is substring of the source IRI.
            RiFragmentStr::new_maybe_unchecked(fragment)
        })
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> RiReferenceString<S> {
    /// Returns the string as [`RiString`], if it is valid as an IRI.
    ///
    /// If it is not an IRI, then [`RiRelativeString`] is returned as `Err(_)`.
    ///
    /// [`RiRelativeString`]: struct.RiRelativeString.html
    /// [`RiString`]: struct.RiString.html
    pub fn into_iri(self) -> Result<RiString<S>, RiRelativeString<S>> {
        let s: String = self.into();
        // Check with `IRI` rule first, because of the syntax.
        //
        // > Some productions are ambiguous. The "first-match-wins" (a.k.a.
        // > "greedy") algorithm applies. For details, see [RFC3986].
        // >
        // > --- <https://tools.ietf.org/html/rfc3987#section-2.2>.
        if iri::<S>(&s).is_ok() {
            Ok(unsafe {
                // This is safe because `s` is already validated by condition of `if`.
                RiString::new_always_unchecked(s)
            })
        } else {
            Err(unsafe {
                // This is safe because of the syntax rule `IRI-reference = IRI / irelative-ref`.
                // It says that if an IRI reference is not an IRI, then it is a relative IRI.
                RiRelativeString::new_maybe_unchecked(s)
            })
        }
    }

    /// Returns the string as [`RiRelativeString`], if it is valid as an IRI.
    ///
    /// If it is not an IRI, then [`RiString`] is returned as `Err(_)`.
    ///
    /// [`RiRelativeString`]: struct.RiRelativeString.html
    /// [`RiString`]: struct.RiString.html
    pub fn into_relative_iri(self) -> Result<RiRelativeString<S>, RiString<S>> {
        match self.into_iri() {
            Ok(iri) => Err(iri),
            Err(relative) => Ok(relative),
        }
    }

    /// Sets the fragment part to the given string.
    ///
    /// Removes fragment part (and following `#` character) if `None` is given.
    pub fn set_fragment(&mut self, fragment: Option<&RiFragmentStr<S>>) {
        raw::set_fragment(&mut self.inner, fragment.map(AsRef::as_ref));
        debug_assert!(iri::<S>(&self.inner).is_ok());
    }
}
