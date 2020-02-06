//! Relative IRI reference.

#[cfg(feature = "alloc")]
use crate::{
    raw,
    resolve::resolve,
    types::{RiAbsoluteStr, RiReferenceString, RiString},
    validate::iri,
};
use crate::{
    spec::Spec,
    types::{RiFragmentStr, RiReferenceStr},
    validate::relative_ref,
};

define_custom_string_slice! {
    /// A borrowed slice of a relative IRI reference.
    ///
    /// This corresponds to [`irelative-ref` rule] in [RFC 3987]
    /// (and [`relative-ref` rule] in [RFC 3986]).
    /// The rule for `irelative-ref` is `irelative-part [ "?" iquery ] [ "#" ifragment ]`.
    ///
    /// # Valid values
    ///
    /// This type can have a relative IRI reference.
    ///
    /// ```
    /// # use iri_string::types::IriRelativeStr;
    /// assert!(IriRelativeStr::new("foo").is_ok());
    /// assert!(IriRelativeStr::new("foo/bar").is_ok());
    /// assert!(IriRelativeStr::new("/foo").is_ok());
    /// assert!(IriRelativeStr::new("//foo/bar").is_ok());
    /// assert!(IriRelativeStr::new("?foo").is_ok());
    /// assert!(IriRelativeStr::new("#foo").is_ok());
    /// assert!(IriRelativeStr::new("foo/bar?baz#qux").is_ok());
    /// // The first path component can have colon if the path is absolute.
    /// assert!(IriRelativeStr::new("/foo:bar/").is_ok());
    /// // Second or following path components can have colon.
    /// assert!(IriRelativeStr::new("foo/bar://baz/").is_ok());
    /// assert!(IriRelativeStr::new("./foo://bar").is_ok());
    /// ```
    ///
    /// Absolute form of a reference is not allowed.
    ///
    /// ```
    /// # use iri_string::types::IriRelativeStr;
    /// assert!(IriRelativeStr::new("https://example.com/").is_err());
    /// // The first path component cannot have colon, if the path is not absolute.
    /// assert!(IriRelativeStr::new("foo:bar").is_err());
    /// assert!(IriRelativeStr::new("foo:").is_err());
    /// assert!(IriRelativeStr::new("foo:/").is_err());
    /// assert!(IriRelativeStr::new("foo://").is_err());
    /// assert!(IriRelativeStr::new("foo:///").is_err());
    /// assert!(IriRelativeStr::new("foo:////").is_err());
    /// assert!(IriRelativeStr::new("foo://///").is_err());
    /// ```
    ///
    /// Some characters and sequences cannot used in an IRI reference.
    ///
    /// ```
    /// # use iri_string::types::IriRelativeStr;
    /// // `<` and `>` cannot directly appear in a relative IRI reference.
    /// assert!(IriRelativeStr::new("<not allowed>").is_err());
    /// // Broken percent encoding cannot appear in a relative IRI reference.
    /// assert!(IriRelativeStr::new("%").is_err());
    /// assert!(IriRelativeStr::new("%GG").is_err());
    /// ```
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC 3987]: https://tools.ietf.org/html/rfc3987
    /// [`irelative-ref` rule]: https://tools.ietf.org/html/rfc3987#section-2.2
    /// [`relative-ref` rule]: https://tools.ietf.org/html/rfc3986#section-4.2
    struct RiRelativeStr {
        validator = relative_ref,
        expecting_msg = "Relative IRI reference string",
    }
}

#[cfg(feature = "alloc")]
define_custom_string_owned! {
    /// An owned string of a relative IRI reference.
    ///
    /// This corresponds to [`irelative-ref` rule] in [RFC 3987]
    /// (and [`relative-ref` rule] in [RFC 3986]).
    /// The rule for `irelative-ref` is `irelative-part [ "?" iquery ] [ "#" ifragment ]`.
    ///
    /// For details, see the document for [`RiRelativeStr`].
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// [RFC 3986]: https://tools.ietf.org/html/rfc3986
    /// [RFC 3987]: https://tools.ietf.org/html/rfc3987
    /// [`irelative-ref` rule]: https://tools.ietf.org/html/rfc3987#section-2.2
    /// [`relative-ref` rule]: https://tools.ietf.org/html/rfc3986#section-4.2
    /// [`RiRelativeString`]: struct.RiRelativeString.html
    struct RiRelativeString {
        validator = relative_ref,
        slice = RiRelativeStr,
        expecting_msg = "Relative IRI reference string",
    }
}

impl<S: Spec> RiRelativeStr<S> {
    /// Returns the fragment part if exists.
    ///
    /// A leading `#` character is truncated if the fragment part exists.
    ///
    /// # Examples
    ///
    /// If the IRI has a fragment part, `Some(_)` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriRelativeStr}, validate::Error};
    /// let iri = IriRelativeStr::new("?foo#bar")?;
    /// let fragment = IriFragmentStr::new("bar")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriRelativeStr}, validate::Error};
    /// let iri = IriRelativeStr::new("#foo")?;
    /// let fragment = IriFragmentStr::new("foo")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// When the fragment part exists but is empty string, `Some(_)` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::{IriFragmentStr, IriRelativeStr}, validate::Error};
    /// let iri = IriRelativeStr::new("#")?;
    /// let fragment = IriFragmentStr::new("")?;
    /// assert_eq!(iri.fragment(), Some(fragment));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// If the IRI has no fragment, `None` is returned.
    ///
    /// ```
    /// # use iri_string::{spec::IriSpec, types::IriRelativeStr, validate::Error};
    /// let iri = IriRelativeStr::new("")?;
    /// assert_eq!(iri.fragment(), None);
    /// # Ok::<_, Error>(())
    /// ```
    pub fn fragment(&self) -> Option<&RiFragmentStr<S>> {
        AsRef::<RiReferenceStr<S>>::as_ref(self).fragment()
    }

    /// Returns resolved IRI against the given base IRI, using strict resolver.
    ///
    /// About reference resolution output example, see [RFC 3986 section
    /// 5.4](https://tools.ietf.org/html/rfc3986#section-5.4).
    ///
    /// About resolver strictness, see [RFC 3986 section
    /// 5.4.2](https://tools.ietf.org/html/rfc3986#section-5.4.2):
    ///
    /// > Some parsers allow the scheme name to be present in a relative
    /// > reference if it is the same as the base URI scheme. This is considered
    /// > to be a loophole in prior specifications of partial URI
    /// > [RFC1630](https://tools.ietf.org/html/rfc1630). Its use should be
    /// avoided but is allowed for backward compatibility.
    /// >
    /// > --- <https://tools.ietf.org/html/rfc3986#section-5.4.2>
    ///
    /// Usual users will want to use strict resolver.
    ///
    /// Enabled by `alloc` or `std` feature.
    #[cfg(feature = "alloc")]
    pub fn resolve_against(&self, base: &RiAbsoluteStr<S>) -> RiString<S> {
        resolve(self, base, true)
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> RiRelativeString<S> {
    /// Sets the fragment part to the given string.
    ///
    /// Removes fragment part (and following `#` character) if `None` is given.
    pub fn set_fragment(&mut self, fragment: Option<&RiFragmentStr<S>>) {
        raw::set_fragment(&mut self.inner, fragment.map(AsRef::as_ref));
        debug_assert!(iri::<S>(&self.inner).is_ok());
    }
}

impl_infallible_conv_between_iri! {
    from_slice: RiRelativeStr,
    from_owned: RiRelativeString,
    to_slice: RiReferenceStr,
    to_owned: RiReferenceString,
}
