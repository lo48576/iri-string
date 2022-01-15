//! Relative IRI reference.

use crate::components::AuthorityComponents;
use crate::parser::trusted as trusted_parser;
#[cfg(feature = "alloc")]
use crate::raw;
#[cfg(feature = "alloc")]
use crate::resolve::{resolve, Error};
use crate::spec::Spec;
#[cfg(feature = "alloc")]
use crate::types::{RiAbsoluteStr, RiReferenceString, RiString};
use crate::types::{RiFragmentStr, RiReferenceStr};
#[cfg(feature = "alloc")]
use crate::validate::iri;
use crate::validate::relative_ref;

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
    /// Returns resolved IRI against the given base IRI, using strict resolver.
    ///
    /// For reference resolution output examples, see [RFC 3986 section 5.4].
    ///
    /// Enabled by `alloc` or `std` feature.
    ///
    /// # Strictness
    ///
    /// The IRI parsers provided by this crate is strict (e.g. `http:g` is
    /// always interpreted as a composition of the scheme `http` and the path
    /// `g`), so backward compatible parsing and resolution are not provided.
    /// About parser and resolver strictness, see [RFC 3986 section 5.4.2]:
    ///
    /// > Some parsers allow the scheme name to be present in a relative
    /// > reference if it is the same as the base URI scheme. This is considered
    /// > to be a loophole in prior specifications of partial URI
    /// > [RFC1630](https://tools.ietf.org/html/rfc1630). Its use should be
    /// > avoided but is allowed for backward compatibility.
    /// >
    /// > --- <https://tools.ietf.org/html/rfc3986#section-5.4.2>
    ///
    /// # Failures
    ///
    /// This fails if
    ///
    /// * memory allocation failed, or
    /// * the IRI referernce is unresolvable against the base.
    ///
    /// To see examples of unresolvable IRIs, visit the documentation
    /// for [`resolve::Error`][`Error`].
    ///
    /// [RFC 3986 section 5.4]: https://tools.ietf.org/html/rfc3986#section-5.4
    /// [RFC 3986 section 5.4.2]: https://tools.ietf.org/html/rfc3986#section-5.4.2
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn resolve_against(&self, base: &RiAbsoluteStr<S>) -> Result<RiString<S>, Error> {
        resolve(self, base)
    }
}

/// Components getters.
impl<S: Spec> RiRelativeStr<S> {
    /// Returns the authority.
    ///
    /// The leading `//` is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriRelativeStr;
    ///
    /// let iri = IriRelativeStr::new("//example.com/pathpath?queryquery#fragfrag")?;
    /// assert_eq!(iri.authority_str(), Some("example.com"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriRelativeStr;
    ///
    /// let iri = IriRelativeStr::new("foo//bar:baz")?;
    /// assert_eq!(iri.authority_str(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn authority_str(&self) -> Option<&str> {
        trusted_parser::extract_authority_relative(self.as_str())
    }

    /// Returns the path.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriRelativeStr;
    ///
    /// let iri = IriRelativeStr::new("//example.com/pathpath?queryquery#fragfrag")?;
    /// assert_eq!(iri.path_str(), "/pathpath");
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriRelativeStr;
    ///
    /// let iri = IriRelativeStr::new("foo//bar:baz")?;
    /// assert_eq!(iri.path_str(), "foo//bar:baz");
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn path_str(&self) -> &str {
        trusted_parser::extract_path_relative(self.as_str())
    }

    /// Returns the path.
    ///
    /// The leading question mark (`?`) is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriRelativeStr;
    ///
    /// let iri = IriRelativeStr::new("//example.com/pathpath?queryquery#fragfrag")?;
    /// assert_eq!(iri.query_str(), Some("queryquery"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriRelativeStr;
    ///
    /// let iri = IriRelativeStr::new("foo//bar:baz?")?;
    /// assert_eq!(iri.query_str(), Some(""));
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn query_str(&self) -> Option<&str> {
        trusted_parser::extract_query(self.as_str())
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
    #[must_use]
    pub fn fragment(&self) -> Option<&RiFragmentStr<S>> {
        AsRef::<RiReferenceStr<S>>::as_ref(self).fragment()
    }

    /// Returns the authority components.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriRelativeStr;
    ///
    /// let iri = IriRelativeStr::new("//user:pass@example.com:8080/pathpath?queryquery")?;
    /// let authority = iri.authority_components()
    ///     .expect("authority is available");
    /// assert_eq!(authority.userinfo(), Some("user:pass"));
    /// assert_eq!(authority.host(), "example.com");
    /// assert_eq!(authority.port(), Some("8080"));
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// ```
    /// # use iri_string::validate::Error;
    /// use iri_string::types::IriRelativeStr;
    ///
    /// let iri = IriRelativeStr::new("foo//bar:baz")?;
    /// assert_eq!(iri.authority_str(), None);
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn authority_components(&self) -> Option<AuthorityComponents<'_>> {
        AuthorityComponents::from_iri(self.as_ref())
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
