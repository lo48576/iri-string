//! URI/IRI builder.
//!
//! See the documentation of [`Builder`] type.

use core::fmt::{self, Display as _, Write as _};
use core::marker::PhantomData;

use crate::format::Censored;
use crate::normalize::{self, DisplayPctCaseNormalize};
use crate::parser::str::{find_split, prior_byte2};
use crate::parser::validate as parser;
use crate::spec::Spec;
use crate::types::{RiAbsoluteStr, RiReferenceStr, RiRelativeStr, RiStr};
#[cfg(feature = "alloc")]
use crate::types::{RiAbsoluteString, RiReferenceString, RiRelativeString, RiString};
use crate::validate;

/// Normalization mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Normalization {
    /// No normalization.
    None,
    /// RFC 3986 algorithm.
    Rfc3986,
    /// WHATWG URL Standard algorithm.
    Whatwg,
}

/// Port builder.
///
/// This type is intended to be created by `From` trait implementations, and
/// to be passed to [`Builder::port`] method.
#[derive(Debug, Clone)]
pub struct PortBuilder<'a>(PortBuilderRepr<'a>);

impl Default for PortBuilder<'_> {
    #[inline]
    fn default() -> Self {
        Self(PortBuilderRepr::Empty)
    }
}

impl<'a> From<u8> for PortBuilder<'a> {
    #[inline]
    fn from(v: u8) -> Self {
        Self(PortBuilderRepr::Integer(v.into()))
    }
}

impl<'a> From<u16> for PortBuilder<'a> {
    #[inline]
    fn from(v: u16) -> Self {
        Self(PortBuilderRepr::Integer(v))
    }
}

impl<'a> From<&'a str> for PortBuilder<'a> {
    #[inline]
    fn from(v: &'a str) -> Self {
        Self(PortBuilderRepr::String(v))
    }
}

#[cfg(feature = "alloc")]
impl<'a> From<&'a alloc::string::String> for PortBuilder<'a> {
    #[inline]
    fn from(v: &'a alloc::string::String) -> Self {
        Self(PortBuilderRepr::String(v.as_str()))
    }
}

/// Internal representation of a port builder.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
enum PortBuilderRepr<'a> {
    /// Empty port.
    Empty,
    /// Port as an integer.
    ///
    /// Note that RFC 3986 accepts any number of digits as a port, but
    /// practically (at least in TCP/IP) `u16` is enough.
    Integer(u16),
    /// Port as a string.
    String(&'a str),
}

/// Userinfo builder.
///
/// This type is intended to be created by `From` trait implementations, and
/// to be passed to [`Builder::userinfo`] method.
#[derive(Clone)]
pub struct UserinfoBuilder<'a>(UserinfoRepr<'a>);

impl Default for UserinfoBuilder<'_> {
    #[inline]
    fn default() -> Self {
        Self(UserinfoRepr::None)
    }
}

impl fmt::Debug for UserinfoBuilder<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("UserinfoBuilder");
        if let Some((user, password)) = self.to_user_password() {
            debug.field("user", &user);
            // > Applications should not render as clear text any data after
            // > the first colon (":") character found within a userinfo
            // > subcomponent unless the data after the colon is the empty
            // > string (indicating no password).
            if matches!(password, None | Some("")) {
                debug.field("password", &password);
            } else {
                debug.field("password", &Some(Censored));
            }
        }
        debug.finish()
    }
}

impl<'a> UserinfoBuilder<'a> {
    /// Decomposes the userinfo into `user` and `password`.
    #[must_use]
    fn to_user_password(&self) -> Option<(Option<&'a str>, Option<&'a str>)> {
        match &self.0 {
            UserinfoRepr::None => None,
            UserinfoRepr::Direct(s) => match find_split(s, b':') {
                None => Some((Some(s), None)),
                Some((user, password)) => Some((Some(user), Some(password))),
            },
            UserinfoRepr::UserPass(user, password) => Some((*user, *password)),
        }
    }
}

impl<'a> From<&'a str> for UserinfoBuilder<'a> {
    #[inline]
    fn from(direct: &'a str) -> Self {
        Self(UserinfoRepr::Direct(direct))
    }
}

impl<'a> From<(&'a str, &'a str)> for UserinfoBuilder<'a> {
    #[inline]
    fn from((user, password): (&'a str, &'a str)) -> Self {
        Self(UserinfoRepr::UserPass(Some(user), Some(password)))
    }
}

impl<'a> From<(&'a str, Option<&'a str>)> for UserinfoBuilder<'a> {
    #[inline]
    fn from((user, password): (&'a str, Option<&'a str>)) -> Self {
        Self(UserinfoRepr::UserPass(Some(user), password))
    }
}

impl<'a> From<(Option<&'a str>, &'a str)> for UserinfoBuilder<'a> {
    #[inline]
    fn from((user, password): (Option<&'a str>, &'a str)) -> Self {
        Self(UserinfoRepr::UserPass(user, Some(password)))
    }
}

impl<'a> From<(Option<&'a str>, Option<&'a str>)> for UserinfoBuilder<'a> {
    #[inline]
    fn from((user, password): (Option<&'a str>, Option<&'a str>)) -> Self {
        Self(UserinfoRepr::UserPass(user, password))
    }
}

#[cfg(feature = "alloc")]
impl<'a> From<&'a alloc::string::String> for UserinfoBuilder<'a> {
    #[inline]
    fn from(v: &'a alloc::string::String) -> Self {
        Self::from(v.as_str())
    }
}

/// Internal representation of a userinfo builder.
#[derive(Clone, Copy)]
enum UserinfoRepr<'a> {
    /// Not specified (absent).
    None,
    /// Direct `userinfo` content.
    Direct(&'a str),
    /// User name and password.
    UserPass(Option<&'a str>, Option<&'a str>),
}

/// URI/IRI authority builder.
#[derive(Default, Debug, Clone)]
struct AuthorityBuilder<'a> {
    /// Host.
    host: HostRepr<'a>,
    /// Port.
    port: PortBuilder<'a>,
    /// Userinfo.
    userinfo: UserinfoBuilder<'a>,
}

impl AuthorityBuilder<'_> {
    /// Writes the authority to the given formatter.
    fn fmt_write_to<S: Spec>(
        &self,
        f: &mut fmt::Formatter<'_>,
        normalize: Normalization,
    ) -> fmt::Result {
        match &self.userinfo.0 {
            UserinfoRepr::None => {}
            UserinfoRepr::Direct(userinfo) => {
                if normalize == Normalization::None {
                    userinfo.fmt(f)?;
                } else {
                    DisplayPctCaseNormalize::<S>::new(userinfo).fmt(f)?;
                }
                f.write_char('@')?;
            }
            UserinfoRepr::UserPass(user, password) => {
                if let Some(user) = user {
                    if normalize == Normalization::None {
                        f.write_str(user)?;
                    } else {
                        DisplayPctCaseNormalize::<S>::new(user).fmt(f)?;
                    }
                }
                if let Some(password) = password {
                    f.write_char(':')?;
                    if normalize == Normalization::None {
                        password.fmt(f)?;
                    } else {
                        DisplayPctCaseNormalize::<S>::new(password).fmt(f)?;
                    }
                }
                f.write_char('@')?;
            }
        }

        match self.host {
            HostRepr::String(host) => {
                if normalize == Normalization::None {
                    f.write_str(host)?;
                } else {
                    normalize::normalize_host_port::<S>(f, host)?;
                }
            }
            #[cfg(feature = "std")]
            HostRepr::IpAddr(ipaddr) => match ipaddr {
                std::net::IpAddr::V4(v) => v.fmt(f)?,
                std::net::IpAddr::V6(v) => write!(f, "[{v}]")?,
            },
        }

        match self.port.0 {
            PortBuilderRepr::Empty => {}
            PortBuilderRepr::Integer(v) => write!(f, ":{v}")?,
            PortBuilderRepr::String(v) => {
                // Omit empty port if the normalization is enabled.
                if !(v.is_empty() && (normalize != Normalization::None)) {
                    write!(f, ":{v}")?;
                }
            }
        }

        Ok(())
    }
}

/// Host representation.
#[derive(Debug, Clone, Copy)]
enum HostRepr<'a> {
    /// Direct string representation.
    String(&'a str),
    #[cfg(feature = "std")]
    /// Dedicated IP address type.
    IpAddr(std::net::IpAddr),
}

impl Default for HostRepr<'_> {
    #[inline]
    fn default() -> Self {
        Self::String("")
    }
}

/// URI/IRI reference builder.
///
/// # Usage
///
/// 1. Create builder by [`Builder::new()`][`Self::new`].
/// 2. Set (or unset) components and set normalization mode as you wish.
/// 3. Validate by [`Builder::build()`][`Self::build`] and get [`DisplayBuild`] value.
/// 4. Use [`core::fmt::Display`] trait to serialize the resulting [`DisplayBuild`],
///    or use [`From`]/[`Into`] traits to convert into an allocated string types.
///
/// ```
/// # use iri_string::build::Error;
/// use iri_string::build::Builder;
/// # #[cfg(not(feature = "alloc"))]
/// # use iri_string::types::IriStr;
/// # #[cfg(feature = "alloc")]
/// use iri_string::types::{IriStr, IriString};
///
/// // 1. Create builder.
/// let mut builder = Builder::new();
///
/// // 2. Set (or unset) component and normalization mode.
/// builder.scheme("http");
/// builder.host("example.com");
/// builder.path("/foo/../");
/// builder.normalize_whatwg();
///
/// // 3. Validate and create the result.
/// let built = builder.build::<IriStr>()?;
///
/// # #[cfg(feature = "alloc")] {
/// // 4a. Serialize by `Display` trait (or `ToString`).
/// let s = built.to_string();
/// assert_eq!(s, "http://example.com/");
/// # }
///
/// # #[cfg(feature = "alloc")] {
/// // 4b. Convert into an allocated string types.
/// // Thanks to pre-validation by `.build::<IriStr>()`, this conversion is infallible!
/// let s: IriString = built.into();
/// assert_eq!(s, "http://example.com/");
/// # }
///
/// # Ok::<_, Error>(())
/// ```
#[derive(Debug, Clone)]
pub struct Builder<'a> {
    /// Scheme.
    scheme: Option<&'a str>,
    /// Authority.
    authority: Option<AuthorityBuilder<'a>>,
    /// Path.
    path: &'a str,
    /// Query (without the leading `?`).
    query: Option<&'a str>,
    /// Fragment (without the leading `#`).
    fragment: Option<&'a str>,
    /// Normalization mode.
    normalize: Normalization,
}

impl Default for Builder<'_> {
    #[inline]
    fn default() -> Self {
        Self {
            scheme: None,
            authority: None,
            path: "",
            query: None,
            fragment: None,
            normalize: Normalization::None,
        }
    }
}

impl<'a> Builder<'a> {
    /// Creates a builder with empty data.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let builder = Builder::new();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Writes the authority to the given formatter.
    ///
    /// Don't expose this as public, since this method does not validate.
    ///
    /// # Preconditions
    ///
    /// The IRI string to be built should be a valid IRI reference.
    /// Callers are responsible to validate the component values before calling
    /// this method.
    fn fmt_write_to<S: Spec>(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(scheme) = self.scheme {
            // Write the scheme.
            if self.normalize == Normalization::None {
                f.write_str(scheme)?;
            } else {
                normalize::normalize_scheme(f, scheme)?;
            }
            f.write_char(':')?;
        }

        if let Some(authority) = &self.authority {
            f.write_str("//")?;
            authority.fmt_write_to::<S>(f, self.normalize)?;
        }

        if self.normalize == Normalization::None {
            f.write_str(self.path)?;
        } else {
            let op = normalize::NormalizationOp {
                case_pct_normalization: true,
            };
            normalize::PathToNormalize::from_single_path(self.path).fmt_write_normalize::<S, _>(
                f,
                op,
                self.authority.is_some(),
            )?;
        }

        if let Some(query) = self.query {
            f.write_char('?')?;
            if self.normalize == Normalization::None {
                f.write_str(query)?;
            } else {
                normalize::normalize_query::<S>(f, query)?;
            }
        }

        if let Some(fragment) = self.fragment {
            f.write_char('#')?;
            if self.normalize == Normalization::None {
                f.write_str(fragment)?;
            } else {
                normalize::normalize_fragment::<S>(f, fragment)?;
            }
        }

        Ok(())
    }

    /// Builds the proxy object that can be converted to the desired IRI string type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriStr;
    /// # #[cfg(feature = "alloc")]
    /// use iri_string::types::IriString;
    ///
    /// let mut builder = Builder::new();
    ///
    /// builder.scheme("http");
    /// builder.host("example.com");
    /// builder.path("/foo/bar");
    ///
    /// let built = builder.build::<IriStr>()?;
    ///
    /// # #[cfg(feature = "alloc")] {
    /// // The returned value implements `core::fmt::Display` and
    /// // `core::string::ToString`.
    /// assert_eq!(built.to_string(), "http://example.com/foo/bar");
    ///
    /// // The returned value implements `Into<{iri_owned_string_type}>`.
    /// let iri = IriString::from(built);
    /// // `let iri: IriString = built.into();` is also OK.
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn build<T>(self) -> Result<DisplayBuild<'a, T>, Error>
    where
        T: ?Sized + Buildable<'a>,
    {
        <T as private::Sealed<'a>>::validate_builder(self)
    }
}

// Setters does not return `&mut Self` or `Self` since it introduces needless
// ambiguity for users.
// For example, if setters return something and allows method chaining, can you
// correctly explain what happens with the code below without reading document?
//
// ```text
// let mut builder = Builder::new().foo("foo").bar("bar");
// let baz = builder.baz("baz").clone().build();
// // Should the result be foo+bar+qux, or foo+bar+baz+qux?
// let qux = builder.qux("qux").build();
// ```
impl<'a> Builder<'a> {
    /// Sets the scheme.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.scheme("foo");
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "foo:");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn scheme(&mut self, v: &'a str) {
        self.scheme = Some(v);
    }

    /// Unsets the scheme.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.scheme("foo");
    /// builder.unset_scheme();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn unset_scheme(&mut self) {
        self.scheme = None;
    }

    /// Sets the path.
    ///
    /// Note that no methods are provided to "unset" path since every IRI
    /// references has a path component (although it can be empty).
    /// If you want to "unset" the path, just set the empty string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.path("foo/bar");
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "foo/bar");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn path(&mut self, v: &'a str) {
        self.path = v;
    }

    /// Initializes the authority builder.
    #[inline]
    fn authority_builder(&mut self) -> &mut AuthorityBuilder<'a> {
        self.authority.get_or_insert_with(AuthorityBuilder::default)
    }

    /// Unsets the authority.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.host("example.com");
    /// builder.unset_authority();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn unset_authority(&mut self) {
        self.authority = None;
    }

    /// Sets the userinfo.
    ///
    /// Note that `(None, None)` is considered as an empty userinfo, rather than
    /// unset userinfo.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.userinfo("user:pass");
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "//user:pass@");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// You can specify `(user, password)` pair.
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    ///
    /// builder.userinfo(("user", Some("pass")));
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(
    ///     builder.clone().build::<IriReferenceStr>()?.to_string(),
    ///     "//user:pass@"
    /// );
    /// # }
    ///
    /// builder.userinfo((None, "pass"));
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(
    ///     builder.clone().build::<IriReferenceStr>()?.to_string(),
    ///     "//:pass@"
    /// );
    /// # }
    ///
    /// builder.userinfo((Some("user"), Some("pass")));
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(
    ///     builder.build::<IriReferenceStr>()?.to_string(),
    ///     "//user:pass@"
    /// );
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// `(None, None)` is considered as an empty userinfo.
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.userinfo((None, None));
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "//@");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn userinfo<T: Into<UserinfoBuilder<'a>>>(&mut self, v: T) {
        self.authority_builder().userinfo = v.into();
    }

    /// Unsets the port.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.userinfo("user:pass");
    /// // Note that this does not unset the entire authority.
    /// // Now empty authority is set.
    /// builder.unset_userinfo();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "//");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn unset_userinfo(&mut self) {
        self.authority_builder().userinfo = UserinfoBuilder::default();
    }

    /// Sets the reg-name or IP address (i.e. host) without port.
    ///
    /// Note that no methods are provided to "unset" host.
    /// Depending on your situation, set empty string as a reg-name, or unset
    /// the authority entirely by [`unset_authority`][`Self::unset_authority`]
    /// method.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.host("example.com");
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "//example.com");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn host(&mut self, v: &'a str) {
        self.authority_builder().host = HostRepr::String(v);
    }

    /// Sets the IP address as a host.
    ///
    /// Note that no methods are provided to "unset" host.
    /// Depending on your situation, set empty string as a reg-name, or unset
    /// the authority entirely by [`unset_authority`][`Self::unset_authority`]
    /// method.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// # #[cfg(feature = "std")] {
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.ip_address(std::net::Ipv4Addr::new(192, 0, 2, 0));
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "//192.0.2.0");
    /// # }
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn ip_address<T: Into<std::net::IpAddr>>(&mut self, addr: T) {
        self.authority_builder().host = HostRepr::IpAddr(addr.into());
    }

    /// Sets the port.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.port(80_u16);
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "//:80");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn port<T: Into<PortBuilder<'a>>>(&mut self, v: T) {
        self.authority_builder().port = v.into();
    }

    /// Unsets the port.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.port(80_u16);
    /// // Note that this does not unset the entire authority.
    /// // Now empty authority is set.
    /// builder.unset_port();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "//");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn unset_port(&mut self) {
        self.authority_builder().port = PortBuilder::default();
    }

    /// Sets the query.
    ///
    /// The string after `?` should be specified.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.query("q=example");
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "?q=example");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn query(&mut self, v: &'a str) {
        self.query = Some(v);
    }

    /// Unsets the query.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.query("q=example");
    /// builder.unset_query();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn unset_query(&mut self) {
        self.query = None;
    }

    /// Sets the fragment.
    ///
    /// The string after `#` should be specified.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.fragment("anchor");
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "#anchor");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn fragment(&mut self, v: &'a str) {
        self.fragment = Some(v);
    }

    /// Unsets the fragment.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.fragment("anchor");
    /// builder.unset_fragment();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn unset_fragment(&mut self) {
        self.fragment = None;
    }

    /// Stop normalizing the result.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.scheme("http");
    /// // `%75%73%65%72` is "user".
    /// builder.userinfo("%75%73%65%72");
    /// builder.host("EXAMPLE.COM");
    /// builder.port("");
    /// builder.path("/foo/../%2e%2e/bar/%2e/baz/.");
    ///
    /// builder.unset_normalize();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(
    ///     iri.to_string(),
    ///     "http://%75%73%65%72@EXAMPLE.COM:/foo/../%2e%2e/bar/%2e/baz/."
    /// );
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn unset_normalize(&mut self) {
        self.normalize = Normalization::None;
    }

    /// Normalizes the result using RFC 3986 normalization algorithm.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.scheme("http");
    /// // `%75%73%65%72` is "user".
    /// builder.userinfo("%75%73%65%72");
    /// builder.host("EXAMPLE.COM");
    /// builder.port("");
    /// builder.path("/foo/../%2e%2e/bar/%2e/baz/.");
    ///
    /// builder.normalize_rfc3986();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "http://user@example.com/bar/baz/");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn normalize_rfc3986(&mut self) {
        self.normalize = Normalization::Rfc3986;
    }

    /// Normalizes the result using WHATWG URL Standard algorithm.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::build::Error;
    /// use iri_string::build::Builder;
    /// use iri_string::types::IriReferenceStr;
    ///
    /// let mut builder = Builder::new();
    /// builder.scheme("http");
    /// // `%75%73%65%72` is "user".
    /// builder.userinfo("%75%73%65%72");
    /// builder.host("EXAMPLE.COM");
    /// builder.port("");
    /// builder.path("/foo/../%2e%2e/bar/%2e/baz/.");
    ///
    /// builder.normalize_whatwg();
    ///
    /// let iri = builder.build::<IriReferenceStr>()?;
    /// # #[cfg(feature = "alloc")] {
    /// assert_eq!(iri.to_string(), "http://user@example.com/bar/baz/");
    /// # }
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn normalize_whatwg(&mut self) {
        self.normalize = Normalization::Whatwg;
    }
}

/// [`Display`]-able IRI build result.
///
/// The value of this type can generate an IRI using [`From`]/[`Into`] traits or
/// [`Display`] trait.
///
/// # Security consideration
///
/// This can be stringified or directly printed by `std::fmt::Display`, but note
/// that this `Display` **does not hide the password part**. Be careful **not to
/// print the value using `Display for DisplayBuild<_>` in public context**.
///
/// [`From`]: `core::convert::From`
/// [`Into`]: `core::convert::Into`
/// [`Display`]: `core::fmt::Display`
#[derive(Debug)]
pub struct DisplayBuild<'a, T: ?Sized> {
    /// Builder with the validated content.
    builder: Builder<'a>,
    /// String type.
    _ty_str: PhantomData<fn() -> T>,
}

impl<T: ?Sized> Clone for DisplayBuild<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            builder: self.builder.clone(),
            _ty_str: PhantomData,
        }
    }
}

impl<S: Spec> fmt::Display for DisplayBuild<'_, RiReferenceStr<S>> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.builder.fmt_write_to::<S>(f)
    }
}

impl<S: Spec> fmt::Display for DisplayBuild<'_, RiStr<S>> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.builder.fmt_write_to::<S>(f)
    }
}

impl<S: Spec> fmt::Display for DisplayBuild<'_, RiAbsoluteStr<S>> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.builder.fmt_write_to::<S>(f)
    }
}

impl<S: Spec> fmt::Display for DisplayBuild<'_, RiRelativeStr<S>> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.builder.fmt_write_to::<S>(f)
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> From<DisplayBuild<'_, RiReferenceStr<S>>> for RiReferenceString<S> {
    #[inline]
    fn from(builder: DisplayBuild<'_, RiReferenceStr<S>>) -> Self {
        (&builder).into()
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> From<&DisplayBuild<'_, RiReferenceStr<S>>> for RiReferenceString<S> {
    fn from(builder: &DisplayBuild<'_, RiReferenceStr<S>>) -> Self {
        let s = builder.to_string();
        Self::try_from(s)
            .expect("[validity] the string to be built should already have been validated")
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> From<DisplayBuild<'_, RiStr<S>>> for RiString<S> {
    #[inline]
    fn from(builder: DisplayBuild<'_, RiStr<S>>) -> Self {
        (&builder).into()
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> From<&DisplayBuild<'_, RiStr<S>>> for RiString<S> {
    fn from(builder: &DisplayBuild<'_, RiStr<S>>) -> Self {
        let s = builder.to_string();
        Self::try_from(s)
            .expect("[validity] the string to be built should already have been validated")
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> From<DisplayBuild<'_, RiAbsoluteStr<S>>> for RiAbsoluteString<S> {
    #[inline]
    fn from(builder: DisplayBuild<'_, RiAbsoluteStr<S>>) -> Self {
        (&builder).into()
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> From<&DisplayBuild<'_, RiAbsoluteStr<S>>> for RiAbsoluteString<S> {
    fn from(builder: &DisplayBuild<'_, RiAbsoluteStr<S>>) -> Self {
        let s = builder.to_string();
        Self::try_from(s)
            .expect("[validity] the string to be built should already have been validated")
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> From<DisplayBuild<'_, RiRelativeStr<S>>> for RiRelativeString<S> {
    #[inline]
    fn from(builder: DisplayBuild<'_, RiRelativeStr<S>>) -> Self {
        (&builder).into()
    }
}

#[cfg(feature = "alloc")]
impl<S: Spec> From<&DisplayBuild<'_, RiRelativeStr<S>>> for RiRelativeString<S> {
    fn from(builder: &DisplayBuild<'_, RiRelativeStr<S>>) -> Self {
        let s = builder.to_string();
        Self::try_from(s)
            .expect("[validity] the string to be built should already have been validated")
    }
}

/// IRI build error.
#[derive(Debug, Clone)]
pub enum Error {
    /// Build result won't be a valid IRI.
    Validate(validate::Error),
    /// Build result won't be normalizable with the specified algorithm.
    Normalize(normalize::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::Validate(_) => "build result won't be a valid IRI",
            Self::Normalize(_) => "build result won't be normalizable with the specified algorithm",
        };
        f.write_str(msg)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Validate(e) => Some(e),
            Self::Normalize(e) => Some(e),
        }
    }
}

impl From<validate::Error> for Error {
    #[inline]
    fn from(e: validate::Error) -> Self {
        Self::Validate(e)
    }
}

impl From<normalize::Error> for Error {
    #[inline]
    fn from(e: normalize::Error) -> Self {
        Self::Normalize(e)
    }
}

/// A trait for borrowed IRI string types buildable by the [`Builder`].
pub trait Buildable<'a>: private::Sealed<'a> {}

impl<'a, S: Spec> private::Sealed<'a> for RiReferenceStr<S> {
    fn validate_builder(builder: Builder<'a>) -> Result<DisplayBuild<'a, Self>, Error> {
        validate_builder_for_iri_reference::<S>(&builder)?;

        Ok(DisplayBuild {
            builder,
            _ty_str: PhantomData,
        })
    }
}
impl<'a, S: Spec> Buildable<'a> for RiReferenceStr<S> {}

impl<'a, S: Spec> private::Sealed<'a> for RiStr<S> {
    fn validate_builder(builder: Builder<'a>) -> Result<DisplayBuild<'a, Self>, Error> {
        if builder.scheme.is_none() {
            return Err(validate::Error::new().into());
        }
        validate_builder_for_iri_reference::<S>(&builder)?;

        Ok(DisplayBuild {
            builder,
            _ty_str: PhantomData,
        })
    }
}
impl<'a, S: Spec> Buildable<'a> for RiStr<S> {}

impl<'a, S: Spec> private::Sealed<'a> for RiAbsoluteStr<S> {
    fn validate_builder(builder: Builder<'a>) -> Result<DisplayBuild<'a, Self>, Error> {
        if builder.scheme.is_none() {
            return Err(validate::Error::new().into());
        }
        if builder.fragment.is_some() {
            return Err(validate::Error::new().into());
        }
        validate_builder_for_iri_reference::<S>(&builder)?;

        Ok(DisplayBuild {
            builder,
            _ty_str: PhantomData,
        })
    }
}
impl<'a, S: Spec> Buildable<'a> for RiAbsoluteStr<S> {}

impl<'a, S: Spec> private::Sealed<'a> for RiRelativeStr<S> {
    fn validate_builder(builder: Builder<'a>) -> Result<DisplayBuild<'a, Self>, Error> {
        if builder.scheme.is_some() {
            return Err(validate::Error::new().into());
        }
        validate_builder_for_iri_reference::<S>(&builder)?;

        Ok(DisplayBuild {
            builder,
            _ty_str: PhantomData,
        })
    }
}
impl<'a, S: Spec> Buildable<'a> for RiRelativeStr<S> {}

/// Checks whether the builder output is valid IRI reference.
fn validate_builder_for_iri_reference<S: Spec>(builder: &Builder<'_>) -> Result<(), Error> {
    if let Some(scheme) = builder.scheme {
        parser::validate_scheme(scheme)?;
    }

    if let Some(authority) = &builder.authority {
        match &authority.userinfo.0 {
            UserinfoRepr::None => {}
            UserinfoRepr::Direct(userinfo) => {
                parser::validate_userinfo::<S>(userinfo)?;
            }
            UserinfoRepr::UserPass(user, password) => {
                // Note that the syntax of components inside `authority`
                // (`user` and `password`) is not specified by RFC 3986.
                if let Some(user) = user {
                    parser::validate_userinfo::<S>(user)?;
                }
                if let Some(password) = password {
                    parser::validate_userinfo::<S>(password)?;
                }
            }
        }

        match authority.host {
            HostRepr::String(s) => parser::validate_host::<S>(s)?,
            #[cfg(feature = "std")]
            HostRepr::IpAddr(_) => {}
        }

        if let PortBuilderRepr::String(s) = authority.port.0 {
            if !s.bytes().all(|b| b.is_ascii_digit()) {
                return Err(validate::Error::new().into());
            }
        }
    }

    let is_path_acceptable = if builder.authority.is_some() {
        // The path should be absolute or empty.
        builder.path.is_empty() || builder.path.starts_with('/')
    } else if builder.scheme.is_some() {
        // The path should not start with '//'.
        !builder.path.starts_with("//")
    } else {
        // If the path is relative (where neither scheme nor authority available),
        //
        // * the path should not start with `//`, and
        // * the first segment should not contain a colon.
        !builder.path.starts_with("//")
            && (prior_byte2(builder.path.as_bytes(), b'/', b':') != Some(b':'))
    };
    if !is_path_acceptable {
        return Err(validate::Error::new().into());
    }
    if (builder.normalize == Normalization::Rfc3986) && builder.authority.is_none() {
        let path = normalize::PathToNormalize::from_single_path(builder.path);
        path.ensure_rfc3986_normalizable_with_authority_absent()?;
    }

    if let Some(query) = builder.query {
        parser::validate_query::<S>(query)?;
    }

    if let Some(fragment) = builder.fragment {
        parser::validate_fragment::<S>(fragment)?;
    }

    Ok(())
}

/// Private module to put the trait to seal.
mod private {
    use super::{Builder, DisplayBuild, Error};

    /// A trait for types buildable by the [`Builder`].
    pub trait Sealed<'a> {
        /// Validates the content of the builder and returns the validated type if possible.
        fn validate_builder(builder: Builder<'a>) -> Result<DisplayBuild<'a, Self>, Error>;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "alloc")]
    use alloc::string::ToString;

    use crate::types::{IriReferenceStr, IriStr};

    #[test]
    fn set_port() {
        let mut builder = Builder::new();
        builder.port(80_u8);
        builder.port(80_u16);
        builder.port("80");
    }

    #[cfg(feature = "std")]
    #[test]
    fn set_ipaddr() {
        let mut builder = Builder::new();
        builder.ip_address(std::net::Ipv4Addr::new(192, 0, 2, 0));
        builder.ip_address(std::net::Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 0));
    }

    #[test]
    fn set_userinfo() {
        let mut builder = Builder::new();
        builder.userinfo("arbitrary-valid-string");
        builder.userinfo("user:password");
        builder.userinfo((None, None));
        builder.userinfo(("user", None));
        builder.userinfo((None, "password"));
        builder.userinfo(("user", "password"));
    }

    #[test]
    fn all() {
        let mut builder = Builder::new();
        builder.scheme("http");
        builder.userinfo(("user", "password"));
        builder.host("example.com");
        builder.port(80_u16);
        builder.path("/path/to/somewhere");
        builder.query("query");
        builder.fragment("fragment");
        #[cfg_attr(not(feature = "alloc"), allow(unused_variables))]
        let built = builder.build::<IriStr>().expect("valid");
        #[cfg(feature = "alloc")]
        assert_eq!(
            built.to_string(),
            "http://user:password@example.com:80/path/to/somewhere?query#fragment"
        );
    }

    #[test]
    fn large_port() {
        let mut builder = Builder::new();
        builder.port("99999999999999999999999999999999");
        builder.port("99999999999999999999999999999999");
        #[cfg_attr(not(feature = "alloc"), allow(unused_variables))]
        let built = builder.build::<IriReferenceStr>().expect("valid");
        #[cfg(feature = "alloc")]
        assert_eq!(built.to_string(), "//:99999999999999999999999999999999");
    }

    #[test]
    fn authority_and_relative_path() {
        let mut builder = Builder::new();
        builder.host("example.com");
        builder.path("relative/path");
        assert!(builder.build::<IriReferenceStr>().is_err());
    }

    #[test]
    fn no_authority_and_double_slash_prefix() {
        let mut builder = Builder::new();
        // This would be interpreted as "network-path reference" (see RFC 3986
        // section 4.2), so this should be rejected.
        builder.path("//double-slash");
        assert!(builder.build::<IriReferenceStr>().is_err());
    }

    #[test]
    fn no_authority_and_relative_first_segment_colon() {
        let mut builder = Builder::new();
        // This would be interpreted as scheme `foo` and host `bar`,
        // so this should be rejected.
        builder.path("foo:bar");
        assert!(builder.build::<IriReferenceStr>().is_err());
    }

    #[test]
    fn normalize_rfc3986_double_slash_prefix() {
        let mut builder = Builder::new();
        builder.scheme("scheme");
        builder.path("/..//bar");
        // Naive application of RFC 3986 normalization/resolution algorithm
        // results in `scheme://bar`, but this is unintentional. `bar` should be
        // the second path segment, not a host. So this should be rejected.
        builder.normalize_rfc3986();
        assert!(builder.build::<IriStr>().is_err());
    }

    #[test]
    fn normalize_whawtg_double_slash_prefix() {
        let mut builder = Builder::new();
        builder.scheme("scheme");
        builder.path("/..//bar");
        // In contrast to RFC 3986, WHATWG URL Standard defines serialization
        // algorithm and handles this case specially. In this case, the result
        // is `scheme:/.//bar`, this won't be considered fully normalized from
        // the RFC 3986 point of view, but more normalization would be
        // impossible and this would practically work in most situations.
        builder.normalize_whatwg();
        #[cfg_attr(not(feature = "alloc"), allow(unused_variables))]
        let built = builder.build::<IriStr>().expect("normalizable");
        #[cfg(feature = "alloc")]
        assert_eq!(built.to_string(), "scheme:/.//bar");
    }
}
