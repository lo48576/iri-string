//! Template string types.

use core::convert::TryFrom;
use core::fmt;

use alloc::borrow::{Cow, ToOwned};
use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::sync::Arc;

use crate::spec::Spec;
use crate::template::error::{CreationError, Error, ErrorKind};
use crate::template::expand::Expanded;
use crate::template::parser::validate_template_str;
use crate::template::Context;

/// Implements `PartialEq` and `PartialOrd`.
macro_rules! impl_cmp {
    ($ty_common:ty, $ty_lhs:ty, $ty_rhs:ty) => {
        impl PartialEq<$ty_rhs> for $ty_lhs {
            #[inline]
            fn eq(&self, o: &$ty_rhs) -> bool {
                <$ty_common as PartialEq<$ty_common>>::eq(self.as_ref(), o.as_ref())
            }
        }
        impl PartialEq<$ty_lhs> for $ty_rhs {
            #[inline]
            fn eq(&self, o: &$ty_lhs) -> bool {
                <$ty_common as PartialEq<$ty_common>>::eq(self.as_ref(), o.as_ref())
            }
        }
        impl PartialOrd<$ty_rhs> for $ty_lhs {
            #[inline]
            fn partial_cmp(&self, o: &$ty_rhs) -> Option<core::cmp::Ordering> {
                <$ty_common as PartialOrd<$ty_common>>::partial_cmp(self.as_ref(), o.as_ref())
            }
        }
        impl PartialOrd<$ty_lhs> for $ty_rhs {
            #[inline]
            fn partial_cmp(&self, o: &$ty_lhs) -> Option<core::cmp::Ordering> {
                <$ty_common as PartialOrd<$ty_common>>::partial_cmp(self.as_ref(), o.as_ref())
            }
        }
    };
}

/// A borrowed slice of a URI template.
///
/// URI Template is defined by [RFC 6570].
///
/// Note that "URI Template" can also be used for IRI.
///
/// [RFC 6570]: https://www.rfc-editor.org/rfc/rfc6570.html
///
/// # Valid values
///
/// This type can have a URI template string.
///
/// # Applied errata
///
/// [Errata ID 6937](https://www.rfc-editor.org/errata/eid6937) is applied, so
/// single quotes are allowed to appear in an URI template.
///
/// ```
/// # use iri_string::template::Error;
/// use iri_string::template::UriTemplateStr;
///
/// let template = UriTemplateStr::new("'quoted'")?;
/// # Ok::<_, Error>(())
/// ```
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UriTemplateStr {
    /// The raw string.
    inner: str,
}

impl UriTemplateStr {
    /// Creates a new string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::template::UriTemplateStr;
    ///
    /// let template = UriTemplateStr::new("/users/{username}")?;
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn new(s: &str) -> Result<&Self, Error> {
        TryFrom::try_from(s)
    }

    /// Creates a new string without any validation.
    ///
    /// This does not validate the given string at any time.
    ///
    /// Intended for internal use.
    ///
    /// # Safety
    ///
    /// The given string must be valid.
    #[inline]
    #[must_use]
    unsafe fn new_always_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the template as a plain `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::template::UriTemplateStr;
    ///
    /// let template = UriTemplateStr::new("/users/{username}")?;
    /// assert_eq!(template.as_str(), "/users/{username}");
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }

    /// Returns the template string length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::template::UriTemplateStr;
    ///
    /// let template = UriTemplateStr::new("/users/{username}")?;
    /// assert_eq!(template.len(), "/users/{username}".len());
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.as_str().len()
    }

    /// Returns whether the string is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::template::UriTemplateStr;
    ///
    /// let template = UriTemplateStr::new("/users/{username}")?;
    /// assert!(!template.is_empty());
    ///
    /// let empty = UriTemplateStr::new("")?;
    /// assert!(empty.is_empty());
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }
}

impl UriTemplateStr {
    /// Expands the template with the given context.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::spec::UriSpec;
    /// use iri_string::template::{Context, UriTemplateStr};
    ///
    /// let mut context = Context::new();
    /// context.insert("username", "foo");
    ///
    /// let template = UriTemplateStr::new("/users/{username}")?;
    /// let expanded = template.expand::<UriSpec>(&context)?;
    ///
    /// assert_eq!(
    ///     expanded.to_string(),
    ///     "/users/foo"
    /// );
    /// # Ok::<_, Error>(())
    /// ```
    ///
    /// You can control allowed characters in the output by changing spec type.
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::spec::{IriSpec, UriSpec};
    /// use iri_string::template::{Context, UriTemplateStr};
    ///
    /// let mut context = Context::new();
    /// context.insert("alpha", "\u{03B1}");
    ///
    /// let template = UriTemplateStr::new("{?alpha}")?;
    ///
    /// assert_eq!(
    ///     template.expand::<UriSpec>(&context)?.to_string(),
    ///     "?alpha=%CE%B1",
    ///     "a URI cannot contain Unicode alpha (U+03B1), so it should be escaped"
    /// );
    /// assert_eq!(
    ///     template.expand::<IriSpec>(&context)?.to_string(),
    ///     "?alpha=\u{03B1}",
    ///     "an IRI can contain Unicode alpha (U+03B1), so it written as is"
    /// );
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn expand<'a, S: Spec>(&'a self, context: &'a Context) -> Result<Expanded<'a, S>, Error> {
        Expanded::new(self, context)
    }
}

impl fmt::Debug for UriTemplateStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("UriTemplateStr").field(&&self.inner).finish()
    }
}

impl AsRef<str> for UriTemplateStr {
    #[inline]
    fn as_ref(&self) -> &str {
        &self.inner
    }
}

impl AsRef<UriTemplateStr> for UriTemplateStr {
    #[inline]
    fn as_ref(&self) -> &UriTemplateStr {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a> From<&'a UriTemplateStr> for Cow<'a, UriTemplateStr> {
    #[inline]
    fn from(s: &'a UriTemplateStr) -> Self {
        Cow::Borrowed(s)
    }
}

impl From<&UriTemplateStr> for Arc<UriTemplateStr> {
    fn from(s: &UriTemplateStr) -> Self {
        let inner: &str = s.as_str();
        let buf = Arc::<str>::from(inner);
        unsafe {
            let raw: *const str = Arc::into_raw(buf);
            Self::from_raw(raw as *const UriTemplateStr)
        }
    }
}

impl From<&UriTemplateStr> for Box<UriTemplateStr> {
    fn from(s: &UriTemplateStr) -> Self {
        let inner: &str = s.as_str();
        let buf = Box::<str>::from(inner);
        unsafe {
            let raw: *mut str = Box::into_raw(buf);
            Self::from_raw(raw as *mut UriTemplateStr)
        }
    }
}

impl From<&UriTemplateStr> for Rc<UriTemplateStr> {
    fn from(s: &UriTemplateStr) -> Self {
        let inner: &str = s.as_str();
        let buf = Rc::<str>::from(inner);
        unsafe {
            let raw: *const str = Rc::into_raw(buf);
            Self::from_raw(raw as *const UriTemplateStr)
        }
    }
}

impl<'a> From<&'a UriTemplateStr> for &'a str {
    #[inline]
    fn from(s: &'a UriTemplateStr) -> &'a str {
        s.as_ref()
    }
}

impl<'a> TryFrom<&'a str> for &'a UriTemplateStr {
    type Error = Error;

    #[inline]
    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        match validate_template_str(s) {
            Ok(()) => Ok(unsafe { UriTemplateStr::new_always_unchecked(s) }),
            Err(e) => Err(e),
        }
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a UriTemplateStr {
    type Error = Error;

    #[inline]
    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        let s = core::str::from_utf8(bytes)
            .map_err(|e| Error::new(ErrorKind::InvalidUtf8, e.valid_up_to()))?;
        match validate_template_str(s) {
            Ok(()) => Ok(unsafe { UriTemplateStr::new_always_unchecked(s) }),
            Err(e) => Err(e),
        }
    }
}

impl_cmp!(str, str, UriTemplateStr);
impl_cmp!(str, &str, UriTemplateStr);
impl_cmp!(str, str, &UriTemplateStr);

impl fmt::Display for UriTemplateStr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Serde deserializer implementation.
#[cfg(feature = "serde")]
mod __serde_slice {
    use super::UriTemplateStr;

    use core::{convert::TryFrom, fmt};

    use serde::{
        de::{self, Visitor},
        Deserialize, Deserializer,
    };

    /// Custom borrowed string visitor.
    #[derive(Debug, Clone, Copy)]
    struct CustomStrVisitor;

    impl<'de> Visitor<'de> for CustomStrVisitor {
        type Value = &'de UriTemplateStr;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("URI template string")
        }

        #[inline]
        fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            <&'de UriTemplateStr as TryFrom<&'de str>>::try_from(v).map_err(E::custom)
        }
    }

    // About `'de` and `'a`, see
    // <https://serde.rs/lifetimes.html#the-deserializede-lifetime>.
    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<'a, 'de: 'a> Deserialize<'de> for &'a UriTemplateStr {
        #[inline]
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_string(CustomStrVisitor)
        }
    }
}

/// A borrowed slice of a URI template.
///
/// URI Template is defined by [RFC 6570].
///
/// Note that "URI Template" can also be used for IRI.
///
/// [RFC 6570]: https://www.rfc-editor.org/rfc/rfc6570.html
///
/// # Valid values
///
/// This type can have a URI template string.
// Note that `From<$ty> for {Arc,Rc}<$slice>` is currently not implemented since
// this won't reuse allocated memory and hides internal memory reallocation. See
// <https://github.com/lo48576/iri-string/issues/20#issuecomment-1105207849>.
// However, this is not decided with firm belief or opinion, so there would be
// a chance that they are implemented in future.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UriTemplateString {
    /// Inner data.
    inner: String,
}

impl UriTemplateString {
    /// Shrinks the capacity of the inner buffer to match its length.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    /// Returns the internal buffer capacity in bytes.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns the borrowed IRI string slice.
    ///
    /// This is equivalent to `&*self`.
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &UriTemplateStr {
        self.as_ref()
    }

    /// Appends the template string.
    #[inline]
    pub fn append(&mut self, other: &UriTemplateStr) {
        self.inner.push_str(other.as_str());
        debug_assert!(validate_template_str(self.as_str()).is_ok());
    }
}

impl AsRef<str> for UriTemplateString {
    #[inline]
    fn as_ref(&self) -> &str {
        &self.inner
    }
}

impl AsRef<UriTemplateStr> for UriTemplateString {
    #[inline]
    fn as_ref(&self) -> &UriTemplateStr {
        unsafe {
            // This is safe because `&self` and `self.as_ref()` must be valid.
            UriTemplateStr::new_always_unchecked(AsRef::<str>::as_ref(self))
        }
    }
}

impl core::borrow::Borrow<str> for UriTemplateString {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_ref()
    }
}

impl core::borrow::Borrow<UriTemplateStr> for UriTemplateString {
    #[inline]
    fn borrow(&self) -> &UriTemplateStr {
        self.as_ref()
    }
}

impl ToOwned for UriTemplateStr {
    type Owned = UriTemplateString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

impl From<&'_ UriTemplateStr> for UriTemplateString {
    #[inline]
    fn from(s: &UriTemplateStr) -> Self {
        // This is safe because `s` must be valid.
        Self {
            inner: alloc::string::String::from(s.as_str()),
        }
    }
}

impl From<UriTemplateString> for alloc::string::String {
    #[inline]
    fn from(s: UriTemplateString) -> Self {
        s.inner
    }
}

impl<'a> From<UriTemplateString> for Cow<'a, UriTemplateStr> {
    #[inline]
    fn from(s: UriTemplateString) -> Cow<'a, UriTemplateStr> {
        Cow::Owned(s)
    }
}

impl From<UriTemplateString> for Box<UriTemplateStr> {
    #[inline]
    fn from(s: UriTemplateString) -> Box<UriTemplateStr> {
        let inner: String = s.into();
        let buf = Box::<str>::from(inner);
        unsafe {
            let raw: *mut str = Box::into_raw(buf);
            Box::<UriTemplateStr>::from_raw(raw as *mut UriTemplateStr)
        }
    }
}

impl TryFrom<&'_ str> for UriTemplateString {
    type Error = Error;

    #[inline]
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        <&UriTemplateStr>::try_from(s).map(Into::into)
    }
}

impl TryFrom<&'_ [u8]> for UriTemplateString {
    type Error = Error;

    #[inline]
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let s = core::str::from_utf8(bytes)
            .map_err(|e| Error::new(ErrorKind::InvalidUtf8, e.valid_up_to()))?;
        <&UriTemplateStr>::try_from(s).map(Into::into)
    }
}

impl core::convert::TryFrom<alloc::string::String> for UriTemplateString {
    type Error = CreationError<String>;

    #[inline]
    fn try_from(s: alloc::string::String) -> Result<Self, Self::Error> {
        match <&UriTemplateStr>::try_from(s.as_str()) {
            Ok(_) => {
                // This is safe because `<&UriTemplateStr>::try_from(s)?` ensures
                // that the string `s` is valid.
                Ok(Self { inner: s })
            }
            Err(e) => Err(CreationError::new(e, s)),
        }
    }
}

impl alloc::str::FromStr for UriTemplateString {
    type Err = Error;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        TryFrom::try_from(s)
    }
}

impl core::ops::Deref for UriTemplateString {
    type Target = UriTemplateStr;

    #[inline]
    fn deref(&self) -> &UriTemplateStr {
        self.as_ref()
    }
}

impl_cmp!(str, UriTemplateStr, Cow<'_, str>);
impl_cmp!(str, &UriTemplateStr, Cow<'_, str>);

impl_cmp!(str, str, UriTemplateString);
impl_cmp!(str, &str, UriTemplateString);
impl_cmp!(str, Cow<'_, str>, UriTemplateString);
impl_cmp!(str, String, UriTemplateString);

impl fmt::Display for UriTemplateString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Serde deserializer implementation.
#[cfg(feature = "serde")]
mod __serde_owned {
    use super::UriTemplateString;

    use core::{convert::TryFrom, fmt};

    #[cfg(feature = "serde")]
    use alloc::string::String;

    use serde::{
        de::{self, Visitor},
        Deserialize, Deserializer,
    };

    /// Custom owned string visitor.
    #[derive(Debug, Clone, Copy)]
    struct CustomStringVisitor;

    impl<'de> Visitor<'de> for CustomStringVisitor {
        type Value = UriTemplateString;

        #[inline]
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("URI template string")
        }

        #[inline]
        fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            <UriTemplateString as TryFrom<&str>>::try_from(v).map_err(E::custom)
        }

        #[cfg(feature = "serde")]
        #[inline]
        fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            <UriTemplateString as TryFrom<String>>::try_from(v).map_err(E::custom)
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<'de> Deserialize<'de> for UriTemplateString {
        #[inline]
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_str(CustomStringVisitor)
        }
    }
}
