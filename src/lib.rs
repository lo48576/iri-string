//! String types for IRI.
//!
//! See [RFC 3987](https://tools.ietf.org/html/rfc3987) about IRI.
#![warn(missing_docs)]

extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate opaque_typedef;
#[macro_use]
extern crate opaque_typedef_macros;
extern crate url;

use opaque_typedef::{OpaqueTypedef, OpaqueTypedefUnsized};
use serde::{Deserialize, Deserializer};
pub use url::ParseError as UrlParseError;
pub use url::Url;


/// Absolute IRI and resolved URI.
///
/// **NOTE**: For now, it does not derive `{,Partial}{Eq,Ord}` and `Hash`
/// because it is not sure how they should be ordered or compared by default.
/// If you want to compare them, use raw absolute IRI (by [`AbsoluteIri::raw`])
/// or resolved URI (by [`AbsoluteIri::resolved`]).
#[derive(Debug, Clone)]
pub struct AbsoluteIri {
    /// Raw absolute IRI string.
    raw: AbsoluteIriString,
    /// Resolved URL.
    resolved: Url,
}

impl AbsoluteIri {
    /// Creates a new `AbsoluteIri`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use iri_string::AbsoluteIri;
    /// let s = "https://例.example.com/example/テスト";
    /// assert!(AbsoluteIri::new(s).is_ok());
    /// assert!(AbsoluteIri::new("not-absolute-iri").is_err());
    /// ```
    pub fn new<S: AsRef<str> + Into<String>>(s: S) -> Result<Self, UrlParseError> {
        let resolved = Url::parse(s.as_ref())?;
        let raw = AbsoluteIriString(s.into());
        Ok(AbsoluteIri { raw, resolved })
    }

    /// Returns raw IRI string slice.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use iri_string::AbsoluteIri;
    /// let s = "https://例.example.com/example/テスト";
    /// let iri = AbsoluteIri::new(s).expect("Should never fail");
    /// assert_eq!(iri.raw(), s);
    /// ```
    pub fn raw(&self) -> &AbsoluteIriStr {
        self.raw.as_iri_str()
    }

    /// Returns reference to the resolved URI.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use iri_string::AbsoluteIri;
    /// let s = "https://例.example.com/example/テスト";
    /// let resolved = "https://xn--fsq.example.com/example/%E3%83%86%E3%82%B9%E3%83%88";
    /// let iri = AbsoluteIri::new(s).expect("Should never fail");
    /// assert_eq!(iri.resolved().as_str(), resolved);
    /// ```
    pub fn resolved(&self) -> &Url {
        &self.resolved
    }

    /// Deconstructs `AbsoluteIri` into [`AbsoluteIriString`] and [`Url`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use iri_string::AbsoluteIri;
    /// let s = "https://例.example.com/example/テスト";
    /// let resolved_str = "https://xn--fsq.example.com/example/%E3%83%86%E3%82%B9%E3%83%88";
    ///
    /// let iri = AbsoluteIri::new(s).expect("Should never fail");
    /// let (raw, resolved) = iri.deconstruct();
    /// assert_eq!(raw, s);
    /// assert_eq!(resolved.as_str(), resolved_str);
    /// ```
    pub fn deconstruct(self) -> (AbsoluteIriString, Url) {
        (self.raw, self.resolved)
    }
}


/// Validates the given string as IRI.
///
/// This is intended to be used by `opaque_typedef` and internal functions.
fn validate_iri_str<S: AsRef<str>>(s: S) -> Result<S, UrlParseError> {
    let _ = Url::parse(s.as_ref())?;
    Ok(s)
}


/// IRI string slice.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, OpaqueTypedefUnsized, Serialize)]
#[repr(C)]
#[opaque_typedef(
    derive(
        AsRef(Deref, Self_),
        Deref,
        Display,
        Into(Arc, Box, Rc, Inner),
        PartialEq(Inner, InnerRev, InnerCow, SelfCow, SelfCowRev),
        PartialOrd(Inner, InnerRev, InnerCow, SelfCow, SelfCowRev)
    )
)]
#[opaque_typedef(
    validation(
        validator = "validate_iri_str",
        error_type = "UrlParseError",
        error_msg = "Failed to create `AbsoluteIriString`"
    )
)]
pub struct AbsoluteIriStr(str);

impl AbsoluteIriStr {
    /// Creates a new `AbsoluteIriStr`.
    ///
    /// If you want [`Url`], you should use [`AbsoluteIri::new`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use iri_string::AbsoluteIriStr;
    /// let s = "https://例.example.com/example/テスト";
    /// let iri_str = AbsoluteIriStr::new(s).expect("Should never fail");
    /// assert_eq!(iri_str, s);
    ///
    /// assert!(AbsoluteIriStr::new("not-absolute-iri").is_err());
    /// ```
    pub fn new(s: &str) -> Result<&AbsoluteIriStr, UrlParseError> {
        <Self as OpaqueTypedefUnsized>::try_from_inner(s)
    }

    /// Creates a new `AbsoluteIriStr` from the given string without validation.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the string passed
    /// to it is successfully parsable as IRI.
    /// If this constraint is violated, undefined behavior results, as the rest
    /// of Rust assumes that `&AbsoluteIriStr` is surely an IRI.
    ///
    /// So, the argument should fulfill:
    ///
    /// * [`url::Url::parse(arg)`][`Url::parse`] should return `Ok(_)`.
    pub unsafe fn from_str_unchecked(s: &str) -> &Self {
        // It is caller's responsibility to ensure that this is safe.
        <Self as OpaqueTypedefUnsized>::from_inner_unchecked(s)
    }

    /// Creates `AbsoluteIriStr` from the string slice.
    ///
    /// This is intended to be used by `opaque_typedef`, and it is because this
    /// function is not `unsafe`.
    fn from_str_unchecked_implicitly_unsafe(s: &str) -> &Self {
        let iri = unsafe {
            // It is caller's (`opaque_typedef`'s) responsibility to ensure that
            // this is safe.
            <Self as OpaqueTypedefUnsized>::from_inner_unchecked(s)
        };
        // Validation requires parsing and it will cost, so run this assert only
        // for debug build.
        debug_assert!(
            validate_iri_str(s).is_ok(),
            "Valid IRI string should be passed to \
             `AbsoluteIriStr::from_str_unchecked_implicitly_unsafe()`, but got {:?}",
            s
        );
        iri
    }

    /// Creates an [`Url`].
    ///
    /// If you want both `AbsoluteIriStr` and [`Url`] at once, you should use
    /// [`AbsoluteIri::new`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use iri_string::{AbsoluteIriStr, Url};
    /// let s = "https://例.example.com/example/テスト";
    /// let iri_str = AbsoluteIriStr::new(s).expect("Should never fail");
    /// let url = Url::parse(s).expect("Should never fail");
    /// assert_eq!(iri_str.to_uri(), url);
    /// ```
    pub fn to_uri(&self) -> Url {
        Url::parse(&self.0).unwrap_or_else(|e| {
            unreachable!(
                "`AbsoluteIriString` should have valid IRI string, but parsing failed: {}",
                e
            )
        })
    }
}

impl ToOwned for AbsoluteIriStr {
    type Owned = AbsoluteIriString;

    fn to_owned(&self) -> Self::Owned {
        unsafe {
            // This is safe because `&self.0` is validated at `self` creation.
            <AbsoluteIriString as OpaqueTypedef>::from_inner_unchecked(self.0.to_owned())
        }
    }
}

impl<'de> Deserialize<'de> for &'de AbsoluteIriStr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = <&str>::deserialize(deserializer)?;
        AbsoluteIriStr::new(s).map_err(serde::de::Error::custom)
    }
}


/// Owned IRI string.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, OpaqueTypedef, Serialize)]
#[opaque_typedef(
    derive(
        AsRef(Deref, Inner),
        Deref,
        Display,
        IntoInner,
        PartialEq(Inner, InnerRev),
        PartialOrd(Inner, InnerRev)
    )
)]
#[opaque_typedef(
    deref(target = "AbsoluteIriStr", deref = "AbsoluteIriStr::from_str_unchecked_implicitly_unsafe")
)]
#[opaque_typedef(
    validation(
        validator = "validate_iri_str",
        error_type = "UrlParseError",
        error_msg = "Failed to create `AbsoluteIriString`"
    )
)]
pub struct AbsoluteIriString(String);

impl AbsoluteIriString {
    /// Creates a new `AbsoluteIriString`.
    ///
    /// If you want [`Url`], you should use [`AbsoluteIri::new`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use iri_string::AbsoluteIriString;
    /// let s = "https://例.example.com/example/テスト";
    /// let iri_str = AbsoluteIriString::new(s.to_owned()).expect("Should never fail");
    /// assert_eq!(iri_str, s);
    ///
    /// assert!(AbsoluteIriString::new("not-absolute-iri".to_owned()).is_err());
    /// ```
    pub fn new(s: String) -> Result<AbsoluteIriString, UrlParseError> {
        <Self as OpaqueTypedef>::try_from_inner(s)
    }

    /// Returns [`&AbsoluteIriStr`][`AbsoluteIriStr`] slice for the inner IRI
    /// string.
    pub fn as_iri_str(&self) -> &AbsoluteIriStr {
        self.as_ref()
    }

    /// Creates an [`Url`].
    ///
    /// If you want both `AbsoluteIriString` and [`Url`] at once, you should
    /// use [`AbsoluteIri::new`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use iri_string::{AbsoluteIriString, Url};
    /// let s = "https://例.example.com/example/テスト";
    /// let iri_str = AbsoluteIriString::new(s.to_owned()).expect("Should never fail");
    /// let url = Url::parse(s).expect("Should never fail");
    /// assert_eq!(iri_str.to_uri(), url);
    /// ```
    pub fn to_uri(&self) -> Url {
        Url::parse(&self.0).unwrap_or_else(|e| {
            unreachable!(
                "`AbsoluteIriString` should have valid IRI string, but parsing failed: {}",
                e
            )
        })
    }

    /// Returns a reference to the inner string as `&str`.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl ::std::borrow::Borrow<AbsoluteIriStr> for AbsoluteIriString {
    fn borrow(&self) -> &AbsoluteIriStr {
        self.as_ref()
    }
}

impl AsRef<str> for AbsoluteIriString {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<'de> Deserialize<'de> for AbsoluteIriString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        AbsoluteIriString::new(s).map_err(serde::de::Error::custom)
    }
}

macro_rules! impl_cmp {
    ($Lhs:ty, $Rhs:ty) => {
        impl PartialEq<$Rhs> for $Lhs {
            fn eq(&self, rhs: &$Rhs) -> bool {
                AsRef::<str>::as_ref(self).eq(AsRef::<str>::as_ref(rhs))
            }
        }
        impl PartialEq<$Lhs> for $Rhs {
            fn eq(&self, rhs: &$Lhs) -> bool {
                AsRef::<str>::as_ref(self).eq(AsRef::<str>::as_ref(rhs))
            }
        }
        impl PartialOrd<$Rhs> for $Lhs {
            fn partial_cmp(&self, rhs: &$Rhs) -> Option<::std::cmp::Ordering> {
                AsRef::<str>::as_ref(self).partial_cmp(AsRef::<str>::as_ref(rhs))
            }
        }
        impl PartialOrd<$Lhs> for $Rhs {
            fn partial_cmp(&self, rhs: &$Lhs) -> Option<::std::cmp::Ordering> {
                AsRef::<str>::as_ref(self).partial_cmp(AsRef::<str>::as_ref(rhs))
            }
        }
    };
    ($Lhs:ty, $Rhs:ty, $($lts:tt)*) => {
        impl<$($lts)*> PartialEq<$Rhs> for $Lhs {
            fn eq(&self, rhs: &$Rhs) -> bool {
                AsRef::<str>::as_ref(self).eq(AsRef::<str>::as_ref(rhs))
            }
        }
        impl<$($lts)*> PartialEq<$Lhs> for $Rhs {
            fn eq(&self, rhs: &$Lhs) -> bool {
                AsRef::<str>::as_ref(self).eq(AsRef::<str>::as_ref(rhs))
            }
        }
        impl<$($lts)*> PartialOrd<$Rhs> for $Lhs {
            fn partial_cmp(&self, rhs: &$Rhs) -> Option<::std::cmp::Ordering> {
                AsRef::<str>::as_ref(self).partial_cmp(AsRef::<str>::as_ref(rhs))
            }
        }
        impl<$($lts)*> PartialOrd<$Lhs> for $Rhs {
            fn partial_cmp(&self, rhs: &$Lhs) -> Option<::std::cmp::Ordering> {
                AsRef::<str>::as_ref(self).partial_cmp(AsRef::<str>::as_ref(rhs))
            }
        }
    };
}

// AbsoluteIriStr - AbsoluteIriStr
impl_cmp!(&'a AbsoluteIriStr, AbsoluteIriStr, 'a);
// AbsoluteIriString - AbsoluteIriStr
impl_cmp!(AbsoluteIriString, AbsoluteIriStr);
impl_cmp!(&'a AbsoluteIriString, AbsoluteIriStr, 'a);
impl_cmp!(AbsoluteIriString, &'a AbsoluteIriStr, 'a);
// AbsoluteIriString - AbsoluteIriString
impl_cmp!(&'a AbsoluteIriString, AbsoluteIriString, 'a);
// AbsoluteIriStr - String
impl_cmp!(AbsoluteIriStr, String);
impl_cmp!(&'a AbsoluteIriStr, String, 'a);
impl_cmp!(AbsoluteIriStr, &'a String, 'a);
// AbsoluteIriString - str
impl_cmp!(AbsoluteIriString, str);
impl_cmp!(&'a AbsoluteIriString, str, 'a);
impl_cmp!(AbsoluteIriString, &'a str, 'a);


#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_ok(s: &str) {
        let iri = AbsoluteIri::new(s).unwrap();
        let iri_str = AbsoluteIriStr::new(s).unwrap();
        let iri_string = AbsoluteIriString::new(s.to_owned()).unwrap();
        // Compare URLs.
        assert_eq!(s, iri.raw());
        assert_eq!(iri.resolved(), &Url::parse(iri.raw()).unwrap());
        // Compare `AbsoluteIriStr`s.
        assert_eq!(iri_string, iri_str);
        assert_eq!(iri_string.as_iri_str(), iri_str);
        assert_eq!(iri_string.as_iri_str().to_owned(), iri_string);
    }

    #[test]
    fn ok_cases() {
        let ok_cases = [
            "https://example.com/",
            "https://example.com/テスト",
            "https://example.com/%e3%83%86ス%E3%83%88",
            "https://テスト.日本語/%E3%83%86%E3%82%B9%E3%83%88",
        ];
        ok_cases.into_iter().for_each(|&s| ensure_ok(s));
    }
}
