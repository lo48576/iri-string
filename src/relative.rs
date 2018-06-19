//! Relative IRI types.
//!
//! RFC 3987 refers [RFC 3986](https://tools.ietf.org/html/rfc3986#section-4.2)
//! for definition of relative IRI reference.

use std::error;
use std::fmt;

use opaque_typedef::{OpaqueTypedef, OpaqueTypedefUnsized};
#[cfg(feature = "serde")]
use serde;
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer};
use url::ParseError as UrlParseError;
use url::Url;

use has_colon_before_slash;


/// Relative URL parse error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelativeIriParseError {
    /// Got a single colon character.
    SingleColon,
    /// Has colon at first component.
    FirstComponentHasColon,
    /// Other URL parsing error.
    Url(UrlParseError),
}

impl error::Error for RelativeIriParseError {
    fn description(&self) -> &str {
        match *self {
            RelativeIriParseError::SingleColon => "Single colon cannot be a relative path",
            RelativeIriParseError::FirstComponentHasColon => {
                "First component should not have a colon"
            },
            RelativeIriParseError::Url(ref e) => e.description(),
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            RelativeIriParseError::Url(ref e) => Some(e),
            _ => None,
        }
    }
}

impl fmt::Display for RelativeIriParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use std::error::Error;

        match *self {
            RelativeIriParseError::SingleColon | RelativeIriParseError::FirstComponentHasColon => {
                f.write_str(self.description())
            },
            RelativeIriParseError::Url(ref e) => e.fmt(f),
        }
    }
}

impl From<UrlParseError> for RelativeIriParseError {
    fn from(e: UrlParseError) -> Self {
        RelativeIriParseError::Url(e)
    }
}


/// Validates the given string as relative IRI.
///
/// This is intended to be used by `opaque_typedef` and internal functions.
fn validate_relative_iri_str<S: AsRef<str>>(s: S) -> Result<S, RelativeIriParseError> {
    // See <https://tools.ietf.org/html/rfc3986#section-4.2>,
    // <https://tools.ietf.org/html/rfc3986#section-3.2> and
    // <https://tools.ietf.org/html/rfc3986#section-3.3>.
    //
    // relative-ref  = relative-part [ "?" query ] [ "#" fragment ]
    // relative-part = "//" authority path-abempty
    //               / path-absolute    ; begins with "/" but not "//"
    //               / path-noscheme    ; begins with a non-colon segment
    //               / path-empty       ; zero characters
    // authority = [ userinfo "@" ] host [ ":" port ]
    // path-abempty = *( "/" segment )
    // path-absolute = "/" [ segment-nz *( "/" segment ) ]
    //
    // `"//" authority path-abempty` can be validated by prepening `"http://"`.
    // `path-absolute` and `path-noscheme` can be validated by pretending
    // `"unknown-scheme:"` and simple string manipulation.
    //
    // scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )
    //
    // Unknown scheme can any unknown (by `url` crate) scheme.
    // However, `url` parser allocates memory, so it is better to use shorter
    // string.

    // Unknown (by `url` crate) scheme.
    const UNKNOWN_DUMMY_SCHEME: &str = "x";

    if s.as_ref().len() < 2 {
        // If "", it matches `path-empty`.
        // If "/", it matches `path-absolute`.
        // If ":", it is an error.
        // Otherwise, it matches `path-noscheme`.
        //
        // NOTE: If "%", "[" or "]", maybe it should be an error.
        // However, `url` crate currently (1.7.0) treat them as valid path
        // component, so consider them as valid here.
        if s.as_ref() == ":" {
            return Err(RelativeIriParseError::SingleColon);
        } else {
            return Ok(s);
        }
    }
    if s.as_ref().starts_with("//") {
        // It can be `"//" authority path-abempty`.
        let dummy_absolute = format!("http:{}", s.as_ref());
        let _ = Url::parse(&dummy_absolute)?;
        Ok(s)
    } else if s.as_ref().starts_with('/') {
        // It can be `path-absolute`.
        let dummy_absolute = format!("{}:{}", UNKNOWN_DUMMY_SCHEME, s.as_ref());
        let _ = Url::parse(&dummy_absolute)?;
        Ok(s)
    } else if has_colon_before_slash(s.as_ref()) {
        // Expected `path-noscheme` but invalid.
        Err(RelativeIriParseError::FirstComponentHasColon)
    } else {
        // Got `path-noscheme`.
        Ok(s)
    }
}


/// Relative IRI string slice.
// derive_hash_xor_eq (clippy lint):
//  This does not matter because explicit `PartialEq` impls are only doing
//  type conversion (`&RelativeIriStr` to `&str`) and equalness is preserved.
#[allow(unknown_lints, derive_hash_xor_eq)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, OpaqueTypedefUnsized)]
#[cfg_attr(feature = "serde", derive(Serialize))]
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
        validator = "validate_relative_iri_str",
        error_type = "RelativeIriParseError",
        error_msg = "Failed to create `RelativeIriString`"
    )
)]
pub struct RelativeIriStr(str);

impl RelativeIriStr {
    /// Creates a new `RelativeIriStr`.
    pub fn new(s: &str) -> Result<&RelativeIriStr, RelativeIriParseError> {
        <Self as OpaqueTypedefUnsized>::try_from_inner(s)
    }

    /// Creates a new `RelativeIriStr` from the given string without validation.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the string passed
    /// to it is successfully parsable as relative IRI.
    /// If this constraint is violated, undefined behavior results, as the rest
    /// of Rust assumes that `&RelativeIriStr` is surely a relative IRI.
    ///
    /// So, the argument should fulfill:
    ///
    /// * it is relative IRI defined at [RFC
    ///   3339](https://tools.ietf.org/html/rfc3986#section-4.2).
    ///     + Precisely, `RelativeIriStr` is a bit torelant and it can accept
    ///       wrong strings, but that behavior may change in future.
    pub unsafe fn from_str_unchecked(s: &str) -> &Self {
        // It is caller's responsibility to ensure that this is safe.
        <Self as OpaqueTypedefUnsized>::from_inner_unchecked(s)
    }

    /// Creates `RelativeIriStr` from the string slice.
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
            validate_relative_iri_str(s).is_ok(),
            "Valid IRI string should be passed to \
             `RelativeIriStr::from_str_unchecked_implicitly_unsafe()`, but got {:?}",
            s
        );
        iri
    }
}

impl ToOwned for RelativeIriStr {
    type Owned = RelativeIriString;

    fn to_owned(&self) -> Self::Owned {
        unsafe {
            // This is safe because `&self.0` is validated at `self` creation.
            <RelativeIriString as OpaqueTypedef>::from_inner_unchecked(self.0.to_owned())
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for &'de RelativeIriStr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = <&str>::deserialize(deserializer)?;
        RelativeIriStr::new(s).map_err(serde::de::Error::custom)
    }
}


/// Owned relative IRI string.
// derive_hash_xor_eq (clippy lint):
//  This does not matter because explicit `PartialEq` impls are only doing
//  type conversion (`&RelativeIriString` to `&str`) and equalness is preserved.
#[allow(unknown_lints, derive_hash_xor_eq)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, OpaqueTypedef)]
#[cfg_attr(feature = "serde", derive(Serialize))]
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
    deref(
        target = "RelativeIriStr", deref = "RelativeIriStr::from_str_unchecked_implicitly_unsafe"
    )
)]
#[opaque_typedef(
    validation(
        validator = "validate_relative_iri_str",
        error_type = "RelativeIriParseError",
        error_msg = "Failed to create `RelativeIriString`"
    )
)]
pub struct RelativeIriString(String);

impl RelativeIriString {
    /// Creates a new `RelativeIriString`.
    pub fn new(s: String) -> Result<RelativeIriString, RelativeIriParseError> {
        <Self as OpaqueTypedef>::try_from_inner(s)
    }

    /// Creates a new `RelativeIriString` from the given string without
    /// validation.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the string passed
    /// to it is successfully parsable as relative IRI.
    /// If this constraint is violated, undefined behavior results, as the rest
    /// of Rust assumes that `RelativeIriString` is surely a relative IRI.
    ///
    /// So, the argument should fulfill:
    ///
    /// * it is relative IRI defined at [RFC
    ///   3339](https://tools.ietf.org/html/rfc3986#section-4.2).
    ///     + Precisely, `RelativeIriStr` is a bit torelant and it can accept
    ///       wrong strings, but that behavior may change in future.
    pub unsafe fn new_unchecked(s: String) -> RelativeIriString {
        <Self as OpaqueTypedef>::from_inner_unchecked(s)
    }

    /// Returns [`&RelativeIriStr`][`RelativeIriStr`] slice for the inner IRI
    /// string.
    pub fn as_iri_str(&self) -> &RelativeIriStr {
        self.as_ref()
    }

    /// Returns a reference to the inner string as `&str`.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl ::std::borrow::Borrow<RelativeIriStr> for RelativeIriString {
    fn borrow(&self) -> &RelativeIriStr {
        self.as_ref()
    }
}

impl AsRef<str> for RelativeIriString {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for RelativeIriString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        RelativeIriString::new(s).map_err(serde::de::Error::custom)
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

// RelativeIriStr - RelativeIriStr
impl_cmp!(&'a RelativeIriStr, RelativeIriStr, 'a);
// RelativeIriString - RelativeIriStr
impl_cmp!(RelativeIriString, RelativeIriStr);
impl_cmp!(&'a RelativeIriString, RelativeIriStr, 'a);
impl_cmp!(RelativeIriString, &'a RelativeIriStr, 'a);
// RelativeIriString - RelativeIriString
impl_cmp!(&'a RelativeIriString, RelativeIriString, 'a);
// RelativeIriStr - String
impl_cmp!(RelativeIriStr, String);
impl_cmp!(&'a RelativeIriStr, String, 'a);
impl_cmp!(RelativeIriStr, &'a String, 'a);
// RelativeIriString - str
impl_cmp!(RelativeIriString, str);
impl_cmp!(&'a RelativeIriString, str, 'a);
impl_cmp!(RelativeIriString, &'a str, 'a);
