//! URI and IRI types.
//!
//! # URI and IRI
//!
//! IRIs (Internationalized Resource Identifiers) are defined in [RFC 3987],
//! and URIs (Uniform Resource Identifiers) are defined in [RFC 3986].
//!
//! URI consists of only ASCII characters, and is a subset of IRI.
//!
//! IRIs are defined as below:
//!
//! ```text
//! IRI           = scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]
//! IRI-reference = IRI / irelative-ref
//! absolute-IRI  = scheme ":" ihier-part [ "?" iquery ]
//! irelative-ref = irelative-part [ "?" iquery ] [ "#" ifragment ]
//!     (`irelative-part` is roughly same as `ihier-part`.)
//! ```
//!
//! Definitions for URIs are almost same, but they cannot have non-ASCII characters.
//!
//! # Types
//!
//! Types can be categorized by:
//!
//! * syntax,
//! * spec, and
//! * ownership.
//!
//! ## Syntax
//!
//! Since URIs and IRIs have almost same syntax and share algorithms, they are implemented by
//! generic types.
//!
//! * [`RiStr`] and [`RiString`]
//!     + String types for `IRI` and `URI` rules.
//! * [`RiAbsoluteStr`] and [`RiAbsoluteString`]
//!     + String types for `absolute-IRI` and `absolute-URI` rules.
//! * [`RiReferenceStr`] and [`RiReferenceString`]
//!     + String types for `IRI-reference` and `URI-reference` rules.
//! * [`RiRelativeStr`] and [`RiRelativeString`]
//!     + String types for `irelative-ref` and `relative-ref` rules.
//! * [`RiFragmentStr`] and [`RiFragmentString`]
//!     + String types for `ifragment` and `fragment` rules.
//!     + Note that these types represents a substring of an IRI / URI references.
//!       They are not intended to used directly as an IRI / URI references.
//!
//! "Ri" stands for "Resource Identifier".
//!
//! ## Spec
//!
//! These types have a type parameter, which represents RFC specification.
//! [`IriSpec`] represents [RFC 3987] spec, and [`UriSpec`] represents [RFC 3986] spec.
//! For example, `RiAbsoluteStr<IriSpec>` can have `absolute-IRI` string value,
//! and `RiReferenceStr<UriSpec>` can have `URI-reference` string value.
//!
//! ## Ownership
//!
//! String-like types have usually two variations, borrowed and owned.
//!
//! Borrowed types (such as `str`, `Path`, `OsStr`) are unsized, and used by reference style.
//! Owned types (such as `String`, `PathBuf`, `OsString`) are sized, and requires heap allocation.
//! Owned types can be coerced to a borrowed type (for example, `&String` is automatically coerced
//! to `&str` in many context).
//!
//! IRI / URI types have same variations, `RiFooStr` and `RiFooString`
//! (`Foo` part represents syntax).
//! They are very similar to `&str` and `String`.
//! `Deref` is implemented, `RiFooStr::len()` is available, `&RiFooString` can be coerced to
//! `&RiFooStr`, `Cow<'_, RiFooStr>` and `Box<RiFooStr>` is available, and so on.
//!
//! # Hierarchy and safe conversion
//!
//! IRI syntaxes have the hierarchy below.
//!
//! ```text
//! RiReferenceStr
//! |-- RiStr
//! |   `-- RiAbsoluteStr
//! `-- RiRelativeStr
//! ```
//!
//! Therefore, the conversions below are safe and cheap:
//!
//! * `RiStr -> RiReferenceStr`
//! * `RiAbsoluteStr -> RiStr`
//! * `RiAbsoluteStr -> RiReferenceStr`
//! * `RiRelativeStr -> RiReferenceStr`
//!
//! For safely convertible types (consider `FooStr -> BarStr` is safe), traits
//! below are implemented:
//!
//! * `AsRef<BarStr> for FooStr`
//! * `AsRef<BarStr> for FooString`
//! * `From<FooString> for BarString`
//! * `PartialEq<FooStr> for BarStr`, and lots of impls like that
//!     + `PartialEq` and `ParitalOrd`.
//!     + Slice, owned, `Cow`, reference, etc...
//!
//! ## Fallible conversions
//!
//! Fallible conversions are implemented from plain string into IRI strings.
//!
//! * `TryFrom<&str> for &FooStr`
//! * `TryFrom<&str> for FooString`
//! * `TryFrom<String> for FooString`
//! * `FromStr for FooString`
//!
//! Some IRI string types provide more convenient methods to convert between IRI types.
//! For example, [`RiReferenceString::into_iri()`] tries to convert an IRI reference into an IRI,
//! and returns `Result<IriString, IriRelativeString>`.
//! This is because an IRI reference is valid as an IRI or a relative IRI reference.
//! Such methods are usually more efficient than using `TryFrom` for plain strings, because they
//! prevents you from losing ownership of a string, and does a conversion without extra memory
//! allocation.
//!
//! # Aliases
//!
//! This module contains type aliases for RFC 3986 URI types and RFC 3987 IRI types.
//!
//! `IriFooStr{,ing}` are aliases of `RiFooStr{,ing}<IriSpec>`, and `UriFooStr{,ing}` are aliases
//! of `RiFooStr{,ing}<UriSpec>`.
//!
//! # Wrapped string types
//!
//! Similar to string types in std (such as `str`, `std::path::Path`, and `std::ffi::OsStr`),
//! IRI string types in this crate provides convenient conversions to:
//!
//! * `std::box::Box`,
//! * `std::borrow::Cow`,
//! * `std::rc::Rc`, and
//! * `std::sync::Arc`.
//!
//! ```
//! # use iri_string::validate::Error;
//! # #[cfg(feature = "std")] {
//! use std::borrow::Cow;
//! use std::rc::Rc;
//! use std::sync::Arc;
//!
//! use iri_string::types::IriStr;
//!
//! let iri = IriStr::new("http://example.com/")?;
//! let iri_owned = iri.to_owned();
//!
//! // From slice.
//! let cow_1_1: Cow<'_, IriStr> = iri.into();
//! let cow_1_2 = Cow::<'_, IriStr>::from(iri);
//! assert!(matches!(cow_1_1, Cow::Borrowed(_)));
//! assert!(matches!(cow_1_2, Cow::Borrowed(_)));
//! // From owned.
//! let cow_2_1: Cow<'_, IriStr> = iri_owned.clone().into();
//! let cow_2_2 = Cow::<'_, IriStr>::from(iri_owned.clone());
//! assert!(matches!(cow_2_1, Cow::Owned(_)));
//! assert!(matches!(cow_2_2, Cow::Owned(_)));
//!
//! // From slice.
//! let box_1_1: Box<IriStr> = iri.into();
//! let box_1_2 = Box::<IriStr>::from(iri);
//! // From owned.
//! let box_2_1: Box<IriStr> = iri_owned.clone().into();
//! let box_2_2 = Box::<IriStr>::from(iri_owned.clone());
//!
//! // From slice.
//! let rc_1_1: Rc<IriStr> = iri.into();
//! let rc_1_2 = Rc::<IriStr>::from(iri);
//! // From owned.
//! // Note that `From<owned> for Rc<borrowed>` is not implemented for now.
//! // Get borrowed string by `.as_slice()` and convert it.
//! let rc_2_1: Rc<IriStr> = iri_owned.clone().as_slice().into();
//! let rc_2_2 = Rc::<IriStr>::from(iri_owned.clone().as_slice());
//!
//! // From slice.
//! let arc_1_1: Arc<IriStr> = iri.into();
//! let arc_1_2 = Arc::<IriStr>::from(iri);
//! // From owned.
//! // Note that `From<owned> for Arc<borrowed>` is not implemented for now.
//! // Get borrowed string by `.as_slice()` and convert it.
//! let arc_2_1: Arc<IriStr> = iri_owned.clone().as_slice().into();
//! let arc_2_2 = Arc::<IriStr>::from(iri_owned.clone().as_slice());
//! # }
//! # Ok::<_, Error>(())
//! ```
//!
//! # IDNA encoding
//!
//! This crate does not have built-in IDNA converter, but the user can provide
//! such conversion function and replace the domain part of IRIs.
//!
//! ## Slice IRI types
//!
//! 1. Get host by `authority_components()?.host()`.
//! 2. Process the name.
//! 3. Create a builder by `Builder::from(&...)`.
//! 4. Overwrite the domain by `.host(...)`.
//! 5. Build the new IRI by `.build()`.
//!
//! ```
//! # #[cfg(feature = "alloc")] extern crate alloc;
//! # #[cfg(feature = "alloc")] use alloc::string::ToString;
//! use iri_string::build::Builder;
//! use iri_string::types::{IriStr, UriStr};
//!
//! struct IdnaEncodedDomain<'a> {
//!     /* ... */
//! #   raw: &'a str,
//! }
//! impl IdnaEncodedDomain<'_> {
//!     pub fn as_str(&self) -> &str {
//!         /* ... */
//! #       match self.raw {
//! #           "alpha.\u{03B1}.example.com" => "alpha.xn--mxa.example.com",
//! #           _ => unimplemented!(),
//! #       }
//!     }
//! }
//! // Usually IDNA conversion requires dynamic memory allocation, but
//! // `iri-string` itself does not require or assume that. It is enough if the
//! // conversion result can be retrieved as `&str`, so users can do whatever
//! // such as limiting the possible input and/or using statically allocated buffer.
//! fn apply_idna(s: &str) -> IdnaEncodedDomain<'_> {
//!     /* ... */
//! #   IdnaEncodedDomain { raw: s }
//! }
//!
//! let orig_iri = IriStr::new("https://alpha.\u{03B1}.example.com").unwrap();
//!
//! // 1. Get the host.
//! let orig_host = orig_iri.authority_components()
//!     .expect("orig_iri has a host")
//!     .host();
//! debug_assert_eq!(orig_host, "alpha.\u{03B1}.example.com");
//!
//! // 2. Process the name.
//! let new_domain = apply_idna(orig_host);
//!
//! // 3. Create a builder.
//! let mut builder = Builder::from(orig_iri);
//!
//! // 4. Overwrite the domain.
//! builder.host(new_domain.as_str());
//!
//! // 5. Build the new IRI.
//! let new_iri = builder.build::<UriStr>()
//!     .expect("the new host is a valid domain and now they are US-ASCII only");
//!
//! // Note that `ToString::to_string()` requires `alloc` feature.
//! #[cfg(feature = "alloc")]
//! debug_assert_eq!(new_iri.to_string(), "https://alpha.xn--mxa.example.com");
//! ```
//!
//! ## Allocated IRI types
//!
//! For allocated types such as `IriString`, you can use
//! `{,try_}replace_host{,_reg_name}` methods.
//!
//! 1. Get host by `authority_components()?.host()`.
//! 2. Process the name.
//! 3. Replace the host by the new result.
//!
//! ```
//! # #[cfg(feature = "alloc")] {
//! # extern crate alloc;
//! # use alloc::string::String;
//! use iri_string::types::IriString;
//!
//! fn apply_idna(s: &str) -> String {
//!     /* ... */
//! #   match s {
//! #       "alpha.\u{03B1}.example.com" => "alpha.xn--mxa.example.com".to_owned(),
//! #       _ => unimplemented!(),
//! #   }
//! }
//!
//! let mut iri =
//!     IriString::try_from("https://alpha.\u{03B1}.example.com")
//!         .unwrap();
//!
//! // 1. Get the host.
//! let orig_host = iri.authority_components()
//!     .expect("orig_iri has a host")
//!     .host();
//! debug_assert_eq!(orig_host, "alpha.\u{03B1}.example.com");
//!
//! // 2. Process the name.
//! let new_domain = apply_idna(orig_host);
//!
//! // 3. Replace the host.
//! iri.replace_host(&new_domain);
//! debug_assert_eq!(iri, "https://alpha.xn--mxa.example.com");
//! # }
//! ```
//!
//! [RFC 3986]: https://www.rfc-editor.org/rfc/rfc3986.html
//! [RFC 3987]: https://www.rfc-editor.org/rfc/rfc3987.html
//! [`RiStr`]: struct.RiStr.html
//! [`RiString`]: struct.RiString.html
//! [`RiAbsoluteStr`]: struct.RiAbsoluteStr.html
//! [`RiAbsoluteString`]: struct.RiAbsoluteString.html
//! [`RiFragmentStr`]: struct.RiFragmentStr.html
//! [`RiFragmentString`]: struct.RiFragmentString.html
//! [`RiReferenceStr`]: struct.RiReferenceStr.html
//! [`RiReferenceString`]: struct.RiReferenceString.html
//! [`RiReferenceString::into_iri()`]: struct.RiReferenceString.html#method.into_iri
//! [`RiRelativeStr`]: struct.RiRelativeStr.html
//! [`RiRelativeString`]: struct.RiRelativeString.html
//! [`IriSpec`]: ../spec/enum.IriSpec.html
//! [`UriSpec`]: ../spec/enum.UriSpec.html

#[cfg(feature = "alloc")]
pub use self::{
    generic::{
        CreationError, RiAbsoluteString, RiFragmentString, RiQueryString, RiReferenceString,
        RiRelativeString, RiString,
    },
    iri::{
        IriAbsoluteString, IriFragmentString, IriQueryString, IriReferenceString,
        IriRelativeString, IriString,
    },
    uri::{
        UriAbsoluteString, UriFragmentString, UriQueryString, UriReferenceString,
        UriRelativeString, UriString,
    },
};
pub use self::{
    generic::{RiAbsoluteStr, RiFragmentStr, RiQueryStr, RiReferenceStr, RiRelativeStr, RiStr},
    iri::{IriAbsoluteStr, IriFragmentStr, IriQueryStr, IriReferenceStr, IriRelativeStr, IriStr},
    uri::{UriAbsoluteStr, UriFragmentStr, UriQueryStr, UriReferenceStr, UriRelativeStr, UriStr},
};

pub(crate) mod generic;
mod iri;
mod uri;
