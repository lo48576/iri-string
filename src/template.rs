//! Processor for [RFC 6570] URI Template.
//!
//! [RFC 6570]: https://www.rfc-editor.org/rfc/rfc6570.html
//!
//! # Usage
//!
//! 1. Prepare a template.
//!     * Template type is [`UriTemplateStr`] (borrowed) and [`UriTemplateString`] (owned).
//! 2. Prepare a context.
//!     * Insert key-value pairs into a [`Context`].
//! 3. Expand.
//!     * Pass the context to [`UriTemplateStr::expand`] method of the template.
//! 4. Use the result.
//!     * Returned [`Expanded`] object can be directly printed since it
//!       implements [`Display`][`core::fmt::Display`] trait. Or, you can call
//!       [`.to_string()`][`alloc::string::ToString`] method to convert it to
//!       a `String`.
//!
//! # Examples
//!
//! ```
//! # use iri_string::template::Error;
//! use iri_string::spec::{IriSpec, UriSpec};
//! use iri_string::template::{Context, UriTemplateStr};
//!
//! let mut context = Context::new();
//! context.insert("username", "foo");
//! // U+2713 CHECK MARK
//! context.insert("utf8", "\u{2713}");
//!
//! let template = UriTemplateStr::new("/users/{username}{?utf8}")?;
//!
//! assert_eq!(
//!     template.expand::<UriSpec>(&context)?.to_string(),
//!     "/users/foo?utf8=%E2%9C%93"
//! );
//! assert_eq!(
//!     template.expand::<IriSpec>(&context)?.to_string(),
//!     "/users/foo?utf8=\u{2713}"
//! );
//! # Ok::<_, Error>(())
//! ```
mod components;
mod error;
mod expand;
mod parser;
mod string;

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use self::components::VarName;
pub use self::error::{CreationError, Error};
pub use self::expand::Expanded;
pub use self::string::{UriTemplateStr, UriTemplateString};

/// Value.
#[derive(Debug, Clone)]
pub enum Value {
    /// Undefined (i.e. null).
    Undefined,
    /// String value.
    String(String),
    /// List.
    List(Vec<String>),
    /// Associative array.
    Assoc(Vec<(String, String)>),
}

impl From<&str> for Value {
    #[inline]
    fn from(v: &str) -> Self {
        Self::String(v.into())
    }
}

impl From<String> for Value {
    #[inline]
    fn from(v: String) -> Self {
        Self::String(v)
    }
}

/// Template expansion context.
#[derive(Default, Debug, Clone)]
pub struct Context {
    /// Variable values.
    // Any map types (including `HashMap`) is ok, but the hash map is not provided by `alloc`.
    //
    // QUESTION: Should hexdigits in percent-encoded triplets in varnames be
    // compared case sensitively?
    variables: BTreeMap<String, Value>,
}

impl Context {
    /// Creates a new empty context.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::spec::UriSpec;
    /// use iri_string::template::{Context, UriTemplateStr};
    ///
    /// let empty_ctx = Context::new();
    /// let template = UriTemplateStr::new("{no_such_variable}")?;
    /// let expanded = template.expand::<UriSpec>(&empty_ctx)?;
    ///
    /// assert_eq!(
    ///     expanded.to_string(),
    ///     ""
    /// );
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts a variable.
    ///
    /// Passing [`Value::Undefined`] removes the value from the context.
    ///
    /// The entry will be inserted or removed even if the key is invalid as a
    /// variable name. Such entries will be simply ignored on expansion.
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
    /// Passing [`Value::Undefined`] removes the value from the context.
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::spec::UriSpec;
    /// use iri_string::template::{Context, UriTemplateStr, Value};
    ///
    /// let mut context = Context::new();
    /// context.insert("username", "foo");
    /// context.insert("username", Value::Undefined);
    ///
    /// let template = UriTemplateStr::new("/users/{username}")?;
    /// let expanded = template.expand::<UriSpec>(&context)?;
    ///
    /// assert_eq!(
    ///     expanded.to_string(),
    ///     "/users/"
    /// );
    /// # Ok::<_, Error>(())
    /// ```
    pub fn insert<K, V>(&mut self, key: K, value: V) -> Option<Value>
    where
        K: Into<String>,
        V: Into<Value>,
    {
        let key = key.into();
        match value.into() {
            Value::Undefined => self.variables.remove(&key),
            value => self.variables.insert(key, value),
        }
    }

    /// Removes all entries in the context.
    ///
    /// # Examples
    ///
    /// ```
    /// # use iri_string::template::Error;
    /// use iri_string::spec::UriSpec;
    /// use iri_string::template::{Context, UriTemplateStr};
    ///
    /// let template = UriTemplateStr::new("{foo,bar}")?;
    /// let mut context = Context::new();
    ///
    /// context.insert("foo", "FOO");
    /// context.insert("bar", "BAR");
    /// assert_eq!(
    ///     template.expand::<UriSpec>(&context)?.to_string(),
    ///     "FOO,BAR"
    /// );
    ///
    /// context.clear();
    /// assert_eq!(
    ///     template.expand::<UriSpec>(&context)?.to_string(),
    ///     ""
    /// );
    /// # Ok::<_, Error>(())
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.variables.clear();
    }

    /// Returns a reference to the value for the key.
    //
    // QUESTION: Should hexdigits in percent-encoded triplets in varnames be
    // compared case sensitively?
    #[inline]
    #[must_use]
    fn get(&self, key: VarName<'_>) -> Option<&Value> {
        self.variables.get(key.as_str())
    }
}
