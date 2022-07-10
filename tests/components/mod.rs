//! Components.
#![allow(dead_code)]

use core::fmt;

use iri_string::build::Builder;

/// Test case.
#[derive(Debug, Clone, Copy)]
pub struct TestCase<'a> {
    /// Test case name.
    pub name: Option<&'a str>,
    /// Test case description.
    pub description: Option<&'a str>,
    /// Composed string.
    pub composed: &'a str,
    /// Components.
    pub components: Components<'a>,
    /// Normalized string as URI.
    pub normalized_uri: &'a str,
    /// Normalized string as IRI.
    pub normalized_iri: &'a str,
    /// Different IRIs.
    pub different_iris: &'a [&'a str],
}

impl TestCase<'_> {
    #[inline]
    #[must_use]
    pub fn is_uri_class(&self) -> bool {
        self.composed.is_ascii()
    }

    #[inline]
    #[must_use]
    pub const fn is_iri_class(&self) -> bool {
        true
    }

    #[inline]
    #[must_use]
    pub const fn is_absolute(&self) -> bool {
        self.components.is_absolute()
    }

    #[inline]
    #[must_use]
    pub const fn is_absolute_without_fragment(&self) -> bool {
        self.components.is_absolute_without_fragment()
    }

    #[inline]
    #[must_use]
    pub const fn is_relative(&self) -> bool {
        self.components.is_relative()
    }

    #[inline]
    #[must_use]
    pub fn is_rfc3986_normalizable(&self) -> bool {
        match self.normalized_iri.find('/') {
            Some(pos) => !self.normalized_iri[(pos + 1)..].starts_with("./"),
            None => true,
        }
    }
}

/// Components.
#[derive(Default, Debug, Clone, Copy)]
pub struct Components<'a> {
    /// `scheme`.
    pub scheme: Option<&'a str>,
    /// User part (string before the first colon) of `userinfo`.
    ///
    /// Note that `host` should also be `Some(_)` if this is `Some(_)`.
    pub user: Option<&'a str>,
    /// Password part (string after the first colon) of `userinfo`.
    ///
    /// Note that `host` should also be `Some(_)` if this is `Some(_)`.
    pub password: Option<&'a str>,
    /// `host`.
    pub host: Option<&'a str>,
    /// `port`.
    ///
    /// Note that `host` should also be `Some(_)` if this is `Some(_)`.
    pub port: Option<&'a str>,
    /// `path`.
    pub path: &'a str,
    /// `query`.
    pub query: Option<&'a str>,
    /// `fragment`.
    pub fragment: Option<&'a str>,
}

impl<'a> Components<'a> {
    #[inline]
    #[must_use]
    const fn const_default() -> Self {
        Self {
            scheme: None,
            user: None,
            password: None,
            host: None,
            port: None,
            path: "",
            query: None,
            fragment: None,
        }
    }

    pub fn feed_builder(&self, builder: &mut Builder<'a>, clean: bool) {
        if let Some(scheme) = self.scheme {
            builder.scheme(scheme);
        } else if clean {
            builder.unset_scheme();
        }

        if let Some(host) = self.host {
            if self.user.is_some() || self.password.is_some() {
                builder.userinfo((self.user.unwrap_or(""), self.password));
            } else if clean {
                builder.unset_userinfo();
            }

            builder.host(host);

            if let Some(port) = self.port {
                builder.port(port);
            } else if clean {
                builder.unset_port();
            }
        } else if clean {
            builder.unset_authority();
        }

        builder.path(self.path);

        if let Some(query) = self.query {
            builder.query(query);
        } else if clean {
            builder.unset_query();
        }

        if let Some(fragment) = self.fragment {
            builder.fragment(fragment);
        } else if clean {
            builder.unset_fragment();
        }
    }

    #[inline]
    #[must_use]
    pub const fn is_absolute(&self) -> bool {
        self.scheme.is_some()
    }

    #[inline]
    #[must_use]
    pub const fn is_absolute_without_fragment(&self) -> bool {
        self.scheme.is_some() && self.fragment.is_none()
    }

    #[inline]
    #[must_use]
    pub const fn is_relative(&self) -> bool {
        self.scheme.is_none()
    }
}

impl fmt::Display for Components<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(scheme) = self.scheme {
            write!(f, "{scheme}:")?;
        }

        assert!(
            self.host.is_some()
                || (self.user.is_none() && self.password.is_none() && self.port.is_none()),
            "`user`, `password`, and `port` requires `host` to be present"
        );
        if let Some(host) = self.host {
            if let Some(user) = self.user {
                f.write_str(user)?;
            }
            if let Some(password) = self.password {
                write!(f, ":{password}")?;
            }
            if self.user.is_some() || self.password.is_some() {
                write!(f, "@")?;
            }
            f.write_str(host)?;
            if let Some(port) = self.port {
                write!(f, ":{port}")?;
            }
        }

        f.write_str(self.path)?;

        if let Some(query) = self.query {
            write!(f, "#{query}")?;
        }

        if let Some(fragment) = self.fragment {
            write!(f, "#{fragment}")?;
        }

        Ok(())
    }
}

macro_rules! components {
    () => {
        Components::default()
    };
    ($($field:ident: $expr:expr),* $(,)?) => {
        Components {
            $( $field: components!(@field; $field: $expr) ),*,
            .. Components::const_default()
        }
    };
    (@field; path: $expr:expr) => {
        $expr
    };
    (@field; $field:ident: None) => {
        None
    };
    (@field; $field:ident: $expr:expr) => {
        Some($expr)
    };
}

macro_rules! test_case {
    // Name.
    (@field=name; name: $value:expr, $($rest:tt)*) => {
        $value
    };
    // Description.
    (@field=description; description: $value:expr, $($rest:tt)*) => {
        Some($value)
    };
    (@field=description;) => {
        None
    };
    // Composed.
    (@field=composed; composed: $value:expr, $($rest:tt)*) => {
        $value
    };
    // Components.
    (@field=components; components: { $($toks:tt)* }, $($rest:tt)*) => {
        components! { $($toks)* }
    };
    // Normalized URI.
    (@field=normalized_uri; normalized_uri: $value:expr, $($rest:tt)*) => {
        $value
    };
    // Normalized IRI.
    (@field=normalized_iri; normalized_iri: $value:expr, $($rest:tt)*) => {
        $value
    };
    // Different IRIs.
    (@field=different_iris; different_iris: $value:expr, $($rest:tt)*) => {
        $value
    };
    (@field=different_iris;) => {
        &[]
    };
    // Fallback.
    (@field=$name:ident; $field:ident: { $($toks:tt)* }, $($rest:tt)*) => {
        test_case!(@field=$name; $($rest)*)
    };
    // Fallback.
    (@field=$name:ident; $field:ident: $value:expr, $($rest:tt)*) => {
        test_case!(@field=$name; $($rest)*)
    };
    ($($args:tt)*) => {
        TestCase {
            name: Some(test_case!(@field=name; $($args)*)),
            description: test_case!(@field=description; $($args)*),
            composed: test_case!(@field=composed; $($args)*),
            components: test_case!(@field=components; $($args)*),
            normalized_uri: test_case!(@field=normalized_uri; $($args)*),
            normalized_iri: test_case!(@field=normalized_iri; $($args)*),
            different_iris: test_case!(@field=different_iris; $($args)*),
        }
    };
}

macro_rules! test_cases {
    ($({$($toks:tt)*}),* $(,)?) => {
        &[ $( test_case! { $($toks)* } ),* ]
    }
}

#[allow(clippy::needless_update)] // For `components!` macro.
pub static TEST_CASES: &[TestCase<'static>] = test_cases![
    {
        name: "typical example URI",
        composed: "http://example.com/",
        components: {
            scheme: "http",
            host: "example.com",
            path: "/",
        },
        normalized_uri: "http://example.com/",
        normalized_iri: "http://example.com/",
    },
    {
        name: "typical example URI with user and password",
        composed: "http://user:password@example.com/",
        components: {
            scheme: "http",
            user: "user",
            password: "password",
            host: "example.com",
            path: "/",
        },
        normalized_uri: "http://user:password@example.com/",
        normalized_iri: "http://user:password@example.com/",
    },
    {
        name: "URI with ASCII-only hostname with capital letters",
        description: "ASCII-only hostname should be normalized to lower letters",
        composed: "http://usER:passWORD@eXAMPLe.CoM/",
        components: {
            scheme: "http",
            user: "usER",
            password: "passWORD",
            host: "eXAMPLe.CoM",
            path: "/",
        },
        normalized_uri: "http://usER:passWORD@example.com/",
        normalized_iri: "http://usER:passWORD@example.com/",
    },
    {
        name: "IRI with non-ASCII hostname with capital letters",
        description: "hostname with non-ASCII characters should not be normalized to lower letters",
        composed: "http://usER:passWORD@\u{03B1}.CoM/",
        components: {
            scheme: "http",
            user: "usER",
            password: "passWORD",
            host: "\u{03B1}.CoM",
            path: "/",
        },
        // The RFC 3986 (not 3987) spec is ambiguous: if the host contains percent-encoded
        // non-ASCII characters, should other part of the host be lowercased?
        // In this crate for now, the operations is implemented based on RFC 3987, i.e.
        // even URI type internally checks whether the percent-encoded characters
        // would be decoded to ASCII or not.
        normalized_uri: "http://usER:passWORD@%CE%B1.CoM/",
        normalized_iri: "http://usER:passWORD@\u{03B1}.CoM/",
    },
    {
        name: "URI with all components set",
        composed: "http://user:password@example.com:80/path/to/somewhere?query#fragment",
        components: {
            scheme: "http",
            user: "user",
            password: "password",
            host: "example.com",
            port: "80",
            path: "/path/to/somewhere",
            query: "query",
            fragment: "fragment",
        },
        normalized_uri: "http://user:password@example.com:80/path/to/somewhere?query#fragment",
        normalized_iri: "http://user:password@example.com:80/path/to/somewhere?query#fragment",
    },
    {
        name: "URI that cannot be normalized by pure RFC 3986",
        composed: "scheme:/.//not-a-host",
        components: {
            scheme: "scheme",
            path: "/.//not-a-host",
        },
        normalized_uri: "scheme:/.//not-a-host",
        normalized_iri: "scheme:/.//not-a-host",
    },
    {
        name: "URI that cannot be normalized by pure RFC 3986",
        composed: "scheme:..///not-a-host",
        components: {
            scheme: "scheme",
            path: "..///not-a-host",
        },
        normalized_uri: "scheme:/.//not-a-host",
        normalized_iri: "scheme:/.//not-a-host",
    },
    {
        name: "Relative URI reference as a relative path `..`",
        description: "Relative path without scheme and authority should not be normalized",
        composed: "..",
        components: {
            path: "..",
        },
        normalized_uri: "..",
        normalized_iri: "..",
    },
    {
        name: "Relative URI reference as a relative path",
        description: "Relative path without scheme and authority should not be normalized",
        composed: "../foo/..",
        components: {
            path: "../foo/..",
        },
        normalized_uri: "../foo/..",
        normalized_iri: "../foo/..",
    },
    {
        name: "Relative URI reference as a relative path",
        description: "Relative path without scheme and authority should not be normalized",
        composed: "foo/../p%61th",
        components: {
            path: "foo/../p%61th",
        },
        normalized_uri: "foo/../path",
        normalized_iri: "foo/../path",
    },
    {
        name: "Relative path in an absolute URI",
        composed: "scheme:foo/../p%61th",
        components: {
            scheme: "scheme",
            path: "foo/../p%61th",
        },
        normalized_uri: "scheme:/path",
        normalized_iri: "scheme:/path",
    },
    {
        name: "Non-normalized URI",
        composed: "HTTPs://EXaMPLE.COM/pA/Th?Query#Frag",
        components: {
            scheme: "HTTPs",
            host: "EXaMPLE.COM",
            path: "/pA/Th",
            query: "Query",
            fragment: "Frag",
        },
        normalized_uri: "https://example.com/pA/Th?Query#Frag",
        normalized_iri: "https://example.com/pA/Th?Query#Frag",
        different_iris: &[
            "https://example.com/pa/th?Query#Frag",
            "https://example.com/pA/Th?query#Frag",
            "https://example.com/pA/Th?Query#frag",
        ],
    },
    {
        name: "UUID URN",
        composed: "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        components: {
            scheme: "urn",
            path: "uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        },
        normalized_uri: "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        normalized_iri: "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        different_iris: &[
            "urn:UUID:7f1450df-6678-465b-a881-188f9b6ec822",
            "urn:uuid:7F1450DF-6678-465B-A881-188F9B6EC822",
        ],
    },
    {
        name: "UUID URN",
        composed: "URN:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        components: {
            scheme: "URN",
            path: "uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        },
        normalized_uri: "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        normalized_iri: "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        different_iris: &[
            "urn:UUID:7f1450df-6678-465b-a881-188f9b6ec822",
            "urn:uuid:7F1450DF-6678-465B-A881-188F9B6EC822",
        ],
    },
    {
        name: "UUID URN",
        composed: "URN:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        components: {
            scheme: "URN",
            path: "uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        },
        normalized_uri: "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        normalized_iri: "urn:uuid:7f1450df-6678-465b-a881-188f9b6ec822",
        different_iris: &[
            "urn:UUID:7f1450df-6678-465b-a881-188f9b6ec822",
            "urn:uuid:7F1450DF-6678-465B-A881-188F9B6EC822",
        ],
    },
    {
        name: "IRI with percent-encoded unreserved characters and non-valid UTF-8 bytes",
        composed: "http://example.com/?a=%CE%B1&b=%CE%CE%B1%B1",
        components: {
            scheme: "http",
            host: "example.com",
            path: "/",
            query: "a=%CE%B1&b=%CE%CE%B1%B1",
        },
        normalized_uri: "http://example.com/?a=%CE%B1&b=%CE%CE%B1%B1",
        normalized_iri: "http://example.com/?a=\u{03B1}&b=%CE\u{03B1}%B1",
    },
    {
        name: "not ASCII-only host",
        composed: "SCHEME://Alpha%ce%b1/",
        components: {
            scheme: "SCHEME",
            host: "Alpha%ce%b1",
            path: "/",
        },
        normalized_uri: "scheme://Alpha%CE%B1/",
        normalized_iri: "scheme://Alpha\u{03B1}/",
    },
    {
        name: "URI with percent-encoded unreserevd and reserved characters",
        description: "Tilde character (0x7e) is unreserved and bang (0x21) is reserved",
        composed: "http://example.com/%7E%41%73%63%69%69%21",
        components: {
            scheme: "http",
            host: "example.com",
            path: "/%7E%41%73%63%69%69%21",
        },
        normalized_uri: "http://example.com/~Ascii%21",
        normalized_iri: "http://example.com/~Ascii%21",
    },
    {
        name: "not ASCII-only host",
        description: "Plus character (0x2B) is reserved (sub-delim), so it should not be decoded in host part",
        composed: "SCHEME://PLUS%2bPLUS/",
        components: {
            scheme: "SCHEME",
            host: "PLUS%2bPLUS",
            path: "/",
        },
        normalized_uri: "scheme://plus%2Bplus/",
        normalized_iri: "scheme://plus%2Bplus/",
    },
    {
        name: "empty port",
        // <https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2.3>:
        //
        // > URI producers and normalizers should omit the port component
        // > and its ":" delimiter if port is empty or if its value would
        // > be the same as that of the scheme's default.
        description: "According to RFC 3986 section 3.2.3, empty port should be omitted by normalization",
        composed: "https://example.com:/",
        components: {
            scheme: "https",
            host: "example.com",
            port: "",
            path: "/",
        },
        normalized_uri: "https://example.com/",
        normalized_iri: "https://example.com/",
    },
    {
        name: "URI with a dot-dot segment",
        composed: "http://example.com/a/b/c/%2e%2e/d/e",
        components: {
            scheme: "http",
            host: "example.com",
            path: "/a/b/c/%2e%2e/d/e",
        },
        normalized_uri: "http://example.com/a/b/d/e",
        normalized_iri: "http://example.com/a/b/d/e",
    },
    {
        name: "URI with a dot-dot segment",
        composed: "http://example.com/a/b/c/%2E%2E/d/e",
        components: {
            scheme: "http",
            host: "example.com",
            path: "/a/b/c/%2E%2E/d/e",
        },
        normalized_uri: "http://example.com/a/b/d/e",
        normalized_iri: "http://example.com/a/b/d/e",
    },
    {
        name: "URI with a dot-dot segment",
        composed: "http://example.com/a/b/c/../d/e",
        components: {
            scheme: "http",
            host: "example.com",
            path: "/a/b/c/../d/e",
        },
        normalized_uri: "http://example.com/a/b/d/e",
        normalized_iri: "http://example.com/a/b/d/e",
    },
    {
        name: "URI with a dot-dot segment",
        composed: "http://example.com/a/b/c/.%2e/d/e",
        components: {
            scheme: "http",
            host: "example.com",
            path: "/a/b/c/.%2e/d/e",
        },
        normalized_uri: "http://example.com/a/b/d/e",
        normalized_iri: "http://example.com/a/b/d/e",
    },
    {
        name: "URI with dot segments",
        composed: "http://example.com/a/./././././b/c/.%2e/d/e",
        components: {
            scheme: "http",
            host: "example.com",
            path: "/a/./././././b/c/.%2e/d/e",
        },
        normalized_uri: "http://example.com/a/b/d/e",
        normalized_iri: "http://example.com/a/b/d/e",
    },
];
