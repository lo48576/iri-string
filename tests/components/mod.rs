//! Components.

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
                builder.userinfo((self.user, self.password));
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

macro_rules! test_cases {
    ($({$($toks:tt)*}),* $(,)?) => {
        &[ $( test_case! { $($toks)* } ),* ]
    }
}

macro_rules! test_case {
    // With description.
    (
        name: $name:expr,
        description: $description:expr,
        composed: $composed:expr,
        components: { $($components:tt)* },
        normalized_uri: $normalized_uri:expr,
        normalized_iri: $normalized_iri:expr,
    ) => {
        TestCase {
            name: Some($name),
            description: Some($description),
            composed: $composed,
            components: components! { $($components)* },
            normalized_uri: $normalized_uri,
            normalized_iri: $normalized_iri,
        }
    };
    // Without description.
    (
        name: $name:expr,
        composed: $composed:expr,
        components: { $($components:tt)* },
        normalized_uri: $normalized_uri:expr,
        normalized_iri: $normalized_iri:expr,
    ) => {
        TestCase {
            name: Some($name),
            description: None,
            composed: $composed,
            components: components! { $($components)* },
            normalized_uri: $normalized_uri,
            normalized_iri: $normalized_iri,
        }
    };
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
];
