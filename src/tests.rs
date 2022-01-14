//! Tests that depends on the internal stuff.
//!
//! This module should only be enabled during building tests.

#[cfg(not(test))]
compile_error!("`tests` module should be enable only when `cfg(tests)`");

use core::fmt;

use crate::components::RiReferenceComponents;
use crate::spec::Spec;
use crate::types::RiReferenceStr;

/// Components.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Components<'a> {
    scheme: Option<&'a str>,
    authority: Option<&'a str>,
    path: &'a str,
    query: Option<&'a str>,
    fragment: Option<&'a str>,
}

impl<'a> Components<'a> {
    #[inline]
    #[must_use]
    pub(crate) fn new(
        scheme: Option<&'a str>,
        authority: Option<&'a str>,
        path: &'a str,
        query: Option<&'a str>,
        fragment: Option<&'a str>,
    ) -> Self {
        assert!(
            authority.is_some() || !path.starts_with("//"),
            "when `authority` is absent, `path` should not start with `//`: \
             authority={:?}, path={:?}",
            authority,
            path
        );
        assert!(
            authority.is_none() || (path.is_empty() || path.starts_with('/')),
            "when `authority` is present, `path` should be empty or \
             start with `/`: authority={:?}, path={:?}",
            authority,
            path
        );
        assert!(
            scheme.is_some()
                || authority.is_some()
                || !path
                    .split('/')
                    .next()
                    .map_or(false, |seg| seg.contains(':')),
            "when `scheme` and `authority` is absent, the first segment of \
             `path` should not contain a colon: scheme={:?}, authority={:?}, path={:?}",
            scheme,
            authority,
            path
        );

        Self {
            scheme,
            authority,
            path,
            query,
            fragment,
        }
    }
}

impl fmt::Display for Components<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(scheme) = self.scheme {
            write!(f, "{}:", scheme)?;
        }
        if let Some(authority) = self.authority {
            write!(f, "//{}", authority)?;
        }
        f.write_str(self.path)?;
        if let Some(query) = self.query {
            write!(f, "?{}", query)?;
        }
        if let Some(fragment) = self.fragment {
            write!(f, "#{}", fragment)?;
        }
        Ok(())
    }
}

impl<'a, S: Spec> From<&'a RiReferenceStr<S>> for Components<'a> {
    #[inline]
    fn from(s: &'a RiReferenceStr<S>) -> Self {
        let RiReferenceComponents {
            scheme,
            authority,
            path,
            query,
            fragment,
            _spec,
        } = RiReferenceComponents::from(s);

        Self {
            scheme,
            authority,
            path,
            query,
            fragment,
        }
    }
}

impl PartialEq<&Components<'_>> for Components<'_> {
    #[inline]
    fn eq(&self, other: &&Components<'_>) -> bool {
        self.eq(*other)
    }
}

impl PartialEq<Components<'_>> for &Components<'_> {
    #[inline]
    fn eq(&self, other: &Components<'_>) -> bool {
        (**self).eq(other)
    }
}

/// Bytes buffer that can be writable by `core::fmt::Write`.
pub(crate) struct WritableByteBuffer<'a> {
    buf: &'a mut [u8],
    len: usize,
}

impl<'a> WritableByteBuffer<'a> {
    pub(crate) fn new(buf: &'a mut [u8]) -> Self {
        Self { buf, len: 0 }
    }

    pub(crate) fn clear(&mut self) {
        self.len = 0;
    }

    pub(crate) fn as_str(&self) -> &str {
        core::str::from_utf8(&self.buf[..self.len])
            .expect("data written by `fmt::Write` must be valid UTF-8 sequences")
    }

    fn rest(&mut self) -> &mut [u8] {
        &mut self.buf[self.len..]
    }
}

impl fmt::Write for WritableByteBuffer<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let rest = self.rest();
        if rest.len() < s.len() {
            // Not enough capacity.
            return Err(fmt::Error);
        }
        rest[..s.len()].copy_from_slice(s.as_bytes());
        self.len += s.len();
        Ok(())
    }
}
