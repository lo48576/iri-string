//! Expansion.

use core::cmp::Ordering;
use core::fmt::{self, Display as _, Write as _};
use core::marker::PhantomData;
use core::mem;

use crate::parser::char::is_utf8_byte_continue;
use crate::parser::str::{
    find_split, find_split_hole, starts_with_double_hexdigits, take_first_char,
};
use crate::parser::trusted::take_xdigits2;
use crate::percent_encode::PercentEncoded;
use crate::spec::Spec;
use crate::template::components::{ExprBody, Modifier, Operator};
use crate::template::error::{Error, ErrorKind};
use crate::template::{Context, UriTemplateStr, Value};

/// A chunk in a template string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Chunk<'a> {
    /// Literal.
    Literal(&'a str),
    /// Expression excluding the wrapping braces.
    Expr(ExprBody<'a>),
}

/// Iterator of template chunks.
#[derive(Debug, Clone)]
struct Chunks<'a> {
    /// Template.
    template: &'a str,
}

impl<'a> Chunks<'a> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    fn new(template: &'a UriTemplateStr) -> Self {
        Self {
            template: template.as_str(),
        }
    }
}

impl<'a> Iterator for Chunks<'a> {
    type Item = Chunk<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.template.is_empty() {
            return None;
        }
        match find_split(self.template, b'{') {
            Some(("", _)) => {
                let (expr_body, rest) = find_split_hole(&self.template[1..], b'}')
                    .expect("[validity] expression inside a template must be closed");
                self.template = rest;
                Some(Chunk::Expr(ExprBody::new(expr_body)))
            }
            Some((lit, rest)) => {
                self.template = rest;
                Some(Chunk::Literal(lit))
            }
            None => Some(Chunk::Literal(mem::take(&mut self.template))),
        }
    }
}

/// Template expansion result.
#[derive(Debug, Clone, Copy)]
pub struct Expanded<'a, S> {
    /// Compiled template.
    template: &'a UriTemplateStr,
    /// Context.
    context: &'a Context,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<'a, S: Spec> Expanded<'a, S> {
    /// Creates a new `Expanded` object.
    #[inline]
    pub(super) fn new(template: &'a UriTemplateStr, context: &'a Context) -> Result<Self, Error> {
        Self::typecheck_context(template, context)?;
        Ok(Self {
            template,
            context,
            _spec: PhantomData,
        })
    }

    /// Checks the types of variables are allowed for the corresponding expressions in the template.
    fn typecheck_context(template: &UriTemplateStr, context: &Context) -> Result<(), Error> {
        let mut pos = 0;
        for chunk in Chunks::new(template) {
            let (_op, varlist) = match chunk {
                Chunk::Expr(expr_body) => expr_body.decompose(),
                Chunk::Literal(lit) => {
                    pos += lit.len();
                    continue;
                }
            };
            for varspec in varlist {
                let name = varspec.name();
                let value = context.get(name).unwrap_or(&Value::Undefined);
                let modifier = varspec.modifier();

                if matches!(modifier, Modifier::MaxLen(_))
                    && matches!(value, Value::List(_) | Value::Assoc(_))
                {
                    // > Prefix modifiers are not applicable to variables that
                    // > have composite values.
                    //
                    // --- [RFC 6570 Section 2.4.1. Prefix](https://www.rfc-editor.org/rfc/rfc6570.html#section-2.4.1)
                    return Err(Error::new(ErrorKind::UnexpectedValueType, pos));
                }
            }
        }
        Ok(())
    }
}

impl<S: Spec> fmt::Display for Expanded<'_, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in Chunks::new(self.template) {
            let expr = match chunk {
                Chunk::Literal(lit) => {
                    f.write_str(lit)?;
                    continue;
                }
                Chunk::Expr(body) => body,
            };
            expand::<S>(f, expr, self.context)?;
        }

        Ok(())
    }
}

/// Properties of an operator.
///
/// See [RFC 6570 Appendix A](https://www.rfc-editor.org/rfc/rfc6570#appendix-A).
#[derive(Debug, Clone, Copy)]
struct OpProps {
    /// Prefix for the first element.
    first: &'static str,
    /// Separator.
    sep: &'static str,
    /// Whether or not the expansion includes the variable or key name.
    named: bool,
    /// Result string if the variable is empty.
    ifemp: &'static str,
    /// Whether or not the reserved values can be written without being encoded.
    allow_reserved: bool,
}

impl OpProps {
    /// Properties for all known operators.
    const PROPS: [Self; 8] = [
        // String
        Self {
            first: "",
            sep: ",",
            named: false,
            ifemp: "",
            allow_reserved: false,
        },
        // Reserved
        Self {
            first: "",
            sep: ",",
            named: false,
            ifemp: "",
            allow_reserved: true,
        },
        // Fragment
        Self {
            first: "#",
            sep: ",",
            named: false,
            ifemp: "",
            allow_reserved: true,
        },
        // Label
        Self {
            first: ".",
            sep: ".",
            named: false,
            ifemp: "",
            allow_reserved: false,
        },
        // PathSegments
        Self {
            first: "/",
            sep: "/",
            named: false,
            ifemp: "",
            allow_reserved: false,
        },
        // PathParams
        Self {
            first: ";",
            sep: ";",
            named: true,
            ifemp: "",
            allow_reserved: false,
        },
        // FormQuery
        Self {
            first: "?",
            sep: "&",
            named: true,
            ifemp: "=",
            allow_reserved: false,
        },
        // FormQueryCont
        Self {
            first: "&",
            sep: "&",
            named: true,
            ifemp: "=",
            allow_reserved: false,
        },
    ];

    /// Returns the properties for the operator.
    #[must_use]
    #[inline]
    fn from_op(op: Operator) -> &'static Self {
        let index = match op {
            Operator::String => 0,
            Operator::Reserved => 1,
            Operator::Fragment => 2,
            Operator::Label => 3,
            Operator::PathSegments => 4,
            Operator::PathParams => 5,
            Operator::FormQuery => 6,
            Operator::FormQueryCont => 7,
        };
        &Self::PROPS[index]
    }
}

/// Expands the variable using the given operator.
fn expand<S: Spec>(
    f: &mut fmt::Formatter<'_>,
    expr: ExprBody<'_>,
    context: &Context,
) -> fmt::Result {
    let (op, varlist) = expr.decompose();
    let oppr = OpProps::from_op(op);

    let mut is_first_varspec = true;
    for varspec in varlist {
        let name = varspec.name();
        // RFC 6570 section 2.3:
        //
        // > A variable defined as a list value is considered undefined if the
        // > list contains zero members.  A variable defined as an associative
        // > array of (name, value) pairs is considered undefined if the array
        // > contains zero members or if all member names in the array are
        // > associated with undefined values.
        let value = match context.get(name) {
            Some(Value::List(list)) if list.is_empty() => &Value::Undefined,
            Some(Value::Assoc(assoc)) if assoc.is_empty() => &Value::Undefined,
            Some(v) => v,
            None => &Value::Undefined,
        };
        match value {
            Value::Undefined => continue,
            Value::List(list) => {
                if !oppr.named && list.is_empty() {
                    continue;
                }
            }
            Value::Assoc(assoc) => {
                if !oppr.named && assoc.is_empty() {
                    continue;
                }
            }
            _ => {}
        }

        if mem::replace(&mut is_first_varspec, false) {
            f.write_str(oppr.first)?;
        } else {
            f.write_str(oppr.sep)?;
        }

        let modifier = varspec.modifier();
        match value {
            Value::Undefined => unreachable!("[consistency] undef is already processed"),
            Value::String(s) => {
                if oppr.named {
                    f.write_str(name.as_str())?;
                    if s.is_empty() {
                        f.write_str(oppr.ifemp)?;
                        continue;
                    }
                    f.write_char('=')?;
                }

                let max_len = match modifier {
                    Modifier::None | Modifier::Explode => None,
                    Modifier::MaxLen(max_len) => Some(max_len),
                };
                escape_write_with_maxlen::<S>(f, s, oppr.allow_reserved, max_len)?;
                continue;
            }
            _ => {}
        }
        if !matches!(modifier, Modifier::Explode) {
            if oppr.named {
                f.write_str(name.as_str())?;
                let is_empty = match value {
                    Value::List(list) => list.is_empty(),
                    Value::Assoc(assoc) => assoc.is_empty(),
                    Value::Undefined | Value::String(_) => {
                        unreachable!("[consistency] undef and string are already processed")
                    }
                };
                if is_empty {
                    f.write_str(oppr.ifemp)?;
                    continue;
                }
                f.write_char('=')?;
            }
            match value {
                Value::List(list) => {
                    let mut is_following = false;
                    for item in list {
                        if mem::replace(&mut is_following, true) {
                            f.write_char(',')?;
                        }
                        escape_write::<S>(f, item, oppr.allow_reserved)?;
                    }
                }
                Value::Assoc(assoc) => {
                    let mut is_following = false;
                    for (key, value) in assoc {
                        if mem::replace(&mut is_following, true) {
                            f.write_char(',')?;
                        }
                        escape_write::<S>(f, key, oppr.allow_reserved)?;
                        f.write_char(',')?;
                        escape_write::<S>(f, value, oppr.allow_reserved)?;
                    }
                }
                Value::Undefined | Value::String(_) => {
                    unreachable!("[consistency] undef and string are already processed")
                }
            }
            continue;
        }

        debug_assert!(
            matches!(modifier, Modifier::Explode),
            "[consistency] non-explode expr is already processed"
        );
        if oppr.named {
            match value {
                Value::List(list) => {
                    let mut is_following = false;
                    for item in list {
                        if mem::replace(&mut is_following, true) {
                            f.write_str(oppr.sep)?;
                        }
                        f.write_str(name.as_str())?;
                        if item.is_empty() {
                            f.write_str(oppr.ifemp)?;
                        } else {
                            f.write_char('=')?;
                            escape_write::<S>(f, item, oppr.allow_reserved)?;
                        }
                    }
                }
                Value::Assoc(assoc) => {
                    let mut is_following = false;
                    for (key, value) in assoc {
                        if mem::replace(&mut is_following, true) {
                            f.write_str(oppr.sep)?;
                        }
                        escape_write::<S>(f, key, oppr.allow_reserved)?;
                        if value.is_empty() {
                            f.write_str(oppr.ifemp)?;
                        } else {
                            f.write_char('=')?;
                            escape_write::<S>(f, value, oppr.allow_reserved)?;
                        }
                    }
                }
                Value::Undefined | Value::String(_) => {
                    unreachable!("[consistency] undef and string are already processed")
                }
            }
        } else {
            debug_assert!(!oppr.named, "[consistency] branch condition");
            match value {
                Value::List(list) => {
                    let mut is_following = false;
                    for item in list {
                        if mem::replace(&mut is_following, true) {
                            f.write_str(oppr.sep)?;
                        }
                        escape_write::<S>(f, item, oppr.allow_reserved)?;
                    }
                }
                Value::Assoc(assoc) => {
                    let mut is_following = false;
                    for (key, value) in assoc {
                        if mem::replace(&mut is_following, true) {
                            f.write_str(oppr.sep)?;
                        }
                        escape_write::<S>(f, key, oppr.allow_reserved)?;
                        f.write_char('=')?;
                        escape_write::<S>(f, value, oppr.allow_reserved)?;
                    }
                }
                Value::Undefined | Value::String(_) => {
                    unreachable!("[consistency] undef and string are already processed")
                }
            }
        }
    }

    Ok(())
}

/// Escapes the given string value, trims with the max length, and writes it.
#[inline]
fn escape_write_with_maxlen<S: Spec>(
    f: &mut fmt::Formatter<'_>,
    s: &str,
    allow_reserved: bool,
    max_len: Option<u16>,
) -> fmt::Result {
    if allow_reserved {
        let max_len = max_len.map_or(usize::MAX, usize::from);
        MaybeEncodedChars::new(s).take(max_len).try_for_each(|s| {
            if s.starts_with('%') {
                if s.len() == 1 {
                    // Stray `%`.
                    f.write_str("%25")
                } else {
                    // Valid percent-encoded triplets.
                    f.write_str(s)
                }
            } else {
                PercentEncoded::<_, S>::characters(s).fmt(f)
            }
        })
    } else {
        let trimmed = match max_len {
            Some(max_len) => {
                let mut chars = s.chars();
                chars.by_ref().take(usize::from(max_len)).for_each(|_| ());
                let len = s.len() - chars.as_str().len();
                &s[..len]
            }
            None => s,
        };
        PercentEncoded::<_, S>::unreserve(trimmed).fmt(f)
    }
}

/// Escapes the given string value and writes it.
#[inline]
fn escape_write<S: Spec>(f: &mut fmt::Formatter<'_>, s: &str, allow_reserved: bool) -> fmt::Result {
    if allow_reserved {
        MaybeEncodedChars::new(s).try_for_each(|s| {
            if s.starts_with('%') {
                if s.len() == 1 {
                    // Stray `%`.
                    f.write_str("%25")
                } else {
                    // Valid percent-encoded triplets.
                    f.write_str(s)
                }
            } else {
                PercentEncoded::<_, S>::characters(s).fmt(f)
            }
        })
    } else {
        PercentEncoded::<_, S>::unreserve(s).fmt(f)
    }
}

/// Iterator of characters in a string possibly with percent-encoded triplets and stray `%`.
#[derive(Debug, Clone)]
struct MaybeEncodedChars<'a> {
    /// Remaining input.
    rest: &'a str,
    /// The number of percent-encoded triplets undecodable to valid UTF-8 sequence.
    num_undecodable_pct_triplets: usize,
}

impl<'a> MaybeEncodedChars<'a> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    fn new(s: &'a str) -> Self {
        Self {
            rest: s,
            num_undecodable_pct_triplets: 0,
        }
    }
}

impl<'a> Iterator for MaybeEncodedChars<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.rest.is_empty() {
            return None;
        }
        if self.num_undecodable_pct_triplets > 0 {
            self.num_undecodable_pct_triplets -= 1;
            let (prefix, suffix) = self.rest.split_at(3);
            self.rest = suffix;
            return Some(prefix);
        }

        let after_pct = match self.rest.strip_prefix('%') {
            Some(v) => v,
            None => {
                // Get the position of the next char of the last char.
                let pos = self
                    .rest
                    .char_indices()
                    .nth(1)
                    .map_or_else(|| self.rest.len(), |(i, _c)| i);
                let (prefix, suffix) = self.rest.split_at(pos);
                self.rest = suffix;
                return Some(prefix);
            }
        };

        // Check if it is the part of a valid percent-encoded triplet.
        if !starts_with_double_hexdigits(after_pct.as_bytes()) {
            // Stray `%` found.
            let pct = &self.rest[..1];
            self.rest = after_pct;
            return Some(pct);
        }

        let (first_decoded, after_triplet) = take_xdigits2(after_pct);
        if first_decoded.is_ascii() {
            // Encoded ASCII character found.
            let encoded_ascii = &self.rest[..3];
            self.rest = after_triplet;
            return Some(encoded_ascii);
        }

        // Get the expected length of decoded char.
        let expected_char_len = match (first_decoded & 0xf0).cmp(&0b1110_0000) {
            Ordering::Less => 2,
            Ordering::Equal => 3,
            Ordering::Greater => 4,
        };

        // Get continue bytes.
        let mut rest = after_triplet;
        let c_buf = &mut [first_decoded, 0, 0, 0][..expected_char_len];
        let before_pct_seqs = rest;
        for (i, buf_dest) in c_buf[1..].iter_mut().enumerate() {
            match take_first_char(rest) {
                Some(('%', after_percent)) => {
                    let (byte, after_triplet) = take_xdigits2(after_percent);
                    if !is_utf8_byte_continue(byte) {
                        // Note that `byte` can start the new string.
                        // Leave the byte in the `rest` for next try (i.e.
                        // don't buffer the current triplet).
                        let first_triplet = &self.rest[..3];
                        self.num_undecodable_pct_triplets = i;
                        self.rest = before_pct_seqs;
                        return Some(first_triplet);
                    }
                    *buf_dest = byte;
                    rest = after_triplet;
                }
                // If the next character is not `%`, decoded bytes so far
                // won't be valid UTF-8 byte sequence.
                // Emit the read percent-encoded triplets without decoding.
                // Note that all characters in `&c_buf[1..]` (if available)
                // were decoded to "continue byte" of UTF-8, so they
                // cannot be the start of a valid UTF-8 byte sequence.
                None | Some(_) => {
                    let first_triplet = &self.rest[..3];
                    self.num_undecodable_pct_triplets = i;
                    self.rest = before_pct_seqs;
                    return Some(first_triplet);
                }
            };
        }

        // Decode the bytes into a character.
        match core::str::from_utf8(&c_buf[..expected_char_len]) {
            Ok(_) => {
                let consumed_len = self.rest.len() - rest.len();
                let consumed = &self.rest[..consumed_len];
                self.rest = rest;
                Some(consumed)
            }
            Err(e) => {
                // The read triplets so far cannot be decoded into a valid
                // UTF-8 bytes sequence. However, the current byte can start
                // a valid UTF-8 byte sequence. So, do not take the whole
                // triplets unconditionally away.

                let undecodable_len = e.error_len().unwrap_or(expected_char_len);
                debug_assert!(
                    undecodable_len > 0,
                    "[validity] decoding cannot fail without undecodable prefix bytes"
                );
                let first_triplet = &self.rest[..3];
                self.num_undecodable_pct_triplets = undecodable_len - 1;
                self.rest = before_pct_seqs;
                Some(first_triplet)
            }
        }
    }
}
