//! Parser implementatitons.

use core::marker::PhantomData;

use nom::{
    branch::alt,
    bytes::complete::{tag, take_while, take_while1, take_while_m_n},
    character::complete::{char as char_, one_of, satisfy},
    combinator::{cut, not, opt, recognize},
    error::{context, ContextError, ParseError},
    multi::{fold_many_m_n, many0_count, many1_count},
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult, Parser,
};

use crate::{
    parser::{char::is_sub_delim, RiReferenceComponents},
    spec::{Spec, SpecInternal, UriSpec},
};

/// Repeats the embedded parser `n` times or until it fails and returns the number of successful
/// iteration.
///
/// Fails if the embedded parser does not succeed at least `m` times.
fn many_m_n_count<I, O, E, F>(m: usize, n: usize, f: F) -> impl nom::Parser<I, usize, E>
where
    F: nom::Parser<I, O, E>,
    I: Clone + PartialEq + nom::InputLength,
    E: ParseError<I>,
{
    fold_many_m_n(m, n, f, || 0, |count, _| count + 1)
}

/// Parses RFC 3986 / 3987 IRI.
pub(crate) fn uri<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "uri",
        recognize(tuple((
            scheme,
            char_(':'),
            hier_part::<E, S>,
            opt(preceded(char_('?'), query::<E, S>)),
            opt(preceded(char_('#'), fragment::<E, S>)),
        ))),
    )(i)
}

/// Parses RFC 3986 / 3987 IRI and returns components.
fn decompose_uri<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, RiReferenceComponents<'a, S>, E> {
    context(
        "uri",
        tuple((
            scheme,
            char_(':'),
            decompose_hier_part::<E, S>,
            opt(preceded(char_('?'), query::<E, S>)),
            opt(preceded(char_('#'), fragment::<E, S>)),
        ))
        .map(|(scheme, _colon, (authority, path), query, fragment)| {
            RiReferenceComponents {
                scheme: Some(scheme),
                authority,
                path,
                query,
                fragment,
                _spec: PhantomData,
            }
        }),
    )(i)
}

/// Parses `hier-part` and `ihier-part` rules.
fn hier_part<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "hier-part",
        recognize(alt((
            recognize(preceded(
                tag("//"),
                pair(authority::<E, S>, path_abempty::<E, S>),
            )),
            path_absolute::<E, S>,
            path_rootless::<E, S>,
            path_empty::<E>,
        ))),
    )(i)
}

/// Parses `hier-part` and `ihier-part` rules and returns authority and path.
fn decompose_hier_part<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, (Option<&'a str>, &'a str), E> {
    context(
        "hier-part",
        alt((
            preceded(
                tag("//"),
                pair(authority::<E, S>.map(Some), path_abempty::<E, S>),
            ),
            path_absolute::<E, S>.map(|path| (None, path)),
            path_rootless::<E, S>.map(|path| (None, path)),
            path_empty::<E>.map(|path| (None, path)),
        )),
    )(i)
}

/// Parses RFC 3986 / 3987 IRI reference.
pub(crate) fn uri_reference<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context("uri_reference", alt((uri::<E, S>, relative_ref::<E, S>)))(i)
}

/// Parses RFC 3986 / 3987 IRI reference and returns components.
pub(crate) fn decompose_uri_reference<
    'a,
    E: ParseError<&'a str> + ContextError<&'a str>,
    S: Spec,
>(
    i: &'a str,
) -> IResult<&'a str, RiReferenceComponents<'a, S>, E> {
    context(
        "uri_reference",
        alt((decompose_uri::<E, S>, decompose_relative_ref::<E, S>)),
    )(i)
}

/// Parses RFC 3986 / 3987 absolute IRI.
pub(crate) fn absolute_uri<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "absolute_uri",
        recognize(tuple((
            scheme,
            char_(':'),
            hier_part::<E, S>,
            opt(preceded(char_('?'), query::<E, S>)),
        ))),
    )(i)
}

/// Parses RFC 3986 / 3987 relative reference.
pub(crate) fn relative_ref<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "relative_ref",
        recognize(tuple((
            relative_part::<E, S>,
            opt(preceded(char_('?'), query::<E, S>)),
            opt(preceded(char_('#'), fragment::<E, S>)),
        ))),
    )(i)
}

/// Parses RFC 3986 / 3987 relative reference and returns components.
fn decompose_relative_ref<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, RiReferenceComponents<'a, S>, E> {
    context(
        "relative_ref",
        tuple((
            decompose_relative_part::<E, S>,
            opt(preceded(char_('?'), query::<E, S>)),
            opt(preceded(char_('#'), fragment::<E, S>)),
        ))
        .map(
            |((authority, path), query, fragment)| RiReferenceComponents {
                scheme: None,
                authority,
                path,
                query,
                fragment,
                _spec: PhantomData,
            },
        ),
    )(i)
}

/// Parses `relative_part` rule.
fn relative_part<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "relative-part",
        alt((
            recognize(tuple((tag("//"), authority::<E, S>, path_abempty::<E, S>))),
            path_absolute::<E, S>,
            path_noscheme::<E, S>,
            path_empty,
        )),
    )(i)
}

/// Parses `relative_part` rule and returns authority and path.
fn decompose_relative_part<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, (Option<&'a str>, &'a str), E> {
    context(
        "relative-part",
        alt((
            preceded(
                tag("//"),
                pair(authority::<E, S>.map(Some), path_abempty::<E, S>),
            ),
            path_absolute::<E, S>.map(|path| (None, path)),
            path_noscheme::<E, S>.map(|path| (None, path)),
            path_empty.map(|path| (None, path)),
        )),
    )(i)
}

/// Parses `scheme` rule.
fn scheme<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "scheme",
        recognize(pair(
            satisfy(|c: char| c.is_ascii_alphabetic()),
            take_while(|c: char| c.is_ascii_alphanumeric() || c == '+' || c == '-' || c == '.'),
        )),
    )(i)
}

/// Parses `authority` and `iauthority` rules.
fn authority<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "authority",
        recognize(tuple((
            opt(terminated(userinfo::<E, S>, char_('@'))),
            host::<E, S>,
            opt(preceded(char_(':'), port)),
        ))),
    )(i)
}

/// Parses `userinfo` and `iuserinfo` rules.
fn userinfo<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "userinfo",
        recognize(many0_count(alt((
            take_while1(|c: char| S::is_char_unreserved(c) || is_sub_delim(c) || c == ':')
                .map(|_| ()),
            pct_encoded.map(|_| ()),
        )))),
    )(i)
}

/// Parses `host` and `ihost` rules.
fn host<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context("host", alt((ip_literal, ipv4address, reg_name::<E, S>)))(i)
}

/// Parses `port` rule.
fn port<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context("port", take_while(|c: char| c.is_ascii_digit()))(i)
}

/// Parses `IP-literal` rules.
fn ip_literal<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "IP-literal",
        recognize(delimited(
            char_('['),
            alt((ipv6address, ipvfuture)),
            char_(']'),
        )),
    )(i)
}

/// Parses `IPvFuture` rules.
fn ipvfuture<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    // > If a URI containing an IP-literal that starts with "v" (case-insensitive),
    // >
    // > --- <https://tools.ietf.org/html/rfc3986#section-3.2.2>
    context(
        "IPvFuture",
        recognize(tuple((
            alt((char_('v'), char_('V'))),
            take_while1(|c: char| c.is_ascii_hexdigit()),
            char_('.'),
            take_while1(|c: char| UriSpec::is_char_unreserved(c) || is_sub_delim(c) || c == ':'),
        ))),
    )(i)
}

/// Parses `IPv6Address` rules.
fn ipv6address<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    /// Generates a parser for a part before `::` (and `::` itself) of IPv6
    /// address.
    fn before_and_double_colon<'b, E: ParseError<&'b str> + ContextError<&'b str>>(
        num_h16: usize,
    ) -> impl nom::Parser<&'b str, &'b str, E> {
        assert!(num_h16 >= 1);
        recognize(terminated(
            pair(
                h16,
                many_m_n_count(num_h16 - 1, num_h16 - 1, preceded(char_(':'), h16)),
            ),
            tag("::"),
        ))
    }

    /// Generates a parser for a part after `::` of IPv6 address.
    fn after_double_colon<'b, E: ParseError<&'b str> + ContextError<&'b str>>(
        num_max_h16: usize,
    ) -> impl nom::Parser<&'b str, &'b str, E> {
        assert!(num_max_h16 >= 2);
        recognize(alt((
            pair(
                many_m_n_count(0, num_max_h16 - 1, terminated(h16, char_(':'))),
                terminated(h16, not(char_('.'))),
            ),
            pair(
                many_m_n_count(0, num_max_h16 - 2, terminated(h16, char_(':'))),
                ipv4address,
            ),
        )))
    }

    context(
        "IPv6Address",
        alt((
            recognize(tuple((tag("::"), after_double_colon(7)))),
            recognize(pair(before_and_double_colon(1), after_double_colon(6))),
            recognize(pair(before_and_double_colon(2), after_double_colon(5))),
            recognize(pair(before_and_double_colon(3), after_double_colon(4))),
            recognize(pair(before_and_double_colon(4), after_double_colon(3))),
            recognize(pair(before_and_double_colon(5), after_double_colon(2))),
            recognize(pair(before_and_double_colon(6), h16)),
            before_and_double_colon(7),
            recognize(pair(
                many_m_n_count(0, 7, terminated(h16, char_(':'))),
                terminated(h16, not(char_('.'))),
            )),
            recognize(pair(
                many_m_n_count(0, 6, terminated(h16, char_(':'))),
                ipv4address,
            )),
        )),
    )(i)
}

/// Parses `h16` rule.
fn h16<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    recognize(take_while_m_n(1, 4, |c: char| c.is_ascii_hexdigit()))(i)
}

/// Parses `IPv4Address` rules.
fn ipv4address<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "IPv4Address",
        recognize(tuple((
            terminated(dec_octet, char_('.')),
            terminated(dec_octet, char_('.')),
            terminated(dec_octet, char_('.')),
            dec_octet,
        ))),
    )(i)
}

/// Parses `dec-octet` rule.
fn dec_octet<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "dec-octet",
        recognize(alt((
            recognize(pair(tag("25"), one_of("012345"))),
            recognize(tuple((
                char_('2'),
                one_of("01234"),
                satisfy(|c: char| c.is_ascii_digit()),
            ))),
            recognize(pair(
                char_('1'),
                take_while_m_n(2, 2, |c: char| c.is_ascii_digit()),
            )),
            recognize(pair(
                satisfy(|c: char| c.is_ascii_digit() || c != '0'),
                satisfy(|c: char| c.is_ascii_digit()),
            )),
            recognize(satisfy(|c: char| c.is_ascii_digit())),
        ))),
    )(i)
}

/// Parses `reg-name` and `ireg-name` rules.
fn reg_name<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "reg-name",
        recognize(many0_count(alt((
            take_while1(|c: char| S::is_char_unreserved(c) || is_sub_delim(c)).map(|_| ()),
            pct_encoded.map(|_| ()),
        )))),
    )(i)
}

/// Parses `path` and `ipath` rules.
pub(crate) fn path<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    // `path-abempty` rule here is ambiguous and can be removed.
    context(
        "path",
        alt((
            path_absolute::<E, S>,
            path_noscheme::<E, S>,
            path_rootless::<E, S>,
            path_empty,
        )),
    )(i)
}

/// Parses `path-abempty` and `ipath-abempty` rules.
fn path_abempty<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "path-abempty",
        recognize(many0_count(preceded(char_('/'), segment::<E, S>))),
    )(i)
}

/// Parses `path-absolute` and `ipath-absolute` rules.
fn path_absolute<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "path-absolute",
        recognize(preceded(
            char_('/'),
            opt(pair(
                segment_nz::<E, S>,
                many0_count(preceded(char_('/'), segment::<E, S>)),
            )),
        )),
    )(i)
}

/// Parses `path-noscheme` and `ipath-noscheme` rules.
fn path_noscheme<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "path-noscheme",
        recognize(pair(
            segment_nz_nc::<E, S>,
            many0_count(preceded(char_('/'), segment::<E, S>)),
        )),
    )(i)
}

/// Parses `path-rootless` and `ipath-rootless` rules.
fn path_rootless<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "path-rootless",
        recognize(pair(
            segment_nz::<E, S>,
            many0_count(preceded(char_('/'), segment::<E, S>)),
        )),
    )(i)
}

/// Parses `path-empty` and `ipath-mpety` rules.
fn path_empty<E>(i: &str) -> IResult<&str, &str, E> {
    Ok((i, &i[0..0]))
}

/// Parses `segment` and `isegment` rules.
fn segment<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context("segment", recognize(many0_count(pchar::<E, S>)))(i)
}

/// Parses `segment-nz` and `isegment-nz` rules.
fn segment_nz<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context("segment-nz", recognize(many1_count(pchar::<E, S>)))(i)
}

/// Parses `segment-nz-nc` and `isegment-nz-nc` rules.
fn segment_nz_nc<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "segment-nz-nc",
        recognize(many1_count(alt((
            satisfy(|c: char| S::is_char_unreserved(c) || is_sub_delim(c) || c == '@').map(|_| ()),
            pct_encoded.map(|_| ()),
        )))),
    )(i)
}

/// Parses `pchar` and `ipchar` rules.
fn pchar<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    recognize(alt((
        satisfy(|c: char| S::is_char_unreserved(c) || is_sub_delim(c) || c == ':' || c == '@')
            .map(|_| ()),
        pct_encoded.map(|_| ()),
    )))(i)
}

/// Parses `query` and `iquery` rules.
fn query<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    // Whole parsing should fail if this fail, because always leading `'?'`
    // exists before the `query`.
    context(
        "query",
        recognize(cut(many0_count(alt((
            pchar::<E, S>,
            private::<E, S>,
            tag("/"),
            tag("?"),
        ))))),
    )(i)
}

/// Parses `fragment` and `ifragment` rules.
pub(crate) fn fragment<'a, E: ParseError<&'a str> + ContextError<&'a str>, S: Spec>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    // Whole parsing should fail if this fail, because always leading `'#'`
    // exists before the `fragment`.
    context(
        "fragment",
        recognize(cut(many0_count(alt((pchar::<E, S>, tag("/"), tag("?")))))),
    )(i)
}

/// Parses `pct-encoded` rule.
fn pct_encoded<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, (char, char), E> {
    context(
        "pct-encoded",
        preceded(
            char_('%'),
            context("pct-encoded/hexdigits", cut(pair(hexdig, hexdig))),
        ),
    )(i)
}

/// Parses `iprivate` rules.
fn private<'a, E: ParseError<&'a str>, S: Spec>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    recognize(satisfy(S::is_char_private))(i)
}

/// Parses hex digit.
fn hexdig<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, char, E> {
    satisfy(|c: char| c.is_ascii_hexdigit())(i)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "alloc")]
    use alloc::format;

    use crate::spec::IriSpec;

    // `nom::error::VerboseError<&'a str>` is useful for debugging,
    // but it requires `alloc` feature to be enabled on `nom`.
    // Avoid using it in tests since `iri-string` itself currently does not
    // require `alloc` feature of `nom`.
    type Error<'a> = ();

    macro_rules! assert_invalid {
        ($parser:expr, $input:expr $(,)?) => {{
            let _ = nom::combinator::all_consuming($parser)($input).unwrap_err();
        }};
    }

    macro_rules! assert_complete {
        ($parser:expr, $input:expr, $expected:expr $(,)?) => {{
            assert_eq!(
                nom::combinator::all_consuming($parser)($input),
                Ok(("", $expected))
            );
        }};
    }

    macro_rules! assert_validate {
        ($parser:expr, $($input:expr),* $(,)?) => {{
            $({
                let input = $input;
                let input: &str = input.as_ref();
                assert_complete!($parser, input, input);
            })*
        }};
    }

    macro_rules! assert_validate_list {
        ($parser:expr, $($list:expr),* $(,)?) => {{
            $({
                for input in $list {
                    assert_validate!($parser, input);
                }
            })*
        }};
    }

    const OK_URI_LIST: &[&str] = &[
        // RFC 3986 itself.
        "https://tools.ietf.org/html/rfc3986",
        // RFC 3986 section 1.1.2.
        "ftp://ftp.is.co.za/rfc/rfc1808.txt",
        "http://www.ietf.org/rfc/rfc2396.txt",
        "ldap://[2001:db8::7]/c=GB?objectClass?one",
        "mailto:John.Doe@example.com",
        "news:comp.infosystems.www.servers.unix",
        "tel:+1-816-555-1212",
        "telnet://192.0.2.16:80/",
        "urn:oasis:names:specification:docbook:dtd:xml:4.1.2",
        // RFC 3986 section 3.
        "foo://example.com:8042/over/there?name=ferret#nose",
        "urn:example:animal:ferret:nose",
        // RFC 3986 section 3.3.
        "mailto:fred@example.com",
        "foo://info.example.com?fred",
        // RFC 3986 section 5.4.
        "http://a/b/c/d;p?q",
        // RFC 3986 section 5.4.1.
        "g:h",
        "http://a/b/c/g",
        "http://a/b/c/g/",
        "http://a/g",
        "http://g",
        "http://a/b/c/d;p?y",
        "http://a/b/c/g?y",
        "http://a/b/c/d;p?q#s",
        "http://a/b/c/g#s",
        "http://a/b/c/g?y#s",
        "http://a/b/c/;x",
        "http://a/b/c/g;x",
        "http://a/b/c/g;x?y#s",
        "http://a/b/c/d;p?q",
        "http://a/b/c/",
        "http://a/b/",
        "http://a/b/g",
        "http://a/",
        // RFC 3986 section 5.4.2.
        "http://a/b/c/g.",
        "http://a/b/c/.g",
        "http://a/b/c/g..",
        "http://a/b/c/..g",
        "http://a/b/c/g/h",
        "http://a/b/c/h",
        "http://a/b/c/g;x=1/y",
        "http://a/b/c/y",
        "http://a/b/c/g?y/./x",
        "http://a/b/c/g?y/../x",
        "http://a/b/c/g#s/./x",
        "http://a/b/c/g#s/../x",
        // RFC 3986 section 6.2.2.
        "example://a/b/c/%7Bfoo%7D",
        "eXAMPLE://a/./b/../b/%63/%7bfoo%7d",
        // RFC 3986 section 6.2.2.1.
        "HTTP://www.EXAMPLE.com/",
        "http://www.example.com/",
        // RFC 3986 section 6.2.3.
        "http://example.com",
        "http://example.com/",
        "http://example.com:/",
        "http://example.com:80/",
        "http://example.com/?",
        "mailto:Joe@Example.COM",
        "mailto:Joe@example.com",
        // RFC 3986 section 6.2.4.
        "http://example.com/data",
        "http://example.com/data/",
        "ftp://cnn.example.com&story=breaking_news@10.0.0.1/top_story.htm",
        // RFC 3986 section Appendix B.
        "http://www.ics.uci.edu/pub/ietf/uri/#Related",
        // RFC 3986 section Appendix C.
        "http://www.w3.org/Addressing/",
        "ftp://foo.example.com/rfc/",
        "http://www.ics.uci.edu/pub/ietf/uri/historical.html#WARNING",
    ];

    const OK_IRI_LIST: &[&str] = &[
        // RFC 3987 itself.
        "https://tools.ietf.org/html/rfc3987",
        // RFC 3987 section 3.1.
        "http://r\u{E9}sum\u{E9}.example.org",
        "http://xn--rsum-bpad.example.org",
        "http://r%C3%A9sum%C3%A9.example.org",
        "http://www.example.org/red%09ros\u{E9}#red",
        "http://www.example.org/red%09ros%C3%A9#red",
        // RFC 3987 section 3.2.
        "http://example.com/\u{10300}\u{10301}\u{10302}",
        "http://example.com/%F0%90%8C%80%F0%90%8C%81%F0%90%8C%82",
        // RFC 3987 section 3.2.1.
        "http://www.example.org/r%C3%A9sum%C3%A9.html",
        "http://www.example.org/r%E9sum%E9.html",
        "http://www.example.org/D%C3%BCrst",
        "http://www.example.org/D%FCrst",
        "http://www.example.org/D\u{FC}rst",
        "http://xn--99zt52a.example.org/%e2%80%ae",
        "http://xn--99zt52a.example.org/%E2%80%AE",
        "http://\u{7D0D}\u{8C46}.example.org/%E2%80%AE",
        // RFC 3987 section 4.4.
        "http://ab.CDEFGH.ij/kl/mn/op.html",
        "http://ab.CDE.FGH/ij/kl/mn/op.html",
        "http://AB.CD.EF/GH/IJ/KL?MN=OP;QR=ST#UV",
        "http://AB.CD.ef/gh/IJ/KL.html",
        "http://ab.cd.EF/GH/ij/kl.html",
        "http://ab.CD.EF/GH/IJ/kl.html",
        "http://ab.CDE123FGH.ij/kl/mn/op.html",
        "http://ab.cd.ef/GH1/2IJ/KL.html",
        "http://ab.cd.ef/GH%31/%32IJ/KL.html",
        "http://ab.CDEFGH.123/kl/mn/op.html",
        // RFC 3987 section 5.2.
        "http://example.org/ros\u{E9}",
        // RFC 3987 section 5.3.2.
        "example://a/b/c/%7Bfoo%7D/ros\u{E9}",
        "eXAMPLE://a/./b/../b/%63/%7bfoo%7d/ros%C3%A9",
        // RFC 3987 section 5.3.2.1.
        "HTTP://www.EXAMPLE.com/",
        "http://www.example.com/",
        // RFC 3987 section 5.3.2.2.
        "http://www.example.org/r\u{E9}sum\u{E9}.html",
        "http://www.example.org/re\u{301}sume\u{301}.html",
        // RFC 3987 section 5.3.2.3.
        "http://example.org/~user",
        "http://example.org/%7euser",
        "http://example.org/%7Euser",
        // RFC 3987 section 5.3.3.
        "http://example.com",
        "http://example.com/",
        "http://example.com:/",
        "http://example.com:80/",
        //"http://r\u{E9}sum\u{E9}.example.org",  // duplicate
        //"http://xn--rsum-bpad.example.org",  // duplicate
        // RFC 3987 section 5.3.4.
        "http://example.com/data",
        "http://example.com/data/",
        // RFC 3987 section 6.4.
        //"http://www.example.org/r%C3%A9sum%C3%A9.html",  // duplicate
        //"http://www.example.org/r\u{E9}sum\u{E9}.html",  // duplicate
        //"http://www.example.org/r%E9sum%E9.html",  // duplicate
        "http://www.example.org/r%E9sum%E9.xml#r\u{E9}sum\u{E9}",
    ];

    #[test]
    fn test_uri() {
        assert_validate_list!(uri::<Error<'_>, UriSpec>, OK_URI_LIST);
    }

    #[test]
    fn test_iri() {
        assert_validate_list!(uri::<Error<'_>, IriSpec>, OK_URI_LIST, OK_IRI_LIST);
    }

    #[test]
    fn test_invalid_chars() {
        // Not allowed characters `<` and `>`.
        assert_invalid!(uri::<Error<'_>, UriSpec>, "foo://bar/<foo>");
        assert_invalid!(uri::<Error<'_>, IriSpec>, "foo://bar/<foo>");
        // U+FFFD Replacement character: Invalid as URI, also invalid as IRI.
        assert_invalid!(uri::<Error<'_>, UriSpec>, "foo://bar/\u{FFFD}");
        assert_invalid!(uri::<Error<'_>, IriSpec>, "foo://bar/\u{FFFD}");
        // U+3044: Hiragana letter I: Invalid as URI, valid as IRI.
        assert_invalid!(uri::<Error<'_>, UriSpec>, "foo://bar/\u{3044}");
        assert_validate!(uri::<Error<'_>, IriSpec>, "foo://bar/\u{3044}");
    }

    #[test]
    fn test_invalid_pct_encoded() {
        // Invalid percent encoding.
        assert_invalid!(uri::<Error<'_>, UriSpec>, "%zz");
        assert_invalid!(uri::<Error<'_>, UriSpec>, "%0");
        assert_invalid!(uri::<Error<'_>, UriSpec>, "foo://bar/%0");
        assert_invalid!(uri::<Error<'_>, UriSpec>, "foo://bar/%0/");
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_ipv6address() {
        use core::cmp::Ordering;

        assert_validate!(ipv6address::<Error<'_>>, "a:bB:cCc:dDdD:e:F:a:B");
        assert_validate!(ipv6address::<Error<'_>>, "1:1:1:1:1:1:1:1");
        assert_validate!(ipv6address::<Error<'_>>, "1:1:1:1:1:1:1.1.1.1");

        // Generate IPv6 addresses with `::`.
        let make_sub = |n: usize| {
            let mut s = "1:".repeat(n);
            s.pop();
            s
        };
        for len_pref in 0..=7 {
            let prefix = make_sub(len_pref);
            for len_suf in 1..=(7 - len_pref) {
                assert_validate!(
                    ipv6address::<Error<'_>>,
                    &format!("{}::{}", prefix, make_sub(len_suf))
                );
                match len_suf.cmp(&2) {
                    Ordering::Greater => assert_validate!(
                        ipv6address::<Error<'_>>,
                        &format!("{}::{}:1.1.1.1", prefix, make_sub(len_suf - 2))
                    ),
                    Ordering::Equal => {
                        assert_validate!(ipv6address::<Error<'_>>, &format!("{}::1.1.1.1", prefix))
                    }
                    Ordering::Less => {}
                }
            }
        }
    }

    #[test]
    fn test_hier_part_only_slashes() {
        assert_validate_list!(
            hier_part::<Error<'_>, IriSpec>,
            &["", "/", "//", "///", "////", "/////"]
        );
    }

    #[test]
    fn test_decompose_hier_part_only_slashes() {
        assert_complete!(decompose_hier_part::<Error<'_>, IriSpec>, "", (None, ""));
        assert_complete!(decompose_hier_part::<Error<'_>, IriSpec>, "/", (None, "/"));
        assert_complete!(
            decompose_hier_part::<Error<'_>, IriSpec>,
            "//",
            (Some(""), "")
        );
        assert_complete!(
            decompose_hier_part::<Error<'_>, IriSpec>,
            "///",
            (Some(""), "/")
        );
        assert_complete!(
            decompose_hier_part::<Error<'_>, IriSpec>,
            "////",
            (Some(""), "//")
        );
        assert_complete!(
            decompose_hier_part::<Error<'_>, IriSpec>,
            "/////",
            (Some(""), "///")
        );
    }

    #[test]
    fn test_decompose_relative_part_only_slashes() {
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriSpec>,
            "",
            (None, "")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriSpec>,
            "/",
            (None, "/")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriSpec>,
            "//",
            (Some(""), "")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriSpec>,
            "///",
            (Some(""), "/")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriSpec>,
            "////",
            (Some(""), "//")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriSpec>,
            "/////",
            (Some(""), "///")
        );
    }
}
