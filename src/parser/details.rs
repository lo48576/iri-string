//! Parser implementatitons.

use crate::parser::{
    char::{is_sub_delim, is_ucschar},
    IriReferenceComponents,
};

use nom::{
    branch::alt,
    bytes::complete::{tag, take_while, take_while1, take_while_m_n},
    character::complete::{char as char_, one_of},
    combinator::{cut, map, not, opt, recognize},
    error::{context, ParseError},
    multi::{fold_many_m_n, many0_count, many1_count},
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult,
};

/// `one_of` with predicate (not characters list).
fn one_is<I, F, E: ParseError<I>>(pred: F) -> impl Fn(I) -> IResult<I, char, E>
where
    I: nom::Slice<core::ops::RangeFrom<usize>> + nom::InputIter,
    <I as nom::InputIter>::Item: nom::AsChar + Copy,
    F: Fn(<I as nom::InputIter>::Item) -> bool,
{
    use nom::AsChar;

    move |i: I| match i.iter_elements().next().map(|c| (c, pred(c))) {
        Some((c, true)) => Ok((i.slice(c.len()..), c.as_char())),
        _ => Err(nom::Err::Error(E::from_error_kind(
            i,
            nom::error::ErrorKind::OneOf,
        ))),
    }
}

/// Repeats the embedded parser `n` times or until it fails and returns the number of successful
/// iteration.
///
/// Fails if the embedded parser does not succeed at least `m` times.
fn many_m_n_count<I, O, E, F>(m: usize, n: usize, f: F) -> impl Fn(I) -> IResult<I, usize, E>
where
    F: Fn(I) -> IResult<I, O, E>,
    I: Clone + PartialEq,
    E: ParseError<I>,
{
    fold_many_m_n(m, n, f, 0, |count, _| count + 1)
}

/// Parser rules different between URI and IRI.
pub(crate) trait Rule {
    /// Checks if the given character matches `unreserved` or `iunreserved`
    /// rule.
    fn is_unreserved(c: char) -> bool;
    /// Checks if the given character matches `iprivate` rule.
    fn is_private(c: char) -> bool;
}

/// URI rules.
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) enum UriRule {}

impl Rule for UriRule {
    fn is_unreserved(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '-' || c == '.' || c == '_' || c == '~'
    }

    fn is_private(_: char) -> bool {
        false
    }
}

/// IRI rules.
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) enum IriRule {}

impl Rule for IriRule {
    fn is_unreserved(c: char) -> bool {
        UriRule::is_unreserved(c) || is_ucschar(c)
    }

    fn is_private(c: char) -> bool {
        match u32::from(c) {
            0xE000..=0xF8FF => true,
            0xF_0000..=0xF_FFFD => true,
            0x10_0000..=0x10_FFFD => true,
            _ => false,
        }
    }
}

/// Parses RFC 3986 / 3987 IRI.
pub(crate) fn uri<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "uri",
        tuple((
            scheme,
            char_(':'),
            hier_part::<E, R>,
            opt(preceded(char_('?'), query::<E, R>)),
            opt(preceded(char_('#'), fragment::<E, R>)),
        )),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses RFC 3986 / 3987 IRI and returns components.
fn decompose_uri<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, IriReferenceComponents<'a>, E> {
    context(
        "uri",
        map(
            tuple((
                scheme,
                char_(':'),
                decompose_hier_part::<E, R>,
                opt(preceded(char_('?'), query::<E, R>)),
                opt(preceded(char_('#'), fragment::<E, R>)),
            )),
            |(scheme, _colon, (authority, path), query, fragment)| IriReferenceComponents {
                scheme: Some(scheme),
                authority,
                path,
                query,
                fragment,
            },
        ),
    )(i)
}

/// Parses `hier-part` and `ihier-part` rules.
fn hier_part<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "hier-part",
        alt((
            recognize(preceded(
                tag("//"),
                pair(authority::<E, R>, path_abempty::<E, R>),
            )),
            path_absolute::<E, R>,
            path_rootless::<E, R>,
            path_empty::<E>,
        )),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `hier-part` and `ihier-part` rules and returns authority and path.
fn decompose_hier_part<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, (Option<&'a str>, &'a str), E> {
    context(
        "hier-part",
        alt((
            preceded(
                tag("//"),
                pair(map(authority::<E, R>, Some), path_abempty::<E, R>),
            ),
            map(path_absolute::<E, R>, |path| (None, path)),
            map(path_rootless::<E, R>, |path| (None, path)),
            map(path_empty::<E>, |path| (None, path)),
        )),
    )(i)
}

/// Parses RFC 3986 / 3987 IRI reference.
pub(crate) fn uri_reference<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context("uri_reference", alt((uri::<E, R>, relative_ref::<E, R>)))(i)
}

/// Parses RFC 3986 / 3987 IRI reference and returns components.
pub(crate) fn decompose_uri_reference<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, IriReferenceComponents<'a>, E> {
    context(
        "uri_reference",
        alt((decompose_uri::<E, R>, decompose_relative_ref::<E, R>)),
    )(i)
}

/// Parses RFC 3986 / 3987 absolute IRI.
pub(crate) fn absolute_uri<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "absolute_uri",
        tuple((
            scheme,
            char_(':'),
            hier_part::<E, R>,
            opt(preceded(char_('?'), query::<E, R>)),
        )),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses RFC 3986 / 3987 relative reference.
pub(crate) fn relative_ref<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    context(
        "relative_ref",
        tuple((
            relative_part::<E, R>,
            opt(preceded(char_('?'), query::<E, R>)),
            opt(preceded(char_('#'), fragment::<E, R>)),
        )),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses RFC 3986 / 3987 relative reference and returns components.
fn decompose_relative_ref<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, IriReferenceComponents<'a>, E> {
    context(
        "relative_ref",
        map(
            tuple((
                decompose_relative_part::<E, R>,
                opt(preceded(char_('?'), query::<E, R>)),
                opt(preceded(char_('#'), fragment::<E, R>)),
            )),
            |((authority, path), query, fragment)| IriReferenceComponents {
                scheme: None,
                authority,
                path,
                query,
                fragment,
            },
        ),
    )(i)
}

/// Parses `relative_part` rule.
fn relative_part<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "relative-part",
        alt((
            recognize(tuple((tag("//"), authority::<E, R>, path_abempty::<E, R>))),
            path_absolute::<E, R>,
            path_noscheme::<E, R>,
            path_empty,
        )),
    )(i)
}

/// Parses `relative_part` rule and returns authority and path.
fn decompose_relative_part<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, (Option<&'a str>, &'a str), E> {
    context(
        "relative-part",
        alt((
            preceded(
                tag("//"),
                pair(map(authority::<E, R>, Some), path_abempty::<E, R>),
            ),
            map(path_absolute::<E, R>, |path| (None, path)),
            map(path_noscheme::<E, R>, |path| (None, path)),
            map(path_empty, |path| (None, path)),
        )),
    )(i)
}

/// Parses `scheme` rule.
fn scheme<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "scheme",
        pair(
            one_is(|c: char| c.is_ascii_alphabetic()),
            take_while(|c: char| c.is_ascii_alphanumeric() || c == '+' || c == '-' || c == '.'),
        ),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `authority` and `iauthority` rules.
fn authority<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "authority",
        tuple((
            opt(terminated(userinfo::<E, R>, char_('@'))),
            host::<E, R>,
            opt(preceded(char_(':'), port)),
        )),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `userinfo` and `iuserinfo` rules.
fn userinfo<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "userinfo",
        many0_count(alt((
            map(
                take_while1(|c: char| R::is_unreserved(c) || is_sub_delim(c) || c == ':'),
                |_| (),
            ),
            map(pct_encoded, |_| ()),
        ))),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `host` and `ihost` rules.
fn host<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context("host", alt((ip_literal, ipv4address, reg_name::<E, R>)))(i)
}

/// Parses `port` rule.
fn port<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context("port", take_while(|c: char| c.is_ascii_digit()))(i)
}

/// Parses `IP-literal` rules.
fn ip_literal<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "IP-literal",
        delimited(char_('['), alt((ipv6address, ipvfuture)), char_(']')),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `IPvFuture` rules.
fn ipvfuture<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    // > If a URI containing an IP-literal that starts with "v" (case-insensitive),
    // >
    // > --- <https://tools.ietf.org/html/rfc3986#section-3.2.2>
    context(
        "IPvFuture",
        tuple((
            alt((char_('v'), char_('V'))),
            take_while1(|c: char| c.is_ascii_hexdigit()),
            char_('.'),
            take_while1(|c: char| UriRule::is_unreserved(c) || is_sub_delim(c) || c == ':'),
        )),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `IPv6Address` rules.
fn ipv6address<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    /// Generates a parser for a part before `::` (and `::` itself) of IPv6
    /// address.
    fn before_and_double_colon<'b, E: ParseError<&'b str>>(
        num_h16: usize,
    ) -> impl Fn(&'b str) -> IResult<&'b str, &'b str, E> {
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
    fn after_double_colon<'b, E: ParseError<&'b str>>(
        num_max_h16: usize,
    ) -> impl Fn(&'b str) -> IResult<&'b str, &'b str, E> {
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
fn h16<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    take_while_m_n(1, 4, |c: char| c.is_ascii_hexdigit())(i)
        .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `IPv4Address` rules.
fn ipv4address<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "IPv4Address",
        tuple((
            terminated(dec_octet, char_('.')),
            terminated(dec_octet, char_('.')),
            terminated(dec_octet, char_('.')),
            dec_octet,
        )),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `dec-octet` rule.
fn dec_octet<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "dec-octet",
        alt((
            recognize(pair(tag("25"), one_of("012345"))),
            recognize(tuple((
                char_('2'),
                one_of("01234"),
                one_is(|c: char| c.is_ascii_digit()),
            ))),
            recognize(pair(
                char_('1'),
                take_while_m_n(2, 2, |c: char| c.is_ascii_digit()),
            )),
            recognize(pair(
                one_is(|c: char| c.is_ascii_digit() || c != '0'),
                one_is(|c: char| c.is_ascii_digit()),
            )),
            recognize(one_is(|c: char| c.is_ascii_digit())),
        )),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `reg-name` and `ireg-name` rules.
fn reg_name<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "reg-name",
        many0_count(alt((
            map(
                take_while1(|c: char| R::is_unreserved(c) || is_sub_delim(c)),
                |_| (),
            ),
            map(pct_encoded, |_| ()),
        ))),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `path` and `ipath` rules.
pub(crate) fn path<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    // `path-abempty` rule here is ambiguous and can be removed.
    context(
        "path",
        alt((
            path_absolute::<E, R>,
            path_noscheme::<E, R>,
            path_rootless::<E, R>,
            path_empty,
        )),
    )(i)
}

/// Parses `path-abempty` and `ipath-abempty` rules.
fn path_abempty<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "path-abempty",
        many0_count(preceded(char_('/'), segment::<E, R>)),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `path-absolute` and `ipath-absolute` rules.
fn path_absolute<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "path-absolute",
        preceded(
            char_('/'),
            opt(pair(
                segment_nz::<E, R>,
                many0_count(preceded(char_('/'), segment::<E, R>)),
            )),
        ),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `path-noscheme` and `ipath-noscheme` rules.
fn path_noscheme<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "path-noscheme",
        pair(
            segment_nz_nc::<E, R>,
            many0_count(preceded(char_('/'), segment::<E, R>)),
        ),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `path-rootless` and `ipath-rootless` rules.
fn path_rootless<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "path-rootless",
        pair(
            segment_nz::<E, R>,
            many0_count(preceded(char_('/'), segment::<E, R>)),
        ),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `path-empty` and `ipath-mpety` rules.
fn path_empty<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    Ok((i, &i[0..0]))
}

/// Parses `segment` and `isegment` rules.
fn segment<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context("segment", many0_count(pchar::<E, R>))(i)
        .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `segment-nz` and `isegment-nz` rules.
fn segment_nz<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context("segment-nz", many1_count(pchar::<E, R>))(i)
        .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `segment-nz-nc` and `isegment-nz-nc` rules.
fn segment_nz_nc<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "segment-nz-nc",
        many1_count(alt((
            map(
                one_is(|c: char| R::is_unreserved(c) || is_sub_delim(c) || c == '@'),
                |_| (),
            ),
            map(pct_encoded, |_| ()),
        ))),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `pchar` and `ipchar` rules.
fn pchar<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    alt((
        map(
            one_is(|c: char| R::is_unreserved(c) || is_sub_delim(c) || c == ':' || c == '@'),
            |_| (),
        ),
        map(pct_encoded, |_| ()),
    ))(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `query` and `iquery` rules.
fn query<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    // Whole parsing should fail if this fail, because always leading `'?'`
    // exists before the `query`.
    context(
        "query",
        cut(many0_count(alt((
            pchar::<E, R>,
            private::<E, R>,
            tag("/"),
            tag("?"),
        )))),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `fragment` and `ifragment` rules.
pub(crate) fn fragment<'a, E: ParseError<&'a str>, R: Rule>(
    i: &'a str,
) -> IResult<&'a str, &'a str, E> {
    // Whole parsing should fail if this fail, because always leading `'#'`
    // exists before the `fragment`.
    context(
        "fragment",
        cut(many0_count(alt((pchar::<E, R>, tag("/"), tag("?"))))),
    )(i)
    .map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses `pct-encoded` rule.
fn pct_encoded<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, (char, char), E> {
    context(
        "pct-encoded",
        preceded(
            char_('%'),
            context("pct-encoded/hexdigits", cut(pair(hexdig, hexdig))),
        ),
    )(i)
}

/// Parses `iprivate` rules.
fn private<'a, E: ParseError<&'a str>, R: Rule>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    one_is(R::is_private)(i).map(|(rest, _)| (rest, &i[..(i.len() - rest.len())]))
}

/// Parses hex digit.
fn hexdig<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, char, E> {
    one_is(|c: char| c.is_ascii_hexdigit())(i)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "alloc")]
    use alloc::format;

    type Error<'a> = nom::error::VerboseError<&'a str>;

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
        assert_validate_list!(uri::<Error<'_>, UriRule>, OK_URI_LIST);
    }

    #[test]
    fn test_iri() {
        assert_validate_list!(uri::<Error<'_>, IriRule>, OK_URI_LIST, OK_IRI_LIST);
    }

    #[test]
    fn test_invalid_chars() {
        // Not allowed characters `<` and `>`.
        assert_invalid!(uri::<Error<'_>, UriRule>, "foo://bar/<foo>");
        assert_invalid!(uri::<Error<'_>, IriRule>, "foo://bar/<foo>");
        // U+FFFD Replacement character: Invalid as URI, also invalid as IRI.
        assert_invalid!(uri::<Error<'_>, UriRule>, "foo://bar/\u{FFFD}");
        assert_invalid!(uri::<Error<'_>, IriRule>, "foo://bar/\u{FFFD}");
        // U+3044: Hiragana letter I: Invalid as URI, valid as IRI.
        assert_invalid!(uri::<Error<'_>, UriRule>, "foo://bar/\u{3044}");
        assert_validate!(uri::<Error<'_>, IriRule>, "foo://bar/\u{3044}");
    }

    #[test]
    fn test_invalid_pct_encoded() {
        // Invalid percent encoding.
        assert_invalid!(uri::<Error<'_>, UriRule>, "%zz");
        assert_invalid!(uri::<Error<'_>, UriRule>, "%0");
        assert_invalid!(uri::<Error<'_>, UriRule>, "foo://bar/%0");
        assert_invalid!(uri::<Error<'_>, UriRule>, "foo://bar/%0/");
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_ipv6address() {
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
                if len_suf > 2 {
                    assert_validate!(
                        ipv6address::<Error<'_>>,
                        &format!("{}::{}:1.1.1.1", prefix, make_sub(len_suf - 2))
                    );
                } else if len_suf == 2 {
                    assert_validate!(ipv6address::<Error<'_>>, &format!("{}::1.1.1.1", prefix));
                }
            }
        }
    }

    #[test]
    fn test_hier_part_only_slashes() {
        assert_validate_list!(
            hier_part::<Error<'_>, IriRule>,
            &["", "/", "//", "///", "////", "/////"]
        );
    }

    #[test]
    fn test_decompose_hier_part_only_slashes() {
        assert_complete!(decompose_hier_part::<Error<'_>, IriRule>, "", (None, ""));
        assert_complete!(decompose_hier_part::<Error<'_>, IriRule>, "/", (None, "/"));
        assert_complete!(
            decompose_hier_part::<Error<'_>, IriRule>,
            "//",
            (Some(""), "")
        );
        assert_complete!(
            decompose_hier_part::<Error<'_>, IriRule>,
            "///",
            (Some(""), "/")
        );
        assert_complete!(
            decompose_hier_part::<Error<'_>, IriRule>,
            "////",
            (Some(""), "//")
        );
        assert_complete!(
            decompose_hier_part::<Error<'_>, IriRule>,
            "/////",
            (Some(""), "///")
        );
    }

    #[test]
    fn test_decompose_relative_part_only_slashes() {
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriRule>,
            "",
            (None, "")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriRule>,
            "/",
            (None, "/")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriRule>,
            "//",
            (Some(""), "")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriRule>,
            "///",
            (Some(""), "/")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriRule>,
            "////",
            (Some(""), "//")
        );
        assert_complete!(
            decompose_relative_part::<Error<'_>, IriRule>,
            "/////",
            (Some(""), "///")
        );
    }
}
