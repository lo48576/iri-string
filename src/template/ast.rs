//! Abstract Syntax tree for the template.

use crate::parser::str::find_split_hole;

/// Literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Literal<'a>(&'a str);

/// Variable name.
// QUESTION: Should hexdigits in percent-encoded triplets be compared case sensitively?
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct VarName<'a>(&'a str);

impl<'a> VarName<'a> {
    /// Creates a `VarName` from the trusted string.
    ///
    /// # Precondition
    ///
    /// The given string should be a valid variable name.
    #[inline]
    #[must_use]
    pub(super) fn new(s: &'a str) -> Self {
        Self(s)
    }

    /// Returns the varibale name.
    #[inline]
    #[must_use]
    pub(super) fn as_str(&self) -> &'a str {
        self.0
    }
}

/// Variable specifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct VarSpec<'a> {
    /// Variable name.
    name: VarName<'a>,
    /// Variable modifier.
    modifier: Modifier,
}

impl<'a> VarSpec<'a> {
    /// Returns the varibale name.
    #[inline]
    #[must_use]
    pub(super) fn name(&self) -> VarName<'a> {
        self.name
    }

    /// Returns the modifier.
    #[inline]
    #[must_use]
    pub(super) fn modifier(&self) -> Modifier {
        self.modifier
    }

    /// Parses the trusted varspec string.
    ///
    /// # Panics
    ///
    /// May panic if the input is invalid.
    #[must_use]
    pub(super) fn parse_trusted(s: &'a str) -> Self {
        if let Some(varname) = s.strip_suffix('*') {
            // `varname "*"`.
            return Self {
                name: VarName::new(varname),
                modifier: Modifier::Explode,
            };
        }
        // `varname ":" max-length` or `varname`.
        match find_split_hole(s, b':') {
            Some((varname, max_len)) => {
                let max_len: u16 = max_len
                    .parse()
                    .expect("[precondition] the input should be valid `varspec`");
                Self {
                    name: VarName::new(varname),
                    modifier: Modifier::MaxLen(max_len),
                }
            }
            None => Self {
                name: VarName(s),
                modifier: Modifier::None,
            },
        }
    }
}

/// Variable modifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Modifier {
    /// No modifiers.
    None,
    /// Max length, greater than 0 and less than 10000.
    MaxLen(u16),
    /// Explode the variable, e.g. the var spec has `*`.
    Explode,
}

/// Variable list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct VarList<'a>(&'a [VarSpec<'a>]);

/// Operator that is possibly reserved for future extension.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum MaybeOperator {
    /// Working operator.
    Operator(Operator),
    /// Reserved for future extensions.
    Reserved(OperatorReservedForFuture),
}

impl MaybeOperator {
    /// Returns the operator for the given character.
    pub(super) fn from_byte(b: u8) -> Option<Self> {
        match b {
            b'+' => Some(Self::Operator(Operator::Reserved)),
            b'#' => Some(Self::Operator(Operator::Fragment)),
            b'.' => Some(Self::Operator(Operator::Label)),
            b'/' => Some(Self::Operator(Operator::PathSegments)),
            b';' => Some(Self::Operator(Operator::PathParams)),
            b'?' => Some(Self::Operator(Operator::FormQuery)),
            b'&' => Some(Self::Operator(Operator::FormQueryCont)),
            b'=' => Some(Self::Reserved(OperatorReservedForFuture::Equals)),
            b',' => Some(Self::Reserved(OperatorReservedForFuture::Comma)),
            b'!' => Some(Self::Reserved(OperatorReservedForFuture::Exclamation)),
            b'@' => Some(Self::Reserved(OperatorReservedForFuture::AtSign)),
            b'|' => Some(Self::Reserved(OperatorReservedForFuture::Pipe)),
            _ => None,
        }
    }
}

/// Working operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Operator {
    /// No operator. String expansion.
    String,
    /// Reserved expansion by `+`.
    Reserved,
    /// Fragment expansion by `#`.
    Fragment,
    /// Label expansion by `.`.
    Label,
    /// Path segments by `/`.
    PathSegments,
    /// Path-style parameters by `;`.
    PathParams,
    /// Form-style query by `?`.
    FormQuery,
    /// Form-style query continuation by `&`.
    FormQueryCont,
}

impl Operator {
    /// Returns the operator for the given character.
    #[must_use]
    pub(super) fn from_byte(b: u8) -> Option<Self> {
        match b {
            b'+' => Some(Self::Reserved),
            b'#' => Some(Self::Fragment),
            b'.' => Some(Self::Label),
            b'/' => Some(Self::PathSegments),
            b';' => Some(Self::PathParams),
            b'?' => Some(Self::FormQuery),
            b'&' => Some(Self::FormQueryCont),
            _ => None,
        }
    }
}

/// Operator reserved for future extension.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum OperatorReservedForFuture {
    /// Reserved `=` operator.
    Equals,
    /// Reserved `,` operator.
    Comma,
    /// Reserved `!` operator.
    Exclamation,
    /// Reserved `@` operator.
    AtSign,
    /// Reserved `|` operator.
    Pipe,
}

/// Expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Expression<'a> {
    /// Operator.
    operator: Operator,
    /// Variable list.
    variables: VarList<'a>,
}
