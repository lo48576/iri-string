//! Expansion.

use core::fmt::{self, Write as _};
use core::marker::PhantomData;
use core::mem;
use core::ops::ControlFlow;

use crate::parser::str::{find_split, find_split_hole};
use crate::parser::str::{process_percent_encoded_best_effort, PctEncodedFragments};
use crate::percent_encode::PercentEncoded;
use crate::spec::Spec;
use crate::template::components::{ExprBody, Modifier, Operator, VarName, VarSpec};
use crate::template::context::{
    private::Sealed as VisitorSealed, AssocVisitor, Context, ListVisitor, Visitor,
};
use crate::template::error::{Error, ErrorKind};
use crate::template::{UriTemplateStr, ValueType};

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
pub struct Expanded<'a, S, C> {
    /// Compiled template.
    template: &'a UriTemplateStr,
    /// Context.
    context: &'a C,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<'a, S: Spec, C: Context> Expanded<'a, S, C> {
    /// Creates a new `Expanded` object.
    #[inline]
    pub(super) fn new(template: &'a UriTemplateStr, context: &'a C) -> Result<Self, Error> {
        Self::typecheck_context(template, context)?;
        Ok(Self {
            template,
            context,
            _spec: PhantomData,
        })
    }

    /// Checks the types of variables are allowed for the corresponding expressions in the template.
    fn typecheck_context(template: &UriTemplateStr, context: &C) -> Result<(), Error> {
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
                let ty = context.visit(TypeVisitor::new(varspec.name()));
                let modifier = varspec.modifier();

                if matches!(modifier, Modifier::MaxLen(_))
                    && matches!(ty, ValueType::List | ValueType::Assoc)
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

impl<S: Spec, C: Context> fmt::Display for Expanded<'_, S, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in Chunks::new(self.template) {
            let expr = match chunk {
                Chunk::Literal(lit) => {
                    f.write_str(lit)?;
                    continue;
                }
                Chunk::Expr(body) => body,
            };
            expand::<S, _>(f, expr, self.context)?;
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
    pub(super) fn from_op(op: Operator) -> &'static Self {
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

/// Expands the expression using the given operator.
fn expand<S: Spec, C: Context>(
    f: &mut fmt::Formatter<'_>,
    expr: ExprBody<'_>,
    context: &C,
) -> fmt::Result {
    let (op, varlist) = expr.decompose();

    let mut is_first_varspec = true;
    for varspec in varlist {
        let visitor = ValueVisitor::<S>::new(f, varspec, op, &mut is_first_varspec);
        let token = context.visit(visitor)?;
        let formatter_ptr = token.formatter_ptr();
        if formatter_ptr != f as *mut _ {
            // Invalid `VisitDoneToken` was returned. This cannot usually happen
            // without intentional unnatural usage.
            panic!("invalid `VisitDoneToken` was returned");
        }
    }

    Ok(())
}

/// Escapes the given value and writes it.
#[inline]
fn escape_write<S: Spec, T: fmt::Display>(
    f: &mut fmt::Formatter<'_>,
    v: T,
    allow_reserved: bool,
) -> fmt::Result {
    use core::fmt::Display;

    if allow_reserved {
        let result = process_percent_encoded_best_effort(v, |frag| {
            let result = match frag {
                PctEncodedFragments::Char(s, _) => f.write_str(s),
                PctEncodedFragments::NoPctStr(s) => PercentEncoded::<_, S>::characters(s).fmt(f),
                PctEncodedFragments::StrayPercent => f.write_str("%25"),
                PctEncodedFragments::InvalidUtf8PctTriplets(s) => f.write_str(s),
            };
            if result.is_err() {
                return ControlFlow::Break(result);
            }
            ControlFlow::Continue(())
        });
        match result {
            Ok(ControlFlow::Break(Ok(_)) | ControlFlow::Continue(_)) => Ok(()),
            Ok(ControlFlow::Break(Err(e))) | Err(e) => Err(e),
        }
    } else {
        /// Writer that escapes the unreserved characters and writes them.
        struct UnreservePercentEncodeWriter<'a, 'b, S> {
            /// Inner writer.
            writer: &'a mut fmt::Formatter<'b>,
            /// Spec.
            _spec: PhantomData<fn() -> S>,
        }
        impl<S: Spec> fmt::Write for UnreservePercentEncodeWriter<'_, '_, S> {
            #[inline]
            fn write_str(&mut self, s: &str) -> fmt::Result {
                fmt::Display::fmt(&PercentEncoded::<_, S>::unreserve(s), self.writer)
            }
        }
        let mut writer = UnreservePercentEncodeWriter::<S> {
            writer: f,
            _spec: PhantomData,
        };
        write!(writer, "{v}")
    }
}

/// Truncates the given value as a string, escapes the value, and writes it.
fn escape_write_with_maxlen<S: Spec, T: fmt::Display>(
    writer: &mut PrefixOnceWriter<'_, '_>,
    v: T,
    allow_reserved: bool,
    max_len: Option<u16>,
) -> fmt::Result {
    if allow_reserved {
        let mut max_len = max_len.map_or(usize::MAX, usize::from);
        let result = process_percent_encoded_best_effort(v, |frag| {
            if max_len == 0 {
                return ControlFlow::Break(Ok(()));
            }
            let result =
                match frag {
                    PctEncodedFragments::Char(s, _) => {
                        max_len -= 1;
                        writer.write_str(s)
                    }
                    PctEncodedFragments::NoPctStr(s) => {
                        let mut chars = s.char_indices();
                        let count =
                            chars.by_ref().take(max_len).last().map(|(i, _)| i).expect(
                                "[consistency] decomposed string fragment must not be empty",
                            );
                        let sub_len = s.len() - chars.as_str().len();
                        max_len -= count;
                        write!(
                            writer,
                            "{}",
                            PercentEncoded::<_, S>::characters(&s[..sub_len])
                        )
                    }
                    PctEncodedFragments::StrayPercent => {
                        max_len -= 1;
                        writer.write_str("%25")
                    }
                    PctEncodedFragments::InvalidUtf8PctTriplets(s) => {
                        let count = max_len.min(s.len() / 3);
                        let sub_len = count * 3;
                        max_len -= count;
                        writer.write_str(&s[..sub_len])
                    }
                };
            if result.is_err() {
                return ControlFlow::Break(result);
            }
            ControlFlow::Continue(())
        });
        match result {
            Ok(ControlFlow::Break(Ok(_)) | ControlFlow::Continue(_)) => Ok(()),
            Ok(ControlFlow::Break(Err(e))) | Err(e) => Err(e),
        }
    } else {
        match max_len {
            Some(max_len) => {
                let mut writer = TruncatePercentEncodeWriter::<S, _> {
                    inner: writer,
                    rest_num_chars: usize::from(max_len),
                    _spec: PhantomData,
                };
                write!(writer, "{v}")
            }
            None => write!(writer, "{}", PercentEncoded::<_, S>::unreserve(v)),
        }
    }
}

/// A writer that truncates the input to the given length and writes to the backend.
struct TruncatePercentEncodeWriter<'a, S, W> {
    /// Inner writer.
    inner: &'a mut W,
    /// Maximum number of characters to be written.
    rest_num_chars: usize,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<S: Spec, W: fmt::Write> fmt::Write for TruncatePercentEncodeWriter<'_, S, W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if self.rest_num_chars == 0 {
            return Ok(());
        }
        let mut chars = s.char_indices();
        let skip_count = chars
            .by_ref()
            .take(self.rest_num_chars)
            .last()
            .map_or(0, |(i, _)| i + 1);
        let len = s.len() - chars.as_str().len();
        let truncated = &s[..len];
        write!(
            self.inner,
            "{}",
            PercentEncoded::<_, S>::unreserve(truncated)
        )?;
        self.rest_num_chars -= skip_count;
        Ok(())
    }
}

/// A writer that writes a prefix only once if and only if some value is written.
struct PrefixOnceWriter<'a, 'b> {
    /// Inner writer.
    inner: &'a mut fmt::Formatter<'b>,
    /// Prefix to write.
    prefix: Option<&'a str>,
}

impl<'a, 'b> PrefixOnceWriter<'a, 'b> {
    /// Creates a new writer with no prefix.
    #[inline]
    #[must_use]
    fn new(inner: &'a mut fmt::Formatter<'b>) -> Self {
        Self {
            inner,
            prefix: None,
        }
    }

    /// Creates a new writer with a prefix.
    #[inline]
    #[must_use]
    fn with_prefix(inner: &'a mut fmt::Formatter<'b>, prefix: &'a str) -> Self {
        Self {
            inner,
            prefix: Some(prefix),
        }
    }

    /// Returns true if the writer have not yet written the prefix.
    #[inline]
    #[must_use]
    fn has_unwritten_prefix(&self) -> bool {
        self.prefix.is_some()
    }
}

impl fmt::Write for PrefixOnceWriter<'_, '_> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if let Some(prefix) = self.prefix.take() {
            self.inner.write_str(prefix)?;
        }
        self.inner.write_str(s)
    }
}

/// An opaque token value that proves some variable is visited.
// This should not be able to be created by any means other than `VarVisitor::visit_foo()`.
// Do not derive any traits that allows the value to be generated or cloned.
struct VisitDoneToken<'a, 'b, S>(ValueVisitor<'a, 'b, S>);

impl<'a, 'b, S: Spec> VisitDoneToken<'a, 'b, S> {
    /// Creates a new token.
    #[inline]
    #[must_use]
    fn new(visitor: ValueVisitor<'a, 'b, S>) -> Self {
        Self(visitor)
    }

    /// Returns the raw pointer to the backend formatter.
    #[inline]
    #[must_use]
    fn formatter_ptr(&self) -> *const fmt::Formatter<'b> {
        self.0.formatter_ptr()
    }
}

impl<S: Spec> fmt::Debug for VisitDoneToken<'_, '_, S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VisitDoneToken")
    }
}

/// Visitor to retrieve a variable value.
// Single `ValueVisitor` should be used for single expansion.
// Do not derive any traits that allows the value to be generated or cloned.
struct ValueVisitor<'a, 'b, S> {
    /// Formatter.
    f: &'a mut fmt::Formatter<'b>,
    /// Varspec.
    varspec: VarSpec<'a>,
    /// Operator.
    op: Operator,
    /// Whether the variable to visit is the first one in an expression.
    is_first_varspec: &'a mut bool,
    /// Spec.
    _spec: PhantomData<fn() -> S>,
}

impl<'a, 'b, S: Spec> ValueVisitor<'a, 'b, S> {
    /// Creates a visitor.
    #[inline]
    #[must_use]
    fn new(
        f: &'a mut fmt::Formatter<'b>,
        varspec: VarSpec<'a>,
        op: Operator,
        is_first_varspec: &'a mut bool,
    ) -> Self {
        Self {
            f,
            varspec,
            op,
            is_first_varspec,
            _spec: PhantomData,
        }
    }

    /// Returns the raw pointer to the backend formatter.
    #[inline]
    #[must_use]
    fn formatter_ptr(&self) -> *const fmt::Formatter<'b> {
        self.f as &_ as *const _
    }
}

impl<S: Spec> VisitorSealed for ValueVisitor<'_, '_, S> {}

impl<'a, 'b, S: Spec> Visitor for ValueVisitor<'a, 'b, S> {
    type Result = Result<VisitDoneToken<'a, 'b, S>, fmt::Error>;
    type ListVisitor = ListValueVisitor<'a, 'b, S>;
    type AssocVisitor = AssocValueVisitor<'a, 'b, S>;

    /// Returns the name of the variable to visit.
    #[inline]
    #[must_use]
    fn var_name(&self) -> VarName<'a> {
        self.varspec.name()
    }

    /// Visits an undefined variable, i.e. indicates that the requested variable is unavailable.
    #[inline]
    fn visit_undefined(self) -> Self::Result {
        Ok(VisitDoneToken::new(self))
    }

    /// Visits a string variable.
    #[inline]
    fn visit_string<T: fmt::Display>(self, v: T) -> Self::Result {
        let oppr = OpProps::from_op(self.op);

        if mem::replace(self.is_first_varspec, false) {
            self.f.write_str(oppr.first)?;
        } else {
            self.f.write_str(oppr.sep)?;
        }
        let mut writer = if oppr.named {
            self.f.write_str(self.varspec.name().as_str())?;
            PrefixOnceWriter::with_prefix(self.f, "=")
        } else {
            PrefixOnceWriter::new(self.f)
        };

        let max_len = match self.varspec.modifier() {
            Modifier::None | Modifier::Explode => None,
            Modifier::MaxLen(max_len) => Some(max_len),
        };
        escape_write_with_maxlen::<S, T>(&mut writer, v, oppr.allow_reserved, max_len)?;
        if writer.has_unwritten_prefix() {
            self.f.write_str(oppr.ifemp)?;
        }
        Ok(VisitDoneToken::new(self))
    }

    /// Visits a list variable.
    #[inline]
    #[must_use]
    fn visit_list(self) -> Self::ListVisitor {
        let oppr = OpProps::from_op(self.op);
        ListValueVisitor {
            visitor: self,
            num_elems: 0,
            oppr,
        }
    }

    /// Visits an associative array variable.
    #[inline]
    #[must_use]
    fn visit_assoc(self) -> Self::AssocVisitor {
        let oppr = OpProps::from_op(self.op);
        AssocValueVisitor {
            visitor: self,
            num_elems: 0,
            oppr,
        }
    }
}

/// Visitor to retrieve value of a list variable.
// RFC 6570 section 2.3:
//
// > A variable defined as a list value is considered undefined if the
// > list contains zero members.  A variable defined as an associative
// > array of (name, value) pairs is considered undefined if the array
// > contains zero members or if all member names in the array are
// > associated with undefined values.
//
// Single variable visitor should be used for single expansion.
// Do not derive any traits that allows the value to be generated or cloned.
struct ListValueVisitor<'a, 'b, S> {
    /// Visitor.
    visitor: ValueVisitor<'a, 'b, S>,
    /// Number of already emitted elements.
    num_elems: usize,
    /// Operator props.
    oppr: &'static OpProps,
}

impl<'a, 'b, S: Spec> ListValueVisitor<'a, 'b, S> {
    /// Visits an item.
    fn visit_item_impl<T: fmt::Display>(&mut self, item: T) -> fmt::Result {
        let modifier = self.visitor.varspec.modifier();
        let is_explode = match modifier {
            Modifier::MaxLen(_) => panic!(
                "value type changed since `UriTemplateStr::expand()`: \
                 prefix modifier is not applicable to a list"
            ),
            Modifier::None => false,
            Modifier::Explode => true,
        };

        // Write prefix for each variable.
        if self.num_elems == 0 {
            if mem::replace(self.visitor.is_first_varspec, false) {
                self.visitor.f.write_str(self.oppr.first)?;
            } else {
                self.visitor.f.write_str(self.oppr.sep)?;
            }
            if self.oppr.named {
                self.visitor
                    .f
                    .write_str(self.visitor.varspec.name().as_str())?;
                self.visitor.f.write_char('=')?;
            }
        } else {
            // Write prefix for the non-first item.
            match (self.oppr.named, is_explode) {
                (_, false) => self.visitor.f.write_char(',')?,
                (false, true) => self.visitor.f.write_str(self.oppr.sep)?,
                (true, true) => {
                    self.visitor.f.write_str(self.oppr.sep)?;
                    escape_write::<S, _>(
                        self.visitor.f,
                        self.visitor.varspec.name().as_str(),
                        self.oppr.allow_reserved,
                    )?;
                    self.visitor.f.write_char('=')?;
                }
            }
        }

        escape_write::<S, _>(self.visitor.f, item, self.oppr.allow_reserved)?;

        self.num_elems += 1;
        Ok(())
    }
}

impl<S: Spec> VisitorSealed for ListValueVisitor<'_, '_, S> {}

impl<'a, 'b, S: Spec> ListVisitor for ListValueVisitor<'a, 'b, S> {
    type Result = Result<VisitDoneToken<'a, 'b, S>, fmt::Error>;

    /// Visits an item.
    #[inline]
    fn visit_item<T: fmt::Display>(&mut self, item: T) -> ControlFlow<Self::Result> {
        match self.visit_item_impl(item) {
            Ok(_) => ControlFlow::Continue(()),
            Err(e) => ControlFlow::Break(Err(e)),
        }
    }

    /// Finishes visiting the list.
    #[inline]
    fn finish(self) -> Self::Result {
        Ok(VisitDoneToken::new(self.visitor))
    }
}

/// Visitor to retrieve entries of an associative array variable.
// RFC 6570 section 2.3:
//
// > A variable defined as a list value is considered undefined if the
// > list contains zero members.  A variable defined as an associative
// > array of (name, value) pairs is considered undefined if the array
// > contains zero members or if all member names in the array are
// > associated with undefined values.
//
// Single variable visitor should be used for single expansion.
// Do not derive any traits that allows the value to be generated or cloned.
struct AssocValueVisitor<'a, 'b, S> {
    /// Visitor.
    visitor: ValueVisitor<'a, 'b, S>,
    /// Number of already emitted elements.
    num_elems: usize,
    /// Operator props.
    oppr: &'static OpProps,
}

impl<'a, 'b, S: Spec> AssocValueVisitor<'a, 'b, S> {
    /// Visits an entry.
    fn visit_entry_impl<K: fmt::Display, V: fmt::Display>(
        &mut self,
        key: K,
        value: V,
    ) -> fmt::Result {
        let modifier = self.visitor.varspec.modifier();
        let is_explode = match modifier {
            Modifier::MaxLen(_) => panic!(
                "value type changed since `UriTemplateStr::expand()`: \
                 prefix modifier is not applicable to an associative array"
            ),
            Modifier::None => false,
            Modifier::Explode => true,
        };

        // Write prefix for each variable.
        if self.num_elems == 0 {
            if mem::replace(self.visitor.is_first_varspec, false) {
                self.visitor.f.write_str(self.oppr.first)?;
            } else {
                self.visitor.f.write_str(self.oppr.sep)?;
            }
            if is_explode {
                escape_write::<S, _>(self.visitor.f, key, self.oppr.allow_reserved)?;
                self.visitor.f.write_char('=')?;
            } else {
                if self.oppr.named {
                    escape_write::<S, _>(
                        self.visitor.f,
                        self.visitor.varspec.name().as_str(),
                        self.oppr.allow_reserved,
                    )?;
                    self.visitor.f.write_char('=')?;
                }
                escape_write::<S, _>(self.visitor.f, key, self.oppr.allow_reserved)?;
                self.visitor.f.write_char(',')?;
            }
        } else {
            // Write prefix for the non-first item.
            match (self.oppr.named, is_explode) {
                (_, false) => {
                    self.visitor.f.write_char(',')?;
                    escape_write::<S, _>(self.visitor.f, key, self.oppr.allow_reserved)?;
                    self.visitor.f.write_char(',')?;
                }
                (false, true) => {
                    self.visitor.f.write_str(self.oppr.sep)?;
                    escape_write::<S, _>(self.visitor.f, key, self.oppr.allow_reserved)?;
                    self.visitor.f.write_char('=')?;
                }
                (true, true) => {
                    self.visitor.f.write_str(self.oppr.sep)?;
                    escape_write::<S, _>(self.visitor.f, key, self.oppr.allow_reserved)?;
                    self.visitor.f.write_char('=')?;
                }
            }
        }

        escape_write::<S, _>(self.visitor.f, value, self.oppr.allow_reserved)?;

        self.num_elems += 1;
        Ok(())
    }
}

impl<S: Spec> VisitorSealed for AssocValueVisitor<'_, '_, S> {}

impl<'a, 'b, S: Spec> AssocVisitor for AssocValueVisitor<'a, 'b, S> {
    type Result = Result<VisitDoneToken<'a, 'b, S>, fmt::Error>;

    /// Visits an entry.
    #[inline]
    fn visit_entry<K: fmt::Display, V: fmt::Display>(
        &mut self,
        key: K,
        value: V,
    ) -> ControlFlow<Self::Result> {
        match self.visit_entry_impl(key, value) {
            Ok(_) => ControlFlow::Continue(()),
            Err(e) => ControlFlow::Break(Err(e)),
        }
    }

    /// Finishes visiting the associative array.
    #[inline]
    fn finish(self) -> Self::Result {
        Ok(VisitDoneToken::new(self.visitor))
    }
}

/// Visitor to retrieve effective type of a variable.
struct TypeVisitor<'a> {
    /// Variable name.
    var_name: VarName<'a>,
}

impl<'a> TypeVisitor<'a> {
    /// Creates a new type visitor.
    #[inline]
    #[must_use]
    fn new(var_name: VarName<'a>) -> Self {
        Self { var_name }
    }
}

impl VisitorSealed for TypeVisitor<'_> {}

impl<'a> Visitor for TypeVisitor<'a> {
    type Result = ValueType;
    type ListVisitor = ListTypeVisitor;
    type AssocVisitor = AssocTypeVisitor;

    #[inline]
    fn var_name(&self) -> VarName<'a> {
        self.var_name
    }
    #[inline]
    fn visit_undefined(self) -> Self::Result {
        ValueType::undefined()
    }
    #[inline]
    fn visit_string<T: fmt::Display>(self, _: T) -> Self::Result {
        ValueType::string()
    }
    #[inline]
    fn visit_list(self) -> Self::ListVisitor {
        ListTypeVisitor
    }
    #[inline]
    fn visit_assoc(self) -> Self::AssocVisitor {
        AssocTypeVisitor
    }
}

/// Visitor to retrieve effective type of a list variable.
struct ListTypeVisitor;

impl VisitorSealed for ListTypeVisitor {}

impl ListVisitor for ListTypeVisitor {
    type Result = ValueType;

    /// Visits an item.
    #[inline]
    fn visit_item<T: fmt::Display>(&mut self, _item: T) -> ControlFlow<Self::Result> {
        ControlFlow::Break(ValueType::nonempty_list())
    }

    /// Finishes visiting the list.
    #[inline]
    fn finish(self) -> Self::Result {
        ValueType::empty_list()
    }
}

/// Visitor to retrieve effective type of an associative array variable.
struct AssocTypeVisitor;

impl VisitorSealed for AssocTypeVisitor {}

impl AssocVisitor for AssocTypeVisitor {
    type Result = ValueType;

    /// Visits an item.
    #[inline]
    fn visit_entry<K: fmt::Display, V: fmt::Display>(
        &mut self,
        _key: K,
        _value: V,
    ) -> ControlFlow<Self::Result> {
        ControlFlow::Break(ValueType::nonempty_assoc())
    }

    /// Finishes visiting the list.
    #[inline]
    fn finish(self) -> Self::Result {
        ValueType::empty_assoc()
    }
}
