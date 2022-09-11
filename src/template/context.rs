//! Template expansion context.

use core::fmt;

use crate::spec::Spec;
use crate::template::components::VarName;
pub use crate::template::expand::VarVisitor;
use crate::template::{Context, Value, ValueType};

/// A trait for types that can behave as a URI template expansion context.
pub trait AsContext {
    /// Visits a variable.
    ///
    /// To get variable name, use [`VarVisitor::var_name()`].
    fn visit<'a, 'b, S: Spec>(
        &self,
        visitor: VarVisitor<'a, 'b, S>,
    ) -> Result<VisitDoneToken<'a, 'b, S>, fmt::Error>;

    /// Returns the type of the variable.
    #[must_use]
    fn get_type(&self, name: VarName<'_>) -> ValueType;
}

impl AsContext for Context {
    fn visit<'a, 'b, S: Spec>(
        &self,
        visitor: VarVisitor<'a, 'b, S>,
    ) -> Result<VisitDoneToken<'a, 'b, S>, fmt::Error> {
        let name = visitor.var_name().as_str();
        match self.variables.get(name) {
            None | Some(Value::Undefined) => visitor.visit_undefined(),
            Some(Value::String(s)) => visitor.visit_string(s),
            Some(Value::List(list)) => {
                let mut visitor = visitor.visit_list();
                list.iter().try_for_each(|item| visitor.visit_item(item))?;
                visitor.finish()
            }
            Some(Value::Assoc(list)) => {
                let mut visitor = visitor.visit_assoc();
                list.iter()
                    .try_for_each(|(k, v)| visitor.visit_entry(k, v))?;
                visitor.finish()
            }
        }
    }

    fn get_type(&self, name: VarName<'_>) -> ValueType {
        match self.variables.get(name.as_str()) {
            None | Some(Value::Undefined) => ValueType::undefined(),
            Some(Value::String(_)) => ValueType::string(),
            Some(Value::List(v)) if v.is_empty() => ValueType::empty_list(),
            Some(Value::List(_)) => ValueType::nonempty_list(),
            Some(Value::Assoc(v)) if v.is_empty() => ValueType::empty_assoc(),
            Some(Value::Assoc(_)) => ValueType::nonempty_assoc(),
        }
    }
}

/// An opaque token value that proves some variable is visited.
// This should not be able to be created by any means other than `VarVisitor::visit_foo()`.
// Do not derive any traits that allows the value to be generated or cloned.
pub struct VisitDoneToken<'a, 'b, S>(VarVisitor<'a, 'b, S>);

impl<'a, 'b, S: Spec> VisitDoneToken<'a, 'b, S> {
    /// Creates a new token.
    #[inline]
    #[must_use]
    pub(super) fn new(visitor: VarVisitor<'a, 'b, S>) -> Self {
        Self(visitor)
    }

    /// Returns the raw pointer to the backend formatter.
    #[inline]
    #[must_use]
    pub(super) fn formatter_ptr(&self) -> *const fmt::Formatter<'b> {
        self.0.formatter_ptr()
    }
}

impl<S: Spec> fmt::Debug for VisitDoneToken<'_, '_, S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VisitDoneToken")
    }
}
