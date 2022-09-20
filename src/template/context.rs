//! Template expansion context.
//!
//! # Examples
//!
//! 1. Define your context type.
//! 2. Implement [`Context`] trait (and [`Context::visit`] method) for the type.
//!     1. Get variable name by [`Visitor::var_name`] method.
//!     2. Feed the corresponding value(s) by one of `Visitor::visit_*` methods.
//!
//! Note that users are required to consistent result across multiple visits for
//! the same variable. In other words, `Context::visit` should return the same
//! result for the same `Visitor::var_name()` during the context is borrowed.
//! If this condition is violated, the URI template processor can return
//! invalid result or panic at worst.
//!
//! ```
//! use iri_string::template::context::{Context, Visitor, ListVisitor, AssocVisitor};
//!
//! struct MyContext {
//!     name: &'static str,
//!     id: u64,
//!     tags: &'static [&'static str],
//!     children: &'static [(&'static str, usize)],
//! }
//!
//! impl Context for MyContext {
//!     fn visit<V: Visitor>(&self, visitor: V) -> V::Result {
//!         let name = visitor.var_name().as_str();
//!         match name {
//!             "name" => visitor.visit_string(self.name),
//!             "id" => visitor.visit_string(self.id),
//!             "tags" => visitor.visit_list().visit_items_and_finish(self.tags),
//!             "children" => visitor
//!                 .visit_assoc()
//!                 .visit_entries_and_finish(self.children.iter().copied()),
//!             _ => visitor.visit_undefined(),
//!         }
//!    }
//! }
//! ```
//
// # Developers note
//
// Visitor types **should not** be cloneable in order to enforce just one
// visitor is used to visit a variable. If visitors are cloneable, it can make
// the wrong usage to be available, i.e. storing cloned visitors somewhere and
// using the wrong one.
//
// However, if visitors are made cloneable by any chance, it does not indicate
// the whole implementation will be broken. Users can only use the visitors
// through visitor traits (and their API do not allow cloning), so the logic
// would work as expected if the internal usage of the visitors are correct.
// Making visitors noncloneable is an optional safety guard (with no overhead).

use core::fmt;
use core::ops::ControlFlow;

pub use crate::template::components::VarName;

/// A trait for types that can behave as a URI template expansion context.
pub trait Context: Sized {
    /// Visits a variable.
    ///
    /// To get variable name, use [`Visitor::var_name()`].
    #[must_use]
    fn visit<V: Visitor>(&self, visitor: V) -> V::Result;
}

/// Variable visitor.
///
/// See [the module documentation][self] for usage.
// NOTE (internal): Visitor types **should not** be cloneable.
pub trait Visitor: Sized + private::Sealed {
    /// Result of the visit.
    type Result;
    /// List visitor.
    type ListVisitor: ListVisitor<Result = Self::Result>;
    /// Associative array visitor.
    type AssocVisitor: AssocVisitor<Result = Self::Result>;

    /// Returns the name of the variable to visit.
    #[must_use]
    fn var_name(&self) -> VarName<'_>;
    /// Visits an undefined variable, i.e. indicates that the requested variable is unavailable.
    #[must_use]
    fn visit_undefined(self) -> Self::Result;
    /// Visits a string variable.
    #[must_use]
    fn visit_string<T: fmt::Display>(self, v: T) -> Self::Result;
    /// Visits a list variable.
    #[must_use]
    fn visit_list(self) -> Self::ListVisitor;
    /// Visits an associative array variable.
    #[must_use]
    fn visit_assoc(self) -> Self::AssocVisitor;
}

/// List visitor.
///
/// See [the module documentation][self] for usage.
// NOTE (internal): Visitor types **should not** be cloneable.
pub trait ListVisitor: Sized + private::Sealed {
    /// Result of the visit.
    type Result;

    /// Visits an item.
    ///
    /// If this returned `ControlFlow::Break(v)`, [`Context::visit`] should also
    /// return this `v`.
    ///
    /// To feed multiple items at once, do
    /// `items.into_iter().try_for_each(|item| self.visit_item(item))` for example.
    #[must_use]
    fn visit_item<T: fmt::Display>(&mut self, item: T) -> ControlFlow<Self::Result>;
    /// Finishes visiting the list.
    #[must_use]
    fn finish(self) -> Self::Result;

    /// Visits items and finish.
    #[must_use]
    fn visit_items_and_finish<T, I>(mut self, items: I) -> Self::Result
    where
        T: fmt::Display,
        I: IntoIterator<Item = T>,
    {
        match items.into_iter().try_for_each(|item| self.visit_item(item)) {
            ControlFlow::Break(v) => v,
            ControlFlow::Continue(()) => self.finish(),
        }
    }
}

/// Associative array visitor.
///
/// See [the module documentation][self] for usage.
// NOTE (internal): Visitor types **should not** be cloneable.
pub trait AssocVisitor: Sized + private::Sealed {
    /// Result of the visit.
    type Result;

    /// Visits an entry.
    ///
    /// If this returned `ControlFlow::Break(v)`, [`Context::visit`] should also
    /// return this `v`.
    ///
    /// To feed multiple items at once, do
    /// `entries.into_iter().try_for_each(|(key, value)| self.visit_entry(key, value))`
    /// for example.
    #[must_use]
    fn visit_entry<K: fmt::Display, V: fmt::Display>(
        &mut self,
        key: K,
        value: V,
    ) -> ControlFlow<Self::Result>;
    /// Finishes visiting the associative array.
    #[must_use]
    fn finish(self) -> Self::Result;

    /// Visits entries and finish.
    #[must_use]
    fn visit_entries_and_finish<K, V, I>(mut self, entries: I) -> Self::Result
    where
        K: fmt::Display,
        V: fmt::Display,
        I: IntoIterator<Item = (K, V)>,
    {
        match entries
            .into_iter()
            .try_for_each(|(key, value)| self.visit_entry(key, value))
        {
            ControlFlow::Break(v) => v,
            ControlFlow::Continue(()) => self.finish(),
        }
    }
}

/// Private module to put the trait to seal.
pub(super) mod private {
    /// A trait for visitor types of variables in a context.
    pub trait Sealed {}
}
