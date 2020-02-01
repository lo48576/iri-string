//! A private module for sealed trait and internal implementations.
//!
//! Note that this MUST be a private module.
//! See [Rust API Guidelines][sealed-trait] about the necessity of being private.
//!
//! [sealed-trait]:
//! https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed

use crate::spec::{IriSpec, UriSpec};

/// A trait to prohibit user-defined types from implementing `Spec`.
///
/// About sealed trait, see [Rust API Guidelines][future-proofing].
///
/// [future-proofing]: https://rust-lang.github.io/api-guidelines/future-proofing.html
pub trait Sealed: SpecInternal {}

impl Sealed for IriSpec {}
impl Sealed for UriSpec {}

/// Internal implementations for spec types.
pub trait SpecInternal {}

impl SpecInternal for IriSpec {}

impl SpecInternal for UriSpec {}
