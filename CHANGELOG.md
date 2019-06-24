# Change Log

## [Unreleased]

## [0.2.0]

* Use nom 5.0.0.
    + This is non-breaking change.

## [0.2.0-beta.1]

* Implement `Clone` and `Copy` for validation error types.
* Let an error type contain source string for conversion from owned string.
* Add `shrink_to_fit()` methods for `types::iri::*String` types.
* Add `set_fragment()` methods for `types::iri::*String` types
  (except for `AbsoluteIriString`).
* Add `as_str()` method for `types::iri::*Str` types.
* Add `types::iri::IriFragment{Str,String}` type.
* Move `fragment()` from `IriStr` to `IriReferenceStr`.

### Changed (non-breaking)
* Implement `Clone` and `Copy` for validation error types
  (`validate::{iri,uri}::Error`) (8c6af409963a).

#### Added
* Add `shrink_to_fit()` methods for `types::iri::*String` types (c8671876229f).
* Add `set_fragment()` methods for `types::iri::*String` types
  (except for `AbsoluteIriString`) (5ae09a327d93).
* Add `as_str()` method for `types::iri::*Str` types (0984140105a1).
* Add `types::iri::IriFragment{Str,String}` type (1c5e06192cf8).
    + This represents fragment part of an IRI.

### Changed (breaking)
* `types::iri::{AbsoluteIri,Iri,IriReference,RelativeIri}String::TryFrom<_>` now
  returns `types::iri::CreationError` as an error (8c6af409963a).
    + `CreationError` owns the source data so that it is not lost on conversion
      failure.
    + `CreationError::into_source()` returns the source data which cannot be
      converted into an IRI type.
    + Previously `validate::iri::Error` is used to represent error, but it does
      not own the source data.
* Move `fragment()` from `IriStr` to `IriReferenceStr` (1c5e06192cf8).
    + `v.fragment()` for `v: &IriStr` is still available thanks to `Deref`.

## [0.2.0-beta.0]

Totally rewritten.

[Unreleased]: <https://github.com/lo48576/iri-string/compare/v0.2.0...develop>
[0.2.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0>
[0.2.0-beta.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0-beta.1>
[0.2.0-beta.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0-beta.0>
