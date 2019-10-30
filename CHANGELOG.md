# Change Log

## [Unreleased]

## [0.2.2]

* `IriReferenceStr::resolve()` is renamed to `resolve_against()`.
    + The old name will be kept until the next minor version bump to keep compatibility.

### Changed (non-breaking)
* `IriReferenceStr::resolve()` is renamed to `resolve_against()`
  (4d64ee9884713644b69b8f227f32637d877a9d5f).
    + `resolve()` was an ambiguous name, and people cannot know which `foo.resolve(bar)` means:
      "resolve foo against bar" or "foo resolves bar".
    + The new name `resolve_against()` is more clear. `foo.resolve_against(bar)` can be natuarally
      interpreted as "resolve foo against bar".
    + The old name will be kept until the next minor version bump to keep compatibility.

## [0.2.1]

* `*Str::new()` methods are added.
* `IriFragmentStr::from_prefixed()` is added.
* `types::CreationError` is renamed to `types::IriCreationError`.
    + The old name will be kept until the next minor version bump to keep compatibility.
* Reduced indirect dependencies

### Added
* `*Str::new()` methods are added (39c8f735ccf6f28aaf2f16dcdc579fb3838bb5fb).
    + Previously the string slices are created as `<&FooStr>::try_from(s)` (where `s: &str`),
      but this is redundant.
      Now `FooStr::new(s)` can be used instead of `<&FooStr>::try_from(s)` for `s: &str`.
* `IriFragmentStr::from_prefixed()` is added (34cec2f422ba8046134668bdb662f69c9db7f52c).
    * This creates `IriFragmentStr` from the given string with leading hash (`#`) character.
      For example, `IriFragmentStr::from_prefixed("#foo")` is same as `IriFragmentStr::new("foo")`.

### Changed (non-breaking)
* `types::CreationError` is renamed to `types::IriCreationError`
  (c6e930608f158281d059e632ffc6117bddf18ebc, c0e650c5e19f1775cf82960afc9610994afba66e).
    + The old name will be kept until the next minor version bump to keep compatibility.
* Disabled `lexical` feature of `nom` crate (a2d5bcd02e02e80af1c4fc8c14d768ca519ef467).
    + This reduces indirect dependencies.
* Migrate code generator from proc-macro crate to non-proc-macro one
  (363337e720a9fdfa7e17153ffc63192bd49f7cc3).
    + This reduces indirect dependencies, and may also reduce compilation time.

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

[Unreleased]: <https://github.com/lo48576/iri-string/compare/v0.2.2...develop>
[0.2.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.2>
[0.2.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.1>
[0.2.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0>
[0.2.0-beta.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0-beta.1>
[0.2.0-beta.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0-beta.0>
