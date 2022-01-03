# Change Log

## [Unreleased]

## [0.4.1]

* Bump internal dependency.
    * `nom` from v6 to v7.

### Changed (non-breaking)
* Bump internal dependency.
    * `nom` from v6 to v7.

## [0.4.0]

* MSRV is bumped to 1.48.0.
* Internal dependencies are bumped.
    + `nom` crate is bumped to 6.
* `serde::{Serialize, Deserialize}` is now implemented only for types with valid spec types.
* Feature flags are refactored.

### Changed (breaking)
* MSRV is bumped to 1.48.0.
    + Rust 1.48.0 is released at 2020-11-19.
* `serde::{Serialize, Deserialize}` is now implemented only for types with valid spec types.
    + Strictly this is a breaking change, but this only forbids the meaningless trait impls,
      so no real world use cases won't be affected by this change.
* Feature flags are refactored.
    + `serde-alloc` and `serde-std` flags are added to control serde's alloc and std support.
    + Unintended dependency from `std` use flag to `serde` crate is now fixed.
      Users who want to enable `serde` and `std` at the same time should also enable `serde-std`
      feature. Same applies for `serde` and `alloc` pair.

## [0.3.0]

**This release contains huge changes, and CHANGELOG may be incomplete.
Beleive rustdoc rather than this CHANGELOG.**

* Minimum supported Rust version is now 1.41 or above.
* Make IRI string types polymorphic, and rename some types.
    + Now IRI types and URI types can share the same codebase.
    + This makes it easy for users to implement functions for both IRI types and URI types.
* Add URI types.
* Remove `Deref` impls for IRI string types.
* Remove depraceted items.
* Add and change methods for IRI string types.
* `resolve::resolve_iri` is now (more) polymorphic, and renamed to `resolve::resolve`.
* Update some internal dependencies.
    + This has no effect for usual users, and this does not introduce any API changes.
    + By this change, the crate now successfully compiles with minimal dependency versions.
* Support `no_std` environment.
    + `std` and `alloc` feature flags are added.
    + `std` feature is enabled by default (and `std` enables `alloc` automatically).

### Fixes
* Update some internal dependencies to make the crate buildable with minimal dependency versions.
    + This has no effect for usual users, and this does not introduce any API changes.
    + By this change, the crate now successfully compiles with minimal dependency versions.
        - To test that, you can run
          `cargo +nightly update -Z minimal-versions && cargo test --all-features`.

### Changed (breaking)
* Make IRI string types polymorphic, and rename some types.
    + Now IRI types and URI types can share the same codebase.
    + This makes it easy for users to implement functions for both IRI types and URI types.
    + Polymorphic types are named `types::Ri{,Absolute,Fragment,Reference,Relative}Str{,ing}`.
    + Type aliases for monomorphized types are also provided, but naming convertions are the same.
      They are named `{Iri,Uri}{..}Str{,ing}`.
        - For example, there is `IriAbsoluteStr` instead of legacy `AbsoluteIriStr`.
    * `types::CreationError` is now revived.
    * `types::IriCreationError` is now removed in favor of `types::CreationError`.
* Remove depraceted items.
    + `IriReferenceStr::resolve()` is now removed.
      Use `IriReferenceStr::resolve_against()` instead.
* Remove `Deref` impls for IRI string types.
    + IRI string types should not implement `Deref`, because they are not smart pointer types.
* Change methods types.
    + `IriReferenceStr::resolve_against()` now returns `Cow<'_, IriStr>`, rather than `IriString`.
* `resolve::resolve_iri` is now polymorphic, and renamed to `resolve::resolve`.
    + Now it can be used for both IRI types and URI types.

### Changed (non-breaking)
* Support `no_std` environment.
    + `std` and `alloc` feature flags are added.
    + `std` feature is enabled by default (and `std` enables `alloc` automatically).
    + In `no_std` environment with allocator support, you can enable `alloc` feature.
* Add methods for IRI string types.
    + `len()` and `is_empty()` methods are added to all IRI string slice types.
    * `IriStr::fragment()` is added.
    * `RelativeIriStr::resolve_against()` is added.
* Add URI types.

## [0.2.3]

* Fixed a bug that URI validators wrongly accepts non-ASCII characters.
    + Now they rejects non-ASCII characters correctly.
* Fixed a bug that abnormal URIs (such as `foo://` or `foo:////`) are wrongly rejected.
    + Now they are accepted as valid IRIs.

### Fixes
* Fixed a bug that URI validators wrongly accepts non-ASCII characters
  (9b8011f54dab3c2f8da78dc2251353453317d8af).
    + Now they rejects non-ASCII characters correctly.
* Fixed a bug that abnormal URIs (such as `foo://` or `foo:////`) are wrongly rejected
  (7a40f4b72964d498970a356368dc320917d88e43).
    + Now they are accepted as valid IRIs.
    + Documents are added to explain why they are valid.

### Improved
* More tests are added to ensure invalid URIs/IRIs are rejected as expected
  (9b8011f54dab3c2f8da78dc2251353453317d8af).

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

[Unreleased]: <https://github.com/lo48576/iri-string/compare/v0.4.1...develop>
[0.4.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.4.1>
[0.4.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.4.0>
[0.3.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.3.0>
[0.2.3]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.3>
[0.2.2]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.2>
[0.2.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.1>
[0.2.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0>
[0.2.0-beta.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0-beta.1>
[0.2.0-beta.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0-beta.0>
