# Change Log

## [0.5.0 (under development)]

This entry describes the changes since the last stable release (v0.4.1).
v0.5.0 is under active development and not yet released.

* Bump MSRV to 1.58.0.
* Add more conversions between IRI string types.
    * Implement `TryFrom<&[u8]>`) for IRI string types.
    * Add `as_slice` method to the owned string types.
* Add `capacity()` method to the owned string types.
* Add components getters for borrowed string types.
* Add IRI normalization API and related types.
* Add normalizing variations for IRI resolution.
* Support nostd for IRI resolution.
* Change IRI resolution API incompatibly.
    + Change number and types of parameters.
    + Change return types.
* Let IRI resolution recognize percent-encoded period during normalization.
* Drop internal dependency to `nom` crate.
* Permit `serde`+`{alloc,std}` without `serde-{alloc,std}`.

### Added
* Add more conversions between IRI string types.
    + Implement `TryFrom<&[u8]>`) for IRI string types.
    + Add `as_slice` method to the owned string types.
* Add `capacity()` method to the owned string types.
* Add components getters for borrowed string types.
    + Add getters for major components of IRIs/URIs:
      `scheme`, `authority`, `path`, and `query`.
    + Add types and getters for subcomponents of `authority`:
      `userinfo`, `host`, and `port`.
        - `components::AuthorityComponents` type and `authority_components` method.
* Add IRI normalization API and related types.
    + Add `{RiStr, RiAbsoluteStr}::normalize()` methods.
    + Add `normalize::NormalizationTask`.
* Add normalizing variations for IRI resolution.
    + `resolve_normalize` for `resolve`.
    + `resolve_normalize_against` for `resolve_against`.
* Support nostd for IRI resolution.
    + Add `resolve::FixedBaseResolver` to get `normalize::NormalizationTask`.
    + Users can write the resolution/normalization result to user-provided buffer by `NormalizationTask`.

### Changed (breaking)
* Bump MSRV to 1.58.0.
    + Rust 1.58.0 is released at 2022-01-13.
* Change IRI resolution API incompatibly.
    + Remove `is_strict: bool` parameter from `resolve::resolve()`.
    + Make IRI resolution fallible.
        - Now IRI resolution returns `Result`.
        - For details about possible resolution/normalization failure, see the
          documentation for `normalize` module and the issue [How `/..//bar`
          should be resolved aganst `scheme:`?
          (#8)](https://github.com/lo48576/iri-string/issues/8).

### Changed (non-breaking)
* Let IRI resolution recognize percent-encoded period during normalization.
    + For example, `/%2e%2e/` in the path are now recognized as `/../`, and
      handled specially as "parent directory".
* Drop internal dependency to `nom` crate.
    + Parsers are rewritten manually, and are now much faster than before.
* Permit `serde`+`{alloc,std}` without `serde-{alloc,std}`.
    + Previously, compilation error are intentionally caused when both `serde`
      and `{alloc,std}` are enabled but corresponding `serde-{alloc,std}` is not.
    + Note that you still need to enable `serde-alloc` or `serde-std` to use
      serde support for owned string types.
        - This change only intends to support the cases when flags are
          independently enabled from different indirect dependencies.

## [Unreleased]

* Add `as_slice` method to owned string types.
* Refine task API
    + Move some methods of `normalize::NormalizationTask` into newly added
      `task::ProcessAndWrite` trait.
        - `allocate_and_write`, `write_to_byte_slice`, `append_to_std_string`,
          and `try_append_to_std_string` is moved.
    + Change type parameter of `NormalizationTask` from a spec into a string slice type.
    + Change error type for `NormalizationTask`.
    + Remove `normalize::create_task()` function.

### Added
* Add `as_slice` method to the owned string types.

### Changed (breaking)
* Move some methods of `normalize::NormalizationTask` into newly added
  `task::ProcessAndWrite` trait.
    + `allocate_and_write`, `write_to_byte_slice`, `append_to_std_string`,
      and `try_append_to_std_string` is moved.
* Change type parameter of `NormalizationTask` from a spec into a string slice type.
    + Now `NormalizationTask<S>` should be changed to `NormalizationTask<RiStr<S>>`
      or `NormalizationTask<RiAbsoluteStr<S>>`.
    + This enables the task to return more appropriate type. For example,
      returning `&RiAbsoluteStr<S>` rather than `&RiStr<S>` when the input IRI
      type is `RiAbsoluteStr<S>`.
* Change error type for `NormalizationTask`.
    + Now buffer error and processing error is split to different types.
* Remove `normalize::create_task()` function.

## [0.5.0-beta.3]

* Add `normalize` module, and unify it with IRI resolution.
    + Move `resolve::{Error, ErrorKind}` to `normalize` module.
    + Move and rename `resolve::ResolutionTask` to `normalize::NormalizationTask`.
    + Add `normalize::create_task` function.
    + Add `{RiStr, RiAbsoluteStr}::normalize()` methods.
* Add normalizing variations for IRI resolution.

### Added
* Add `normalize` module.
    + Add `normalize::create_task()` function.
    + Add `{RiStr, RiAbsoluteStr}::normalize()` methods.
* Add normalizing variations for IRI resolution.
    + `resolve_normalize` for `resolve`.
    + `resolve_normalize_against` for `resolve_against`.

### Changed (breaking)
* Move `resolve::{Error, ErrorKind}` to `normalize` module.
* Move and rename `resolve::ResolutionTask` to `normalize::NormalizationTask`.
    + Now `resolve::FixedBaseResolver::create_task()` returns `NormalizationTask`.

## [0.5.0-beta.2]

* Fix a bug that `serde-std` feature did not enable serde support for owned types.

### Fixed
* Fix a bug that `serde-std` feature did not enable serde support for owned types.
    + Now `serde-std` enables `alloc` features automatically.

## [0.5.0-beta.1]

* Add getters for major components of IRIs/URIs: `scheme`, `authority`, `path`, and `query`.
* Add types and getters for subcomponents of `authority`: `userinfo`, `host`, and `port`.
    + `components::AuthorityComponents` type and `authority_components` method.
* Fix a bug that `serde-std` feature did not enable serde support for owned types.

### Added
* Add getters for major components of IRIs/URIs: `scheme`, `authority`, `path`, and `query`.
    + Method names are `scheme_str`, `authority_str`, `path_str`, and `query_str`, respectively.
    + Getters for `fragment` component is already provided.
* Add getter for subcomponents of `authority`: `userinfo`, `host`, and `port`.
    + `components::AuthorityComponents` type and `authority_components` method.

### Fixed
* Fix a bug that `serde-std` feature did not enable serde support for owned types.
    + Now `serde-std` enables `alloc` features automatically.

## [0.5.0-beta.0]

* Bump MSRV to 1.58.0.
* Add conversion from a byte slice (`&[u8]`) into IRI string types.
* Add `capacity` method to allocated string types.
* Remove `is_strict: bool` parameter from `resolve::resolve()`.
* Add `resolve::FixedBaseResolver`, `resolve::ResolutionTask`, and `resolve::Error` types.
    + Some methods for IRI resolution are now available even when `alloc` feature is disabled.
    + See [IRI resolution using user-provided buffers (#6)](https://github.com/lo48576/iri-string/issues/6).
* Make IRI resolution fallible.
    + Now `resolve()` and its family returns `Result<_, resolve::Error>`.
    + See [How `/..//bar` should be resolved aganst `scheme:`? (#8)](https://github.com/lo48576/iri-string/issues/8).
* Make IRI resolution recognize percent-encoded period.
    + Now `%2E` and `%2e` in path segment is handled as a plain period `.`.
    + See [Recognize percent-encoded periods (`%2E`) during IRI resolution (#9)](https://github.com/lo48576/iri-string/issues/9)
* Make parsers faster.
    + See [Make the parsers faster (#7)](https://github.com/lo48576/iri-string/issues/7)
* Drop internal dependency to `nom`.
* Stop emitting compilation error when both `serde` and `std`/`alloc` are enabled
  without corresponding `serde-{std,alloc}` features.

### Added
* Add conversion from a byte slice (`&[u8]`) into IRI string types.
* Add `capacity` method to allocated string types.
    + `shrink_to_fit()` and `len()` already exists, so this would be useful to determine
      when to do `shrink_to_fit`.
* Add `resolve::FixedBaseResolver`, `resolve::ResolutionTask`, and `resolve::Error` types.
    + They provide more efficient and controllable IRI resolution.
    + Some methods for IRI resolution are now available even when `alloc` feature is disabled.

### Changed (breaking)
* Bump MSRV to 1.58.0.
    + Rust 1.58.0 is released at 2022-01-13.
* Remove `is_strict: bool` parameter from `resolve::resolve()`.
    + The IRI parsers provided by this crate is "strict", so resolution
      algorithm should use an algorithm for the strict parser.
* Make IRI resolution fallible.
    + Now `resolve()` and its family returns `Result<_, resolve::Error>`.
    + For the reasons behind, see crate-level documentation.
    + See [How `/..//bar` should be resolved aganst `scheme:`? (#8)](https://github.com/lo48576/iri-string/issues/8).
* Make IRI resolution recognize percent-encoded period.
    + Now `%2E` and `%2e` in path segment is handled as a plain period `.`.
    + Period is `unreserved` character, and can be escaped at any time
      (see [RFC 3986 section 2.4](https://datatracker.ietf.org/doc/html/rfc3986#section-2.4).
      This means that `%2E` and `%2e` in the path can be normalized to `.` before IRI resolution,
      and thus they should also be handled specially during `remove_dot_segments` algorithm.
    + See [Recognize percent-encoded periods (`%2E`) during IRI resolution (#9)](https://github.com/lo48576/iri-string/issues/9)

### Changed (non-breaking)
* Make parsers faster.
    + Parsers are rewritten, and they became very fast!
    + Almost all usages are affected: type conversions, validations, and IRI resolutions.
    + See [Make the parsers faster (#7)](https://github.com/lo48576/iri-string/issues/7)
* Drop internal dependency to `nom`.
    + Parsers are rewritten without `nom`.
* Stop emitting compilation error when both `serde` and `std`/`alloc` are enabled
  without corresponding `serde-{std,alloc}` features.
    + `serde` and `std`/`alloc` might be enabled independently from the different
      indirect dependencies, so this situation should not be compilation error.

## [0.4.1]

* Bump internal dependency.
    + `nom` from v6 to v7.

### Changed (non-breaking)
* Bump internal dependency.
    + `nom` from v6 to v7.

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
    + `types::CreationError` is now revived.
    + `types::IriCreationError` is now removed in favor of `types::CreationError`.
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
    + `IriStr::fragment()` is added.
    + `RelativeIriStr::resolve_against()` is added.
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
    + This creates `IriFragmentStr` from the given string with leading hash (`#`) character.
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

[0.5.0 (under development)]: <https://github.com/lo48576/iri-string/compare/v0.4.1...develop>
[Unreleased]: <https://github.com/lo48576/iri-string/compare/v0.5.0-beta.3...develop>
[0.5.0-beta.3]: <https://github.com/lo48576/iri-string/releases/tag/v0.5.0-beta.3>
[0.5.0-beta.2]: <https://github.com/lo48576/iri-string/releases/tag/v0.5.0-beta.2>
[0.5.0-beta.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.5.0-beta.1>
[0.5.0-beta.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.5.0-beta.0>
[0.4.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.4.1>
[0.4.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.4.0>
[0.3.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.3.0>
[0.2.3]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.3>
[0.2.2]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.2>
[0.2.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.1>
[0.2.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0>
[0.2.0-beta.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0-beta.1>
[0.2.0-beta.0]: <https://github.com/lo48576/iri-string/releases/tag/v0.2.0-beta.0>
