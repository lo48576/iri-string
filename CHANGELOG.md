# Change Log

## [Unreleased]

### Added

  * Add `RelativeIri{Str,String}` types to `relative` module.
      + Additionaly, `RelativeIriParseError` type is also added.
      + Note that this is not well tested...
        Contributions are welcomed!
  * `AbsoluteIriString::from_string_unchecked` method is added for consistency.

### Changed (non-breaking)

  * Move `AbsoluteIri{,Str,String}` to `absolute` module.
      + These types are re-exported at root, so this is not breaking change.

### Fixed (non-breaking)

  * Clippy lint `derive_hash_xor_eq` is explicitly disabled.
      + See source comments at commit `23049e17d502` for detail.
      + This does not affect normal use, affects only `cargo clippy`


## [0.1.0] - 2018-05-04

Initial release.

### Added

  * `AbsoluteIri{,Str,String}` types.
  * Optional `serde` integration.
      + Enabled by default.



[Unreleased]: <https://github.com/lo48576/iri-string/compare/v0.1.0...develop>
[0.0.1]: <https://github.com/lo48576/iri-string/releases/tag/v0.1.0>
