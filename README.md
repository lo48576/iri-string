# iri-string

[![Latest version](https://img.shields.io/crates/v/iri-string.svg)](https://crates.io/crates/iri-string)
[![Documentation](https://docs.rs/iri-string/badge.svg)](https://docs.rs/iri-string)
![Minimum rustc version: 1.60](https://img.shields.io/badge/rustc-1.60+-lightgray.svg)

String types for [IRI](https://tools.ietf.org/html/rfc3987)s (Internationalized Resource
Identifiers) and [URI](https://tools.ietf.org/html/rfc3986)s (Uniform Resource Identifiers).

See the [documentation](https://docs.rs/iri-string) for details.

## Features

* `no_std` support.
* String types (both owned and borrowed) for IRIs.
* IRI reference resolution algorithm.
* IRI normalization algorithm.

### Feature flags

#### Direct
* `alloc` (enabled by default)
    + Enables types and functions which require memory allocation.
    + Requires `std` or `alloc` crate available.
* `std` (enabled by default)
    + Enables all `std` features (such as memory allocations and `std::error::Error` trait).
    + Requires `std` crate available.
    + This automatically enables `alloc` feature.

#### memchr
* `memchr`
    + Enable optimization for internal parsers, using [`memchr`] crate.

[`memchr`]: https://crates.io/crates/memchr

#### serde
* `serde`
    + Implements `Serialize` and `Deserialize` traits for string types.

## CI

CI must pass on `develop` and `master` branches.
No automated online CI is set up (since they consumes credit too fast), so run
`cargo make manual-ci-all` locally before committing to these branches.
On other branches, tests and some lints (such as `dead_code`) are allowed to
fail, but all commits must be successfully compilable and must be formatted.

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE.txt](LICENSE-APACHE.txt) or
  <https://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT.txt](LICENSE-MIT.txt) or
  <https://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
