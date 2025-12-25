#!/bin/sh
set -eu

cd "$(readlink -f "$(dirname "$0")/../..")"

set -x

# Use the preset for CI environment.
cp .woodpecker/cargo-config.toml ${CARGO_HOME}/config.toml

# Use the Rust toolchain(s) cached in the CI workspace directory.
export RUSTUP_HOME=${CI_WORKSPACE}/.tmp-rustup-home && test -d ${RUSTUP_HOME}

rustc --version && cargo --version

set +x
