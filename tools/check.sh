#!/bin/bash

set -e

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

source "tools/utils.sh"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

function on_failure {
    echo >&2
    echo -e "${RED}Whoopsie-daisy: something failed!$NC" >&2
}

assert_installed "cargo-fmt"
assert_installed "cargo-clippy"
assert_installed "cargo-rdme"

trap on_failure ERR

echo 'Building:'
cargo build --all-features --all-targets
echo 'Testing:'
SHORT_BENCH=1 cargo test  --all-features --all-targets --benches

# We test property-based tests will a much higher number of testcases. We need to compile this with the release profile,
# otherwise this would be very slow.
echo 'Testing property-based tests for longer:'
QUICKCHECK_TESTS=200000 cargo test --all-features --release property_

# Weirdly, the `cargo test ... --all-targets ...` above does not run the tests in the documentation, so we run the
# doc tests like this.
# See https://github.com/rust-lang/cargo/issues/6669.
echo 'Testing doc:'
cargo test  --all-features --doc
echo 'Checking documentation:'
cargo doc   --all-features --no-deps --document-private-items

echo 'Checking clippy:'
cargo clippy --all-features --all-targets

echo 'Checking packaging:'
cargo package --allow-dirty
echo 'Checking code style:'
cargo fmt -- --check
echo 'Checking readme:'
cargo rdme --check

echo
echo -e "${GREEN}Everything looks lovely!$NC"

exit 0
