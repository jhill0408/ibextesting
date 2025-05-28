#!/bin/bash
set -e

REPO_ROOT=`git rev-parse --show-toplevel`

#Build log_checker if not already built
pushd $REPO_ROOT/verif/rust
cargo build --release --bin log_checker
popd

$REPO_ROOT/verif/rust/target/release/log_checker $@
