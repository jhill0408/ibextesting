#!/bin/bash
set -e

REPO_ROOT=`git rev-parse --show-toplevel`

#Build log_checker if not already built
pushd $REPO_ROOT/verif/rust
cargo build --release --bin stats_from_log
popd

$REPO_ROOT/verif/rust/target/release/stats_from_log $@
