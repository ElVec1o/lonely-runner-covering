#!/bin/bash
# Build the dense-window tools. Usage: bash code/dense/build.sh [OUTDIR]   (default build/dense)
# Toolchain: rustc 1.96.0, edition 2021. No crates.
set -e
OUT=${1:-build/dense}; mkdir -p "$OUT"
S=$(dirname "$0")/src
for t in v1 g1 lg cg xc fb yind m94; do
  src=$S/$t/main.rs
  bin=$t; [ $t = lg ] && bin=lg2
  rustc --edition 2021 -O -o "$OUT/$bin" "$src" 2>&1 | grep -E "^error" || true
done
ls -la "$OUT"
