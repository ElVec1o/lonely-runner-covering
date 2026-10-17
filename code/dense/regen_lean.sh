#!/bin/bash
# Regenerate the split-style Lean modules for m >= 64 from the certificates in data/dense/certs and compare
# them byte for byte (except provenance comment line 4) with lean/LRSpectrumFull/Delta2CoverRangeS<M>.lean (m = 64 is module SB).
# Usage, from the bundle root:  bash code/dense/regen_lean.sh [BUILD_DIR]   (default build/dense)
BIN=${1:-build/dense}; ROOT=$PWD; case "$BIN" in /*) ;; *) BIN=$ROOT/$BIN;; esac; T=$(mktemp -d); fail=0; n=0
cd data/dense
for f in certs/m*.g1.sol; do
  m=${f#certs/m}; m=${m%.g1.sol}
  [ "$m" = 62 ] && { echo "m=62: module SA was generated from the data of the monolithic module AC; not compared"; continue; }
  tag=S$m; [ "$m" = 64 ] && tag=SB
  tgt=$ROOT/lean/LRSpectrumFull/Delta2CoverRange$tag.lean
  [ -f "$tgt" ] || { echo "m=$m: no Lean module in the bundle (certificate only)"; continue; }
  "$BIN/lg2" gen2 $m $f $tag $T/out.lean > /dev/null 2>&1
  # line 4 is a provenance comment (for m = 64 it names the unbuilt file the data was copied from)
  if cmp -s <(sed 4d $T/out.lean) <(sed 4d "$tgt"); then echo "m=$m IDENTICAL"; else echo "m=$m DIFFERS"; fail=$((fail+1)); fi
  n=$((n+1))
done
echo "compared $n, differing $fail"; rm -rf $T; exit $fail
