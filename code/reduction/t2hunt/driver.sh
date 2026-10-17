#!/bin/bash
# Reproduces Table 2. Run from code/reduction/t2hunt after `cargo build --release`.
mkdir -p out
for m in 14 16 18 20; do
  ./target/release/t2hunt run $m 5000 720 4 $((m*101+1)) out/h5000_m$m
  ./target/release/t2hunt run $m 60 180 4 $((m*101+2)) out/h60_m$m
done
