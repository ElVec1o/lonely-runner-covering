#!/bin/bash
# build_generator.sh : compile the certificate generator (std only, no crates).
. "$(dirname "$0")/env.sh"
mkdir -p "$E/bin"
rustc -O --edition 2021 -o "$GEN" "$E/generator/l7v4.rs" && echo "built $GEN"
