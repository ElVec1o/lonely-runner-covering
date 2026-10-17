#!/bin/bash
# repro_check.sh P : regenerate the certificate sources of prime P and compare the combined SHA-256
# with records/P<P>/record.txt. No Lean run; seconds per prime.
. "$(dirname "$0")/env.sh"
P=$1; R=$REC/P$P; T=$W/repro_P$P
args=$(sed -n 's/^generator_cmd: l7v4s \([0-9]*\) stage <dir> \(.*\)$/\2/p' "$R/record.txt")
rm -rf "$T"; "$GEN" "$P" stage "$T" $args 2>/dev/null
want=$(sed -n 's/^combined_sha256 //p' "$R/record.txt")
got=$(cd "$T" && cat $(ls *.lean | sort) | shasum -a 256 | cut -d' ' -f1)
rm -rf "$T"
[ "$want" = "$got" ] && echo "P$P REPRODUCED $got" || { echo "P$P MISMATCH want $want got $got"; exit 1; }
