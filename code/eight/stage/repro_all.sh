#!/bin/bash
# repro_all.sh : repro_check.sh on all 27 primes.
. "$(dirname "$0")/env.sh"
fail=0
for p in 31 37 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163; do
  "$S/repro_check.sh" $p || fail=1
done
exit $fail
