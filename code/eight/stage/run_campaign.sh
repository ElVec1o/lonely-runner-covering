#!/bin/bash
# run_campaign.sh [primes...] : run_prime.sh on each prime in turn (default: all 27). Resumable;
# stops on the first failure, on low disk, or when work/STOP exists.
. "$(dirname "$0")/env.sh"
PR=${*:-"31 37 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163"}
for p in $PR; do
  [ -f "$W/STOP" ] && { echo "stopped before P$p"; exit 3; }
  "$S/run_prime.sh" "$p" 2 || { echo "halted at P$p rc=$?"; exit 1; }
done
echo "ALLDONE"
