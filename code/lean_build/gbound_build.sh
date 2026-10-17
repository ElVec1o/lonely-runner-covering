#!/bin/bash
# Build Lean modules strictly one at a time (a named target may parallelise its dependency closure;
# one lean worker needed about 10 GB on a 24 GB machine). Stops on the first failure or on low disk.
# Usage, from anywhere:  bash code/lean_build/gbound_build.sh Module1 Module2 ...
# Module names are given without the prefix LRSpectrumFull.   Logs go to build/logs/.
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$ROOT/build/logs"
cd "$ROOT/lean" || exit 2
for m in "$@"; do
  free_mb=$(df -m "$ROOT" | awk 'NR==2{print $4}')
  if [ "$free_mb" -lt 1536 ]; then echo "STOP low disk ${free_mb}MB before $m"; exit 3; fi
  start=$(date +%s)
  lake build "LRSpectrumFull.$m" > "$ROOT/build/logs/build_$m.log" 2>&1
  rc=$?
  echo "$m EXIT:$rc $(( $(date +%s) - start ))s free=${free_mb}MB"
  if [ $rc -ne 0 ]; then
    grep -n -A8 "error:" "$ROOT/build/logs/build_$m.log" | head -40
    exit 1
  fi
done
echo "ALL OK"
