#!/bin/bash
# real27_driver.sh : run_prime.sh with KEEP=1 for the 27 primes in increasing order (41 excluded).
# Checkpoint: work/records/P<p>/KEPT + work/olean/E8Stage/P<p>/Asm.olean. Resume-safe: rerun it.
# Waits (retries every 180 s, up to 240 times) while free disk < 2500 MB or a lean/disk refusal (rc=3) occurs;
# aborts on a real build/check failure or when work/HALT exists (user stop). Log: build/logs/real27.log
# (per-prime lines and ETA from the mean of finished primes scaled by total_nodes). Stop: kill -- -<pgid>.
. "$(dirname "$0")/env.sh"
export KEEP=1 MINMB=2000
LOG=$ROOT/build/logs/real27.log
PR="31 37 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163"
say() { echo "$(date '+%F %T') $*" >> "$LOG"; }
nodes() { head -1 "$REC/P$1/manifest.txt" | sed 's/.*total_nodes \([0-9]*\).*/\1/'; }
tot=0; for p in $PR; do tot=$((tot + $(nodes $p))); done
done_nodes=0; t_start=$(date +%s); work_nodes=0; ndone=0
say "driver start pid=$$ total_nodes=$tot"
for p in $PR; do
  n=$(nodes $p)
  if [ -f "$W/records/P$p/KEPT" ] && [ -f "$W/olean/E8Stage/P$p/Asm.olean" ]; then
    done_nodes=$((done_nodes + n)); ndone=$((ndone + 1)); say "P$p already kept ($ndone/27)"; continue; fi
  tries=0
  while :; do
    [ -f "$W/HALT" ] && { say "ABORT HALT file"; exit 3; }
    free_mb=$(df -m "$W" | awk 'NR==2{print $4}')
    if [ "$free_mb" -lt 2100 ]; then
      tries=$((tries + 1)); [ $tries -gt 240 ] && { say "ABORT free disk ${free_mb}MB for too long before P$p"; exit 3; }
      say "WAIT free disk ${free_mb}MB < 2100 before P$p (try $tries)"; sleep 180; continue; fi
    rm -f "$W/STOP" "$W/records/P$p/KEPT"
    s=$(date +%s)
    "$S/run_prime.sh" "$p" 2; rc=$?
    el=$(( $(date +%s) - s ))
    if [ $rc -eq 3 ]; then
      tries=$((tries + 1)); [ $tries -gt 240 ] && { say "ABORT P$p refused too often"; exit 3; }
      say "WAIT P$p refused (rc=3, low disk or busy), retry $tries"; sleep 180; continue; fi
    if [ $rc -ne 0 ] || [ ! -f "$W/records/P$p/KEPT" ]; then say "ABORT P$p rc=$rc after ${el}s"; exit 1; fi
    break
  done
  ndone=$((ndone + 1)); done_nodes=$((done_nodes + n)); work_nodes=$((work_nodes + n))
  used=$(( $(date +%s) - t_start )); rem=$(( tot - done_nodes ))
  eta=$(( used * rem / (work_nodes > 0 ? work_nodes : 1) ))
  say "P$p KEPT ${el}s ($ndone/27) nodes $done_nodes/$tot free=$(df -m "$W" | awk 'NR==2{print $4}')MB olean_total=$(du -sk "$W/olean" | cut -f1)KiB ETA_s=$eta (linear in nodes)"
done
say "ALL27 KEPT"
