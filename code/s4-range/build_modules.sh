#!/bin/bash
# usage: build_modules.sh TAG MODULE...   (module names without the prefix LRSpectrumFull.)  builds each module (lake build, 12000 MB wrapper), one at a time, prints one summary line each.
# Log name = <TAG>_<MODULE>; failed logs are kept (never overwritten: refuses if the log exists).
# Set LEAN_DIR (the directory lean/ of this archive, or any Lake project containing LRSpectrumFull), LOG_DIR (an empty or existing directory for logs)
# and WATCHDOG (the path of launch_watchdog.sh from this directory) in the environment. Paths were the only change made for the archive.
cd "${LEAN_DIR:?set LEAN_DIR}" || exit 9
W=${WATCHDOG:?set WATCHDOG}
L=${LOG_DIR:?set LOG_DIR}
mkdir -p "$L"
TAG=$1; shift
for m in "$@"; do
  N=${TAG}_$m
  [ -e $L/$N.watch ] && { echo "SKIP $N log exists"; continue; }
  FREE=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
  [ "$FREE" -lt 4 ] && { echo "STOP free disk ${FREE}GB"; exit 3; }
  P=$(pgrep -f 'toolchains/[^ ]*/bin/(lean|lake)[ ]' | wc -l | tr -d ' ')
  [ "$P" != "0" ] && { echo "STOP lean/lake processes running: $P"; exit 4; }
  S=$(date +%s)
  bash $W 12000 $L $N lake build LRSpectrumFull.$m > /dev/null 2>&1
  E=$(date +%s)
  PEAK=$(grep -o 'rss=[0-9]*MB' $L/$N.watch | tr -dc '0-9\n' | sort -n | tail -1)
  EX=$(grep '^exit=' $L/$N.watch | tail -1 | cut -d' ' -f1)
  KILL=$(grep -c 'WATCHDOG KILL' $L/$N.watch)
  ERR=$(grep -c 'error' $L/$N.out)
  echo "BUILT $m $EX killed=$KILL errors=$ERR secs=$((E-S)) peakMB=$PEAK"
  grep -h 'depends on axioms\|does not depend' $L/$N.out | sed 's/^info: //' | cut -c1-260
done
